use halo2_proofs::{arithmetic::FieldExt,
    circuit::*, 
    plonk::*, 
    poly::Rotation,
    pasta::Fp, dev::MockProver,};
use std::marker::PhantomData;


#[cfg(feature = "dev-graph")]
use halo2_proofs::{dev::circuit_dot_graph};

#[derive(Debug, Clone)]


// Defines the configuration of all the columns, and all of the column definitions
// Will be incrementally populated and passed around
struct FibonacciConfig {
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct FibonacciChip<F: FieldExt> {
    config: FibonacciConfig,
    _marker: PhantomData<F>,
    // In rust, when you have a struct that is generic over a type parameter (here F),
    // but the type parameter is not referenced in a field of the struct,
    // you have to use PhantomData to virtually reference the type parameter,
    // so that the compiler can track it.  Otherwise it would give an error. - Jason
}

impl<F: FieldExt> FibonacciChip<F> {
    // Default constructor
    pub fn construct(config: FibonacciConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    // Configure will set what type of columns things are, enable equality, create gates, and return a config with all the gates
    pub fn configure(meta: &mut ConstraintSystem<F>) -> FibonacciConfig {
       //add to advice column to ConstraintSystem. Set Query of this column to zero and add to conut of advice columns
        let col_a = meta.advice_column();
        // returns an advice column where {index= num_advice_column, column type = Advice}
        let col_b = meta.advice_column();
        // private witnesses
        let col_c = meta.advice_column();
        // selevtor for gate
        let selector = meta.selector();
        // public inputs
        let instance = meta.instance_column();
        // All of these are added to the constaint system 
        //println!("Column's A Index: {:?}",instance); 


        // enable_equality has some cost, so we only want to define it on rows where we need copy constraints
        // adds column to permutation vector in constraint system  
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        // Adds to permutation vector 
        // if it has not been quried then adds it to
        //advice_queries and sets num_advice_queries to be 1 at corresponding spot 
        meta.enable_equality(instance);

        //adds to query HERE! 


        // Defining a create_gate here applies it over every single column in the circuit.
        // We will use the selector column to decide when to turn this gate on and off, since we probably don't want it on every row
        meta.create_gate("add", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s
            //
            // add to quried_cells in vituual cells 
            // returns selector expersision with seleleter inside
            let s = meta.query_selector(selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            //println!("Column's A Index in VCell: {:?}",a); 

            let b = meta.query_advice(col_b, Rotation::cur());
            //println!("Column's b Index in VCell: {:?}",b); 

            let c = meta.query_advice(col_c, Rotation::cur());
            //println!("Column's c Index in VCell: {:?}",c); 

            vec![s * (a + b - c)]
        });
//println!("GATES {:?}",meta);
        FibonacciConfig {
            col_a,
            col_b,
            col_c,
            selector,
            instance,
        }
    }

    // These assign functions are to be called by the synthesizer, and will be used to assign values to the columns (the witness)
    // The layouter will collect all the region definitions and compress it horizontally (i.e. squeeze up/down)
    // but not vertically (i.e. will not squeeze left/right, at least right now)
    #[allow(clippy::type_complexity)]
    pub fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;
                //Assign the value of the instance column's cell
                //at absolute location row to the column advice at 
                //offset within this region.
                //Returns the advice cell, and its value if known.
                let a_cell = region.assign_advice_from_instance(
                    || "f(0)",
                    self.config.instance,
                    0,
                    self.config.col_a,
                    0,
                )?;
                // How doe witness column and instance column cowork? 
                // Instance are the public inputs
                // adive are the private values

                // Example Starting input and endng value for Fibonancci sequence
                
                // assign to advice column b at row 0 the instance column enrry 1

                let b_cell = region.assign_advice_from_instance(
                    || "f(1)",
                    self.config.instance,
                    1,
                    self.config.col_b,
                    0,
                )?;
                // assign_advice is you witnessing something
                // assign_advice_from_instance is you copying something from instance column

                // Start by assigning the public inputs (instance) f(0),f(1) to Witness columns
                let c_cell = region.assign_advice(
                    || "a + b",
                    self.config.col_c,
                    0,
                    || a_cell.value().copied() + b_cell.value(),
                )?;

                Ok((a_cell, b_cell, c_cell))
                // NOTE ASSIGN_ADVICE DOES NOT IMPOSE copy constraints
            },
        )
    }

// Note copy_advice does impost restrictions 
// NEW REGION NEW REGION
    // This will be repeatedly called. Note that each time it makes a new region, comprised of a, b, c, s that happen to all be in the same row
    pub fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        prev_b: &AssignedCell<F, F>,
        prev_c: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "next row",
            |mut region| {
                //enable this selector within the given region at 0 
                self.config.selector.enable(&mut region, 0)?;

                // Copy the value from b & c in previous row to a & b in current row
                
                //For previous b I would likt to copy col_a at current row
                prev_b.copy_advice(|| "a", &mut region, self.config.col_a, 0)?;
                prev_c.copy_advice(|| "b", &mut region, self.config.col_b, 0)?;

                let c_cell = region.assign_advice(
                    || "c",
                    self.config.col_c,
                    0,
                    || prev_b.value().copied() + prev_c.value(),
                )?;

                Ok(c_cell)
            },
        )
    }
// Final constraint 
// A cell must equal to the absolute value of the instance row
    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit<F>(PhantomData<F>);

// Our circuit will instantiate an instance based on the interface defined on the chip and floorplanner (layouter)
// There isn't a clear reason this and the chip aren't the same thing, except for better abstractions for complex circuits

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = FibonacciConfig;
    type FloorPlanner = SimpleFloorPlanner;

    // Circuit without witnesses, called only during key generation
    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    // Has the arrangement of columns. Called only during keygen, and will just call chip config most of the time
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FibonacciChip::configure(meta)
    }

    // Take the output of configure and floorplanner type to make the actual circuit
    // Called both at key generation time, and proving time with a specific witness
    // Will call all of the copy constraints
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        //Constructs Constraint System 
        let chip = FibonacciChip::construct(config);
        //Calls Layouter and assigns first row 
        let (_, mut prev_b, mut prev_c) =
            chip.assign_first_row(layouter.namespace(|| "first row"))?;
        // Uses layouter to assign other rows 
        for _i in 3..10 {
            let c_cell = chip.assign_row(layouter.namespace(|| "next row"), &prev_b, &prev_c)?;
            prev_b = prev_c;
            prev_c = c_cell;
        }

        chip.expose_public(layouter.namespace(|| "out"), &prev_c, 2)?;

        Ok(())
    }
}

/* 

fn main(){
    print!("Okay");
    let k = 4;

    let a = Fp::from(1); // F[0]
    let b = Fp::from(1); // F[1]
    let out = Fp::from(55); // F[9]

    let circuit = MyCircuit(PhantomData);

    let mut public_input = vec![a, b, out];
    let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
    // This function will pretty-print on errors
    prover.assert_satisfied();

    public_input[2] += Fp::one();
    let _prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
    prover.assert_satisfied();}

    
*/



#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use super::MyCircuit;
    use halo2_proofs::{dev::MockProver, pasta::Fp};

    #[cfg(feature = "dev-graph")]
    pub use halo2_proofs::dev::{circuit_dot_graph};



    #[test]
    fn fibonacci_example1() {
        let k = 8;

        let a = Fp::from(1); // F[0]
        let b = Fp::from(1); // F[1]
        let out = Fp::from(55); // F[9]

        let circuit = MyCircuit(PhantomData);

        let mut public_input = vec![a, b, out];

        // This prover is faster and 'fake', but is mostly a devtool for debugging
        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
        // This function will pretty-print on errors
        prover.assert_satisfied();

        public_input[2] += Fp::one();
        let _prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();
        //let dot_string = halo2_proofs::dev::circuit_dot_graph(&circuit);
        //print!("{}", dot_string);
        //println!("{:?}", _prover);

        // uncomment the following line and the assert will fail
        //_prover.assert_satisfied();

    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_fibonacci1() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("fib-1-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fib 1 Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fp>(PhantomData);
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();

            let dot_string = halo2_proofs::dev::circuit_dot_graph(&circuit);
            //print!("{}", dot_string);
    }
}