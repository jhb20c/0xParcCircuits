use halo2_proofs::{arithmetic::FieldExt,
    circuit::*, 
    plonk::*, 
    poly::Rotation,
    pasta::Fp, dev::MockProver,};
use std::marker::PhantomData;


#[cfg(feature = "dev-graph")]
use halo2_proofs::{dev::circuit_dot_graph};

#[derive(Debug, Clone)]


// Defines the columns that will be used with in the circuit.
// Does not include the assignment of values within the circuit. 
struct FibonacciConfig {
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
}
// a | b | c | s | i 



#[derive(Debug, Clone)]
struct FibonacciChip<F: FieldExt> {
    config: FibonacciConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FibonacciChip<F> {
    // Default constructor
    pub fn construct(config: FibonacciConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    // Configure defines the gate constraint for the circuit. 
    pub fn configure(meta: &mut ConstraintSystem<F>) -> FibonacciConfig {
        // Gate requires 3 advice columns
        // Instantiate these columns
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        
        // Gate requires one selector for gate
        // Instantiate the selector
        let selector = meta.selector();
        
        // Instantiate the input column  
        let instance = meta.instance_column();
        

        // Enable equality allows us to define columns that have copy constraints. 
        // This does not assign copy constraints but instead marks columns that contain copy constraints. 
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);



        // Defining our addition gate.
        // Selector column decides when to turn this gate on and off.
        // 
        meta.create_gate("add", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s

            let s = meta.query_selector(selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            // Defines Gate equation
            vec![s * (a + b - c)]
        });

        FibonacciConfig {
            col_a,
            col_b,
            col_c,
            selector,
            instance,
        }
    }

   // This assign values to the first row of our circuit.
   //
    #[allow(clippy::type_complexity)]
    pub fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                // Turn on our addition gate. 
                self.config.selector.enable(&mut region, 0)?;
                
                // Assigns position zero of column a within current region to be 
                // position zero of instance vector.
                // No copy constraints assigned.
                let a_cell = region.assign_advice_from_instance(
                    || "f(0)",
                    self.config.instance,
                    0,
                    self.config.col_a,
                    0,
                )?;

                // Assigns position zero of column b within current region to be 
                // position one of instance vector.
                // No copy constraints assigned.
                let b_cell = region.assign_advice_from_instance(
                    || "f(1)",
                    self.config.instance,
                    1,
                    self.config.col_b,
                    0,
                )?;
                
                // Assigns advice a + b to column c position zero within current region
                // No copy constraints assigned. 
                let c_cell = region.assign_advice(
                    || "a + b",
                    self.config.col_c,
                    0,
                    || a_cell.value().copied() + b_cell.value(),
                )?;
                // Returns the triplet of our assigned cells. 
                Ok((a_cell, b_cell, c_cell))
            },
        )
    }
    // | a  | b  |   c   |
    // | I0 | I1 | I0+I1 |  


   // This assign values to the nth row of our circuit.
   // Input is previous cells 
    pub fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        prev_b: &AssignedCell<F, F>,
        prev_c: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "next row",
            |mut region| {
                // Turn on our addition gate. 
                self.config.selector.enable(&mut region, 0)?;

                // Copy the value from b & c in previous row to a & b in current row
                
                // From previous cell b/c copy the value and place it in column a/b at position 0 within current region. 
                // Constraints the values to be equal! 
                prev_b.copy_advice(|| "a", &mut region, self.config.col_a, 0)?;
                prev_c.copy_advice(|| "b", &mut region, self.config.col_b, 0)?;
                
                
                // assigns b+c to be equal to position zero of column c in current region 
                let c_cell = region.assign_advice(
                    || "c",
                    self.config.col_c,
                    0,
                    || prev_b.value().copied() + prev_c.value(),
                )?;

                Ok(c_cell)
                // Returns only cell C 
            },
        )
    }
    // | b | c | b+c | 

// Checks that output is expected.  
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


impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = FibonacciConfig;
    type FloorPlanner = SimpleFloorPlanner;

    // Circuit without witnesses.
    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FibonacciChip::configure(meta)
    }

    // Take the output of configure and floorplanner type to make the actual circuit
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // Constructs Gate constraints 
        let chip = FibonacciChip::construct(config);
        // Assigns first row 
        let (_, mut prev_b, mut prev_c) =
            chip.assign_first_row(layouter.namespace(|| "first row"))?;
        // Assign remaining rows 
        for _i in 3..10 {
            let c_cell = chip.assign_row(layouter.namespace(|| "next row"), &prev_b, &prev_c)?;
            prev_b = prev_c;
            prev_c = c_cell;
        }
        // Constraints the output to be equal to the instance input at position 2
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