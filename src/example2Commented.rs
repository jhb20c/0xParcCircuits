use halo2_proofs::{arithmetic::FieldExt,
     circuit::*,
      plonk::*, 
      poly::Rotation};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct ACell<F: FieldExt>(AssignedCell<F, F>);

//Column 
// | a | s | i | 
#[derive(Debug, Clone)]
struct FiboConfig {
    advice: Column<Advice>,
    selector: Selector,
    instance: Column<Instance>,
} 

// Chip definition
#[derive(Debug, Clone)]
struct FiboChip<F: FieldExt> {
    config: FiboConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FiboChip<F> {
    pub fn construct(config: FiboConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
    // Configure defines the gate constraint for the circuit
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: Column<Advice>,
        instance: Column<Instance>,
    ) -> FiboConfig {
        // Gate Requires 1 advice column
        let selector = meta.selector();
        
        // Enable Permutation checking 
        meta.enable_equality(advice);
        meta.enable_equality(instance);

        // Defining the addition gate
        // Selector Column turns this gate on and off
        // 
        meta.create_gate("add", |meta| {
            //
            // advice | selector
            //   a    |   s
            //   b    |
            //   c    |
            //
            let s = meta.query_selector(selector);
            let a = meta.query_advice(advice, Rotation::cur());
            let b = meta.query_advice(advice, Rotation::next());
            let c = meta.query_advice(advice, Rotation(2));
            vec![s * (a + b - c)]
        });

// Returns a configuration 
        FiboConfig {
            advice,
            selector,
            instance,
        }
    }

// This assigns values each time the addition gate
// called. 
// No Copy Constraints assigned! 
    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        nrows: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "entire fibonacci table",
            |mut region| {
                // enable row 0 and row 1 selector 
                self.config.selector.enable(&mut region, 0)?;
                self.config.selector.enable(&mut region, 1)?;
                

                // Columns are treated as vectors
                // Assign to adivce column row 0 
                // the instance element at entry 0 
                let mut a_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    0,
                    self.config.advice,
                    0,
                )?;

                // Assign to adivce column row 1 
                // the instance element at entry 1                 
                let mut b_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    1,
                    self.config.advice,
                    1,
                )?;

                //   I     A   S
                // | 1  | 1  | 1 | 
                // | 1  | 1  | 1 |
                // 
                //      
                // Summary of above


                for row in 2..nrows {
                    if row < nrows - 2 {
                        self.config.selector.enable(&mut region, row)?;
                    }

                    let c_cell = region.assign_advice(
                        || "advice",
                        self.config.advice,
                        row,
                        || a_cell.value().copied() + b_cell.value(),
                    )?;

                    a_cell = b_cell;
                    b_cell = c_cell;
                    
                    // Summary of First Loop
                    //   I     A   S
                    // | 1  | 1  | 1 | 
                    // | 1  | 1  | 1 |
                    // |    | 2  | 1 |
                    //
                    // Then a = 1 and b = 2 
                    //
                }

                Ok(b_cell)
            },
        )
    }

// Checks that the output is expected. 
    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, pasta::Fp};

    #[derive(Default)]
    struct MyCircuit<F>(PhantomData<F>);

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = FiboConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            // Allocate an advice column and an instance column in ConstraintSystem
            let advice = meta.advice_column();
            let instance = meta.instance_column();
            FiboChip::configure(meta, advice, instance)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = FiboChip::construct(config);

            let out_cell = chip.assign(layouter.namespace(|| "entire table"), 10)?;

            chip.expose_public(layouter.namespace(|| "out"), out_cell, 2)?;

            Ok(())
        }
    }



    #[test]
    fn test_example2() {
        let k = 4;

        let a = Fp::from(1); // F[0]
        let b = Fp::from(1); // F[1]
        let out = Fp::from(55); // F[9]

        let circuit = MyCircuit(PhantomData);

        let mut public_input = vec![a, b, out];

        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
        prover.assert_satisfied();

        //public_input[2] += Fp::one();
        //let _prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();
        // uncomment the following line and the assert will fail
        // _prover.assert_satisfied();
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_fibo2() {
        use plotters::prelude::*;
        let root = BitMapBackend::new("fib-2-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fib 2 Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fp>(PhantomData);
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}

