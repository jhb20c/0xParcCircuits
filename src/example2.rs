use halo2_proofs::{arithmetic::FieldExt,
     circuit::*,
      plonk::*, 
      poly::Rotation};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct ACell<F: FieldExt>(AssignedCell<F, F>);


// One Advice column
// Selector remains
// instance column  
// Holds columns in used in circuit 
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
    // contruscts a Fibochip object
    pub fn construct(config: FiboConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
    // configure a chip object
    // THIS DEFINES ARE CONSTRAINTS BASED ON CELLS 
    // I.E GATE DEFINTIONS - via the call create_gate
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: Column<Advice>,
        instance: Column<Instance>,
    ) -> FiboConfig {
        // create a new selector turns it on!
        let selector = meta.selector();
        // Enable equality for advice columns
        meta.enable_equality(advice);
        meta.enable_equality(instance);

        // create gate 
        // This is the constraints that we would like to hold between the five columns 
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

// ASSIGNS COPY CONSTRAINTS
// no constraints here though

    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        nrows: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "entire fibonacci table",
            |mut region| {
                // enable selector in row0 and row 1 
                self.config.selector.enable(&mut region, 0)?;
                self.config.selector.enable(&mut region, 1)?;
                

                // All columns are treated as vectors
                //assign to adivce column row 0 the instance column at entry 0 
                let mut a_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    0,
                    self.config.advice,
                    0,
                )?;
                // assign to advice column at row 1 the instance column enrry 1
                let mut b_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    1,
                    self.config.advice,
                    1,
                )?;

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
                }

                Ok(b_cell)
            },
        )
    }

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

