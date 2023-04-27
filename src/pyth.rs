use halo2_proofs::{arithmetic::FieldExt,
circuit::*,
plonk::*,
poly::Rotation,
pasta::Fp,
dev::MockProver,};

use std::marker::PhantomData; 

#[derive(Debug, Clone)]
struct pythConfig{
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub addition_selector: Selector,
    pub multi_selector: Selector,
    pub instance: Column<Instance>
}

#[derive(Debug,Clone)]
struct pythChip<F: FieldExt> {
    config: pythConfig,
    _marker: PhantomData<F>, 
}

impl<F: FieldExt> pythChip<F>{
    pub fn construct(config: pythConfig)-> Self{
        Self{
            config,
            _marker: PhantomData, 
        }
    }

pub fn configure(meta: &mut ConstraintSystem<F>) -> pythConfig{
    // ins
    let col_a = meta.advice_column();
    let col_b = meta.advice_column();
    let col_c = meta.advice_column();
    let addition_selector = meta.selector(); 
    let multi_selector = meta.selector(); 

    let instance = meta.instance_column();

    meta.enable_equality(col_a);
    meta.enable_equality(col_b);
    meta.enable_equality(col_c);
    meta.enable_equality(instance);

    meta.create_gate("add", |meta|{
        let s = meta.query_selector(addition_selector); 
        let a = meta.query_advice(col_a, Rotation::cur());
        let b = meta.query_advice(col_b, Rotation::cur());
        let c = meta.query_advice(col_c, Rotation::cur());
        vec![s * (a + b - c)] 
    });

    meta.create_gate("multiply", |meta|{
        let s = meta.query_selector(multi_selector); 
        let a = meta.query_advice(col_a, Rotation::cur());
        let b = meta.query_advice(col_b, Rotation::cur());
        let c = meta.query_advice(col_c, Rotation::cur());
        vec![s * (a * b - c)] 
    });

    pythConfig{
    col_a,
    col_b,
    col_c,
    addition_selector,
    multi_selector,
    instance,}
}


#[allow(clippy::type_complexity)]
pub fn assign_all(
    &self,
    mut layouter: impl Layouter<F>,
) -> Result<AssignedCell<F, F>, Error> {

    layouter.assign_region(
        || "Entire Circuit",
        |mut region|{
        
        self.config.multi_selector.enable(&mut region, 0)?;
        
        let a1_cell = region.assign_advice_from_instance(
            || "a",
            self.config.instance,
            0,
            self.config.col_a,
            0,
        )?;

        a1_cell.copy_advice(|| "a", &mut region, self.config.col_b, 0)?;

        let c1_cell = region.assign_advice(
            || "aa",
            self.config.col_c,
            0,
            || a1_cell.value().copied() * a1_cell.value(),
        )?;

        
        self.config.multi_selector.enable(&mut region, 1)?;
        
        let a2_cell = region.assign_advice_from_instance(
            || "b",
            self.config.instance,
            1,
            self.config.col_a,
            1,
        )?;

        a2_cell.copy_advice(|| "b", &mut region, self.config.col_b, 1)?;

        let c2_cell = region.assign_advice(
            || "bb",
            self.config.col_c,
            1,
            || a2_cell.value().copied() * a2_cell.value(),
        )?;


        self.config.multi_selector.enable(&mut region, 2)?;
        
        let a3_cell = region.assign_advice_from_instance(
            || "c",
            self.config.instance,
            2,
            self.config.col_a,
            2,
        )?;

        a3_cell.copy_advice(|| "c", &mut region, self.config.col_b, 2)?;

        let c3_cell = region.assign_advice(
            || "cc",
            self.config.col_c,
            2,
            || a3_cell.value().copied() * a3_cell.value(),
        )?;
//
        self.config.addition_selector.enable(&mut region, 3)?;

        c1_cell.copy_advice(|| "aa", &mut region, self.config.col_a, 3)?;
        c2_cell.copy_advice(|| "bb", &mut region, self.config.col_b, 3)?;
        c3_cell.copy_advice(|| "cc", &mut region, self.config.col_c, 3)?;
        

       //region.constrain_equal(c3_cell.cell(),c4_cell.cell());


        Ok(c3_cell)

        },
    )
}
/* 
pub fn expose_public(
    &self,
    mut layouter: impl Layouter<F>,
    cell: &AssignedCell<F, F>,
    row: usize,
) -> Result<(), Error> {
    layouter.constrain_instance(cell.cell(), self.config.instance, row)
}*/


}

mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, pasta::Fp};

    #[derive(Default)]
    struct MyCircuit<F>(PhantomData<F>);

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = pythConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> pythConfig {
            pythChip::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = pythChip::construct(config);

            let out_cell = chip.assign_all(layouter.namespace(|| "entire table"))?;


            Ok(())
        }
    }



    #[test]
    fn test_example2() {
        let k = 4;

        let a = Fp::from(5); // F[0]
        let b = Fp::from(12); // F[1]
        let c = Fp::from(13); // F[9]

        let circuit = MyCircuit(PhantomData);

        let mut public_input = vec![a, b, c];

        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
        prover.assert_satisfied();

        public_input[2] += Fp::one();
        let _prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();
        // uncomment the following line and the assert will fail
        // _prover.assert_satisfied();
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_fibo2() {
        use plotters::prelude::*;
        let root = BitMapBackend::new("pyth-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Pyth Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fp>(PhantomData);
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}

