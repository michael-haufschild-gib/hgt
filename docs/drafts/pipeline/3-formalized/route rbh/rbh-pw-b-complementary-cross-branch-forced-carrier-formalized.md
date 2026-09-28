# RBH / PW-B complementary cross-branch forced carrier — Lean certificate

- **Paper card:** `rbh-pw-b-complementary-cross-branch-forced-carrier.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCrossBranchBidegree`,
  `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCrossBranchSource`; input
  `ThetaCuspHawkingBMStreamMetricEinstein`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old env lean` clean; `#print axioms` of every listed theorem =
  `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

| Card item | Lean theorem |
|-|-|
| `Δ(H₊H₋) = (param₊+param₋)H₊H₋ + crossBranchAngularForcing` | `crossBranchAngular_product_equation` |
| complementary clock `-6`, clock parameter `χ = 20` | `crossBranchClock_eq_neg_six`, `crossBranchClockParameter_eq_twenty` |
| `ΔB = χB + Fcross`, `Fcross = forcing + (param - χ)B` | `crossBranchField_clock_equation`, `crossBranchClockForcing` (def), `crossBranchClockForcing_eq_scalar_defect` |
| `Vcross = coexact B` smooth and divergence-free | `crossBranchCovector_smooth`, `crossBranchCovector_divergence` |
| `roughLaplacian(Vcross) + Vcross = χVcross + Jcross` | `crossBranchCovector_rough_forced` |
| angular master slot `= χVcross + Jcross` | `crossBranch_streamAngularOperator_forced` |
| metric `streamMetricField(-6, a²b²/64, false, Vcross)`, `C²` | `crossBranchMetric`, `crossBranchMetric_clock`, `crossBranchMetric_smooth` |
| all sixteen linearized cosmological Einstein components = stream tensor | `crossBranchMetric_einstein` |
