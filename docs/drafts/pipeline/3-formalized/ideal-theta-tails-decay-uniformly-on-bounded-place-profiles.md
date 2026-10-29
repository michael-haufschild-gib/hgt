# Uniform exponential decay of ideal theta tails

- **ID:** hecke-uniform-ideal-theta-tail
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Hecke HL7; convergence of the unit-domain Mellin integral
- **Statement:** For every nonzero fractional ideal `I` and real `M`, there are
  `C > 0` and `c > 0` such that, for all `t ≥ 1` and place profiles satisfying
  `y_w ≤ M`, `0 ≤ θ_I(y,t) − 1 ≤ C exp(−c t)`.

## Corpus audit

- `NumberFieldIdealTheta` proves actual ideal Gaussian summability and inversion.
- The place-scaled version and unit-log periodicity are formalized in
  [archimedean place scaling](../3-formalized/ideal-theta-under-archimedean-place-scaling.md).
- `LatticeSubsetLinearEquivMinimum.exists_minimal_image_norm_mem_of_nonempty_subset`
  attains the minimum of the norm after an actual continuous linear equivalence
  on every nonempty subset of a discrete lattice. This supplies the positive
  minimum among nonzero weighted ideal vectors.
- `QuasiAbelianScaledGaussianDamping.norm_scaledGaussian_realTranslate_damped`
  uses the Gaussian exponent-splitting mechanism for diagonal widths on `Fin d`.
  Its shifted complex Gaussian setup differs from the actual ideal theta sum.
- Completed semantic searches also returned scalar theta-tail bounds; no matching
  actual-ideal uniform tail theorem was found in those returned results.

## Proof target

Let `δ > 0` be the minimum nonzero weighted ideal-vector norm and put
`q = exp(−M)^2 > 0`. The placewise norm formula gives
`‖S(scale_y ι(a))‖² ≥ q ‖S ι(a)‖²` whenever `y_w ≤ M`.
For `a ≠ 0` and `t ≥ 1`, split the exponent using
`t q ‖S ι(a)‖² ≥ (q/2) ‖S ι(a)‖² + (q δ²/2)t`.
The first term has a fixed summable Gaussian majorant; the second supplies
uniform exponential decay. Separate the zero element, whose summand is one.

Only an upper bound on the profiles is needed. This covers every bounded
unit fundamental domain without assuming a chosen system of units.

## Lean declarations and validation

The image-minimum source is inspected; its olean already exists. The additive
zero-term splitting lemma is Mathlib `Summable.tsum_eq_add_tsum_ite`, generated
from `Multipliable.tprod_eq_mul_tprod_ite` in `InfiniteSum/Group.lean`.
In [NumberFieldIdealThetaDecay.lean](../../../../formal/GaloisForLFunctions/HTGeometry/NumberFieldIdealThetaDecay.lean),
namespace `GaloisForLFunctions.HTGeometry`:

- `exists_positive_ideal_traceNorm_lower_bound`
- `norm_sq_placeScale_ge`
- `numberFieldScaledIdealTheta_sub_one_eq`
- `exists_uniform_exponential_numberFieldIdealTheta_tail`

The complete scratch and final direct `lake --old env lean` source audit pass
without warnings. The uniform bound's transitive axiom audit contains only
`propext`, `Classical.choice`, and `Quot.sound`. The source is wired into the
umbrella; no umbrella was compiled. Its olean is built for the written Hecke
parity-tail consumer. Fractional-ideal
subtypes are tested for zero through their value in `K`, and their zero element
is constructed explicitly; no extra algebraic instance is postulated. No proof
limits were raised. The completed scratch is removed after the final audit.

Parity-weighted Gaussian transforms are now formalized. Unit-domain Mellin integration remains open.

- [x] Exact target and corpus search.
- [x] Lean proof and final direct source audit.
- [x] Transitive axiom audit.
