# The weighted hyperbolic Green kernel is summable over the rational torus

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133: potential theory on the rational-torus quotient.
- **Statement:** The weighted mixed Green kernel, with canonical Robin values at collisions, has an absolutely convergent rational-torus orbit sum at every pair of full-carrier points. This sum is symmetric and descends in both arguments to the actual rational-torus quotient.

## Proof

Write `A=Σ_p p⁻² A_p`, `a²=λ+1/4`, and
`h_s(x,y)=Π_p p^(−s d_p(x_p,y_p))`. The spectral row
`E(s)=Σ_p p⁻²(p^s+p^(1−s))` is continuous near `1/2`: its summands
are dominated by `2p^(−5/4)` on `[1/4,3/4]`. Since `E(1/2)=λ`,
choose `s>1/2` with `E(s)<a²`. Put `c=a−√(a²−E(s))>0`.
Local Green identities give `A h_s≤E(s)h_s`.

Positive finite Dirichlet root iterations, using `E(s)+c²=2ac`,
give the barrier bound. Strong convergence of the finite sections transfers
it to the full operator `R=aI−√(a²I−A)` acting on actual square-summable
charges. No global square-summability of `h_s` is assumed.
For distinct finite vertices, the identity entry in `exp(rR)` vanishes.
Consequently, including the Robin extension at `r=0`,

`0≤K_reg(r;x,y)≤c h_s(x,y)/(4π)` for all `r≥0`, `x≠y`.

Submultiplicativity of the local matrix norm gives
`H(x,y)H(y,z)≤H(x,z)` for `H=finiteGreenProduct`. On the base orbit,
`H(base,q·base)=1/(|num(q)| den(q))`, for either sign of `q`.
Transport and raising to `2s` give the full-carrier bound

`h_s(x,q·y)≤[H(base,x)H(y,base)]^(−2s) (|num(q)| den(q))^(−2s)`.

The reduced numerator-denominator embedding bounds its sum by the product
of integer and natural power series, convergent because `2s>1`.
Equal-finite-vertex terms have profile one, so they form a finite exceptional
set. The uniform Green bound proves absolute summability off that set;
the finitely many exceptional terms have defined Green or Robin values.

The actual adjacency, positive root, exponential, and regularized kernel
commute with adelic isometries. Reindexing the orbit sum by left and right
multiplication proves invariance in both arguments; inversion proves
symmetry. These identities construct the kernel on
`T(ℚ) \ (ℍ³ × Π'_p PGL₂(ℚ_p)/PGL₂(ℤ_p))`.

## Lean declarations

Namespace `GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen`.
Modules in `formal/GaloisForLFunctions/HyperbolicArakelovTheory/`:

- `TheWeightedAdelicProductAdmitsStrictlyTemperedBarriers.lean`:
  `barrierExponent_gt_half`, `barrierEnergy_lt`, `adjacency_barrierProfile_le`.
- `TheHyperbolicGreenKernelHasUniformAdelicDecay.lean`:
  `rootRemainder_charge_bound`, `regularizedMixedEntry_bound`.
- `TheRationalTorusHasSummableAdelicProfiles.lean`:
  `product_base_rationalTorus`, `summable_powerProfile_rationalTorus`,
  `finite_rationalTorus_equal_fibres`.
- `TheHyperbolicGreenKernelRespectsAdelicIsometries.lean`:
  `regularizedMixedKernel_smul`, `regularizedMixedKernel_symm`.
- `TheWeightedHyperbolicGreenKernelDescendsToTheRationalTorus.lean`:
  `summable_norm_torusGreen`, `torusGreenSum_left`, `torusGreenSum_right`,
  `torusQuotientGreen`, `torusQuotientGreen_symm`.

All production modules pass plain `lake --old env lean`; audited declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

This is the standard branch of the specified weighted operator. The theorem
proves torus descent and absolute convergence with a termwise Robin prescription;
it does not yet identify that prescription as the global diagonal finite part.
It asserts neither an integral inverse on the full rational `SL₂` quotient
nor identification with Weil's diagonal. The accepted invariant-gluing
obstruction remains in force.
