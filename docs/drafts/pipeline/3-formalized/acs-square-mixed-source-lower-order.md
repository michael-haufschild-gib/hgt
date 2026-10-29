# Uniform finite heads for the mixed square-prime source

- **ID:** acs-square-mixed-source-lower-order
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The actual even-power coarse/detail mixed source has arbitrarily small tails in the original complete-profile Gamma energy, uniformly in horizon.

## Exact theorem

Let `S₂(f)=squarePrimeSource f`, the full even-power source, and set
`B₂(q,d,X)=S₂(g+h)-S₂(g)-S₂(h)` for the actual complete profiles.
For every ε>0 there is one fixed A≥1 such that

`|B₂(q,d_tail,X)|≤εΓ(completePairProfile q d X)`

for all q,d,X, where `d_tail(a)=1_(A≤a)d_a`.
The controlling Gamma energy is that of the original d.

This lets the joint full-detail payment in
[the verified coarse-reserve theorem](../3-formalized/acs-full-detail-payment-with-coarse-reserve.md)
absorb the remaining square mixed block, without spending the whole square
source's separate Gamma reserve again. The resulting
[joint payment](acs-joint-nonfirst-mixed-payment.md) covers every mixed
exponent at least two and has uniformly bounded negative dimension.
First-prime mixing, coarse signed terms, polar cross terms and finite heads
remain outside that subform.

## Checked corpus inputs

- `ArithmeticIndexDescent/TheSquarePrimeBoundaryHasAGammaGap.lean`:
  `squarePrimeRegularSymbol(t)=2 Re zetaLogDerivReg(1+2it)`.
- `RHTower/Sieve/VinogradovKorobovLogDeriv.lean`:
  the two-sided zero-free strip is proved, but the existing logarithmic
  derivative bound is `C log(t)/w(t+1)`. This bound is too large to imply
  a lower-order Gamma multiplier.
- `RHTower/Sieve/VinogradovZetaGrowth.lean`:
  `norm_riemannZeta_le_vinogradovKorobov` gives `|ζ(σ+it)|≤C log t`
  on its explicitly wider growth strip.
- `ArithmeticIndexDescent/CompleteCellAveragesAreBoundedInGammaEnergy.lean`:
  the original Gamma energy controls coarse Gamma and weighted detail mass.
- `ArithmeticIndexDescent/GammaBoundedCompleteProfilesHaveCompactDetails.lean`:
  exact reciprocal-width control of tail square mass in the original source.

## Mechanism and verification status

1. Use the polylogarithmic zeta growth bound inside the zero-free strip,
   and the three-four-one lower bound at a centre to the right of one, to
   sharpen the logarithmic derivative estimate to `O(log log t / w(t))`.
   This step passed Lean verification; see
   [the sublogarithmic input card](../3-formalized/acs-square-boundary-sublogarithmic-input.md).
   The existing `C log t / w(t+1)` theorem does not supply this step.
2. The absolute regular square multiplier is now proved
   `o(gammaIncrementSymbol)` at infinity:
   `exists_squarePrime_regular_abs_le_epsilon_gamma` in
   `TheSquarePrimeBoundaryIsLowerOrder.lean` passed its direct Lean check.
3. Pair averages and details are orthogonal in ordinary square mass. Subtract
   the constant multiplier at zero from the mixed pairing. Its local analytic
   vanishing gives a low-frequency estimate by `C sqrt(Γ(g)∫h²)`, avoiding
   an uncontrolled coarse square-mass term. The
   [centred multiplier proof](../3-formalized/acs-centered-square-boundary-gamma-mass-bound.md)
   passed its direct Lean check.
4. Split low and high frequencies, use the existing homogeneous projection
   bounds and the detail tail mass bound, then transfer the exact physical
   square source including its mean pole. The detail mean is zero, so the
   mean-pole mixed term vanishes.

## Mixed-form reduction

Write m for the regular square multiplier and γ for the Gamma increment.
Set `Q(f)=S₂(f)−(∫f)²/2−m(0)∫f²`. For every η>0, the formalized
physical-source theorem gives one Cη such that all compact BV f,h satisfy

`|Q(f+h)−Q(f)−Q(h)|≤η(Γf+Γh)+Cη∫h²`.

High frequencies use `|m−m(0)|≤δγ`. At low frequencies, differentiability
of m gives `m(t)−m(0)=O(t)`, while the first positive term in the Gauss
digamma difference gives `γ(t)≥c_R t²` on every fixed compact interval.
Thus `|m−m(0)|≤K_R sqrt γ` there. Pointwise Young's inequality absorbs
the coarse Fourier factor into ηΓf, leaving only detail square mass.
Apply the smooth Fourier identity first; transfer the inequality through
the existing pole-preserving smoothing. Orthogonality need only hold for
the final original profiles, because the mean and square-mass
corrections remain explicit throughout smoothing.

For actual averages and details, ∫h=0 and ∫fh=0. Existing homogeneous
projection bounds control Γf+Γh in the original full profile, and tail
detail mass tends uniformly to zero in that same energy. This proves
the target without requiring a uniform bound on coarse ordinary mass.

Useful exact inputs: `Complex.hasSum_digammaRealDifferenceTerm`,
`Complex.digammaRealDifferenceTerm_nonneg`,
`tendsto_poleSmooth_squarePrimeSource`, `tendsto_poleSmooth_levyEnergy`,
`tendsto_poleSmooth_square_mass`, `tendsto_poleSmooth_mean`.

All components passed direct Lean checks. The
[physical BV mixed-source proof](../3-formalized/acs-centered-square-source-gamma-mass-bound.md)
and [uniform arithmetic tail proof](acs-square-mixed-source-uniform-tail.md)
record their exact declarations and commands. The final source theorem is
`exists_uniform_small_squarePrimeMixed_tail` in
`ArithmeticIndexDescent/TheMixedSquareSourceHasUniformSmallTails.lean`.
No web search, novelty checks, numerical experiments or axiom checks.
