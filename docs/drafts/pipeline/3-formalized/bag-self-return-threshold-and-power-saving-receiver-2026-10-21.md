# BAG: the self-return threshold is the distance to nonvanishing targets; power-saving receiver

**Route:** BAG (deterministic ζ self-return). **Obstacle attacked:** the self-target at a point
not known to be zero-free (review-2110 O5: "exclude a zero from the disc, no intermediate
estimate"). **Status:** formalized 2026-10-21. **Module:**
`formal/GaloisForLFunctions/RHTower/ZetaSelfReturnThresholdIsTheDistanceToNonvanishingTargets.lean`
(wired into the RHTower umbrella; `lake env lean` clean, no warnings; axioms
`propext, Classical.choice, Quot.sound`; lint clean).

## Statements (all unconditional)

Let `D = closedBall z₀ r`, `zetaReturnSet D ε = {τ : sup_D |ζ(s+iτ) − ζ(s)| < ε}`.
`nonvanishingDiscTargets z₀ r` = functions analytic and nonvanishing on a neighbourhood of `D`;
`zetaNonvanishingDistance z₀ r` = `d` = infimum of the tolerances `ε` with some target within
`ε` of `ζ` uniformly on `D`.

1. **Above the threshold** (`exists_pos_density_zetaReturnSet_of_distance_lt`): doubled disc in
   the strip, `d < ε` ⟹ the `ε`-self-returns have positive lower density (universality on small
   discs applied to a target within `ε₁ < ε`; triangle inequality).
2. **Below the threshold** (`exists_zero_of_mem_zetaReturnSet_of_lt_distance`): `ε < d` ⟹ every
   `ε`-self-return height carries a zero of `ζ` in `D + iτ` (else `ζ(·+iτ)` is an admissible target).
   Hence (`zetaReturnSet_subset_shadow_of_lt_distance`) the returns lie in the zero shadow
   `zetaZeroShadow (Re z₀ − r) 2`, and by Ingham–Huxley
   (`exists_volume_zetaReturnSet_window_le_rpow_of_lt_distance`,
   `exists_volume_zetaReturnSet_le_rpow_of_lt_distance`) `|zetaReturnSet D ε ∩ [0,T]| ≤ T^θ`,
   `θ < 1`, for large `T`.
3. **Threshold = zero-freeness** (`zetaNonvanishingDistance_eq_zero_iff`): `d = 0 ⟺ ζ ≠ 0` on the
   open disc. (`⟸`: scaled copies `ζ(z₀ + λ(z − z₀))`, `λ ↑ 1`, are admissible and converge
   uniformly; `⟹`: a zero inside forces every admissible target to a zero by the minimum modulus
   principle on an isolating circle, so `d ≥ m/2`.)
4. **Dichotomy** (`zetaReturnSet_volume_dichotomy`): linear in `T` above `d`, at most `T^θ` below
   `d`. No intermediate regime exists.
5. **Strong recurrence = threshold zero = open disc zero-free**
   (`zetaDiscStronglyRecurrentOn_iff_distance_eq_zero`,
   `zetaDiscStronglyRecurrentOn_iff_forall_ball_ne_zero`), for discs with doubled closure in the
   strip. Sharpens the corpus forms (`∃ r` / zero-free on a larger ball).
6. **Power-saving receiver** (`riemannZeta_ne_zero_iff_zetaReturnSet_not_powerSaving`):
   `ζ(z₀) ≠ 0 ⟺ ∃ r` (doubled margin) `∀ ε > 0 ∀ θ < 1`, `|zetaReturnSet D ε ∩ [0,T]| > T^θ`
   infinitely often. The old receiver needed positive (upper) density; now beating any fixed
   power `T^θ` suffices.
7. **Zero case** (`exists_volume_zetaReturnSet_le_rpow_of_zero`): around an off-line zero the
   self-returns are power-saving rare (sharpening `exists_zetaSelfReturn_density_zero`).

Reusable: `exists_forall_volume_inter_Icc_zero_le_rpow_of_window` (dyadic power-saving window
bounds give prefix bounds), `volume_inter_Icc_le_three_windows` (translated sets on dyadic
windows), `exists_pos_ball_ne_zero_of_closedBall` (nonvanishing on a closed disc extends to a
neighbourhood), `eventually_rpow_lt_const_mul_atTop`.

## What the obstacle looks like now

The self-target obstacle is exactly `d(z₀, r) = 0`: `ζ|_D` must be a uniform limit of functions
analytic and nonvanishing near `D`. Hurwitz's theorem is the whole obstruction (a zero inside
`D` keeps every such limit away by half the minimum modulus on an isolating circle). The orbit
`ζ(·+iτ)` supplies exactly the nonvanishing approximants that exist (universality), so the
receiver cannot be lowered below "beat `T^θ` infinitely often": below the threshold the
self-returns are shadows of nearby zeros and Ingham–Huxley caps them at `T^θ`.

## Modules (all wired into `GaloisForLFunctions.RHTower`, `lake env lean` clean, axioms standard)

1. `ZetaSelfReturnThresholdIsTheDistanceToNonvanishingTargets` — threshold law, dichotomy,
   power-saving receiver.
2. `ZetaSelfReturnThresholdReadsTheVanishingOrder` — `d(z₀,r) ≍ r^{ord}`.
3. `ZetaOrbitApproachesEveryAnalyticTargetWithTheHurwitzThreshold` — every analytic target.
4. `ZetaTwistedDirichletHeadsNearAZeroHaveVanishingHaarMass` — twisted heads, Haar mass → 0.
5. `ZetaTwistedDirichletHeadsApproximateZetaWithPositiveHaarMassIffZeroFree` — Haar mass bounded
   below iff zero-free; explicit decay; RH ⟺ Haar-mass law.

## Conjecture log

- C1 threshold law: **proved** (items 1–5).
- C2 power-saving receiver: **proved** (items 6–7).
- C3 vanishing-order law: **proved** 2026-10-21 in
  `formal/GaloisForLFunctions/RHTower/ZetaSelfReturnThresholdReadsTheVanishingOrder.lean` (wired,
  axioms standard): at a zero `z₀` of order `D = analyticOrderNatAt ζ z₀ ≥ 1` with cofactor `g`
  (`exists_zeta_local_factorization`, Mathlib `AnalyticAt.analyticOrderAt_ne_top`), for all small
  `r` the disc has doubled closure in the strip and
  `|g(z₀)|/4 · r^D ≤ d(z₀,r) ≤ 4·3^D·|g(z₀)|·r^D`
  (`exists_vanishingOrder_bounds_zetaNonvanishingDistance`; lower bound: minimum modulus on the
  circle of radius `r` via `half_le_zetaNonvanishingDistance_of_sphere`; upper bound: the admissible
  target `(z − z₀ − 2r)^D g` via `zetaNonvanishingDistance_le_of_target`). Hence the threshold
  exponent `log d/log r → D` reads the multiplicity, and `zetaReturnSet_volume_dichotomy_at_zero`:
  returns are `≤ T^θ` for `ε < |g(z₀)| r^D/4` and of positive lower density for
  `ε > 4·3^D|g(z₀)| r^D`.
- C4 general analytic targets: **proved** 2026-10-21 in
  `formal/GaloisForLFunctions/RHTower/ZetaOrbitApproachesEveryAnalyticTargetWithTheHurwitzThreshold.lean`
  (wired, axioms standard): `targetNonvanishingDistance h z₀ r` (Hurwitz distance of any target),
  `zetaTargetReturnSet_volume_dichotomy` (linear above, `≤ T^θ` below, for every target continuous
  on the closed disc), `targetNonvanishingDistance_eq_zero_iff` (analytic `h ≢ 0`: distance zero iff
  no zero in the open disc; identity theorem on the ball + minimum modulus on a small circle via
  `exists_sphere_norm_ge_of_analyticAt_of_not_eventually_zero`), and the universality law with its
  exact threshold `exists_pos_density_zetaTargetReturnSet_iff_forall_ne_zero`. Reusable:
  `exists_volume_le_rpow_of_subset_zetaZeroShadow` (any set carried into the zero shadow by a
  translation is power-saving rare).
- C5 twisted heads: **the emptiness version is not implied** (a set of phases of vanishing Haar
  mass can still be nonempty for every `M`); the true statement was **proved** 2026-10-21 in
  `formal/GaloisForLFunctions/RHTower/ZetaTwistedDirichletHeadsNearAZeroHaveVanishingHaarMass.lean`
  (wired, axioms standard): `primePhaseTwist ω n = ∏_{p∣n} ω(p)^{v_p(n)}` (continuous, unimodular,
  equal to `n^{−iτ}` along the prime phase flow), `twistedDirichletHead M ω = edPoly (primePhaseTwist ω) (Icc 1 M)`,
  `twistedHeadPhaseSet M D ε` (open; `headTargetReturnSet = flow⁻¹' twistedHeadPhaseSet`).
  **`eventually_torusHaar_twistedHeadPhaseSet_le`**: for `ε < d(z₀,r)` and every `δ > 0`, the Haar
  mass of the phases under which the length-`M` twisted head is within `ε` of `ζ` on the disc is
  `≤ δ` for all large `M` (Kronecker–Weyl lower density of visits + head-target ⊆ tail-bad ∪
  self-return, self-return `≤ T^θ`, tail-bad density `≤ δ/2`). Zero-free open disc ⟹ the phase set
  is nonempty for all large `M` (`eventually_nonempty_twistedHeadPhaseSet_of_zeroFree`). Around an
  off-line zero: `exists_eventually_torusHaar_twistedHeadPhaseSet_le_of_zero`. Twisted heads can
  vanish, so this is not Hurwitz: it is the zero-density theorem acting on finite Dirichlet
  polynomials. The uniform lower bound and the RH equivalence were **proved** the same day in
  `formal/GaloisForLFunctions/RHTower/ZetaTwistedDirichletHeadsApproximateZetaWithPositiveHaarMassIffZeroFree.lean`
  (wired, axioms standard): `le_torusHaar_twistedHeadPhaseSet_of_density` (a Urysohn function
  `1_{U(ε/2)} ≤ ψ ≤ 1_{U(ε)}` on the prime torus, `exists_continuous_zero_one_of_isClosed`, turns
  the lower density of visits into the Haar integral via `tendsto_windowAverage_primeFlow_real`),
  `exists_pos_forall_eventually_torusHaar_twistedHeadPhaseSet_ge` (zero-free open disc ⟹
  `Haar(U_M(ε)) ≥ c > 0` for all long heads), `torusHaar_twistedHeadPhaseSet_le_tailMass` and
  `torusHaar_twistedHeadPhaseSet_le_rpow` (below the threshold:
  `Haar(U_M(ε)) ≤ 28K ε'^{−2}·tailMass(M, Re z₀−2r) = O((M+1)^{1−2(Re z₀−2r)})`, from the corpus
  explicit fixed-`M` tail density `eventually_volume_discTailBadSet_le_tailMass`), and
  **`riemannHypothesis_iff_forall_twistedHeadPhaseSet_haar_pos`**: RH ⟺ on every strip disc with
  doubled closure in the strip and for every `ε > 0`, the Haar mass of the prime phases under
  which the twisted length-`M` head is within `ε` of `ζ` on the disc is bounded below by a positive
  constant for all long heads. So RH is a statement about *random completely multiplicative
  twists of finite Dirichlet polynomials*: the probability that a random twist of the head of
  length `M` reproduces `ζ` on a disc stays bounded below (RH) or decays like the Carlson tail mass
  (a zero inside).
