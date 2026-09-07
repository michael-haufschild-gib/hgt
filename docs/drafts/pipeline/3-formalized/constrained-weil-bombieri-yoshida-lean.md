# Bombieri–Yoshida for the constrained restricted Weil form (Lean)

**Stage:** 3 (formalized), 2026-09-04.  Modules (all wired into `RHTower.lean`, axioms
`[propext, Classical.choice, Quot.sound]`): `SuzukiPolarTranslateMultiplier`,
`SuzukiWeightedScrewTwoBumpLimit`, `WeightedScrewLandauEngine`, `WeightedScrewPoleContradiction`,
`CCMRestrictedWeilPolarBombieriYoshida`.

**Theorem** (`RHTower.riemannHypothesis_of_polarGroundEnergy_nonneg`).  If the pole-vanishing ground
energy `ccmRestrictedWeilPolarGroundEnergy A` of the CCM restricted Weil form is `≥ 0` at every
aperture `A`, then `RiemannHypothesis`.  Strict form `riemannHypothesis_of_polarGroundEnergy_pos`.
This closes MUST-144 of the Weil working log ("the link `μ₀ > 0 everywhere ⇒ RH` is Bombieri–Yoshida;
the corpus cannot currently formalize it").

## Proof architecture (all new)

1. **Polar translate multiplier.**  `M∗f = Σ_k μ_k f(· − τ_k)` with five symmetric translates
   (`τ ∈ {0, ±h, ±2h}`) and symbol `(cosh(zh) − 1)(cosh(zh) − cosh(h/2))`
   (`translateSymbol_polarMultiplier`), which kills the exponential moments at `z = 0, ±1/2`.  Hence
   `M∗u` is pole-vanishing for **every** smooth interior source `u` (`isPolarConstrained_polarTranslate`),
   and the derivative test `M∗u'` has Suzuki ray coefficients multiplied by
   `M(γ) = (cos γh − 1)(cos γh − cosh(h/2))` (`suzukiTestRayCoef_polarTranslateTest`).  The CCM quadratic
   of a smooth source is the real part of Suzuki's smooth form of its derivative
   (`ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm`).
2. **Twisted two-bump limit.**  `Q(M∗(b_t − b_0)) → 2Φ_h(t)`,
   `Φ_h(t) = Σ'_q M(γ_q)² (1 − cos γ_q t)/γ_q²` (`weightedXiScrewDivisor`), by dominated convergence over
   the zero copies (`tendsto_suzukiScrewSmoothForm_polarTranslateTest_twoBumpSeq`).  Constrained
   positivity at all apertures ⇒ `Φ_h ≥ 0` (`weightedXiScrewDivisor_polar_re_nonneg`); `Φ_h` is real by the
   Schwarz copy equivalence.
3. **Weighted Widder–Landau engine.**  The corpus's halving argument for `Ψ` re-proved for any bounded
   weight: `weightedScrewMomentsAbove_zero` (all exponential moments),
   `analyticOnNhd_weightedScrewLaplace_rightHalf`, termwise Laplace transform
   `weightedScrewLaplace_eq_continuation` (weighted atom series `Σ' W_q/(s(s²+γ_q²))`).
4. **Pole contradiction.**  The punctured half-plane `{Re s > 0} ∖ {±iγ_q}` is connected
   (`isPreconnected_rightHalfPunctured`: image of the complement of a countable set under the chart
   `u ↦ e^{Re u} + i Im u`); the atom series is analytic there
   (`analyticAt_weightedScrewContinuationExcept`, uniform majorant on small balls); identity theorem;
   along `s_n = s₀ + ρ/(n+2)` towards an off-line pole `s₀ = iγ₀`, `(s_n − s₀)G(s_n) → |E| W(γ₀)/(2s₀²) ≠ 0`
   while `(s_n − s₀)F(s_n) → 0` (`riemannHypothesis_of_weighted_positive`).
5. **Assembly** with `h = 1`: `M(γ) ≠ 0` for `0 < |Im γ| < 1/2` because `cos z = 1` or
   `cos z = cosh(1/2)` forces `Im z ∈ {0, ±1/2}` (`polarMultiplierSpectral_ne_zero`).

## What this changes

Every constrained-Weil statement of the corpus (Theorems C/D, the log-soft entry law, the degeneracy
alternative, Connes–Consani's √2 inequality) now lands at `RiemannHypothesis` in Lean; the O route
has a complete Lean chain from "positivity at all apertures" to RH.  The converse
(RH ⇒ constrained ground energy ≥ 0) is formal in `CCMRestrictedWeilPolarMultiplierCriterion`:
Suzuki smooth-test positivity and the exact same-aperture pole-multiplier image criterion give
`riemannHypothesis_iff_polarGroundEnergy_nonneg`. The support-preserving inverse and the
first-zero completion boundary are described in [the local-inverse card](weil-polar-local-inverse.md).

## Traps recorded

`push_neg` deprecated; `le_or_gt`; `pow_le_pow_left₀`; `Summable.tsum_le_tsum`; `Summable.tsum_add`;
`HasCompactSupport.mul_left` unification stalls (use `.mono`); `integral_sub_right_eq_self` needs the
function and measure explicit; zsh does not word-split `$VAR` (use arrays) — the first collision sweep
silently checked nothing; macOS `sed` has no `\b`.

## The twisted odd test law (added 2026-09-08, Lean, `ConstrainedWeilTwistedOddTest`)

For a real smooth odd profile `ψ` supported in `[−a, a]` (`OddSmoothProfile a`) and a centre `γ`, the
test `cos(γx)ψ(x)` is a `SuzukiSmoothZeroMeanTest a` (`twistedOddTest`; zero mean by oddness). With the
twisted moments `twistedMoment ψ b μ = ∫ e^{(b+iμ)u} ψ(u) du` and the pair moment
`twistedPairMoment ψ γ q = A(−Im z_q, Re z_q − γ) + A(−Im z_q, Re z_q + γ)` (`z_q = xiSpectralPoint q`,
`−Im z_q = Re ρ_q − ½`):

* `suzukiTestRayCoef_twistedOddTest : Coef_q = −½ · pairMoment`,
  `suzukiTestRayCoefBar_twistedOddTest : Bar_q = ½ · pairMoment` (odd symmetry
  `twistedMoment_neg_neg : A(−b, −μ) = −A(b, μ)`, conjugation `conj_twistedMoment : conj A(b, μ) = A(b, −μ)`).
* `suzukiScrewSmoothForm_twistedOddTest : Q(cos(γ·)ψ) = Σ'_q −(1/4) pairMoment_q² / z_q²` (exact,
  unconditional); `summable_suzukiTestRayEnergy` (any smooth zero-mean test) and
  `re_suzukiScrewSmoothForm_twistedOddTest` (real part termwise).
* Critical-line copies (`Im z_q = 0`): `twistedOddTest_rayTerm_of_im_eq_zero` — the term equals the real
  number `(Im pairMoment_q)²/(4 (Re z_q)²) ≥ 0`; hence
  `re_suzukiScrewSmoothForm_twistedOddTest_nonneg_of_forall_im_eq_zero`.
* Centred off-line copy: `twistedPairMoment_centre` — at `γ = Re z_q` the pair moment is
  `A(Re ρ_q − ½, 0) + A(Re ρ_q − ½, 2 Re z_q)` with the first term real (`twistedMoment_centre_im`).

This is the exact zero-side content of STATUS CANNOT-330: an off-line copy contributes
`−(1/4)(A + A')²/z_q²`, whose real part at the centre is `≈ −(1/4)(∫ e^{(Re ρ − ½)u} ψ)²/|z_q|²`, against
nonnegative critical-line terms. The transfer inequalities (isolated rate `(log log|γ| + log a + C)/(2a)`,
clustered Turán rate) remain paper. Trap: rewriting `xiSpectralPoint q = ↑re + ↑im·I` must be scoped with
`conv_lhs`, since the right-hand side mentions `(xiSpectralPoint q).re`; the exponent identities close by
`linear_combination (±↑im·↑u) * Complex.I_sq`.

## The negativity witness (added 2026-09-08, Lean, `ConstrainedWeilNegativityWitness`)

`re_suzukiScrewSmoothForm_twistedOddTest_le_of_topExcess`: for an odd profile `ψ` on `[−a, a]` and a copy
`q₀` with `z₀ = xiSpectralPoint q₀`, `Re z₀ ≥ 2`, `|Im z₀| ≤ Re z₀/32`, `Φ₊ := (twistedMoment ψ (−Im z₀) 0).re ≥ 0`,
second-frequency moment `‖twistedMoment ψ (−Im z₀) (2 Re z₀)‖ ≤ Φ₊/8`, and the gap hypothesis
`∀ q, z_q ≠ z₀ → z_q ≠ conj z₀ → |Im z_q| ≤ −Im z₀ − δ`:

`Re Q(cos(Re z₀ · x)ψ) ≤ −(9/50) Φ₊²/(Re z₀)² + e^{2a(−Im z₀ − δ)} · (∫|ψ|)² · S₂`, `S₂ = Σ_q ‖z_q‖⁻²` (`xiSpectralInvSqTotal`).

Supporting lemmas: `twistedMoment_eq_testTransform` (twisted moment = `HTGeometry.testTransform` at `μ − b i`),
`norm_twistedMoment_le` (trivial bound `e^{a|b|}∫|ψ|`), `norm_twistedMoment_le_div` (one integration by parts,
`e^{a|b|}‖ψ'‖₁/|μ|`, via `testTransform_ibp` and `norm_testTransform_le_exp`), `norm_twistedRayTerm_le`,
`twistedRayTerm_congr` / `twistedRayTerm_of_conj` (copies at `z₀` repeat the term, copies at `conj z₀` conjugate it),
`re_sq_div_sq_ge` (`Re((Φ+E)²/z²) ≥ (18/25)Φ²/(Re z)²` for `|E| ≤ Φ/8`, `|Im z| ≤ Re z/32`),
`re_twistedRayTerm_centre_le`. Reading: with `Φ₊ ≍ e^{a₀a}/a₀` and `∫|ψ| ≤ 2a`, the form is negative once
`e^{2δa} ≳ a₀² a² (Re z₀)² S₂`, i.e. a top excess gap `δ` is detected at aperture `a ≈ (log γ₀ + log a)/δ`;
this is the exact Lean content of CANNOT-330 (i) (with the global constant `S₂` in place of the local zero count).
Remaining to instantiate: the aperture-uniform plateau profile (`Real.smoothTransition` construction) supplying
`Φ₊ ≥ (e^{a₀(a−1/4)} − e^{a₀/4})/a₀ − 1/a₀`, `∫|ψ| ≤ 2a`, `‖ψ'‖₁ ≤ 4M₁`, and the discharge of the
second-frequency hypothesis from `norm_twistedMoment_le_div` for `Re z₀ ≥ 32 M₁ a₀ e^{a₀/4}`.
Traps: `linarith` treats `c * Φ^2 / r^2` with different `c` as unrelated atoms (state the scalar identity first);
`Summable.tsum_subtype_le` takes `(f) (s) (hf : ∀ i, 0 ≤ f i) (hs : Summable f)` explicitly;
`Complex.norm_ofReal` does not exist (use `Complex.norm_real` + `Real.norm_eq_abs`).

## Aperture averaging: plateau profile, exact moments, exponential polynomials (added 2026-09-08, Lean)

Modules (wired into `RHTower.lean` / `HTGeometry.lean`, axioms clean):

* `ConstrainedWeilPlateauProfile` — the odd plateau profile `ψ_a = h_a − h_a(−·)`, `h_a(u) = τ(4u)τ(4(a−u))`
  (`Real.smoothTransition`), as an `OddSmoothProfile a` (`plateauProfile`), with `|ψ_a| ≤ 1`, `ψ_a = h_a` on `u ≥ 0`,
  `h_a = 1` on `[1/4, a − 1/4]`. **Exact moments** for `a ≥ 1/2`, `c ≠ 0`:
  `∫ e^{cu} h_a = e^{ca} κ(c) + ρ(c)` (`integral_exp_mul_plateauBump`), hence
  `twistedMoment ψ_a b μ = e^{ca}κ(c) + ρ(c) − e^{−ca}κ(−c) − ρ(−c)`, `c = b + iμ` (`twistedMoment_plateauProfile`),
  with `κ(c) = ∫_0^{1/4} e^{−cs}τ(4s) + e^{−c/4}/c`, `ρ(c) = ∫_0^{1/4} e^{cu}τ(4u) − e^{c/4}/c`.
* `ConstrainedWeilPlateauBounds` — one integration by parts on the edge: `κ(c) = (1/c)∫_0^{1/4}(edge)'e^{−cs}`,
  `ρ(c) = −(1/c)∫_0^{1/4}(edge)'e^{cu}` (`plateauKappa_eq`, `plateauRho_eq`); `exists_plateau_coeff_bound`:
  `∃ M ≥ 0, ∀ c ≠ 0, ‖κ(c)‖, ‖ρ(c)‖ ≤ M e^{|Re c|/4}/‖c‖`; `plateauKappa_ofReal`: `κ(b)` real, `≥ e^{−b/4}/b`.
* `HTGeometry.ExponentialPolynomialWindowMean` — `ExpPoly = List (ℂ × ℂ)`, `eval`, `constTerm` (sum of
  coefficients at exponent `0`), `decayNorm` (`Σ_{λ≠0}‖C‖/‖λ‖`), `Decaying` (all `Re λ ≤ 0`), `mul`, `smul`,
  append; `norm_integral_sub_constTerm_le`: `‖∫_A^{A+L} eval − L·constTerm‖ ≤ 2·decayNorm` for `A ≥ 0`;
  `abs_windowMean_re_sub_le`: the real window mean is within `2·decayNorm/L` of `Re constTerm`.
* `ConstrainedWeilApertureAveraging` — `plateauMomentPoly c`, `rayPairPoly γ q`, `rayTermPoly γ q`,
  `normalizedRayTermPoly Θ γ q`: for `a ≥ 1/2`, `twistedRayTerm ψ_a γ q = eval (rayTermPoly γ q) a` and
  `eval (normalizedRayTermPoly Θ γ q) a = e^{−2Θa} · twistedRayTerm ψ_a γ q`; `decaying_normalizedRayTermPoly`
  when `|Im z_q| ≤ Θ`.

**Purpose.** In the aperture variable every ray term of the plateau profile is an exact exponential polynomial with
exponents from `{±c₁ − Θ, ±c₂ − Θ, −Θ}` (`c₁ = −Im z_q + i(Re z_q − γ)`, `c₂ = −Im z_q + i(Re z_q + γ)`).
When `Θ = max_q |Im z_q|` is attained at `q₀` and the test is centred at `γ = Re z₀`, the only exponent sums
equal to `0` come from the four copies `±z₀, ±conj z₀`, each contributing the constant term
`−(1/4)κ(Θ)²/z₀²` (real part `< 0`, since `κ(Θ) > 0` and `Re z₀⁻² > 0`); every other copy has constant term
`0` and its window mean tends to `0` at rate `2·decayNorm/L`, with `Σ_q decayNorm_q < ∞` from the coefficient
bounds and `Σ_q |z_q|⁻² < ∞`. Hence the window mean of `e^{−2Θa} Re Q(cos(Re z₀ · x)ψ_a)` tends to a negative
limit and the form is negative for some aperture: **attained top excess ⟹ twisted-family negativity, with no
isolation or gap hypothesis** (the clustered-zero obstruction of CANNOT-330 (ii) is removed by averaging in
the aperture instead of the centre). Remaining Lean steps: the constant-term identification (25 exponent-sum
cases), `Σ_q decayNorm_q < ∞`, the interchange of `Σ'_q` with the window integral, and the assembly.
