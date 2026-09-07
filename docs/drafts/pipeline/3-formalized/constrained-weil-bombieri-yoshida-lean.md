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

## Recurrent exponential negativity for an attained top excess (added 2026-09-08, Lean)

`ConstrainedWeilApertureWindowMean` (wired; imports `ConstrainedWeilApertureDecay` and
`XiEndpointStrongHeightGap` for `|ordinate| > 9/2`):

* `nine_halves_le_abs_re_xiSpectralPoint`, `xiSpectralPoint_re_ne_zero` (from `xiDivisorSupport_fortyOne_div_two_lt_im_sq`).
* `profileMass_plateauProfile_le : ∫|ψ_a| ≤ 2a`.
* `normalizedTwistedForm Θ γ a := Σ'_q Re eval(normalizedRayTermPoly Θ γ q) a`;
  `normalizedTwistedForm_eq : S(a) = e^{−2Θa} Re Q(cos(γx)ψ_a)` for `a ≥ ½`;
  `abs_re_eval_normalizedRayTermPoly_le` (uniform bound `4B²/‖z_q‖²` on `[½, B]`);
  `continuousOn_normalizedTwistedForm`.
* `integral_normalizedTwistedForm_eq_tsum` (interchange, via `integral_tsum_of_summable_integral_norm`),
  `summable_integral_re_eval`, `integral_re_eval_le` (per copy: `∫_A^{A+L} Re eval ≤ L·Re constTerm + 2·decayNorm`).
* `topCentreSet Θ γ` (top height, ordinate `±γ`), `finite_topCentreSet`; `topKappa`, `topConstant Θ γ =
  (1/4)κ(Θ)²(γ² − Θ²)/(γ² + Θ²)²`, `topConstant_pos`; `re_inv_sq_of_sq_eq`;
  `re_constTerm_of_mem_topCentreSet` (`= −topConstant`), `constTerm_eq_zero_of_not_mem_topCentreSet`;
  `tsum_re_constTerm_le : Σ'_q Re constTerm_q ≤ −topConstant`.
* `decayTotal`, `summable_decayNorm_top`; **`integral_normalizedTwistedForm_le`**:
  `∫_A^{A+L} S ≤ −c L + 2D` for `A ≥ ½`, `L > 0`.
* **`exists_normalizedTwistedForm_le_of_attainedTop`**: `L > 4D/c ⟹ ∃ a ∈ [A, A+L], S(a) ≤ −c/2`;
  **`exists_aperture_twistedOddTest_neg_of_attainedTop`**: `∃ c > 0, ∃ L₀ > 0, ∀ A ≥ ½, ∀ L ≥ L₀, ∃ a ∈ [A, A+L],
  Re Q(cos(γ₀x)ψ_a) ≤ −c e^{2Θa}`. STATUS MUST-259.

Traps: `setIntegral_const` now yields `μ.real s • c` (unfold `Measure.real`, then `Real.volume_Icc`);
`continuousOn_tsum` needs `(f := …)` and `(u := …)` explicitly; `integral_tsum_of_summable_integral_norm`
works on `volume.restrict (Ioc A B)` after `simp_rw [intervalIntegral.integral_of_le]` on both sides;
`lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _)` turns `(9/2)² < |x|²` into `9/2 < |x|`; `hcont.intervalIntegrable_of_Icc`
for a `ContinuousOn` on `Icc`. The ordinate bound `41/2 < (Im ρ)²` is corpus-owned (`XiEndpointStrongHeightGap`).

## Exponential decay of the pole-vanishing ground energy (added 2026-09-08, Lean)

Five further modules (all wired into `RHTower.lean`, axioms clean):

* `ConstrainedWeilPlateauSecondOrder` — the edge `τ(4·)` is flat at `0` and `1/4` (`deriv_plateauEdge_zero`,
  `deriv_plateauEdge_quarter`, by `IsLocalMin/IsLocalMax.deriv_eq_zero`); second integration by parts
  `plateauKappa_eq₂ : κ(c) = (1/c²)∫_0^{1/4}(edge)''e^{−cs}`, `plateauRho_eq₂`; `exists_plateau_coeff_bound₂ :
  ∃ M₂ ≥ 0, ∀ c ≠ 0, ‖κ(c)‖, ‖ρ(c)‖ ≤ M₂e^{|Re c|/4}/‖c‖²`; global edge-derivative bound `K`; derivative of the
  plateau profile `plateauProfileDeriv` with `|·| ≤ 4K`.
* `ConstrainedWeilPolarDerivativeTest` — `SuzukiSmoothZeroMeanTest.polarDerivativeTest φ := φ'' − φ/4` (zero mean
  since `∫φ'' = 0 = ∫φ`); `suzukiTestRayCoef_polarDerivativeTest : Coef(Dφ) = −(z² + ¼) Coef(φ)` and the `Bar`
  version (two ibp via `testTransform_ibp_two`; conjugation commutes with `deriv` via `Complex.conjCLE`);
  `suzukiScrewSmoothForm_polarDerivativeTest : Q(Dφ) = Σ'(z_q²+¼)² Bar·Coef/z_q²`; the source
  `polarDerivativeSource φ A hA := (zeroMeanPrimitiveSource).polarMultiplier` (corpus `D`-operator source),
  polar-constrained, with derivative test `Dφ` (`deriv_polarDerivativeSource`); **transfer**
  `polarGroundEnergy_mul_le_re_smoothForm_polarDerivativeTest : μ₀(A)‖DΦ‖² ≤ Re Q(Dφ)`;
  `norm_sq_toAperture_eq_integral` (aperture norm = `L²` norm); `norm_sq_twistedPlateau_polarDerivativeSource_le :
  ‖DΦ_a‖² ≤ 2a(|γ| + 4K + (2a+1)/4)²`.
* `ConstrainedWeilWeightedRayBounds` — `dWeight q = (z_q²+¼)²`, `freqConst γ q = 1/‖c₁‖² + 1/‖c₂‖²`;
  second-order moment bound `norm_twistedMoment_plateau_le₂ : ‖A(b,μ)‖ ≤ 4M₂e^{Θ/4}e^{aΘ}/‖c‖²`;
  `rayMajorant M Θ γ q = 4M₂²e^{Θ/2}‖w_q‖κ_q²/‖z_q‖²` bounds `‖Re eval(w_q P_q)(a)‖` uniformly in `a ≥ ½`
  (`norm_re_eval_weightedRayPoly_le`); `summable_rayMajorant` (far copies `|Re z_q| ≥ 2|γ|`: `≤ 4096M₂²e^{Θ/2}/‖z_q‖²`;
  the rest finite); `coeffSum_shiftedPairPoly_le₂`, `decayNorm_weightedRayPoly_le_far`, `summable_decayNorm_weightedRayPoly`.
* `ConstrainedWeilPolarGroundDecay` — `weightedTwistedForm Θ γ a = Σ' Re eval(w_q P_q)(a) = e^{−2Θa}Re Q(D(cos γx ψ_a))`
  (`weightedTwistedForm_eq`); interchange, per-copy window bound; weighted constant terms
  `re_constTerm_weighted_of_mem_topCentreSet : = −topConstantD Θ γ` with
  `topConstantD = (1/4)κ(Θ)²((γ²−Θ²) + ½ + (γ²−Θ²)/(16(γ²+Θ²)²))` (`dWeight_div_sq : (z²+¼)²/z² = z² + ½ + (1/16)(z²)⁻¹`);
  `integral_weightedTwistedForm_le : ∫_A^{A+L} S_w ≤ −c_D L + 2D_w`; `exists_weightedTwistedForm_le_of_attainedTop`;
  `polarGroundEnergy_apertureSucc_le : μ₀(a+1) ≤ −(c_D/2)e^{2Θa}/(2a(|γ|+4K+(2a+1)/4)²)` at the recurrent apertures;
  **`polarGroundEnergy_le_neg_exp_of_attainedTop`**: `∃ c' > 0, ∃ B₀ ≥ 1, ∀ B, B₀ ≤ B.1 → μ₀(B) ≤ −c'e^{2ΘB.1}/B.1³`.
  STATUS MUST-260.

Traps: `MeasureTheory.integral_div`/`integral_const_mul`/`integral_congr_ae` are ambiguous with the `intervalIntegral`
versions once both namespaces are open — qualify them; `HasDerivAt.comp_neg` does not exist (use `comp_const_sub 0`);
`(hd1.add hd2).deriv` needs the lambda-sum form stated explicitly; `gcongr` side goals `0 ≤ M` appear when a
multiplicative constant is not visibly nonnegative (keep `hM` in the signature only where such a goal arises);
`linear_combination (-(1/16)) * hinv` with `hinv : (z²)⁻¹ * z² = 1` closes the weight identity.

## Exponential lower bounds cap the attained excess (added 2026-09-08, Lean)

`ConstrainedWeilPolarGroundDecay.two_mul_attainedExcess_le_of_polarGroundEnergy_ge`: if
`−C e^{εB} ≤ μ₀(B)` for every aperture `B`, then every attained excess `Θ` satisfies `2Θ ≤ ε`
(from MUST-260 and `exists_cube_mul_exp_neg_lt`: `B³e^{−δB} → 0`). STATUS MUST-261. The non-attained
case is the quantitative Bombieri–Yoshida, planned on `lag-ratio-law.md`.

## Quantitative Bombieri–Yoshida (added 2026-09-08, Lean)

Three modules (wired into `RHTower.lean`, axioms clean):

* `WeightedScrewLandauEngineThreshold` — `thrDivisor W C₀ ε t = Φ_W(t) + C₀e^{εt}`, `thrDensity`, `thrMeasure`,
  `ThrMomentsAbove W C₀ ε b`; `thrLaplace`, `thrContinuation = weightedScrewLaplaceContinuation + C₀/(s − ε)`;
  `integral_Ioi_cexp_neg_mul_exp : ∫₀^∞ e^{−st}e^{εt} = 1/(s − ε)` (`Re s > ε`);
  `thrLaplace_eq_continuation` (`Re s > ½`); `thrRadius ε r = min(r/2, (r−ε)/2)`,
  `differentiableOn_thrContinuation_ball`; `thrStrip ε b` (convex, hence preconnected);
  `thr_landau_integrable_transfer`, `thrMomentsAbove_half : b ↦ (b + ε)/2`, `thrThreshold ε n = ε + (½ − ε)/2ⁿ`,
  `thrMomentsAbove_eps`, **`analyticOnNhd_thrLaplace_gt_eps`** (analytic on `Re s > ε`).
* `WeightedScrewPoleContradictionThreshold` — `thrPunctured ε = {Re s > ε} ∖ spectralPoleSet`, connected via
  the shifted chart `thrChart ε u = ε + rightHalfPlaneChart u`; `thrLaplace_eqOn_punctured`;
  **`neg_le_im_of_thr`** (no copy with `Im z_q < −ε`, by the corpus pole-contradiction pattern with the extra
  term `c_n C₀/(s_n − ε) → 0`), **`abs_im_le_of_thr`** (both signs by `xiZeroCopyReflectEquiv`).
* `CCMRestrictedWeilPolarBombieriYoshidaQuantitative` — `norm_zeroMeanPrimitive_le_integral_norm`;
  `twoBumpSource t n` (polar translate of the primitive of the two-bump test at aperture `|t| + 3`, enlarged to
  `|t| + 6`), `norm_twoBumpSource_le` (pointwise `10(1 + cosh ½)`), `norm_sq_twoBumpSource_le`
  (`≤ 200(1 + cosh ½)²(|t| + 4)`); `re_smoothForm_twoBump_ge` (ground-energy transfer with the exponential
  bound), `re_weightedXiScrewDivisor_polar_ge` (limit `n → ∞`), `one_add_le_exp_div`;
  `abs_im_le_add_of_polarGroundEnergy_ge`, **`abs_im_xiSpectralPoint_le_of_polarGroundEnergy_ge`**,
  **`riemannHypothesis_of_polarGroundEnergy_subexponential`**. STATUS MUST-262.

Traps: `Filter.Tendsto.const_mul_atTop_of_neg` for `e^{ct} → 0` with `Re c < 0`; `integral_Ioi_of_hasDerivAt_of_tendsto'`
wants `HasDerivAt` on `Ici`; `-(1/(ε − s)) = 1/(s − ε)` via `show ε − s = −(s − ε)` then `div_neg, neg_neg`;
`fin_cases k <;> simp [...] <;> first | (constructor <;> linarith) | linarith` needs both `cosh (1/2)` and
`cosh 2⁻¹` forms of `one_le_cosh` in context; `rw [h]` closes `≤`/`=` goals by `rfl`, so a following `<;> simp`
is flagged — use bullets.

## Prime-side landing: `RHTower/SuzukiScrewSubexponentialCriterion.lean`

The threshold engine with the constant weight `W ≡ 1` lands on Suzuki's unweighted screw function
`Ψ(t) = Σ'_q (1 − cos(z_q t))/z_q²`, which is real (`xiScrewDivisor_im_eq_zero`) and equals the
explicit smooth part minus the prime hinge sum on `t ≥ 0`
(`suzukiPsi_eq_smoothPart_sub_screwPrimeSum`).

- `weightedXiScrewDivisor_one`; `abs_im_xiSpectralPoint_le_of_suzukiPsi_ge` (rate `ε < 1/2`),
  `abs_im_xiSpectralPoint_le_of_suzukiPsi_ge'` (any `ε ≥ 0`, via `|Im z_q| < 1/2`);
  `SuzukiPsiSubexponentialBelow`; `riemannHypothesis_of_suzukiPsiSubexponentialBelow`,
  `suzukiPsiSubexponentialBelow_of_riemannHypothesis`, **`riemannHypothesis_iff_suzukiPsiSubexponentialBelow`**;
  **`abs_im_xiSpectralPoint_le_of_screwPrimeSum_le`** (one-sided hinge-sum bound of rate `ε` ⟹ every zero
  in `|Re ρ − 1/2| ≤ ε`), **`riemannHypothesis_iff_screwPrimeSum_subexponential`**. STATUS MUST-263.

Trap: `screwPrimeSum` lives in `GaloisForLFunctions.RHTower`, not `RHTower`; qualify it fully.
Axioms `[propext, Classical.choice, Quot.sound]`; built as a leaf of `RHTower` (12332 jobs).

## Sharp cap: `RHTower/CCMRestrictedWeilPolarBombieriYoshidaSharp.lean`

Translation invariance of the screw form halves the two-bump aperture and the excess cap.

- `SuzukiSmoothZeroMeanTest.translate φ s hsupp hfit` (`x ↦ φ(x + s)` at any aperture containing the
  shifted support), `integral_exp_sub_one_mul_translate` (exponential moments of a zero-integral
  compactly supported function under translation), `suzukiTestRayCoef_translate` (factor `e^{i z_q s}`),
  `suzukiTestRayCoefBar_translate` (factor `e^{−i z_q s}`), **`suzukiScrewSmoothForm_translate`**,
  `coe_polarTranslateTest_translate` (the multiplier commutes with translation),
  `suzukiScrewSmoothForm_polarTranslateTest_translate`.
- `twoBumpSeq_support_subset` (support within one unit of the bump segment), `twoBumpFit`, `twoBumpSeqC`
  (centred test at aperture `|t|/2 + 2`), `twoBumpApertureC = |t|/2 + 3`, `twoBumpSourceC` (aperture
  `|t|/2 + 6`), `suzukiScrewSmoothForm_twoBumpSeqC`, `integral_norm_twoBumpSeqC_le`,
  `norm_twoBumpSourceC_le`, `twoBumpSourceC_support_subset`, `norm_sq_twoBumpSourceC_le`
  (`≤ 200(1 + cosh ½)²(|t|/2 + 4)`).
- `re_smoothForm_twoBump_ge_half`, `re_weightedXiScrewDivisor_polar_ge_half`,
  `abs_im_le_half_add_of_polarGroundEnergy_ge`, **`abs_im_xiSpectralPoint_le_half_of_polarGroundEnergy_ge`**
  (`|Im z_q| ≤ ε/2`), **`two_mul_abs_im_xiSpectralPoint_le_of_polarGroundEnergy_ge`**. STATUS MUST-264.

Traps: in `have hfun : (fun u : ℝ => …) = fun u => …` annotate the second binder too, otherwise
`w * u` elaborates `u : ℂ`; `push_neg` is deprecated in this toolchain (`push Not`); membership in
`Function.support` of a translate is closed by `simpa [Function.mem_support] using hx`.
Axioms `[propext, Classical.choice, Quot.sound]`.
