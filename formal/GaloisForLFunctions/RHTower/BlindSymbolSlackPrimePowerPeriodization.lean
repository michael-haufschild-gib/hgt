import GaloisForLFunctions.RHTower.BlindArchimedeanNodeTwoCertificate
import GaloisForLFunctions.RHTower.PrimeCirclePeriodization

/-!
# The blind symbol slack of a single prime is the period mean of the archimedean symbol

Write `γ(r) = Re ψ(¼ + ir/2) − log π` (`EF.gammaBracket`) and `ℓ = log 2`.  For a nonnegative
combination `c` of Weil tests whose autocorrelations vanish at every `log n`, the spectral density
`G = Σ c_f |f̂|²` has vanishing cosine moments at every `j ℓ` (the nodes `2^j`).

**Even periodization** (`integral_mul_periodic_eq_of_cos_blind`).  Vanishing cosine moments at all
multiples of `ℓ` make the phase `r ℓ mod 2π` of the symmetrized density uniform on the circle, so
every even continuous function `P` of the phase integrates to `(∫G) · mean(P)`.  This is the
cosine-only form of the corpus equidistribution theorem `integral_periodic_eq_of_blind`.

**The folded symbol.**  `γ` is even and increasing in `|r|` (vertical Gauss expansion,
`gammaBracket_le_of_abs_le`), so it dominates its fold `γ(‖r ℓ mod 2π‖/ℓ)` onto one period
(`foldedSymbol_phase_le`).  The circle mean of the fold is
`m₂ = (ℓ/π) ∫_0^{π/ℓ} γ` (`integral_foldedSymbol`).

**Theorems.**
* `twoPeriodMean_mul_massOf_le`: `m₂ · mass(c) ≤ A_sym(c)` for every blind nonnegative combination,
  where `A_sym = A − P` is the symbol integral without the pole.  Hence
  `blindSymbolSlack_twoPeriodMean : BlindSymbolSlack (−m₂)`.
* `twoPeriodMean_ge`: `m₂ ≥ γ(0) + 121/32`, from monotone left Riemann sums on a 32-point grid and
  eight Gauss terms.  So `blindSymbolSlack_two_powers : BlindSymbolSlack (−γ(0) − 121/32)`, a
  slack of about `1.59`, against `−γ(0) − 2 ≈ 3.37` from the single cosine `cos(r log 2)`.
* `nodePoleMass_lt_of_nodeArchEnergy_neg_twoPeriod`: a blind combination with negative pole and
  archimedean energy has pole mass below `(−γ(0) − 121/32)` times its mass.

**Reading.**
* `∫_0^R γ = 2θ(R)` with the Riemann–Siegel theta function, so
  `m₂ = (2 log 2/π) θ(π/log 2) ≈ −1.50`.
* The bound is sharp for blindness at the powers of `2` alone: densities close to uniform on one
  period `[−π/ℓ, π/ℓ]` approach it.  This is a paper remark, not formalized here.
* The same argument works for any prime `p`, with `π/log p` in place of `π/log 2`.  The prime `2`
  has the longest period and gives the best single-prime constant.
* The remaining slack is removed only by the pole constraint, which is the RH content
  (`riemannHypothesis_iff_forall_pos_zeroPoleBlindSymbolSlack`).
-/

open MeasureTheory Set Real Complex
open RHTower.PrimeCirclePeriodization Zeta23

namespace RHTower.BlindPrimePowerSlack

noncomputable section

theorem integrable_mul_bounded {G : ℝ → ℝ} (hGi : Integrable G) {F : ℝ → ℝ} (hF : Continuous F)
    {C : ℝ} (hC : ∀ r, |F r| ≤ C) : Integrable fun r => G r * F r := by
  have := hGi.bdd_mul (c := C) hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact hC r)
  simpa only [mul_comm] using this

/-- **Even periodization under cosine blindness.**  If a nonnegative integrable continuous density
has vanishing cosine moments at every multiple of `ℓ`, then every even continuous function of the
phase `t ℓ mod 2π` integrates against it to its circle mean. -/
theorem integral_mul_periodic_eq_of_cos_blind {G : ℝ → ℝ} (hGc : Continuous G)
    (hG0 : ∀ r, 0 ≤ G r) (hGi : Integrable G) {ℓ : ℝ}
    (hcos : ∀ j : ℕ, 1 ≤ j → ∫ r, G r * Real.cos (r * ((j : ℝ) * ℓ)) = 0)
    {P : AddCircle (2 * π) → ℝ} (hP : Continuous P) (heven : ∀ z, P (-z) = P z) :
    ∫ r, G r * P (phase ℓ r) = (∫ r, G r) * ∫ z, P z ∂AddCircle.haarAddCircle := by
  set Gs : ℝ → ℝ := fun r => (G r + G (-r)) / 2 with hGs
  have hGsc : Continuous Gs := (hGc.add (hGc.comp continuous_neg)).div_const 2
  have hGs0 : ∀ r, 0 ≤ Gs r := fun r => by simp only [hGs]; linarith [hG0 r, hG0 (-r)]
  have hGsi : Integrable Gs := (hGi.add hGi.comp_neg).div_const 2
  set g : ℝ → NNReal := fun r => (Gs r).toNNReal with hg
  have hgm : Measurable g := hGsc.measurable.real_toNNReal
  set μ : Measure ℝ := volume.withDensity fun r => (g r : ENNReal) with hμ
  haveI : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hGsi.2
  have hint : ∀ F : ℝ → ℝ, ∫ r, F r ∂μ = ∫ r, Gs r * F r := fun F => by
    rw [hμ, integral_withDensity_eq_integral_smul hgm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [hg, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hGs0 r)]
  have hneg : ∀ F : ℝ → ℝ, ∫ r, F (-r) = ∫ r, F r := fun F => integral_neg_eq_self F volume
  -- cosine and sine moments of the symmetrization
  have hcosS : ∀ t : ℝ, ∫ r, Gs r * Real.cos (r * t) = ∫ r, G r * Real.cos (r * t) := fun t => by
    have i1 := integrable_mul_bounded hGi (F := fun r => Real.cos (r * t)) (by fun_prop)
      (C := 1) fun r => Real.abs_cos_le_one _
    have i2 : Integrable fun r => G (-r) * Real.cos (r * t) := by
      have := i1.comp_neg
      refine this.congr (Filter.Eventually.of_forall fun r => ?_)
      simp only [neg_mul, Real.cos_neg]
    have e : (fun r => Gs r * Real.cos (r * t)) =
        fun r => (G r * Real.cos (r * t) + G (-r) * Real.cos (r * t)) / 2 := by
      ext r; simp only [hGs]; ring
    rw [e, integral_div, integral_add i1 i2]
    have h2 : ∫ r, G (-r) * Real.cos (r * t) = ∫ r, G r * Real.cos (r * t) := by
      rw [← hneg (fun r => G r * Real.cos (r * t))]
      simp only [neg_mul, Real.cos_neg]
    rw [h2]; ring
  have hsinS : ∀ t : ℝ, ∫ r, Gs r * Real.sin (r * t) = 0 := fun t => by
    have h := hneg (fun r => Gs r * Real.sin (r * t))
    have e : (fun r => Gs (-r) * Real.sin (-r * t)) = fun r => -(Gs r * Real.sin (r * t)) := by
      ext r; simp only [hGs, neg_neg, neg_mul, Real.sin_neg]; ring
    simp only [e, integral_neg] at h
    linarith
  have hblind : ∀ j : ℕ, 1 ≤ j → charFun μ ((j : ℝ) * ℓ) = 0 := by
    intro j hj
    set t : ℝ := (j : ℝ) * ℓ
    rw [charFun_apply_real, hμ, integral_withDensity_eq_integral_smul hgm]
    have e : ∀ r : ℝ, g r • Complex.exp (↑t * ↑r * I) =
        ((Gs r * Real.cos (r * t) : ℝ) : ℂ) + ((Gs r * Real.sin (r * t) : ℝ) : ℂ) * I := by
      intro r
      rw [NNReal.smul_def, Complex.real_smul, show (↑t * ↑r : ℂ) = ((r * t : ℝ) : ℂ) by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.coe_toNNReal _ (hGs0 r)]
      push_cast; ring
    have ic := integrable_mul_bounded hGsi (F := fun r => Real.cos (r * t)) (by fun_prop)
      (C := 1) fun r => Real.abs_cos_le_one (r * t)
    have is := integrable_mul_bounded hGsi (F := fun r => Real.sin (r * t)) (by fun_prop)
      (C := 1) fun r => Real.abs_sin_le_one (r * t)
    simp_rw [e]
    rw [integral_add ic.ofReal (is.ofReal.mul_const _), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal, hcosS, hcos j hj, hsinS]
    simp
  have h1 := integral_periodic_eq_of_blind μ ℓ hblind hP
  rw [hint] at h1
  have hmass : μ.real Set.univ = ∫ r, G r := by
    have h := hint (fun _ => 1)
    rw [integral_const, smul_eq_mul, mul_one] at h
    rw [h]
    simp only [mul_one]
    have i2 := hGi.comp_neg
    rw [show (fun r => Gs r) = fun r => (G r + G (-r)) / 2 from rfl, integral_div,
      integral_add hGi i2, hneg G]
    ring
  rw [hmass] at h1
  rw [← h1]
  -- symmetrize the left side
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hP.continuousOn
  have hPb : ∀ r, |P (phase ℓ r)| ≤ C := fun r => by
    rw [← Real.norm_eq_abs]; exact hC _ (Set.mem_univ _)
  have hPc : Continuous fun r => P (phase ℓ r) := hP.comp (continuous_phase ℓ)
  have i1 := integrable_mul_bounded hGi hPc hPb
  have hph : ∀ r, phase ℓ (-r) = -phase ℓ r := fun r => by
    simp only [phase, neg_mul]; exact AddCircle.coe_neg (p := 2 * π)
  have i2 : Integrable fun r => G (-r) * P (phase ℓ r) := by
    refine i1.comp_neg.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [hph, heven]
  have e : (fun r => Gs r * P (phase ℓ r)) =
      fun r => (G r * P (phase ℓ r) + G (-r) * P (phase ℓ r)) / 2 := by
    ext r; simp only [hGs]; ring
  rw [e, integral_div, integral_add i1 i2]
  have h2 : ∫ r, G (-r) * P (phase ℓ r) = ∫ r, G r * P (phase ℓ r) := by
    rw [← hneg (fun r => G r * P (phase ℓ r))]
    simp only [hph, heven]
  rw [h2]; ring

/-! ## The archimedean symbol is even and increasing in `|r|` -/

/-- The `n`-th Gauss term of `γ(r) − γ(0)` at `a = 1/4`. -/
def gaussTerm (r : ℝ) (n : ℕ) : ℝ :=
  (r / 2) ^ 2 / ((1 / 4 + n) * ((1 / 4 + n) ^ 2 + (r / 2) ^ 2))

theorem hasSum_gaussTerm (r : ℝ) :
    HasSum (gaussTerm r) (EF.gammaBracket r - EF.gammaBracket 0) := by
  have h := hasSum_re_digamma_vertical_sub (a := (1 / 4 : ℝ)) (by norm_num) (r / 2)
  have e1 : (1 / 4 : ℂ) + I * (r : ℂ) / 2 = ((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have e0 : (1 / 4 : ℂ) + I * ((0 : ℝ) : ℂ) / 2 = ((1 / 4 : ℝ) : ℂ) := by push_cast; ring
  have hv : EF.gammaBracket r - EF.gammaBracket 0 =
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re -
        (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re := by
    unfold EF.gammaBracket; rw [e1, e0]; ring
  rw [hv]; exact h

theorem gaussTerm_nonneg (r : ℝ) (n : ℕ) : 0 ≤ gaussTerm r n := by
  unfold gaussTerm; positivity

theorem gaussTerm_le_of_abs_le {s r : ℝ} (h : |s| ≤ |r|) (n : ℕ) :
    gaussTerm s n ≤ gaussTerm r n := by
  unfold gaussTerm
  have hc : (0 : ℝ) < 1 / 4 + n := by positivity
  have hs2 : (s / 2) ^ 2 ≤ (r / 2) ^ 2 := by
    rw [div_pow, div_pow]
    exact div_le_div_of_nonneg_right (sq_le_sq.mpr h) (by norm_num)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hd : 0 ≤ (r / 2) ^ 2 - (s / 2) ^ 2 := by linarith
  nlinarith [mul_nonneg hd (mul_nonneg hc.le (pow_pos hc 2).le)]

/-- `γ` is monotone in `|r|`. -/
theorem gammaBracket_le_of_abs_le {s r : ℝ} (h : |s| ≤ |r|) :
    EF.gammaBracket s ≤ EF.gammaBracket r := by
  have := hasSum_le (gaussTerm_le_of_abs_le h) (hasSum_gaussTerm s) (hasSum_gaussTerm r)
  linarith

theorem gammaBracket_neg (r : ℝ) : EF.gammaBracket (-r) = EF.gammaBracket r :=
  le_antisymm (gammaBracket_le_of_abs_le (abs_neg r).le)
    (gammaBracket_le_of_abs_le (abs_neg r).ge)

/-- The Gauss partial sums are lower bounds: `γ(r) − γ(0) ≥ Σ_{n<K} gaussTerm r n`. -/
theorem sum_gaussTerm_le (r : ℝ) (K : ℕ) :
    ∑ n ∈ Finset.range K, gaussTerm r n ≤ EF.gammaBracket r - EF.gammaBracket 0 :=
  sum_le_hasSum _ (fun n _ => gaussTerm_nonneg r n) (hasSum_gaussTerm r)

/-! ## The folded symbol on the prime circle -/

/-- The folded symbol `z ↦ γ(‖z‖/ℓ)` on `ℝ/2πℤ`: the symbol on one period around `0`. -/
def foldedSymbol (ℓ : ℝ) (z : AddCircle (2 * π)) : ℝ := EF.gammaBracket (‖z‖ / ℓ)

theorem continuous_foldedSymbol (ℓ : ℝ) : Continuous (foldedSymbol ℓ) :=
  WeilHerglotz.continuous_gammaBracket.comp (continuous_norm.div_const ℓ :
    Continuous fun z : AddCircle (2 * π) => ‖z‖ / ℓ)

theorem foldedSymbol_neg (ℓ : ℝ) (z : AddCircle (2 * π)) :
    foldedSymbol ℓ (-z) = foldedSymbol ℓ z := by
  simp only [foldedSymbol, norm_neg]

/-- The folded symbol is a minorant of the symbol. -/
theorem foldedSymbol_phase_le {ℓ : ℝ} (hℓ : 0 < ℓ) (r : ℝ) :
    foldedSymbol ℓ (phase ℓ r) ≤ EF.gammaBracket r := by
  apply gammaBracket_le_of_abs_le
  have hn : ‖phase ℓ r‖ ≤ |r * ℓ| := by
    have := QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (2 * π)) (m := r * ℓ)
    simpa [phase, Real.norm_eq_abs] using this
  rw [abs_div, abs_of_pos hℓ, abs_norm, div_le_iff₀ hℓ]
  rwa [abs_mul, abs_of_pos hℓ] at hn

/-- **The circle mean of the folded symbol** is the mean of `γ` over `[0, π/ℓ]`. -/
theorem integral_foldedSymbol {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ z, foldedSymbol ℓ z ∂AddCircle.haarAddCircle =
      ℓ / π * ∫ v in (0 : ℝ)..π / ℓ, EF.gammaBracket v := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hpre := AddCircle.intervalIntegral_preimage (2 * π) (-π) (foldedSymbol ℓ)
  rw [AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal hpi.le, show -π + 2 * π = π by ring] at hpre
  have hcongr : ∫ a in (-π)..π, foldedSymbol ℓ (a : AddCircle (2 * π)) =
      ∫ a in (-π)..π, EF.gammaBracket (|a| / ℓ) := by
    refine intervalIntegral.integral_congr fun a ha => ?_
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ha
    simp only [foldedSymbol]
    rw [(AddCircle.norm_coe_eq_abs_iff (2 * π) hpi.ne').mpr]
    rw [abs_of_pos hpi]
    exact abs_le.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hc : Continuous fun a : ℝ => EF.gammaBracket (|a| / ℓ) :=
    WeilHerglotz.continuous_gammaBracket.comp (continuous_abs.div_const ℓ)
  have hsplit : ∫ a in (-π)..π, EF.gammaBracket (|a| / ℓ) =
      2 * ∫ a in (0 : ℝ)..π, EF.gammaBracket (a / ℓ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have h1 : ∫ a in (-π)..0, EF.gammaBracket (|a| / ℓ) =
        ∫ a in (0 : ℝ)..π, EF.gammaBracket (a / ℓ) := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := π)
        (fun a => EF.gammaBracket (|a| / ℓ))
      simp only [abs_neg, neg_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun a ha => ?_
      rw [Set.uIcc_of_le Real.pi_pos.le] at ha
      simp only [abs_of_nonneg ha.1]
    have h2 : ∫ a in (0 : ℝ)..π, EF.gammaBracket (|a| / ℓ) =
        ∫ a in (0 : ℝ)..π, EF.gammaBracket (a / ℓ) := by
      refine intervalIntegral.integral_congr fun a ha => ?_
      rw [Set.uIcc_of_le Real.pi_pos.le] at ha
      simp only [abs_of_nonneg ha.1]
    rw [h1, h2]; ring
  have hsub : ∫ a in (0 : ℝ)..π, EF.gammaBracket (a / ℓ) =
      ℓ * ∫ v in (0 : ℝ)..π / ℓ, EF.gammaBracket v := by
    rw [intervalIntegral.integral_comp_div (fun v => EF.gammaBracket v) hℓ.ne', zero_div,
      smul_eq_mul]
  rw [hcongr, hsplit, hsub] at hpre
  have : ∫ z, foldedSymbol ℓ z ∂AddCircle.haarAddCircle =
      (2 * (ℓ * ∫ v in (0 : ℝ)..π / ℓ, EF.gammaBracket v)) / (2 * π) := by
    rw [hpre, smul_eq_mul]; field_simp
  rw [this]; field_simp

/-- **Left Riemann sums bound the mean from below**: for `N ≥ 1`,
`(ℓ/π) ∫_0^{π/ℓ} γ ≥ (1/N) Σ_{i<N} γ(iπ/(Nℓ))`, since `γ` increases on `[0, ∞)`. -/
theorem sum_le_mean_gammaBracket {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ i ∈ Finset.range N, EF.gammaBracket (i * (π / (N * ℓ)))) / N ≤
      ℓ / π * ∫ v in (0 : ℝ)..π / ℓ, EF.gammaBracket v := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set c : ℝ := π / (N * ℓ) with hc
  have hcpos : 0 < c := by positivity
  have hmono : MonotoneOn (fun u => EF.gammaBracket (c * u)) (Set.Icc (0 : ℝ) (0 + N)) := by
    intro u hu w hw huw
    apply gammaBracket_le_of_abs_le
    rw [abs_of_nonneg (mul_nonneg hcpos.le hu.1), abs_of_nonneg (mul_nonneg hcpos.le hw.1)]
    exact mul_le_mul_of_nonneg_left huw hcpos.le
  have hs := hmono.sum_le_integral
  simp only [zero_add] at hs
  rw [intervalIntegral.integral_comp_mul_left (fun v => EF.gammaBracket v) hcpos.ne', mul_zero,
    smul_eq_mul, show c * N = π / ℓ by rw [hc]; field_simp] at hs
  have e : ∀ i : ℕ, EF.gammaBracket (c * i) = EF.gammaBracket (i * c) := fun i => by
    rw [mul_comm]
  simp only [e] at hs
  rw [div_le_iff₀ hNpos]
  have : c⁻¹ = N * ℓ / π := by rw [hc, inv_div]
  rw [this] at hs
  have hpi := Real.pi_pos
  calc ∑ i ∈ Finset.range N, EF.gammaBracket (i * c) ≤
      N * ℓ / π * ∫ v in (0 : ℝ)..π / ℓ, EF.gammaBracket v := hs
    _ = ℓ / π * (∫ v in (0 : ℝ)..π / ℓ, EF.gammaBracket v) * N := by ring

/-! ## Single tests: symbol energy, Plancherel and the node values at the powers of `2` -/

open WeilOneSided

theorem exists_Icc_support (f : WeilTestFn) : ∃ a : ℝ, tsupport f.1 ⊆ Icc (-a) a := by
  obtain ⟨a, ha⟩ := f.2.2.isCompact.isBounded.subset_closedBall 0
  refine ⟨a, fun x hx => ?_⟩
  have := ha hx
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  exact abs_le.mp this

theorem continuous_normSq_paperFT (f : WeilTestFn) :
    Continuous fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 :=
  ((WeilHerglotz.continuous_paperFT_real
    (f.2.1.continuous.integrable_of_hasCompactSupport f.2.2)).norm).pow 2

theorem integrable_normSq_paperFT (f : WeilTestFn) :
    Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 := by
  obtain ⟨a, ha⟩ := exists_Icc_support f
  simpa using integrable_normSq_paperFT_mul_cos f.2.1 ha 0

theorem integrable_normSq_paperFT_mul_gammaBracket (f : WeilTestFn) :
    Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * EF.gammaBracket r := by
  obtain ⟨F, hF, hFc⟩ := f
  have hint := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hF hFc hF hFc
  refine hint.re.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only
  rw [paperFT_weilTest_self_ofReal hF.continuous hFc r]
  push_cast
  rw [show ((‖paperFT F ↑r‖ : ℂ) ^ 2 * (EF.gammaBracket r : ℂ)) =
    ((‖paperFT F ↑r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) by push_cast; ring]
  exact Complex.ofReal_re _

/-- The archimedean part without the pole is the symbol integral `(1/2π)∫|f̂|²γ`. -/
theorem weilArchRe_sub_pole_eq (f : WeilTestFn) :
    weilArchRe (EF.weilTest f.1 f.1) - (weilPoleTerm (EF.weilTest f.1 f.1)).re =
      (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * EF.gammaBracket r := by
  obtain ⟨F, hF, hFc⟩ := f
  simp only
  have hreal : ∀ r : ℝ, paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ) =
      ((‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := fun r => by
    rw [paperFT_weilTest_self_ofReal hF.continuous hFc r]
    push_cast
    ring
  have hint_eq : ∫ r : ℝ, paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ) =
      ((∫ r : ℝ, ‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
    simp_rw [hreal]
    exact integral_complex_ofReal
  unfold weilArchRe weilPoleTerm
  rw [hint_eq, Complex.add_re]
  have hc : (1 / (2 * (π : ℂ))) * ((∫ r : ℝ, ‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) =
      (((1 / (2 * π)) * ∫ r : ℝ, ‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
    push_cast; ring
  rw [hc, Complex.ofReal_re]
  ring

theorem integral_normSq_paperFT_eq (f : WeilTestFn) :
    ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 = 2 * π * ∫ x, ‖f.1 x‖ ^ 2 := by
  obtain ⟨a, ha⟩ := exists_Icc_support f
  exact integral_norm_paperFT_sq f.2.1 ha

/-- The cosine moment at `j log 2` is the node value at `2^j`. -/
theorem integral_normSq_paperFT_mul_cos_two_pow (f : WeilTestFn) (j : ℕ) :
    ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * Real.cos (r * ((j : ℝ) * Real.log 2)) =
      π * Real.sqrt ((2 ^ j : ℕ) : ℝ) * logValue f.1 (2 ^ j) := by
  obtain ⟨a, ha⟩ := exists_Icc_support f
  rw [integral_normSq_paperFT_mul_cos_eq f.2.1 ha, logValue]
  have hlog : Real.log ((2 ^ j : ℕ) : ℝ) = (j : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hlog]
  have hs : 0 < Real.sqrt ((2 ^ j : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-! ## The exact single-prime slack -/

/-- The mean of the archimedean symbol over one period `[−π/log 2, π/log 2]` of the prime `2`. -/
def twoPeriodMean : ℝ := Real.log 2 / π * ∫ v in (0 : ℝ)..π / Real.log 2, EF.gammaBracket v

/-- **The symbol integral of a blind combination is at least the period mean times its mass.**
Blindness at the powers of `2` makes the phase `r log 2 mod 2π` of the spectral measure uniform,
and `γ` dominates its fold `γ(‖r log 2‖/log 2)` onto one period. -/
theorem twoPeriodMean_mul_massOf_le (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f)
    (hv : nodeVector c = 0) : twoPeriodMean * massOf c ≤ nodeArchOnly c := by
  have hℓ : 0 < Real.log 2 := Real.log_pos one_lt_two
  set G : ℝ → ℝ := fun r => ∑ f ∈ c.support, c f * ‖paperFT f.1 r‖ ^ 2 with hG
  have hGc : Continuous G :=
    continuous_finsetSum _ fun f _ => continuous_const.mul (continuous_normSq_paperFT f)
  have hG0 : ∀ r, 0 ≤ G r := fun r =>
    Finset.sum_nonneg fun f _ => mul_nonneg (hc f) (by positivity)
  have hGi : Integrable G :=
    integrable_finsetSum _ fun f _ => (integrable_normSq_paperFT f).const_mul _
  have hcos : ∀ j : ℕ, 1 ≤ j → ∫ r, G r * Real.cos (r * ((j : ℝ) * Real.log 2)) = 0 := by
    intro j hj
    have h2j : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    have hnode := congrArg (fun w : LogIndex →₀ ℝ => w ⟨2 ^ j, h2j⟩) hv
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hnode
    rw [nodeVector_eq, linearCombination_logVector_apply] at hnode
    simp only [hG, Finset.sum_mul]
    rw [integral_finsetSum _ fun f _ => by
      simpa [mul_assoc] using ((integrable_normSq_paperFT_mul_cos f.2.1
        (exists_Icc_support f).choose_spec ((j : ℝ) * Real.log 2)).const_mul (c f))]
    simp_rw [mul_assoc, integral_const_mul, integral_normSq_paperFT_mul_cos_two_pow]
    have e : ∀ f : WeilTestFn, c f * (π * Real.sqrt ((2 ^ j : ℕ) : ℝ) * logValue f.1 (2 ^ j)) =
        π * Real.sqrt ((2 ^ j : ℕ) : ℝ) * (c f * logValue f.1 (2 ^ j)) := fun f => by ring
    simp_rw [e, ← Finset.mul_sum]
    rw [Finsupp.sum] at hnode
    rw [hnode, mul_zero]
  -- periodization against the folded symbol
  have hper := integral_mul_periodic_eq_of_cos_blind hGc hG0 hGi hcos
    (continuous_foldedSymbol (Real.log 2)) (foldedSymbol_neg (Real.log 2))
  rw [integral_foldedSymbol hℓ] at hper
  have hfold : Continuous fun r => foldedSymbol (Real.log 2) (phase (Real.log 2) r) :=
    (continuous_foldedSymbol _).comp (continuous_phase _)
  have hGγ : Integrable fun r => G r * EF.gammaBracket r := by
    have : (fun r => G r * EF.gammaBracket r) =
        fun r : ℝ => ∑ f ∈ c.support, c f * (‖paperFT f.1 r‖ ^ 2 * EF.gammaBracket r) := by
      ext r; simp only [hG, Finset.sum_mul]; refine Finset.sum_congr rfl fun f _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun f _ =>
      (integrable_normSq_paperFT_mul_gammaBracket f).const_mul _
  have hGf : Integrable fun r => G r * foldedSymbol (Real.log 2) (phase (Real.log 2) r) := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_foldedSymbol (Real.log 2)).continuousOn
    exact integrable_mul_bounded hGi hfold (C := C) fun r => by
      rw [← Real.norm_eq_abs]; exact hC _ (Set.mem_univ _)
  have hmono : ∫ r, G r * foldedSymbol (Real.log 2) (phase (Real.log 2) r) ≤
      ∫ r, G r * EF.gammaBracket r :=
    integral_mono hGf hGγ fun r =>
      mul_le_mul_of_nonneg_left (foldedSymbol_phase_le hℓ r) (hG0 r)
  -- identify the two sides
  have hsym : ∫ r, G r * EF.gammaBracket r = 2 * π * nodeArchOnly c := by
    have : (fun r => G r * EF.gammaBracket r) =
        fun r : ℝ => ∑ f ∈ c.support, c f * (‖paperFT f.1 r‖ ^ 2 * EF.gammaBracket r) := by
      ext r; simp only [hG, Finset.sum_mul]; refine Finset.sum_congr rfl fun f _ => by ring
    rw [this, integral_finsetSum _ fun f _ =>
      (integrable_normSq_paperFT_mul_gammaBracket f).const_mul _]
    simp_rw [integral_const_mul]
    rw [nodeArchOnly, nodeArchEnergy_eq, nodePoleMass, Finsupp.linearCombination_apply,
      Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [smul_eq_mul]
    rw [← mul_sub, weilArchRe_sub_pole_eq]
    field_simp
  have hmass : ∫ r, G r = 2 * π * massOf c := by
    rw [hG, integral_finsetSum _ fun f _ => (integrable_normSq_paperFT f).const_mul _]
    simp_rw [integral_const_mul, integral_normSq_paperFT_eq]
    rw [massOf, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => by ring
  rw [hper, hsym, hmass] at hmono
  have hpi : 0 < 2 * π := by positivity
  rw [twoPeriodMean]
  nlinarith

/-- **Single-prime blind symbol slack.**  `BlindSymbolSlack (−m₂)` holds with `m₂` the mean of `γ`
over one period `[−π/log 2, π/log 2]` of the prime `2`. -/
theorem blindSymbolSlack_twoPeriodMean : BlindSymbolSlack (-twoPeriodMean) := by
  intro c hc hv
  have := twoPeriodMean_mul_massOf_le c hc hv
  linarith

/-! ## The numerical value -/

/-- Grid lower bound for the period mean through truncated Gauss sums. -/
theorem gammaBracket_zero_add_le_twoPeriodMean {N : ℕ} (hN : 1 ≤ N) {r₀ : ℝ} (hr₀ : 0 ≤ r₀)
    (hr : r₀ ≤ π / (N * Real.log 2)) (K : ℕ) :
    EF.gammaBracket 0 + (∑ i ∈ Finset.range N, ∑ n ∈ Finset.range K, gaussTerm (i * r₀) n) / N ≤
      twoPeriodMean := by
  have hℓ : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine le_trans ?_ (sum_le_mean_gammaBracket hℓ hN)
  have hterm : ∀ i ∈ Finset.range N, EF.gammaBracket 0 +
      ∑ n ∈ Finset.range K, gaussTerm (i * r₀) n ≤
        EF.gammaBracket (i * (π / (N * Real.log 2))) := by
    intro i _
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have habs : |(i : ℝ) * r₀| ≤ |(i : ℝ) * (π / (N * Real.log 2))| := by
      rw [abs_of_nonneg (mul_nonneg hi hr₀), abs_of_nonneg (mul_nonneg hi (hr₀.trans hr))]
      exact mul_le_mul_of_nonneg_left hr hi
    have h1 := Finset.sum_le_sum fun n (_ : n ∈ Finset.range K) => gaussTerm_le_of_abs_le habs n
    have h2 := sum_gaussTerm_le ((i : ℝ) * (π / (N * Real.log 2))) K
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [le_div_iff₀ hNpos, add_mul, div_mul_cancel₀ _ hNpos.ne']
  linarith

/-- `γ(r) − γ(0)` averaged over the 32-point grid of step `0.1416 ≤ π/(32 log 2)` is at least
`121/32`, from eight Gauss terms. -/
theorem gauss_grid_certificate :
    (121 : ℝ) ≤ ∑ i ∈ Finset.range 32, ∑ n ∈ Finset.range 8, gaussTerm (i * (1416 / 10000)) n := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, gaussTerm]
  norm_num

/-- `m₂ ≥ γ(0) + 121/32`. -/
theorem twoPeriodMean_ge : EF.gammaBracket 0 + 121 / 32 ≤ twoPeriodMean := by
  have hr : (1416 / 10000 : ℝ) ≤ π / ((32 : ℕ) * Real.log 2) := by
    have hl := Real.log_two_lt_d9
    have hp := Real.pi_gt_d6
    have hlpos : 0 < Real.log 2 := Real.log_pos one_lt_two
    rw [le_div_iff₀ (by positivity)]
    push_cast
    nlinarith
  have h := gammaBracket_zero_add_le_twoPeriodMean (N := 32) (by norm_num) (by norm_num) hr 8
  have hc := gauss_grid_certificate
  push_cast at h
  linarith

/-- **Blind symbol slack at the prime `2`, numerically**: `BlindSymbolSlack (−γ(0) − 121/32)`, i.e.
`M ≈ 1.59`, against `−γ(0) − 2 ≈ 3.37` from the single cosine `cos(r log 2)`. -/
theorem blindSymbolSlack_two_powers : BlindSymbolSlack (-EF.gammaBracket 0 - 121 / 32) :=
  BlindSymbolSlack.mono (by linarith [twoPeriodMean_ge]) blindSymbolSlack_twoPeriodMean

/-- **Violators are pole-light, with the period threshold.**  A blind nonnegative combination with
negative pole and archimedean energy has pole mass below `−m₂ ≤ −γ(0) − 121/32 ≈ 1.59` times its
mass. -/
theorem nodePoleMass_lt_of_nodeArchEnergy_neg_twoPeriod (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f)
    (hv : nodeVector c = 0) (hneg : nodeArchEnergy c < 0) :
    nodePoleMass c < (-EF.gammaBracket 0 - 121 / 32) * massOf c := by
  have h := blindSymbolSlack_two_powers c hc hv
  rw [nodeArchOnly] at h
  linarith

end

end RHTower.BlindPrimePowerSlack
