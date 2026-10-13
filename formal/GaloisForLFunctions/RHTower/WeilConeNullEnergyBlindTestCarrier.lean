import GaloisForLFunctions.RHTower.WeilConeXiDivisibleBlindTest
import GaloisForLFunctions.RHTower.WeilFullConeAtomExtraction

/-!
# A prime-blind test of zero Weil energy carries every Weil-positive boundary measure

Let `F` be a real test of the decay class `|F|, |F'| ≤ C e^{−(1/2+δ)|x|}` (`ExpDecayTest`) whose
autocorrelation vanishes at every `log n`, `n ≥ 2`, and whose pole and archimedean energy
`2 Re(F̂(i/2) · conj F̂(−i/2)) + (1/2π) ∫ |F̂(r)|² G(r) dr` vanishes (`archPoleEnergy F = 0`).
Neither condition involves a prime or a zero of `ζ`.

**Theorem** (`boundaryMeasure_paperFT_ne_zero_of_null`).  For every full-cone Weil-positive
system `lam`, the boundary measure `μ_lam` is carried by the real zeros of `F̂`:
`μ_lam{r : F̂(r) ≠ 0} = 0`.

**Corollary** (`eq_vonMangoldt_of_null_of_zeroFaithful`).  If moreover every real zero of `F̂`
is the ordinate of a zero of `ζ` on the critical line, every full-cone Weil-positive system is `Λ`,
and the Riemann hypothesis is equivalent to prime-blind positivity
(`riemannHypothesis_iff_primeBlindPositive_of_null_of_zeroFaithful`).

So the (N1) premise of route HF splits into a zeta-free part (a nonzero prime-blind test of zero
energy) and a containment of real zero sets.  No hypothesis on the zeros of `ζ` off the critical
line is needed.  A `Ξ`-divisible prime-blind test has both properties
(`archPoleEnergy_eq_zero_of_xiDivisibleBlindTest`, `riemannZeta_eq_zero_of_xiDivisibleBlindTest`).

**Zeta-free spectral identity** (`integral_norm_sq_paperFT_eq_archPoleEnergy`).  For every
prime-blind test of the decay class (zero energy not assumed) and every cone point `lam`,
`∫ |F̂|² dμ_lam = archPoleEnergy F`.  So all cone points agree on prime-blind tests, and prime-blind
positivity extends from compactly supported tests to the whole decay class
(`archPoleEnergy_nonneg_of_primeBlindPositive`).  Under RH, every zero-energy test vanishes at the
ordinate of every critical zero (`paperFT_eq_zero_of_null_of_riemannHypothesis`).

**Proof.**  For the truncations `F_L`, the spectral representation of `lam` gives
`∫ |F̂_L|² dμ_lam = archPoleEnergy F_L − T_lam(F_L ⋆ F̃_L)`.  The energy tends to
`archPoleEnergy F = 0` (`tendsto_archPoleEnergy_truncTest`).  The partial sums of `lam` grow at
most linearly (corpus `exists_sharp_source_sum_le`), so summation by parts and blindness give
`T_lam(F_L ⋆ F̃_L) → 0` (`tendsto_atomPairing_truncTest`).  Fatou's lemma gives
`∫ |F̂|² dμ_lam = 0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate ENNReal NNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

/-- **The partial sums of a Weil-positive system grow at most linearly.** -/
theorem exists_abs_primeWeightPartialSum_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ A : ℝ, ∀ N : ℕ, |primeWeightPartialSum lam N| ≤ A * (N + 1) := by
  obtain ⟨C, hC, hS⟩ := WeilSingularArithmetic.exists_sharp_source_sum_le hW
    (ε := 1 / 2) (by norm_num)
  refine ⟨C + 1, fun N => ?_⟩
  have h1 := hS N
  rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one] at h1
  have hc : (∑ n ∈ Finset.range (N + 1), ((if 2 ≤ n then lam n else 0 : ℝ) : ℂ)) - (N : ℂ) =
      (((∑ n ∈ Finset.range (N + 1), (if 2 ≤ n then lam n else 0)) - N : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_natCast]
  rw [hc, Complex.norm_real, Real.norm_eq_abs] at h1
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold primeWeightPartialSum
  rw [abs_le]
  have := abs_le.mp h1
  constructor <;> nlinarith

/-- The real part of the Weil functional of a truncated autocorrelation is its pole and
archimedean energy minus its prime pairing. -/
theorem re_weilFullFunctional_weilTest_truncTest_eq (lam : ℕ → ℝ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (L : ℝ) :
    (weilFullFunctional lam
        (EF.weilTest (fun u => (truncTest F L u : ℂ)) (fun u => (truncTest F L u : ℂ)))).re =
      archPoleEnergy (truncTest F L) -
        atomPairing lam (crossCorr (truncTest F L) (truncTest F L)) := by
  set f : ℝ → ℂ := fun u => (truncTest F L u : ℂ) with hf
  have hk : EF.weilTest f f = fun y => ((crossCorr (truncTest F L) (truncTest F L) y : ℝ) : ℂ) :=
    funext fun y => weilTest_ofReal_eq (truncTest F L) y
  rw [← weilArchRe_weilTest_truncTest_eq hF L]
  have hsum : (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))) =
      ((atomPairing lam (crossCorr (truncTest F L) (truncTest F L)) : ℝ) : ℂ) := by
    rw [atomPairing, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [hk]
    push_cast
    ring
  unfold WeilOneSided.weilArchRe weilFullFunctional
  rw [hsum]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  ring

/-- The spectral energy of a truncation is its pole and archimedean energy minus its prime
pairing. -/
theorem toReal_lintegral_specDensity_truncTest_eq_archPole {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (L : ℝ) :
    (∫⁻ r, (specDensity (fun u => (truncTest F L u : ℂ)) r : ℝ≥0∞) ∂boundaryMeasure hW) < ⊤ ∧
    (∫⁻ r, (specDensity (fun u => (truncTest F L u : ℂ)) r : ℝ≥0∞) ∂boundaryMeasure hW).toReal =
      archPoleEnergy (truncTest F L) -
        atomPairing lam (crossCorr (truncTest F L) (truncTest F L)) := by
  have hFL := contDiff_ofReal_truncTest hF L
  have hFLc : HasCompactSupport fun u => (truncTest F L u : ℂ) :=
    (hasCompactSupport_truncTest F L).comp_left Complex.ofReal_zero
  obtain ⟨hfin, hrep⟩ := weilFullFunctional_weilTest_eq_lintegral hW hFL hFLc
  have h := re_weilFullFunctional_weilTest_truncTest_eq lam hF L
  rw [hrep, Complex.ofReal_re] at h
  exact ⟨hfin, h⟩

/-- **Fatou along the truncations.**  If the spectral energies of the truncations tend to `0`,
the spectral energy of `F` vanishes. -/
theorem lintegral_specDensity_eq_zero_of_tendsto {F : ℝ → ℝ} (hF : ExpDecayTest F)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hfin : ∀ L : ℝ,
      (∫⁻ r, (specDensity (fun u => (truncTest F L u : ℂ)) r : ℝ≥0∞) ∂boundaryMeasure hW) < ⊤)
    (hreal : Tendsto (fun L : ℝ =>
      (∫⁻ r, (specDensity (fun u => (truncTest F L u : ℂ)) r : ℝ≥0∞) ∂boundaryMeasure hW).toReal)
      atTop (𝓝 0)) :
    (∫⁻ r, (specDensity (fun u => (F u : ℂ)) r : ℝ≥0∞) ∂boundaryMeasure hW) = 0 := by
  set μ := boundaryMeasure hW
  have hlim : Tendsto (fun L : ℝ =>
      ∫⁻ r, (specDensity (fun u => (truncTest F L u : ℂ)) r : ℝ≥0∞) ∂μ) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hreal
    rw [ENNReal.ofReal_zero] at h
    exact h.congr fun L => ENNReal.ofReal_toReal (hfin L).ne
  have hmeas : ∀ k : ℕ, Measurable fun r =>
      (specDensity (fun u => (truncTest F (k : ℝ) u : ℂ)) r : ℝ≥0∞) := fun k =>
    (measurable_specDensity
      ((contDiff_ofReal_truncTest hF.1 _).continuous.integrable_of_hasCompactSupport
        ((hasCompactSupport_truncTest F _).comp_left Complex.ofReal_zero))).coe_nnreal_ennreal
  have hpt : ∀ r : ℝ, Tendsto (fun k : ℕ =>
      (specDensity (fun u => (truncTest F (k : ℝ) u : ℂ)) r : ℝ≥0∞)) atTop
      (𝓝 (specDensity (fun u => (F u : ℂ)) r : ℝ≥0∞)) := by
    intro r
    have hz : |((r : ℂ)).im| ≤ 1 / 2 := by simp
    have h := (tendsto_paperFT_truncTest hF hz).comp tendsto_natCast_atTop_atTop
    have hc : Continuous fun z : ℂ => ((‖z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.continuous_coe.comp (continuous_nnnorm.pow 2)
    exact (hc.tendsto _).comp h
  have hfatou := lintegral_liminf_le (μ := μ) (u := (atTop : Filter ℕ)) hmeas
  have hliminf : liminf (fun k : ℕ => ∫⁻ r,
      (specDensity (fun u => (truncTest F (k : ℝ) u : ℂ)) r : ℝ≥0∞) ∂μ) atTop = 0 :=
    (hlim.comp tendsto_natCast_atTop_atTop).liminf_eq
  rw [hliminf] at hfatou
  exact le_antisymm (le_of_eq_of_le (lintegral_congr fun r => (hpt r).liminf_eq.symm) hfatou)
    (zero_le)

/-- **The spectral energy of a null prime-blind test vanishes.** -/
theorem lintegral_specDensity_eq_zero_of_null {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0) (hnull : archPoleEnergy F = 0)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    (∫⁻ r, (specDensity (fun u => (F u : ℂ)) r : ℝ≥0∞) ∂boundaryMeasure hW) = 0 := by
  obtain ⟨A, hA⟩ := exists_abs_primeWeightPartialSum_le hW
  have henergy := tendsto_archPoleEnergy_truncTest hF
  rw [hnull] at henergy
  have hprime := tendsto_atomPairing_truncTest hF hA hblind
  have h := henergy.sub hprime
  rw [sub_zero] at h
  exact lintegral_specDensity_eq_zero_of_tendsto hF hW
    (fun L => (toReal_lintegral_specDensity_truncTest_eq_archPole hF.1 hW L).1)
    (h.congr fun L => (toReal_lintegral_specDensity_truncTest_eq_archPole hF.1 hW L).2.symm)

/-- **A null prime-blind test carries every Weil-positive boundary measure on its real zeros.** -/
theorem boundaryMeasure_paperFT_ne_zero_of_null {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0) (hnull : archPoleEnergy F = 0)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    boundaryMeasure hW {r : ℝ | paperFT (fun u => (F u : ℂ)) r ≠ 0} = 0 := by
  have h0 := lintegral_specDensity_eq_zero_of_null hF hblind hnull hW
  have hFint : Integrable fun u => (F u : ℂ) := by
    obtain ⟨hF2, δ, C, hδ, hC, hb⟩ := hF
    have hκ : (0 : ℝ) < 1 / 2 + δ := by positivity
    have hint := ((RHTower.integrable_exp_neg_abs).comp_mul_left' hκ.ne').const_mul C
    refine hint.mono' (Complex.continuous_ofReal.comp hF2.continuous).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (hb u).1.trans (le_of_eq ?_)
    simp only [abs_mul, abs_of_pos hκ]
  rw [lintegral_eq_zero_iff (measurable_specDensity hFint).coe_nnreal_ennreal] at h0
  have hnull' : boundaryMeasure hW
      {r : ℝ | (specDensity (fun u => (F u : ℂ)) r : ℝ≥0∞) ≠ 0} = 0 := ae_iff.mp h0
  refine measure_mono_null (fun r hr => ?_) hnull'
  simp only [Set.mem_setOf_eq] at hr ⊢
  intro hs
  apply hr
  simpa [specDensity] using hs

/-- **Null plus zero-faithful pins the Weil cone to `Λ`.**  If `F` is a prime-blind test of the
decay class with zero pole and archimedean energy, and every real zero of `F̂` is the ordinate of
a zero of `ζ` on the critical line, every full-cone Weil-positive system equals `Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_null_of_zeroFaithful {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0) (hnull : archPoleEnergy F = 0)
    (hreal : ∀ r : ℝ, paperFT (fun u => (F u : ℂ)) r = 0 → riemannZeta ((1 / 2 : ℂ) + r * I) = 0)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  refine eq_vonMangoldt_of_boundaryMeasure_criticalZeros hW
    (measure_mono_null (fun r hr => ?_)
      (boundaryMeasure_paperFT_ne_zero_of_null hF hblind hnull hW))
  simp only [Set.mem_setOf_eq] at hr ⊢
  exact fun h => hr (hreal r h)

/-- **RH ⟺ PBAP under a null, zero-faithful prime-blind test.** -/
theorem riemannHypothesis_iff_primeBlindPositive_of_null_of_zeroFaithful {F : ℝ → ℝ}
    (hF : ExpDecayTest F) (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0)
    (hnull : archPoleEnergy F = 0)
    (hreal : ∀ r : ℝ, paperFT (fun u => (F u : ℂ)) r = 0 →
      riemannZeta ((1 / 2 : ℂ) + r * I) = 0) :
    RiemannHypothesis ↔ WeilOneSided.PrimeBlindPositive := by
  refine ⟨fun hRH => WeilOneSided.exists_weilPositiveFull_iff_primeBlindPositive.mp
      ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH⟩, fun hP => ?_⟩
  obtain ⟨lam, hW⟩ := WeilOneSided.exists_weilPositiveFull_iff_primeBlindPositive.mpr hP
  exact riemannHypothesis_of_boundaryMeasure_criticalZeros hW
    (measure_mono_null (fun r hr => fun h => hr (hreal r h))
      (boundaryMeasure_paperFT_ne_zero_of_null hF hblind hnull hW))

/-! ### Under RH, null tests vanish at every critical zero -/

/-- **Zeta-free localization of the zeros under RH.**  If RH holds, the transform of every
prime-blind test of the decay class with zero pole and archimedean energy vanishes at the ordinate
of every zero of `ζ` on the critical line.  The zeros of `ζ` then lie in the common real zero set of
all such tests, a set defined by the archimedean place and the positions `log n` alone. -/
theorem paperFT_eq_zero_of_null_of_riemannHypothesis (hRH : RiemannHypothesis) {F : ℝ → ℝ}
    (hF : ExpDecayTest F) (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0)
    (hnull : archPoleEnergy F = 0) {a : ℝ} (ha : riemannZeta ((1 / 2 : ℂ) + a * I) = 0) :
    paperFT (fun u => (F u : ℂ)) a = 0 := by
  have hΛ := riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH
  have h0 := boundaryMeasure_paperFT_ne_zero_of_null hF hblind hnull hΛ
  by_contra hne
  have hsing : boundaryMeasure hΛ {a} = 0 :=
    measure_mono_null (fun r hr => by rw [Set.mem_singleton_iff.mp hr]; exact hne) h0
  have hreal : (boundaryMeasure hΛ).real {a} = 0 := by simp [Measure.real, hsing]
  rw [boundaryMeasure_vonMangoldt_real_singleton hΛ a, Nat.cast_eq_zero] at hreal
  set s₀ : ℂ := (1 / 2 : ℂ) + a * I with hs₀
  have hxi : RHTower.xi s₀ = 0 := by
    have hre : 0 < s₀.re := by simp [hs₀]
    have hne1 : s₀ ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp [hs₀] at this
    exact (RHTower.xi_eq_zero_iff hre hne1).mpr ha
  have hord : analyticOrderAt RHTower.xi s₀ ≠ ⊤ := RHTower.xi_orderAt_ne_top s₀
  have hzero : analyticOrderAt RHTower.xi s₀ = 0 := by
    unfold analyticOrderNatAt at hreal
    rcases (ENat.toNat_eq_zero.mp hreal) with h | h
    · exact h
    · exact absurd h hord
  exact ((RHTower.xi_differentiable.analyticAt s₀).analyticOrderAt_eq_zero.mp hzero) hxi

/-- **A falsification receiver.**  A prime-blind test of the decay class with zero pole and
archimedean energy whose transform does not vanish at some critical zero ordinate refutes RH. -/
theorem not_riemannHypothesis_of_null_of_paperFT_ne_zero {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0) (hnull : archPoleEnergy F = 0)
    {a : ℝ} (ha : riemannZeta ((1 / 2 : ℂ) + a * I) = 0)
    (hne : paperFT (fun u => (F u : ℂ)) a ≠ 0) : ¬ RiemannHypothesis := fun hRH =>
  hne (paperFT_eq_zero_of_null_of_riemannHypothesis hRH hF hblind hnull ha)

/-! ### The zeta-free spectral identity on prime-blind tests -/

/-- On a truncation, the boundary-measure energy is the pole and archimedean energy minus the
prime pairing. -/
theorem integral_norm_sq_paperFT_truncTest_eq {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (L : ℝ) :
    ∫ r, ‖paperFT (fun u => (truncTest F L u : ℂ)) r‖ ^ 2 ∂boundaryMeasure hW =
      archPoleEnergy (truncTest F L) -
        atomPairing lam (crossCorr (truncTest F L) (truncTest F L)) := by
  have hFL := contDiff_ofReal_truncTest hF L
  have hFLc : HasCompactSupport fun u => (truncTest F L u : ℂ) :=
    (hasCompactSupport_truncTest F L).comp_left Complex.ofReal_zero
  have h := weilFullFunctional_weilTest_self_eq_integral hW hFL hFLc
  rw [integral_complex_ofReal] at h
  have h2 := re_weilFullFunctional_weilTest_truncTest_eq lam hF L
  rw [h, Complex.ofReal_re] at h2
  exact h2

/-- **The spectral identity on the decay class.**  For every full-cone Weil-positive system
`lam` and every real test `F` of the decay class,
`∫ |F̂|² dμ_lam = archPoleEnergy F − abelPrimePairing lam F`: Weil positivity of `lam` holds on the
whole decay class, with the prime side in its absolutely convergent Abel form. -/
theorem integral_norm_sq_paperFT_eq_archPoleEnergy_sub {F : ℝ → ℝ} (hF : ExpDecayTest F)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∫ r, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 ∂boundaryMeasure hW =
      archPoleEnergy F - abelPrimePairing lam F := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨A, hA⟩ := exists_abs_primeWeightPartialSum_le hW
  -- the right side: energies minus prime pairings
  have hR : Tendsto (fun L : ℝ => archPoleEnergy (truncTest F L) -
      atomPairing lam (crossCorr (truncTest F L) (truncTest F L))) atTop
      (𝓝 (archPoleEnergy F - abelPrimePairing lam F)) :=
    (tendsto_archPoleEnergy_truncTest hF).sub
      (tendsto_atomPairing_truncTest_abelPrimePairing hF hA)
  -- the left side: dominated convergence against `μ_lam`
  set M : ℝ := ∫ u, tailMajorant F Λ u with hM
  have hint := (integrable_inv_one_add_sq_boundaryMeasure hW).1.const_mul (M ^ 2)
  have hL : Tendsto (fun L : ℝ => ∫ r, ‖paperFT (fun u => (truncTest F L u : ℂ)) r‖ ^ 2
      ∂boundaryMeasure hW) atTop
      (𝓝 (∫ r, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 ∂boundaryMeasure hW)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun r : ℝ => M ^ 2 * (1 / (1 + r ^ 2))) ?_ ?_ hint ?_
    · refine Eventually.of_forall fun L => ?_
      have hc : Continuous fun r : ℝ => paperFT (fun u => (truncTest F L u : ℂ)) r :=
        WeilHerglotz.continuous_paperFT_real
          ((contDiff_ofReal_truncTest hF.1 L).continuous.integrable_of_hasCompactSupport
            ((hasCompactSupport_truncTest F L).comp_left Complex.ofReal_zero))
      exact (hc.norm.pow 2).aestronglyMeasurable
    · refine Eventually.of_forall fun L => Eventually.of_forall fun r => ?_
      have hr0 : 0 < 1 + |r| := by positivity
      have hu := one_add_abs_mul_norm_paperFT_truncTest_le hF hΛ hΛ0 L r
      have hn : ‖paperFT (fun u => (truncTest F L u : ℂ)) r‖ ≤ M / (1 + |r|) := by
        rw [le_div_iff₀ hr0, mul_comm]; exact hu
      have hsq : (1 + r ^ 2) ≤ (1 + |r|) ^ 2 := by nlinarith [abs_nonneg r, sq_abs r]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖paperFT (fun u => (truncTest F L u : ℂ)) r‖ ^ 2 ≤ (M / (1 + |r|)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hn 2
        _ = M ^ 2 / (1 + |r|) ^ 2 := by rw [div_pow]
        _ ≤ M ^ 2 / (1 + r ^ 2) :=
            div_le_div_of_nonneg_left (sq_nonneg M) (by positivity) hsq
        _ = M ^ 2 * (1 / (1 + r ^ 2)) := by ring
    · refine Eventually.of_forall fun r => ?_
      have hz : |((r : ℂ)).im| ≤ 1 / 2 := by simp
      exact ((tendsto_paperFT_truncTest hF hz).norm.pow 2)
  exact tendsto_nhds_unique (hL.congr fun L => integral_norm_sq_paperFT_truncTest_eq hF.1 hW L) hR

/-- **The zeta-free spectral identity.**  For every full-cone Weil-positive system `lam` and every
prime-blind test `F` of the decay class, `∫ |F̂|² dμ_lam = archPoleEnergy F`.  All points of the
Weil cone therefore agree on prime-blind tests, with values fixed by the archimedean place. -/
theorem integral_norm_sq_paperFT_eq_archPoleEnergy {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0) {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∫ r, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 ∂boundaryMeasure hW = archPoleEnergy F := by
  rw [integral_norm_sq_paperFT_eq_archPoleEnergy_sub hF hW,
    abelPrimePairing_eq_zero_of_blind lam hblind, sub_zero]

/-- **Prime-blind positivity extends to the decay class.**  If the Weil cone is nonempty, the pole
and archimedean energy is nonnegative on every prime-blind test of the decay class. -/
theorem archPoleEnergy_nonneg_of_primeBlindPositive (hP : WeilOneSided.PrimeBlindPositive)
    {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0) : 0 ≤ archPoleEnergy F := by
  obtain ⟨lam, hW⟩ := WeilOneSided.exists_weilPositiveFull_iff_primeBlindPositive.mpr hP
  rw [← integral_norm_sq_paperFT_eq_archPoleEnergy hF hblind hW]
  exact integral_nonneg fun r => by positivity

end RHTower.WeilSpectral
