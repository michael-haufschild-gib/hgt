import GaloisForLFunctions.RHTower.DeckIncompleteEisenstein
import GaloisForLFunctions.RHTower.EisensteinHeckeMaassSelberg
import GaloisForLFunctions.RHTower.EisensteinMaassSelbergRegion
import GaloisForLFunctions.RHTower.FractionalPartZeta
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The horocycle reads the zeros

For a height profile `ψ` vanishing outside `[a, b] ⊂ (1, ∞)` the pseudo-Eisenstein series
`F_ψ(z) = Σ_{(c,d) coprime} ψ(Im M_{c,d} z)` is a `SL₂(ℤ)`-invariant function vanishing high in the
cusp. Its mean along the closed horocycle of height `y` is `A_ψ(y) = ∫_0^1 F_ψ(x + iy) dx`.

**Mellin transform of the horocycle mean** (`mellin_horocycleMean`). For `Re s > 1`,

  `∫_0^∞ A_ψ(y) y^{s-2} dy = 2 ψ̃(s - 1) + 2 (Λ(2s - 1)/Λ(2s)) ψ̃(-s)`,

`ψ̃` the Mellin transform of `ψ`. The left side is the strip integral of `F_ψ Im^s`; unfolding the
strip over the coprime rows turns it into `½ ∫_𝒟 F_ψ Σ_v Im(M_v z)^s`, the row sum is the
Eisenstein series, and on `𝒟` only the cusp term `2ψ(Im z)` of `F_ψ` survives, which pairs with
the constant term `Λ(2s)y^s + Λ(2s-1)y^{1-s}`.

**Zagier's converse** (`re_le_of_horocycle_rate`). If for every smooth `φ` supported in `(1, ∞)`
the horocycle means converge at rate `y^α`, `‖A_φ(y) - c_φ‖ ≤ C_φ y^α` on `(0, 1]`, then every zero
of `ζ` with `Re ρ > 0` has `Re ρ ≤ 2 - 2α`. The constant `c_φ` is arbitrary. The remainder
`A_φ - c_φ 1_{(0,1]}` has a Mellin transform holomorphic on `Re s > 1 - α`, so the identity above
continues `Λ(2s)·(...) = 2Λ(2s - 1)ψ̃(-s)` to the quarter plane `Re s > max(1 - α, 0)`, `Im s > 0`. At
`s₀ = ρ/2` the left side vanishes and `Λ(ρ - 1) = Λ(2 - ρ) ≠ 0`, so `ψ̃(-s₀) = 0` for every bump;
by the fundamental lemma of the calculus of variations `y^{-s₀-1}` would vanish on `(1, ∞)`.

Hence the rate `y^{3/4 - ε}` for every `ε > 0` gives the Riemann hypothesis
(`riemannHypothesis_of_horocycle_rate`): `3/4 = 1/2 + 1/4`, the volume exponent plus the
universal rate, as in the graph form `ArithmeticScatteringHolography.horocycle_rate_iff`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex Asymptotics EisensteinSeries
open scoped MatrixGroups ContDiff

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.DeckPointPair

noncomputable section

/-! ## Pseudo-Eisenstein series and horocycle means -/

/-- The pseudo-Eisenstein series `F_ψ(z) = Σ_{(c,d) coprime} ψ(Im M_{c,d} z)`. -/
def pseudoEisenstein (ψ : ℝ → ℂ) (z : ℍ) : ℂ :=
  ∑' p : gammaSet 1 1 0, ψ (gammaSetMatrix p • z).im

/-- The mean of `F` along the closed horocycle `{x + iy : 0 ≤ x < 1}`. -/
def horocycleMean (F : ℍ → ℂ) (y : ℝ) : ℂ :=
  ∫ x in Ico (0 : ℝ) 1, F (ofComplex ⟨x, y⟩)

theorem im_ofComplex_mk {x y : ℝ} (hy : 0 < y) : (ofComplex (⟨x, y⟩ : ℂ)).im = y := by
  rw [ofComplex_apply_of_im_pos hy]
  rfl

section Profile

variable {ψ : ℝ → ℂ} {a b : ℝ}

theorem pseudoEisenstein_eq_sum {z : ℍ} {S : Finset (gammaSet 1 1 0)}
    (hS : ∀ p ∉ S, ψ (gammaSetMatrix p • z).im = 0) :
    pseudoEisenstein ψ z = ∑ p ∈ S, ψ (gammaSetMatrix p • z).im :=
  tsum_eq_sum hS

/-- Near every point the series is a finite sum of continuous terms. -/
theorem continuous_pseudoEisenstein (hψc : Continuous ψ) (ha : 0 < a)
    (hψa : ∀ y, y < a → ψ y = 0) : Continuous (pseudoEisenstein ψ) := by
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  obtain ⟨S, hS⟩ := exists_finset_profile_eq_zero ha hψa (isCompact_closedBall z₀ 1)
  have heq : (fun z => ∑ p ∈ S, ψ (gammaSetMatrix p • z).im) =ᶠ[𝓝 z₀] pseudoEisenstein ψ := by
    filter_upwards [Metric.closedBall_mem_nhds z₀ one_pos] with z hz
    exact (pseudoEisenstein_eq_sum (hS z hz)).symm
  exact ((continuous_finsetSum S fun p _ =>
    hψc.comp (continuous_im.comp (continuous_modular_smul _))).continuousAt).congr heq

/-- Right multiplication by `A` permutes the coprime rows, up to a translation. -/
theorem im_gammaSetMatrix_smul_smul (A : SL(2, ℤ)) (p : gammaSet 1 1 0) (z : ℍ) :
    (gammaSetMatrix p • A • z).im = (gammaSetMatrix (gammaSetSelfEquiv A p) • z).im := by
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_mul_of_bottomRow_eq (gammaSetMatrix p * A)
    (gammaSetMatrix (gammaSetSelfEquiv A p))
    (by rw [gammaSetMatrix_mul_apply_one, gammaSetMatrix_apply_one_zero, gammaSetSelfEquiv_apply_val])
    (by rw [gammaSetMatrix_mul_apply_one, gammaSetMatrix_apply_one_one, gammaSetSelfEquiv_apply_val])
  rw [← mul_smul, hn, mul_smul, ModularGroup.im_T_zpow_smul]

/-- **Invariance** `F_ψ(Az) = F_ψ(z)`. -/
theorem pseudoEisenstein_smul (A : SL(2, ℤ)) (z : ℍ) :
    pseudoEisenstein ψ (A • z) = pseudoEisenstein ψ z := by
  unfold pseudoEisenstein
  simp_rw [im_gammaSetMatrix_smul_smul A _ z]
  exact (gammaSetSelfEquiv A).tsum_eq (fun p => ψ (gammaSetMatrix p • z).im)

theorem pseudoEisenstein_eq_zero_of_im_gt (ha : 0 < a) (hψa : ∀ y, y < a → ψ y = 0)
    (hψb : ∀ y, b < y → ψ y = 0) {z : ℍ} (hz : max b a⁻¹ < z.im) : pseudoEisenstein ψ z = 0 := by
  rw [pseudoEisenstein_eq_sum (S := ∅) fun p _ => profile_eq_zero_of_im_gt ha hψa hψb hz p]
  simp

/-- On `𝒟` only the two rows `(0, ±1)` reach height `1`, so `F_ψ = 2ψ ∘ Im` there. -/
theorem pseudoEisenstein_of_mem_fd (ha : 1 < a) (hψa : ∀ y, y < a → ψ y = 0) {z : ℍ}
    (hz : z ∈ fd) : pseudoEisenstein ψ z = 2 * ψ z.im := by
  rw [pseudoEisenstein_eq_sum (S := {rowPlus, rowMinus}) fun p hp => ?_]
  · rw [Finset.sum_pair rowPlus_ne_rowMinus]
    change ψ (rowHeight rowPlus z) + ψ (rowHeight rowMinus z) = _
    rw [rowHeight_rowPlus, rowHeight_rowMinus]
    ring
  · have hc : p.1 0 ≠ 0 := by
      intro h0
      rcases (first_zero_iff p).1 h0 with h | h <;> simp [h] at hp
    exact hψa _ (lt_of_le_of_lt (rowHeight_le_one_of_mem_fd hz hc) ha)

theorem exists_norm_pseudoEisenstein_le (hψc : Continuous ψ) (ha : 1 < a)
    (hψa : ∀ y, y < a → ψ y = 0) (hψb : ∀ y, b < y → ψ y = 0) :
    ∃ B, 0 ≤ B ∧ ∀ z, ‖pseudoEisenstein ψ z‖ ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hψc.continuousOn
  refine ⟨2 * max C 0, by positivity, fun z => ?_⟩
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  rw [← pseudoEisenstein_smul g z, pseudoEisenstein_of_mem_fd ha hψa hg, norm_mul]
  have h : ‖ψ (g • z).im‖ ≤ max C 0 := by
    by_cases h1 : (g • z).im < a
    · rw [hψa _ h1, norm_zero]; exact le_max_right _ _
    by_cases h2 : b < (g • z).im
    · rw [hψb _ h2, norm_zero]; exact le_max_right _ _
    exact (hC _ ⟨not_lt.1 h1, not_lt.1 h2⟩).trans (le_max_left _ _)
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  linarith

theorem horocycleMean_eq_zero_of_gt (ha : 0 < a) (hψa : ∀ y, y < a → ψ y = 0)
    (hψb : ∀ y, b < y → ψ y = 0) {y : ℝ} (hy : max b a⁻¹ < y) :
    horocycleMean (pseudoEisenstein ψ) y = 0 := by
  have hy0 : 0 < y := lt_of_le_of_lt ((inv_pos.2 ha).le.trans (le_max_right _ _)) hy
  refine setIntegral_eq_zero_of_forall_eq_zero fun x _ => ?_
  exact pseudoEisenstein_eq_zero_of_im_gt ha hψa hψb (by rw [im_ofComplex_mk hy0]; exact hy)

end Profile

/-! ## Integrability on the strip -/

section Strip

variable {ψ : ℝ → ℂ} {a b : ℝ}

/-- `F_ψ Im^s` on the strip, the integrand of the Mellin transform of the horocycle mean. -/
def stripIntegrand (ψ : ℝ → ℂ) (s : ℂ) (z : ℍ) : ℂ := pseudoEisenstein ψ z * (z.im : ℂ) ^ s

theorem stripIntegrand_T_zpow (s : ℂ) (n : ℤ) (z : ℍ) :
    stripIntegrand ψ s (ModularGroup.T ^ n • z) = stripIntegrand ψ s z := by
  rw [stripIntegrand, stripIntegrand, pseudoEisenstein_smul, ModularGroup.im_T_zpow_smul]

theorem stripChartIntegrand_stripIntegrand {s : ℂ} {p : ℝ × ℝ} (hp : 0 < p.1) :
    stripChartIntegrand (stripIntegrand ψ s) p =
      (p.1 : ℂ) ^ (s - 2) * pseudoEisenstein ψ (ofComplex ⟨p.2, p.1⟩) := by
  have h0 : (p.1 : ℂ) ≠ 0 := ofReal_ne_zero.2 hp.ne'
  rw [stripChartIntegrand, stripIntegrand, im_ofComplex_mk hp, Complex.real_smul,
    cpow_sub _ _ h0, cpow_two]
  push_cast
  field_simp

/-- **Integrability on the strip** for `Re s > 1`: `F_ψ` is bounded and vanishes above `max(b, 1/a)`,
and `∫_0^Y y^{Re s - 2} dy < ∞`. -/
theorem integrableOn_stripIntegrand (hψc : Continuous ψ) (ha : 1 < a)
    (hψa : ∀ y, y < a → ψ y = 0) (hψb : ∀ y, b < y → ψ y = 0) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (stripIntegrand ψ s) modularStrip volume := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_pseudoEisenstein_le hψc ha hψa hψb
  have ha0 : 0 < a := by linarith
  set Y := max b a⁻¹ with hY
  have hY0 : 0 < Y := lt_of_lt_of_le (inv_pos.2 ha0) (le_max_right _ _)
  -- the dominating function `B y^{Re s - 2} 1_{(0, Y]}(y)` on `(0, ∞) × [0, 1)`
  set D : ℝ × ℝ → ℝ := fun p => (Ioc 0 Y).indicator (fun y => B * y ^ (s.re - 2)) p.1 * 1
  have hD : IntegrableOn D (Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1) volume := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine Integrable.mul_prod ?_ (integrableOn_const (C := (1 : ℝ)) (by simp))
    have h1 : IntegrableOn (fun y : ℝ => B * y ^ (s.re - 2)) (Ioc 0 Y) volume :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := Y) (r := s.re - 2)
        (by linarith)).1.const_mul B
    exact (h1.integrable_indicator measurableSet_Ioc).integrableOn
  rw [integrableOn_modularStrip_iff]
  refine Integrable.mono' hD ?_ ?_
  · -- measurability through the chart formula
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (p.1 : ℂ) ^ (s - 2) * pseudoEisenstein ψ (ofComplex ⟨p.2, p.1⟩))
        (Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1) := by
      intro p hp
      have hp0 : (0 : ℝ) < p.1 := hp.1
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.mul ?_ ?_
      · exact ContinuousAt.comp (g := fun w : ℂ => w ^ (s - 2)) (f := fun q : ℝ × ℝ => (q.1 : ℂ))
          (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hp0))
          (Complex.continuous_ofReal.comp continuous_fst).continuousAt
      · have hF := (continuous_pseudoEisenstein hψc ha0 hψa).continuousAt (x := ofComplex ⟨p.2, p.1⟩)
        have hmk : ContinuousAt (fun q : ℝ × ℝ => (⟨q.2, q.1⟩ : ℂ)) p := by
          have : (fun q : ℝ × ℝ => (⟨q.2, q.1⟩ : ℂ)) =
              fun q : ℝ × ℝ => (q.2 : ℂ) + (q.1 : ℂ) * Complex.I := by
            funext q; apply Complex.ext <;> simp
          rw [this]
          fun_prop
        have hoc : ContinuousAt (fun q : ℝ × ℝ => ofComplex (⟨q.2, q.1⟩ : ℂ)) p :=
          (ofComplex.continuousAt (by simp [ofComplex, hp0])).comp hmk
        exact ContinuousAt.comp (f := fun q : ℝ × ℝ => ofComplex (⟨q.2, q.1⟩ : ℂ)) (x := p) hF hoc
    refine (hcont.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ico)).congr ?_
    exact (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ico)).2
      (Eventually.of_forall fun p hp => (stripChartIntegrand_stripIntegrand hp.1).symm)
  · refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ico)).2
      (Eventually.of_forall fun p hp => ?_)
    have hp0 : (0 : ℝ) < p.1 := hp.1
    rw [stripChartIntegrand_stripIntegrand hp0, norm_mul, norm_cpow_eq_rpow_re_of_pos hp0]
    simp only [D, mul_one]
    by_cases hpY : p.1 ≤ Y
    · rw [indicator_of_mem (show p.1 ∈ Ioc 0 Y from ⟨hp0, hpY⟩)]
      have : (s - 2).re = s.re - 2 := by simp
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_right (hB _) (Real.rpow_nonneg hp0.le _)
    · rw [indicator_of_notMem (show p.1 ∉ Ioc 0 Y from fun h => hpY h.2),
        pseudoEisenstein_eq_zero_of_im_gt ha0 hψa hψb
          (by rw [im_ofComplex_mk hp0]; exact not_le.1 hpY), norm_zero, mul_zero]

/-- The Mellin integrand of the horocycle mean is integrable: Fubini on the strip. -/
theorem mellinConvergent_horocycleMean (hψc : Continuous ψ) (ha : 1 < a)
    (hψa : ∀ y, y < a → ψ y = 0) (hψb : ∀ y, b < y → ψ y = 0) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (horocycleMean (pseudoEisenstein ψ)) (s - 1) := by
  have h := (integrableOn_modularStrip_iff _).1 (integrableOn_stripIntegrand hψc ha hψa hψb hs)
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  have h2 := h.integral_prod_left
  unfold MellinConvergent
  refine (h2.congr ?_ : IntegrableOn _ (Ioi (0 : ℝ)) volume)
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_)
  have hy0 : (0 : ℝ) < y := hy
  show ∫ x in Ico (0 : ℝ) 1, stripChartIntegrand (stripIntegrand ψ s) (y, x) =
    (y : ℂ) ^ (s - 1 - 1) • horocycleMean (pseudoEisenstein ψ) y
  rw [horocycleMean, smul_eq_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
  rw [stripChartIntegrand_stripIntegrand (p := (y, x)) hy0]
  congr 2
  ring

/-- **Fubini on the strip**: the strip integral of `F_ψ Im^s` is the Mellin transform of the
horocycle mean at `s - 1`. -/
theorem setIntegral_stripIntegrand (hψc : Continuous ψ) (ha : 1 < a)
    (hψa : ∀ y, y < a → ψ y = 0) (hψb : ∀ y, b < y → ψ y = 0) {s : ℂ} (hs : 1 < s.re) :
    ∫ z in modularStrip, stripIntegrand ψ s z = mellin (horocycleMean (pseudoEisenstein ψ)) (s - 1) := by
  rw [setIntegral_modularStrip_eq_iterated _ (integrableOn_stripIntegrand hψc ha hψa hψb hs), mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have h0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy0.ne'
  rw [horocycleMean, smul_eq_mul, ← integral_const_mul, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
  rw [stripIntegrand, im_ofComplex_mk hy0, Complex.real_smul, show s - 1 - 1 = s - 2 by ring,
    cpow_sub _ _ h0, cpow_two]
  push_cast
  field_simp

end Strip

/-! ## The Mellin transform of the horocycle mean -/

section Mellin

variable {ψ : ℝ → ℂ} {a b : ℝ}

/-- Unfolding: `2 ∫_{strip} F_ψ Im^s = ∫_𝒟 F_ψ(z) Σ_v Im(M_v z)^s`. -/
theorem two_mul_setIntegral_stripIntegrand (hψc : Continuous ψ) (ha : 1 < a)
    (hψa : ∀ y, y < a → ψ y = 0) (hψb : ∀ y, b < y → ψ y = 0) {s : ℂ} (hs : 1 < s.re) :
    2 * ∫ z in modularStrip, stripIntegrand ψ s z =
      ∫ z in fd, pseudoEisenstein ψ z * rowSum s z := by
  have hint := integrableOn_stripIntegrand hψc ha hψa hψb hs
  have hφ : ∀ (n : ℤ) (z : ℍ), stripIntegrand ψ s (ModularGroup.T ^ n • z) = stripIntegrand ψ s z :=
    stripIntegrand_T_zpow s
  rw [← tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip _ hφ hint]
  have hterm : ∀ (v : gammaSet 1 1 0) (z : ℍ), stripIntegrand ψ s (gammaSetMatrix v • z) =
      pseudoEisenstein ψ z * (rowHeight v z : ℂ) ^ s := fun v z => by
    rw [stripIntegrand, pseudoEisenstein_smul]
    rfl
  simp_rw [hterm]
  -- the norms are summable: unfold `‖F_ψ Im^s‖`
  have hφn : ∀ (n : ℤ) (z : ℍ), ((‖stripIntegrand ψ s (ModularGroup.T ^ n • z)‖ : ℝ) : ℂ) =
      ((‖stripIntegrand ψ s z‖ : ℝ) : ℂ) := fun n z => by rw [hφ]
  have hsum := summable_fdUnfoldTerm hφn hint.norm.ofReal
  unfold fdUnfoldTerm at hsum
  simp_rw [integral_ofReal, hterm] at hsum
  rw [integral_tsum_of_summable_integral_norm (fun v => ?_) (Complex.summable_ofReal.1 hsum)]
  · refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
    rw [rowSum, tsum_mul_left]
  · have h1 := (integrableOn_smul_set_iff (gammaSetMatrix v) _ fd).1
      (integrableOn_smul_fd_of_periodic hφ hint (gammaSetMatrix v))
    refine h1.congr_fun (fun z _ => hterm v z) isClosed_fd.measurableSet

/-- On `𝒟` the integrand is a band integrand against the Eisenstein series `E*(z, s)`. -/
theorem pseudoEisenstein_mul_rowSum_of_mem_fd (ha : 1 < a) (hψa : ∀ y, y < a → ψ y = 0)
    (hψb : ∀ y, b < y → ψ y = 0) {s : ℂ} (hs : 1 < s.re) {z : ℍ} (hz : z ∈ fd) :
    pseudoEisenstein ψ z * rowSum s z =
      if 1 < z.im ∧ z.im ≤ b then
        4 * ψ z.im / msA (s - 1 / 2) * eisensteinLineModel (s - 1 / 2) z else 0 := by
  rw [pseudoEisenstein_of_mem_fd ha hψa hz]
  split_ifs with h
  · have hu : 1 / 2 < (s - 1 / 2).re := by simp; linarith
    have hA := msA_ne_zero_of_re hu
    rw [eisensteinLineModel_eq_rowSum hu, show (1 / 2 : ℂ) + (s - 1 / 2) = s by ring]
    generalize msA (s - 1 / 2) = A at hA ⊢
    field_simp
    ring
  · have : ψ z.im = 0 := by
      rcases not_and_or.1 h with h1 | h1
      · exact hψa _ (by linarith [not_lt.1 h1])
      · exact hψb _ (not_le.1 h1)
    rw [this]
    ring

theorem cpow_div_sq {y : ℝ} (hy : 0 < y) (w : ℂ) :
    (y : ℂ) ^ w / ((y : ℝ) : ℂ) ^ 2 = (y : ℂ) ^ (w - 2) := by
  rw [cpow_sub _ _ (ofReal_ne_zero.2 hy.ne'), cpow_two]

/-- **The Mellin transform of the horocycle mean.** For `Re s > 1`,
`∫_0^∞ A_ψ(y) y^{s-2} dy = 2ψ̃(s - 1) + 2 (Λ(2s - 1)/Λ(2s)) ψ̃(-s)`. -/
theorem mellin_horocycleMean (hψc : Continuous ψ) (ha : 1 < a)
    (hψa : ∀ y, y < a → ψ y = 0) (hψb : ∀ y, b < y → ψ y = 0) {s : ℂ} (hs : 1 < s.re) :
    mellin (horocycleMean (pseudoEisenstein ψ)) (s - 1) =
      2 * mellin ψ (s - 1) + 2 * (msB (s - 1 / 2) / msA (s - 1 / 2)) * mellin ψ (-s) := by
  have hu : 1 / 2 < (s - 1 / 2).re := by simp; linarith
  have hA := msA_ne_zero_of_re hu
  have h1 : (1 : ℝ) ≤ 1 := le_rfl
  -- the band integral against the constant term
  have hband := setIntegral_band_mul_line (s - 1 / 2) (Y₂ := b) h1 (fun y => 4 * ψ y / msA (s - 1 / 2))
    ((hψc.const_mul 4).div_const _).continuousOn
  rw [← setIntegral_stripIntegrand hψc ha hψa hψb hs]
  have h2 := two_mul_setIntegral_stripIntegrand hψc ha hψa hψb hs
  rw [setIntegral_congr_fun isClosed_fd.measurableSet
    (fun z hz => pseudoEisenstein_mul_rowSum_of_mem_fd ha hψa hψb hs hz), hband] at h2
  -- pointwise algebra on `(1, b]`
  have hpt : ∀ y ∈ Ioc (1 : ℝ) b,
      4 * ψ y / msA (s - 1 / 2) * d4BMCompletedEisensteinCuspConstantPart .scalar (s - 1 / 2) y /
        ((y : ℝ) : ℂ) ^ 2 =
      2 * (2 * ((y : ℂ) ^ (s - 1 - 1) • ψ y)) +
        2 * (2 * (msB (s - 1 / 2) / msA (s - 1 / 2)) * ((y : ℂ) ^ (-s - 1) • ψ y)) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := by linarith [hy.1]
    rw [cuspConstantPart_eq_msAB, show (1 / 2 : ℂ) - (s - 1 / 2) = 1 - s by ring,
      show (1 / 2 : ℂ) + (s - 1 / 2) = s by ring, smul_eq_mul, smul_eq_mul,
      show s - 1 - 1 = s - 2 by ring, show -s - 1 = (1 - s) - 2 by ring, ← cpow_div_sq hy0,
      ← cpow_div_sq hy0]
    have hy2 : ((y : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (ofReal_ne_zero.2 hy0.ne')
    generalize msA (s - 1 / 2) = A at hA ⊢
    generalize msB (s - 1 / 2) = M
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt] at h2
  -- the two pieces are integrable on `(1, b]`
  have hcont : ∀ w : ℂ, IntegrableOn (fun y : ℝ => (y : ℂ) ^ w • ψ y) (Ioc 1 b) volume := by
    intro w
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    refine ContinuousOn.smul (f := fun y : ℝ => (y : ℂ) ^ w) (g := ψ) (fun y hy => ?_)
      hψc.continuousOn
    have hy0 : (0 : ℝ) < y := by linarith [hy.1]
    exact ((continuousAt_cpow_const (ofReal_mem_slitPlane.2 hy0)).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  rw [integral_add (((hcont _).const_mul 2).const_mul 2) (((hcont _).const_mul _).const_mul 2),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul] at h2
  -- the Mellin integrals live on `(1, b]`
  have hsupp : ∀ w : ℂ, mellin ψ w = ∫ y in Ioc 1 b, (y : ℂ) ^ (w - 1) • ψ y := by
    intro w
    rw [mellin]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun y hy => lt_trans one_pos hy.1) fun y hy => ?_
    have : ψ y = 0 := by
      by_cases h : y ≤ 1
      · exact hψa _ (by linarith)
      · exact hψb _ (by
          by_contra h'
          exact hy.2 ⟨not_le.1 h, not_lt.1 h'⟩)
    rw [this, smul_zero]
  rw [hsupp, hsupp, show -s - 1 = -s - 1 by rfl]
  linear_combination h2 / 2

end Mellin

/-! ## Zagier's converse -/

section Converse

/-- A function with compact support inside `(1, ∞)` vanishes outside some `[a, b]` with `a > 1`. -/
theorem exists_band_of_tsupport {φ : ℝ → ℝ} (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 1) :
    ∃ a b : ℝ, 1 < a ∧ a ≤ b ∧ (∀ y, y < a → φ y = 0) ∧ ∀ y, b < y → φ y = 0 := by
  have hK : IsCompact (tsupport φ ∪ {2}) := hc.isCompact.union isCompact_singleton
  have hne : (tsupport φ ∪ {2}).Nonempty := ⟨2, Or.inr rfl⟩
  obtain ⟨a, ha, hamin⟩ := hK.exists_isMinOn hne continuousOn_id
  obtain ⟨b, -, hbmax⟩ := hK.exists_isMaxOn hne continuousOn_id
  refine ⟨a, b, ?_, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rcases ha with ha | ha
    · exact hs ha
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      norm_num
  · have h1 := isMinOn_iff.1 hamin 2 (Or.inr rfl)
    have h2 := isMaxOn_iff.1 hbmax 2 (Or.inr rfl)
    simp only [id] at h1 h2
    linarith
  · by_contra hne'
    have := isMinOn_iff.1 hamin y (Or.inl (subset_tsupport _ hne'))
    simp only [id] at this
    linarith
  · by_contra hne'
    have := isMaxOn_iff.1 hbmax y (Or.inl (subset_tsupport _ hne'))
    simp only [id] at this
    linarith

/-- The quarter plane `Re s > max(1 - α, 0)`, `Im s > 0`, on which the continuation lives. -/
def quarterPlane (α : ℝ) : Set ℂ := {s | max (1 - α) 0 < s.re ∧ 0 < s.im}

theorem isOpen_quarterPlane (α : ℝ) : IsOpen (quarterPlane α) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

theorem isPreconnected_quarterPlane (α : ℝ) : IsPreconnected (quarterPlane α) :=
  ((convex_halfSpace_re_gt (max (1 - α) 0)).inter (convex_halfSpace_im_gt 0)).isPreconnected

theorem mem_eisensteinLineDomain_of_mem_quarterPlane {α : ℝ} {s : ℂ} (hs : s ∈ quarterPlane α) :
    s - 1 / 2 ∈ eisensteinLineDomain := by
  have h0 : 0 < s.re := lt_of_le_of_lt (le_max_right _ _) hs.1
  refine ⟨?_, ?_⟩ <;> simp <;> linarith [hs.2]

/-- The Mellin transform of a profile vanishing outside `[a, b] ⊂ (0, ∞)` is entire. -/
theorem differentiableAt_mellin_of_band {ψ : ℝ → ℂ} (hψc : Continuous ψ) {a b : ℝ} (ha : 0 < a)
    (hψa : ∀ y, y < a → ψ y = 0) (hψb : ∀ y, b < y → ψ y = 0) (w : ℂ) :
    DifferentiableAt ℂ (mellin ψ) w := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := w.re + 1) (b := w.re - 1)
    (hψc.continuousOn.locallyIntegrableOn measurableSet_Ioi) ?_ (by linarith) ?_ (by linarith)
  · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop b] with y hy using (hψb y hy).symm
  · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy using (hψa y hy.2).symm

/-- **The continuation.** If the horocycle mean converges at rate `y^α` on `(0, 1]`, then on the
quarter plane `Λ(2s)(M(s) + c/(s - 1) - 2ψ̃(s - 1)) = 2Λ(2s - 1)ψ̃(-s)`, `M` the Mellin transform
of the remainder `A_ψ - c 1_{(0,1]}`, holomorphic on `Re s > 1 - α`. At a zero of `Λ(2s)` the right
side vanishes. -/
theorem msB_mul_mellin_eq_zero_of_rate {α : ℝ} {ψ : ℝ → ℂ} (hψc : Continuous ψ) {a b : ℝ}
    (ha : 1 < a) (hψa : ∀ y, y < a → ψ y = 0) (hψb : ∀ y, b < y → ψ y = 0) {c : ℂ} {C : ℝ}
    (hrate : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖horocycleMean (pseudoEisenstein ψ) y - c‖ ≤ C * y ^ α)
    {s₀ : ℂ} (hs₀ : s₀ ∈ quarterPlane α) (hA : msA (s₀ - 1 / 2) = 0) :
    msB (s₀ - 1 / 2) * mellin ψ (-s₀) = 0 := by
  set A := horocycleMean (pseudoEisenstein ψ) with hAdef
  set ind : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator fun _ => c with hind
  set g : ℝ → ℂ := fun y => A y - ind y with hg
  have ha0 : 0 < a := by linarith
  have hind_smul : ind = fun y => c • (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) y := by
    funext y
    by_cases hy : y ∈ Ioc (0 : ℝ) 1 <;> simp [hind, hy]
  have hindM : ∀ w : ℂ, 0 < w.re → MellinConvergent ind w ∧ mellin ind w = c / w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hasMellin_one_Ioc hw
    rw [hind_smul]
    refine ⟨h1.const_smul c, ?_⟩
    rw [mellin_const_smul, h2, smul_eq_mul]
    ring
  -- `A` is integrable on `(0, ∞)`
  have hAint : IntegrableOn A (Ioi 0) := by
    have h := mellinConvergent_horocycleMean hψc ha hψa hψb (s := 2) (by norm_num)
    refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
    norm_num
    rfl
  have hindint : IntegrableOn ind (Ioi 0) := by
    have := (hindM 1 one_pos).1
    refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
    norm_num
  -- the Mellin transform of `A` splits
  have hsplit : ∀ s : ℂ, 1 < s.re → mellin A (s - 1) = mellin g (s - 1) + c / (s - 1) := by
    intro s hs
    have hw : 0 < (s - 1).re := by simp; linarith
    have hAM := mellinConvergent_horocycleMean hψc ha hψa hψb hs
    obtain ⟨hiM, hiV⟩ := hindM (s - 1) hw
    have hgM : MellinConvergent g (s - 1) := by
      refine (hAM.sub hiM).congr_fun (fun y _ => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply, hg, smul_sub]
      rfl
    rw [← hiV, mellin, mellin, mellin, ← integral_add hgM hiM]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [hg, smul_sub, sub_add_cancel]
  -- the identity on `Re s > 1`
  have heq : ∀ s : ℂ, 1 < s.re →
      msA (s - 1 / 2) * (mellin g (s - 1) + c / (s - 1) - 2 * mellin ψ (s - 1)) =
        2 * msB (s - 1 / 2) * mellin ψ (-s) := by
    intro s hs
    have hu : 1 / 2 < (s - 1 / 2).re := by simp; linarith
    have hA0 := msA_ne_zero_of_re hu
    rw [← hsplit s hs, mellin_horocycleMean hψc ha hψa hψb hs]
    generalize msA (s - 1 / 2) = M at hA0 ⊢
    field_simp
    ring
  -- holomorphy on the quarter plane
  have hgint : LocallyIntegrableOn g (Ioi 0) := (hAint.sub hindint).locallyIntegrableOn
  have hg_top : ∀ w : ℂ, g =O[atTop] (· ^ (-(w.re + 1))) := by
    intro w
    refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (max (max b a⁻¹) 1)] with y hy
    have h1 : max b a⁻¹ < y := lt_of_le_of_lt (le_max_left _ _) hy
    have h2 : ¬ y ≤ 1 := not_le.2 (lt_of_le_of_lt (le_max_right _ _) hy)
    simp [hg, hAdef, horocycleMean_eq_zero_of_gt ha0 hψa hψb h1, hind, h2]
  have hg_bot : g =O[𝓝[>] 0] (· ^ (-(-α))) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy
    have hy1 : y ∈ Ioc (0 : ℝ) 1 := ⟨hy.1, hy.2.le⟩
    rw [neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg hy.1.le _)]
    simpa [hg, hind, indicator_of_mem hy1] using hrate y hy.1 hy.2.le
  have hdiff : ∀ s ∈ quarterPlane α, DifferentiableAt ℂ
      (fun s => msA (s - 1 / 2) * (mellin g (s - 1) + c / (s - 1) - 2 * mellin ψ (s - 1))) s ∧
      DifferentiableAt ℂ (fun s => 2 * msB (s - 1 / 2) * mellin ψ (-s)) s := by
    intro s hs
    have hL := mem_eisensteinLineDomain_of_mem_quarterPlane hs
    have hsub : DifferentiableAt ℂ (fun s : ℂ => s - 1 / 2) s := differentiableAt_id.sub_const _
    have hmA := (hasDerivAt_msA hL).differentiableAt.comp s hsub
    have hmB := (hasDerivAt_msB hL).differentiableAt.comp s hsub
    have hs1 : s - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith [hs.2]
    have hre : -α < (s - 1).re := by
      have := lt_of_le_of_lt (le_max_left _ _) hs.1
      simp
      linarith
    have hmg : DifferentiableAt ℂ (mellin g) (s - 1) :=
      mellin_differentiableAt_of_isBigO_rpow hgint (hg_top (s - 1)) (by linarith) hg_bot hre
    have hmψ := differentiableAt_mellin_of_band hψc ha0 hψa hψb
    refine ⟨hmA.mul (((hmg.comp s (differentiableAt_id.sub_const 1)).add
      ((differentiableAt_const c).div (differentiableAt_id.sub_const 1) hs1)).sub
      (((hmψ (s - 1)).comp s (differentiableAt_id.sub_const 1)).const_mul 2)), ?_⟩
    exact (hmB.const_mul 2).mul ((hmψ (-s)).comp s differentiableAt_id.neg)
  have hU := isOpen_quarterPlane α
  have hf₁ : AnalyticOnNhd ℂ
      (fun s => msA (s - 1 / 2) * (mellin g (s - 1) + c / (s - 1) - 2 * mellin ψ (s - 1)))
      (quarterPlane α) :=
    DifferentiableOn.analyticOnNhd (fun s hs => (hdiff s hs).1.differentiableWithinAt) hU
  have hf₂ : AnalyticOnNhd ℂ (fun s => 2 * msB (s - 1 / 2) * mellin ψ (-s)) (quarterPlane α) :=
    DifferentiableOn.analyticOnNhd (fun s hs => (hdiff s hs).2.differentiableWithinAt) hU
  -- a base point with `Re > 1`
  set z₀ : ℂ := ((max (1 - α) 1 + 1 : ℝ) : ℂ) + Complex.I with hz₀
  have hz₀re : z₀.re = max (1 - α) 1 + 1 := by simp [hz₀]
  have hz₀U : z₀ ∈ quarterPlane α := by
    refine ⟨?_, by simp [hz₀]⟩
    rw [hz₀re]
    have : max (1 - α) 0 ≤ max (1 - α) 1 := max_le_max le_rfl zero_le_one
    linarith
  have hev : (fun s => msA (s - 1 / 2) * (mellin g (s - 1) + c / (s - 1) - 2 * mellin ψ (s - 1)))
      =ᶠ[𝓝 z₀] fun s => 2 * msB (s - 1 / 2) * mellin ψ (-s) := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
    have hmem : z₀ ∈ {s : ℂ | 1 < s.re} := by
      show 1 < z₀.re
      rw [hz₀re]
      linarith [le_max_right (1 - α) 1]
    filter_upwards [hopen.mem_nhds hmem] with s hs using heq s hs
  have hEq := hf₁.eqOn_of_preconnected_of_eventuallyEq hf₂ (isPreconnected_quarterPlane α) hz₀U
    hev hs₀
  simp only [hA, zero_mul] at hEq
  have := hEq.symm
  rw [mul_assoc] at this
  exact (mul_eq_zero.1 this).resolve_left two_ne_zero

/-- `Λ(ρ - 1) = Λ(2 - ρ) ≠ 0` for a zero `ρ` in the open strip off the real axis. -/
theorem msB_ne_zero_of_zero {ρ : ℂ} (hρ1 : ρ.re < 1) (him : 0 < ρ.im) :
    msB (ρ / 2 - 1 / 2) ≠ 0 := by
  have hw : 2 * (ρ / 2 - 1 / 2) = ρ - 1 := by ring
  rw [msB, hw, reflectedCompletedLambda]
  have hG : ∀ w : ℂ, 0 < w.im → Gammaℝ w ≠ 0 := by
    intro w hw h
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.1 h
    have := congrArg Complex.im hn
    simp at this
    linarith
  have h1 : (ρ - 1).im = ρ.im := by simp
  have h2re : 1 < (2 - ρ).re := by simp; linarith
  have h2im : (2 - ρ).im = -ρ.im := by simp
  have hΛ2 : completedRiemannZeta (2 - ρ) ≠ 0 := by
    intro h
    have hz := riemannZeta_def_of_ne_zero (s := 2 - ρ) (by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith)
    rw [h, zero_div] at hz
    exact riemannZeta_ne_zero_of_one_lt_re h2re hz
  have hΛ : completedRiemannZeta (ρ - 1) ≠ 0 := by
    have := completedRiemannZeta_one_sub (2 - ρ)
    rw [show 1 - (2 - ρ) = ρ - 1 by ring] at this
    rw [this]
    exact hΛ2
  have hne : ρ - 1 ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp at this; linarith
  refine mul_ne_zero (hG _ (by rw [h1]; exact him)) ?_
  rw [riemannZeta_def_of_ne_zero hne]
  exact div_ne_zero hΛ (hG _ (by rw [h1]; exact him))

/-- **Zagier's converse.** If the horocycle means of all smooth pseudo-Eisenstein series with
profile supported in `(1, ∞)` converge at rate `y^α`, then every zero of `ζ` with positive real
part has `Re ρ ≤ 2 - 2α`. -/
theorem re_le_of_horocycle_rate {α : ℝ}
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 1 →
      ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y - c‖ ≤ C * y ^ α)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re) : ρ.re ≤ 2 - 2 * α := by
  by_contra hlt
  push Not at hlt
  have hρ1 : ρ.re < 1 := by
    by_contra h1
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 h1) hρ
  -- a zero with the same real part in the upper half plane
  obtain ⟨ρ', hρ', hre', him'⟩ : ∃ ρ' : ℂ, riemannZeta ρ' = 0 ∧ ρ'.re = ρ.re ∧ 0 < ρ'.im := by
    rcases lt_trichotomy ρ.im 0 with hi | hi | hi
    · refine ⟨(starRingEnd ℂ) ρ, by rw [riemannZeta_conj, hρ, map_zero], by simp, ?_⟩
      simp
      linarith
    · exfalso
      have hreal : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hi])
      exact riemannZeta_ne_zero_of_ofReal_mem_Ioo hρ0 hρ1 (hreal ▸ hρ)
    · exact ⟨ρ, hρ, rfl, hi⟩
  set s₀ : ℂ := ρ' / 2 with hs₀def
  have hs₀ : s₀ ∈ quarterPlane α := by
    refine ⟨max_lt ?_ ?_, ?_⟩ <;> simp [hs₀def] <;> linarith
  have hA : msA (s₀ - 1 / 2) = 0 := by
    rw [msA, show 1 + 2 * (s₀ - 1 / 2) = ρ' by rw [hs₀def]; ring, reflectedCompletedLambda, hρ',
      mul_zero]
  have hB : msB (s₀ - 1 / 2) ≠ 0 := msB_ne_zero_of_zero (by rw [hre']; exact hρ1) him'
  -- every admissible bump has `ψ̃(-s₀) = 0`
  have hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 1 →
      mellin (fun t => (φ t : ℂ)) (-s₀) = 0 := by
    intro φ hφ hc hs
    obtain ⟨a, b, ha, -, hφa, hφb⟩ := exists_band_of_tsupport hc hs
    obtain ⟨c, C, hrate⟩ := h φ hφ hc hs
    have := msB_mul_mellin_eq_zero_of_rate (a := a) (b := b)
      (Complex.continuous_ofReal.comp hφ.continuous) ha
      (fun y hy => by simp [hφa y hy]) (fun y hy => by simp [hφb y hy]) hrate hs₀ hA
    exact (mul_eq_zero.1 this).resolve_left hB
  -- the fundamental lemma: `y^{-s₀-1}` would vanish on `(1, ∞)`
  set f : ℝ → ℂ := fun y => (y : ℂ) ^ (-s₀ - 1) with hf
  have hfint : LocallyIntegrableOn f (Ioi 1) := by
    refine ContinuousOn.locallyIntegrableOn (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    exact ((continuousAt_cpow_const (ofReal_mem_slitPlane.2 hy0)).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hae := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfint
    (fun g hg hgc hgs => by
      rw [← hzero g hg hgc hgs, mellin,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) (fun y hy => ?_)]
      · refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
        simp only [hf, Complex.real_smul, smul_eq_mul]
        ring
      · have : g y = 0 :=
          image_eq_zero_of_notMem_tsupport fun h' =>
            hy (mem_Ioi.2 (lt_trans one_pos (mem_Ioi.1 (hgs h'))))
        simp [this])
  have hnull : volume (Ioi (1 : ℝ)) = 0 := by
    rw [ae_iff] at hae
    refine measure_mono_null (fun y hy => ?_) hae
    have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 (lt_trans one_pos hy).ne'
    simp only [mem_setOf_eq, Classical.not_imp]
    exact ⟨hy, by simp [hf, cpow_eq_zero_iff, hy0]⟩
  rw [Real.volume_Ioi] at hnull
  exact ENNReal.top_ne_zero hnull

/-- **Horocycle equidistribution at rate `y^{3/4 - ε}` gives the Riemann hypothesis.** -/
theorem riemannHypothesis_of_horocycle_rate
    (h : ∀ ε : ℝ, 0 < ε → ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioi 1 → ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y - c‖ ≤ C * y ^ (3 / 4 - ε)) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hρ, hρ1, -⟩ := _root_.RHTower.exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  set ε := (ρ.re - 1 / 2) / 4 with hε
  have := re_le_of_horocycle_rate (h ε (by rw [hε]; linarith)) hρ (by linarith)
  rw [hε] at this
  linarith

end Converse

end

end GaloisForLFunctions.BlackHoleRingdown
