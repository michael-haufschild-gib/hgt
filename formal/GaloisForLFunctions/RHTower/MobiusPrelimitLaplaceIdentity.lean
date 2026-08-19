import GaloisForLFunctions.RHTower.MobiusCriticalLaplaceIdentity
import GaloisForLFunctions.RHTower.MobiusPrelimitSafeWidth

/-!
# The prelimit causal Laplace transform

The same Tonelli interchange as at the critical abscissa computes the causal transform of the
weighted Mertens partial sums at any abscissa `a > 1`, and hence the transform of the centered
prelimit vector: card equation `(16)`.
-/

open MeasureTheory Set Filter ArithmeticFunction LSeries
open scoped Topology LSeries.notation Moebius

namespace RHTower

noncomputable section

/-- The `n`-th atom of the causal Möbius transform at abscissa `a`. -/
def mertensAtomAt (a : ℝ) (w : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  Set.indicator (Ici (Real.log n)) (fun s : ℝ => Complex.exp (-(w * (s : ℂ)))) t
    * mobiusRealWeight a n

theorem norm_mertensAtomAt (a : ℝ) (w : ℂ) (n : ℕ) (t : ℝ) :
    ‖mertensAtomAt a w n t‖
      = Set.indicator (Ici (Real.log n)) (fun s : ℝ => Real.exp (-(w.re * s))) t
        * ‖mobiusRealWeight a n‖ := by
  rw [mertensAtomAt, norm_mul]
  congr 1
  by_cases h : t ∈ Ici (Real.log n)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, norm_zero]

theorem integrableOn_mertensAtomAt {w : ℂ} (hw : 0 < w.re) (a : ℝ) (n : ℕ) :
    IntegrableOn (mertensAtomAt a w n) (Ioi (0 : ℝ)) volume := by
  unfold mertensAtomAt
  refine Integrable.mul_const ?_ _
  exact (GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul hw).indicator
    measurableSet_Ici

theorem integral_mertensAtomAt {w : ℂ} (hw : 0 < w.re) (a : ℝ) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), mertensAtomAt a w n t)
      = mobiusRealWeight a n * (Complex.exp (-(w * ((Real.log n : ℝ) : ℂ))) / w) := by
  simp only [mertensAtomAt]
  rw [MeasureTheory.integral_mul_const,
    MeasureTheory.setIntegral_indicator measurableSet_Ici,
    MeasureTheory.setIntegral_congr_set (ioi_inter_ici_ae (log_natCast_nonneg n)),
    GaloisForLFunctions.RHTower.integral_Ioi_cexp_neg_mul_shift hw (Real.log n)]
  ring

theorem integral_norm_mertensAtomAt {w : ℂ} (hw : 0 < w.re) (a : ℝ) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖mertensAtomAt a w n t‖)
      = ‖mobiusRealWeight a n‖ * (Real.exp (-(w.re * Real.log n)) / w.re) := by
  simp only [norm_mertensAtomAt]
  rw [MeasureTheory.integral_mul_const,
    MeasureTheory.setIntegral_indicator measurableSet_Ici,
    MeasureTheory.setIntegral_congr_set (ioi_inter_ici_ae (log_natCast_nonneg n)),
    integral_Ioi_exp_neg_mul_shift hw (Real.log n)]
  ring

theorem weight_mul_cexp_eq_termAt {w : ℂ} (a : ℝ) (n : ℕ) :
    mobiusRealWeight a n * Complex.exp (-(w * ((Real.log n : ℝ) : ℂ)))
      = LSeries.term (↗μ) ((a : ℂ) + w) n := by
  by_cases hn : n = 0
  · subst hn
    simp [mobiusRealWeight]
  · have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [cexp_neg_mul_log_eq_cpow (w := w) hn, mobiusRealWeight_eq_term,
      LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_add _ _ hne, Complex.cpow_neg]
    field_simp

theorem integral_norm_atomAt_le {w : ℂ} (hw : 0 < w.re) {a : ℝ} (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖mertensAtomAt a w n t‖) ≤ (n : ℝ) ^ (-(a + w.re)) / w.re := by
  rw [integral_norm_mertensAtomAt hw a n]
  by_cases hn : n = 0
  · subst hn
    simp [mobiusRealWeight]
    positivity
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hexp : Real.exp (-(w.re * Real.log n)) = (n : ℝ) ^ (-w.re) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    have hsplit : (n : ℝ) ^ (-(a + w.re)) = (n : ℝ) ^ (-a) * (n : ℝ) ^ (-w.re) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    rw [hexp, hsplit, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (norm_mobiusRealWeight_le a n) (by positivity)

theorem summable_integral_norm_mertensAtomAt {w : ℂ} (hw : 0 < w.re) {a : ℝ} (ha : 1 < a) :
    Summable (fun n : ℕ => ∫ t in Ioi (0 : ℝ), ‖mertensAtomAt a w n t‖) := by
  refine Summable.of_nonneg_of_le (fun n => MeasureTheory.integral_nonneg fun t => norm_nonneg _)
    (fun n => integral_norm_atomAt_le hw n) ?_
  exact (Real.summable_nat_rpow.mpr (by linarith : -(a + w.re) < -1)).div_const _

theorem tsum_mertensAtomAt {a : ℝ} {w : ℂ} {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, mertensAtomAt a w n t)
      = Complex.exp (-(w * (t : ℂ))) * mobiusWeightedPartial a t := by
  classical
  set M : ℕ := ⌊Real.exp t⌋₊ with hM
  have hzero : ∀ n ∉ Finset.range (M + 1), mertensAtomAt a w n t = 0 := by
    intro n hn
    have hMn : M < n := by simpa [Nat.lt_succ_iff] using hn
    have hexp : Real.exp t < (n : ℝ) := (Nat.floor_lt (Real.exp_pos t).le).mp hMn
    have hn1 : 1 ≤ n := by
      by_contra hcon
      have hn0 : n = 0 := by omega
      rw [hn0] at hexp
      simp only [Nat.cast_zero] at hexp
      exact absurd hexp (not_lt.mpr (Real.exp_pos t).le)
    have hlog : t < Real.log n := by
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have h := Real.log_lt_log (Real.exp_pos t) hexp
      rwa [Real.log_exp] at h
    simp only [mertensAtomAt]
    rw [Set.indicator_of_notMem (by simp only [mem_Ici]; linarith), zero_mul]
  rw [tsum_eq_sum hzero]
  have hval : ∀ n ∈ Finset.range (M + 1),
      mertensAtomAt a w n t = Complex.exp (-(w * (t : ℂ))) * mobiusRealWeight a n := by
    intro n hn
    have hnM : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hlogle : Real.log n ≤ t := by
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · rw [hn0]
        simpa using ht.le
      · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
        have hny : (n : ℝ) ≤ Real.exp t := by
          calc (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnM
            _ ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
        have h := Real.log_le_log hnpos hny
        rwa [Real.log_exp] at h
    simp only [mertensAtomAt]
    rw [Set.indicator_of_mem (by simp only [mem_Ici]; linarith), mul_comm]
  rw [Finset.sum_congr rfl hval, ← Finset.mul_sum]
  congr 1

/-- **Card equation `(16)`, the partial-sum half.** -/
theorem causalTransform_mobiusWeightedPartial {a : ℝ} (ha : 1 < a) {w : ℂ} (hw : 0 < w.re) :
    causalTransform (Set.indicator (Ioi (0 : ℝ)) (fun s : ℝ => mobiusWeightedPartial a s)) w
      = (1 / w) * (riemannZeta ((a : ℂ) + w))⁻¹ := by
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun (n : ℕ) (t : ℝ) => mertensAtomAt a w n t)
    (fun n => integrableOn_mertensAtomAt hw a n)
    (summable_integral_norm_mertensAtomAt hw ha)
  have hpoint : ∫ t in Ioi (0 : ℝ), (∑' n : ℕ, mertensAtomAt a w n t)
      = causalTransform (Set.indicator (Ioi (0 : ℝ))
          (fun s : ℝ => mobiusWeightedPartial a s)) w := by
    rw [causalTransform]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [tsum_mertensAtomAt (mem_Ioi.mp ht), neg_mul, Set.indicator_of_mem ht]
  rw [← hpoint, ← hswap]
  have hterm : ∀ n : ℕ, (∫ t in Ioi (0 : ℝ), mertensAtomAt a w n t)
      = LSeries.term (↗μ) ((a : ℂ) + w) n / w := by
    intro n
    rw [integral_mertensAtomAt hw a n, ← weight_mul_cexp_eq_termAt (w := w) a n]
    ring
  rw [tsum_congr hterm, tsum_div_const]
  have hre : 1 < (((a : ℂ)) + w).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  rw [show (∑' n : ℕ, LSeries.term (↗μ) ((a : ℂ) + w) n) = (riemannZeta ((a : ℂ) + w))⁻¹ from
    LSeries_moebius_eq_inv_riemannZeta hre]
  ring

/-! ## The centered prelimit transform -/

theorem causalTransform_indicator_one {z : ℂ} (hz : 0 < z.re) :
    causalTransform (Set.indicator (Ioi (0 : ℝ)) (fun _ : ℝ => (1 : ℂ))) z = 1 / z := by
  rw [causalTransform]
  have hcongr : ∫ t in Ioi (0 : ℝ),
      Complex.exp (-z * (t : ℂ)) * Set.indicator (Ioi (0 : ℝ)) (fun _ : ℝ => (1 : ℂ)) t
      = ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [Set.indicator_of_mem ht, mul_one, neg_mul]
  rw [hcongr, GaloisForLFunctions.RHTower.integral_Ioi_cexp_neg_mul_shift hz 0]
  simp

theorem norm_mobiusWeightedPartial_le {a : ℝ} (ha : 1 < a) (t : ℝ) :
    ‖mobiusWeightedPartial a t‖ ≤ ∑' n : ℕ, ((n : ℝ)) ^ (-a) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-a)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc ‖mobiusWeightedPartial a t‖
      ≤ ∑ n ∈ Finset.range (⌊Real.exp t⌋₊ + 1), ‖mobiusRealWeight a n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (⌊Real.exp t⌋₊ + 1), ((n : ℝ)) ^ (-a) :=
        Finset.sum_le_sum fun n _ => norm_mobiusRealWeight_le a n
    _ ≤ ∑' n : ℕ, ((n : ℝ)) ^ (-a) :=
        hbase.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem integrableOn_kernel_mul_bounded {z : ℂ} (hz : 0 < z.re) {f : ℝ → ℂ} {C : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (hbd : ∀ t : ℝ, ‖f t‖ ≤ C) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * f t) (Ioi (0 : ℝ)) volume := by
  have hexp : IntegrableOn (fun t : ℝ => C * Real.exp (-z.re * t)) (Ioi (0 : ℝ)) volume :=
    (exp_neg_integrableOn_Ioi 0 hz).const_mul _
  refine Integrable.mono' hexp ?_ ?_
  · exact ((Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable).mul hf
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_mul, norm_cexp_neg_mul_ofReal]
    calc Real.exp (-z.re * t) * ‖f t‖ ≤ Real.exp (-z.re * t) * C :=
          mul_le_mul_of_nonneg_left (hbd t) (Real.exp_pos _).le
      _ = C * Real.exp (-z.re * t) := by ring

/-- **Card equation `(16)`: the causal transform of the centered prelimit vector.** -/
theorem causalTransform_centeredMertensVector {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 < z.re) :
    causalTransform (centeredMertensVector ω) z
      = (1 / ((1 : ℂ) + (ω : ℂ))) *
        ((1 / z) * (riemannZeta (((1 + 2 * ω : ℝ) : ℂ) + z))⁻¹
          - (riemannZeta (((1 + 2 * ω : ℝ)) : ℂ))⁻¹ * (1 / z)) := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  set c : ℂ := 1 / ((1 : ℂ) + (ω : ℂ)) with hcdef
  set Z : ℂ := (riemannZeta (((1 + 2 * ω : ℝ)) : ℂ))⁻¹ with hZdef
  set P : ℝ → ℂ := Set.indicator (Ioi (0 : ℝ)) (fun s : ℝ => mobiusWeightedPartial (1 + 2 * ω) s)
    with hPdef
  set U : ℝ → ℂ := Set.indicator (Ioi (0 : ℝ)) (fun _ : ℝ => (1 : ℂ)) with hUdef
  have hsplit : ∀ t : ℝ, centeredMertensVector ω t = c * P t - (c * Z) * U t := by
    intro t
    rw [centeredMertensVector, hPdef, hUdef]
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Set.indicator_of_mem ht, hcdef, hZdef]
      ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      ring
  have hPmeas : AEStronglyMeasurable P (volume.restrict (Ioi (0 : ℝ))) := by
    refine (Measurable.indicator ?_ measurableSet_Ioi).aestronglyMeasurable
    exact measurable_mobiusWeightedPartial (1 + 2 * ω)
  have hPbd : ∀ t : ℝ, ‖P t‖ ≤ ∑' n : ℕ, ((n : ℝ)) ^ (-(1 + 2 * ω)) := by
    intro t
    rw [hPdef]
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem ht]
      exact norm_mobiusWeightedPartial_le ha t
    · rw [Set.indicator_of_notMem ht, norm_zero]
      exact tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hUmeas : AEStronglyMeasurable U (volume.restrict (Ioi (0 : ℝ))) := by
    refine (Measurable.indicator measurable_const measurableSet_Ioi).aestronglyMeasurable
  have hUbd : ∀ t : ℝ, ‖U t‖ ≤ 1 := by
    intro t
    rw [hUdef]
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem ht, norm_one]
    · rw [Set.indicator_of_notMem ht, norm_zero]
      norm_num
  have hPint := integrableOn_kernel_mul_bounded hz hPmeas hPbd
  have hUint := integrableOn_kernel_mul_bounded hz hUmeas hUbd
  have hexpand : causalTransform (centeredMertensVector ω) z
      = c * causalTransform P z - (c * Z) * causalTransform U z := by
    rw [causalTransform, causalTransform, causalTransform]
    have hfun : ∀ t : ℝ, Complex.exp (-z * (t : ℂ)) * centeredMertensVector ω t
        = c * (Complex.exp (-z * (t : ℂ)) * P t)
          - (c * Z) * (Complex.exp (-z * (t : ℂ)) * U t) := by
      intro t
      rw [hsplit t]
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => hfun t),
      MeasureTheory.integral_sub (hPint.const_mul c) (hUint.const_mul (c * Z)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hexpand, causalTransform_mobiusWeightedPartial ha hz, causalTransform_indicator_one hz]
  ring

/-! ## The prelimit zero-free half planes -/

/-- The weighted centered prelimit vector `e^{αt} m_ω(t)`. -/
def weightedCenteredVector (ω α : ℝ) (t : ℝ) : ℂ :=
  (Real.exp (α * t) : ℂ) * centeredMertensVector ω t

/-- The prelimit weighted domain condition. -/
def WeightedPrelimitMoment (ω α : ℝ) : Prop :=
  MemLp (weightedCenteredVector ω α) 2 (volume.restrict (Ioi (0 : ℝ)))

theorem causalTransform_weightedCenteredVector (ω α : ℝ) (z : ℂ) :
    causalTransform (weightedCenteredVector ω α) z
      = causalTransform (centeredMertensVector ω) (z - (α : ℂ)) := by
  rw [causalTransform, causalTransform]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [weightedCenteredVector, ← mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Card equation `(19)`: one prelimit weight gives one zero-free half plane.** -/
theorem zeta_ne_zero_of_weightedPrelimitMoment {ω α : ℝ} (hω : 0 < ω) (hα : 0 ≤ α)
    (h : WeightedPrelimitMoment ω α) {s : ℂ} (hs : 1 + 2 * ω - α < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hzero
  set A : ℂ := ((1 + 2 * ω : ℝ) : ℂ) with hAdef
  have hAre : A.re = 1 + 2 * ω := by rw [hAdef, Complex.ofReal_re]
  set c : ℂ := 1 / ((1 : ℂ) + (ω : ℂ)) with hcdef
  have hden : ((1 : ℂ) + (ω : ℂ)) ≠ 0 := by
    intro hc
    have := congrArg Complex.re hc
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at this
    linarith
  have hcne : c ≠ 0 := by
    rw [hcdef]
    exact one_div_ne_zero hden
  set Z : ℂ := (riemannZeta A)⁻¹ with hZdef
  set F : ℂ → ℂ := causalTransform (weightedCenteredVector ω α) with hF
  set H : ℂ → ℂ := fun z =>
    F z * ((z - (α : ℂ)) * zetaPoleUnit (A + z - (α : ℂ)))
      - c * ((((2 * ω : ℝ) : ℂ) + z - (α : ℂ))
        - zetaPoleUnit (A + z - (α : ℂ)) * Z) with hH
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hFdiff : DifferentiableOn ℂ F {z : ℂ | 0 < z.re} := differentiableOn_causalTransform h
  have hpoly : Differentiable ℂ (fun z : ℂ => zetaPoleUnit (A + z - (α : ℂ))) :=
    differentiable_zetaPoleUnit.comp (by fun_prop)
  have hHdiff : DifferentiableOn ℂ H {z : ℂ | 0 < z.re} := by
    refine (hFdiff.mul (((differentiable_id.sub_const _).mul hpoly).differentiableOn)).sub ?_
    exact (((differentiable_const _).add differentiable_id).sub_const _ |>.sub
      (hpoly.mul (differentiable_const _))).differentiableOn.const_mul c
  have hHan : AnalyticOnNhd ℂ H {z : ℂ | 0 < z.re} := hHdiff.analyticOnNhd hU
  have hV : IsOpen {z : ℂ | α < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((α : ℂ) + 1) ∈ {z : ℂ | α < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hzero_nbhd : H =ᶠ[nhds ((α : ℂ) + 1)] 0 := by
    filter_upwards [hV.mem_nhds hmem] with z hz
    have hzre : α < z.re := hz
    have hzα : z ≠ (α : ℂ) := by
      intro hc
      rw [hc] at hzre
      simp at hzre
    have hzα0 : (z - (α : ℂ)) ≠ 0 := sub_ne_zero.mpr hzα
    have hre : 0 < (z - (α : ℂ)).re := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith
    have hzeta : riemannZeta (A + (z - (α : ℂ))) ≠ 0 := by
      refine riemannZeta_ne_zero_of_one_lt_re ?_
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, hAre]
      linarith
    have hne1 : (A + (z - (α : ℂ))) ≠ 1 := by
      intro hc
      have hcre := congrArg Complex.re hc
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, hAre, Complex.one_re] at hcre
      linarith
    show F z * ((z - (α : ℂ)) * zetaPoleUnit (A + z - (α : ℂ)))
        - c * ((((2 * ω : ℝ) : ℂ) + z - (α : ℂ))
          - zetaPoleUnit (A + z - (α : ℂ)) * Z) = 0
    rw [hF, causalTransform_weightedCenteredVector,
      causalTransform_centeredMertensVector hω hre,
      show A + z - (α : ℂ) = A + (z - (α : ℂ)) by ring,
      zetaPoleUnit_of_ne hne1, ← hAdef, ← hZdef]
    have hA1 : A + (z - (α : ℂ)) - 1 = ((2 * ω : ℝ) : ℂ) + z - (α : ℂ) := by
      rw [hAdef]
      push_cast
      ring
    rw [hA1, hcdef]
    field_simp
    ring
  have hbase : ((α : ℂ) + 1) ∈ {z : ℂ | 0 < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hHzero := hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn hbase hzero_nbhd
  have hz0mem : (s - A + (α : ℂ)) ∈ {z : ℂ | 0 < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.sub_re, Complex.ofReal_re, hAre]
    linarith
  have h0 := hHzero hz0mem
  have hshift : A + (s - A + (α : ℂ)) - (α : ℂ) = s := by ring
  have hshift2 : ((2 * ω : ℝ) : ℂ) + (s - A + (α : ℂ)) - (α : ℂ) = s - 1 := by
    rw [hAdef]
    push_cast
    ring
  rw [hH] at h0
  simp only [hshift, hshift2, Pi.zero_apply] at h0
  rw [zetaPoleUnit_of_ne hs1, hzero, mul_zero] at h0
  simp only [mul_zero, zero_mul, sub_zero] at h0
  have hcs : c * (s - 1) = 0 := by linear_combination -h0
  rcases mul_eq_zero.mp hcs with hc | hs0
  · exact hcne hc
  · exact hs1 (by linear_combination hs0)

end

end RHTower
