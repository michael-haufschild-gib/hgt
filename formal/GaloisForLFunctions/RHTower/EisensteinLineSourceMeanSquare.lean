import GaloisForLFunctions.RHTower.EisensteinLineSourceIntegrability

/-!
# The mean and the mean square of the principal-subtraction Eisenstein source

With `M = ∫_{fd} g` and `V = ∫_{fd} g²` for the source
`g = ‖E*(·, 1/2+it)‖² − 1_{y > H} ‖c(y)‖²`, `H = e²`, this module proves

* `M ≥ (5/2) ‖Λ(1+2it)‖²`: the region `1 < y ≤ H` carries at least the mean square of the
  constant term, and the other two regions contribute nonnegatively (Parseval and the zero mean of
  the nonconstant part);
* `V ≤ 128 ‖Λ‖⁴ H + 256 ‖Λ‖² P₂ (log t + 1) + 2 K(t)`, with `K(t)` an explicit combination of the
  mode-sum constants, by integrating the horizontal slice bounds against `y⁻²` with the explicit
  majorant `128‖Λ‖⁴ 1_{y ≤ H} + 256 ‖Λ‖² P₂ 1_{y ≤ t} / y + K / y³`.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SelbergMaassCellCurvature
  GaloisForLFunctions.RHTower.SelbergMaassFullCurvatureBudget
  GaloisForLFunctions.RHTower.SelbergMaassStripGap
  GaloisForLFunctions.RHTower.SelbergModularDomainSlices
  GaloisForLFunctions.RHTower.SelbergMaassTraceStokes

namespace RHTower

noncomputable section

/-! ## Fubini on products with the unit interval -/

/-- The unit interval `[-1/2, 1/2]`. -/
abbrev unitIcc : Set ℝ := Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem setIntegral_prod_unitIcc {S : Set ℝ} {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (unitIcc ×ˢ S)) :
    ∫ p in unitIcc ×ˢ S, f p = ∫ y in S, ∫ x in unitIcc, f (x, y) := by
  have hprod : Integrable f ((volume.restrict unitIcc).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hf
  have h := integral_prod_symm f hprod
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  exact h

theorem integrableOn_slice_of_prod_unitIcc {S : Set ℝ} {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (unitIcc ×ˢ S)) :
    IntegrableOn (fun y => ∫ x in unitIcc, f (x, y)) S := by
  have hprod : Integrable f ((volume.restrict unitIcc).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hf
  exact hprod.integral_prod_right

/-- The slice integral of `g / y²` in the unit interval is `(∫_{-1/2}^{1/2} g dx) / y²`. -/
theorem setIntegral_unitIcc_div (t y : ℝ) :
    ∫ x in unitIcc, eisSourceCoord t x y / y ^ 2 =
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), eisSourceCoord t x y) / y ^ 2 := by
  rw [MeasureTheory.integral_div, integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]

theorem setIntegral_unitIcc_sq_div (t y : ℝ) :
    ∫ x in unitIcc, eisSourceCoord t x y ^ 2 / y ^ 2 =
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), eisSourceCoord t x y ^ 2) / y ^ 2 := by
  rw [MeasureTheory.integral_div, integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]

/-! ## Decomposition of the full domain by height -/

theorem fullDomain_diff_le_one : fullDomain \ {p : ℝ × ℝ | p.2 ≤ 1} = unitIcc ×ˢ Ioi 1 := by
  ext p
  simp only [Set.mem_sdiff, Set.mem_setOf_eq, not_le, Set.mem_prod, Set.mem_Ioi]
  constructor
  · rintro ⟨⟨hx, _⟩, hy⟩; exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨hx, (arcHeight_le_one hx).trans hy.le⟩, hy⟩

theorem prod_Ioi_inter_le (H : ℝ) :
    unitIcc ×ˢ Ioi 1 ∩ {p : ℝ × ℝ | p.2 ≤ H} = unitIcc ×ˢ Ioc 1 H := by
  ext p
  simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_setOf_eq, mem_Ioc]
  tauto

theorem prod_Ioi_diff_le {H : ℝ} (hH : 1 ≤ H) :
    unitIcc ×ˢ Ioi 1 \ {p : ℝ × ℝ | p.2 ≤ H} = unitIcc ×ˢ Ioi H := by
  ext p
  simp only [Set.mem_sdiff, Set.mem_prod, Set.mem_Ioi, Set.mem_setOf_eq, not_le]
  constructor
  · rintro ⟨⟨hx, _⟩, hy⟩; exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩; exact ⟨⟨hx, lt_of_le_of_lt hH hy⟩, hy⟩

theorem measurableSet_le_height (H : ℝ) : MeasurableSet {p : ℝ × ℝ | p.2 ≤ H} :=
  measurableSet_le measurable_snd measurable_const

theorem arcFloor_le_one : arcFloor ≤ 1 := arcHeight_le_one ⟨by norm_num, le_rfl⟩

theorem prod_Ioi_one_subset_rectangle : unitIcc ×ˢ Ioi 1 ⊆ rectangle := by
  rintro p ⟨hx, hy⟩
  exact ⟨hx, arcFloor_le_one.trans (le_of_lt hy)⟩

/-! ## The mean of the source -/

theorem setIntegral_fullDomain_div_split {t : ℝ} (ht : 2 ≤ t) :
    ∫ p in fullDomain, eisSourceCoord t p.1 p.2 / p.2 ^ 2 =
      (∫ p in fullDomain ∩ {p : ℝ × ℝ | p.2 ≤ 1}, eisSourceCoord t p.1 p.2 / p.2 ^ 2) +
      (∫ p in unitIcc ×ˢ Ioc 1 sourceHeight, eisSourceCoord t p.1 p.2 / p.2 ^ 2) +
      ∫ p in unitIcc ×ˢ Ioi sourceHeight, eisSourceCoord t p.1 p.2 / p.2 ^ 2 := by
  have hint := integrableOn_eisSourceCoord_div_fullDomain ht
  have h1 := integral_inter_add_sdiff (measurableSet_le_height 1) hint
  rw [fullDomain_diff_le_one] at h1
  have hint2 : IntegrableOn (fun p : ℝ × ℝ => eisSourceCoord t p.1 p.2 / p.2 ^ 2)
      (unitIcc ×ˢ Ioi 1) := by
    rw [← fullDomain_diff_le_one]; exact hint.mono_set sdiff_subset
  have h2 := integral_inter_add_sdiff (measurableSet_le_height sourceHeight) hint2
  rw [prod_Ioi_inter_le, prod_Ioi_diff_le one_lt_sourceHeight.le] at h2
  linarith

theorem setIntegral_low_nonneg (t : ℝ) :
    0 ≤ ∫ p in fullDomain ∩ {p : ℝ × ℝ | p.2 ≤ 1}, eisSourceCoord t p.1 p.2 / p.2 ^ 2 := by
  refine setIntegral_nonneg (fullDomain_measurable.inter (measurableSet_le_height 1)) fun p hp => ?_
  have hyH : ¬ sourceHeight < p.2 := not_lt.mpr (hp.2.trans one_lt_sourceHeight.le)
  have hg : 0 ≤ eisSourceCoord t p.1 p.2 := by
    unfold eisSourceCoord; rw [if_neg hyH, sub_zero]; positivity
  positivity

theorem setIntegral_mid_ge {t : ℝ} (ht : 2 ≤ t) :
    (5 / 2) * ‖eisLineLambda t‖ ^ 2 ≤
      ∫ p in unitIcc ×ˢ Ioc 1 sourceHeight, eisSourceCoord t p.1 p.2 / p.2 ^ 2 := by
  have hint : IntegrableOn (fun p : ℝ × ℝ => eisSourceCoord t p.1 p.2 / p.2 ^ 2)
      (unitIcc ×ˢ Ioc 1 sourceHeight) :=
    (integrableOn_eisSourceCoord_div_rectangle ht).mono_set
      ((Set.prod_mono_right Ioc_subset_Ioi_self).trans prod_Ioi_one_subset_rectangle)
  rw [setIntegral_prod_unitIcc hint]
  have hslice := integrableOn_slice_of_prod_unitIcc hint
  have hc : IntegrableOn (fun y => ‖eisLineConst t y‖ ^ 2 / y ^ 2) (Ioc 1 sourceHeight) := by
    have hcont : ContinuousOn (fun y => ‖eisLineConst t y‖ ^ 2 / y ^ 2) (Icc 1 sourceHeight) := by
      refine ContinuousOn.div (((continuousOn_eisLineConst t).mono ?_).norm.pow 2)
        (continuousOn_id.pow 2) fun y hy => by have := hy.1; positivity
      intro y hy; exact mem_Ioi.mpr (by linarith [hy.1])
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  calc (5 / 2) * ‖eisLineLambda t‖ ^ 2
      ≤ ∫ y in (1 : ℝ)..sourceHeight, ‖eisLineConst t y‖ ^ 2 / y ^ 2 :=
        integral_normSq_eisLineConst_ge ht
    _ = ∫ y in Ioc 1 sourceHeight, ‖eisLineConst t y‖ ^ 2 / y ^ 2 :=
        integral_of_le one_lt_sourceHeight.le
    _ ≤ ∫ y in Ioc 1 sourceHeight, ∫ x in unitIcc, eisSourceCoord t x y / y ^ 2 := by
        refine setIntegral_mono_on hc hslice measurableSet_Ioc fun y hy => ?_
        have hy2 : 1 / 2 ≤ y := by linarith [hy.1]
        rw [setIntegral_unitIcc_div, intervalIntegral_eisSourceCoord_of_le t hy2 hy.2]
        have hy0 : 0 < y ^ 2 := by have := hy.1; positivity
        have h8 : 0 ≤ 8 * ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 := by positivity
        exact div_le_div_of_nonneg_right (by linarith) hy0.le

theorem setIntegral_high_nonneg {t : ℝ} (ht : 2 ≤ t) :
    0 ≤ ∫ p in unitIcc ×ˢ Ioi sourceHeight, eisSourceCoord t p.1 p.2 / p.2 ^ 2 := by
  have hint : IntegrableOn (fun p : ℝ × ℝ => eisSourceCoord t p.1 p.2 / p.2 ^ 2)
      (unitIcc ×ˢ Ioi sourceHeight) :=
    (integrableOn_eisSourceCoord_div_rectangle ht).mono_set
      ((Set.prod_mono_right (Ioi_subset_Ioi one_lt_sourceHeight.le)).trans
        prod_Ioi_one_subset_rectangle)
  rw [setIntegral_prod_unitIcc hint]
  refine setIntegral_nonneg measurableSet_Ioi fun y hy => ?_
  have hy2 : 1 / 2 ≤ y := by linarith [one_lt_sourceHeight, mem_Ioi.mp hy]
  rw [setIntegral_unitIcc_div, intervalIntegral_eisSourceCoord_of_gt t hy2 hy]
  have hy0 : 0 < y := by linarith [one_lt_sourceHeight, mem_Ioi.mp hy]
  positivity

/-- **The mean of the source:** `∫_{fd} g ≥ (5/2) ‖Λ(1+2it)‖²`. -/
theorem setIntegral_fullDomain_eisSourceCoord_div_ge {t : ℝ} (ht : 2 ≤ t) :
    (5 / 2) * ‖eisLineLambda t‖ ^ 2 ≤ ∫ p in fullDomain, eisSourceCoord t p.1 p.2 / p.2 ^ 2 := by
  rw [setIntegral_fullDomain_div_split ht]
  have h1 := setIntegral_low_nonneg (t := t)
  have h2 := setIntegral_mid_ge ht
  have h3 := setIntegral_high_nonneg ht
  linarith

/-! ## The majorant of the slice mean square -/

/-- `e^{-πy/4} ≤ 15 / y³` for `y > 0`. -/
theorem exp_neg_pi_div_four_le {y : ℝ} (hy : 0 < y) :
    Real.exp (-(Real.pi * y / 4)) ≤ 15 / y ^ 3 := by
  have hπ := Real.pi_gt_three
  have hu : 0 ≤ Real.pi * y / 4 := by positivity
  have h := Real.pow_div_factorial_le_exp (Real.pi * y / 4) hu 3
  have h3 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h3] at h
  have hy3 : 0 < y ^ 3 := by positivity
  have hE : 0 < Real.exp (Real.pi * y / 4) := Real.exp_pos _
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ hE hy3]
  have hπ3 : 27 * y ^ 3 ≤ Real.pi ^ 3 * y ^ 3 := by
    have : (3 : ℝ) ^ 3 ≤ Real.pi ^ 3 := pow_le_pow_left₀ (by norm_num) hπ.le 3
    nlinarith
  have hlow : 27 * y ^ 3 / 384 ≤ Real.exp (Real.pi * y / 4) := by
    calc 27 * y ^ 3 / 384 ≤ Real.pi ^ 3 * y ^ 3 / 384 := by gcongr
      _ = (Real.pi * y / 4) ^ 3 / 6 := by ring
      _ ≤ _ := h
  nlinarith

/-- The tail constant `K(t)`. -/
def vTailConst (t : ℝ) : ℝ :=
  1024 * (2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) * (ellTwoHead t + 60 * ellTwoTail t) +
    3840 * ‖eisLineLambda t‖ ^ 2 * ellTwoTail t

theorem vTailConst_nonneg {t : ℝ} (ht : 2 ≤ t) : 0 ≤ vTailConst t := by
  unfold vTailConst
  have := ellOneHead_nonneg ht
  have := ellOneTail_nonneg t
  have := ellTwoHead_nonneg ht
  have := ellTwoTail_nonneg t
  positivity

/-- `ℓ¹(y)² ≤ (2P₁² + 60Q₁²)/y` on `y ≥ 1/2`. -/
theorem ellOne_sq_le {t y : ℝ} (ht : 2 ≤ t) (hy : 1 / 2 ≤ y) :
    (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 ≤
      (2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) / y := by
  have h := ellOne_le ht hy
  have hy0 : 0 < y := by linarith
  have hL0 : 0 ≤ ∑' N : ℕ, eisensteinLineModeSize t y N :=
    tsum_nonneg fun N => eisensteinLineModeSize_nonneg t y N
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0.le
  set a := ellOneHead t / Real.sqrt y with ha
  set b := ellOneTail t * Real.sqrt y * Real.exp (-(Real.pi * y / 8)) with hb
  have hab : (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    have := pow_le_pow_left₀ hL0 h 2
    nlinarith [sq_nonneg (a - b)]
  have ha2 : a ^ 2 = ellOneHead t ^ 2 / y := by
    rw [ha, div_pow, hsq]
  have hE : Real.exp (-(Real.pi * y / 8)) ^ 2 = Real.exp (-(Real.pi * y / 4)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hb2 : b ^ 2 = ellOneTail t ^ 2 * (y * Real.exp (-(Real.pi * y / 4))) := by
    rw [hb]
    calc (ellOneTail t * Real.sqrt y * Real.exp (-(Real.pi * y / 8))) ^ 2
        = ellOneTail t ^ 2 * (Real.sqrt y ^ 2 * Real.exp (-(Real.pi * y / 8)) ^ 2) := by ring
      _ = _ := by rw [hsq, hE]
  have hexp := exp_neg_pi_div_four_le hy0
  have hQ := ellOneTail_nonneg t
  have hyy : y * (15 / y ^ 3) ≤ 30 / y := by
    have e : y * (15 / y ^ 3) = 15 / y ^ 2 := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) hy0]
    nlinarith
  have hb2' : b ^ 2 ≤ 30 * ellOneTail t ^ 2 / y := by
    rw [hb2]
    calc ellOneTail t ^ 2 * (y * Real.exp (-(Real.pi * y / 4)))
        ≤ ellOneTail t ^ 2 * (y * (15 / y ^ 3)) := by gcongr
      _ ≤ ellOneTail t ^ 2 * (30 / y) := by gcongr
      _ = 30 * ellOneTail t ^ 2 / y := by ring
  calc (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := hab
    _ ≤ 2 * (ellOneHead t ^ 2 / y) + 2 * (30 * ellOneTail t ^ 2 / y) := by rw [ha2]; gcongr
    _ = _ := by ring

/-- `ℓ²(y) ≤ P₂ + 60 Q₂` on `y ≥ 1/2`. -/
theorem ellTwo_le_const {t y : ℝ} (ht : 2 ≤ t) (hy : 1 / 2 ≤ y) :
    ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 ≤ ellTwoHead t + 60 * ellTwoTail t := by
  have h := ellTwo_le ht hy
  have hy0 : 0 < y := by linarith
  have hexp := exp_neg_pi_div_four_le hy0
  have hQ := ellTwoTail_nonneg t
  have hyy : y * (15 / y ^ 3) ≤ 60 := by
    have e : y * (15 / y ^ 3) = 15 / y ^ 2 := by field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  calc ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2
      ≤ ellTwoHead t + ellTwoTail t * y * Real.exp (-(Real.pi * y / 4)) := h
    _ ≤ ellTwoHead t + ellTwoTail t * (y * (15 / y ^ 3)) := by rw [mul_assoc]; gcongr
    _ ≤ ellTwoHead t + ellTwoTail t * 60 := by gcongr
    _ = _ := by ring

/-- The majorant of the horizontal slice mean square divided by `y²`. -/
def vMajorant (t y : ℝ) : ℝ :=
  (Icc arcFloor sourceHeight).indicator (fun _ => 128 * ‖eisLineLambda t‖ ^ 4) y +
    (Icc arcFloor t).indicator (fun y => 256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t / y) y +
    vTailConst t / y ^ 3

/-- The slice mean square divided by `y²` is at most the majorant, for `y ≥ √3/2`. -/
theorem slice_sq_div_le_vMajorant {t y : ℝ} (ht : 2 ≤ t) (hy : arcFloor ≤ y) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2), eisSourceCoord t x y ^ 2) / y ^ 2 ≤ vMajorant t y := by
  have hy2 : 1 / 2 ≤ y := arcFloor_gt_half.le.trans hy
  have hy0 : 0 < y := by linarith
  have ht0 : t ≠ 0 := by positivity
  have hc := norm_eisLineConst_le ht0 hy0
  have hb := norm_nonneg (eisLineLambda t)
  have hc0 := norm_nonneg (eisLineConst t y)
  have hL1 := ellOne_sq_le ht hy2
  have hL2 := ellTwo_le_const ht hy2
  have hL2nn : 0 ≤ ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 := by positivity
  have hL1nn : 0 ≤ (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 := by positivity
  have hP2 := ellTwoHead_nonneg ht
  have hQ2 := ellTwoTail_nonneg t
  have hA : 0 ≤ 2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2 := by positivity
  have hB : 0 ≤ ellTwoHead t + 60 * ellTwoTail t := by positivity
  -- the product of the two mode sums
  have hprod : (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 *
      ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 ≤
      (2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) * (ellTwoHead t + 60 * ellTwoTail t) / y := by
    calc (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 * ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2
        ≤ ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) / y) * (ellTwoHead t + 60 * ellTwoTail t) :=
          mul_le_mul hL1 hL2 hL2nn (by positivity)
      _ = _ := by ring
  have hK : 0 ≤ vTailConst t := vTailConst_nonneg ht
  have hind2 : 0 ≤ (Icc arcFloor t).indicator
      (fun y => 256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t / y) y :=
    Set.indicator_nonneg (fun y hy => by
      have hy0' : 0 < y := arcFloor_pos.trans_le hy.1
      positivity) y
  have hy3 : 0 < y ^ 3 := by positivity
  have hyy : 0 < y ^ 2 := by positivity
  unfold vMajorant
  rcases le_or_gt y sourceHeight with hyH | hyH
  · -- below the subtraction height
    rw [Set.indicator_of_mem (show y ∈ Icc arcFloor sourceHeight from ⟨hy, hyH⟩)]
    have hslice := intervalIntegral_eisSourceCoord_sq_le_of_le t hy2 hyH
    have hc4 : ‖eisLineConst t y‖ ^ 4 ≤ 16 * ‖eisLineLambda t‖ ^ 4 * y ^ 2 := by
      have h := pow_le_pow_left₀ hc0 hc 4
      have hsq : Real.sqrt y ^ 4 = y ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hy0.le]
      calc ‖eisLineConst t y‖ ^ 4 ≤ (2 * ‖eisLineLambda t‖ * Real.sqrt y) ^ 4 := h
        _ = 16 * ‖eisLineLambda t‖ ^ 4 * Real.sqrt y ^ 4 := by ring
        _ = _ := by rw [hsq]
    have hmain : (∫ x in (-(1 / 2 : ℝ))..(1 / 2), eisSourceCoord t x y ^ 2) ≤
        128 * ‖eisLineLambda t‖ ^ 4 * y ^ 2 + 1024 *
          ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) * (ellTwoHead t + 60 * ellTwoTail t) / y) := by
      calc _ ≤ 8 * ‖eisLineConst t y‖ ^ 4 + 1024 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 *
            ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 := hslice
        _ ≤ 8 * (16 * ‖eisLineLambda t‖ ^ 4 * y ^ 2) + 1024 *
            ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) * (ellTwoHead t + 60 * ellTwoTail t) / y) := by
            rw [mul_assoc 1024]; gcongr
        _ = _ := by ring
    have hdiv : (128 * ‖eisLineLambda t‖ ^ 4 * y ^ 2 + 1024 *
        ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) * (ellTwoHead t + 60 * ellTwoTail t) / y)) / y ^ 2 =
        128 * ‖eisLineLambda t‖ ^ 4 + 1024 * ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) *
          (ellTwoHead t + 60 * ellTwoTail t)) / y ^ 3 := by
      field_simp
    have hK' : 1024 * ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) *
        (ellTwoHead t + 60 * ellTwoTail t)) / y ^ 3 ≤ vTailConst t / y ^ 3 := by
      unfold vTailConst
      refine div_le_div_of_nonneg_right ?_ hy3.le
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3840) (sq_nonneg ‖eisLineLambda t‖)) hQ2]
    calc (∫ x in (-(1 / 2 : ℝ))..(1 / 2), eisSourceCoord t x y ^ 2) / y ^ 2
        ≤ (128 * ‖eisLineLambda t‖ ^ 4 * y ^ 2 + 1024 *
            ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) * (ellTwoHead t + 60 * ellTwoTail t) / y)) /
            y ^ 2 := div_le_div_of_nonneg_right hmain hyy.le
      _ = _ := hdiv
      _ ≤ 128 * ‖eisLineLambda t‖ ^ 4 + vTailConst t / y ^ 3 := by linarith
      _ ≤ _ := by linarith
  · -- above the subtraction height
    rw [Set.indicator_of_notMem (show y ∉ Icc arcFloor sourceHeight from fun h => absurd h.2 (not_le.mpr hyH))]
    have hslice := intervalIntegral_eisSourceCoord_sq_le_of_gt t hy2 hyH
    have hc2 : ‖eisLineConst t y‖ ^ 2 ≤ 4 * ‖eisLineLambda t‖ ^ 2 * y := by
      have h := pow_le_pow_left₀ hc0 hc 2
      calc ‖eisLineConst t y‖ ^ 2 ≤ (2 * ‖eisLineLambda t‖ * Real.sqrt y) ^ 2 := h
        _ = 4 * ‖eisLineLambda t‖ ^ 2 * Real.sqrt y ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hy0.le]
    -- the `ℓ²` sum with the head present only up to height `t/π`
    have hexp := exp_neg_pi_div_four_le hy0
    have hL2' : ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 ≤
        ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y + 15 * ellTwoTail t / y ^ 2 := by
      have htail : ellTwoTail t * y * Real.exp (-(Real.pi * y / 4)) ≤ 15 * ellTwoTail t / y ^ 2 := by
        calc ellTwoTail t * y * Real.exp (-(Real.pi * y / 4))
            ≤ ellTwoTail t * y * (15 / y ^ 3) := by gcongr
          _ = 15 * ellTwoTail t / y ^ 2 := by field_simp
      rcases le_or_gt y (t / Real.pi) with hyt | hyt
      · have hyt' : y ≤ t := by
          have hπ := Real.pi_gt_three
          calc y ≤ t / Real.pi := hyt
            _ ≤ t := div_le_self (by linarith) (by linarith)
        rw [Set.indicator_of_mem (show y ∈ Icc arcFloor t from ⟨hy, hyt'⟩), mul_one]
        have := ellTwo_le ht hy2
        linarith
      · have := ellTwo_le_of_gt hy2 hyt
        have hind : 0 ≤ ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y :=
          mul_nonneg hP2 (Set.indicator_nonneg (fun _ _ => zero_le_one) y)
        linarith
    have hmain : (∫ x in (-(1 / 2 : ℝ))..(1 / 2), eisSourceCoord t x y ^ 2) ≤
        64 * (4 * ‖eisLineLambda t‖ ^ 2 * y) *
          (ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y + 15 * ellTwoTail t / y ^ 2) +
        256 * ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) * (ellTwoHead t + 60 * ellTwoTail t) / y) := by
      calc _ ≤ 64 * ‖eisLineConst t y‖ ^ 2 * (∑' N : ℕ, eisensteinLineModeSize t y N ^ 2) +
            256 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 *
              ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 := hslice
        _ ≤ 64 * (4 * ‖eisLineLambda t‖ ^ 2 * y) *
            (ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y + 15 * ellTwoTail t / y ^ 2) +
            256 * ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) *
              (ellTwoHead t + 60 * ellTwoTail t) / y) := by
            rw [mul_assoc 256]
            gcongr
    have hind1 : (Icc arcFloor t).indicator (fun y => 256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t / y) y =
        256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y / y := by
      by_cases hmem : y ∈ Icc arcFloor t
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]; ring
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]; ring
    rw [hind1]
    have hdiv : (64 * (4 * ‖eisLineLambda t‖ ^ 2 * y) *
        (ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y + 15 * ellTwoTail t / y ^ 2) +
        256 * ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) * (ellTwoHead t + 60 * ellTwoTail t) / y)) / y ^ 2 =
        256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y / y +
        (3840 * ‖eisLineLambda t‖ ^ 2 * ellTwoTail t + 256 * ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) *
          (ellTwoHead t + 60 * ellTwoTail t))) / y ^ 3 := by
      field_simp
      ring
    have hK' : (3840 * ‖eisLineLambda t‖ ^ 2 * ellTwoTail t + 256 * ((2 * ellOneHead t ^ 2 +
        60 * ellOneTail t ^ 2) * (ellTwoHead t + 60 * ellTwoTail t))) / y ^ 3 ≤ vTailConst t / y ^ 3 := by
      unfold vTailConst
      refine div_le_div_of_nonneg_right ?_ hy3.le
      nlinarith [mul_nonneg hA hB]
    calc (∫ x in (-(1 / 2 : ℝ))..(1 / 2), eisSourceCoord t x y ^ 2) / y ^ 2
        ≤ _ := div_le_div_of_nonneg_right hmain hyy.le
      _ = _ := hdiv
      _ ≤ 256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y / y +
          vTailConst t / y ^ 3 := by linarith
      _ = 0 + 256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y / y +
          vTailConst t / y ^ 3 := by ring

/-! ## Integrating the majorant -/

theorem integrableOn_inv_cube_Ici {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => 1 / y ^ 3) (Ici a) := by
  have h := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) ha
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : 0 < y := ha.trans hy
  show y ^ (-3 : ℝ) = 1 / y ^ 3
  rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hy0.le, Real.rpow_natCast,
    one_div]

theorem setIntegral_inv_cube_Ici {a : ℝ} (ha : 0 < a) :
    ∫ y in Ici a, 1 / y ^ 3 = a ^ (-2 : ℝ) / 2 := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) ha
  have hcongr : ∫ y in Ioi a, 1 / y ^ 3 = ∫ y in Ioi a, y ^ (-3 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : 0 < y := ha.trans hy
    rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hy0.le, Real.rpow_natCast,
      one_div]
  rw [hcongr, h]
  norm_num

theorem integrableOn_vMajorant (t : ℝ) : IntegrableOn (vMajorant t) (Ici arcFloor) := by
  have ha := arcFloor_pos
  have h1 : Integrable ((Icc arcFloor sourceHeight).indicator
      (fun _ : ℝ => 128 * ‖eisLineLambda t‖ ^ 4)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have h2 : Integrable ((Icc arcFloor t).indicator
      (fun y : ℝ => 256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t / y)) := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_const.div continuousOn_id fun y hy =>
      (arcFloor_pos.trans_le hy.1).ne'
  have h3 : IntegrableOn (fun y : ℝ => vTailConst t / y ^ 3) (Ici arcFloor) := by
    have := (integrableOn_inv_cube_Ici ha).const_mul (vTailConst t)
    refine IntegrableOn.congr_fun this (fun y _ => ?_) measurableSet_Ici
    simp [div_eq_mul_inv]
  exact (h1.integrableOn.add h2.integrableOn).add h3

/-- The integral of the majorant: `128‖Λ‖⁴(H − a) + 256‖Λ‖² P₂ log(t/a) + K a⁻²/2`. -/
theorem setIntegral_vMajorant_eq {t : ℝ} (ht : 2 ≤ t) :
    ∫ y in Ici arcFloor, vMajorant t y =
      128 * ‖eisLineLambda t‖ ^ 4 * (sourceHeight - arcFloor) +
        256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t * Real.log (t / arcFloor) +
        vTailConst t * (arcFloor ^ (-2 : ℝ) / 2) := by
  have ha := arcFloor_pos
  have haH : arcFloor ≤ sourceHeight := arcFloor_le_one.trans one_lt_sourceHeight.le
  have hat : arcFloor ≤ t := arcFloor_le_one.trans (by linarith)
  have h1 : Integrable ((Icc arcFloor sourceHeight).indicator
      (fun _ : ℝ => 128 * ‖eisLineLambda t‖ ^ 4)) (volume.restrict (Ici arcFloor)) :=
    ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc).integrableOn
  have h2 : Integrable ((Icc arcFloor t).indicator
      (fun y : ℝ => 256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t / y)) (volume.restrict (Ici arcFloor)) := by
    refine (IntegrableOn.integrable_indicator ?_ measurableSet_Icc).integrableOn
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_const.div continuousOn_id fun y hy =>
      (arcFloor_pos.trans_le hy.1).ne'
  have h3 : IntegrableOn (fun y : ℝ => vTailConst t / y ^ 3) (Ici arcFloor) := by
    have := (integrableOn_inv_cube_Ici ha).const_mul (vTailConst t)
    refine IntegrableOn.congr_fun this (fun y _ => ?_) measurableSet_Ici
    simp [div_eq_mul_inv]
  unfold vMajorant
  have h12 : Integrable (fun y : ℝ => (Icc arcFloor sourceHeight).indicator
      (fun _ : ℝ => 128 * ‖eisLineLambda t‖ ^ 4) y + (Icc arcFloor t).indicator
      (fun y : ℝ => 256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t / y) y)
      (volume.restrict (Ici arcFloor)) := h1.add h2
  rw [integral_add h12 h3, integral_add h1 h2]
  -- first piece
  have e1 : ∫ y in Ici arcFloor, (Icc arcFloor sourceHeight).indicator
      (fun _ : ℝ => 128 * ‖eisLineLambda t‖ ^ 4) y =
      128 * ‖eisLineLambda t‖ ^ 4 * (sourceHeight - arcFloor) := by
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_restrict_apply measurableSet_Icc,
      Set.inter_eq_self_of_subset_left Set.Icc_subset_Ici_self, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  -- second piece
  have e2 : ∫ y in Ici arcFloor, (Icc arcFloor t).indicator
      (fun y : ℝ => 256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t / y) y =
      256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t * Real.log (t / arcFloor) := by
    rw [MeasureTheory.integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_self_of_subset_left Set.Icc_subset_Ici_self, integral_Icc_eq_integral_Ioc,
      ← integral_of_le hat]
    have : (fun y : ℝ => 256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t / y) =
        fun y : ℝ => 256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t * (1 / y) := by
      funext y; ring
    rw [this, intervalIntegral.integral_const_mul, integral_one_div_of_pos ha (by linarith)]
  -- third piece
  have e3 : ∫ y in Ici arcFloor, vTailConst t / y ^ 3 = vTailConst t * (arcFloor ^ (-2 : ℝ) / 2) := by
    have : (fun y : ℝ => vTailConst t / y ^ 3) = fun y : ℝ => vTailConst t * (1 / y ^ 3) := by
      funext y; ring
    rw [this, MeasureTheory.integral_const_mul, setIntegral_inv_cube_Ici ha]
  rw [e1, e2, e3]

theorem log_div_arcFloor_le {t : ℝ} (ht : 2 ≤ t) : Real.log (t / arcFloor) ≤ Real.log t + 1 := by
  have ha := arcFloor_pos
  have hhalf := arcFloor_gt_half
  rw [Real.log_div (by linarith) ha.ne']
  have h1 : Real.log (1 / 2) ≤ Real.log arcFloor := Real.log_le_log (by norm_num) hhalf.le
  have h2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have h3 := Real.log_two_lt_d9
  linarith

theorem arcFloor_rpow_neg_two_le : arcFloor ^ (-2 : ℝ) / 2 ≤ 2 := by
  have ha := arcFloor_pos
  have hhalf := arcFloor_gt_half
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le, Real.rpow_natCast]
  have h4 : (1 / 4 : ℝ) ≤ arcFloor ^ 2 := by nlinarith
  have : (arcFloor ^ 2)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  linarith

/-- `∫ vMajorant ≤ 128‖Λ‖⁴ H + 256‖Λ‖² P₂ (log t + 1) + 2 K`. -/
theorem setIntegral_vMajorant_le {t : ℝ} (ht : 2 ≤ t) :
    ∫ y in Ici arcFloor, vMajorant t y ≤
      128 * ‖eisLineLambda t‖ ^ 4 * sourceHeight +
        256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t * (Real.log t + 1) + 2 * vTailConst t := by
  rw [setIntegral_vMajorant_eq ht]
  have ha := arcFloor_pos
  have hK := vTailConst_nonneg ht
  have hP := ellTwoHead_nonneg ht
  have hb2 : 0 ≤ ‖eisLineLambda t‖ ^ 2 := by positivity
  have hb4 : 0 ≤ ‖eisLineLambda t‖ ^ 4 := by positivity
  have hlog := log_div_arcFloor_le ht
  have hpow := arcFloor_rpow_neg_two_le
  have hH : sourceHeight - arcFloor ≤ sourceHeight := by linarith
  have h1 : 128 * ‖eisLineLambda t‖ ^ 4 * (sourceHeight - arcFloor) ≤
      128 * ‖eisLineLambda t‖ ^ 4 * sourceHeight := by gcongr
  have h2 : 256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t * Real.log (t / arcFloor) ≤
      256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t * (Real.log t + 1) := by gcongr
  have h3 : vTailConst t * (arcFloor ^ (-2 : ℝ) / 2) ≤ vTailConst t * 2 := by gcongr
  linarith

/-- **The mean square of the source:**
`∫_{fd} g² ≤ 128‖Λ‖⁴ H + 256‖Λ‖² P₂ (log t + 1) + 2 K(t)`. -/
theorem setIntegral_fullDomain_eisSourceCoord_sq_div_le {t : ℝ} (ht : 2 ≤ t) :
    ∫ p in fullDomain, eisSourceCoord t p.1 p.2 ^ 2 / p.2 ^ 2 ≤
      128 * ‖eisLineLambda t‖ ^ 4 * sourceHeight +
        256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t * (Real.log t + 1) + 2 * vTailConst t := by
  have hint := integrableOn_eisSourceCoord_sq_div_rectangle ht
  have hrect : rectangle = unitIcc ×ˢ Ici arcFloor := rfl
  calc ∫ p in fullDomain, eisSourceCoord t p.1 p.2 ^ 2 / p.2 ^ 2
      ≤ ∫ p in rectangle, eisSourceCoord t p.1 p.2 ^ 2 / p.2 ^ 2 := by
        refine setIntegral_mono_set hint ?_ (LE.le.eventuallyLE fullDomain_subset_rectangle)
        exact Filter.Eventually.of_forall fun p => by positivity
    _ = ∫ y in Ici arcFloor, ∫ x in unitIcc, eisSourceCoord t x y ^ 2 / y ^ 2 := by
        rw [hrect] at hint ⊢
        exact setIntegral_prod_unitIcc hint
    _ ≤ ∫ y in Ici arcFloor, vMajorant t y := by
        rw [hrect] at hint
        refine setIntegral_mono_on (integrableOn_slice_of_prod_unitIcc hint)
          (integrableOn_vMajorant t) measurableSet_Ici fun y hy => ?_
        rw [setIntegral_unitIcc_sq_div]
        exact slice_sq_div_le_vMajorant ht hy
    _ ≤ _ := setIntegral_vMajorant_le ht

end

end RHTower
