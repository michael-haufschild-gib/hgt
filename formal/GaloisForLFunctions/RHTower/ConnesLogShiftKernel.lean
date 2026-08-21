import Mathlib

/-!
# Connes' logarithmic shift kernel of §VII (44)-(45)

Formalization of the scaling step (44)-(45) inside the proof of Lemma 2 of §VII of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Lemma VII.2 bounds the error term `δ_q(Λ)` of the `S`-local trace formula by a Besov-type norm; the
key pointwise input is that for the fractional convolution operator `C_{α,v}` one has

  `∫_{k_v} ψ(|ε|) |log|x+ε| - log|x|| dε/|ε|^{1+α} ≤ c'_α |x|^{-α}`,        (45)

with the finite constant `c'_α = ∫_{k_v} log|1+y| dy/|y|^{1+α}` of (44).

Both are proved here at the real place:

* `connes_logShift_substitution` - the exact scaling `ε = x y`, without hypotheses;
* `connes_integrable_logShiftKernel` - (44): `c'_α` is finite for `0 < α < 1`, by splitting the
  line at the three singularities `y = 0`, `y = -1`, `y = ∞`;
* `connes_logShift_bound` - (45) itself, by dropping the cut-off `0 ≤ ψ ≤ 1`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory Set Real Filter Topology

/-- Connes' §VII (44) kernel: the logarithmic difference weighted by `|y|^{-(1+α)}`. -/
def connesLogShiftKernel (α : ℝ) (y : ℝ) : ℝ :=
  abs (Real.log |1 + y|) * (|y| ^ (1 + α))⁻¹

/-- **§VII (45), the scaling identity.**  The logarithmic-difference integral at the point `x` is
`|x|^{-α}` times the same integral at `1`.  This is the exact form of Connes' inequality (45)
before dropping the cut-off `ψ`. -/
theorem connes_logShift_substitution {x : ℝ} (hx : x ≠ 0) (α : ℝ) (Ψ : ℝ → ℝ) :
    (∫ ε : ℝ, Ψ (ε / x) *
        (abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹))
      = (|x| ^ (-α)) * ∫ y : ℝ, Ψ y * connesLogShiftKernel α y := by
  have hxpos : (0:ℝ) < |x| := abs_pos.mpr hx
  set H : ℝ → ℝ := fun ε => Ψ (ε / x) *
      (abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹) with hH
  have hae : ∀ᵐ y : ℝ, y ≠ 0 ∧ 1 + y ≠ 0 := by
    have h0 : (volume : Measure ℝ) {(0:ℝ)} = 0 := Real.volume_singleton
    have h1 : (volume : Measure ℝ) {(-1:ℝ)} = 0 := Real.volume_singleton
    filter_upwards [compl_mem_ae_iff.2 h0, compl_mem_ae_iff.2 h1] with y hy0 hy1
    refine ⟨by simpa using hy0, ?_⟩
    intro hc
    exact (by simpa using hy1 : y ≠ -1) (by linarith [hc])
  have hpt : ∀ y : ℝ, y ≠ 0 → 1 + y ≠ 0 →
      H (x * y) = (|x| ^ (1 + α))⁻¹ * (Ψ y * connesLogShiftKernel α y) := by
    intro y hy0 hy1
    have hdiv : x * y / x = y := by field_simp
    have habs : |x + x * y| = |x| * |1 + y| := by
      rw [show x + x * y = x * (1 + y) by ring, abs_mul]
    have hlog : Real.log |x + x * y| - Real.log |x| = Real.log |1 + y| := by
      rw [habs, Real.log_mul (ne_of_gt hxpos) (abs_ne_zero.mpr hy1)]
      ring
    have habsxy : |x * y| = |x| * |y| := abs_mul x y
    have hpow : (|x * y| ^ (1 + α))⁻¹ = (|x| ^ (1 + α))⁻¹ * (|y| ^ (1 + α))⁻¹ := by
      rw [habsxy, Real.mul_rpow (le_of_lt hxpos) (abs_nonneg y), mul_inv]
    simp only [hH, hdiv, hlog, hpow, connesLogShiftKernel]
    ring
  have hshift : (∫ y : ℝ, H (x * y)) = |x|⁻¹ * ∫ ε : ℝ, H ε := by
    have h := Measure.integral_comp_mul_left H x
    rw [abs_inv] at h
    simpa [smul_eq_mul] using h
  have hcongr : (∫ y : ℝ, H (x * y))
      = (|x| ^ (1 + α))⁻¹ * ∫ y : ℝ, Ψ y * connesLogShiftKernel α y := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    exact hpt y hy.1 hy.2
  rw [hcongr] at hshift
  have hxne : (|x| : ℝ) ≠ 0 := ne_of_gt hxpos
  have hval : |x| ^ (-α) = |x| * (|x| ^ (1 + α))⁻¹ := by
    have h1 : (-α : ℝ) = 1 + (-(1 + α)) := by ring
    rw [h1, Real.rpow_add hxpos, Real.rpow_one, Real.rpow_neg (le_of_lt hxpos)]
  rw [hval]
  have hI : (∫ ε : ℝ, H ε)
      = |x| * ((|x| ^ (1 + α))⁻¹ * ∫ y : ℝ, Ψ y * connesLogShiftKernel α y) := by
    calc (∫ ε : ℝ, H ε) = |x| * (|x|⁻¹ * ∫ ε : ℝ, H ε) := by field_simp
      _ = |x| * ((|x| ^ (1 + α))⁻¹ * ∫ y : ℝ, Ψ y * connesLogShiftKernel α y) := by
          rw [← hshift]
  rw [hI]
  ring

/-! ### Finiteness of Connes' constant `c'_α` (§VII (44)) -/

/-- `|y| ^ r` is integrable near the origin when `-1 < r`. -/
theorem connes_integrableOn_abs_rpow_Icc {r c : ℝ} (hr : -1 < r) (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => |y| ^ r) (Icc (-c) c) := by
  have hunion : Icc (-c) c = Icc (-c) 0 ∪ Icc (0:ℝ) c := by
    rw [Set.Icc_union_Icc_eq_Icc (by linarith) (le_of_lt hc)]
  rw [hunion]
  have hpos : IntegrableOn (fun y : ℝ => |y| ^ r) (Icc (0:ℝ) c) := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (le_of_lt hc)]
    refine IntervalIntegrable.congr ?_ (intervalIntegral.intervalIntegrable_rpow' hr)
    intro y hy
    rw [Set.uIoc_of_le (le_of_lt hc)] at hy
    show y ^ r = |y| ^ r
    rw [abs_of_pos hy.1]
  have hneg : IntegrableOn (fun y : ℝ => |y| ^ r) (Icc (-c) 0) := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : (-c:ℝ) ≤ 0)]
    have hbase : IntervalIntegrable (fun y : ℝ => (-y) ^ r) volume (-c) 0 := by
      have h := (IntervalIntegrable.iff_comp_neg
        (f := fun y : ℝ => y ^ r) (a := c) (b := (0:ℝ))
        (by finiteness)).mp (intervalIntegral.intervalIntegrable_rpow' hr)
      simpa using h
    refine IntervalIntegrable.congr ?_ hbase
    intro y hy
    rw [Set.uIoc_of_le (by linarith : (-c:ℝ) ≤ 0)] at hy
    show (-y) ^ r = |y| ^ r
    rw [abs_of_nonpos hy.2]
  exact hneg.union hpos

/-- `|y| ^ r` is integrable at infinity when `r < -1`. -/
theorem connes_integrableOn_abs_rpow_tail {r c : ℝ} (hr : r < -1) (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => |y| ^ r) {y : ℝ | c < |y|} := by
  have hset : {y : ℝ | c < |y|} = Iio (-c) ∪ Ioi c := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro h
      rcases le_or_gt y 0 with hy | hy
      · left; rw [abs_of_nonpos hy] at h; linarith
      · right; rw [abs_of_pos hy] at h; exact h
    · rintro (h | h)
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
  rw [hset]
  have hpos : IntegrableOn (fun y : ℝ => |y| ^ r) (Ioi c) := by
    have hbase : IntegrableOn (fun y : ℝ => y ^ r) (Ioi c) :=
      (integrableOn_Ioi_rpow_iff hc).mpr hr
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro y hy
    show y ^ r = |y| ^ r
    rw [abs_of_pos (lt_trans hc hy)]
  have hneg : IntegrableOn (fun y : ℝ => |y| ^ r) (Iio (-c)) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (f := fun y : ℝ => |y| ^ r) (s := Iio (-c)) (measurableEmbedding_neg (α := ℝ))
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' (Iio (-c) : Set ℝ) = Ioi c := by
      ext y; simp
    rw [hpre] at h
    have hfun : ((fun y : ℝ => |y| ^ r) ∘ (Neg.neg : ℝ → ℝ)) = fun y : ℝ => |y| ^ r := by
      funext y; simp
    rw [hfun] at h
    exact h.mp hpos
  exact hneg.union hpos

/-- **§VII (44), local bound.**  `|log|1+t|| ≤ 2|t|` for `|t| ≤ 1/2`. -/
theorem connes_abs_log_one_add_le {t : ℝ} (ht : |t| ≤ 1/2) :
    abs (Real.log |1 + t|) ≤ 2 * |t| := by
  have hle : -|t| ≤ t := neg_abs_le t
  have h2 : (0:ℝ) < 1 + t := by linarith
  have habs : |1 + t| = 1 + t := abs_of_pos h2
  rw [habs]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hlow : 1 - (1 + t)⁻¹ ≤ Real.log (1 + t) := Real.one_sub_inv_le_log_of_pos h2
    have hnn : 0 ≤ |t| := abs_nonneg t
    have hpos1 : (0:ℝ) < 1 + 2 * |t| := by linarith
    have hkey : 1 ≤ (1 + t) * (1 + 2 * |t|) := by
      nlinarith [hle, hnn, ht, mul_le_mul_of_nonneg_right hle hnn]
    have hfinal : (1 + 2 * |t|)⁻¹ ≤ 1 + t := by
      have hmul : (1 + 2 * |t|)⁻¹ * 1 ≤ (1 + 2 * |t|)⁻¹ * ((1 + t) * (1 + 2 * |t|)) :=
        mul_le_mul_of_nonneg_left hkey (le_of_lt (inv_pos.mpr hpos1))
      rw [mul_one] at hmul
      calc (1 + 2 * |t|)⁻¹ ≤ (1 + 2 * |t|)⁻¹ * ((1 + t) * (1 + 2 * |t|)) := hmul
        _ = (1 + t) * ((1 + 2 * |t|)⁻¹ * (1 + 2 * |t|)) := by ring
        _ = 1 + t := by rw [inv_mul_cancel₀ (ne_of_gt hpos1), mul_one]
    have hinv : (1 + t)⁻¹ ≤ 1 + 2 * |t| := (inv_le_comm₀ h2 hpos1).mpr hfinal
    linarith
  · have hup : Real.log (1 + t) ≤ (1 + t) - 1 := Real.log_le_sub_one_of_pos h2
    have hself : t ≤ |t| := le_abs_self t
    linarith [abs_nonneg t]

/-- **§VII (44).**  Connes' constant `c'_α = ∫ log|1+y| dy/|y|^{1+α}` is finite for `0 < α < 1`
at the real place. -/
theorem connes_integrable_logShiftKernel {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Integrable (connesLogShiftKernel α) := by
  have hpowneg : ∀ y : ℝ, (|y| ^ (1 + α))⁻¹ = |y| ^ (-(1 + α)) := fun y => by
    rw [Real.rpow_neg (abs_nonneg y)]
  have hmeas : AEStronglyMeasurable (connesLogShiftKernel α) volume := by
    have h1 : Measurable fun y : ℝ => abs (Real.log |1 + y|) :=
      ((measurable_const.add measurable_id).norm.log).abs
    have h2 : Measurable fun y : ℝ => (|y| ^ (1 + α))⁻¹ :=
      (measurable_norm.pow_const (1 + α)).inv
    exact (h1.mul h2).aestronglyMeasurable
  have hcover : (Icc (-(1/2):ℝ) (1/2)) ∪ ({y : ℝ | 1/2 < |y| ∧ |y| ≤ 2} ∪ {y : ℝ | 2 < |y|})
      = Set.univ := by
    ext y
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rcases le_or_gt |y| (1/2) with h | h
    · left
      have hle := neg_abs_le y
      have hle' := le_abs_self y
      constructor <;> linarith
    · rcases le_or_gt |y| 2 with h' | h'
      · exact Or.inr (Or.inl ⟨h, h'⟩)
      · exact Or.inr (Or.inr h')
  have hA : IntegrableOn (connesLogShiftKernel α) (Icc (-(1/2):ℝ) (1/2)) := by
    have hdom : IntegrableOn (fun y : ℝ => 2 * |y| ^ (-α)) (Icc (-(1/2):ℝ) (1/2)) :=
      (connes_integrableOn_abs_rpow_Icc (by linarith : (-1:ℝ) < -α) (by norm_num)).const_mul 2
    refine Integrable.mono' hdom (hmeas.restrict) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with y hy
    have hyabs : |y| ≤ 1/2 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hlogle := connes_abs_log_one_add_le hyabs
    have hnn : (0:ℝ) ≤ (|y| ^ (1 + α))⁻¹ := by positivity
    have hval : |y| * (|y| ^ (1 + α))⁻¹ = |y| ^ (-α) := by
      rcases eq_or_lt_of_le (abs_nonneg y) with h0 | h0
      · rw [← h0, Real.zero_rpow (by linarith : (1:ℝ) + α ≠ 0),
          Real.zero_rpow (by linarith : (-α:ℝ) ≠ 0)]
        simp
      · rw [hpowneg y]
        nth_rewrite 1 [← Real.rpow_one |y|]
        rw [← Real.rpow_add h0]
        congr 1
        ring
    rw [Real.norm_eq_abs, connesLogShiftKernel, abs_of_nonneg (by positivity)]
    calc abs (Real.log |1 + y|) * (|y| ^ (1 + α))⁻¹
        ≤ (2 * |y|) * (|y| ^ (1 + α))⁻¹ := mul_le_mul_of_nonneg_right hlogle hnn
      _ = 2 * (|y| * (|y| ^ (1 + α))⁻¹) := by ring
      _ = 2 * |y| ^ (-α) := by rw [hval]
  have hB : IntegrableOn (connesLogShiftKernel α) {y : ℝ | 1/2 < |y| ∧ |y| ≤ 2} := by
    have hsub : {y : ℝ | 1/2 < |y| ∧ |y| ≤ 2} ⊆ Icc (-2:ℝ) 2 := by
      intro y hy
      exact ⟨by linarith [neg_abs_le y, hy.2], by linarith [le_abs_self y, hy.2]⟩
    have hlogInt : IntegrableOn (fun y : ℝ => abs (Real.log |1 + y|)) (Icc (-2:ℝ) 2) := by
      have h : IntervalIntegrable (fun y : ℝ => Real.log |1 + y|) volume (-2) 2 := by
        have h0 : IntervalIntegrable (fun y : ℝ => Real.log |y|) volume (-1) 3 := by
          refine IntervalIntegrable.congr ?_ intervalIntegral.intervalIntegrable_log'
          intro y _
          show Real.log y = Real.log |y|
          rw [Real.log_abs]
        have h1 := h0.comp_add_right 1
        have hb1 : (-1 : ℝ) - 1 = -2 := by norm_num
        have hb2 : (3 : ℝ) - 1 = 2 := by norm_num
        rw [hb1, hb2] at h1
        refine IntervalIntegrable.congr ?_ h1
        intro y _
        show Real.log |y + 1| = Real.log |1 + y|
        rw [add_comm]
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-2:ℝ) ≤ 2)] at h
      exact h.norm.congr (by filter_upwards with y using rfl)
    have hmeasB : MeasurableSet {y : ℝ | 1/2 < |y| ∧ |y| ≤ 2} :=
      (measurableSet_lt measurable_const measurable_norm).inter
        (measurableSet_le measurable_norm measurable_const)
    have hdom : IntegrableOn (fun y : ℝ => (2:ℝ) ^ (1 + α) * abs (Real.log |1 + y|))
        {y : ℝ | 1/2 < |y| ∧ |y| ≤ 2} :=
      ((hlogInt.mono_set hsub)).const_mul _
    refine Integrable.mono' hdom (hmeas.restrict) ?_
    filter_upwards [self_mem_ae_restrict hmeasB] with y hy
    have hy1 : (1:ℝ)/2 < |y| := hy.1
    have hlognn : (0:ℝ) ≤ abs (Real.log |1 + y|) := abs_nonneg _
    have hpow : (|y| ^ (1 + α))⁻¹ ≤ (2:ℝ) ^ (1 + α) := by
      rw [inv_le_comm₀ (by positivity) (by positivity)]
      have hh : ((2:ℝ) ^ (1 + α))⁻¹ = ((1:ℝ)/2) ^ (1 + α) := by
        rw [← Real.inv_rpow (by norm_num), one_div]
      rw [hh]
      exact Real.rpow_le_rpow (by norm_num) (le_of_lt hy1) (by linarith)
    rw [Real.norm_eq_abs, connesLogShiftKernel, abs_of_nonneg (by positivity)]
    calc abs (Real.log |1 + y|) * (|y| ^ (1 + α))⁻¹
        ≤ abs (Real.log |1 + y|) * (2:ℝ) ^ (1 + α) :=
          mul_le_mul_of_nonneg_left hpow hlognn
      _ = (2:ℝ) ^ (1 + α) * abs (Real.log |1 + y|) := by ring
  have hC : IntegrableOn (connesLogShiftKernel α) {y : ℝ | 2 < |y|} := by
    have hdom : IntegrableOn (fun y : ℝ => (2 / α * (2:ℝ) ^ (α/2)) * |y| ^ (-1 - α/2))
        {y : ℝ | 2 < |y|} :=
      (connes_integrableOn_abs_rpow_tail (by linarith : (-1:ℝ) - α/2 < -1)
        (by norm_num : (0:ℝ) < 2)).const_mul _
    refine Integrable.mono' hdom (hmeas.restrict) ?_
    filter_upwards [self_mem_ae_restrict
      (measurableSet_lt measurable_const (measurable_norm : Measurable fun y : ℝ => |y|))]
      with y hy
    have hy2 : (2:ℝ) < |y| := hy
    have hyabs : (0:ℝ) < |y| := by linarith
    have h2 : |y| - 1 ≤ |1 + y| := by
      have hb := abs_sub_abs_le_abs_sub y (-1 : ℝ)
      simp only [abs_neg, abs_one] at hb
      calc |y| - 1 ≤ |y - (-1)| := hb
        _ = |1 + y| := by rw [sub_neg_eq_add, add_comm]
    have hone : (1:ℝ) < |1 + y| := by linarith
    have hlogpos : (0:ℝ) ≤ Real.log |1 + y| := Real.log_nonneg (le_of_lt hone)
    have hle2 : |1 + y| ≤ 2 * |y| := by
      have hb := abs_add_le (1:ℝ) y
      rw [abs_one] at hb
      linarith
    have hlogbound : Real.log |1 + y| ≤ (2 / α) * ((2:ℝ) ^ (α/2) * |y| ^ (α/2)) := by
      have h1 : Real.log |1 + y| ≤ Real.log (2 * |y|) :=
        Real.log_le_log (by linarith) hle2
      have hb2 : Real.log (2 * |y|) ≤ (2 * |y|) ^ (α/2) / (α/2) :=
        Real.log_le_rpow_div (by positivity) (by linarith)
      have h3 : (2 * |y|) ^ (α/2) = (2:ℝ) ^ (α/2) * |y| ^ (α/2) :=
        Real.mul_rpow (by norm_num) (abs_nonneg y)
      rw [h3] at hb2
      have h4 : (2:ℝ) ^ (α/2) * |y| ^ (α/2) / (α/2)
          = (2 / α) * ((2:ℝ) ^ (α/2) * |y| ^ (α/2)) := by
        field_simp
      rw [h4] at hb2
      linarith
    have hpowval : |y| ^ (α/2) * (|y| ^ (1 + α))⁻¹ = |y| ^ (-1 - α/2) := by
      rw [hpowneg y, ← Real.rpow_add hyabs]
      congr 1
      ring
    have hinvnn : (0:ℝ) ≤ (|y| ^ (1 + α))⁻¹ := by positivity
    rw [Real.norm_eq_abs, connesLogShiftKernel, abs_of_nonneg (by positivity),
      abs_of_nonneg hlogpos]
    calc Real.log |1 + y| * (|y| ^ (1 + α))⁻¹
        ≤ ((2 / α) * ((2:ℝ) ^ (α/2) * |y| ^ (α/2))) * (|y| ^ (1 + α))⁻¹ :=
          mul_le_mul_of_nonneg_right hlogbound hinvnn
      _ = (2 / α * (2:ℝ) ^ (α/2)) * (|y| ^ (α/2) * (|y| ^ (1 + α))⁻¹) := by ring
      _ = (2 / α * (2:ℝ) ^ (α/2)) * |y| ^ (-1 - α/2) := by rw [hpowval]
  rw [← integrableOn_univ, ← hcover]
  exact hA.union (hB.union hC)

/-- **§VII (45).**  Connes' inequality: the cut-off logarithmic-difference integral at `x` is at
most `c'_α |x|^{-α}`. -/
theorem connes_logShift_bound {x : ℝ} (hx : x ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {Ψ : ℝ → ℝ} (hΨc : Continuous Ψ) (hΨ0 : ∀ t, 0 ≤ Ψ t) (hΨ1 : ∀ t, Ψ t ≤ 1) :
    (∫ ε : ℝ, Ψ (ε / x) *
        (abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹))
      ≤ (|x| ^ (-α)) * ∫ y : ℝ, connesLogShiftKernel α y := by
  have hK : Integrable (connesLogShiftKernel α) := connes_integrable_logShiftKernel hα0 hα1
  have hKnn : ∀ y : ℝ, 0 ≤ connesLogShiftKernel α y := by
    intro y
    rw [connesLogShiftKernel]
    positivity
  have hΨK : Integrable (fun y : ℝ => Ψ y * connesLogShiftKernel α y) := by
    refine Integrable.mono' hK (hΨc.aestronglyMeasurable.mul hK.aestronglyMeasurable) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      exact mul_nonneg (hΨ0 y) (hKnn y))]
    calc Ψ y * connesLogShiftKernel α y ≤ 1 * connesLogShiftKernel α y :=
          mul_le_mul_of_nonneg_right (hΨ1 y) (hKnn y)
      _ = connesLogShiftKernel α y := one_mul _
  have hmono : (∫ y : ℝ, Ψ y * connesLogShiftKernel α y)
      ≤ ∫ y : ℝ, connesLogShiftKernel α y := by
    refine integral_mono hΨK hK ?_
    intro y
    calc Ψ y * connesLogShiftKernel α y ≤ 1 * connesLogShiftKernel α y :=
          mul_le_mul_of_nonneg_right (hΨ1 y) (hKnn y)
      _ = connesLogShiftKernel α y := one_mul _
  rw [connes_logShift_substitution hx α Ψ]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

end

end GaloisForLFunctions.RHTower
