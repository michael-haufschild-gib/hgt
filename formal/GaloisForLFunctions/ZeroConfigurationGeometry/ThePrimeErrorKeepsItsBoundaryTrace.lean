import GaloisForLFunctions.ZeroConfigurationGeometry.TheRightSubstripsHaveSummableReciprocalZeros
import GaloisForLFunctions.ZeroConfigurationGeometry.TheOneOffsAreFiniteOscillationsOfThePrimeError
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.HTGeometry.BohrExponentialSeriesCoefficient

/-!
# Removing smoothing above the critical line

A right-substrip tail costs its summable reciprocal mass. The remaining
zeros admit the interpolated short-window bound. Together these estimates
retain the boundary trace without requiring an isolated top layer.
-/

open Complex MeasureTheory Filter Topology Set
open _root_.RHTower

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- Reciprocal mass outside a finite set in a closed right substrip. -/
def rightSubstripTailWeight (σ : ℝ) (F : Finset XiZeroCopy) (q : XiZeroCopy) : ℝ :=
  if σ ≤ (q.1 : ℂ).re ∧ q ∉ F then ‖(q.1 : ℂ)‖⁻¹ else 0

theorem rightSubstripTailWeight_nonneg (σ : ℝ) (F : Finset XiZeroCopy) (q : XiZeroCopy) :
    0 ≤ rightSubstripTailWeight σ F q := by
  unfold rightSubstripTailWeight
  split_ifs <;> positivity

theorem summable_rightSubstripTailWeight {σ : ℝ} (hσ : 1 / 2 < σ)
    (F : Finset XiZeroCopy) : Summable (rightSubstripTailWeight σ F) := by
  classical
  have hs : Summable ({q : XiZeroCopy | σ ≤ (q.1 : ℂ).re}.indicator
      (fun q => ‖(q.1 : ℂ)‖⁻¹)) :=
    summable_subtype_iff_indicator.mp (summable_rightSubstrip_norm_inv hσ)
  refine hs.of_nonneg_of_le (rightSubstripTailWeight_nonneg σ F) fun q => ?_
  by_cases hq : σ ≤ (q.1 : ℂ).re
  · rw [Set.indicator_of_mem (show q ∈ {q : XiZeroCopy | σ ≤ (q.1 : ℂ).re} from hq)]
    unfold rightSubstripTailWeight
    split_ifs
    · exact le_rfl
    · positivity
  · rw [Set.indicator_of_notMem (show q ∉ {q : XiZeroCopy | σ ≤ (q.1 : ℂ).re} from hq)]
    simp only [rightSubstripTailWeight, hq, false_and, if_false, le_refl]

private theorem norm_lagWindowZeroTerm_le_reciprocal {β x a b : ℝ}
    (hx : 1 ≤ x) (ha : 0 < a) (hab : a < b) (hb : b ≤ 2 * x)
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≤ β) :
    ‖lagWindowZeroTerm (q.1 : ℂ) a b‖ ≤ 2 * x ^ β * ‖(q.1 : ℂ)‖⁻¹ := by
  have hq0 := xiZeroCopy_re_pos q
  have hq1 := xiZeroCopy_re_lt_one q
  have hn : 0 < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr (xiZeroCopy_ne_zero q)
  have hmean := norm_mul_lagWindowZeroTerm_le ha hab hq0 hq1
  rw [norm_mul] at hmean
  have hp : b ^ (q.1 : ℂ).re ≤ 2 * x ^ β := by
    calc
      _ ≤ (2 * x) ^ (q.1 : ℂ).re :=
        Real.rpow_le_rpow (ha.trans hab).le hb hq0.le
      _ = (2 : ℝ) ^ (q.1 : ℂ).re * x ^ (q.1 : ℂ).re :=
        Real.mul_rpow (by norm_num) (zero_le_one.trans hx)
      _ ≤ 2 * x ^ β := by
        apply mul_le_mul
        · simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hq1.le
        · exact Real.rpow_le_rpow_of_exponent_le hx hq
        · positivity
        · norm_num
  rw [← div_eq_mul_inv, le_div_iff₀ hn]
  simpa only [mul_comm] using hmean.trans hp

/-- A finite zero sum approximates either adjacent short window. Unretained
right zeros cost only their reciprocal tail mass. -/
theorem norm_tsum_window_add_finiteSum_le {F : Finset XiZeroCopy}
    {σ β θ x H a b : ℝ} (hσ : 1 / 2 < σ)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hx : 1 ≤ x) (hH : 0 < H) (hxa : x / 2 ≤ a) (ha : 1 ≤ a) (hax : a ≤ x)
    (hxa' : x - a ≤ H) (hab : b - a = H) (hb : b ≤ 2 * x) :
    ‖(∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a b)
        + ∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)‖ ≤
      F.card * (2 * H) + 2 * x ^ β * (∑' q, rightSubstripTailWeight σ F q) +
        16 * x ^ σ * (x / H) ^ θ * ∑' q, zeroWeight θ q := by
  classical
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hablt : a < b := by linarith only [hab, hH]
  have hsT := Summable.of_norm (summable_norm_lagWindowZeroTerm ha hablt)
  let K := 16 * x ^ σ * (x / H) ^ θ
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  let g := fun q : XiZeroCopy => if q ∈ F then (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) else 0
  have hgs : Summable g := summable_of_ne_finset_zero (s := F) fun q hq => by simp [g, hq]
  have hgt : ∑' q, g q = ∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) := by
    rw [tsum_eq_sum (s := F) fun q hq => by simp [g, hq]]
    exact Finset.sum_congr rfl fun q hq => by simp [g, hq]
  let e := fun q : XiZeroCopy => (if q ∈ F then 2 * H else 0) +
    2 * x ^ β * rightSubstripTailWeight σ F q + K * zeroWeight θ q
  have hsF : Summable (fun q : XiZeroCopy => if q ∈ F then 2 * H else (0 : ℝ)) :=
    summable_of_ne_finset_zero (s := F) fun q hq => by simp [hq]
  have hsR := (summable_rightSubstripTailWeight hσ F).mul_left (2 * x ^ β)
  have hsW := (summable_zeroWeight hθ0).mul_left K
  have hes : Summable e := (hsF.add hsR).add hsW
  have het : ∑' q, e q = F.card * (2 * H) +
      2 * x ^ β * (∑' q, rightSubstripTailWeight σ F q) + K * ∑' q, zeroWeight θ q := by
    rw [(hsF.add hsR).tsum_add hsW, hsF.tsum_add hsR, tsum_mul_left, tsum_mul_left,
      tsum_eq_sum (s := F) fun q hq => by simp [hq]]
    congr 2
    rw [Finset.sum_congr rfl fun q hq => if_pos hq, Finset.sum_const, nsmul_eq_mul]
  have hbd (q : XiZeroCopy) : ‖lagWindowZeroTerm (q.1 : ℂ) a b + g q‖ ≤ e q := by
    have hq0 := xiZeroCopy_re_pos q
    have hq1 := xiZeroCopy_re_lt_one q
    have hR : 0 ≤ 2 * x ^ β * rightSubstripTailWeight σ F q :=
      mul_nonneg (by positivity) (rightSubstripTailWeight_nonneg σ F q)
    have hW : 0 ≤ K * zeroWeight θ q := mul_nonneg hK0 (zeroWeight_nonneg θ q)
    by_cases hq : q ∈ F
    · simp only [g, e, hq, if_true]
      have hh := norm_lagWindowZeroTerm_add_cpow_div_le ha hax hxa' hab hH hq0 hq1
      linarith only [hh, hR, hW]
    · by_cases hr : σ ≤ (q.1 : ℂ).re
      · simp only [g, e, hq, if_false, add_zero, zero_add,
          rightSubstripTailWeight, hr, not_false_eq_true, and_self, if_true]
        exact (norm_lagWindowZeroTerm_le_reciprocal hx (zero_lt_one.trans_le ha)
          hablt hb q (hβ q)).trans (le_add_of_nonneg_right hW)
      · simp only [g, e, hq, if_false, add_zero, zero_add,
          rightSubstripTailWeight, hr, false_and, mul_zero]
        exact norm_lagWindowZeroTerm_le_interpolated hx hH hxa hab hb hθ0.le hθ1
          hq0 hq1 (le_of_not_ge hr)
  have hsum : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a b)
      + ∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) =
      ∑' q, (lagWindowZeroTerm (q.1 : ℂ) a b + g q) := by
    rw [hsT.tsum_add hgs, hgt]
  have hsn := hes.of_nonneg_of_le (fun _ => norm_nonneg _) hbd
  rw [hsum, ← het]
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hbd hes)

/-- The raw prime error is squeezed by the finite zero sum, the reciprocal
right-substrip tail and the lower-strip window error. -/
theorem abs_psi_sub_add_re_finiteSum_le {F : Finset XiZeroCopy} {σ β θ x H : ℝ}
    (hσ : 1 / 2 < σ) (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hx : 4 ≤ x) (hH1 : 1 ≤ H) (hHx : H ≤ x / 2) :
    |Chebyshev.psi x - x + (∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re|
      ≤ H + 1 + Real.log (2 * Real.pi) + F.card * (2 * H)
        + 2 * x ^ β * (∑' q, rightSubstripTailWeight σ F q) + 16 * x ^ σ * (x / H) ^ θ * ∑' q, zeroWeight θ q := by
  have hH : 0 < H := by linarith
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  set Err : ℝ := F.card * (2 * H) +
    2 * x ^ β * (∑' q, rightSubstripTailWeight σ F q) + 16 * x ^ σ * (x / H) ^ θ * ∑' q, zeroWeight θ q with hErr
  set Tp : ℂ := ∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) with hTp
  -- the right window `[x, x + H]`
  have hU := norm_tsum_window_add_finiteSum_le (F := F) (x := x) (H := H) (a := x) (b := x + H) hσ hβ hθ0 hθ1
    (by linarith) hH (by linarith) (by linarith) le_rfl (by linarith) (by ring) (by linarith)
  have hwU : 0 < 1 / x - 1 / (x + H) := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt hx0 (by linarith)
  have hψU : Chebyshev.psi x ≤ chebyshevLagWindow x (x + H) / (1 / x - 1 / (x + H)) := by
    rw [le_div_iff₀ hwU]
    exact (chebyshevLagWindow_bounds hx0 (by linarith)).1
  rw [chebyshevLagWindow_div_eq (by linarith) (by linarith)] at hψU
  have hLU : Real.log ((x + H) / x) / (1 / x - 1 / (x + H)) ≤ x + H := by
    rw [div_le_iff₀ hwU]
    exact (log_div_le_mul_inv_sub hx0 (by linarith)).2
  have hEU := trivialWindowTerm_le (show 2 ≤ x by linarith) hH (by linarith)
  have hE1 : 4 / (x * H) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hReU : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) x (x + H)).re + Tp.re ≤ Err := by
    rw [← Complex.add_re]
    exact (Complex.re_le_norm _).trans hU
  -- the left window `[x − H, x]`
  have hL := norm_tsum_window_add_finiteSum_le (F := F) (x := x) (H := H) (a := x - H) (b := x) hσ hβ hθ0 hθ1
    (by linarith) hH (by linarith) (by linarith) (by linarith) (by linarith) (by ring) (by linarith)
  have ha0 : 0 < x - H := by linarith
  have hwL : 0 < 1 / (x - H) - 1 / x := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha0 (by linarith)
  have hψL : chebyshevLagWindow (x - H) x / (1 / (x - H) - 1 / x) ≤ Chebyshev.psi x := by
    rw [div_le_iff₀ hwL]
    exact (chebyshevLagWindow_bounds ha0 (by linarith)).2
  rw [chebyshevLagWindow_div_eq (by linarith) (by linarith)] at hψL
  have hLL : x - H ≤ Real.log (x / (x - H)) / (1 / (x - H) - 1 / x) := by
    rw [le_div_iff₀ hwL]
    exact (log_div_le_mul_inv_sub ha0 (by linarith)).1
  have hEL : 0 ≤ (trivialZeroSeriesReal (x - H) / (x - H) - trivialZeroSeriesReal x / x)
      / (1 / (x - H) - 1 / x) :=
    div_nonneg (sub_nonneg.mpr (trivialZeroSeriesReal_div_anti (by linarith) (by linarith))) hwL.le
  have hReL : -Err ≤ (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) (x - H) x).re + Tp.re := by
    rw [← Complex.add_re]
    have h := Complex.abs_re_le_norm
      ((∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) (x - H) x) + Tp)
    have h' := neg_le_of_abs_le (h.trans hL)
    exact h'
  have hcard : 0 ≤ Err := by
    rw [hErr]
    have := summable_zeroWeight hθ0
    have hW : 0 ≤ ∑' q, zeroWeight θ q := tsum_nonneg (zeroWeight_nonneg θ)
    have hR : 0 ≤ ∑' q, rightSubstripTailWeight σ F q :=
      tsum_nonneg (rightSubstripTailWeight_nonneg σ F)
    positivity
  rw [abs_le]
  constructor <;> linarith

/-- A power-saving short-window error remains after paying the reciprocal
mass omitted from the right substrip. -/
theorem exists_finite_sum_approximation_with_reciprocal_tail {F : Finset XiZeroCopy} {β σ : ℝ} (hσ : 1 / 2 < σ)
    (hσβ : σ < β) (hβ1 : β ≤ 1) (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) :
    ∃ C x₀ : ℝ, ∀ x, x₀ ≤ x →
      |Chebyshev.psi x - x + (∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re|
        ≤ C * x ^ ((β + σ) / 2) +
          2 * x ^ β * (∑' q, rightSubstripTailWeight σ F q) := by
  set E : ℝ := (β + σ) / 2 with hE
  set θ : ℝ := (β - σ) / 4 with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have hE0 : 0 < E := by rw [hE]; linarith
  have hE1 : E < 1 := by rw [hE]; linarith
  have hgap : 0 < 1 - E := by linarith
  set W : ℝ := ∑' q, zeroWeight θ q with hW
  have hW0 : 0 ≤ W := tsum_nonneg (zeroWeight_nonneg θ)
  have hlog : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  refine ⟨2 + Real.log (2 * Real.pi) + 2 * F.card + 16 * W,
    max 4 ((2 : ℝ) ^ (1 / (1 - E))), fun x hx => ?_⟩
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx2 : (2 : ℝ) ^ (1 / (1 - E)) ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set H : ℝ := x ^ E with hH
  have hH1 : 1 ≤ H := Real.one_le_rpow hx1 hE0.le
  have hH0 : 0 < H := by linarith
  have h2 : 2 ≤ x ^ (1 - E) := by
    have h := Real.rpow_le_rpow (by positivity) hx2 hgap.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hgap.ne', Real.rpow_one] at h
  have hsplit : H * x ^ (1 - E) = x := by
    rw [hH, ← Real.rpow_add hx0]
    simp
  have hHx : H ≤ x / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hmain := abs_psi_sub_add_re_finiteSum_le (F := F) (x := x) (H := H) hσ hβ hθ0 hθ1 hx4 hH1 hHx
  refine hmain.trans ?_
  have hratio : (x / H) ^ θ ≤ x ^ θ := by
    refine Real.rpow_le_rpow (by positivity) ?_ hθ0.le
    exact div_le_self hx0.le hH1
  have hβθ : x ^ σ * x ^ θ ≤ H := by
    rw [← Real.rpow_add hx0, hH]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    rw [hE, hθ]
    linarith
  have hxβ : 0 ≤ x ^ σ := Real.rpow_nonneg hx0.le _
  have hlast : 16 * x ^ σ * (x / H) ^ θ * W ≤ 16 * W * H := by
    calc 16 * x ^ σ * (x / H) ^ θ * W ≤ 16 * x ^ σ * x ^ θ * W := by gcongr
      _ = 16 * W * (x ^ σ * x ^ θ) := by ring
      _ ≤ 16 * W * H := by gcongr
  have hc : (F.card : ℝ) * (2 * H) = 2 * F.card * H := by ring
  rw [hc]
  nlinarith [mul_nonneg hlog (sub_nonneg.mpr hH1)]

/-- A finite subset of the right substrip carries all but an arbitrarily small
reciprocal mass. -/
theorem exists_rightSubstripTailWeight_lt {σ ε : ℝ} (hσ : 1 / 2 < σ) (hε : 0 < ε) :
    ∃ F : Finset XiZeroCopy, (∀ q ∈ F, σ ≤ (q.1 : ℂ).re) ∧
      (∑' q, rightSubstripTailWeight σ F q) < ε := by
  classical
  let w := rightSubstripTailWeight σ ∅
  have hs : Summable w := summable_rightSubstripTailWeight hσ ∅
  obtain ⟨S, hS⟩ := Metric.tendsto_atTop.mp hs.hasSum ε hε
  let F := S.filter (fun q => σ ≤ (q.1 : ℂ).re)
  have hF : ∀ q ∈ F, σ ≤ (q.1 : ℂ).re := fun q hq => (Finset.mem_filter.mp hq).2
  refine ⟨F, hF, ?_⟩
  have heq : (∑ q ∈ F, w q) = ∑ q ∈ S, w q := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hq hnot
    have hr : ¬ σ ≤ (q.1 : ℂ).re := fun hr => hnot (Finset.mem_filter.mpr ⟨hq, hr⟩)
    simp only [w, rightSubstripTailWeight, hr, false_and, if_false]
  have htail : (∑' q : ((F : Set XiZeroCopy)ᶜ : Set XiZeroCopy), w q) =
      ∑' q, rightSubstripTailWeight σ F q := by
    rw [tsum_subtype]
    apply tsum_congr
    intro q
    by_cases hq : q ∈ F <;> by_cases hr : σ ≤ (q.1 : ℂ).re <;>
      simp [Set.indicator, w, rightSubstripTailWeight, hq, hr]
  have hsplit := hs.sum_add_tsum_compl (s := F)
  rw [heq, htail] at hsplit
  have hd := hS S le_rfl
  rw [Real.dist_eq, abs_lt] at hd
  linarith only [hsplit, hd.1]

/-- The normalized zero term retained by a closed right substrip. -/
def rightNormalizedZeroTerm (σ β x : ℝ) (q : XiZeroCopy) : ℂ :=
  if σ ≤ (q.1 : ℂ).re then (x : ℂ) ^ ((q.1 : ℂ) - (β : ℂ)) / (q.1 : ℂ) else 0

/-- The absolutely convergent normalized trace of the right substrip. -/
def rightNormalizedZeroTrace (σ β x : ℝ) : ℂ := ∑' q, rightNormalizedZeroTerm σ β x q

theorem norm_rightNormalizedZeroTerm_le {σ β x : ℝ} (hx : 1 ≤ x)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) (q : XiZeroCopy) :
    ‖rightNormalizedZeroTerm σ β x q‖ ≤ rightSubstripTailWeight σ ∅ q := by
  classical
  by_cases hq : σ ≤ (q.1 : ℂ).re
  · simp only [rightNormalizedZeroTerm, rightSubstripTailWeight, hq, Finset.notMem_empty,
      not_false_eq_true, and_self, if_true]
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx),
      Complex.sub_re, Complex.ofReal_re]
    simpa only [one_div] using div_le_div_of_nonneg_right
      (Real.rpow_le_one_of_one_le_of_nonpos hx (sub_nonpos.mpr (hβ q))) (norm_nonneg _)
  · simp only [rightNormalizedZeroTerm, rightSubstripTailWeight, hq, false_and, if_false,
      norm_zero, le_refl]

theorem summable_rightNormalizedZeroTerm {σ β x : ℝ} (hσ : 1 / 2 < σ)
    (hx : 1 ≤ x) (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) :
    Summable (rightNormalizedZeroTerm σ β x) :=
  Summable.of_norm_bounded (summable_rightSubstripTailWeight hσ ∅)
    (norm_rightNormalizedZeroTerm_le hx hβ)

/-- The normalized trace is uniformly approximated by its finite zero sums. -/
theorem norm_rightNormalizedZeroTrace_sub_sum_le {σ β x : ℝ} (hσ : 1 / 2 < σ)
    (hx : 1 ≤ x) (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) (F : Finset XiZeroCopy) :
    ‖rightNormalizedZeroTrace σ β x - ∑ q ∈ F, rightNormalizedZeroTerm σ β x q‖ ≤
      ∑' q, rightSubstripTailWeight σ F q := by
  classical
  have hs := summable_rightNormalizedZeroTerm hσ hx hβ
  have hsplit := hs.sum_add_tsum_compl (s := F)
  have heq : rightNormalizedZeroTrace σ β x - ∑ q ∈ F, rightNormalizedZeroTerm σ β x q =
      ∑' q : ((F : Set XiZeroCopy)ᶜ : Set XiZeroCopy), rightNormalizedZeroTerm σ β x q := by
    rw [rightNormalizedZeroTrace, ← hsplit]
    ring
  have htail : (∑' q : ((F : Set XiZeroCopy)ᶜ : Set XiZeroCopy), rightSubstripTailWeight σ ∅ q) =
      ∑' q, rightSubstripTailWeight σ F q := by
    rw [tsum_subtype]
    apply tsum_congr
    intro q
    by_cases hq : q ∈ F <;> by_cases hr : σ ≤ (q.1 : ℂ).re <;>
      simp [Set.indicator, rightSubstripTailWeight, hq, hr]
  rw [heq, ← htail]
  refine (norm_tsum_le_tsum_norm (hs.norm.subtype _)).trans ?_
  exact (hs.norm.subtype _).tsum_le_tsum (fun q => norm_rightNormalizedZeroTerm_le hx hβ q)
    ((summable_rightSubstripTailWeight hσ ∅).subtype _)

private theorem rightNormalizedZeroTerm_eq_div {σ β x : ℝ} (hx : 0 < x)
    (q : XiZeroCopy) (hq : σ ≤ (q.1 : ℂ).re) :
    rightNormalizedZeroTerm σ β x q =
      ((x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)) / ((x ^ β : ℝ) : ℂ) := by
  rw [rightNormalizedZeroTerm, if_pos hq,
    Complex.cpow_sub _ _ (by exact_mod_cast hx.ne'), Complex.ofReal_cpow hx.le β]
  ring

/-- Above the critical line the raw prime error has the same normalized trace
as any fixed right substrip containing the boundary. -/
theorem tendsto_normalized_primeError_add_rightTrace {σ β : ℝ}
    (hσ : 1 / 2 < σ) (hσβ : σ < β) (hβ1 : β ≤ 1)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - x) / x ^ β +
      (rightNormalizedZeroTrace σ β x).re) atTop (𝓝 0) := by
  classical
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨F, hF, htail⟩ := exists_rightSubstripTailWeight_lt hσ
    (show 0 < ε / 6 by positivity)
  obtain ⟨C, x₀, hC⟩ := exists_finite_sum_approximation_with_reciprocal_tail
    (F := F) hσ hσβ hβ1 hβ
  have hg : 0 < β - (β + σ) / 2 := by linarith only [hσβ]
  have hp : Tendsto (fun x : ℝ => (x ^ (β - (β + σ) / 2))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hg)
  have hsmall : Tendsto (fun x : ℝ => C * x ^ ((β + σ) / 2) / x ^ β) atTop (𝓝 0) := by
    have h := hp.const_mul C
    simp only [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_neg hx.le, neg_sub, Real.rpow_sub hx]
    ring
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1
    (hsmall.eventually_lt_const (show 0 < ε / 2 by positivity))
  refine ⟨max 1 (max x₀ x₁), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hxx₀ : x₀ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxx₁ : x₁ ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hxβ : 0 < x ^ β := Real.rpow_pos_of_pos hx0 _
  have hR : (∑ q ∈ F, rightNormalizedZeroTerm σ β x q).re =
      (∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re / x ^ β := by
    rw [Finset.sum_congr rfl fun q hq => rightNormalizedZeroTerm_eq_div hx0 q (hF q hq),
      ← Finset.sum_div]
    simp only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  have hfinite : |(Chebyshev.psi x - x) / x ^ β +
      (∑ q ∈ F, rightNormalizedZeroTerm σ β x q).re| ≤
      C * x ^ ((β + σ) / 2) / x ^ β + 2 * (∑' q, rightSubstripTailWeight σ F q) := by
    rw [hR, ← add_div, abs_div, abs_of_pos hxβ]
    refine (div_le_div_of_nonneg_right (hC x hxx₀) hxβ.le).trans_eq ?_
    field_simp
  have htrace : |(rightNormalizedZeroTrace σ β x).re -
      (∑ q ∈ F, rightNormalizedZeroTerm σ β x q).re| ≤
      ∑' q, rightSubstripTailWeight σ F q := by
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans
      (norm_rightNormalizedZeroTrace_sub_sum_le hσ hx1 hβ F)
  have heq : (Chebyshev.psi x - x) / x ^ β + (rightNormalizedZeroTrace σ β x).re =
      ((Chebyshev.psi x - x) / x ^ β + (∑ q ∈ F, rightNormalizedZeroTerm σ β x q).re) +
      ((rightNormalizedZeroTrace σ β x).re - (∑ q ∈ F, rightNormalizedZeroTerm σ β x q).re) := by ring
  rw [Real.dist_eq, sub_zero, heq]
  refine (abs_add_le _ _).trans_lt ?_
  have hc := hx₁ x hxx₁
  linarith only [hfinite, htrace, hc, htail]

/-- The real boundary trace, with multiplicities and the sign of the explicit formula. -/
def primeErrorBoundaryTrace (β u : ℝ) : ℝ :=
  -(∑' q : XiZeroCopy, if (q.1 : ℂ).re = β then
    Complex.exp (((q.1 : ℂ) - (β : ℂ)) * (u : ℂ)) / (q.1 : ℂ) else 0).re

private theorem rightNormalizedZeroTrace_exp (σ β u : ℝ) :
    rightNormalizedZeroTrace σ β (Real.exp u) =
      ∑' q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re},
        Complex.exp (((q.1.1 : ℂ) - (β : ℂ)) * (u : ℂ)) / (q.1.1 : ℂ) := by
  classical
  change (∑' q, {q : XiZeroCopy | σ ≤ (q.1 : ℂ).re}.indicator
    (fun q => ((Real.exp u : ℝ) : ℂ) ^ ((q.1 : ℂ) - (β : ℂ)) / (q.1 : ℂ)) q) = _
  rw [← tsum_subtype]
  apply tsum_congr
  intro q
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.exp_ne_zero u),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
  congr 2
  ring

theorem tendsto_rightNormalizedZeroTrace_add_boundary {σ β : ℝ}
    (hσ : 1 / 2 < σ) (hσβ : σ ≤ β)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) :
    Tendsto (fun u : ℝ => (rightNormalizedZeroTrace σ β (Real.exp u)).re +
      primeErrorBoundaryTrace β u) atTop (𝓝 0) := by
  classical
  have h := (Complex.continuous_re.tendsto 0).comp
    (tendsto_rightSubstrip_sum_sub_boundary hσ hβ)
  simp only [Complex.zero_re, Function.comp_def, Complex.sub_re] at h
  refine h.congr fun u => ?_
  rw [rightNormalizedZeroTrace_exp, primeErrorBoundaryTrace, sub_eq_add_neg]
  congr 2
  apply congrArg Complex.re
  change (∑' q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re},
      (fun q : XiZeroCopy => if (q.1 : ℂ).re = β then
        Complex.exp (((q.1 : ℂ) - (β : ℂ)) * (u : ℂ)) / (q.1 : ℂ) else 0) q) = _
  refine (tsum_subtype {q : XiZeroCopy | σ ≤ (q.1 : ℂ).re}
    (fun q : XiZeroCopy => if (q.1 : ℂ).re = β then
      Complex.exp (((q.1 : ℂ) - (β : ℂ)) * (u : ℂ)) / (q.1 : ℂ) else 0)).trans ?_
  apply tsum_congr
  intro q
  by_cases hq : (q.1 : ℂ).re = β
  · have hr : σ ≤ (q.1 : ℂ).re := by rwa [hq]
    simp only [Set.indicator_of_mem (show q ∈ {q : XiZeroCopy | σ ≤ (q.1 : ℂ).re} from hr),
      hq, if_true]
  · by_cases hr : σ ≤ (q.1 : ℂ).re <;> simp [Set.indicator, hq, hr]

/-- The boundary expansion of the unsmoothed prime error at every bounding
abscissa strictly above `1/2`, including a boundary with infinitely many zeros. -/
theorem tendsto_normalized_primeError_sub_boundary_of_bound {β : ℝ}
    (hβ0 : 1 / 2 < β) (hβ1 : β ≤ 1)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - x) / x ^ β -
      primeErrorBoundaryTrace β (Real.log x)) atTop (𝓝 0) := by
  let σ := (β + 1 / 2) / 2
  have hσ : 1 / 2 < σ := by dsimp [σ]; linarith only [hβ0]
  have hσβ : σ < β := by dsimp [σ]; linarith only [hβ0]
  have hprime := (tendsto_normalized_primeError_add_rightTrace hσ hσβ hβ1 hβ).comp
    Real.tendsto_exp_atTop
  have hboundary := tendsto_rightNormalizedZeroTrace_add_boundary hσ hσβ.le hβ
  have h := hprime.sub hboundary
  simp only [sub_zero, Function.comp_def] at h
  have he : Tendsto (fun u : ℝ => (Chebyshev.psi (Real.exp u) - Real.exp u) /
      (Real.exp u) ^ β - primeErrorBoundaryTrace β u) atTop (𝓝 0) := by
    refine h.congr fun u => ?_
    ring
  refine (he.comp Real.tendsto_log_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_def, Real.exp_log hx]

/-- At the actual zero abscissa, the normalized prime error differs from its
absolutely convergent boundary trace by a function tending to zero. -/
theorem tendsto_normalized_primeError_sub_boundary (hΘ : 1 / 2 < zetaZeroAbscissa) :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - x) / x ^ zetaZeroAbscissa -
      primeErrorBoundaryTrace zetaZeroAbscissa (Real.log x)) atTop (𝓝 0) :=
  tendsto_normalized_primeError_sub_boundary_of_bound hΘ zetaZeroAbscissa_le_one
    (fun q => re_le_zetaZeroAbscissa (riemannZeta_eq_zero_of_xiZeroCopy q))

/-- The multiplicity-copy amplitude of the boundary trace. -/
def primeErrorBoundaryAmplitude (β : ℝ) (q : XiZeroCopy) : ℂ :=
  if (q.1 : ℂ).re = β then -((q.1 : ℂ)⁻¹) else 0

theorem summable_primeErrorBoundaryAmplitude {β : ℝ} (hβ : 1 / 2 < β) :
    Summable (fun q => ‖primeErrorBoundaryAmplitude β q‖) := by
  refine (summable_rightSubstripTailWeight hβ ∅).of_nonneg_of_le
    (fun q => norm_nonneg _) fun q => ?_
  by_cases hq : (q.1 : ℂ).re = β
  · have hr : β ≤ (q.1 : ℂ).re := hq.ge
    simp only [primeErrorBoundaryAmplitude, hq, if_true, norm_neg, norm_inv,
      rightSubstripTailWeight, hq, le_refl, Finset.notMem_empty, not_false_eq_true, and_self, if_true]
  · simp only [primeErrorBoundaryAmplitude, hq, if_false, norm_zero]
    exact rightSubstripTailWeight_nonneg β ∅ q

theorem primeErrorBoundaryTrace_eq_re_expSeries (β u : ℝ) :
    primeErrorBoundaryTrace β u =
      (expSeriesCarrier (primeErrorBoundaryAmplitude β) xiCopyOrdinate u).re := by
  classical
  have he : expSeriesCarrier (primeErrorBoundaryAmplitude β) xiCopyOrdinate u =
      -(∑' q : XiZeroCopy, if (q.1 : ℂ).re = β then
        Complex.exp (((q.1 : ℂ) - (β : ℂ)) * (u : ℂ)) / (q.1 : ℂ) else 0) := by
    rw [expSeriesCarrier, ← tsum_neg]
    apply tsum_congr
    intro q
    by_cases hq : (q.1 : ℂ).re = β
    · have hphase : ((q.1 : ℂ) - (β : ℂ)) * (u : ℂ) =
          ((xiCopyOrdinate q * u : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp [xiCopyOrdinate, hq]
      simp only [primeErrorBoundaryAmplitude, hq, if_true, expChar, hphase]
      ring
    · simp only [primeErrorBoundaryAmplitude, hq, if_false, zero_mul, neg_zero]
  rw [he, Complex.neg_re]
  rfl

/-- The boundary trace is uniformly almost periodic, even when the top layer is infinite. -/
theorem isBohrAlmostPeriodic_primeErrorBoundaryTrace {β : ℝ} (hβ : 1 / 2 < β) :
    HTGeometry.IsBohrAlmostPeriodic (primeErrorBoundaryTrace β) := by
  have hap := isBohrAlmostPeriodic_expSeriesCarrier
    (summable_primeErrorBoundaryAmplitude hβ) xiCopyOrdinate
  intro ε hε
  obtain ⟨L, hL, hshift⟩ := hap ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτ, hτbound⟩ := hshift a
  refine ⟨τ, hτ, fun u => ?_⟩
  rw [primeErrorBoundaryTrace_eq_re_expSeries, primeErrorBoundaryTrace_eq_re_expSeries,
    Real.norm_eq_abs, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (hτbound u)

/-- At zero logarithmic time every boundary zero contributes a strictly
negative real reciprocal. Thus a nonempty boundary trace cannot vanish. -/
theorem primeErrorBoundaryTrace_zero_lt {β : ℝ} (hβ : 1 / 2 < β)
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re = β) : primeErrorBoundaryTrace β 0 < 0 := by
  classical
  let a := primeErrorBoundaryAmplitude β
  let v := fun p : XiZeroCopy => -(a p).re
  have hs : Summable a := Summable.of_norm (summable_primeErrorBoundaryAmplitude hβ)
  have hv : Summable v := (Complex.hasSum_re hs.hasSum).summable.neg
  have hv0 (p : XiZeroCopy) : 0 ≤ v p := by
    by_cases hp : (p.1 : ℂ).re = β
    · simp only [v, a, primeErrorBoundaryAmplitude, hp, if_true, Complex.neg_re,
        neg_neg, Complex.inv_re]
      exact div_nonneg (by linarith only [hβ]) (Complex.normSq_nonneg _)
    · simp only [v, a, primeErrorBoundaryAmplitude, hp, if_false, Complex.zero_re, neg_zero,
        le_refl]
  have hvq : 0 < v q := by
    simp only [v, a, primeErrorBoundaryAmplitude, hq, if_true, Complex.neg_re,
      neg_neg, Complex.inv_re]
    exact div_pos (by linarith only [hβ]) (Complex.normSq_pos.mpr (xiZeroCopy_ne_zero q))
  have hle : v q ≤ ∑' p, v p := by
    simpa only [Finset.sum_singleton] using hv.sum_le_tsum {q} (fun p _ => hv0 p)
  have he : primeErrorBoundaryTrace β 0 = -(∑' p, v p) := by
    rw [primeErrorBoundaryTrace_eq_re_expSeries, expSeriesCarrier]
    simp only [expChar, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [Complex.re_tsum hs]
    simp only [v, tsum_neg, neg_neg, a]
  rw [he]
  exact neg_neg_of_pos (hvq.trans_le hle)

theorem primeErrorBoundaryTrace_eq_zero_of_empty {β : ℝ}
    (h : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ β) (u : ℝ) :
    primeErrorBoundaryTrace β u = 0 := by
  simp only [primeErrorBoundaryTrace, h, if_false, tsum_zero, Complex.zero_re, neg_zero]

/-- Decay of the almost-periodic boundary is equivalent to an empty top line. -/
theorem tendsto_primeErrorBoundaryTrace_zero_iff {β : ℝ} (hβ : 1 / 2 < β) :
    Tendsto (primeErrorBoundaryTrace β) atTop (𝓝 0) ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ β := by
  constructor
  · intro ht q hq
    have hz := HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero
      (isBohrAlmostPeriodic_primeErrorBoundaryTrace hβ) ht 0
    exact (ne_of_lt (primeErrorBoundaryTrace_zero_lt hβ q hq)) hz
  · intro h
    have he : primeErrorBoundaryTrace β = fun _ => (0 : ℝ) :=
      funext (primeErrorBoundaryTrace_eq_zero_of_empty h)
    rw [he]
    exact tendsto_const_nhds

/-- The normalized raw prime error tends to zero exactly when the actual top
line is empty. -/
theorem tendsto_normalized_primeError_zero_iff_empty_top
    (hΘ : 1 / 2 < zetaZeroAbscissa) :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - x) / x ^ zetaZeroAbscissa) atTop (𝓝 0) ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ zetaZeroAbscissa := by
  have hrem := tendsto_normalized_primeError_sub_boundary hΘ
  constructor
  · intro hnorm
    have hb : Tendsto (fun x : ℝ => primeErrorBoundaryTrace zetaZeroAbscissa (Real.log x))
        atTop (𝓝 0) := by
      have h := hnorm.sub hrem
      simp only [sub_zero] at h
      refine h.congr fun x => ?_
      ring
    have ht : Tendsto (primeErrorBoundaryTrace zetaZeroAbscissa) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.log_exp] using hb.comp Real.tendsto_exp_atTop
    exact (tendsto_primeErrorBoundaryTrace_zero_iff hΘ).mp ht
  · intro h
    simpa only [primeErrorBoundaryTrace_eq_zero_of_empty h, sub_zero] using hrem

end GaloisForLFunctions.ZeroConfigurationGeometry
