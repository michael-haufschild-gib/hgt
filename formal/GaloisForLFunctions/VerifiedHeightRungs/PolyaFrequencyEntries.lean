import GaloisForLFunctions.VerifiedHeightRungs.JensenEntries
import GaloisForLFunctions.RHTower.XiSliceCoeffOrderTwentyThreeBand

/-!
# Pólya frequency orders and the slice band from verified zeros

A zero of `ξ` lies in the visibility cone of order `k` at height `t` when
`cos(π/(k+1)) ((γ−t)² + δ²) ≤ (γ−t)² − δ²`, `δ = β − ½`. An on-line zero always does, and an off-line zero does when
`|γ − t| ≥ Δ`, `k + 1 ≤ 3Δ`, `Δ ≥ 5`, since `Δ²(1 − cos(π/(3Δ))) ≥ ½`. So if RH holds through `T`:

* **Centre** (`xi_centre_pfSeq_of_rhVerifiedThrough`): the Taylor coefficients of `ξ(½ + x)` form a `PF_k` sequence
  for `k + 1 ≤ 3T`, `T ≥ 5`;
* **Slice** (`xiSliceCoeff_pfSeq_of_rhVerifiedThrough`): the slice coefficients at `t` are `PF_k` for
  `k + 1 ≤ 3Δ`, `|t| + Δ ≤ T`;
* **Band** (`xiSliceCoeff_nonneg_of_rhVerifiedThrough`): every coefficient of `ξ(½+x+it)ξ(½−x+it)` is nonnegative for
  `|t| ≤ T − ½`.
-/

open Complex
open RHTower GaloisForLFunctions.HTGeometry
open scoped ComplexOrder

namespace GaloisForLFunctions.VerifiedHeightRungs

theorem one_sub_cos_ge {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 4) : 49 / 100 * θ ^ 2 ≤ 1 - Real.cos θ := by
  have habs : |θ| ≤ 1 := by rw [abs_of_nonneg h0]; linarith only [h1]
  have hb := Real.cos_bound habs
  rw [abs_of_nonneg h0] at hb
  have hup := (abs_le.1 hb).2
  have h2 : θ ^ 2 ≤ 1 / 16 := by nlinarith only [h0, h1]
  have h4 : θ ^ 4 ≤ 1 / 16 * θ ^ 2 := by
    have := mul_le_mul_of_nonneg_right h2 (sq_nonneg θ)
    nlinarith only [this]
  nlinarith only [hup, h4, sq_nonneg θ]

/-- The cone constant: `½ ≤ Δ²(1 − cos(π/(k+1)))` for `k + 1 ≤ 3Δ`, `Δ ≥ 5`. -/
theorem half_le_sq_mul_one_sub_cos {Δ : ℝ} (hΔ : 5 ≤ Δ) {k : ℕ} (hk : ((k : ℝ) + 1) ≤ 3 * Δ) :
    1 / 2 ≤ Δ ^ 2 * (1 - Real.cos (Real.pi / ((k : ℝ) + 1))) := by
  have hΔ0 : 0 < Δ := by linarith only [hΔ]
  have hk0 : 0 < (k : ℝ) + 1 := by positivity
  have hπ := Real.pi_pos
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀, θ₀ = Real.pi / (3 * Δ) := ⟨_, rfl⟩
  have hθ₀0 : 0 ≤ θ₀ := by rw [hθ₀]; positivity
  have hθ₀1 : θ₀ ≤ 1 / 4 := by
    rw [hθ₀, div_le_iff₀ (by positivity)]
    have := Real.pi_lt_d2
    linarith only [this, hΔ]
  have hle : θ₀ ≤ Real.pi / ((k : ℝ) + 1) := by
    rw [hθ₀]
    exact div_le_div_of_nonneg_left hπ.le hk0 hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith only [this]
  have hpi : Real.pi / ((k : ℝ) + 1) ≤ Real.pi := div_le_self hπ.le hk1
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hθ₀0 hpi hle
  have hlow := one_sub_cos_ge hθ₀0 hθ₀1
  have hsq : Δ ^ 2 * θ₀ ^ 2 = Real.pi ^ 2 / 9 := by
    rw [hθ₀]
    field_simp
    norm_num
  have hπ2 : (9 : ℝ) ≤ Real.pi ^ 2 + 0.1 := by
    have := Real.pi_gt_three
    nlinarith only [this]
  have h1 : 1 - Real.cos θ₀ ≤ 1 - Real.cos (Real.pi / ((k : ℝ) + 1)) := by linarith only [hcos]
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg _
  calc
    (1 / 2 : ℝ) ≤ 49 / 100 * (Real.pi ^ 2 / 9) := by
      have := Real.pi_gt_d2
      nlinarith only [this]
    _ = Δ ^ 2 * (49 / 100 * θ₀ ^ 2) := by rw [← hsq]; ring
    _ ≤ Δ ^ 2 * (1 - Real.cos θ₀) := mul_le_mul_of_nonneg_left hlow hΔ2
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 hΔ2

/-- The cone inequality from distance `Δ`. -/
theorem cone_of_distance {x δ Δ c : ℝ} (hc : c ≤ 1) (hδ : δ ^ 2 < 1 / 4) (hΔ : 0 ≤ Δ)
    (hx : Δ ≤ |x|) (hmain : 1 / 2 ≤ Δ ^ 2 * (1 - c)) : c * (x ^ 2 + δ ^ 2) ≤ x ^ 2 - δ ^ 2 := by
  have hsq : Δ ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ hΔ hx 2
  have h1 : Δ ^ 2 * (1 - c) ≤ x ^ 2 * (1 - c) := mul_le_mul_of_nonneg_right hsq (by linarith only [hc])
  have h2 : δ ^ 2 * (1 + c) ≤ δ ^ 2 * 2 := mul_le_mul_of_nonneg_left (by linarith only [hc]) (sq_nonneg _)
  nlinarith only [h1, h2, hmain, hδ]

theorem re_eq_half_of_rhVerifiedThrough {T : ℝ} (hRH : RHVerifiedThrough T) (q : XiZeroCopy)
    (hq : |(q.1 : ℂ).im| ≤ T) : (q.1 : ℂ).re - 1 / 2 = 0 := by
  have h := im_xiSpectralPoint_eq_zero hRH q (by rw [re_xiSpectralPoint]; exact hq)
  rw [im_xiSpectralPoint] at h
  linarith only [h]

/-- **Centre rung.** If RH holds through `T ≥ 5`, the Taylor coefficients of `ξ` at the centre are `PF_k` for
`k + 1 ≤ 3T`. -/
theorem xi_centre_pfSeq_of_rhVerifiedThrough {T : ℝ} (hT : 5 ≤ T) (hRH : RHVerifiedThrough T) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ((k : ℝ) + 1) ≤ 3 * T) : PFSeq k (evenTaylorRe (fun x => xi (1 / 2 + x))) := by
  refine xi_centre_pfSeq_of_cone hk1 fun q => ?_
  by_cases hq : |(q.1 : ℂ).im| ≤ T
  · rw [re_eq_half_of_rhVerifiedThrough hRH q hq]
    have hc := Real.cos_le_one (Real.pi / ((k : ℝ) + 1))
    nlinarith only [hc, sq_nonneg ((q.1 : ℂ).im)]
  · exact cone_of_distance (Real.cos_le_one _)
      (xi_divisor_support_centered_re_sq_lt_quarter q.1) (by linarith only [hT]) (not_le.1 hq).le
      (half_le_sq_mul_one_sub_cos hT hk)

/-- **Slice rung.** If RH holds through `T` and `|t| + Δ ≤ T`, `Δ ≥ 5`, the slice coefficients at `t` are `PF_k`
for `k + 1 ≤ 3Δ`. -/
theorem xiSliceCoeff_pfSeq_of_rhVerifiedThrough {T Δ t : ℝ} (hΔ : 5 ≤ Δ) (ht : |t| + Δ ≤ T) (hRH : RHVerifiedThrough T)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : ((k : ℝ) + 1) ≤ 3 * Δ) :
    PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re) := by
  refine xiSliceCoeff_pfSeq_of_cone hk1 fun q => ?_
  by_cases hq : |(q.1 : ℂ).im| ≤ T
  · rw [re_eq_half_of_rhVerifiedThrough hRH q hq]
    have hc := Real.cos_le_one (Real.pi / ((k : ℝ) + 1))
    nlinarith only [hc, sq_nonneg ((q.1 : ℂ).im - t)]
  · refine cone_of_distance (Real.cos_le_one _)
      (xi_divisor_support_centered_re_sq_lt_quarter q.1) (by linarith only [hΔ]) ?_
      (half_le_sq_mul_one_sub_cos hΔ hk)
    have h1 := abs_sub_abs_le_abs_sub ((q.1 : ℂ).im) t
    linarith only [h1, not_le.1 hq, ht]

/-- **Band rung.** If RH holds through `T`, every Taylor coefficient of `ξ(½+x+it)ξ(½−x+it)` is nonnegative for
`|t| ≤ T − ½`. -/
theorem xiSliceCoeff_nonneg_of_rhVerifiedThrough {T t : ℝ} (ht : |t| + 1 / 2 ≤ T) (hRH : RHVerifiedThrough T) (n : ℕ) :
    0 ≤ xiSliceCoeff t n := by
  refine xiSliceCoeff_nonneg_of_cone (fun q => ?_) n
  by_cases hq : |(q.1 : ℂ).im| ≤ T
  · rw [re_eq_half_of_rhVerifiedThrough hRH q hq, abs_zero]
    exact abs_nonneg _
  · have h1 := abs_sub_abs_le_abs_sub ((q.1 : ℂ).im) t
    have hs := xiZeroCopy_re_mem_open_unit q
    have h2 : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith only [hs.1, hs.2]
    linarith only [h1, not_le.1 hq, ht, h2]

end GaloisForLFunctions.VerifiedHeightRungs

#print axioms GaloisForLFunctions.VerifiedHeightRungs.xi_centre_pfSeq_of_rhVerifiedThrough
#print axioms GaloisForLFunctions.VerifiedHeightRungs.xiSliceCoeff_pfSeq_of_rhVerifiedThrough
#print axioms GaloisForLFunctions.VerifiedHeightRungs.xiSliceCoeff_nonneg_of_rhVerifiedThrough
