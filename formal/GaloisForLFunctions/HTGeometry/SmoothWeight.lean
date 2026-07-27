import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# A smooth cutoff with scaled derivative bounds

`smoothWeight N H` is smooth, equal to `1` on `(-∞, N]`, to `0` on `[N+H, ∞)`, takes values in
`[0,1]`, and has `j`-th derivative bounded by `C j / H ^ j`.

The scaling of the derivatives is what matters downstream: it is the source of the decay
`(1 + |t| H / N)^{-j}` of the Mellin transform of the weight, obtained by integrating by parts `j`
times, and hence of the absolute convergence of the vertical integral in the smoothed Perron
formula.

Every derivative of `Real.smoothTransition` is bounded because it is continuous and vanishes
outside `[0,1]`: the transition is locally constant on either side, so all derivatives of positive
order vanish there.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

/-- Every iterated derivative of the smooth transition is globally bounded. -/
theorem exists_bound_iteratedDeriv_smoothTransition (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv j Real.smoothTransition x| ≤ C := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine ⟨1, zero_le_one, fun x => ?_⟩
    rw [iteratedDeriv_zero, abs_of_nonneg (Real.smoothTransition.nonneg x)]
    exact Real.smoothTransition.le_one x
  have hcont : Continuous (iteratedDeriv j Real.smoothTransition) :=
    ContDiff.continuous_iteratedDeriv j (Real.smoothTransition.contDiff (n := (j : ℕ∞))) le_rfl
  have hjne : j ≠ 0 := by omega
  have hleft : ∀ x : ℝ, x < 0 → iteratedDeriv j Real.smoothTransition x = 0 := by
    intro x hx
    have heq : Real.smoothTransition =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [heq.iteratedDeriv_eq j, iteratedDeriv_const, if_neg hjne]
  have hright : ∀ x : ℝ, 1 < x → iteratedDeriv j Real.smoothTransition x = 0 := by
    intro x hx
    have heq : Real.smoothTransition =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [heq.iteratedDeriv_eq j, iteratedDeriv_const, if_neg hjne]
  obtain ⟨x₀, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (continuous_abs.comp hcont).continuousOn
  refine ⟨max |iteratedDeriv j Real.smoothTransition x₀| 1,
    le_trans zero_le_one (le_max_right _ _), fun x => ?_⟩
  rcases lt_or_ge x 0 with hx | hx0
  · rw [hleft x hx, abs_zero]
    exact le_trans zero_le_one (le_max_right _ _)
  rcases le_or_gt x 1 with hx1 | hx1
  · exact le_trans (hmax ⟨hx0, hx1⟩) (le_max_left _ _)
  · rw [hright x hx1, abs_zero]
    exact le_trans zero_le_one (le_max_right _ _)

/-- A smooth cutoff: `1` up to `N`, `0` from `N + H` on. -/
noncomputable def smoothWeight (N H : ℝ) : ℝ → ℝ :=
  fun x => 1 - Real.smoothTransition (H⁻¹ * (x + -N))

theorem smoothWeight_contDiff (N H : ℝ) {n : ℕ∞} : ContDiff ℝ (n : WithTop ℕ∞) (smoothWeight N H) := by
  refine ContDiff.sub contDiff_const ?_
  exact (Real.smoothTransition.contDiff (n := n)).comp (by fun_prop)

theorem smoothWeight_eq_one {N H : ℝ} (hH : 0 < H) {x : ℝ} (hx : x ≤ N) :
    smoothWeight N H x = 1 := by
  rw [smoothWeight, Real.smoothTransition.zero_of_nonpos ?_, sub_zero]
  have : x + -N ≤ 0 := by linarith
  have hinv : (0 : ℝ) < H⁻¹ := by positivity
  nlinarith

theorem smoothWeight_eq_zero {N H : ℝ} (hH : 0 < H) {x : ℝ} (hx : N + H ≤ x) :
    smoothWeight N H x = 0 := by
  have hkey : (1 : ℝ) ≤ H⁻¹ * (x + -N) := by
    have hinv : (0 : ℝ) < H⁻¹ := by positivity
    have hHx : H ≤ x + -N := by linarith
    have h1 : H⁻¹ * H ≤ H⁻¹ * (x + -N) := mul_le_mul_of_nonneg_left hHx hinv.le
    rwa [inv_mul_cancel₀ hH.ne'] at h1
  rw [smoothWeight, Real.smoothTransition.one_of_one_le hkey, sub_self]

theorem smoothWeight_nonneg (N H : ℝ) (x : ℝ) : 0 ≤ smoothWeight N H x := by
  rw [smoothWeight]
  linarith [Real.smoothTransition.le_one (H⁻¹ * (x + -N))]

theorem smoothWeight_le_one (N H : ℝ) (x : ℝ) : smoothWeight N H x ≤ 1 := by
  rw [smoothWeight]
  linarith [Real.smoothTransition.nonneg (H⁻¹ * (x + -N))]

/-- **Scaled derivative bounds.**  The `j`-th derivative of the cutoff is `O(H^{-j})`. -/
theorem exists_bound_iteratedDeriv_smoothWeight {H : ℝ} (hH : 0 < H) (N : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv j (smoothWeight N H) x| ≤ C / H ^ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine ⟨1, zero_le_one, fun x => ?_⟩
    rw [iteratedDeriv_zero, pow_zero, div_one,
      abs_of_nonneg (smoothWeight_nonneg N H x)]
    exact smoothWeight_le_one N H x
  obtain ⟨C, hC, hbound⟩ := exists_bound_iteratedDeriv_smoothTransition j
  refine ⟨C, hC, fun x => ?_⟩
  have hcd : ContDiff ℝ ((j : ℕ) : WithTop ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff (n := (j : ℕ∞))
  -- peel off the constant, then the shift, then the scaling
  have hG : ContDiff ℝ ((j : ℕ) : WithTop ℕ∞)
      (fun y : ℝ => Real.smoothTransition (H⁻¹ * (y + -N))) :=
    hcd.comp (by fun_prop)
  have hstep : iteratedDeriv j (smoothWeight N H) x
      = -iteratedDeriv j (fun y : ℝ => Real.smoothTransition (H⁻¹ * (y + -N))) x := by
    have hdef : smoothWeight N H
        = fun y : ℝ => 1 - Real.smoothTransition (H⁻¹ * (y + -N)) := rfl
    rw [hdef, iteratedDeriv_const_sub hj]
    simp [iteratedDeriv_neg]
  rw [hstep, abs_neg]
  have hshift : (iteratedDeriv j fun y : ℝ => Real.smoothTransition (H⁻¹ * (y + -N)))
      = fun t : ℝ => iteratedDeriv j (fun z : ℝ => Real.smoothTransition (H⁻¹ * z)) (t + -N) :=
    iteratedDeriv_comp_add_const j (fun z : ℝ => Real.smoothTransition (H⁻¹ * z)) (-N)
  rw [hshift]
  have hscale : (iteratedDeriv j fun z : ℝ => Real.smoothTransition (H⁻¹ * z))
      = fun z : ℝ => (H⁻¹) ^ j * iteratedDeriv j Real.smoothTransition (H⁻¹ * z) :=
    iteratedDeriv_comp_const_mul hcd H⁻¹
  rw [hscale, abs_mul, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < H⁻¹)]
  rw [div_eq_mul_inv, ← inv_pow, mul_comm C ((H⁻¹) ^ j)]
  exact mul_le_mul_of_nonneg_left (hbound _) (by positivity)

end GaloisForLFunctions.HTGeometry
