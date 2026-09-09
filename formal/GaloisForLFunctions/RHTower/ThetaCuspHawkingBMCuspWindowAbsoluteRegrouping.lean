import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspHeightRowPeriodization

/-! Absolute row admission gives full projective orbit admission through the unchanged translation window. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMModularCore
noncomputable section

/-- The original translation partition is nonnegative. -/
theorem cuspWindow_nonneg (x : ℝ) : 0 ≤ cuspWindow x := by
  unfold cuspWindow
  exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

/-- Every horizontal coordinate has only finitely many nonzero translation-window values. -/
theorem cuspWindow_translation_finite (x : ℝ) :
    Function.HasFiniteSupport (fun n : ℤ => cuspWindow (x+n)) := by
  apply (Set.finite_Icc ⌊-x-1⌋ ⌈1-x⌉).subset
  intro n hn
  have hl : -1 < x+n := lt_of_not_ge (fun h => hn (cuspWindow_zero_left h))
  have hr : x+n < 1 := lt_of_not_ge (fun h => hn (cuspWindow_zero_right h))
  constructor
  · have h : (⌊-x-1⌋:ℝ) ≤ (n:ℝ) := by linarith [Int.floor_le (-x-1)]
    exact_mod_cast h
  · have h : (n:ℝ) ≤ (⌈1-x⌉:ℝ) := by linarith [Int.le_ceil (1-x)]
    exact_mod_cast h

/-- The full translation row retains exactly the norm of its original height value. -/
theorem cuspHeightSeed_translation_norm_sum (h : ℝ → ℂ) (v : gammaSetHalf) (z : UpperHalfPlane) :
    (∑' n : ℤ, ‖cuspHeightSeed h (cuspOrbitEquiv (v,n) • z)‖) =
      ‖h (gammaSetMatrix v.1 • z).im‖ := by
  simp_rw [cuspOrbitEquiv_smul,cuspHeightSeed,ModularGroup.re_T_zpow_smul,
    ModularGroup.im_T_zpow_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (cuspWindow_nonneg _)]
  rw [tsum_mul_right,cuspWindow_partition_all,one_mul]

/-- Summable height rows admit the entire projective sum, even for profiles extending to height zero. -/
theorem cuspHeightSeed_orbit_summable_of_rows (h : ℝ → ℂ) (z : UpperHalfPlane)
    (hs : Summable (fun v : gammaSetHalf => h (gammaSetMatrix v.1 • z).im)) :
    Summable (fun γ : PSL2Z => cuspHeightSeed h (γ • z)) := by
  have hi : ∀ v : gammaSetHalf, Summable (fun n : ℤ => ‖cuspHeightSeed h (cuspOrbitEquiv (v,n) • z)‖) := by
    intro v
    simp_rw [cuspOrbitEquiv_smul,cuspHeightSeed,ModularGroup.re_T_zpow_smul,
      ModularGroup.im_T_zpow_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (cuspWindow_nonneg _)]
    exact (summable_of_hasFiniteSupport (cuspWindow_translation_finite _)).mul_right _
  have hp : Summable (fun p : gammaSetHalf × ℤ => ‖cuspHeightSeed h (cuspOrbitEquiv p • z)‖) := by
    apply (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
    exact ⟨hi,hs.norm.congr (fun v => (cuspHeightSeed_translation_norm_sum h v z).symm)⟩
  exact cuspOrbitEquiv.summable_iff.mp hp.of_norm

/-- The exact row identity now follows from row convergence itself, without a high-support premise. -/
theorem periodize_cuspHeightSeed_eq_rows_of_rows_summable (h : ℝ → ℂ) (z : UpperHalfPlane)
    (hs : Summable (fun v : gammaSetHalf => h (gammaSetMatrix v.1 • z).im)) :
    periodize (cuspHeightSeed h) z = ∑' v : gammaSetHalf, h (gammaSetMatrix v.1 • z).im :=
  periodize_cuspHeightSeed_eq_rows_of_summable h z (cuspHeightSeed_orbit_summable_of_rows h z hs)

end
end RHTower.D4BMModularCore
