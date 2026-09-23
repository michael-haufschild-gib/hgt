import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularCuspWeight

/-! Smooth cutoffs at growing cusp scale with uniform hyperbolic derivative bounds. -/
open Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def baseCuspCutoff (y : ℝ) : ℝ := 1-Real.smoothTransition (y-2)
def scaledCuspCutoff (N y : ℝ) : ℝ := baseCuspCutoff (y/N)

theorem baseCuspCutoff_smooth : ContDiff ℝ ∞ baseCuspCutoff :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem baseCuspCutoff_bounds (y : ℝ) : 0 ≤ baseCuspCutoff y ∧ baseCuspCutoff y ≤ 1 := by
  dsimp [baseCuspCutoff]
  constructor <;> linarith [Real.smoothTransition.nonneg (y-2),Real.smoothTransition.le_one (y-2)]

theorem baseCuspCutoff_low (y : ℝ) (hy : y ≤ 2) : baseCuspCutoff y = 1 := by
  rw [baseCuspCutoff,Real.smoothTransition.zero_of_nonpos (by linarith),sub_zero]

theorem baseCuspCutoff_high (y : ℝ) (hy : 3 ≤ y) : baseCuspCutoff y = 0 := by
  rw [baseCuspCutoff,Real.smoothTransition.one_of_one_le (by linarith),sub_self]

private theorem base_derivatives_zero (y : ℝ) (hy : y < 2 ∨ 3 < y) :
    deriv baseCuspCutoff y = 0 ∧ deriv (deriv baseCuspCutoff) y = 0 := by
  have he : ∃ c : ℝ, baseCuspCutoff =ᶠ[𝓝 y] fun _ => c := by
    rcases hy with hy | hy
    · refine ⟨1,?_⟩
      filter_upwards [gt_mem_nhds hy] with z hz
      exact baseCuspCutoff_low z hz.le
    · refine ⟨0,?_⟩
      filter_upwards [lt_mem_nhds hy] with z hz
      exact baseCuspCutoff_high z hz.le
  obtain ⟨c,hc⟩ := he
  constructor
  · rw [hc.deriv_eq,deriv_const]
  · have hd : deriv baseCuspCutoff =ᶠ[𝓝 y] fun _ => (0:ℝ) :=
      hc.deriv.trans (Filter.Eventually.of_forall (fun z => deriv_const z c))
    rw [hd.deriv_eq,deriv_const]

theorem scaledCuspCutoff_smooth (N : ℝ) : ContDiff ℝ ∞ (scaledCuspCutoff N) :=
  baseCuspCutoff_smooth.comp (contDiff_id.div_const N)

theorem scaledCuspCutoff_low (N y : ℝ) (hN : 0 < N) (hy : y ≤ 2*N) :
    scaledCuspCutoff N y = 1 :=
  baseCuspCutoff_low _ ((div_le_iff₀ hN).mpr hy)

theorem scaledCuspCutoff_high (N y : ℝ) (hN : 0 < N) (hy : 3*N ≤ y) :
    scaledCuspCutoff N y = 0 :=
  baseCuspCutoff_high _ ((le_div_iff₀ hN).mpr hy)

theorem scaledCuspCutoff_deriv (N y : ℝ) :
    deriv (scaledCuspCutoff N) y = deriv baseCuspCutoff (y/N)/N := by
  have h := (baseCuspCutoff_smooth.differentiable (by simp)).differentiableAt.hasDerivAt
    (x := y/N)
  have hh : HasDerivAt (scaledCuspCutoff N) (deriv baseCuspCutoff (y/N)*(1/N)) y :=
    h.comp y ((hasDerivAt_id y).div_const N)
  rw [hh.deriv]
  ring

theorem scaledCuspCutoff_second (N y : ℝ) :
    deriv (deriv (scaledCuspCutoff N)) y = deriv (deriv baseCuspCutoff) (y/N)/N^(2 : ℕ) := by
  have hd := (contDiff_infty_iff_deriv.mp baseCuspCutoff_smooth).2
  have h := (hd.differentiable (by simp)).differentiableAt.hasDerivAt (x := y/N)
  rw [show deriv (scaledCuspCutoff N) = fun z => deriv baseCuspCutoff (z/N)/N by
    funext z; exact scaledCuspCutoff_deriv N z]
  have hh : HasDerivAt (fun z => deriv baseCuspCutoff (z/N)/N)
      (deriv (deriv baseCuspCutoff) (y/N)*(1/N)/N) y := by
    simpa only [Function.comp_def,id_eq] using
      (h.comp y ((hasDerivAt_id y).div_const N)).div_const N
  rw [hh.deriv]
  ring

/-- Both hyperbolic cutoff derivatives have a common bound independent of the cusp scale. -/
theorem scaledCuspCutoff_derivative_bounds : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (N y : ℝ),
      |y*deriv (scaledCuspCutoff N) y| ≤ C ∧
      |y^(2 : ℕ)*deriv (deriv (scaledCuspCutoff N)) y| ≤ C := by
  have hd := (contDiff_infty_iff_deriv.mp baseCuspCutoff_smooth).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_id.mul hd.continuous).continuousOn (s := Icc (2:ℝ) 3)
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_id.pow 2).mul hdd.continuous).continuousOn (s := Icc (2:ℝ) 3)
  let C := max 0 (max A B)
  have hc : 0 ≤ C := le_max_left _ _
  have hb (x : ℝ) : |x*deriv baseCuspCutoff x| ≤ C ∧
      |x^(2 : ℕ)*deriv (deriv baseCuspCutoff) x| ≤ C := by
    by_cases hx : x ∈ Icc (2:ℝ) 3
    · exact ⟨(hA x hx).trans ((le_max_left A B).trans (le_max_right 0 _)),
        (hB x hx).trans ((le_max_right A B).trans (le_max_right 0 _))⟩
    · have hz := base_derivatives_zero x (by simpa only [mem_Icc,not_and_or,not_le] using hx)
      simpa only [hz.1,hz.2,mul_zero,abs_zero] using And.intro hc hc
  refine ⟨C,hc,?_⟩
  intro N y
  rw [scaledCuspCutoff_deriv,scaledCuspCutoff_second]
  rw [show y*(deriv baseCuspCutoff (y/N)/N) = (y/N)*deriv baseCuspCutoff (y/N) by ring,
    show y^(2 : ℕ)*(deriv (deriv baseCuspCutoff) (y/N)/N^(2 : ℕ)) =
      (y/N)^(2 : ℕ)*deriv (deriv baseCuspCutoff) (y/N) by ring]
  exact hb (y/N)

end
end RHTower.D4BMJointWave
