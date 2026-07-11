import GaloisForLFunctions.RHTower.SlepianBandCommutation
import GaloisForLFunctions.RHTower.ProlateWronskian

/-!
# Diagonalization of the band transform on prolate eigenfunctions

A prolate ODE eigenfunction spans an invariant line of the time–band transform: combining the
commuting theorem (the transform of a `χ`-eigenfunction is again a `χ`-eigenfunction) with the
conserved-Wronskian mechanism (bounded same-eigenvalue solutions are first-order proportional
inside the band) forces

`∃ μ, T̃ψ = μ·ψ` on every compact subinterval of the band where `ψ` does not vanish
(`bandTransform_eigen_smul_on`).

The scalar `μ` is the concentration eigenvalue of the time–band problem attached to the ODE
eigenfunction `ψ` — the object whose large-bandwidth asymptotics the fixed-index eigenvalue
laws describe.  No boundedness hypotheses are needed: `ψ`, `T̃ψ` and their derivatives are
continuous, hence automatically bounded on the closed band half `[0,1]`, which is all the
Wronskian squeeze uses.
-/

open Filter

namespace RHTower

/-- The band transform of a `C¹` input is everywhere differentiable. -/
theorem differentiable_bandTransform (c : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    Differentiable ℝ (bandTransform c ψ) :=
  fun x => (hasDerivAt_bandTransform c hψ x).differentiableAt

theorem differentiable_deriv_bandTransform (c : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    Differentiable ℝ (deriv (bandTransform c ψ)) := by
  rw [deriv_bandTransform c hψ]
  exact fun x => (hasDerivAt_bandTranslationTransform (differentiable_deriv_sincSmooth c)
    (continuous_deriv2_sincSmooth c) hψ x).differentiableAt

/-- **The band transform is scalar on prolate eigenlines.**  If `ψ` is a pointwise prolate
eigenfunction, then on every compact subinterval of the band where `ψ` does not vanish the
transform acts as multiplication by a single scalar: `T̃ψ = μ·ψ` there.  The scalar is the
concentration eigenvalue attached to `ψ`. -/
theorem bandTransform_eigen_smul_on {c χ : ℝ} {ψ : ℝ → ℝ}
    (hf1 : Differentiable ℝ ψ) (hf2 : Differentiable ℝ (deriv ψ))
    (hf2c : Continuous (deriv (deriv ψ)))
    (heig : ∀ y, prolateSLAction c ψ y = χ * ψ y)
    {a b : ℝ} (hsub : Set.Icc a b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hne : ∀ y ∈ Set.Icc a b, ψ y ≠ 0) :
    ∃ μ : ℝ, ∀ y ∈ Set.Icc a b, bandTransform c ψ y = μ * ψ y := by
  have hψc : Continuous ψ := hf1.continuous
  have hT1 : Differentiable ℝ (bandTransform c ψ) := differentiable_bandTransform c hψc
  have hT2 : Differentiable ℝ (deriv (bandTransform c ψ)) :=
    differentiable_deriv_bandTransform c hψc
  have heigT : ∀ y, prolateSLAction c (bandTransform c ψ) y = χ * bandTransform c ψ y :=
    fun y => slepian_commutation_eigen c y hf1 hf2 hf2c heig
  -- automatic bounds on the closed band half
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hψc.continuousOn
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf2.continuous.continuousOn
  obtain ⟨C₃, hC₃⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hT1.continuous.continuousOn
  obtain ⟨C₄, hC₄⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hT2.continuous.continuousOn
  set C : ℝ := max (max C₁ C₂) (max C₃ C₄) with hCdef
  have hb₁ : ∀ y ∈ Set.Ico (0 : ℝ) 1, |ψ y| ≤ C ∧ |deriv ψ y| ≤ C := by
    intro y hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hy
    constructor
    · rw [← Real.norm_eq_abs]
      exact (hC₁ y hy').trans ((le_max_left C₁ C₂).trans (le_max_left _ _))
    · rw [← Real.norm_eq_abs]
      exact (hC₂ y hy').trans ((le_max_right C₁ C₂).trans (le_max_left _ _))
  have hb₂ : ∀ y ∈ Set.Ico (0 : ℝ) 1,
      |bandTransform c ψ y| ≤ C ∧ |deriv (bandTransform c ψ) y| ≤ C := by
    intro y hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hy
    constructor
    · rw [← Real.norm_eq_abs]
      exact (hC₃ y hy').trans ((le_max_left C₃ C₄).trans (le_max_right _ _))
    · rw [← Real.norm_eq_abs]
      exact (hC₄ y hy').trans ((le_max_right C₃ C₄).trans (le_max_right _ _))
  -- first-order proportionality inside the band
  have hrel : ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      ψ y * deriv (bandTransform c ψ) y = bandTransform c ψ y * deriv ψ y :=
    fun y hy => prolate_firstOrder_relation hf1 hf2 hT1 hT2 heig heigT hb₁ hb₂ hy
  -- the quotient is constant on [a,b]
  have hq : ∀ x ∈ Set.Icc a b,
      (fun y => bandTransform c ψ y / ψ y) x = (fun y => bandTransform c ψ y / ψ y) a := by
    apply constant_of_has_deriv_right_zero
    · exact (hT1.continuous.continuousOn).div (hψc.continuousOn) hne
    · intro x hx
      have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := hsub (Set.Ico_subset_Icc_self hx)
      have hψx : ψ x ≠ 0 := hne x (Set.Ico_subset_Icc_self hx)
      have hdiv := ((hT1 x).hasDerivAt).div ((hf1 x).hasDerivAt) hψx
      have hnum : deriv (bandTransform c ψ) x * ψ x - bandTransform c ψ x * deriv ψ x = 0 := by
        linear_combination hrel x hxI
      rw [hnum, zero_div] at hdiv
      exact hdiv.hasDerivWithinAt
  refine ⟨bandTransform c ψ a / ψ a, fun y hy => ?_⟩
  have hqy : bandTransform c ψ y / ψ y = bandTransform c ψ a / ψ a := hq y hy
  rw [← hqy, div_mul_cancel₀ _ (hne y hy)]

end RHTower
