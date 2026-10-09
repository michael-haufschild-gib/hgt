import GaloisForLFunctions.HTGeometry.ProjectiveWignerSmithTomography
import GaloisForLFunctions.HTGeometry.ConformalClockSpeciesMixing

/-!
# Mixed clock scale recovery by projective matrix observations

A complete mixed potential has the form `s • M + d • 1`, where the known mass
matrix is `M`, scale is `s`, and the common scalar defect is `d`. Projective
normalization removes the defect. The resulting observations determine scale
exactly when the mass matrix is nonscalar, without any diagonalization assumption.

For a real symmetric two-channel source, the diagonal contrast and off-diagonal
entry give a direct formula with denominator equal to the squared spectral gap.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Projective reference normalization commutes with scalar multiplication. -/
theorem projectiveDelayNormalize_smul {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s : ℂ) :
    projectiveDelayNormalize (s • M) = s • projectiveDelayNormalize M := by
  ext i j
  by_cases hij : i = j <;> simp [projectiveDelayNormalize, hij, mul_sub]

/-- The projective normalization of a mixed clock potential is scale times the
projective mass matrix; the entire common scalar defect cancels. -/
theorem projectiveDelayNormalize_mixedClock {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s d : ℂ) :
    projectiveDelayNormalize (s • M + d • 1) = s • projectiveDelayNormalize M := by
  rw [projectiveDelayNormalize_add_scalar, projectiveDelayNormalize_smul]

/-- The projective mass matrix vanishes exactly for scalar mass matrices. -/
theorem projectiveDelayNormalize_eq_zero_iff_scalar {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    projectiveDelayNormalize M = 0 ↔ ∃ c : ℂ, M = c • 1 := by
  constructor
  · intro h
    refine ⟨M (Fin.last n) (Fin.last n), ?_⟩
    ext i j
    have hij := congrFun (congrFun h i) j
    by_cases heq : i = j
    · subst j
      have hi : M i i - M (Fin.last n) (Fin.last n) = 0 := by
        simpa [projectiveDelayNormalize] using hij
      simpa using sub_eq_zero.mp hi
    · simpa [projectiveDelayNormalize, heq] using hij
  · rintro ⟨c, rfl⟩
    ext i j
    by_cases hij : i = j <;> simp [projectiveDelayNormalize, hij]

/-- Complete projective observations of mixed clock potentials agree exactly
when their scales agree or the known mass matrix is scalar. -/
theorem projectiveDelayPanel_mixedClock_eq_iff {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s₁ d₁ s₂ d₂ : ℂ) :
    projectiveDelayPanel (s₁ • M + d₁ • 1) =
        projectiveDelayPanel (s₂ • M + d₂ • 1) ↔
      s₁ = s₂ ∨ ∃ c : ℂ, M = c • 1 := by
  constructor
  · intro h
    have hn := projectiveDelayPanel_eq_imp_normalize_eq h
    rw [projectiveDelayNormalize_mixedClock, projectiveDelayNormalize_mixedClock] at hn
    by_cases hs : s₁ = s₂
    · exact Or.inl hs
    · right
      apply (projectiveDelayNormalize_eq_zero_iff_scalar M).mp
      ext i j
      have hij : s₁ * projectiveDelayNormalize M i j =
          s₂ * projectiveDelayNormalize M i j := congrFun (congrFun hn i) j
      have hzero : (s₁ - s₂) * projectiveDelayNormalize M i j = 0 := by
        linear_combination hij
      exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hs)
  · rintro (hs | hscalar)
    · rw [hs, projectiveDelayPanel_add_scalar, projectiveDelayPanel_add_scalar]
    · have hz := (projectiveDelayNormalize_eq_zero_iff_scalar M).mpr hscalar
      funext p
      simp only [projectiveDelayPanel, projectiveDelayNormalize_mixedClock, hz, smul_zero]

/-- The exact scale-identifiability condition from the existing projective
reporter panel is nonscalarity of the known mass matrix. -/
theorem mixedClock_scale_identifiable_iff {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (∀ s₁ d₁ s₂ d₂ : ℂ,
      projectiveDelayPanel (s₁ • M + d₁ • 1) =
        projectiveDelayPanel (s₂ • M + d₂ • 1) → s₁ = s₂) ↔
      ¬ ∃ c : ℂ, M = c • 1 := by
  constructor
  · intro h hscalar
    exact zero_ne_one (h 0 0 1 0
      ((projectiveDelayPanel_mixedClock_eq_iff M 0 0 1 0).mpr (Or.inr hscalar)))
  · intro h s₁ d₁ s₂ d₂ hpanel
    exact ((projectiveDelayPanel_mixedClock_eq_iff M s₁ d₁ s₂ d₂).mp hpanel).resolve_right h

/-- The full diagonal/off-diagonal reporter contrast equals scale times the
squared mass gap; no eigenstate transformation is required. -/
theorem conformalMixedClock_reporter_contrast
    (weight a b d scale defectLaplace defectGradient : ℝ) :
    (a - d) *
        (conformalPotentialData weight a scale defectLaplace defectGradient -
          conformalPotentialData weight d scale defectLaplace defectGradient) +
      4 * b * (scale * b) = scale * massMixingGap a b d ^ 2 := by
  rw [conformalPotentialData_difference, sq_massMixingGap]
  ring

/-- Direct reconstruction from the complete symmetric two-channel potential.
The only exceptional case is a scalar mass matrix, where the contrast vanishes. -/
theorem conformalMixedClock_reporter_recovery
    (weight a b d scale defectLaplace defectGradient : ℝ) :
    ((a - d) *
        (conformalPotentialData weight a scale defectLaplace defectGradient -
          conformalPotentialData weight d scale defectLaplace defectGradient) +
      4 * b * (scale * b)) / massMixingGap a b d ^ 2 =
      if a = d ∧ b = 0 then 0 else scale := by
  rw [conformalMixedClock_reporter_contrast, sq_massMixingGap]
  by_cases h : a = d ∧ b = 0
  · simp [h.1, h.2]
  · rw [if_neg h]
    have hden : (a - d) ^ 2 + 4 * b ^ 2 ≠ 0 := by
      intro heq
      have had : a = d := by nlinarith [sq_nonneg (a - d), sq_nonneg b]
      have hb : b = 0 := by nlinarith [sq_nonneg (a - d), sq_nonneg b]
      exact h ⟨had, hb⟩
    exact mul_div_cancel_right₀ scale hden

end GaloisForLFunctions.HTGeometry
