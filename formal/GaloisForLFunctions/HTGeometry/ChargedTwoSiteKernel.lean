import GaloisForLFunctions.HTGeometry.ChargedTwoSitePencil

/-! # Exact nonzero modes and determinant of the charged two-site wave equation -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Scalar determinant of the actual two-site wave residual. -/
def chargedTwoSiteDeterminant (k m c d : ℝ) (ω : ℂ) : ℂ :=
  (((chargedTwoSiteBase k m : ℝ) : ℂ) - (ω - ((c + d : ℝ) : ℂ)) ^ 2) *
    (((chargedTwoSiteBase k m : ℝ) : ℂ) - (ω - ((c - d : ℝ) : ℂ)) ^ 2) - (Real.exp k : ℂ) ^ 2

/-- A canonical candidate whose first component never vanishes. -/
def chargedTwoSiteModeVector (k m c d : ℝ) (ω : ℂ) : ℂ × ℂ :=
  ((Real.exp k : ℂ), ((chargedTwoSiteBase k m : ℝ) : ℂ) - (ω - ((c + d : ℝ) : ℂ)) ^ 2)

/-- Actual mode existence, with a nonzero state required explicitly. -/
def ChargedTwoSiteHasMode (k m c d : ℝ) (ω : ℂ) : Prop :=
  ∃ v : ℂ × ℂ, v ≠ 0 ∧ chargedTwoSitePencil k m c d ω v = 0

/-- The canonical candidate is a nonzero state at every frequency, without a spectral assumption. -/
theorem chargedTwoSiteModeVector_ne_zero (k m c d : ℝ) (ω : ℂ) :
    chargedTwoSiteModeVector k m c d ω ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : ℂ × ℂ => v.1.re) h
  change Real.exp k = 0 at h0
  exact (Real.exp_pos k).ne' h0

/-- The actual residual of the canonical candidate is exactly its scalar determinant in the second component. -/
theorem chargedTwoSiteModeVector_residual (k m c d : ℝ) (ω : ℂ) :
    chargedTwoSitePencil k m c d ω (chargedTwoSiteModeVector k m c d ω) =
      (0, chargedTwoSiteDeterminant k m c d ω) := by
  rw [chargedTwoSitePencil_apply]
  unfold chargedTwoSiteModeVector chargedTwoSiteDeterminant
  ext <;> dsimp <;> ring

/-- Determinant zeros are equivalent to actual nonzero modes, with an explicit witness in the reverse direction. -/
theorem chargedTwoSiteHasMode_iff_determinant (k m c d : ℝ) (ω : ℂ) :
    ChargedTwoSiteHasMode k m c d ω ↔ chargedTwoSiteDeterminant k m c d ω = 0 := by
  constructor
  · rintro ⟨v, hv, hP⟩
    rw [chargedTwoSitePencil_apply] at hP
    have h0 := congrArg Prod.fst hP
    have h1 := congrArg Prod.snd hP
    dsimp at h0 h1
    have hc : (Real.exp k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos k).ne'
    have hv0 : v.1 ≠ 0 := by
      intro hz
      have hprod : (Real.exp k : ℂ) * v.2 = 0 := by
        rw [hz, mul_zero] at h0
        linear_combination -h0
      have hz2 : v.2 = 0 := (mul_eq_zero.mp hprod).resolve_left hc
      exact hv (Prod.ext hz hz2)
    have hd : chargedTwoSiteDeterminant k m c d ω * v.1 = 0 := by
      unfold chargedTwoSiteDeterminant
      linear_combination
        (((chargedTwoSiteBase k m : ℝ) : ℂ) - (ω - ((c - d : ℝ) : ℂ)) ^ 2) * h0 +
          (Real.exp k : ℂ) * h1
    exact (mul_eq_zero.mp hd).resolve_right hv0
  · intro hd
    refine ⟨chargedTwoSiteModeVector k m c d ω, chargedTwoSiteModeVector_ne_zero k m c d ω, ?_⟩
    rw [chargedTwoSiteModeVector_residual, hd]
    rfl

/-- Centering at the mean electrostatic frequency makes the determinant an even quartic. -/
theorem chargedTwoSiteDeterminant_centered_square (k m c d : ℝ) (ω : ℂ) :
    chargedTwoSiteDeterminant k m c d ω =
      ((ω - (c : ℂ)) ^ 2 - ((chargedTwoSiteBase k m + d ^ 2 : ℝ) : ℂ)) ^ 2 -
        (((Real.exp k) ^ 2 + 4 * chargedTwoSiteBase k m * d ^ 2 : ℝ) : ℂ) := by
  unfold chargedTwoSiteDeterminant
  push_cast
  ring

/-- The centered quadratic discriminant is strictly positive even at zero charge and zero mass. -/
theorem chargedTwoSiteDiscriminant_pos (k m d : ℝ) :
    0 < (Real.exp k) ^ 2 + 4 * chargedTwoSiteBase k m * d ^ 2 := by
  have h := mul_nonneg (chargedTwoSiteBase_pos k m).le (sq_nonneg d)
  nlinarith [sq_pos_of_pos (Real.exp_pos k)]

end
end GaloisForLFunctions.HTGeometry
