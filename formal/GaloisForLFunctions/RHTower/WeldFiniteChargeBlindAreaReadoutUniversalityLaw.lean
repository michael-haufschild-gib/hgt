import GaloisForLFunctions.RHTower.WeldChargeFaithfulness
import GaloisForLFunctions.RHTower.WeldPolarizationDirection

/-!
# Weld finite-charge blindness versus faithful area readout

Every finite-valued additive charge annihilates the real weld-class line, but the same line has one
canonical faithful scalar readout: evaluate its alternating area form on the ordered plane basis.
Thus all bounded finite observers collapse the flux coordinate while one continuous oriented-plane
observer recovers it completely.

No prime specialization, Riemann-hypothesis premise, or noncanonical complex structure occurs.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Every finite-valued charge kills every point of the weld-class line. -/
theorem weldClassLine_finiteCharge_invisible
    {M : Type*} [AddCommGroup M] [Fintype M] [Nonempty M]
    (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ M)
    (c : WeldClassLine) :
    φ c.1 = 0 := by
  rcases c with ⟨c, ⟨θ, hθ⟩⟩
  change φ c = 0
  rw [← hθ]
  exact weldClass_finite_charge_invisible φ θ

/-- Scalar oriented-area coordinate of a weld-line class. -/
def weldClassAreaReadout (c : WeldClassLine) : ℝ :=
  weldClassLineToArea c (1, 0) (0, 1)

/-- The canonical area readout returns the original conversion coordinate. -/
theorem weldClassAreaReadout_rangeRestrict (θ : ℝ) :
    weldClassAreaReadout (weldClassHom.rangeRestrict θ) = θ := by
  rw [weldClassAreaReadout, weldClassLineToArea_apply]
  simp [weldAreaForm]

/-- One scalar area evaluation is faithful on the complete weld-class line. -/
theorem weldClassAreaReadout_injective :
    Function.Injective weldClassAreaReadout := by
  intro c d h
  apply weldClassLineToArea_injective
  apply LinearMap.BilinForm.ext
  intro x y
  obtain ⟨θ, hθ⟩ := c.2
  obtain ⟨η, hη⟩ := d.2
  have hc : c = weldClassHom.rangeRestrict θ := by
    apply Subtype.ext
    exact hθ.symm
  have hd : d = weldClassHom.rangeRestrict η := by
    apply Subtype.ext
    exact hη.symm
  rw [hc, hd, weldClassLineToArea_apply, weldClassLineToArea_apply]
  have hθη : θ = η := by
    rw [hc, hd, weldClassAreaReadout_rangeRestrict,
      weldClassAreaReadout_rangeRestrict] at h
    exact h
  rw [hθη]

/-- **Weld finite-charge-blind area-readout universality.** Every finite charge collapses the
selected class, while equality of canonical scalar area readouts exactly classifies weld classes. -/
theorem weld_finiteChargeBlind_areaReadoutUniversality
    {M : Type*} [AddCommGroup M] [Fintype M] [Nonempty M]
    (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ M)
    (c d : WeldClassLine) :
    φ c.1 = 0 ∧
      (weldClassAreaReadout c = weldClassAreaReadout d ↔ c = d) := by
  refine ⟨weldClassLine_finiteCharge_invisible φ c, ?_⟩
  exact Function.Injective.eq_iff weldClassAreaReadout_injective

end

end GaloisForLFunctions.RHTower
