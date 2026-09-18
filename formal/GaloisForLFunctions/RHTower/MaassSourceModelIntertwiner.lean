import GaloisForLFunctions.RHTower.MaassModelHilbertRepresentation

/-!
# The source-attached completed Maass intertwiner

For an exceptional quotient-\`L²\` Maass eigenform, the completed complementary-model
embedding has a canonical preimage of the actual quotient source.  Its full real \`SL(2)\`
orbit is carried exactly to the literal quotient-\`L²\` orbit.  This is only the real-place
model attachment: it asserts neither finite-place factors nor a global lift.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower
open MaassModelQuotientL2

noncomputable section

/-- The actual exceptional Maass source belongs to the completed complementary-model image. -/
theorem sourceLp_mem_range_completedModelIsometry
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1) :
    MaassQuotientL2.sourceLp N f ∈ Set.range (completedModelIsometry N lam f) := by
  simpa [integralSubgroupUnitary_one] using
    sourceLp_diagonal_mem_range_completedModelIsometry_of_abs_lt N lam f 0 (by norm_num)

/-- Canonical completed complementary-model vector whose quotient-\`L²\` image is the
actual exceptional Maass source. -/
def maassSourceModelVector
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1) :
    ComplementaryHilbert lam :=
  (completedModelRangeEquiv N lam f).symm
    ⟨MaassQuotientL2.sourceLp N f, sourceLp_mem_range_completedModelIsometry N lam f⟩

/-- Coercing the range equivalence to quotient \`L²\` is the completed model embedding. -/
theorem completedModelRangeEquiv_coe
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryHilbert lam) :
    ((completedModelRangeEquiv N lam f v :
      LinearMap.range (completedModelIsometry N lam f).toLinearMap) :
      Lp ℂ 2 (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))) =
      completedModelIsometry N lam f v := rfl

/-- The source-attached model vector maps exactly to the quotient-\`L²\` Maass source. -/
theorem completedModelIsometry_maassSourceModelVector
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1) :
    completedModelIsometry N lam f (maassSourceModelVector N lam f) =
      MaassQuotientL2.sourceLp N f := by
  let x : LinearMap.range (completedModelIsometry N lam f).toLinearMap :=
    ⟨MaassQuotientL2.sourceLp N f, sourceLp_mem_range_completedModelIsometry N lam f⟩
  have hx := (completedModelRangeEquiv N lam f).apply_symm_apply x
  change completedModelIsometry N lam f ((completedModelRangeEquiv N lam f).symm x) =
    MaassQuotientL2.sourceLp N f
  simpa only [completedModelRangeEquiv_coe] using congrArg Subtype.val hx

/-- The canonical complementary-model source vector is nonzero. -/
theorem maassSourceModelVector_ne_zero
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1) :
    maassSourceModelVector N lam f ≠ 0 := by
  intro hzero
  have himage := congrArg (MaassModelQuotientL2.completedModelIsometry N lam f) hzero
  rw [completedModelIsometry_maassSourceModelVector, map_zero] at himage
  exact MaassQuotientL2.sourceLp_ne_zero N f himage

/-- The completed complementary representation intertwines the canonical source vector with
the literal full \`SL(2,R)\` quotient orbit. -/
theorem maassSourceModelVector_orbit_intertwines
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (g : SL2R) :
    completedModelIsometry N lam f
      (completedComplementaryModelRepresentation N lam f g
        (maassSourceModelVector N lam f)) =
      integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) g
        (MaassQuotientL2.sourceLp N f) := by
  rw [← completedModelRangeEquiv_coe]
  rw [completedComplementaryModelRepresentation_intertwines]
  rw [completedModelIsometry_maassSourceModelVector]

end

end GaloisForLFunctions.RHTower
