import GaloisForLFunctions.BiarithmeticGeometry.CriticalCoefficientWienerRealization
import GaloisForLFunctions.BiarithmeticGeometry.CriticalGoldenContinuumDefect

/-!
# Continuum-dimensional unreduced defects in the one-prime coefficient space

Normalized coefficient restriction recovers the actual power-tail family.
Its classes map to the independent classes in the full golden quotient,
so they are already independent in the one-prime quotient and its closure
defect. The coefficient isometry gives the matching cardinality bound.
-/

noncomputable section
open GaloisForLFunctions.ArithmeticOrientationTheory
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The unreduced payment quotient in the actual normalized one-prime coefficient space. -/
abbrev CriticalCoefficientPaymentQuotient := CriticalCoefficientSpace ⧸ criticalCoefficientDomain

/-- Critical payment viewed as a subspace of its coefficient closure. -/
def criticalCoefficientClosurePaid : Submodule ℂ criticalCoefficientDomain.topologicalClosure :=
  criticalCoefficientDomain.comap criticalCoefficientDomain.topologicalClosure.subtype

/-- The algebraic gap between one-prime coefficient payment and its closure. -/
abbrev CriticalCoefficientClosureDefect :=
  criticalCoefficientDomain.topologicalClosure ⧸ criticalCoefficientClosurePaid

/-- Coefficient classes map to their actual full golden payment classes. -/
def criticalCoefficientQuotientToGolden :
    CriticalCoefficientPaymentQuotient →ₗ[ℂ] CriticalGoldenPaymentQuotient :=
  criticalCoefficientDomain.liftQ
    (criticalGoldenPaidSubmodule.mkQ.comp criticalCoefficientLift.toLinearMap) (by
      intro g hg
      change criticalGoldenPaidSubmodule.mkQ (criticalCoefficientLift g) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact (criticalCoefficientLift_mem_golden_paidIdeal_iff g).mpr hg)

theorem criticalCoefficientQuotientToGolden_mk (g : CriticalCoefficientSpace) :
    criticalCoefficientQuotientToGolden (criticalCoefficientDomain.mkQ g) =
      criticalGoldenPaidSubmodule.mkQ (criticalCoefficientLift g) := rfl

/-- The closure-defect quotient maps canonically into the unreduced coefficient quotient. -/
def criticalCoefficientDefectToQuotient :
    CriticalCoefficientClosureDefect →ₗ[ℂ] CriticalCoefficientPaymentQuotient :=
  criticalCoefficientClosurePaid.liftQ
    (criticalCoefficientDomain.mkQ.comp criticalCoefficientDomain.topologicalClosure.subtype) (by
      intro g hg
      change criticalCoefficientDomain.mkQ (g : CriticalCoefficientSpace) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hg)

theorem criticalCoefficientDefectToQuotient_mk (g : criticalCoefficientDomain.topologicalClosure) :
    criticalCoefficientDefectToQuotient (criticalCoefficientClosurePaid.mkQ g) =
      criticalCoefficientDomain.mkQ (g : CriticalCoefficientSpace) := rfl

/-- The normalized one-prime coefficient vector of an actual unpaid power-tail kernel. -/
def criticalPowerCoefficientVector (α : CriticalPowerExponent) : CriticalCoefficientSpace :=
  criticalNormalizedCoefficients (powerTailWiener α α.property.1)

theorem criticalCoefficientLift_powerVector (α : CriticalPowerExponent) :
    criticalCoefficientLift (criticalPowerCoefficientVector α) = powerTailWiener α α.property.1 :=
  criticalCoefficientLift_normalizedCoefficients _ (powerTailWiener_off_support α α.property.1)

theorem criticalPowerCoefficientVector_apply (α : CriticalPowerExponent) (r : ℕ) :
    criticalPowerCoefficientVector α r = (criticalPowerCoeff (α : ℝ) r : ℂ) := by
  change (powerTailWiener α α.property.1).toFn (5 ^ r) / (Real.sqrt 5 : ℂ) ^ r = _
  rw [powerTailWiener_pow]
  have hs : (Real.sqrt 5 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  field_simp [hs]

theorem criticalPowerCoefficientVector_mem_closure (α : CriticalPowerExponent) :
    criticalPowerCoefficientVector α ∈ criticalCoefficientDomain.topologicalClosure := by
  change criticalPowerCoefficientVector α ∈ closure (criticalCoefficientDomain : Set CriticalCoefficientSpace)
  rw [closure_criticalCoefficientDomain]
  change criticalTotalEvaluation (criticalPowerCoefficientVector α) = 0
  rw [criticalTotalEvaluation_apply]
  simp only [criticalPowerCoefficientVector_apply, ← Complex.ofReal_tsum,
    tsum_criticalPowerCoeff (α : ℝ) α.property.1, Complex.ofReal_zero]

/-- The power-tail class in the unreduced one-prime coefficient quotient. -/
def criticalPowerCoefficientClass (α : CriticalPowerExponent) : CriticalCoefficientPaymentQuotient :=
  criticalCoefficientDomain.mkQ (criticalPowerCoefficientVector α)

/-- The same power-tail class in the coefficient closure defect. -/
def criticalPowerCoefficientDefectClass (α : CriticalPowerExponent) : CriticalCoefficientClosureDefect :=
  criticalCoefficientClosurePaid.mkQ
    ⟨criticalPowerCoefficientVector α, criticalPowerCoefficientVector_mem_closure α⟩

/-- Independence of the actual golden classes already forces one-prime coefficient independence. -/
theorem criticalPowerCoefficientClass_linearIndependent :
    LinearIndependent ℂ criticalPowerCoefficientClass := by
  apply LinearIndependent.of_comp criticalCoefficientQuotientToGolden
  have hcomp : criticalCoefficientQuotientToGolden ∘ criticalPowerCoefficientClass =
      criticalGoldenPowerClass := by
    funext α
    change criticalCoefficientQuotientToGolden
      (criticalCoefficientDomain.mkQ (criticalPowerCoefficientVector α)) = _
    rw [criticalCoefficientQuotientToGolden_mk, criticalCoefficientLift_powerVector]
    rfl
  rw [hcomp]
  exact criticalGoldenPowerClass_linearIndependent

/-- The same independent family lies inside the coefficient closure defect. -/
theorem criticalPowerCoefficientDefectClass_linearIndependent :
    LinearIndependent ℂ criticalPowerCoefficientDefectClass := by
  apply LinearIndependent.of_comp criticalCoefficientDefectToQuotient
  have hcomp : criticalCoefficientDefectToQuotient ∘ criticalPowerCoefficientDefectClass =
      criticalPowerCoefficientClass := by
    funext α
    exact criticalCoefficientDefectToQuotient_mk
      ⟨criticalPowerCoefficientVector α, criticalPowerCoefficientVector_mem_closure α⟩
  rw [hcomp]
  exact criticalPowerCoefficientClass_linearIndependent

private theorem cardinal_criticalCoefficientSpace_le_continuum :
    Cardinal.mk CriticalCoefficientSpace ≤ Cardinal.continuum :=
  (Cardinal.mk_le_of_injective criticalCoefficientLift.injective).trans
    (WienerAlgebraAt.cardinal_le_continuum (1 / 2))

/-- The unreduced one-prime coefficient cokernel has complex Hamel dimension continuum. -/
theorem rank_criticalCoefficientPaymentQuotient_eq_continuum :
    Module.rank ℂ CriticalCoefficientPaymentQuotient = Cardinal.continuum := by
  apply le_antisymm
  · exact (rank_le_card ℂ CriticalCoefficientPaymentQuotient).trans
      ((Cardinal.mk_le_of_surjective criticalCoefficientDomain.mkQ_surjective).trans
        cardinal_criticalCoefficientSpace_le_continuum)
  · have h := criticalPowerCoefficientClass_linearIndependent.cardinal_le_rank
    change Cardinal.mk (Set.Ioo (0 : ℝ) (1 / 2)) ≤ _ at h
    rwa [Cardinal.mk_Ioo_real (by norm_num : (0 : ℝ) < 1 / 2)] at h

/-- The coefficient closure defect itself has exactly continuum complex dimensions. -/
theorem rank_criticalCoefficientClosureDefect_eq_continuum :
    Module.rank ℂ CriticalCoefficientClosureDefect = Cardinal.continuum := by
  apply le_antisymm
  · have hc : Cardinal.mk criticalCoefficientDomain.topologicalClosure ≤ Cardinal.continuum :=
      (Cardinal.mk_le_of_injective
        (Subtype.val_injective : Function.Injective
          (fun g : criticalCoefficientDomain.topologicalClosure => (g : CriticalCoefficientSpace)))).trans
        cardinal_criticalCoefficientSpace_le_continuum
    exact (rank_le_card ℂ CriticalCoefficientClosureDefect).trans
      ((Cardinal.mk_le_of_surjective criticalCoefficientClosurePaid.mkQ_surjective).trans hc)
  · have h := criticalPowerCoefficientDefectClass_linearIndependent.cardinal_le_rank
    change Cardinal.mk (Set.Ioo (0 : ℝ) (1 / 2)) ≤ _ at h
    rwa [Cardinal.mk_Ioo_real (by norm_num : (0 : ℝ) < 1 / 2)] at h

end GaloisForLFunctions.BiarithmeticGeometry

