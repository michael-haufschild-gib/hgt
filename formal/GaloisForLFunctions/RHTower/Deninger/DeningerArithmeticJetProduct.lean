import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticContinuousJets

/-!
# Global jet observation for Deninger arithmetic cohomology

All multiplicity-bounded Xi jets assemble into one continuous linear map from the compact-open
entire source to the product of local jet spaces.  The Xi differential range lies in its kernel,
and that kernel is closed.

The reverse inclusion is the exact global analytic-division conjecture.  Isolating it shows that
closed range follows from division alone; interpolation is needed later for surjectivity onto the
full jet product, not for closedness.
-/

namespace RHTower

noncomputable section

/-- Full product of multiplicity-bounded local Xi jet coordinates. -/
abbrev DeningerArithmeticJetProduct :=
  (rho : XiDivisorSupport) → DeningerArithmeticJetIndex rho → ℂ

/-- Simultaneous continuous observation of every local Xi jet. -/
def deningerCompactOpenAllJets :
    DeningerCompactOpenEntire →L[ℂ] DeningerArithmeticJetProduct :=
  ContinuousLinearMap.pi fun rho =>
    ContinuousLinearMap.pi fun k =>
      deningerCompactOpenJet (xiSpectralPointSupport rho) k

@[simp]
theorem deningerCompactOpenAllJets_apply
    (F : DeningerCompactOpenEntire)
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    deningerCompactOpenAllJets F rho k =
      iteratedDeriv k (F : ℂ → ℂ)
        (xiSpectralPointSupport rho) :=
  rfl

/-- Every compact-open Xi coboundary has all multiplicity-bounded local jets zero. -/
theorem deningerCompactOpenXiRange_le_allJets_ker :
    deningerCompactOpenXiRange ≤ deningerCompactOpenAllJets.ker := by
  rintro _ ⟨F, rfl⟩
  change deningerCompactOpenAllJets (deningerCompactOpenXiMul F) = 0
  funext rho k
  exact deningerCompactOpenJet_XiMul_eq_zero rho k.isLt F

/-- The simultaneous vanishing-jet locus is closed in the compact-open entire source. -/
theorem isClosed_deningerCompactOpenAllJets_ker :
    IsClosed
      (deningerCompactOpenAllJets.ker :
        Set DeningerCompactOpenEntire) :=
  deningerCompactOpenAllJets.isClosed_ker

/--
Exact global analytic-division conjecture: an entire source is divisible by Xi precisely when all
jets below every Xi multiplicity vanish.
-/
def DeningerArithmeticGlobalJetDivision : Prop :=
  deningerCompactOpenXiRange =
    deningerCompactOpenAllJets.ker

/-- Global analytic division immediately implies closed range of the Xi differential. -/
theorem deningerArithmeticXiRangeClosed_of_globalJetDivision
    (hdiv : DeningerArithmeticGlobalJetDivision) :
    DeningerArithmeticXiRangeClosed := by
  rw [DeningerArithmeticXiRangeClosed, hdiv]
  exact isClosed_deningerCompactOpenAllJets_ker

end

end RHTower
