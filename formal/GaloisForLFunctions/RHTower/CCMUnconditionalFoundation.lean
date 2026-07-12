/-
# Unconditional CCM route foundation

This module gathers the three unconditional mechanisms used by the current
Connes--Consani--Moscovici route:

* finite diagonal-Fock defect/passivity and source incidence;
* bilateral polarization of an off-line quartet resolvent;
* exact Sonin resolvent dressing of the boundary commutator.

It also states the cofinal finite-section law.  The remaining RH-bearing input
is now a single named predicate: source-resolved passivity at every finite
section for the actual Euler/boundary/Mellin incidence.  Nothing in this file
asserts that predicate for zeta.
-/
import GaloisForLFunctions.RHTower.CCMFiniteFockPassivity
import GaloisForLFunctions.RHTower.CCMQuartetResolventPolarization
import GaloisForLFunctions.RHTower.CCMSoninResolventCommutator
import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz
import GaloisForLFunctions.HTGeometry.PrimeLogCauchySeamRank
import GaloisForLFunctions.RHTower.GammaDampedPrimeLogCauchyDomain
import GaloisForLFunctions.RHTower.PolarPrimeMellinDefect
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt
import GaloisForLFunctions.RHTower.XiThetaSquareRateLaplace

namespace RHTower

noncomputable section

/-- Cofinal source-resolved passivity for a family of finite CCM sections. -/
def CCMCofinalSourceResolvedPassivity
    (A E B M : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ n, CCMSourceResolvedPassivity (A n) (E n) (B n) (M n)

/-- Cofinal contractivity of the finite diagonal-Fock lifts. -/
def CCMCofinalFiniteFockPassivity
    (A C : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ n, CCMFiniteFockPassivity (A n) (C n)

/-- Exact cofinal algebraic reduction from source incidence to diagonal-Fock
contractivity. -/
theorem ccmCofinalFiniteFockPassivity_iff_sourceResolved
    (A C E B M : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ n, C n = E n - B n + M n) :
    CCMCofinalFiniteFockPassivity A C ↔
      CCMCofinalSourceResolvedPassivity A E B M := by
  unfold CCMCofinalFiniteFockPassivity CCMCofinalSourceResolvedPassivity
  apply forall_congr'
  intro n
  exact ccmFiniteFockPassivity_iff_sourceResolved
    (A n) (C n) (E n) (B n) (M n) (hC n)

/-- Exact cofinal defect law.  Under the incidence identity, positivity of every
finite diagonal-Fock defect is equivalent to the one remaining cofinal
source-resolved passivity assertion. -/
theorem ccmCofinalDefect_kreinNonneg_iff_sourceResolved
    (A C E B M : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ n, C n = E n - B n + M n) :
    (∀ n, KreinNonneg (ccmDiagonalDefectGram (A n) (C n))) ↔
      CCMCofinalSourceResolvedPassivity A E B M := by
  unfold CCMCofinalSourceResolvedPassivity
  apply forall_congr'
  intro n
  exact ccmDiagonalDefect_kreinNonneg_iff_sourceResolved
    (A n) (C n) (E n) (B n) (M n) (hC n)

end

end RHTower
