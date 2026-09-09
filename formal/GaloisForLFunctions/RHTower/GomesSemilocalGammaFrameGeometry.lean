import GaloisForLFunctions.HTGeometry.GomesCanonicalMomentGeometry
import GaloisForLFunctions.RHTower.CompletedPrimeGammaHankelFarRightAnchor
import GaloisForLFunctions.RHTower.SemilocalJacobiLinearGrowthProlateDomainGate
import Mathlib.NumberTheory.PrimeCounting

/-!
Concrete corpus applications of the internal-frame and tensor-observation viewpoint in
Gomes, arXiv:2404.10461 and arXiv:2509.25276v7. Source equality is proved before
transferring the geometry. These are applications, not numbered paper transcriptions.
-/
open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.RHTower
open _root_.HTGeometry
open GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- The canonical frame model of this concrete corpus source. -/
def gomesCompletedGammaModel : GomesMomentModel := gomesCanonicalMomentModel (completedPrimeGammaFarRightMoment)

/-- Exact source identification, retaining its original mass. -/
theorem gomesCompletedGammaModel_moments :
    (gomesCompletedGammaModel).moments = (completedPrimeGammaFarRightMoment) := by
  apply (gomesCanonicalMomentModel_moments_iff _).mpr
  exact completedPrimeGammaFarRightMoment_positiveMomentForm

/-- The actual source polynomials strictly increase distance from the real axis at every higher quotient. -/
theorem gomesCompletedGamma_quotient_height (n : ℕ) (z : ℂ) :
    |z.im| < |(monicOrthoC (completedPrimeGammaFarRightMoment) ((n+1)+1) z /
      monicOrthoC (completedPrimeGammaFarRightMoment) (n+1) z).im| ↔ z.im ≠ 0 := by
  simpa only [gomesMomentQuotient,gomesCompletedGammaModel_moments] using
    gomesMomentQuotient_succ_abs_im_gt_iff (gomesCompletedGammaModel) n z

/-- The normalized flux detects the upper half-plane and the exact observation-depth threshold. -/
theorem gomesCompletedGamma_flux_signature (n : ℕ) (z : ℂ) :
    (gomesMomentNormalizedFlux (gomesCompletedGammaModel) n z).PosDef ↔ 0 < z.im ∧ n ≠ 0 :=
  gomesMomentNormalizedFlux_posDef_iff (gomesCompletedGammaModel) n z

/-- A single fixed tensor entry measures the reciprocal mass of the original source. -/
theorem gomesCompletedGamma_mass_probe :
    gomesMomentNormalizedFlux (gomesCompletedGammaModel) 0 Complex.I 0 0 = ((2/(completedPrimeGammaFarRightMoment) 0 : ℝ) : ℂ) := by
  rw [gomesMomentNormalizedFlux_mass_probe,gomesCompletedGammaModel_moments]

/-- The canonical frame model of this concrete corpus source. -/
def gomesArchGammaModel : GomesMomentModel := gomesCanonicalMomentModel (ccmMetaplecticGammaMoment)

/-- Exact source identification, retaining its original mass. -/
theorem gomesArchGammaModel_moments :
    (gomesArchGammaModel).moments = (ccmMetaplecticGammaMoment) := by
  apply (gomesCanonicalMomentModel_moments_iff _).mpr
  exact positiveMomentForm_ccmMetaplecticGammaMoment

/-- The actual source polynomials strictly increase distance from the real axis at every higher quotient. -/
theorem gomesArchGamma_quotient_height (n : ℕ) (z : ℂ) :
    |z.im| < |(monicOrthoC (ccmMetaplecticGammaMoment) ((n+1)+1) z /
      monicOrthoC (ccmMetaplecticGammaMoment) (n+1) z).im| ↔ z.im ≠ 0 := by
  simpa only [gomesMomentQuotient,gomesArchGammaModel_moments] using
    gomesMomentQuotient_succ_abs_im_gt_iff (gomesArchGammaModel) n z

/-- The normalized flux detects the upper half-plane and the exact observation-depth threshold. -/
theorem gomesArchGamma_flux_signature (n : ℕ) (z : ℂ) :
    (gomesMomentNormalizedFlux (gomesArchGammaModel) n z).PosDef ↔ 0 < z.im ∧ n ≠ 0 :=
  gomesMomentNormalizedFlux_posDef_iff (gomesArchGammaModel) n z

/-- A single fixed tensor entry measures the reciprocal mass of the original source. -/
theorem gomesArchGamma_mass_probe :
    gomesMomentNormalizedFlux (gomesArchGammaModel) 0 Complex.I 0 0 = ((2/(ccmMetaplecticGammaMoment) 0 : ℝ) : ℂ) := by
  rw [gomesMomentNormalizedFlux_mass_probe,gomesArchGammaModel_moments]

/-- The canonical frame model of this concrete corpus source. -/
def gomesFinitePrimeCyclicModel {d : ℕ} (k : Fin d → ℕ) : GomesMomentModel := gomesCanonicalMomentModel (semilocalFinitePrimeCyclicMoment (fun i => Nat.nth Nat.Prime (k i)))

/-- Exact source identification, retaining its original mass. -/
theorem gomesFinitePrimeCyclicModel_moments {d : ℕ} (k : Fin d → ℕ) :
    (gomesFinitePrimeCyclicModel k).moments = (semilocalFinitePrimeCyclicMoment (fun i => Nat.nth Nat.Prime (k i))) := by
  apply (gomesCanonicalMomentModel_moments_iff _).mpr
  exact positiveMomentForm_semilocalFinitePrimeCyclicMoment _ (fun i => Nat.prime_nth_prime (k i))

/-- The actual source polynomials strictly increase distance from the real axis at every higher quotient. -/
theorem gomesFinitePrimeCyclic_quotient_height {d : ℕ} (k : Fin d → ℕ) (n : ℕ) (z : ℂ) :
    |z.im| < |(monicOrthoC (semilocalFinitePrimeCyclicMoment (fun i => Nat.nth Nat.Prime (k i))) ((n+1)+1) z /
      monicOrthoC (semilocalFinitePrimeCyclicMoment (fun i => Nat.nth Nat.Prime (k i))) (n+1) z).im| ↔ z.im ≠ 0 := by
  simpa only [gomesMomentQuotient,gomesFinitePrimeCyclicModel_moments] using
    gomesMomentQuotient_succ_abs_im_gt_iff (gomesFinitePrimeCyclicModel k) n z

/-- The normalized flux detects the upper half-plane and the exact observation-depth threshold. -/
theorem gomesFinitePrimeCyclic_flux_signature {d : ℕ} (k : Fin d → ℕ) (n : ℕ) (z : ℂ) :
    (gomesMomentNormalizedFlux (gomesFinitePrimeCyclicModel k) n z).PosDef ↔ 0 < z.im ∧ n ≠ 0 :=
  gomesMomentNormalizedFlux_posDef_iff (gomesFinitePrimeCyclicModel k) n z

/-- A single fixed tensor entry measures the reciprocal mass of the original source. -/
theorem gomesFinitePrimeCyclic_mass_probe {d : ℕ} (k : Fin d → ℕ) :
    gomesMomentNormalizedFlux (gomesFinitePrimeCyclicModel k) 0 Complex.I 0 0 = ((2/(semilocalFinitePrimeCyclicMoment (fun i => Nat.nth Nat.Prime (k i))) 0 : ℝ) : ℂ) := by
  rw [gomesMomentNormalizedFlux_mass_probe,gomesFinitePrimeCyclicModel_moments]

end GaloisForLFunctions.RHTower
