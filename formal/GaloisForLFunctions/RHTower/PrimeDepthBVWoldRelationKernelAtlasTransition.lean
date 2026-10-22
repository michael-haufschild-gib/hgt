import GaloisForLFunctions.RHTower.PrimeDepthBVWoldSourceDaggerAtlasTransition
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerRelationKernelBoundarySeparation

/-!
# BV-Wold / relation-kernel atlas transition

The source-pointed Calderón--Witt relation-kernel calibrator is vector-valued,
nonzero, and coefficient-faithful.  This file determines its relation to the
scalar BV--Wold anomaly exactly.  The anomaly logarithm is the completed Green
fracture times a positive prime/depth source scale, and the Green-scaled
relation-kernel ray is the corresponding logarithmic anomaly ray.

Consequently target dimension and nondegeneracy do not increase atlas rank:
the relation-kernel carrier has the same zero radical as the scalar anomaly.
A successful merged route still needs an independent arithmetic vanishing
law on that carrier.  All statements are unconditional.
-/

open Complex

namespace RHTower

noncomputable section

/-- Positive logarithmic scale converting the horizontal Green fracture
to the Wold anomaly at prime `p` and depth `e`. -/
def primeDepthBVWoldPrimeConsecutiveTriangleLogScale
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  (1 - ((p.1 : ℝ)⁻¹)) ^ (3 : ℕ) * ((p.1 : ℝ)⁻¹) ^ e *
    Real.log (p.1 : ℝ)

theorem primeDepthBVWoldPrimeConsecutiveTriangleLogScale_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < primeDepthBVWoldPrimeConsecutiveTriangleLogScale p e := by
  rw [primeDepthBVWoldPrimeConsecutiveTriangleLogScale]
  have hp1 : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
  have hb : 0 < 1 - ((p.1 : ℝ)⁻¹) :=
    sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)
  have hlog : 0 < Real.log (p.1 : ℝ) := Real.log_pos hp1
  positivity

/-- Logarithm linearizes the BV--Wold anomaly to the centered horizontal
rate with a positive source scale. -/
theorem log_primeDepthBVWoldPrimeConsecutiveTriangleAnomaly
    (s : ℂ) (p : Nat.Primes) (e : ℕ) :
    Real.log (primeDepthBVWoldPrimeConsecutiveTriangleAnomaly
        (2 * s.re - 1) p e) =
      (2 * s.re - 1) *
        primeDepthBVWoldPrimeConsecutiveTriangleLogScale p e := by
  rw [primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq,
    Real.log_exp, primeDepthBVWoldPrimeConsecutiveTriangleLogScale]
  ring

/-- Complex Green-fracture coefficient is the logarithmic anomaly
coordinate divided only by a fixed positive source scale. -/
theorem log_primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq_greenFracture
    (s : ℂ) (p : Nat.Primes) (e : ℕ) :
    ((Real.log (primeDepthBVWoldPrimeConsecutiveTriangleAnomaly
        (2 * s.re - 1) p e) : ℝ) : ℂ) =
      xiNearbyPoleDualityAdjunctionFracture s *
        (primeDepthBVWoldPrimeConsecutiveTriangleLogScale p e : ℂ) := by
  rw [log_primeDepthBVWoldPrimeConsecutiveTriangleAnomaly,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  push_cast
  ring

/-- Relation-kernel Green ray is exactly the logarithmic BV--Wold anomaly
ray after multiplication by its positive source scale. -/
theorem primeDepthBVWold_logAnomaly_sourcePointedTau_transition
    (s : ℂ) (p : Nat.Primes) (e : ℕ) :
    (primeDepthBVWoldPrimeConsecutiveTriangleLogScale p e : ℂ) •
        (xiNearbyPoleDualityAdjunctionFracture s •
          deningerCalderonWittSourcePointedTau p) =
      (Real.log (primeDepthBVWoldPrimeConsecutiveTriangleAnomaly
        (2 * s.re - 1) p e) : ℂ) •
          deningerCalderonWittSourcePointedTau p := by
  rw [smul_smul]
  congr 1
  rw [log_primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq_greenFracture]
  ring

/-- Vector-valued relation-kernel calibration is coefficient-faithful but
has the same zero radical as every scalar anomaly chart. -/
theorem deningerCalderonWittSourcePointedGreenRay_eq_zero_iff_anomaly_eq_one
    (s : ℂ) (p : Nat.Primes) (e : ℕ) :
    xiNearbyPoleDualityAdjunctionFracture s •
          deningerCalderonWittSourcePointedTau p = 0 ↔
      primeDepthBVWoldPrimeConsecutiveTriangleAnomaly
          (2 * s.re - 1) p e = 1 := by
  constructor
  · intro hzero
    have hfracture : xiNearbyPoleDualityAdjunctionFracture s = 0 :=
      (smul_eq_zero.mp hzero).resolve_right
        (deningerCalderonWittSourcePointedTau_ne_zero p)
    have hline :=
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff s).mp hfracture
    exact
      (primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq_one_iff_re_eq_half
        s p e).2 hline
  · intro hanomaly
    have hline :=
      (primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq_one_iff_re_eq_half
        s p e).1 hanomaly
    rw [(xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff s).2 hline,
      zero_smul]

end

end RHTower
