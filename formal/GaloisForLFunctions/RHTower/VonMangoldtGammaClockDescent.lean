import GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona
import GaloisForLFunctions.HTGeometry.ClockDescentAnomaly
import GaloisForLFunctions.RHTower.EulerTranslationAnalyticFaithful

/-!
# The finite von Mangoldt source has the exact Gamma-clock Bianchi current

The resolved prime-power source is a finite exponential packet with logarithmic frequencies.
Its unit coefficient shift is the coordinate operation `a_n ↦ exp (-log n) a_n`; its finite
observations are raw derivative jets.  The Gamma Taylor shadow does not descend exactly from this
source operation.  This file identifies the adjacent-depth incoherence of that affine descent
anomaly with the already-constructed rank-one factorial Gamma boundary current.

The result is deliberately source-specific: it is the finite-aperture algebraic core of the
von Mangoldt/Gamma anomaly colligation.  Passing from these finite apertures to the nonnormal Euler
unit boundary, and proving the corresponding Ward Gram factorization, remain separate analytic
problems.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Coordinate translation on a resolved exponential source. -/
def finiteExponentialSourceShift {P : Type*}
    (frequency : P → ℂ) : (P → ℂ) →ₗ[ℂ] (P → ℂ) where
  toFun a p := Complex.exp (-frequency p) * a p
  map_add' _ _ := by
    funext p
    simp [mul_add]
  map_smul' _ _ := by
    funext p
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The first `N` raw derivatives of a finite resolved exponential source at `x`. -/
def finiteExponentialJetObservation {P : Type*} [Fintype P]
    (weight frequency : P → ℂ) (x : ℂ) (N : ℕ) :
    (P → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun a i := ∑ p : P, weight p * a p * (-frequency p) ^ (i : ℕ) *
    Complex.exp (-x * frequency p)
  map_add' a b := by
    funext i
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  map_smul' c a := by
    funext i
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    calc
      _ = ∑ p : P, c * (weight p * a p * (-frequency p) ^ (i : ℕ) *
          Complex.exp (-x * frequency p)) := by
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = c * ∑ p : P, weight p * a p * (-frequency p) ^ (i : ℕ) *
          Complex.exp (-x * frequency p) := by
        rw [Finset.mul_sum]

/-- Finite exponential jet observations are compatible under Gamma-clock truncation. -/
theorem finiteExponentialJetObservation_truncate {P : Type*} [Fintype P]
    (weight frequency : P → ℂ) (x : ℂ) (N : ℕ) :
    (gammaClockTruncate N).comp
        (finiteExponentialJetObservation weight frequency x (N + 1)) =
      finiteExponentialJetObservation weight frequency x N := by
  rfl

/-- Source-to-Gamma-shadow failure for a finite resolved exponential source. -/
def finiteExponentialGammaAnomaly {P : Type*} [Fintype P]
    (weight frequency : P → ℂ) (x : ℂ) (N : ℕ) :
    (P → ℂ) →ₗ[ℂ] (Fin N → ℂ) :=
  clockDescentAnomaly (finiteExponentialSourceShift frequency)
    (finiteExponentialJetObservation weight frequency x N)
    (gammaClockTranslation N)

/-- The adjacent-depth anomaly defect is exactly the Gamma boundary curvature. -/
theorem finiteExponentialGammaAnomaly_bianchi {P : Type*} [Fintype P]
    (weight frequency : P → ℂ) (x : ℂ) (N : ℕ) :
    (gammaClockTruncate N).comp
        (finiteExponentialGammaAnomaly weight frequency x (N + 1)) -
      finiteExponentialGammaAnomaly weight frequency x N =
    (gammaClockCurvature N).comp
      (finiteExponentialJetObservation weight frequency x (N + 1)) := by
  simpa [finiteExponentialGammaAnomaly, clockAnomalyCoherenceDefect] using!
    clockAnomalyCoherenceDefect_eq_shadowCurvature_comp
      (finiteExponentialSourceShift frequency)
      (finiteExponentialJetObservation weight frequency x N)
      (finiteExponentialJetObservation weight frequency x (N + 1))
      (gammaClockTranslation N) (gammaClockTranslation (N + 1))
      (gammaClockTruncate N)
      (finiteExponentialJetObservation_truncate weight frequency x N)

/-- Coordinate form of the Bianchi current: only the newly exposed top derivative survives. -/
theorem finiteExponentialGammaAnomaly_bianchi_apply {P : Type*} [Fintype P]
    (weight frequency : P → ℂ) (x : ℂ) (N : ℕ)
    (a : P → ℂ) (i : Fin N) :
    (((gammaClockTruncate N).comp
          (finiteExponentialGammaAnomaly weight frequency x (N + 1)) -
        finiteExponentialGammaAnomaly weight frequency x N) a) i =
      finiteExponentialJetObservation weight frequency x (N + 1) a (Fin.last N) /
        ((N - i).factorial : ℂ) := by
  rw [LinearMap.congr_fun
    (finiteExponentialGammaAnomaly_bianchi weight frequency x N) a]
  simp only [LinearMap.comp_apply]
  exact gammaClockCurvature_apply N _ i

/-- Actual finite von Mangoldt weight on the natural-number aperture. -/
def finiteVonMangoldtWeight (n : ℕ) : ℂ :=
  LSeries.term (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) 1 n

/-- Logarithmic prime-power frequency. -/
def finiteVonMangoldtFrequency (n : ℕ) : ℂ :=
  (Real.log n : ℂ)

/-- The first `M` natural coordinates of the von Mangoldt source, shifted past `0,1`. -/
def finiteVonMangoldtGammaAnomaly (M : ℕ) (x : ℂ) (N : ℕ) :
    (Fin M → ℂ) →ₗ[ℂ] (Fin N → ℂ) :=
  finiteExponentialGammaAnomaly
    (fun n : Fin M ↦ finiteVonMangoldtWeight (n + 2))
    (fun n : Fin M ↦ finiteVonMangoldtFrequency (n + 2)) x N

/-- The finite von Mangoldt/Gamma anomaly has the same exact rank-one Bianchi boundary current. -/
theorem finiteVonMangoldtGammaAnomaly_bianchi_apply
    (M : ℕ) (x : ℂ) (N : ℕ) (a : Fin M → ℂ) (i : Fin N) :
    (((gammaClockTruncate N).comp (finiteVonMangoldtGammaAnomaly M x (N + 1)) -
        finiteVonMangoldtGammaAnomaly M x N) a) i =
      finiteExponentialJetObservation
          (fun n : Fin M ↦ finiteVonMangoldtWeight (n + 2))
          (fun n : Fin M ↦ finiteVonMangoldtFrequency (n + 2)) x (N + 1) a
          (Fin.last N) /
        ((N - i).factorial : ℂ) := by
  exact finiteExponentialGammaAnomaly_bianchi_apply _ _ _ _ _ _

end

end RHTower
