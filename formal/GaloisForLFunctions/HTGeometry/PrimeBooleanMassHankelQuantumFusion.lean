import GaloisForLFunctions.HTGeometry.ConstitutiveCyclicProcessFourShadow
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.BooleanGibbsCapacityResponse
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.PhaseHistoryDilation
import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue

/-!
# Prime Boolean--Mass--Hankel--quantum fusion

One finite positive clock packet has four source-generated values:

* the parity--clock Schur capacity;
* the squared Gibbs-damped Mass current, namely the clock variance `C`;
* the first positive Hankel determinant `A*C-B^(2 : ℕ)`;
* the transverse pure-state QFI, four times the Schur capacity.

Their exact conservation law is

`transverseQFI * massEnergy = 4 * pi^(2 : ℕ) * hankelDet`.

The module also transports the certified Boolean tilt response into the QFI organ, re-exports the
arbitrarily-late prime-clock return theorem, records the exact half-density Mass damping, and
specializes the corpus's finite Prony reconstruction theorem to real clock packets.
-/

namespace HTGeometry

noncomputable section

open ConstraintFrameRelativity

variable {ι : Type*} [Fintype ι]

/-- Squared Gibbs-damped Mass current: the weighted clock energy `C`. -/
def fusionMassEnergy (w lam : ι → ℝ) : ℝ := capC w lam

/-- First positive prime-clock Hankel determinant. -/
def fusionHankelDet (w lam : ι → ℝ) : ℝ :=
  capA w * capC w lam - capB w lam ^ (2 : ℕ)

/-- Conventional pure-state QFI normal to clock reparametrisation. -/
def fusionTransverseQFI (w lam : ι → ℝ) : ℝ :=
  4 * schurCapacity w lam

/-- Directional QFI before minimising over the clock correction `t`. -/
def fusionDirectionalQFI (w lam : ι → ℝ) (t : ℝ) : ℝ :=
  4 * (Real.pi ^ (2 : ℕ) * capA w - 2 * Real.pi * t * capB w lam + t ^ (2 : ℕ) * capC w lam)

theorem fusionMassEnergy_eq_capC (w lam : ι → ℝ) :
    fusionMassEnergy w lam = capC w lam := rfl

theorem fusionTransverseQFI_eq_four_mul_schurCapacity (w lam : ι → ℝ) :
    fusionTransverseQFI w lam = 4 * schurCapacity w lam := rfl

variable [DecidableEq ι]

/-- The directional value is literally the pure-state QFI of the Boolean parity--clock tangent:
the overlap is its mean and the tangent energy is its second moment. -/
theorem pureStateQuantumFisherValue_booleanParityClock_eq_directional
    (q lam : ι → ℝ) (t : ℝ) :
    pureStateQuantumFisherValue 1
      (bernoulliExp q (linearStat fun p => Real.pi - t * lam p))
      (bernoulliExp q (fun S => (linearStat (fun p => Real.pi - t * lam p) S) ^ (2 : ℕ)))
      = fusionDirectionalQFI (bernoulliVar q) lam t := by
  unfold pureStateQuantumFisherValue projectiveQuantumTangentValue fusionDirectionalQFI
  simp only [one_pow, div_one]
  have hcov := bernoulliCov_affine_clock q lam Real.pi t
  rw [quadratic_expand] at hcov
  have hvar :
      bernoulliExp q (fun S => (linearStat (fun p => Real.pi - t * lam p) S) ^ (2 : ℕ)) -
          bernoulliExp q (linearStat fun p => Real.pi - t * lam p) ^ (2 : ℕ) =
        Real.pi ^ (2 : ℕ) * capA (bernoulliVar q)
          - 2 * Real.pi * t * capB (bernoulliVar q) lam
          + t ^ (2 : ℕ) * capC (bernoulliVar q) lam := by
    calc
      _ = bernoulliCov q (linearStat fun p => Real.pi - t * lam p)
          (linearStat fun p => Real.pi - t * lam p) := by
            simp only [bernoulliCov, pow_two]
      _ = _ := hcov
  simpa only [one_mul] using congrArg (fun x : ℝ => 4 * x) hvar

omit [DecidableEq ι] in

/-- The transverse QFI is the minimum over all clock reparametrisations. -/
theorem fusionTransverseQFI_le_directional {w lam : ι → ℝ}
    (hC : 0 < capC w lam) (t : ℝ) :
    fusionTransverseQFI w lam ≤ fusionDirectionalQFI w lam t := by
  exact mul_le_mul_of_nonneg_left (schurCapacity_le_quadratic hC t) (by norm_num)

omit [DecidableEq ι] in

/-- The canonical regression clock attains the transverse QFI. -/
theorem fusionDirectionalQFI_canonical {w lam : ι → ℝ} (hC : 0 < capC w lam) :
    fusionDirectionalQFI w lam (Real.pi * capB w lam / capC w lam) =
      fusionTransverseQFI w lam := by
  unfold fusionDirectionalQFI fusionTransverseQFI
  rw [quadratic_eq_schurCapacity hC]

omit [DecidableEq ι] in

/-- **Four-organ conserved-volume identity.** -/
theorem fusionTransverseQFI_mul_massEnergy {w lam : ι → ℝ}
    (hC : 0 < capC w lam) :
    fusionTransverseQFI w lam * fusionMassEnergy w lam =
      4 * Real.pi ^ (2 : ℕ) * fusionHankelDet w lam := by
  unfold fusionTransverseQFI fusionMassEnergy fusionHankelDet
  rw [schurCapacity_eq_ratio hC]
  field_simp

omit [DecidableEq ι] in

/-- Positive weights and two different clocks give strictly positive transverse QFI. -/
theorem fusionTransverseQFI_pos {w lam : ι → ℝ} (hw : ∀ p, 0 < w p)
    {p r : ι} (hne : lam p ≠ lam r) :
    0 < fusionTransverseQFI w lam := by
  exact mul_pos (by norm_num) (schurCapacity_pos hw hne)

omit [DecidableEq ι] in

/-- The same hypotheses give a strictly positive first Hankel determinant. -/
theorem fusionHankelDet_pos {w lam : ι → ℝ} (hw : ∀ p, 0 < w p)
    {p r : ι} (hne : lam p ≠ lam r) :
    0 < fusionHankelDet w lam := by
  exact capA_mul_capC_sub_capB_sq_pos hw hne

/-! ## Exact half-density Mass damping -/

/-- Squared primitive-prime Mass coefficient `lam^(2 : ℕ) / p`. -/
def primitiveMassEnergy (p lam : ℝ) : ℝ := lam ^ (2 : ℕ) / p

/-- Squared Gibbs-damped coefficient at the half-density weight. -/
def gibbsDampedMassEnergy (p lam : ℝ) : ℝ := p / (p + 1) ^ (2 : ℕ) * lam ^ (2 : ℕ)

/-- At half density, Gibbs damping is exactly multiplication by `(p/(p+1))^(2 : ℕ)` on Mass energy. -/
theorem gibbsDampedMassEnergy_eq_damping_sq_mul_primitive
    {p lam : ℝ} (hp : 0 < p) :
    gibbsDampedMassEnergy p lam =
      (p / (p + 1)) ^ (2 : ℕ) * primitiveMassEnergy p lam := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hp1 : p + 1 ≠ 0 := by linarith
  unfold gibbsDampedMassEnergy primitiveMassEnergy
  field_simp

/-! ## Fourth-organ intervention response -/

/-- Transverse QFI along the exact finite Boolean tilt. -/
def booleanTiltTransverseQFI (q lam : ι → ℝ) (r : Finset ι → ℝ) (e : ℝ) : ℝ :=
  4 * (Real.pi ^ (2 : ℕ) *
    (tiltCov (bernoulliWeight q) r e (linearStat fun _ => 1) (linearStat fun _ => 1)
      - tiltCov (bernoulliWeight q) r e (linearStat fun _ => 1) (linearStat lam) ^ (2 : ℕ)
        / tiltCov (bernoulliWeight q) r e (linearStat lam) (linearStat lam)))

/-- **Fourth-organ response law.**  The QFI response is four times the certified Schur-capacity
response, hence `4*pi^(2 : ℕ) Cov(r,R^(2 : ℕ))`. -/
theorem hasDerivAt_booleanTiltTransverseQFI (q lam : ι → ℝ) (r : Finset ι → ℝ)
    (hC : capC (bernoulliVar q) lam ≠ 0) :
    HasDerivAt (booleanTiltTransverseQFI q lam r)
      (4 * (Real.pi ^ (2 : ℕ) * wcov (bernoulliWeight q) r (fun S =>
        ((linearStat (fun _ => 1) S - wexp (bernoulliWeight q) (linearStat fun _ => 1))
          - (capB (bernoulliVar q) lam / capC (bernoulliVar q) lam)
            * (linearStat lam S - wexp (bernoulliWeight q) (linearStat lam))) ^ (2 : ℕ)))) 0 := by
  unfold booleanTiltTransverseQFI
  exact (hasDerivAt_booleanTiltCapacity q lam r hC).const_mul 4

/-! ## Finite joint reconstruction -/

/-- Real positive atomic clock packets are represented by the existing complex process moments. -/
def realClockMoment {r : ℕ} (lam : Fin r → ℝ) (w : Fin r → ℝ) (n : ℕ) : ℂ :=
  GaloisForLFunctions.HTGeometry.processMoment (fun i => (lam i : ℂ)) w n

/-- The first `2r` real clock moments reconstruct the spectral polynomial, hence the unordered
clock packet. -/
theorem realClockSpectrumPoly_eq_of_moments_eq {r : ℕ}
    (lam lam' : Fin r → ℝ) (w w' : Fin r → ℝ)
    (hinj : Function.Injective lam) (hw : ∀ j, 0 < w j)
    (h : ∀ n, n < 2 * r → realClockMoment lam w n = realClockMoment lam' w' n) :
    GaloisForLFunctions.HTGeometry.spectrumPoly (fun i => (lam i : ℂ)) =
      GaloisForLFunctions.HTGeometry.spectrumPoly (fun i => (lam' i : ℂ)) := by
  apply GaloisForLFunctions.HTGeometry.spectrumPoly_eq_of_moments_eq
    (fun i => (lam i : ℂ)) (fun i => (lam' i : ℂ)) w w'
  · exact Complex.ofReal_injective.comp hinj
  · exact hw
  · exact h

/-- Once the real clock nodes are fixed, the first `r` moments reconstruct all positive weights. -/
theorem realClockWeights_eq_of_moments_eq {r : ℕ}
    (lam : Fin r → ℝ) (w w' : Fin r → ℝ)
    (hinj : Function.Injective lam)
    (h : ∀ n, n < r → realClockMoment lam w n = realClockMoment lam w' n) :
    w = w' := by
  exact GaloisForLFunctions.HTGeometry.weights_eq_of_moments_eq
    (fun i => (lam i : ℂ)) w w'
    (Complex.ofReal_injective.comp hinj) h

/-! ## Prime-clock recurrence -/

/-- Every finite prime phase clock returns arbitrarily close to the identity at arbitrarily late
times.  This is the recurrence input used by the paper theorem's Boolean pure-state corollary. -/
theorem primeBooleanFusion_exists_large_return (F : Finset Nat.Primes) {ε T : ℝ}
    (hε : 0 < ε) (hT : 0 < T) :
    ∃ t : ℝ, T ≤ t ∧ ∀ p : F,
      ‖shellFlow (F := F) 1 t p - 1‖ < ε :=
  exists_large_return 1 F hε hT

end

end HTGeometry
