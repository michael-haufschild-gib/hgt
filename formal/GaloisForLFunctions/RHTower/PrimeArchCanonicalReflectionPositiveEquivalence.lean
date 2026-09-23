import GaloisForLFunctions.HTGeometry.ReflectionPositiveHankel
import GaloisForLFunctions.RHTower.PrimeArchMomentMeasureRH
import GaloisForLFunctions.RHTower.PrimeArchThetaAllOrderCumulant
import GaloisForLFunctions.RHTower.XiReciprocalSquareSourceCore

/-!
# Canonical reflection-positive realization of the prime--archimedean moments

The normalized continued prime--Gamma moment sequence has a reflection-positive Gram realization
if and only if RH holds.  The reverse implication is the static Osterwalder--Schrader/Hankel
norm-square law.  Under RH, the converse is realized canonically on the multiplicity-exact Xi
`ell^(2 : ℕ)` space: if `lambda_q` is the reciprocal square of the centered spectral coordinate, then

`v_n(q) = sqrt(lambda_q) * lambda_q^n`.

The same construction is the vacuum orbit of the bounded reciprocal-square Xi operator.  This
gives an equivalent self-adjoint vacuum-moment formulation whose moments are read entirely from
the fixed continued prime--Gamma source germ.  The equivalence does not assert the missing
source-side construction of this positive orbit without RH.
-/

open Complex

namespace RHTower

noncomputable section

/-- The canonical reciprocal-square moment coordinate.  Its `ell^(2 : ℕ)` membership is conditional on
RH, but the coordinate formula itself is unconditional. -/
def primeArchReflectionCoordinate (n : ℕ) (q : XiZeroCopy) : ℂ :=
  ((Real.sqrt (xiZeroCopyReciprocalSquare q).re : ℝ) : ℂ) *
    xiZeroCopyReciprocalSquare q ^ n

theorem primeArchReflectionCoordinate_eq_of_riemannHypothesis
    (hRH : RiemannHypothesis) (n : ℕ) (q : XiZeroCopy) :
    ∃ x : ℝ, 0 < x ∧
      xiZeroCopyReciprocalSquare q = (x : ℂ) ∧
      primeArchReflectionCoordinate n q =
        ((Real.sqrt x * x ^ n : ℝ) : ℂ) := by
  obtain ⟨x, hx, hcoord⟩ :=
    xiCentralReciprocalSquare_pos_real_of_rh hRH q.1
  refine ⟨x, hx, ?_, ?_⟩
  · simpa only [xiZeroCopyReciprocalSquare_eq] using hcoord
  · rw [primeArchReflectionCoordinate]
    rw [xiZeroCopyReciprocalSquare_eq, hcoord]
    simp

theorem summable_norm_sq_primeArchReflectionCoordinate_of_riemannHypothesis
    (hRH : RiemannHypothesis) (n : ℕ) :
    Summable (fun q : XiZeroCopy =>
      ‖primeArchReflectionCoordinate n q‖ ^ (2 : ℕ)) := by
  have hp := (summable_xiZeroCopyReciprocalSquare_pow (2 * n)).norm
  apply hp.congr
  intro q
  obtain ⟨x, hx, hcoord, hv⟩ :=
    primeArchReflectionCoordinate_eq_of_riemannHypothesis hRH n q
  rw [hv, hcoord]
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_pos hx, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow, Real.sq_sqrt hx.le]
  ring

/-- Under RH, the `n`th canonical prime--archimedean reflection vector in the Xi `ell^(2 : ℕ)` space. -/
def primeArchReflectionVector
    (hRH : RiemannHypothesis) (n : ℕ) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  ⟨primeArchReflectionCoordinate n,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_primeArchReflectionCoordinate_of_riemannHypothesis hRH n)⟩

@[simp] theorem primeArchReflectionVector_apply
    (hRH : RiemannHypothesis) (n : ℕ) (q : XiZeroCopy) :
    primeArchReflectionVector hRH n q =
      primeArchReflectionCoordinate n q := rfl

/-- The canonical reflection vectors have exactly the normalized continued prime--Gamma moments
as their Hankel Gram matrix. -/
theorem inner_primeArchReflectionVector_eq_normalizedMoment
    (hRH : RiemannHypothesis) (i j : ℕ) :
    inner ℂ (primeArchReflectionVector hRH i)
        (primeArchReflectionVector hRH j) =
      (normalizedPrimeArchMoment (i + j) : ℂ) := by
  rw [lp.inner_eq_tsum]
  calc
    (∑' q : XiZeroCopy,
        inner ℂ (primeArchReflectionVector hRH i q)
          (primeArchReflectionVector hRH j q)) =
        ∑' q : XiZeroCopy,
          xiZeroCopyReciprocalSquare q ^ (i + j + 1) := by
      apply tsum_congr
      intro q
      obtain ⟨x, hx, hcoord, _⟩ :=
        primeArchReflectionCoordinate_eq_of_riemannHypothesis hRH i q
      have hi : primeArchReflectionCoordinate i q =
          ((Real.sqrt x * x ^ i : ℝ) : ℂ) := by
        rw [primeArchReflectionCoordinate, hcoord]
        simp
      have hj : primeArchReflectionCoordinate j q =
          ((Real.sqrt x * x ^ j : ℝ) : ℂ) := by
        rw [primeArchReflectionCoordinate, hcoord]
        simp
      rw [primeArchReflectionVector_apply,
        primeArchReflectionVector_apply, hi, hj, hcoord]
      simp only [RCLike.inner_apply]
      rw [Complex.conj_ofReal]
      norm_cast
      rw [show (Real.sqrt x * x ^ j) * (Real.sqrt x * x ^ i) =
          (Real.sqrt x) ^ (2 : ℕ) * x ^ (i + j) by ring]
      rw [Real.sq_sqrt hx.le]
      ring
    _ = xiCentralReciprocalMoment (i + j) := by
      simpa [add_assoc] using tsum_xiZeroCopyReciprocalSquare_pow (i + j)
    _ = (normalizedPrimeArchMoment (i + j) : ℂ) := by
      symm
      exact primeArchSourceMoment_eq_xiCentralReciprocalMoment (i + j)

theorem exists_primeArchComplexReflectionPositiveGram_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∃ v : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2,
      ∀ i j, inner ℂ (v i) (v j) =
        (normalizedPrimeArchMoment (i + j) : ℂ) := by
  exact ⟨primeArchReflectionVector hRH,
    inner_primeArchReflectionVector_eq_normalizedMoment hRH⟩

theorem riemannHypothesis_of_canonicalPrimeArchComplexReflectionPositiveGram
    (v : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2)
    (hgram : ∀ i j, inner ℂ (v i) (v j) =
      (normalizedPrimeArchMoment (i + j) : ℂ)) :
    RiemannHypothesis := by
  apply primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis.mp
  intro p
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  exact HTGeometry.momentFunctional_pow_two_nonneg_of_complexReflectionPositiveGram
    normalizedPrimeArchMoment v hgram _

/-- **Canonical reflection-positive source equivalence.** -/
theorem riemannHypothesis_iff_exists_primeArchComplexReflectionPositiveGram :
    RiemannHypothesis ↔
      ∃ v : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2,
        ∀ i j, inner ℂ (v i) (v j) =
          (normalizedPrimeArchMoment (i + j) : ℂ) := by
  constructor
  · exact exists_primeArchComplexReflectionPositiveGram_of_riemannHypothesis
  · rintro ⟨v, hgram⟩
    exact riemannHypothesis_of_canonicalPrimeArchComplexReflectionPositiveGram v hgram

/-- Powers of the reciprocal-square operator act coordinatewise by powers of the reciprocal-square
spectral coordinate. -/
theorem xiReciprocalSquareOperator_pow_apply
    (n : ℕ) (f : lp (fun _ : XiZeroCopy => ℂ) 2) (q : XiZeroCopy) :
    (xiReciprocalSquareOperator ^ n) f q =
      xiZeroCopyReciprocalSquare q ^ n * f q := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp, ih,
        xiReciprocalSquareOperator_apply]
      ring

/-- The reflection vectors are the vacuum orbit of the canonical reciprocal-square operator. -/
theorem xiReciprocalSquareOperator_pow_reflectionVacuum
    (hRH : RiemannHypothesis) (n : ℕ) :
    (xiReciprocalSquareOperator ^ n)
        (primeArchReflectionVector hRH 0) =
      primeArchReflectionVector hRH n := by
  apply Subtype.ext
  funext q
  rw [xiReciprocalSquareOperator_pow_apply,
    primeArchReflectionVector_apply,
    primeArchReflectionVector_apply]
  simp [primeArchReflectionCoordinate, mul_comm]

theorem exists_primeArchSelfAdjointVacuumRealization_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∃ (A : lp (fun _ : XiZeroCopy => ℂ) 2 →L[ℂ]
          lp (fun _ : XiZeroCopy => ℂ) 2)
        (omega : lp (fun _ : XiZeroCopy => ℂ) 2),
      IsSelfAdjoint A ∧
      ∀ n, inner ℂ omega ((A ^ n) omega) =
        (normalizedPrimeArchMoment n : ℂ) := by
  refine ⟨xiReciprocalSquareOperator,
    primeArchReflectionVector hRH 0,
    xiReciprocalSquareOperator_isSelfAdjoint_of_riemannHypothesis hRH, ?_⟩
  intro n
  rw [xiReciprocalSquareOperator_pow_reflectionVacuum hRH n,
    inner_primeArchReflectionVector_eq_normalizedMoment]
  simp

theorem riemannHypothesis_of_primeArchSelfAdjointVacuumRealization
    (A : lp (fun _ : XiZeroCopy => ℂ) 2 →L[ℂ]
      lp (fun _ : XiZeroCopy => ℂ) 2)
    (omega : lp (fun _ : XiZeroCopy => ℂ) 2)
    (hA : IsSelfAdjoint A)
    (hmom : ∀ n, inner ℂ omega ((A ^ n) omega) =
      (normalizedPrimeArchMoment n : ℂ)) :
    RiemannHypothesis := by
  apply primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis.mp
  intro p
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  exact HTGeometry.momentFunctional_pow_two_nonneg_of_complexSelfAdjointObservable
    normalizedPrimeArchMoment A omega hA hmom _

/-- **Self-adjoint vacuum-moment equivalence.**  The moment values are the Taylor coefficients of
the fixed normalized continued prime--Gamma source germ. -/
theorem riemannHypothesis_iff_exists_primeArchSelfAdjointVacuumRealization :
    RiemannHypothesis ↔
      ∃ (A : lp (fun _ : XiZeroCopy => ℂ) 2 →L[ℂ]
            lp (fun _ : XiZeroCopy => ℂ) 2)
          (omega : lp (fun _ : XiZeroCopy => ℂ) 2),
        IsSelfAdjoint A ∧
        ∀ n, inner ℂ omega ((A ^ n) omega) =
          (normalizedPrimeArchMoment n : ℂ) := by
  constructor
  · exact exists_primeArchSelfAdjointVacuumRealization_of_riemannHypothesis
  · rintro ⟨A, omega, hA, hmom⟩
    exact riemannHypothesis_of_primeArchSelfAdjointVacuumRealization
      A omega hA hmom

end

end RHTower
