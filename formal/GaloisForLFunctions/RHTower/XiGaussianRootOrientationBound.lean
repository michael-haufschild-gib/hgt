import GaloisForLFunctions.RHTower.XiGaussianOrientationPhase

/-!
# Orientation control before coefficient Cauchy--Schwarz

The square-root monomial envelopes are combined with the full coefficient
vector before squaring. This retains the column-dependent weights needed
for interpolation and is never larger than the separated coefficient bound.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

def xiGaussianFiniteRootEnvelope {N : ℕ} (a : Fin N → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : ℝ :=
  (∑ j, |a j| * Real.sqrt (xiGaussianOrientationMonomialEnvelope j s t)) ^ 2

theorem xiGaussianFiniteRootEnvelope_nonneg {N : ℕ} (a : Fin N → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : 0 ≤ xiGaussianFiniteRootEnvelope a s t := sq_nonneg _

theorem xiGaussianImaginaryChannelAtom_finSum_eq {N : ℕ} (a : Fin N → ℝ)
    (t : ℝ) (q : XiZeroCopy) :
    xiGaussianImaginaryChannelAtom
      (∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) t q =
      (∑ j, a j *
        (heatPhaseAmplitude ((xiSpectralPoint q ^ 2) ^ (j : ℕ)) t (xiSpectralPoint q ^ 2)).im) ^ 2 := by
  let Q : Polynomial ℝ := ∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)
  let z := xiSpectralPoint q ^ 2
  let A := heatPhaseAmplitude (evalRealPolynomial Q z) t z
  have hsq : A ^ 2 = xiPolynomialGaussianHeatTerm Q t q := by
    rw [heatPhaseAmplitude_sq]
    rfl
  have hI : xiGaussianImaginaryChannelAtom Q t q = A.im ^ 2 := by
    rw [xiGaussianImaginaryChannelAtom, ← hsq, norm_pow, Complex.sq_norm,
      Complex.normSq_apply, pow_two, Complex.mul_re]
    ring
  have heval : evalRealPolynomial Q z = ∑ j, (a j : ℂ) * z ^ (j : ℕ) := by
    simp [Q, evalRealPolynomial, Polynomial.map_sum, Polynomial.eval_finsetSum]
  have him : A.im = ∑ j, a j * (heatPhaseAmplitude (z ^ (j : ℕ)) t z).im := by
    dsimp only [A]
    rw [heval, heatPhaseAmplitude, Finset.sum_mul, Complex.im_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [heatPhaseAmplitude, mul_assoc, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
  exact hI.trans (congrArg (fun x : ℝ => x ^ 2) him)

/-- Every actual copy obeys the coefficient-sensitive orientation envelope. -/
theorem xiGaussianImaginaryAtom_finSum_le_root_orientation {N : ℕ}
    (F : Finset XiZeroCopy) (a : Fin N → ℝ) (s : {s : ℝ // 0 < s})
    (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) (q : XiZeroCopy) :
    xiGaussianImaginaryChannelAtom
      (∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) t.1 q ≤
      (Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
        xiGaussianFiniteRootEnvelope a s t.1) * (xiZeroCopyReciprocalSquare q).im ^ 2 := by
  by_cases hreal : (xiSpectralPoint q).im = 0
  · rw [xiGaussianImaginaryChannelAtom_of_real _ t.1 ⟨q, hreal⟩]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (xiGaussianFiniteRootEnvelope_nonneg a s t.1)) (sq_nonneg _)
  let e := Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F))
  let u := (xiZeroCopyReciprocalSquare q).im
  let h : Fin N → ℝ := fun j =>
    (heatPhaseAmplitude ((xiSpectralPoint q ^ 2) ^ (j : ℕ)) t.1 (xiSpectralPoint q ^ 2)).im
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hroot (j : Fin N) : |h j| ≤ Real.sqrt e * |u| *
      Real.sqrt (xiGaussianOrientationMonomialEnvelope j s t.1) := by
    have hb := xiGaussianMonomial_im_sq_le_orientation_envelope F j s t ⟨q, hreal⟩
    have hA := xiGaussianOrientationMonomialEnvelope_nonneg j s t.1
    change h j ^ 2 ≤ e * xiGaussianOrientationMonomialEnvelope j s t.1 * u ^ 2 at hb
    calc
      _ = Real.sqrt (h j ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (e * xiGaussianOrientationMonomialEnvelope j s t.1 * u ^ 2) :=
        Real.sqrt_le_sqrt hb
      _ = _ := by
        rw [Real.sqrt_mul (mul_nonneg he hA), Real.sqrt_mul he, Real.sqrt_sq_eq_abs]
        ring
  have htri : |∑ j, a j * h j| ≤ (Real.sqrt e * |u|) *
      ∑ j, |a j| * Real.sqrt (xiGaussianOrientationMonomialEnvelope j s t.1) := by
    calc
      _ ≤ ∑ j, |a j| * |h j| := by
        simpa only [Real.norm_eq_abs, abs_mul] using
          norm_sum_le Finset.univ (fun j => a j * h j)
      _ ≤ ∑ j, |a j| * (Real.sqrt e * |u| *
          Real.sqrt (xiGaussianOrientationMonomialEnvelope j s t.1)) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hroot j) (abs_nonneg _)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr htri
  simp only [mul_pow, sq_abs, Real.sq_sqrt he] at hs
  rw [xiGaussianImaginaryChannelAtom_finSum_eq]
  change (∑ j, a j * h j) ^ 2 ≤ _
  unfold xiGaussianFiniteRootEnvelope
  dsimp only [e, u] at hs
  nlinarith only [hs]

/-- Summing the full polynomial phase keeps the square-root coefficient envelope. -/
theorem xiGaussianImaginaryChannel_finSum_le_root_budget {N : ℕ}
    (F : Finset XiZeroCopy) (a : Fin N → ℝ) (s : {s : ℝ // 0 < s})
    (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
      (∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) t.1 q) ≤
      Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
        xiGaussianFiniteRootEnvelope a s t.1 * xiResidualOrientationBudget F := by
  let C := Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
    xiGaussianFiniteRootEnvelope a s t.1
  have h := (summable_xiGaussianImaginaryChannelAtom _ t.1).tsum_le_tsum
    (xiGaussianImaginaryAtom_finSum_le_root_orientation F a s t)
    (summable_xiThermalOrientationTerm.mul_left C)
  rw [tsum_mul_left] at h
  change _ ≤ C * xiThermalOrientationEnergy at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (xiThermalOrientationEnergy_le_residualOrientationBudget F)
      (mul_nonneg (Real.exp_pos _).le (xiGaussianFiniteRootEnvelope_nonneg a s t.1)))

/-- The new envelope is bounded by the old separated coefficient envelope at every time. -/
theorem xiGaussianFiniteRootEnvelope_le_separated {N : ℕ} (a : Fin N → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    xiGaussianFiniteRootEnvelope a s t ≤
      xiGaussianOrientationEnvelope N s t * (∑ j, a j ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => |a j|)
    (fun j => Real.sqrt (xiGaussianOrientationMonomialEnvelope j s t))
  simp only [sq_abs, Real.sq_sqrt (xiGaussianOrientationMonomialEnvelope_nonneg _ s t)] at h
  rw [Fin.sum_univ_eq_sum_range (fun j => xiGaussianOrientationMonomialEnvelope j s t) N] at h
  simpa only [xiGaussianFiniteRootEnvelope, xiGaussianOrientationEnvelope, mul_comm] using h

end RHTower
