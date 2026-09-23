import GaloisForLFunctions.RHTower.GaussConjugationSymmetry
import GaloisForLFunctions.RHTower.GaussDiagonalLogResidue

/-!
# The logarithmic mean of the iterated Fourier diagonal at every `m`

The relative form of equation (11) puts the whole deviation of `⟪e_n, G^m e_n⟫` from its model
*behind* the step scalar `(p |d_n|²)^m`, which is `≍ 1/n`.  A harmonically weighted vanishing error
has partial sums `o(log N)`, so the logarithmic mean of the two-sided diagonal is the exact
critical residue of the principal model — and, after restoring the local-factor coefficient of the
source reduction, formula `(A)` of the card, at every `m ≥ 2`.

The negative frequency costs nothing: `G` commutes with pointwise conjugation, so the diagonal
there is the complex conjugate of the diagonal at `+n`, while the model term is real.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions

open GaloisForLFunctions.RHTower

noncomputable section

variable {m : ℕ}

/-- **The logarithmic mean of the two-sided iterated Fourier diagonal**, at every `m ≥ 2`. -/
theorem tendsto_gaussFourierDiagonal_pow_logResidue (hm2 : 2 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N,
        ((inner ℂ (fourierLp 2 ((n : ℤ) + 1))
            ((gaussQuasiInnerGFull (le_trans one_le_two hm2) k p ^ m)
              (fourierLp 2 ((n : ℤ) + 1))) : ℂ) +
          inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
            ((gaussQuasiInnerGFull (le_trans one_le_two hm2) k p ^ m)
              (fourierLp 2 (-((n : ℤ) + 1)))))) / (Real.log N : ℂ))
      atTop (nhds ((2 * ((p : ℝ) ^ m - 1) ^ (2 : ℕ) /
        ((m : ℝ) ^ (2 : ℕ) * Real.log (p : ℝ)) : ℝ) : ℂ)) := by
  have hm : (1 : ℕ) ≤ m := le_trans one_le_two hm2
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp
  have harch : (0 : ℝ) ≤ gaussArchScale m ^ (2 * m) := pow_nonneg (gaussArchScale_pos hm).le _
  obtain ⟨C, hC0, hCb⟩ := exists_norm_gaussSampleValue_pow_mul_succ_le_gaussConjugationSymmetry hm k p
  set F : ℤ → ℝ := fun i =>
    ‖(inner ℂ (fourierLp 2 i) ((gaussQuasiInnerG hm k p ^ m) (fourierLp 2 i)) : ℂ) -
      ((((p : ℝ) : ℂ) *
          (starRingEnd ℂ (gaussSampleValue k p i) * gaussSampleValue k p i)) ^ m) *
        ((gaussAmplitudeSegment (p : ℝ) m
          (Int.fract (gaussSamplePhase m p i) ) : ℝ) : ℂ)‖ /
      ‖(((p : ℝ) : ℂ) *
          (starRingEnd ℂ (gaussSampleValue k p i) * gaussSampleValue k p i)) ^ m‖
    with hFdef
  have hF0 : Tendsto (fun n : ℕ => F ((n : ℤ) + 1)) atTop (nhds 0) := by
    have h := (tendsto_norm_inner_gaussQuasiInnerG_pow_sub_amplitude_div hm2 k p hp).comp
      (Filter.tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, hFdef]
    push_cast
    rfl
  have hFnn : ∀ i : ℤ, 0 ≤ F i := fun i => by rw [hFdef]; positivity
  set S : ℕ → ℂ := fun n =>
    (inner ℂ (fourierLp 2 ((n : ℤ) + 1))
        ((gaussQuasiInnerGFull hm k p ^ m) (fourierLp 2 ((n : ℤ) + 1))) : ℂ) +
      inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
        ((gaussQuasiInnerGFull hm k p ^ m) (fourierLp 2 (-((n : ℤ) + 1)))) with hSdef
  set err : ℕ → ℂ := fun n => S n - gaussPrincipalDiagonalTerm k p n with herrdef
  have hbound : ∀ n : ℕ, ((n : ℝ) + 1) * ‖err n‖
      ≤ 2 * gaussArchScale m ^ (2 * m) * ((p : ℝ) ^ m * C) * F ((n : ℤ) + 1) := by
    intro n
    have hne : ((n : ℤ) + 1) ≠ 0 := by omega
    set σ : ℂ := ((p : ℝ) : ℂ) *
      (starRingEnd ℂ (gaussSampleValue k p ((n : ℤ) + 1)) *
        gaussSampleValue k p ((n : ℤ) + 1)) with hσ
    set A : ℂ := ((gaussAmplitudeSegment (p : ℝ) m
      (Int.fract (gaussSamplePhase m p ((n : ℤ) + 1))) : ℝ) : ℂ) with hA
    set X : ℂ := (inner ℂ (fourierLp 2 ((n : ℤ) + 1))
      ((gaussQuasiInnerG hm k p ^ m) (fourierLp 2 ((n : ℤ) + 1))) : ℂ) with hX
    have hFval : F ((n : ℤ) + 1) = ‖X - σ ^ m * A‖ / ‖σ ^ m‖ := by
      rw [hFdef, hX, hσ, hA]
    have hσnorm : ‖σ ^ m‖ = (p : ℝ) ^ m * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * m) := by
      rw [norm_pow, hσ, norm_gaussStepScalar_conj_eq, mul_pow, ← pow_mul]
    have hσne : ‖σ ^ m‖ ≠ 0 := by
      have hd : gaussSampleValue k p ((n : ℤ) + 1) ≠ 0 := gaussSampleValue_ne_zero hm k p hne
      have hpne : ((p : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hppos
      have hcd : starRingEnd ℂ (gaussSampleValue k p ((n : ℤ) + 1)) ≠ 0 := by simpa using hd
      refine norm_ne_zero_iff.mpr (pow_ne_zero m ?_)
      rw [hσ]
      exact mul_ne_zero hpne (mul_ne_zero hcd hd)
    have hEeq : ‖X - σ ^ m * A‖ = ‖σ ^ m‖ * F ((n : ℤ) + 1) := by
      rw [hFval, mul_div_cancel₀ _ hσne]
    have hneg : (inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
        ((gaussQuasiInnerG hm k p ^ m) (fourierLp 2 (-((n : ℤ) + 1)))) : ℂ)
        = starRingEnd ℂ X := by
      rw [hX]
      exact inner_gaussQuasiInnerG_pow_neg hm k p m ((n : ℤ) + 1)
    have hEneg : ‖starRingEnd ℂ X - σ ^ m * A‖ = ‖X - σ ^ m * A‖ := by
      have hreal : starRingEnd ℂ (σ ^ m * A) = σ ^ m * A := by
        rw [hσ, hA]
        exact conj_gaussStepScalar_pow_mul_amplitude k p ((n : ℤ) + 1) m _
      have hstep : starRingEnd ℂ X - σ ^ m * A
          = starRingEnd ℂ (X - σ ^ m * A) := by
        rw [map_sub, hreal]
      rw [hstep, RCLike.norm_conj]
    have hsplit : err n = ((gaussArchScale m ^ (2 * m) : ℝ) : ℂ) *
        ((X - σ ^ m * A) + (starRingEnd ℂ X - σ ^ m * A)) := by
      have hpdt := gaussPrincipalDiagonalTerm_eq hm k p n
      have hval1 := inner_gaussQuasiInnerGFull_pow hm k p m ((n : ℤ) + 1)
      have hval2 := inner_gaussQuasiInnerGFull_pow hm k p m (-((n : ℤ) + 1))
      show S n - gaussPrincipalDiagonalTerm k p n
          = ((gaussArchScale m ^ (2 * m) : ℝ) : ℂ) *
            ((X - σ ^ m * A) + (starRingEnd ℂ X - σ ^ m * A))
      rw [← hpdt]
      simp only [hSdef]
      rw [hval1, hval2, hneg, ← hX, ← hσ, ← hA]
      ring
    have hnormsplit : ‖err n‖
        ≤ gaussArchScale m ^ (2 * m) * (2 * (‖σ ^ m‖ * F ((n : ℤ) + 1))) := by
      rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg harch]
      refine mul_le_mul_of_nonneg_left ?_ harch
      refine (norm_add_le _ _).trans ?_
      rw [hEneg, hEeq]
      linarith
    have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hscalar : ((n : ℝ) + 1) * ‖σ ^ m‖ ≤ (p : ℝ) ^ m * C := by
      rw [hσnorm]
      have hb := hCb n
      have hpm : (0 : ℝ) < (p : ℝ) ^ m := by positivity
      calc ((n : ℝ) + 1) * ((p : ℝ) ^ m *
              ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * m))
          = (p : ℝ) ^ m *
              (‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * m) * ((n : ℝ) + 1)) := by ring
        _ ≤ (p : ℝ) ^ m * C := mul_le_mul_of_nonneg_left hb hpm.le
    calc ((n : ℝ) + 1) * ‖err n‖
        ≤ ((n : ℝ) + 1) * (gaussArchScale m ^ (2 * m) * (2 * (‖σ ^ m‖ * F ((n : ℤ) + 1)))) :=
          mul_le_mul_of_nonneg_left hnormsplit hnn
      _ = 2 * gaussArchScale m ^ (2 * m) * ((((n : ℝ) + 1) * ‖σ ^ m‖) * F ((n : ℤ) + 1)) := by
          ring
      _ ≤ 2 * gaussArchScale m ^ (2 * m) * (((p : ℝ) ^ m * C) * F ((n : ℤ) + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hscalar (hFnn ((n : ℤ) + 1))
      _ = 2 * gaussArchScale m ^ (2 * m) * ((p : ℝ) ^ m * C) * F ((n : ℤ) + 1) := by ring
  have hbig : Tendsto (fun n : ℕ =>
      2 * gaussArchScale m ^ (2 * m) * ((p : ℝ) ^ m * C) * F ((n : ℤ) + 1)) atTop (nhds 0) := by
    have h := hF0.const_mul (2 * gaussArchScale m ^ (2 * m) * ((p : ℝ) ^ m * C))
    simpa using h
  have hscaled : Tendsto (fun n : ℕ => (((n : ℝ) + 1) : ℝ) • err n) atTop (nhds 0) := by
    refine squeeze_zero_norm (fun n => ?_) hbig
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    exact hbound n
  have hharm := tendsto_complexHarmonicWeighted_error_zero hscaled
  have herr : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, err n) / (Real.log N : ℂ)) atTop (nhds 0) := by
    refine hharm.congr fun N => ?_
    have hinner : ∀ n : ℕ,
        ((((n : ℝ) + 1)⁻¹ : ℝ) • ((((n : ℝ) + 1) : ℝ) • err n)) = err n := by
      intro n
      rw [smul_smul, inv_mul_cancel₀ (by positivity : ((n : ℝ) + 1) ≠ 0), one_smul]
    rw [Finset.sum_congr rfl fun n _ => hinner n, Complex.real_smul,
      Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  have hPDT := gaussPrincipalDiagonalTerm_logResidue hm k p
  have hsum := hPDT.add herr
  rw [add_zero] at hsum
  refine hsum.congr fun N => ?_
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  show gaussPrincipalDiagonalTerm k p n + (S n - gaussPrincipalDiagonalTerm k p n) = S n
  ring

/-- **Formula (A) for the operator, at every `m ≥ 2`.** -/
theorem tendsto_gaussLocalDiagonal_pow_logResidue (hm2 : 2 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      ((gaussLocalFactorWeight m p : ℝ) : ℂ) *
        ((∑ n ∈ Finset.range N,
          ((inner ℂ (fourierLp 2 ((n : ℤ) + 1))
              ((gaussQuasiInnerGFull (le_trans one_le_two hm2) k p ^ m)
                (fourierLp 2 ((n : ℤ) + 1))) : ℂ) +
            inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
              ((gaussQuasiInnerGFull (le_trans one_le_two hm2) k p ^ m)
                (fourierLp 2 (-((n : ℤ) + 1)))))) / (Real.log N : ℂ)))
      atTop (nhds ((gaussChannelResidue m p : ℝ) : ℂ)) := by
  have hm : (1 : ℕ) ≤ m := le_trans one_le_two hm2
  have hbase := (tendsto_gaussFourierDiagonal_pow_logResidue hm2 k p).const_mul
    ((gaussLocalFactorWeight m p : ℝ) : ℂ)
  have hval : ((gaussLocalFactorWeight m p : ℝ) : ℂ) *
      ((2 * ((p : ℝ) ^ m - 1) ^ (2 : ℕ) / ((m : ℝ) ^ (2 : ℕ) * Real.log (p : ℝ)) : ℝ) : ℂ)
      = ((gaussChannelResidue m p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, gaussLocalFactorWeight_mul_principalResidue hm p]
  rwa [hval] at hbase

end

end RHTower
