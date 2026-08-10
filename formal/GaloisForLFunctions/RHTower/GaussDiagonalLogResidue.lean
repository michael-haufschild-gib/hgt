import GaloisForLFunctions.RHTower.GaussRelativeDiagonal
import GaloisForLFunctions.HTGeometry.HarmonicComplexResidueTransfer

/-!
# The logarithmic mean of the Fourier diagonal

For a single Gauss component the relative form of the diagonal converts into the logarithmic mean
directly: the error is the main term times a vanishing factor, the main term is `≍ 1/n`, and a
harmonically weighted error tending to zero has partial sums `o(log N)`.

This upgrades the card's equation (14) from a statement about the principal diagonal *model* to a
statement about the operator itself.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology

noncomputable section

/-! ## The sampled square decays like `1/n` -/

theorem exists_norm_gaussSampleValue_sq_mul_succ_le (k : Fin 1) (p : Nat.Primes) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ 2 * ((n : ℝ) + 1) ≤ C := by
  obtain ⟨c, C, hc, hC, hb⟩ :=
    exists_gaussComponentPrimeMagnitudeEnergy_bounds (le_refl 1) k p
  have harch : 0 < gaussArchConst 1 := gaussArchConst_pos (le_refl 1)
  refine ⟨C / gaussArchConst 1, by positivity, fun n => ?_⟩
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hub := (hb n).2
  rw [gaussComponentPrimeMagnitudeEnergy_eq (le_refl 1) k p n, le_div_iff₀ hden] at hub
  rw [le_div_iff₀ harch]
  have hpow : ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * 1)
      = ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ 2 := by norm_num
  rw [hpow] at hub
  calc ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ 2 * ((n : ℝ) + 1) * gaussArchConst 1
      = gaussArchConst 1 * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ 2 * ((n : ℝ) + 1) := by ring
    _ ≤ C := hub

/-! ## The two frequencies carry the same scalar -/

theorem gaussStepScalar_neg {m : ℕ} (k : Fin m) (p : Nat.Primes) (i : ℤ) :
    ((p : ℝ) : ℂ) * (starRingEnd ℂ (gaussSampleValue k p (-i)) * gaussSampleValue k p (-i))
      = ((p : ℝ) : ℂ) *
        (gaussSampleValue k p i * starRingEnd ℂ (gaussSampleValue k p i)) := by
  rw [gaussSampleValue_neg, Complex.conj_conj]
  ring

theorem norm_gaussStepScalar_eq {m : ℕ} (k : Fin m) (p : Nat.Primes) (i : ℤ) :
    ‖((p : ℝ) : ℂ) * (gaussSampleValue k p i * starRingEnd ℂ (gaussSampleValue k p i))‖
      = (p : ℝ) * ‖gaussSampleValue k p i‖ ^ 2 := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have h : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    linarith
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hppos,
    RCLike.norm_conj]
  ring

/-! ## The logarithmic mean -/

set_option maxHeartbeats 1000000 in
/-- **The logarithmic mean of the two-sided Fourier diagonal of a single Gauss component.**  The
limit is the exact critical residue of the principal model, now for the operator itself. -/
theorem tendsto_gaussFourierDiagonal_logResidue (k : Fin 1) (p : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N,
        ((inner ℂ (fourierLp 2 ((n : ℤ) + 1))
            ((gaussQuasiInnerGFull (le_refl 1) k p ^ 1) (fourierLp 2 ((n : ℤ) + 1))) : ℂ) +
          inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
            ((gaussQuasiInnerGFull (le_refl 1) k p ^ 1)
              (fourierLp 2 (-((n : ℤ) + 1)))))) / (Real.log N : ℂ))
      atTop (nhds ((2 * ((p : ℝ) ^ 1 - 1) ^ 2 /
        ((1 : ℝ) ^ 2 * Real.log (p : ℝ)) : ℝ) : ℂ)) := by
  have hm : (1 : ℕ) ≤ 1 := le_refl 1
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp
  have harch : (0 : ℝ) ≤ gaussArchScale 1 ^ (2 * 1) :=
    pow_nonneg (gaussArchScale_pos hm).le _
  obtain ⟨C, hC0, hCb⟩ := exists_norm_gaussSampleValue_sq_mul_succ_le k p
  set b : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleBlock hp (fourierLp 2 0) with hbdef
  set F : ℤ → ℝ := fun i =>
    gaussFoldDefect hm k p hp i * (gaussFoldDefect hm k p hp i + 2 * ‖b‖) with hF
  have hFnn : ∀ i : ℤ, 0 ≤ F i := by
    intro i
    have h0 : (0 : ℝ) ≤ gaussFoldDefect hm k p hp i := norm_nonneg _
    have h1 : (0 : ℝ) ≤ ‖b‖ := norm_nonneg _
    rw [hF]
    positivity
  have hιp : Tendsto (fun n : ℕ => (((n : ℤ) + 1)).natAbs) atTop atTop := by
    refine (Filter.tendsto_add_atTop_nat 1).congr fun n => ?_
    omega
  have hιm : Tendsto (fun n : ℕ => ((-((n : ℤ) + 1))).natAbs) atTop atTop := by
    refine (Filter.tendsto_add_atTop_nat 1).congr fun n => ?_
    omega
  have hFp : Tendsto (fun n : ℕ => F ((n : ℤ) + 1)) atTop (nhds 0) :=
    tendsto_gaussRelativeDiagonalFactor hm k p hp hιp
  have hFm : Tendsto (fun n : ℕ => F (-((n : ℤ) + 1))) atTop (nhds 0) :=
    tendsto_gaussRelativeDiagonalFactor hm k p hp hιm
  set S : ℕ → ℂ := fun n =>
    (inner ℂ (fourierLp 2 ((n : ℤ) + 1))
        ((gaussQuasiInnerGFull hm k p ^ 1) (fourierLp 2 ((n : ℤ) + 1))) : ℂ) +
      inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
        ((gaussQuasiInnerGFull hm k p ^ 1) (fourierLp 2 (-((n : ℤ) + 1)))) with hSdef
  set err : ℕ → ℂ := fun n => S n - gaussPrincipalDiagonalTerm k p n with herrdef
  -- the pointwise relative bound
  have hbound : ∀ n : ℕ, ((n : ℝ) + 1) * ‖err n‖
      ≤ gaussArchScale 1 ^ (2 * 1) * ((p : ℝ) * C) * (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) := by
    intro n
    have hip : ((n : ℤ) + 1) ≠ 0 := by omega
    have him : (-((n : ℤ) + 1)) ≠ 0 := by omega
    have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    set X : ℂ := (inner ℂ (fourierLp 2 ((n : ℤ) + 1))
        (gaussQuasiInnerG hm k p (fourierLp 2 ((n : ℤ) + 1))) : ℂ) -
      (((p : ℝ) : ℂ) * (gaussSampleValue k p ((n : ℤ) + 1) *
          starRingEnd ℂ (gaussSampleValue k p ((n : ℤ) + 1)))) *
        ((gaussAmplitudeSegment (p : ℝ) 1
          (Int.fract (gaussSamplePhase 1 p ((n : ℤ) + 1))) : ℝ) : ℂ) with hX
    set Y : ℂ := (inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
        (gaussQuasiInnerG hm k p (fourierLp 2 (-((n : ℤ) + 1)))) : ℂ) -
      (((p : ℝ) : ℂ) * (gaussSampleValue k p (-((n : ℤ) + 1)) *
          starRingEnd ℂ (gaussSampleValue k p (-((n : ℤ) + 1))))) *
        ((gaussAmplitudeSegment (p : ℝ) 1
          (Int.fract (gaussSamplePhase 1 p (-((n : ℤ) + 1)))) : ℝ) : ℂ) with hY
    have hsplit : err n = ((gaussArchScale 1 ^ (2 * 1) : ℝ) : ℂ) * (X + Y) := by
      have hpdt := gaussPrincipalDiagonalTerm_eq hm k p n
      have hval1 := inner_gaussQuasiInnerGFull_pow hm k p 1 ((n : ℤ) + 1)
      have hval2 := inner_gaussQuasiInnerGFull_pow hm k p 1 (-((n : ℤ) + 1))
      have hphase : gaussSamplePhase 1 p (-((n : ℤ) + 1))
          = gaussSamplePhase 1 p ((n : ℤ) + 1) := gaussSamplePhase_neg 1 p _
      have hscal := gaussStepScalar_neg k p ((n : ℤ) + 1)
      rw [herrdef, hSdef, ← hpdt, hval1, hval2, hX, hY, hphase]
      simp only [pow_one]
      rw [gaussSampleValue_neg, Complex.conj_conj]
      ring
    have h1 := norm_inner_gaussQuasiInnerG_sub_amplitude_le hm k p hp hip
    have h2 := norm_inner_gaussQuasiInnerG_sub_amplitude_le hm k p hp him
    rw [← hX, norm_gaussStepScalar_eq, ← hF] at h1
    rw [← hY, norm_gaussStepScalar_eq, ← hF] at h2
    have hvalneg : ‖gaussSampleValue k p (-((n : ℤ) + 1))‖
        = ‖gaussSampleValue k p ((n : ℤ) + 1)‖ := by
      rw [gaussSampleValue_neg, RCLike.norm_conj]
    rw [hvalneg] at h2
    have hstep : ‖err n‖ ≤ gaussArchScale 1 ^ (2 * 1) *
        ((p : ℝ) * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ 2 *
          (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1)))) := by
      rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg harch]
      refine mul_le_mul_of_nonneg_left ?_ harch
      calc ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := norm_add_le _ _
        _ ≤ (p : ℝ) * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ 2 * F ((n : ℤ) + 1) +
              (p : ℝ) * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ 2 * F (-((n : ℤ) + 1)) :=
            add_le_add h1 h2
        _ = (p : ℝ) * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ 2 *
              (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) := by ring
    have hFsum : (0 : ℝ) ≤ F ((n : ℤ) + 1) + F (-((n : ℤ) + 1)) :=
      add_nonneg (hFnn _) (hFnn _)
    have hcoef : (0 : ℝ) ≤ gaussArchScale 1 ^ (2 * 1) * (p : ℝ) :=
      mul_nonneg harch hppos.le
    calc ((n : ℝ) + 1) * ‖err n‖
        ≤ ((n : ℝ) + 1) * (gaussArchScale 1 ^ (2 * 1) *
            ((p : ℝ) * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ 2 *
              (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))))) :=
          mul_le_mul_of_nonneg_left hstep hnn
      _ = gaussArchScale 1 ^ (2 * 1) * (p : ℝ) *
            (‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ 2 * ((n : ℝ) + 1)) *
            (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) := by ring
      _ ≤ gaussArchScale 1 ^ (2 * 1) * (p : ℝ) * C *
            (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hCb n) hcoef) hFsum
      _ = gaussArchScale 1 ^ (2 * 1) * ((p : ℝ) * C) *
            (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) := by ring
  -- the weighted error vanishes
  have hbig : Tendsto (fun n : ℕ =>
      gaussArchScale 1 ^ (2 * 1) * ((p : ℝ) * C) *
        (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1)))) atTop (nhds 0) := by
    have hsum := hFp.add hFm
    rw [add_zero] at hsum
    have := hsum.const_mul (gaussArchScale 1 ^ (2 * 1) * ((p : ℝ) * C))
    simpa using this
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
  rw [div_add_div_same, ← Finset.sum_add_distrib]
  refine congrArg (fun z : ℂ => z / (Real.log N : ℂ)) ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [herrdef]
  ring

end

end RHTower
