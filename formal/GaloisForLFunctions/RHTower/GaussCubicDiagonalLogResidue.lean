import GaloisForLFunctions.RHTower.GaussCubicOuterConvergence
import GaloisForLFunctions.RHTower.GaussSquareDiagonalLogResidue

/-!
# The logarithmic mean of the cubic Fourier diagonal at `m = 3`

The newly closed triple-defect convergence makes the cubic principal moment relatively exact.
After multiplication by the step scalar cubed, the diagonal error is `o(1/n)` and hence has zero
logarithmic mean.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology
open GaloisForLFunctions.RHTower

noncomputable section

set_option maxRecDepth 4000

theorem inner_one_gaussMovingAmplitude_cube_eq_segment
    {p : ℝ} (hp : 1 < p) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (inner ℂ (fourierLp 2 0)
        ((gaussMovingAmplitudeBlock hp ((s : ℝ) : AddCircle (1 : ℝ)) ^ (3 : ℕ))
          (fourierLp 2 0)) : ℂ) =
      ((gaussAmplitudeSegment p 3 s : ℝ) : ℂ) := by
  rw [GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff,
    fourierCoeff_gaussAmplitudeIterate_zero hp hs0 hs1 3]

/-- Vanishing relative factor for the cubic diagonal. -/
def gaussCubicRelativeFactor (k : Fin 3) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) : ℝ :=
  ‖(inner ℂ (fourierLp 2 0)
        ((gaussPrincipalStepBlock (by omega : 1 ≤ 3) k p hp i ^ (3 : ℕ))
          (fourierLp 2 0)) : ℂ) -
    ((gaussAmplitudeSegment (p : ℝ) 3
      (Int.fract (gaussSamplePhase 3 p i)) : ℝ) : ℂ)‖

theorem gaussCubicRelativeFactor_nonneg (k : Fin 3) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    0 ≤ gaussCubicRelativeFactor k p hp i := norm_nonneg _

theorem norm_inner_one_gaussPrincipalStep_cube_sub_segment_le
    (k : Fin 3) (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    ‖(inner ℂ (fourierLp 2 0)
          ((gaussPrincipalStepBlock (by omega : 1 ≤ 3) k p hp i ^ (3 : ℕ))
            (fourierLp 2 0)) : ℂ) -
      ((gaussAmplitudeSegment (p : ℝ) 3
        (Int.fract (gaussSamplePhase 3 p i)) : ℝ) : ℂ)‖ ≤
      gaussCubicRelativeFactor k p hp i := le_rfl

theorem tendsto_gaussCubicRelativeFactor (k : Fin 3) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ => gaussCubicRelativeFactor k p hp (ι n)) atTop (nhds 0) := by
  have h := tendsto_norm_inner_one_gaussPrincipalStep_cube_sub_movingAmplitude_cube
    k p hp hι
  refine h.congr fun n => ?_
  rw [gaussCubicRelativeFactor]
  have hs0 := Int.fract_nonneg (gaussSamplePhase 3 p (ι n))
  have hs1 := Int.fract_lt_one (gaussSamplePhase 3 p (ι n))
  have hδ : ((gaussSamplePhase 3 p (ι n) : ℝ) : AddCircle (1 : ℝ)) =
      ((Int.fract (gaussSamplePhase 3 p (ι n)) : ℝ) : AddCircle (1 : ℝ)) :=
    (coe_fract_eq _).symm
  rw [hδ, inner_one_gaussMovingAmplitude_cube_eq_segment hp hs0 hs1]

/-- **The logarithmic mean of the two-sided cubic Fourier diagonal of a three-fold Gauss
component.**  The limit is the exact critical residue of the principal model, for the operator
itself. -/
theorem tendsto_gaussCubicFourierDiagonal_logResidue (k : Fin 3) (p : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N,
        ((inner ℂ (fourierLp 2 ((n : ℤ) + 1))
            ((gaussQuasiInnerGFull (by omega : 1 ≤ 3) k p ^ (3 : ℕ)) (fourierLp 2 ((n : ℤ) + 1))) : ℂ) +
          inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
            ((gaussQuasiInnerGFull (by omega : 1 ≤ 3) k p ^ (3 : ℕ))
              (fourierLp 2 (-((n : ℤ) + 1)))))) / (Real.log N : ℂ))
      atTop (nhds ((2 * ((p : ℝ) ^ (3 : ℕ) - 1) ^ (2 : ℕ) / (9 * Real.log (p : ℝ)) : ℝ) : ℂ)) := by
  have hm : (1 : ℕ) ≤ 3 := by omega
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp
  have harch : (0 : ℝ) ≤ gaussArchScale 3 ^ (2 * 3) :=
    pow_nonneg (gaussArchScale_pos hm).le _
  obtain ⟨C, hC0, hCb⟩ := exists_norm_gaussSampleValue_pow_mul_succ_le hm k p
  set F : ℤ → ℝ := fun i => gaussCubicRelativeFactor k p hp i with hF
  have hFnn : ∀ i : ℤ, 0 ≤ F i := fun i => gaussCubicRelativeFactor_nonneg k p hp i
  have hιp : Tendsto (fun n : ℕ => (((n : ℤ) + 1)).natAbs) atTop atTop := by
    refine (Filter.tendsto_add_atTop_nat 1).congr fun n => ?_
    omega
  have hιm : Tendsto (fun n : ℕ => ((-((n : ℤ) + 1))).natAbs) atTop atTop := by
    refine (Filter.tendsto_add_atTop_nat 1).congr fun n => ?_
    omega
  have hFp : Tendsto (fun n : ℕ => F ((n : ℤ) + 1)) atTop (nhds 0) :=
    tendsto_gaussCubicRelativeFactor k p hp hιp
  have hFm : Tendsto (fun n : ℕ => F (-((n : ℤ) + 1))) atTop (nhds 0) :=
    tendsto_gaussCubicRelativeFactor k p hp hιm
  set S : ℕ → ℂ := fun n =>
    (inner ℂ (fourierLp 2 ((n : ℤ) + 1))
        ((gaussQuasiInnerGFull hm k p ^ (3 : ℕ)) (fourierLp 2 ((n : ℤ) + 1))) : ℂ) +
      inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
        ((gaussQuasiInnerGFull hm k p ^ (3 : ℕ)) (fourierLp 2 (-((n : ℤ) + 1)))) with hSdef
  set err : ℕ → ℂ := fun n => S n - gaussPrincipalDiagonalTerm k p n with herrdef
  -- the diagonal of `G³` at a nonzero frequency is the cubed step scalar times `⟨1, R³·1⟩`
  have hdiag : ∀ i : ℤ, i ≠ 0 →
      (inner ℂ (fourierLp 2 i)
          ((gaussQuasiInnerG hm k p ^ (3 : ℕ)) (fourierLp 2 i)) : ℂ)
        = ((((p : ℝ) : ℂ) *
              (starRingEnd ℂ (gaussSampleValue k p i) * gaussSampleValue k p i)) ^ (3 : ℕ)) *
            inner ℂ (fourierLp 2 0)
              ((gaussPrincipalStepBlock hm k p hp i ^ (3 : ℕ)) (fourierLp 2 0)) := by
    intro i hi
    have hblock := gaussQuasiInnerG_pow_fourierMulBlock hm k p hp hi (fourierLp 2 0) 3
    rw [← fourierMulBlock_fourierLp_zero i, hblock, inner_smul_right,
      fourierMulBlock_inner]
  -- the pointwise relative bound
  have hbound : ∀ n : ℕ, ((n : ℝ) + 1) * ‖err n‖
      ≤ gaussArchScale 3 ^ (2 * 3) * ((p : ℝ) ^ (3 : ℕ) * C) *
        (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) := by
    intro n
    have hip : ((n : ℤ) + 1) ≠ 0 := by omega
    have him : (-((n : ℤ) + 1)) ≠ 0 := by omega
    have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    set σ : ℂ := ((p : ℝ) : ℂ) *
      (starRingEnd ℂ (gaussSampleValue k p ((n : ℤ) + 1)) *
        gaussSampleValue k p ((n : ℤ) + 1)) with hσ
    set X : ℂ := (inner ℂ (fourierLp 2 ((n : ℤ) + 1))
        ((gaussQuasiInnerG hm k p ^ (3 : ℕ)) (fourierLp 2 ((n : ℤ) + 1))) : ℂ) -
      σ ^ (3 : ℕ) * ((gaussAmplitudeSegment (p : ℝ) 3
          (Int.fract (gaussSamplePhase 3 p ((n : ℤ) + 1))) : ℝ) : ℂ) with hX
    set Y : ℂ := (inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
        ((gaussQuasiInnerG hm k p ^ (3 : ℕ)) (fourierLp 2 (-((n : ℤ) + 1)))) : ℂ) -
      (((p : ℝ) : ℂ) *
          (starRingEnd ℂ (gaussSampleValue k p (-((n : ℤ) + 1))) *
            gaussSampleValue k p (-((n : ℤ) + 1)))) ^ (3 : ℕ) *
        ((gaussAmplitudeSegment (p : ℝ) 3
          (Int.fract (gaussSamplePhase 3 p (-((n : ℤ) + 1)))) : ℝ) : ℂ) with hY
    have hsplit : err n = ((gaussArchScale 3 ^ (2 * 3) : ℝ) : ℂ) * (X + Y) := by
      have hpdt := gaussPrincipalDiagonalTerm_eq hm k p n
      have hval1 := inner_gaussQuasiInnerGFull_pow hm k p 3 ((n : ℤ) + 1)
      have hval2 := inner_gaussQuasiInnerGFull_pow hm k p 3 (-((n : ℤ) + 1))
      have hphase : gaussSamplePhase 3 p (-((n : ℤ) + 1))
          = gaussSamplePhase 3 p ((n : ℤ) + 1) := gaussSamplePhase_neg 3 p _
      show S n - gaussPrincipalDiagonalTerm k p n
          = ((gaussArchScale 3 ^ (2 * 3) : ℝ) : ℂ) * (X + Y)
      rw [← hpdt]
      simp only [hSdef]
      rw [hval1, hval2]
      simp only [hX, hY, hσ, hphase]
      rw [gaussSampleValue_neg, Complex.conj_conj]
      ring
    have hscalar : ‖σ ^ (3 : ℕ)‖ * ((n : ℝ) + 1) ≤ (p : ℝ) ^ (3 : ℕ) * C := by
      have hnormσ : ‖σ‖ = (p : ℝ) * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 : ℕ) := by
        rw [hσ, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hppos, RCLike.norm_conj]
        ring
      have hCn := hCb n
      rw [norm_pow, hnormσ]
      calc ((p : ℝ) * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 : ℕ)) ^ (3 : ℕ) * ((n : ℝ) + 1)
          = (p : ℝ) ^ (3 : ℕ) *
            (‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * 3) * ((n : ℝ) + 1)) := by
            ring
        _ ≤ (p : ℝ) ^ (3 : ℕ) * C := by
            exact mul_le_mul_of_nonneg_left hCn (by positivity)
    have hXbound : ‖X‖ ≤ ‖σ ^ (3 : ℕ)‖ * F ((n : ℤ) + 1) := by
      have hd := hdiag ((n : ℤ) + 1) hip
      have hrel := norm_inner_one_gaussPrincipalStep_cube_sub_segment_le k p hp ((n : ℤ) + 1)
      calc ‖X‖ = ‖σ ^ (3 : ℕ) *
            ((inner ℂ (fourierLp 2 0)
                ((gaussPrincipalStepBlock hm k p hp ((n : ℤ) + 1) ^ (3 : ℕ))
                  (fourierLp 2 0)) : ℂ) -
              ((gaussAmplitudeSegment (p : ℝ) 3
                (Int.fract (gaussSamplePhase 3 p ((n : ℤ) + 1))) : ℝ) : ℂ))‖ := by
            rw [hX, hd, hσ, mul_sub]
        _ = ‖σ ^ (3 : ℕ)‖ * ‖(inner ℂ (fourierLp 2 0)
              ((gaussPrincipalStepBlock hm k p hp ((n : ℤ) + 1) ^ (3 : ℕ))
                (fourierLp 2 0)) : ℂ) -
              ((gaussAmplitudeSegment (p : ℝ) 3
                (Int.fract (gaussSamplePhase 3 p ((n : ℤ) + 1))) : ℝ) : ℂ)‖ := norm_mul _ _
        _ ≤ ‖σ ^ (3 : ℕ)‖ * F ((n : ℤ) + 1) :=
            mul_le_mul_of_nonneg_left hrel (norm_nonneg _)
    have hσm : ‖(((p : ℝ) : ℂ) *
        (starRingEnd ℂ (gaussSampleValue k p (-((n : ℤ) + 1))) *
          gaussSampleValue k p (-((n : ℤ) + 1)))) ^ (3 : ℕ)‖ = ‖σ ^ (3 : ℕ)‖ := by
      rw [norm_pow, norm_pow]
      congr 1
      rw [hσ, norm_mul, norm_mul, norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj,
        gaussSampleValue_neg, RCLike.norm_conj]
    have hYbound : ‖Y‖ ≤ ‖σ ^ (3 : ℕ)‖ * F (-((n : ℤ) + 1)) := by
      have hd := hdiag (-((n : ℤ) + 1)) him
      have hrel := norm_inner_one_gaussPrincipalStep_cube_sub_segment_le k p hp (-((n : ℤ) + 1))
      calc ‖Y‖ = ‖(((p : ℝ) : ℂ) *
            (starRingEnd ℂ (gaussSampleValue k p (-((n : ℤ) + 1))) *
              gaussSampleValue k p (-((n : ℤ) + 1)))) ^ (3 : ℕ)‖ *
            ‖(inner ℂ (fourierLp 2 0)
                ((gaussPrincipalStepBlock hm k p hp (-((n : ℤ) + 1)) ^ (3 : ℕ))
                  (fourierLp 2 0)) : ℂ) -
              ((gaussAmplitudeSegment (p : ℝ) 3
                (Int.fract (gaussSamplePhase 3 p (-((n : ℤ) + 1)))) : ℝ) : ℂ)‖ := by
            rw [hY, hd, ← mul_sub, norm_mul]
        _ ≤ ‖σ ^ (3 : ℕ)‖ * F (-((n : ℤ) + 1)) := by
            rw [hσm]
            exact mul_le_mul_of_nonneg_left hrel (norm_nonneg _)
    have hFsum : (0 : ℝ) ≤ F ((n : ℤ) + 1) + F (-((n : ℤ) + 1)) :=
      add_nonneg (hFnn _) (hFnn _)
    calc ((n : ℝ) + 1) * ‖err n‖
        ≤ ((n : ℝ) + 1) * (gaussArchScale 3 ^ (2 * 3) * (‖X‖ + ‖Y‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hnn
          rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg harch]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) harch
      _ ≤ ((n : ℝ) + 1) * (gaussArchScale 3 ^ (2 * 3) *
            (‖σ ^ (3 : ℕ)‖ * (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ harch) hnn
          calc ‖X‖ + ‖Y‖ ≤ ‖σ ^ (3 : ℕ)‖ * F ((n : ℤ) + 1) + ‖σ ^ (3 : ℕ)‖ * F (-((n : ℤ) + 1)) :=
                add_le_add hXbound hYbound
            _ = ‖σ ^ (3 : ℕ)‖ * (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) := by ring
      _ = gaussArchScale 3 ^ (2 * 3) * (‖σ ^ (3 : ℕ)‖ * ((n : ℝ) + 1)) *
            (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) := by ring
      _ ≤ gaussArchScale 3 ^ (2 * 3) * ((p : ℝ) ^ (3 : ℕ) * C) *
            (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hscalar harch) hFsum
  -- the weighted error vanishes, and the model supplies the residue
  have hbig : Tendsto (fun n : ℕ =>
      gaussArchScale 3 ^ (2 * 3) * ((p : ℝ) ^ (3 : ℕ) * C) *
        (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1)))) atTop (nhds 0) := by
    have hsum := hFp.add hFm
    rw [add_zero] at hsum
    have := hsum.const_mul (gaussArchScale 3 ^ (2 * 3) * ((p : ℝ) ^ (3 : ℕ) * C))
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
  have hval : ((2 * ((p : ℝ) ^ (3 : ℕ) - 1) ^ (2 : ℕ) /
      (((3 : ℕ) : ℝ) ^ (2 : ℕ) * Real.log (p : ℝ)) : ℝ) : ℂ)
      = ((2 * ((p : ℝ) ^ (3 : ℕ) - 1) ^ (2 : ℕ) / (9 * Real.log (p : ℝ)) : ℝ) : ℂ) := by
    norm_num
  rw [hval] at hPDT
  have hsum := hPDT.add herr
  rw [add_zero] at hsum
  refine hsum.congr fun N => ?_
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  show gaussPrincipalDiagonalTerm k p n + (S n - gaussPrincipalDiagonalTerm k p n) = S n
  ring

/-! ## The local factor -/

/-- Formula (A) for the operator at `m = 3`: restoring the local-factor coefficient gives the
exact critical channel residue. -/
theorem tendsto_gaussCubicLocalDiagonal_logResidue (k : Fin 3) (p : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      ((gaussLocalFactorWeight 3 p : ℝ) : ℂ) *
        ((∑ n ∈ Finset.range N,
          ((inner ℂ (fourierLp 2 ((n : ℤ) + 1))
              ((gaussQuasiInnerGFull (by omega : 1 ≤ 3) k p ^ (3 : ℕ))
                (fourierLp 2 ((n : ℤ) + 1))) : ℂ) +
            inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
              ((gaussQuasiInnerGFull (by omega : 1 ≤ 3) k p ^ (3 : ℕ))
                (fourierLp 2 (-((n : ℤ) + 1)))))) / (Real.log N : ℂ)))
      atTop (nhds ((gaussChannelResidue 3 p : ℝ) : ℂ)) := by
  have hbase := (tendsto_gaussCubicFourierDiagonal_logResidue k p).const_mul
    ((gaussLocalFactorWeight 3 p : ℝ) : ℂ)
  have hval : ((gaussLocalFactorWeight 3 p : ℝ) : ℂ) *
      ((2 * ((p : ℝ) ^ (3 : ℕ) - 1) ^ (2 : ℕ) / (9 * Real.log (p : ℝ)) : ℝ) : ℂ) =
      ((gaussChannelResidue 3 p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    have h := gaussLocalFactorWeight_mul_principalResidue (by omega : 1 ≤ 3) p
    norm_num at h
    rw [← h]
  rwa [hval] at hbase

end

end RHTower
