import GaloisForLFunctions.RHTower.GaussRelativeOneStep
import GaloisForLFunctions.RHTower.GaussDiagonalLogResidue

/-!
# The logarithmic mean of the squared Fourier diagonal at `m = 2`

For the two-fold Gauss component the critical power of the quasi-inner block is the square, and
its Fourier diagonal folds through the self-adjointness of the principal step:

`⟨e_i, G² e_i⟩ = σ² ⟨1, R² 1⟩ = σ² ‖R·1‖²`.

The relative one-step law makes `‖R·1‖²` converge to the exact period average `A₂(δ_i)` with no
step scalar in front, so the deviation of the diagonal from the principal model is the step
scalar squared — of harmonic size — times a vanishing factor.  A harmonically weighted vanishing
error has partial sums `o(log N)`, and the model's logarithmic mean is the exact critical
residue.  This closes formula (A) for the operator at `m = 2`.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology

open GaloisForLFunctions.RHTower

noncomputable section

/-! ## The sampled energy decays harmonically at every order -/

theorem exists_norm_gaussSampleValue_pow_mul_succ_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * m) * ((n : ℝ) + 1) ≤ C := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_gaussComponentPrimeMagnitudeEnergy_bounds hm k p
  have harch : 0 < gaussArchConst m := gaussArchConst_pos hm
  refine ⟨C / gaussArchConst m, by positivity, fun n => ?_⟩
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hub := (hb n).2
  rw [gaussComponentPrimeMagnitudeEnergy_eq hm k p n, le_div_iff₀ hden] at hub
  rw [le_div_iff₀ harch]
  calc ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * m) * ((n : ℝ) + 1) * gaussArchConst m
      = gaussArchConst m * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * m) * ((n : ℝ) + 1) := by
        ring
    _ ≤ C := hub

/-! ## The squared diagonal folds through self-adjointness -/

/-- `⟨1, R²·1⟩` is the squared norm of `R·1`. -/
theorem inner_one_gaussPrincipalStep_sq {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    (inner ℂ (fourierLp 2 0)
        ((gaussPrincipalStepBlock hm k p hp i ^ 2) (fourierLp 2 0)) : ℂ)
      = ((‖gaussPrincipalStepBlock hm k p hp i (fourierLp 2 0)‖ ^ 2 : ℝ) : ℂ) := by
  have happ : (gaussPrincipalStepBlock hm k p hp i ^ 2) (fourierLp 2 0)
      = gaussPrincipalStepBlock hm k p hp i
          (gaussPrincipalStepBlock hm k p hp i (fourierLp 2 0)) := by
    rw [pow_two]
    rfl
  rw [happ, ← gaussPrincipalStepBlock_inner hm k p hp i (fourierLp 2 0),
    inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The squared norm of the moving-amplitude vector is the exact period average of the squared
amplitude. -/
theorem norm_sq_gaussMovingAmplitude_one {p : ℝ} (hp : 1 < p) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ((‖gaussMovingAmplitudeBlock hp ((s : ℝ) : AddCircle (1 : ℝ)) (fourierLp 2 0)‖ ^ 2 : ℝ) : ℂ)
      = ((gaussAmplitudeSegment p 2 s : ℝ) : ℂ) := by
  have happ : (gaussMovingAmplitudeBlock hp ((s : ℝ) : AddCircle (1 : ℝ)) ^ 2)
      (fourierLp 2 0)
      = gaussMovingAmplitudeBlock hp ((s : ℝ) : AddCircle (1 : ℝ))
          (gaussMovingAmplitudeBlock hp ((s : ℝ) : AddCircle (1 : ℝ)) (fourierLp 2 0)) := by
    rw [pow_two]
    rfl
  have hfold : ((‖gaussMovingAmplitudeBlock hp ((s : ℝ) : AddCircle (1 : ℝ))
      (fourierLp 2 0)‖ ^ 2 : ℝ) : ℂ)
      = inner ℂ (fourierLp 2 0)
          ((gaussMovingAmplitudeBlock hp ((s : ℝ) : AddCircle (1 : ℝ)) ^ 2)
            (fourierLp 2 0)) := by
    rw [happ, ← gaussMovingAmplitudeBlock_inner hp _ (fourierLp 2 0),
      inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hfold, GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff,
    fourierCoeff_gaussAmplitudeIterate_zero hp hs0 hs1 2]

/-! ## The relative factor -/

/-- The vanishing relative factor of the squared diagonal. -/
def gaussSquareRelativeFactor {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) : ℝ :=
  ‖gaussPrincipalStepBlock hm k p hp i (fourierLp 2 0) -
      gaussMovingAmplitudeBlock hp
        ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) (fourierLp 2 0)‖ *
    (‖gaussPrincipalStepBlock hm k p hp i (fourierLp 2 0) -
        gaussMovingAmplitudeBlock hp
          ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) (fourierLp 2 0)‖ + 2 * (p : ℝ))

theorem gaussSquareRelativeFactor_nonneg {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) : 0 ≤ gaussSquareRelativeFactor hm k p hp i := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rw [gaussSquareRelativeFactor]
  positivity

/-- Along every escaping frequency sequence the relative factor vanishes, for `m ≥ 2`. -/
theorem tendsto_gaussSquareRelativeFactor {m : ℕ} (hm2 : 2 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ =>
      gaussSquareRelativeFactor (le_trans one_le_two hm2) k p hp (ι n)) atTop (nhds 0) := by
  have hbase := tendsto_norm_gaussPrincipalStep_one_sub_amplitude hm2 k p hp hι
  have hsum := hbase.add (tendsto_const_nhds (x := 2 * (p : ℝ)) (f := (atTop : Filter ℕ)))
  rw [zero_add] at hsum
  have := hbase.mul hsum
  rw [zero_mul] at this
  exact this

/-- **Deviation of the squared scalar diagonal.**  The distance from `⟨1, R²·1⟩` to the exact
period average is at most the relative factor. -/
theorem norm_inner_one_gaussPrincipalStep_sq_sub_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    ‖(inner ℂ (fourierLp 2 0)
        ((gaussPrincipalStepBlock hm k p hp i ^ 2) (fourierLp 2 0)) : ℂ) -
      ((gaussAmplitudeSegment (p : ℝ) 2 (Int.fract (gaussSamplePhase m p i)) : ℝ) : ℂ)‖
      ≤ gaussSquareRelativeFactor hm k p hp i := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  set R1 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrincipalStepBlock hm k p hp i (fourierLp 2 0) with hR1
  set a : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussMovingAmplitudeBlock hp
      ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) (fourierLp 2 0) with ha
  have hδ : ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
      = ((Int.fract (gaussSamplePhase m p i) : ℝ) : AddCircle (1 : ℝ)) :=
    (coe_fract_eq _).symm
  have hs0 : 0 ≤ Int.fract (gaussSamplePhase m p i) := Int.fract_nonneg _
  have hs1 : Int.fract (gaussSamplePhase m p i) < 1 := Int.fract_lt_one _
  have hAval : ((gaussAmplitudeSegment (p : ℝ) 2 (Int.fract (gaussSamplePhase m p i)) : ℝ) : ℂ)
      = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [ha, hδ]
    exact (norm_sq_gaussMovingAmplitude_one hp hs0 hs1).symm
  rw [inner_one_gaussPrincipalStep_sq hm k p hp i, hAval, ← hR1, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  have hanorm : ‖a‖ ≤ (p : ℝ) := by
    rw [ha]
    refine ((gaussMovingAmplitudeBlock hp _).le_opNorm _).trans ?_
    rw [GaloisForLFunctions.norm_fourierLp_eq_one, mul_one]
    exact norm_gaussMovingAmplitudeBlock_le hp _
  have htri : ‖R1‖ ≤ ‖R1 - a‖ + ‖a‖ := by
    have h := norm_add_le (R1 - a) a
    rwa [sub_add_cancel] at h
  have habs : |‖R1‖ - ‖a‖| ≤ ‖R1 - a‖ := abs_norm_sub_norm_le R1 a
  have hfactor : |‖R1‖ ^ 2 - ‖a‖ ^ 2| = |‖R1‖ - ‖a‖| * (‖R1‖ + ‖a‖) := by
    rw [show ‖R1‖ ^ 2 - ‖a‖ ^ 2 = (‖R1‖ - ‖a‖) * (‖R1‖ + ‖a‖) from by ring, abs_mul,
      abs_of_nonneg (add_nonneg (norm_nonneg R1) (norm_nonneg a))]
  rw [gaussSquareRelativeFactor, ← hR1, ← ha, hfactor]
  have hsum : ‖R1‖ + ‖a‖ ≤ ‖R1 - a‖ + 2 * (p : ℝ) := by
    have := norm_nonneg (R1 - a)
    linarith
  exact mul_le_mul habs hsum (by positivity) (norm_nonneg _)

/-! ## The logarithmic mean at `m = 2` -/

set_option maxHeartbeats 1000000 in
/-- **The logarithmic mean of the two-sided squared Fourier diagonal of a two-fold Gauss
component.**  The limit is the exact critical residue of the principal model, for the operator
itself. -/
theorem tendsto_gaussSquareFourierDiagonal_logResidue (k : Fin 2) (p : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N,
        ((inner ℂ (fourierLp 2 ((n : ℤ) + 1))
            ((gaussQuasiInnerGFull one_le_two k p ^ 2) (fourierLp 2 ((n : ℤ) + 1))) : ℂ) +
          inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
            ((gaussQuasiInnerGFull one_le_two k p ^ 2)
              (fourierLp 2 (-((n : ℤ) + 1)))))) / (Real.log N : ℂ))
      atTop (nhds ((2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (4 * Real.log (p : ℝ)) : ℝ) : ℂ)) := by
  have hm : (1 : ℕ) ≤ 2 := one_le_two
  have hm2 : (2 : ℕ) ≤ 2 := le_refl 2
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp
  have harch : (0 : ℝ) ≤ gaussArchScale 2 ^ (2 * 2) :=
    pow_nonneg (gaussArchScale_pos hm).le _
  obtain ⟨C, hC0, hCb⟩ := exists_norm_gaussSampleValue_pow_mul_succ_le hm k p
  set F : ℤ → ℝ := fun i => gaussSquareRelativeFactor hm k p hp i with hF
  have hFnn : ∀ i : ℤ, 0 ≤ F i := fun i => gaussSquareRelativeFactor_nonneg hm k p hp i
  have hιp : Tendsto (fun n : ℕ => (((n : ℤ) + 1)).natAbs) atTop atTop := by
    refine (Filter.tendsto_add_atTop_nat 1).congr fun n => ?_
    omega
  have hιm : Tendsto (fun n : ℕ => ((-((n : ℤ) + 1))).natAbs) atTop atTop := by
    refine (Filter.tendsto_add_atTop_nat 1).congr fun n => ?_
    omega
  have hFp : Tendsto (fun n : ℕ => F ((n : ℤ) + 1)) atTop (nhds 0) :=
    tendsto_gaussSquareRelativeFactor hm2 k p hp hιp
  have hFm : Tendsto (fun n : ℕ => F (-((n : ℤ) + 1))) atTop (nhds 0) :=
    tendsto_gaussSquareRelativeFactor hm2 k p hp hιm
  set S : ℕ → ℂ := fun n =>
    (inner ℂ (fourierLp 2 ((n : ℤ) + 1))
        ((gaussQuasiInnerGFull hm k p ^ 2) (fourierLp 2 ((n : ℤ) + 1))) : ℂ) +
      inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
        ((gaussQuasiInnerGFull hm k p ^ 2) (fourierLp 2 (-((n : ℤ) + 1)))) with hSdef
  set err : ℕ → ℂ := fun n => S n - gaussPrincipalDiagonalTerm k p n with herrdef
  -- the diagonal of `G²` at a nonzero frequency is the squared step scalar times `⟨1, R²·1⟩`
  have hdiag : ∀ i : ℤ, i ≠ 0 →
      (inner ℂ (fourierLp 2 i)
          ((gaussQuasiInnerG hm k p ^ 2) (fourierLp 2 i)) : ℂ)
        = ((((p : ℝ) : ℂ) *
              (starRingEnd ℂ (gaussSampleValue k p i) * gaussSampleValue k p i)) ^ 2) *
            inner ℂ (fourierLp 2 0)
              ((gaussPrincipalStepBlock hm k p hp i ^ 2) (fourierLp 2 0)) := by
    intro i hi
    have hblock := gaussQuasiInnerG_pow_fourierMulBlock hm k p hp hi (fourierLp 2 0) 2
    rw [← fourierMulBlock_fourierLp_zero i, hblock, inner_smul_right,
      fourierMulBlock_inner]
  -- the pointwise relative bound
  have hbound : ∀ n : ℕ, ((n : ℝ) + 1) * ‖err n‖
      ≤ gaussArchScale 2 ^ (2 * 2) * ((p : ℝ) ^ 2 * C) *
        (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) := by
    intro n
    have hip : ((n : ℤ) + 1) ≠ 0 := by omega
    have him : (-((n : ℤ) + 1)) ≠ 0 := by omega
    have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    set σ : ℂ := ((p : ℝ) : ℂ) *
      (starRingEnd ℂ (gaussSampleValue k p ((n : ℤ) + 1)) *
        gaussSampleValue k p ((n : ℤ) + 1)) with hσ
    set X : ℂ := (inner ℂ (fourierLp 2 ((n : ℤ) + 1))
        ((gaussQuasiInnerG hm k p ^ 2) (fourierLp 2 ((n : ℤ) + 1))) : ℂ) -
      σ ^ 2 * ((gaussAmplitudeSegment (p : ℝ) 2
          (Int.fract (gaussSamplePhase 2 p ((n : ℤ) + 1))) : ℝ) : ℂ) with hX
    set Y : ℂ := (inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
        ((gaussQuasiInnerG hm k p ^ 2) (fourierLp 2 (-((n : ℤ) + 1)))) : ℂ) -
      (((p : ℝ) : ℂ) *
          (starRingEnd ℂ (gaussSampleValue k p (-((n : ℤ) + 1))) *
            gaussSampleValue k p (-((n : ℤ) + 1)))) ^ 2 *
        ((gaussAmplitudeSegment (p : ℝ) 2
          (Int.fract (gaussSamplePhase 2 p (-((n : ℤ) + 1)))) : ℝ) : ℂ) with hY
    have hsplit : err n = ((gaussArchScale 2 ^ (2 * 2) : ℝ) : ℂ) * (X + Y) := by
      have hpdt := gaussPrincipalDiagonalTerm_eq hm k p n
      have hval1 := inner_gaussQuasiInnerGFull_pow hm k p 2 ((n : ℤ) + 1)
      have hval2 := inner_gaussQuasiInnerGFull_pow hm k p 2 (-((n : ℤ) + 1))
      have hphase : gaussSamplePhase 2 p (-((n : ℤ) + 1))
          = gaussSamplePhase 2 p ((n : ℤ) + 1) := gaussSamplePhase_neg 2 p _
      show S n - gaussPrincipalDiagonalTerm k p n
          = ((gaussArchScale 2 ^ (2 * 2) : ℝ) : ℂ) * (X + Y)
      rw [← hpdt]
      simp only [hSdef]
      rw [hval1, hval2]
      simp only [hX, hY, hσ, hphase]
      rw [gaussSampleValue_neg, Complex.conj_conj]
      ring
    have hscalar : ‖σ ^ 2‖ * ((n : ℝ) + 1) ≤ (p : ℝ) ^ 2 * C := by
      have hnormσ : ‖σ‖ = (p : ℝ) * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ 2 := by
        rw [hσ, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hppos, RCLike.norm_conj]
        ring
      have hCn := hCb n
      rw [norm_pow, hnormσ]
      calc ((p : ℝ) * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ 2) ^ 2 * ((n : ℝ) + 1)
          = (p : ℝ) ^ 2 *
            (‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * 2) * ((n : ℝ) + 1)) := by
            ring
        _ ≤ (p : ℝ) ^ 2 * C := by
            exact mul_le_mul_of_nonneg_left hCn (by positivity)
    have hXbound : ‖X‖ ≤ ‖σ ^ 2‖ * F ((n : ℤ) + 1) := by
      have hd := hdiag ((n : ℤ) + 1) hip
      have hrel := norm_inner_one_gaussPrincipalStep_sq_sub_le hm k p hp ((n : ℤ) + 1)
      calc ‖X‖ = ‖σ ^ 2 *
            ((inner ℂ (fourierLp 2 0)
                ((gaussPrincipalStepBlock hm k p hp ((n : ℤ) + 1) ^ 2)
                  (fourierLp 2 0)) : ℂ) -
              ((gaussAmplitudeSegment (p : ℝ) 2
                (Int.fract (gaussSamplePhase 2 p ((n : ℤ) + 1))) : ℝ) : ℂ))‖ := by
            rw [hX, hd, hσ, mul_sub]
        _ = ‖σ ^ 2‖ * ‖(inner ℂ (fourierLp 2 0)
              ((gaussPrincipalStepBlock hm k p hp ((n : ℤ) + 1) ^ 2)
                (fourierLp 2 0)) : ℂ) -
              ((gaussAmplitudeSegment (p : ℝ) 2
                (Int.fract (gaussSamplePhase 2 p ((n : ℤ) + 1))) : ℝ) : ℂ)‖ := norm_mul _ _
        _ ≤ ‖σ ^ 2‖ * F ((n : ℤ) + 1) :=
            mul_le_mul_of_nonneg_left hrel (norm_nonneg _)
    have hσm : ‖(((p : ℝ) : ℂ) *
        (starRingEnd ℂ (gaussSampleValue k p (-((n : ℤ) + 1))) *
          gaussSampleValue k p (-((n : ℤ) + 1)))) ^ 2‖ = ‖σ ^ 2‖ := by
      rw [norm_pow, norm_pow]
      congr 1
      rw [hσ, norm_mul, norm_mul, norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj,
        gaussSampleValue_neg, RCLike.norm_conj]
    have hYbound : ‖Y‖ ≤ ‖σ ^ 2‖ * F (-((n : ℤ) + 1)) := by
      have hd := hdiag (-((n : ℤ) + 1)) him
      have hrel := norm_inner_one_gaussPrincipalStep_sq_sub_le hm k p hp (-((n : ℤ) + 1))
      calc ‖Y‖ = ‖(((p : ℝ) : ℂ) *
            (starRingEnd ℂ (gaussSampleValue k p (-((n : ℤ) + 1))) *
              gaussSampleValue k p (-((n : ℤ) + 1)))) ^ 2‖ *
            ‖(inner ℂ (fourierLp 2 0)
                ((gaussPrincipalStepBlock hm k p hp (-((n : ℤ) + 1)) ^ 2)
                  (fourierLp 2 0)) : ℂ) -
              ((gaussAmplitudeSegment (p : ℝ) 2
                (Int.fract (gaussSamplePhase 2 p (-((n : ℤ) + 1)))) : ℝ) : ℂ)‖ := by
            rw [hY, hd, ← mul_sub, norm_mul]
        _ ≤ ‖σ ^ 2‖ * F (-((n : ℤ) + 1)) := by
            rw [hσm]
            exact mul_le_mul_of_nonneg_left hrel (norm_nonneg _)
    have hFsum : (0 : ℝ) ≤ F ((n : ℤ) + 1) + F (-((n : ℤ) + 1)) :=
      add_nonneg (hFnn _) (hFnn _)
    calc ((n : ℝ) + 1) * ‖err n‖
        ≤ ((n : ℝ) + 1) * (gaussArchScale 2 ^ (2 * 2) * (‖X‖ + ‖Y‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hnn
          rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg harch]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) harch
      _ ≤ ((n : ℝ) + 1) * (gaussArchScale 2 ^ (2 * 2) *
            (‖σ ^ 2‖ * (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ harch) hnn
          calc ‖X‖ + ‖Y‖ ≤ ‖σ ^ 2‖ * F ((n : ℤ) + 1) + ‖σ ^ 2‖ * F (-((n : ℤ) + 1)) :=
                add_le_add hXbound hYbound
            _ = ‖σ ^ 2‖ * (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) := by ring
      _ = gaussArchScale 2 ^ (2 * 2) * (‖σ ^ 2‖ * ((n : ℝ) + 1)) *
            (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) := by ring
      _ ≤ gaussArchScale 2 ^ (2 * 2) * ((p : ℝ) ^ 2 * C) *
            (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hscalar harch) hFsum
  -- the weighted error vanishes, and the model supplies the residue
  have hbig : Tendsto (fun n : ℕ =>
      gaussArchScale 2 ^ (2 * 2) * ((p : ℝ) ^ 2 * C) *
        (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1)))) atTop (nhds 0) := by
    have hsum := hFp.add hFm
    rw [add_zero] at hsum
    have := hsum.const_mul (gaussArchScale 2 ^ (2 * 2) * ((p : ℝ) ^ 2 * C))
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
  have hval : ((2 * ((p : ℝ) ^ (2 : ℕ) - 1) ^ 2 /
      (((2 : ℕ) : ℝ) ^ 2 * Real.log (p : ℝ)) : ℝ) : ℂ)
      = ((2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (4 * Real.log (p : ℝ)) : ℝ) : ℂ) := by
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

/-- **Formula (A) for the operator, at `m = 2`.**  Restoring the local-factor coefficient turns
the logarithmic mean of the squared Fourier diagonal into the exact critical residue
`2(p-1)⁴(p²-1)²/(4p⁴ log p)`. -/
theorem tendsto_gaussSquareLocalDiagonal_logResidue (k : Fin 2) (p : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      ((gaussLocalFactorWeight 2 p : ℝ) : ℂ) *
        ((∑ n ∈ Finset.range N,
          ((inner ℂ (fourierLp 2 ((n : ℤ) + 1))
              ((gaussQuasiInnerGFull one_le_two k p ^ 2) (fourierLp 2 ((n : ℤ) + 1))) : ℂ) +
            inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
              ((gaussQuasiInnerGFull one_le_two k p ^ 2)
                (fourierLp 2 (-((n : ℤ) + 1)))))) / (Real.log N : ℂ)))
      atTop (nhds ((gaussChannelResidue 2 p : ℝ) : ℂ)) := by
  have hbase := (tendsto_gaussSquareFourierDiagonal_logResidue k p).const_mul
    ((gaussLocalFactorWeight 2 p : ℝ) : ℂ)
  have hval : ((gaussLocalFactorWeight 2 p : ℝ) : ℂ) *
      ((2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (4 * Real.log (p : ℝ)) : ℝ) : ℂ)
      = ((gaussChannelResidue 2 p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    have h := gaussLocalFactorWeight_mul_principalResidue (one_le_two) p
    norm_num at h
    rw [← h]
  rwa [hval] at hbase

end

end RHTower
