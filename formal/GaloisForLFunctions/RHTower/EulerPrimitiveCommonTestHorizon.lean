import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestSource
import GaloisForLFunctions.RHTower.EulerPrimeCurrentClockLaw
import GaloisForLFunctions.RHTower.GammaCoPoissonReflectedIntervalCommonTest

/-!
# Normalized primitive Euler common-test horizon

This module constructs the finite-`σ` head/tail horizon of the retained-label
Euler source.  Each label `n` splits the universal Hardy half-line exactly at
its primitive action `log n`.  The compact head is the endpoint-dressed
Gamma/co-Poisson interval Gram; the translated tail is its Hardy semigroup
transport.

The normalized tail is a positive Schur Gram.  Multiplication by the
diverging Euler total removes probability normalization and exposes the
shifted critical primitive source exactly.  At `σ = 1` that source is the
critical label-time object from `EulerPrimitiveCommonTestSource`.
-/

open Complex MeasureTheory Set Matrix Filter
open scoped BigOperators ComplexOrder Topology

namespace RHTower

noncomputable section

/-- Symmetric spectral shift whose square produces the Euler density
`Λ(n)n^{-σ}` from the critical primitive amplitude. -/
def eulerPrimitiveHorizonShift (sigma : ℝ) (w : ℂ) : ℂ :=
  w + ((sigma - 1) / 2 : ℝ)

/-- Hardy tail multiplier attached to primitive action `log n`. -/
def eulerPrimitiveHorizonMultiplier (n : ℕ) (w : ℂ) : ℂ :=
  Complex.exp (-w * (Real.log n : ℂ))

/-- Tail transport in the `n` fibre. -/
def eulerPrimitiveHorizonTailTransportMatrix
    {N : ℕ} (n : ℕ) (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    eulerPrimitiveHorizonMultiplier n (w i) *
      rightHalfPlaneHardyCauchyGram w i j *
      star (eulerPrimitiveHorizonMultiplier n (w j))

/-- Compact head in the `n` fibre.  Reflection of the spectral packet is
forced by the completed functional equation. -/
def eulerPrimitiveHorizonHeadFibreMatrix
    {N : ℕ} (n : ℕ) (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  gammaCoPoissonReflectedIntervalMatrix (Real.log n)
    (fun i => 1 / 2 - star (w i))

theorem real_log_nat_nonneg (n : ℕ) : 0 ≤ Real.log n := by
  rcases n with _ | n
  · simp
  · exact Real.log_nonneg
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

theorem star_eulerPrimitiveHorizonMultiplier (n : ℕ) (w : ℂ) :
    star (eulerPrimitiveHorizonMultiplier n w) =
      Complex.exp (-(star w) * (Real.log n : ℂ)) := by
  rw [eulerPrimitiveHorizonMultiplier]
  change (starRingEnd ℂ) (Complex.exp (-w * (Real.log n : ℂ))) = _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal]
  rfl

theorem eulerPrimitiveHorizonMultiplier_eq_cpow_inv
    (n : ℕ) (hn : n ≠ 0) (w : ℂ) :
    eulerPrimitiveHorizonMultiplier n w = ((n : ℂ) ^ w)⁻¹ := by
  rw [eulerPrimitiveHorizonMultiplier,
    Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
    ← Complex.exp_neg]
  congr 1
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log hnpos.le]
  rw [hlog]
  ring

/-- Euler mass times two retained-label tail multipliers is exactly one
von-Mangoldt Dirichlet term at the jointly shifted coordinate. -/
theorem ofReal_eulerPrimeCurrentMass_mul_horizonMultipliers_eq
    (sigma : ℝ) (w v : ℂ) (n : ℕ) :
    ((eulerPrimeCurrentMass sigma n : ℝ) : ℂ) *
        eulerPrimitiveHorizonMultiplier n w *
        star (eulerPrimitiveHorizonMultiplier n v) =
      LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        ((sigma : ℂ) + w + star v) n := by
  by_cases hn : n = 0
  · subst n
    simp [eulerPrimeCurrentMass, LSeries.term]
  · rw [ofReal_eulerPrimeCurrentMass_eq,
      eulerPrimitiveHorizonMultiplier_eq_cpow_inv n hn w,
      star_eulerPrimitiveHorizonMultiplier]
    have hstarMultiplier :
        Complex.exp (-(star v) * (Real.log n : ℂ)) =
          ((n : ℂ) ^ (star v))⁻¹ :=
      eulerPrimitiveHorizonMultiplier_eq_cpow_inv n hn (star v)
    rw [hstarMultiplier]
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [Complex.cpow_add ((sigma : ℂ) + w) (star v)
        (Nat.cast_ne_zero.mpr hn),
      Complex.cpow_add (sigma : ℂ) w (Nat.cast_ne_zero.mpr hn)]
    field_simp

/-- Exact source-horizon split in every retained prime-power fibre. -/
theorem eulerPrimitiveHorizonHeadFibreMatrix_add_tail
    {N : ℕ} (n : ℕ) (w : Fin N → ℂ)
    (hw : ∀ i, 0 < (w i).re) :
    eulerPrimitiveHorizonHeadFibreMatrix n w +
        eulerPrimitiveHorizonTailTransportMatrix n w =
      rightHalfPlaneHardyCauchyGram w := by
  ext i j
  let s : ℂ := w i + star (w j)
  have hsre : 0 < s.re := by
    dsimp only [s]
    change 0 < (w i).re + (w j).re
    linarith [hw i, hw j]
  have hs : s ≠ 0 := by
    intro hs0
    rw [hs0] at hsre
    exact (lt_irrefl 0) hsre
  rw [Matrix.add_apply]
  change
    gammaCoPoissonReflectedIntervalKernel (Real.log n)
        (1 / 2 - star (w j)) (1 / 2 - star (w i)) +
      eulerPrimitiveHorizonTailTransportMatrix n w i j =
        rightHalfPlaneHardyCauchyGram w i j
  rw [gammaCoPoissonReflectedIntervalKernel_eq_integral
    (real_log_nat_nonneg n)]
  rw [eulerPrimitiveHorizonTailTransportMatrix,
    rightHalfPlaneHardyCauchyGram,
    star_eulerPrimitiveHorizonMultiplier]
  have hexponent :
      (1 / 2 - star (w j)) +
          (starRingEnd ℂ) (1 / 2 - star (w i)) - 1 = -s := by
    dsimp only [s]
    have hhalf :
        (starRingEnd ℂ) (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
      apply Complex.ext <;> norm_num
    rw [map_sub, hhalf]
    change
      1 / 2 - star (w j) +
          (1 / 2 - (starRingEnd ℂ) ((starRingEnd ℂ) (w i))) - 1 =
        -(w i + star (w j))
    rw [starRingEnd_self_apply]
    ring
  rw [hexponent, integral_exp_mul_complex (neg_ne_zero.mpr hs)]
  rw [eulerPrimitiveHorizonMultiplier]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  change
    (Complex.exp (-s * (Real.log n : ℂ)) - 1) / (-s) +
      Complex.exp (-(w i) * (Real.log n : ℂ)) * (1 / s) *
        Complex.exp (-(star (w j)) * (Real.log n : ℂ)) = 1 / s
  rw [show
    Complex.exp (-(w i) * (Real.log n : ℂ)) * (1 / s) *
        Complex.exp (-(star (w j)) * (Real.log n : ℂ)) =
      (1 / s) *
        (Complex.exp (-(w i) * (Real.log n : ℂ)) *
          Complex.exp (-(star (w j)) * (Real.log n : ℂ))) by ring,
    ← Complex.exp_add]
  have hadd :
      -(w i) * (Real.log n : ℂ) +
          -(star (w j)) * (Real.log n : ℂ) =
        -s * (Real.log n : ℂ) := by
    dsimp only [s]
    ring
  rw [hadd]
  field_simp [hs]
  ring

theorem eulerPrimitiveHorizonHeadFibreMatrix_posSemidef
    {N : ℕ} (n : ℕ) (w : Fin N → ℂ) :
    (eulerPrimitiveHorizonHeadFibreMatrix n w).PosSemidef :=
  gammaCoPoissonReflectedIntervalMatrix_posSemidef _ _

/-- Unnormalized shifted tail.  Prime-power and Hardy coordinates remain
separate tensor factors. -/
def eulerPrimitiveHorizonShiftedTailGram
    {N : ℕ} (sigma : ℝ) (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (vonMangoldtPrimeRightHalfPlaneGram
      (fun i => eulerPrimitiveHorizonShift sigma (w i))) ⊙
    rightHalfPlaneHardyCauchyGram w

/-- Probability-normalized Euler tail at `σ > 1`. -/
def eulerPrimitiveHorizonTailGram
    {N : ℕ} (sigma : ℝ) (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (((eulerPrimeCurrentTotal sigma : ℝ) : ℂ)⁻¹) •
    eulerPrimitiveHorizonShiftedTailGram sigma w

/-- Complementary head of the normalized horizon.  Its independent source
realization is obtained by mixing the positive compact head fibres. -/
def eulerPrimitiveHorizonHeadGram
    {N : ℕ} (sigma : ℝ) (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  rightHalfPlaneHardyCauchyGram w -
    eulerPrimitiveHorizonTailGram sigma w

theorem eulerPrimitiveHorizonShift_re
    (sigma : ℝ) (w : ℂ) :
    (eulerPrimitiveHorizonShift sigma w).re =
      w.re + (sigma - 1) / 2 := by
  simp [eulerPrimitiveHorizonShift]

theorem eulerPrimitiveHorizonShiftedTailGram_posSemidef
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    (eulerPrimitiveHorizonShiftedTailGram sigma w).PosSemidef := by
  apply Matrix.PosSemidef.hadamard
  · apply vonMangoldtPrimeRightHalfPlaneGram_posSemidef
    intro i
    rw [eulerPrimitiveHorizonShift_re]
    linarith [hw i]
  · exact rightHalfPlaneHardyCauchyGram_posSemidef hw

theorem eulerPrimitiveHorizonTailGram_posSemidef
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    (eulerPrimitiveHorizonTailGram sigma w).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact eulerPrimitiveHorizonShiftedTailGram_posSemidef hsigma w hw
  · apply Complex.nonneg_iff.mpr
    constructor
    · have hpos : 0 < (eulerPrimeCurrentTotal sigma)⁻¹ :=
        inv_pos.mpr (eulerPrimeCurrentTotal_pos hsigma)
      simpa using hpos.le
    · simp

/-- Pole normalization removes the probability denominator exactly. -/
theorem eulerPrimitiveHorizon_poleNormal_tail
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (w : Fin N → ℂ) :
    ((eulerPrimeCurrentTotal sigma : ℝ) : ℂ) •
        eulerPrimitiveHorizonTailGram sigma w =
      eulerPrimitiveHorizonShiftedTailGram sigma w := by
  rw [eulerPrimitiveHorizonTailGram, smul_smul]
  have hne : ((eulerPrimeCurrentTotal sigma : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (eulerPrimeCurrentTotal_pos hsigma))
  rw [mul_inv_cancel₀ hne, one_smul]

theorem eulerPrimitiveHorizonShift_one (w : ℂ) :
    eulerPrimitiveHorizonShift 1 w = w := by
  simp [eulerPrimitiveHorizonShift]

/-- Exact critical endpoint of the pole-normalized source. -/
theorem eulerPrimitiveHorizonShiftedTailGram_one
    {N : ℕ} (w : Fin N → ℂ) :
    eulerPrimitiveHorizonShiftedTailGram 1 w =
      eulerPrimitiveCommonTestGram w := by
  simp [eulerPrimitiveHorizonShiftedTailGram,
    eulerPrimitiveCommonTestGram, eulerPrimitiveHorizonShift]

/-- Finite retained-label tail mixture. -/
def eulerPrimitiveHorizonPartialTailGram
    {N : ℕ} (sigma : ℝ) (M : ℕ) (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  ∑ n ∈ Finset.range M,
    (eulerPrimeCurrentProbability sigma n : ℂ) •
      eulerPrimitiveHorizonTailTransportMatrix n w

/-- Finite positive head mixture, including unspent probability mass in the
zero-action universal Hardy fibre. -/
def eulerPrimitiveHorizonPartialHeadSourceGram
    {N : ℕ} (sigma : ℝ) (M : ℕ) (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  ((1 - ∑ n ∈ Finset.range M,
      eulerPrimeCurrentProbability sigma n : ℝ) : ℂ) •
      rightHalfPlaneHardyCauchyGram w +
    ∑ n ∈ Finset.range M,
      (eulerPrimeCurrentProbability sigma n : ℂ) •
        eulerPrimitiveHorizonHeadFibreMatrix n w

theorem eulerPrimitiveHorizonPartialHeadSourceGram_posSemidef
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (M : ℕ) (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    (eulerPrimitiveHorizonPartialHeadSourceGram sigma M w).PosSemidef := by
  have hpartial :
      ∑ n ∈ Finset.range M, eulerPrimeCurrentProbability sigma n ≤ 1 := by
    calc
      ∑ n ∈ Finset.range M, eulerPrimeCurrentProbability sigma n ≤
          ∑' n : ℕ, eulerPrimeCurrentProbability sigma n :=
        Summable.sum_le_tsum
          (Finset.range M)
          (fun n _ => eulerPrimeCurrentProbability_nonneg hsigma n)
          (summable_eulerPrimeCurrentProbability hsigma)
      _ = 1 := tsum_eulerPrimeCurrentProbability hsigma
  apply Matrix.PosSemidef.add
  · apply Matrix.PosSemidef.smul
    · exact rightHalfPlaneHardyCauchyGram_posSemidef hw
    · apply Complex.nonneg_iff.mpr
      exact ⟨by simpa using sub_nonneg.mpr hpartial, by simp⟩
  · exact Finset.sum_induction _ _
      (fun _ _ => Matrix.PosSemidef.add)
      Matrix.PosSemidef.zero
      (fun n _ => by
        apply Matrix.PosSemidef.smul
        · exact eulerPrimitiveHorizonHeadFibreMatrix_posSemidef n w
        · apply Complex.nonneg_iff.mpr
          exact ⟨eulerPrimeCurrentProbability_nonneg hsigma n, by simp⟩)

theorem eulerPrimitiveHorizonPartialHeadSourceGram_add_tail
    {N : ℕ} {sigma : ℝ}
    (M : ℕ) (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    eulerPrimitiveHorizonPartialHeadSourceGram sigma M w +
        eulerPrimitiveHorizonPartialTailGram sigma M w =
      rightHalfPlaneHardyCauchyGram w := by
  ext i j
  simp only [eulerPrimitiveHorizonPartialHeadSourceGram,
    eulerPrimitiveHorizonPartialTailGram, Matrix.add_apply,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  have hsplit (n : ℕ) :
      eulerPrimitiveHorizonHeadFibreMatrix n w i j +
          eulerPrimitiveHorizonTailTransportMatrix n w i j =
        rightHalfPlaneHardyCauchyGram w i j := by
    exact congrArg (fun A => A i j)
      (eulerPrimitiveHorizonHeadFibreMatrix_add_tail n w hw)
  have hcombine :
      (∑ x ∈ Finset.range M,
          (eulerPrimeCurrentProbability sigma x : ℂ) *
            eulerPrimitiveHorizonHeadFibreMatrix x w i j) +
        ∑ x ∈ Finset.range M,
          (eulerPrimeCurrentProbability sigma x : ℂ) *
            eulerPrimitiveHorizonTailTransportMatrix x w i j =
      ∑ x ∈ Finset.range M,
        (eulerPrimeCurrentProbability sigma x : ℂ) *
          rightHalfPlaneHardyCauchyGram w i j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← mul_add, hsplit n]
  rw [add_assoc, hcombine]
  push_cast
  rw [← Finset.sum_mul]
  ring

theorem eulerPrimitiveHorizonProbability_tailTerm_eq
    {sigma : ℝ} (hsigma : 1 < sigma) (w v : ℂ) (n : ℕ) :
    (eulerPrimeCurrentProbability sigma n : ℂ) *
        eulerPrimitiveHorizonMultiplier n w *
        star (eulerPrimitiveHorizonMultiplier n v) =
      (((eulerPrimeCurrentTotal sigma : ℝ) : ℂ)⁻¹) *
        LSeries.term
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((sigma : ℂ) + w + star v) n := by
  rw [eulerPrimeCurrentProbability]
  push_cast
  have hne : ((eulerPrimeCurrentTotal sigma : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (eulerPrimeCurrentTotal_pos hsigma))
  calc
    ((eulerPrimeCurrentMass sigma n : ℝ) : ℂ) /
          ((eulerPrimeCurrentTotal sigma : ℝ) : ℂ) *
        eulerPrimitiveHorizonMultiplier n w *
        star (eulerPrimitiveHorizonMultiplier n v) =
      (((eulerPrimeCurrentTotal sigma : ℝ) : ℂ)⁻¹) *
        (((eulerPrimeCurrentMass sigma n : ℝ) : ℂ) *
          eulerPrimitiveHorizonMultiplier n w *
          star (eulerPrimitiveHorizonMultiplier n v)) := by
            field_simp [hne]
    _ = _ := by
      rw [ofReal_eulerPrimeCurrentMass_mul_horizonMultipliers_eq]

theorem summable_eulerPrimitiveHorizonWeightedTail_apply
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) (i j : Fin N) :
    Summable (fun n : ℕ =>
      ((eulerPrimeCurrentProbability sigma n : ℂ) •
        eulerPrimitiveHorizonTailTransportMatrix n w) i j) := by
  have hs :
      Summable (LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        ((sigma : ℂ) + w i + star (w j))) := by
    apply ArithmeticFunction.LSeriesSummable_vonMangoldt
    change 1 < sigma + (w i).re + (w j).re
    linarith [hw i, hw j]
  apply
    ((hs.mul_left (((eulerPrimeCurrentTotal sigma : ℝ) : ℂ)⁻¹)).mul_right
      (rightHalfPlaneHardyCauchyGram w i j)).congr
  intro n
  simp only [Matrix.smul_apply, smul_eq_mul,
    eulerPrimitiveHorizonTailTransportMatrix]
  symm
  calc
    (eulerPrimeCurrentProbability sigma n : ℂ) *
          (eulerPrimitiveHorizonMultiplier n (w i) *
            rightHalfPlaneHardyCauchyGram w i j *
            star (eulerPrimitiveHorizonMultiplier n (w j))) =
        ((eulerPrimeCurrentProbability sigma n : ℂ) *
            eulerPrimitiveHorizonMultiplier n (w i) *
            star (eulerPrimitiveHorizonMultiplier n (w j))) *
          rightHalfPlaneHardyCauchyGram w i j := by ring
    _ = _ := by
      rw [eulerPrimitiveHorizonProbability_tailTerm_eq hsigma]

/-- Infinite normalized tail mixture equals the shifted analytic source,
entry by entry. -/
theorem tsum_eulerPrimitiveHorizonWeightedTail_apply
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) (i j : Fin N) :
    (∑' n : ℕ,
      ((eulerPrimeCurrentProbability sigma n : ℂ) •
        eulerPrimitiveHorizonTailTransportMatrix n w) i j) =
      eulerPrimitiveHorizonTailGram sigma w i j := by
  have hs :
      Summable (LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        ((sigma : ℂ) + w i + star (w j))) := by
    apply ArithmeticFunction.LSeriesSummable_vonMangoldt
    change 1 < sigma + (w i).re + (w j).re
    linarith [hw i, hw j]
  rw [show
    (fun n : ℕ =>
      ((eulerPrimeCurrentProbability sigma n : ℂ) •
        eulerPrimitiveHorizonTailTransportMatrix n w) i j) =
      fun n : ℕ =>
        (((eulerPrimeCurrentTotal sigma : ℝ) : ℂ)⁻¹) *
          LSeries.term
            (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
            ((sigma : ℂ) + w i + star (w j)) n *
          rightHalfPlaneHardyCauchyGram w i j by
    funext n
    simp only [Matrix.smul_apply, smul_eq_mul,
      eulerPrimitiveHorizonTailTransportMatrix]
    calc
      (eulerPrimeCurrentProbability sigma n : ℂ) *
            (eulerPrimitiveHorizonMultiplier n (w i) *
              rightHalfPlaneHardyCauchyGram w i j *
              star (eulerPrimitiveHorizonMultiplier n (w j))) =
          ((eulerPrimeCurrentProbability sigma n : ℂ) *
              eulerPrimitiveHorizonMultiplier n (w i) *
              star (eulerPrimitiveHorizonMultiplier n (w j))) *
            rightHalfPlaneHardyCauchyGram w i j := by ring
      _ = _ := by
        rw [eulerPrimitiveHorizonProbability_tailTerm_eq hsigma],
    (hs.mul_left
      (((eulerPrimeCurrentTotal sigma : ℝ) : ℂ)⁻¹)).tsum_mul_right]
  rw [hs.tsum_mul_left]
  have hparameter :
      (sigma : ℂ) + w i + star (w j) =
        eulerPrimitiveHorizonShift sigma (w i) +
          star (eulerPrimitiveHorizonShift sigma (w j)) + 1 := by
    simp [eulerPrimitiveHorizonShift]
    ring
  have hseries :
      LSeries
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((sigma : ℂ) + w i + star (w j)) =
        vonMangoldtPrimeLaplaceChannelComplex
          (eulerPrimitiveHorizonShift sigma (w i) +
            star (eulerPrimitiveHorizonShift sigma (w j))) := by
    unfold vonMangoldtPrimeLaplaceChannelComplex
    rw [hparameter]
  have htsum :
      (∑' n : ℕ,
        LSeries.term
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((sigma : ℂ) + w i + star (w j)) n) =
        vonMangoldtPrimeLaplaceChannelComplex
          (eulerPrimitiveHorizonShift sigma (w i) +
            star (eulerPrimitiveHorizonShift sigma (w j))) := by
    change
      LSeries
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((sigma : ℂ) + w i + star (w j)) = _
    exact hseries
  rw [htsum]
  simp only [eulerPrimitiveHorizonTailGram,
    eulerPrimitiveHorizonShiftedTailGram, Matrix.smul_apply,
    Matrix.hadamard_apply, smul_eq_mul,
    vonMangoldtPrimeRightHalfPlaneGram]
  ring

theorem tendsto_eulerPrimitiveHorizonPartialTailGram
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    Tendsto (fun M => eulerPrimitiveHorizonPartialTailGram sigma M w)
      atTop (nhds (eulerPrimitiveHorizonTailGram sigma w)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hsum :=
    (summable_eulerPrimitiveHorizonWeightedTail_apply hsigma w hw i j).hasSum
  rw [tsum_eulerPrimitiveHorizonWeightedTail_apply hsigma w hw i j] at hsum
  simpa only [eulerPrimitiveHorizonPartialTailGram, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul] using hsum.tendsto_sum_nat

theorem tendsto_eulerPrimitiveHorizonPartialHeadSourceGram
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    Tendsto
      (fun M => eulerPrimitiveHorizonPartialHeadSourceGram sigma M w)
      atTop (nhds (eulerPrimitiveHorizonHeadGram sigma w)) := by
  have htail :=
    tendsto_eulerPrimitiveHorizonPartialTailGram hsigma w hw
  have hsub :
      Tendsto
        (fun M =>
          rightHalfPlaneHardyCauchyGram w -
            eulerPrimitiveHorizonPartialTailGram sigma M w)
        atTop (nhds (eulerPrimitiveHorizonHeadGram sigma w)) := by
    simpa [eulerPrimitiveHorizonHeadGram] using
      (tendsto_const_nhds.sub htail)
  apply hsub.congr'
  filter_upwards with M
  have hsplit :=
    eulerPrimitiveHorizonPartialHeadSourceGram_add_tail
      (sigma := sigma) M w hw
  rw [← hsplit]
  simp

/-- Both sides of the normalized infinite horizon are positive.  Head
positivity is inherited from the literal compact-fibre source, not postulated
for the analytic difference. -/
theorem eulerPrimitiveHorizonHeadGram_posSemidef
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    (eulerPrimitiveHorizonHeadGram sigma w).PosSemidef := by
  apply Matrix.PosSemidef.of_tendsto_complex
    (l := atTop)
    (A := fun M =>
      eulerPrimitiveHorizonPartialHeadSourceGram sigma M w)
  · exact Filter.Eventually.of_forall fun M =>
      eulerPrimitiveHorizonPartialHeadSourceGram_posSemidef
        hsigma M w hw
  · exact tendsto_eulerPrimitiveHorizonPartialHeadSourceGram hsigma w hw

/-- The resolved prime channel is continuous throughout its open
right-half-plane of absolute convergence. -/
theorem continuousAt_vonMangoldtPrimeLaplaceChannelComplex
    {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt vonMangoldtPrimeLaplaceChannelComplex s := by
  have habs :
      LSeries.abscissaOfAbsConv
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt
      (by simpa using hy)
  unfold vonMangoldtPrimeLaplaceChannelComplex
  have hL := (LSeries_hasDerivAt
    (lt_of_le_of_lt habs (by
      exact_mod_cast (show (1 : ℝ) < (s + 1).re by
        simp
        linarith)))).continuousAt
  have hadd : ContinuousAt (fun z : ℂ => z + 1) s := by
    fun_prop
  exact ContinuousAt.comp (x := s) hL hadd

/-- The pole-normal source has a genuine critical limit, not merely an
assigned endpoint value. -/
theorem tendsto_eulerPrimitiveHorizonShiftedTailGram_one
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    Tendsto (fun sigma : ℝ =>
        eulerPrimitiveHorizonShiftedTailGram sigma w)
      (nhds 1) (nhds (eulerPrimitiveCommonTestGram w)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let arg : ℝ → ℂ := fun sigma =>
    eulerPrimitiveHorizonShift sigma (w i) +
      star (eulerPrimitiveHorizonShift sigma (w j))
  have hargContinuous : ContinuousAt arg 1 := by
    dsimp only [arg, eulerPrimitiveHorizonShift]
    fun_prop
  have hre : 0 < (arg 1).re := by
    simp [arg, eulerPrimitiveHorizonShift]
    linarith [hw i, hw j]
  have hchannel :
      ContinuousAt
        (fun sigma =>
          vonMangoldtPrimeLaplaceChannelComplex (arg sigma))
        1 :=
    (continuousAt_vonMangoldtPrimeLaplaceChannelComplex hre).comp
      hargContinuous
  have hproduct :=
    hchannel.mul_const (rightHalfPlaneHardyCauchyGram w i j)
  simpa [eulerPrimitiveHorizonShiftedTailGram,
    eulerPrimitiveCommonTestGram, vonMangoldtPrimeRightHalfPlaneGram,
    eulerPrimitiveHorizonShift_one, arg] using hproduct.tendsto

/-- Along the physical Euler region, multiplying the normalized tail by its
diverging partition function converges to the critical retained-label
source. -/
theorem tendstoWithin_eulerPrimitiveHorizon_poleNormal_tail
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    Tendsto (fun sigma : ℝ =>
        ((eulerPrimeCurrentTotal sigma : ℝ) : ℂ) •
          eulerPrimitiveHorizonTailGram sigma w)
      (nhdsWithin 1 (Ioi 1))
      (nhds (eulerPrimitiveCommonTestGram w)) := by
  have hshiftWithin :
      Tendsto (fun sigma : ℝ =>
          eulerPrimitiveHorizonShiftedTailGram sigma w)
        (nhdsWithin 1 (Ioi 1))
        (nhds (eulerPrimitiveCommonTestGram w)) :=
    (tendsto_eulerPrimitiveHorizonShiftedTailGram_one w hw).mono_left
      inf_le_left
  apply hshiftWithin.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  exact (eulerPrimitiveHorizon_poleNormal_tail hsigma w).symm

end

end RHTower
