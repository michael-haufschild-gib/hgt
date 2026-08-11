import Mathlib
import GaloisForLFunctions.HTGeometry.FiniteUnitaryEnergyDefectLaw

/-!
# Finite spectral phase action

The nearest-neighbour chord variation of an ordered finite phase vector is subadditive under
pointwise multiplication and stable under both vertexwise and Hilbert--Schmidt perturbations.
Radial normalization therefore recovers a quantitative amount of target phase action without a
minimum-modulus or minimum-spectral-gap hypothesis.  The matrix form retains only diagonal error
and is controlled by the full entrywise square error.

For diagonal unitary targets, normalized Choi overlap now supplies the error term exactly: after
choosing the trace-aligning global phase, squared Hilbert--Schmidt distance is
`2D - 2 |tr(T⁺W)|`.  The recovered diagonal phase therefore retains target action with a fully
explicit Choi-scale loss.

The final alternating-phase theorem is the hostile boundary: a single binary character already
attains the maximal action.  Hence phase action is a robust recurrence/phase-recovery invariant,
but by itself cannot certify local circuit complexity; any such use requires a separate bound on
the action of the permitted generators in the source eigenbasis.
-/

open scoped BigOperators Matrix ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Radially project a nonzero complex amplitude to the unit circle, using `target` at zero. -/
noncomputable def phaseNormalize (target a : ℂ) : ℂ :=
  if a = 0 then target else a / ‖a‖

theorem norm_phaseNormalize {target a : ℂ} (htarget : ‖target‖ = 1) :
    ‖phaseNormalize target a‖ = 1 := by
  by_cases ha : a = 0
  · simp [phaseNormalize, ha, htarget]
  · rw [phaseNormalize, if_neg ha, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg a), div_self (norm_ne_zero_iff.mpr ha)]

theorem norm_phaseNormalize_sub_le {target a : ℂ} (htarget : ‖target‖ = 1) :
    ‖phaseNormalize target a - target‖ ≤ 2 * ‖a - target‖ := by
  by_cases ha : a = 0
  · simp [phaseNormalize, ha]
  · have hnorma : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hradial : ‖a / ‖a‖ - a‖ = |1 - ‖a‖| := by
      rw [div_eq_inv_mul]
      calc
        ‖(↑‖a‖ : ℂ)⁻¹ * a - a‖ = ‖((↑‖a‖ : ℂ)⁻¹ - 1) * a‖ := by
          congr 1
          ring
        _ = ‖(↑‖a‖ : ℂ)⁻¹ - 1‖ * ‖a‖ := norm_mul _ _
        _ = |(‖a‖)⁻¹ - 1| * ‖a‖ := by
          rw [show ((↑‖a‖ : ℂ)⁻¹ - 1) = ↑((‖a‖ : ℝ)⁻¹ - 1) by norm_num,
            Complex.norm_real, Real.norm_eq_abs]
        _ = |(‖a‖)⁻¹ - 1| * |‖a‖| := by rw [abs_of_pos hnorma]
        _ = |((‖a‖)⁻¹ - 1) * ‖a‖| := (abs_mul _ _).symm
        _ = |1 - ‖a‖| := by
          congr 1
          field_simp [ne_of_gt hnorma]
    have hreverse : |1 - ‖a‖| ≤ ‖a - target‖ := by
      rw [show |1 - ‖a‖| = |‖target‖ - ‖a‖| by rw [htarget]]
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le target a
    rw [phaseNormalize, if_neg ha]
    calc
      ‖a / ‖a‖ - target‖ ≤ ‖a / ‖a‖ - a‖ + ‖a - target‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (a / ‖a‖ - a) (a - target)
      _ ≤ ‖a - target‖ + ‖a - target‖ := by
        rw [hradial]
        gcongr
      _ = 2 * ‖a - target‖ := by ring

/-- Chord variation of a phase vector along its fixed finite ordering. -/
noncomputable def spectralPhaseAction {n : ℕ} (z : Fin (n + 1) → ℂ) : ℝ :=
  ∑ j : Fin n, ‖z j.succ - z j.castSucc‖

theorem spectralPhaseAction_nonneg {n : ℕ} (z : Fin (n + 1) → ℂ) :
    0 ≤ spectralPhaseAction z := by
  unfold spectralPhaseAction
  positivity

theorem spectralPhaseAction_le_add_vertexError {n : ℕ}
    (z w : Fin (n + 1) → ℂ) :
    spectralPhaseAction z ≤ spectralPhaseAction w +
      2 * ∑ i, ‖z i - w i‖ := by
  unfold spectralPhaseAction
  calc
    (∑ j : Fin n, ‖z j.succ - z j.castSucc‖) ≤
        ∑ j : Fin n, (‖w j.succ - w j.castSucc‖ +
          ‖z j.succ - w j.succ‖ + ‖z j.castSucc - w j.castSucc‖) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        ‖z j.succ - z j.castSucc‖ =
            ‖(w j.succ - w j.castSucc) +
              (z j.succ - w j.succ) - (z j.castSucc - w j.castSucc)‖ := by
          congr 1
          ring
        _ ≤ ‖(w j.succ - w j.castSucc) + (z j.succ - w j.succ)‖ +
            ‖z j.castSucc - w j.castSucc‖ := by
          exact norm_sub_le
            ((w j.succ - w j.castSucc) + (z j.succ - w j.succ))
            (z j.castSucc - w j.castSucc)
        _ ≤ ‖w j.succ - w j.castSucc‖ + ‖z j.succ - w j.succ‖ +
            ‖z j.castSucc - w j.castSucc‖ := by
          have hadd := norm_add_le (w j.succ - w j.castSucc)
            (z j.succ - w j.succ)
          linarith
    _ ≤ (∑ j : Fin n, ‖w j.succ - w j.castSucc‖) +
        2 * ∑ i, ‖z i - w i‖ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hsucc : (∑ j : Fin n, ‖z j.succ - w j.succ‖) ≤
          ∑ i : Fin (n + 1), ‖z i - w i‖ := by
        rw [Fin.sum_univ_succ]
        exact le_add_of_nonneg_left (norm_nonneg _)
      have hcast : (∑ j : Fin n, ‖z j.castSucc - w j.castSucc‖) ≤
          ∑ i : Fin (n + 1), ‖z i - w i‖ := by
        rw [Fin.sum_univ_castSucc]
        exact le_add_of_nonneg_right (norm_nonneg _)
      linarith
    _ = spectralPhaseAction w + 2 * ∑ i, ‖z i - w i‖ := rfl

theorem spectralPhaseAction_phaseNormalize_lower {n : ℕ}
    (target a : Fin (n + 1) → ℂ) (htarget : ∀ i, ‖target i‖ = 1) :
    spectralPhaseAction target - 4 * ∑ i, ‖a i - target i‖ ≤
      spectralPhaseAction (fun i => phaseNormalize (target i) (a i)) := by
  have h := spectralPhaseAction_le_add_vertexError target
    (fun i => phaseNormalize (target i) (a i))
  have herr : (∑ i, ‖target i - phaseNormalize (target i) (a i)‖) ≤
      2 * ∑ i, ‖a i - target i‖ := by
    calc
      _ = ∑ i, ‖phaseNormalize (target i) (a i) - target i‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_sub_rev]
      _ ≤ ∑ i, 2 * ‖a i - target i‖ :=
        Finset.sum_le_sum fun i _ => norm_phaseNormalize_sub_le (htarget i)
      _ = 2 * ∑ i, ‖a i - target i‖ := by rw [Finset.mul_sum]
  linarith

theorem sum_le_sqrt_card_mul_sqrt_sum_sq
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) :
    ∑ i, e i ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, (e i) ^ 2) := by
  classical
  have hsq : (∑ i, e i) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, (e i) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset ι)) (f := e)
  have hsum : 0 ≤ ∑ i, e i := Finset.sum_nonneg fun i _ => he i
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have henergy : 0 ≤ ∑ i, (e i) ^ 2 := by positivity
  have hsqrtCard : Real.sqrt (Fintype.card ι) ^ 2 = (Fintype.card ι : ℝ) :=
    Real.sq_sqrt hcard
  have hsqrtEnergy : Real.sqrt (∑ i, (e i) ^ 2) ^ 2 = ∑ i, (e i) ^ 2 :=
    Real.sq_sqrt henergy
  have hrhs : 0 ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, (e i) ^ 2) := by
    positivity
  nlinarith [sq_nonneg
    (Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, (e i) ^ 2))]

/-- **Hilbert--Schmidt-stable phase recovery.** Radial projection loses at most the square-root
vertex error multiplied by the square root of the number of spectral vertices. -/
theorem spectralPhaseAction_phaseNormalize_lower_l2 {n : ℕ}
    (target a : Fin (n + 1) → ℂ) (htarget : ∀ i, ‖target i‖ = 1) :
    spectralPhaseAction target -
        4 * Real.sqrt (n + 1) * Real.sqrt (∑ i, ‖a i - target i‖ ^ 2) ≤
      spectralPhaseAction (fun i => phaseNormalize (target i) (a i)) := by
  have hl1 := sum_le_sqrt_card_mul_sqrt_sum_sq
    (fun i : Fin (n + 1) => ‖a i - target i‖) (fun _ => norm_nonneg _)
  have hbase := spectralPhaseAction_phaseNormalize_lower target a htarget
  simp only [Fintype.card_fin] at hl1
  norm_num [Nat.cast_add, Nat.cast_one] at hl1 ⊢
  have hscale : 4 * ∑ i, ‖a i - target i‖ ≤
      4 * (Real.sqrt ((n : ℝ) + 1) * Real.sqrt (∑ i, ‖a i - target i‖ ^ 2)) := by
    gcongr
  nlinarith

/-- Diagonal matrix carrying a prescribed ordered phase vector. -/
noncomputable def phaseDiagonalMatrix {n : ℕ}
    (target : Fin (n + 1) → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal target

/-- Entrywise squared error between two finite complex matrices. -/
noncomputable def matrixEntryErrorEnergy {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j - B i j‖ ^ 2

theorem diagonalErrorEnergy_le_matrixEntryErrorEnergy {n : ℕ}
    (target : Fin (n + 1) → ℂ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (∑ i, ‖A i i - target i‖ ^ 2) ≤
      matrixEntryErrorEnergy A (phaseDiagonalMatrix target) := by
  classical
  unfold matrixEntryErrorEnergy phaseDiagonalMatrix
  apply Finset.sum_le_sum
  intro i hi
  have hone : ‖A i i - Matrix.diagonal target i i‖ ^ 2 ≤
      ∑ j, ‖A i j - Matrix.diagonal target i j‖ ^ 2 := by
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin (n + 1))))
      (f := fun j => ‖A i j - Matrix.diagonal target i j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  simpa using hone

/-- **Matrix phase-recovery law.** Full entrywise square error controls loss of diagonal phase
action; no lower bound on the approximate diagonal entries is assumed. -/
theorem spectralPhaseAction_phaseNormalize_diagonal_lower_l2 {n : ℕ}
    (target : Fin (n + 1) → ℂ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (htarget : ∀ i, ‖target i‖ = 1) :
    spectralPhaseAction target -
        4 * Real.sqrt (n + 1) *
          Real.sqrt (matrixEntryErrorEnergy A (phaseDiagonalMatrix target)) ≤
      spectralPhaseAction (fun i => phaseNormalize (target i) (A i i)) := by
  have hdiag := diagonalErrorEnergy_le_matrixEntryErrorEnergy target A
  have hsqrt := Real.sqrt_le_sqrt hdiag
  have hscale :
      4 * Real.sqrt ((n : ℝ) + 1) * Real.sqrt (∑ i, ‖A i i - target i‖ ^ 2) ≤
        4 * Real.sqrt ((n : ℝ) + 1) *
          Real.sqrt (matrixEntryErrorEnergy A (phaseDiagonalMatrix target)) := by
    gcongr
  have hbase := spectralPhaseAction_phaseNormalize_lower_l2 target
    (fun i => A i i) htarget
  norm_num [Nat.cast_add, Nat.cast_one] at hbase ⊢
  linarith

theorem spectralPhaseAction_const_mul {n : ℕ} (c : ℂ)
    (z : Fin (n + 1) → ℂ) (hc : ‖c‖ = 1) :
    spectralPhaseAction (fun i => c * z i) = spectralPhaseAction z := by
  unfold spectralPhaseAction
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_sub, norm_mul, hc, one_mul]

/-- Radial normalization aligns a complex number with the positive real axis. -/
theorem star_phaseNormalize_one_mul (z : ℂ) :
    star (phaseNormalize 1 z) * z = ‖z‖ := by
  by_cases hz : z = 0
  · simp [phaseNormalize, hz]
  · rw [phaseNormalize, if_neg hz]
    change (starRingEnd ℂ) (z / (‖z‖ : ℂ)) * z = (‖z‖ : ℂ)
    rw [map_div₀ (starRingEnd ℂ), Complex.conj_ofReal]
    have hn : (‖z‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr hz
    rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self]
    rw [← Complex.sq_norm]
    field_simp
    norm_num

/-- Global phase aligning the normalized trace overlap of two finite unitaries. -/
noncomputable def unitaryTraceAlignmentPhase
    {n : ℕ} (T W : Matrix.unitaryGroup (Fin (n + 1)) ℂ) : ℂ :=
  phaseNormalize 1
    (Matrix.trace
      (star (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *
        (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)))

theorem norm_unitaryTraceAlignmentPhase {n : ℕ}
    (T W : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
    ‖unitaryTraceAlignmentPhase T W‖ = 1 := by
  exact norm_phaseNormalize (by norm_num)

/-- Entrywise square error is the trace-defined Hilbert--Schmidt energy of the difference. -/
theorem matrixEntryErrorEnergy_eq_finiteMatrixHilbertSchmidtEnergy {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    matrixEntryErrorEnergy A B = finiteMatrixHilbertSchmidtEnergy (A - B) := by
  rw [finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq]
  unfold matrixEntryErrorEnergy
  simp_rw [Complex.sq_norm, Matrix.sub_apply]
  rw [Finset.sum_comm]

/-- **Exact projective unitary distance law.** Trace alignment converts squared Hilbert--Schmidt
distance into `2D - 2 |tr(T⁺W)|`. -/
theorem finiteMatrixHilbertSchmidtEnergy_unitary_sub_aligned {n : ℕ}
    (T W : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
    finiteMatrixHilbertSchmidtEnergy
        ((W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
          unitaryTraceAlignmentPhase T W •
            (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) =
      2 * (n + 1) - 2 *
        ‖Matrix.trace
          (star (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *
            (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))‖ := by
  let TM : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := T
  let WM : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := W
  let z : ℂ := Matrix.trace (star TM * WM)
  let c : ℂ := unitaryTraceAlignmentPhase T W
  have hc : ‖c‖ = 1 := norm_unitaryTraceAlignmentPhase T W
  have halign : star c * z = ‖z‖ := by
    exact star_phaseNormalize_one_mul z
  have hW : (∑ i, ∑ j, Complex.normSq (WM i j)) =
      (n + 1 : ℝ) := by
    calc
      _ = ∑ _i : Fin (n + 1), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa [WM, finiteUnitaryEntryWeight] using
          sum_finiteUnitaryEntryWeight_row W i
      _ = (n + 1 : ℝ) := by simp
  have hT : (∑ i, ∑ j, Complex.normSq (TM i j)) =
      (n + 1 : ℝ) := by
    calc
      _ = ∑ _i : Fin (n + 1), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa [TM, finiteUnitaryEntryWeight] using
          sum_finiteUnitaryEntryWeight_row T i
      _ = (n + 1 : ℝ) := by simp
  have hcrossComplex :
      (∑ i, ∑ j,
        WM i j * star (c * TM i j)) =
        star c * z := by
    dsimp [z]
    simp only [map_mul]
    calc
      _ = star c * (∑ i, ∑ j,
          star (TM i j) * WM i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [RCLike.star_def]
        ring
      _ = _ := by
        congr 1
        rw [Matrix.trace]
        simp only [Matrix.diag, Matrix.mul_apply, star, Matrix.conjTranspose_apply]
        rw [Finset.sum_comm]
  rw [← matrixEntryErrorEnergy_eq_finiteMatrixHilbertSchmidtEnergy]
  change matrixEntryErrorEnergy WM (c • TM) = 2 * (n + 1) - 2 * ‖z‖
  unfold matrixEntryErrorEnergy
  simp only [Matrix.smul_apply, smul_eq_mul]
  simp_rw [Complex.sq_norm]
  simp only [Complex.normSq_sub, Complex.normSq_mul]
  have hcSq : Complex.normSq c = 1 := by
    rw [← Complex.sq_norm, hc]
    norm_num
  have hscaled :
      (∑ i, ∑ j, Complex.normSq c *
        Complex.normSq (TM i j)) =
      Complex.normSq c * (n + 1 : ℝ) := by
    rw [← hT, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  have hcrossRe :
      (∑ i, ∑ j,
        ((WM i j * star (c * TM i j)).re)) =
        ‖z‖ := by
    calc
      _ = ((∑ i, ∑ j, WM i j * star (c * TM i j)) : ℂ).re := by
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Complex.re_sum]
      _ = (star c * z).re := by rw [hcrossComplex]
      _ = ‖z‖ := by rw [halign]; simp
  have hcrossScaled :
      (∑ i, ∑ j, 2 *
        ((WM i j * star (c * TM i j)).re)) =
        2 * ‖z‖ := by
    rw [← hcrossRe, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  let eW : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => Complex.normSq (WM i j)
  let eT : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => Complex.normSq c * Complex.normSq (TM i j)
  let eX : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => 2 * (WM i j * star (c * TM i j)).re
  change (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (eW i j + eT i j - eX i j)) =
    2 * (n + 1) - 2 * ‖z‖
  have heW : (∑ i, ∑ j, eW i j) = (n + 1 : ℝ) := by
    simpa only [eW] using hW
  have heT : (∑ i, ∑ j, eT i j) = Complex.normSq c * (n + 1 : ℝ) := by
    simpa only [eT] using hscaled
  have heX : (∑ i, ∑ j, eX i j) = 2 * ‖z‖ := by
    simpa only [eX] using hcrossScaled
  calc
    _ = ∑ i, ((∑ j, eW i j) + (∑ j, eT i j) - (∑ j, eX i j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = (∑ i, ∑ j, eW i j) + (∑ i, ∑ j, eT i j) -
        (∑ i, ∑ j, eX i j) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = _ := by
      rw [heW, heT, heX, hcSq]
      ring

/-- **Choi-to-phase-action extraction.** Every unitary shortcut to a diagonal phase target has,
after the optimal global-phase alignment and radial diagonal normalization, the target's phase
action up to the exact normalized-trace Hilbert--Schmidt loss. -/
theorem finiteUnitary_choiPhaseAction_lower {n : ℕ}
    (target : Fin (n + 1) → ℂ) (htarget : ∀ i, ‖target i‖ = 1)
    (T W : Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (hTdiag : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      phaseDiagonalMatrix target) :
    spectralPhaseAction target -
        4 * Real.sqrt (n + 1) *
          Real.sqrt
            (2 * (n + 1) - 2 *
              ‖Matrix.trace
                (star (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *
                  (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))‖) ≤
      spectralPhaseAction (fun i =>
        phaseNormalize
          (unitaryTraceAlignmentPhase T W * target i)
          ((W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i i)) := by
  let c : ℂ := unitaryTraceAlignmentPhase T W
  have hc : ‖c‖ = 1 := norm_unitaryTraceAlignmentPhase T W
  have hctarget : ∀ i, ‖c * target i‖ = 1 := by
    intro i
    rw [norm_mul, hc, htarget, one_mul]
  have haction : spectralPhaseAction (fun i => c * target i) =
      spectralPhaseAction target := spectralPhaseAction_const_mul c target hc
  have hdiagc : phaseDiagonalMatrix (fun i => c * target i) =
      c • (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    rw [hTdiag]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [phaseDiagonalMatrix]
    · simp [phaseDiagonalMatrix, hij]
  have herror :
      matrixEntryErrorEnergy
          (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
          (phaseDiagonalMatrix (fun i => c * target i)) =
        2 * (n + 1) - 2 *
          ‖Matrix.trace
            (star (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *
              (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))‖ := by
    rw [hdiagc, matrixEntryErrorEnergy_eq_finiteMatrixHilbertSchmidtEnergy]
    exact finiteMatrixHilbertSchmidtEnergy_unitary_sub_aligned T W
  have hbase := spectralPhaseAction_phaseNormalize_diagonal_lower_l2
    (fun i => c * target i)
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) hctarget
  rw [haction, herror] at hbase
  exact hbase

theorem spectralPhaseAction_mul_le {n : ℕ} (z w : Fin (n + 1) → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (hw : ∀ i, ‖w i‖ = 1) :
    spectralPhaseAction (fun i => z i * w i) ≤
      spectralPhaseAction z + spectralPhaseAction w := by
  unfold spectralPhaseAction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  calc
    ‖z j.succ * w j.succ - z j.castSucc * w j.castSucc‖ =
        ‖z j.succ * (w j.succ - w j.castSucc) +
          (z j.succ - z j.castSucc) * w j.castSucc‖ := by
      congr 1
      ring
    _ ≤ ‖z j.succ * (w j.succ - w j.castSucc)‖ +
        ‖(z j.succ - z j.castSucc) * w j.castSucc‖ := norm_add_le _ _
    _ = ‖w j.succ - w j.castSucc‖ + ‖z j.succ - z j.castSucc‖ := by
      rw [norm_mul, norm_mul, hz, hw, one_mul, mul_one]
    _ = _ := by ring

theorem spectralPhaseAction_le_two_mul {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) :
    spectralPhaseAction z ≤ 2 * n := by
  unfold spectralPhaseAction
  calc
    (∑ j : Fin n, ‖z j.succ - z j.castSucc‖) ≤ ∑ _j : Fin n, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        ‖z j.succ - z j.castSucc‖ ≤ ‖z j.succ‖ + ‖z j.castSucc‖ := norm_sub_le _ _
        _ = 2 := by rw [hz, hz]; ring
    _ = 2 * n := by simp [mul_comm]

/-- Alternating binary character on an ordered finite spectrum. -/
noncomputable def alternatingSpectralPhase {n : ℕ} (i : Fin (n + 1)) : ℂ :=
  (-1 : ℂ) ^ i.val

theorem norm_alternatingSpectralPhase {n : ℕ} (i : Fin (n + 1)) :
    ‖alternatingSpectralPhase i‖ = 1 := by
  simp [alternatingSpectralPhase]

/-- **Sharp hostile boundary.** One alternating binary character attains maximal phase action. -/
theorem spectralPhaseAction_alternating {n : ℕ} :
    spectralPhaseAction (alternatingSpectralPhase : Fin (n + 1) → ℂ) = 2 * n := by
  unfold spectralPhaseAction
  calc
    (∑ j : Fin n,
        ‖alternatingSpectralPhase j.succ - alternatingSpectralPhase j.castSucc‖) =
        ∑ _j : Fin n, (2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [alternatingSpectralPhase, Fin.val_succ, Fin.val_castSucc, pow_succ]
      rw [show (-1 : ℂ) ^ j.val * -1 - (-1 : ℂ) ^ j.val =
        (-2 : ℂ) * (-1 : ℂ) ^ j.val by ring]
      rw [norm_mul, norm_pow]
      norm_num
    _ = 2 * n := by simp [mul_comm]

end

end GaloisForLFunctions.HTGeometry
