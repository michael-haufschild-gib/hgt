import Mathlib

/-!
# Finite spectral phase action

The nearest-neighbour chord variation of an ordered finite phase vector is subadditive under
pointwise multiplication and stable under both vertexwise and Hilbert--Schmidt perturbations.
Radial normalization therefore recovers a quantitative amount of target phase action without a
minimum-modulus or minimum-spectral-gap hypothesis.  The matrix form retains only diagonal error
and is controlled by the full entrywise square error.

The final alternating-phase theorem is the hostile boundary: a single binary character already
attains the maximal action.  Hence phase action is a robust recurrence/phase-recovery invariant,
but by itself cannot certify local circuit complexity; any such use requires a separate bound on
the action of the permitted generators in the source eigenbasis.
-/

open scoped BigOperators

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
