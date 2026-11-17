import GaloisForLFunctions.ExclusionOfTheCriticalState.Certificates.WeilProbeCutBudget
import Mathlib.Analysis.Complex.Circle

/-!
# Exact phase loss and rigidity of the safe Weil probe kernel

Positive entries make phase alignment the unique energy maximizer on
nonzero coefficient support. The loss is a weighted sum of squared
phase distances. Independent coordinate phases preserve the full kernel
only when they are common: a concrete rigidity restriction on the
coordinatewise symmetries suggested by Pick-body geometry.
-/

open scoped BigOperators ComplexConjugate
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
open Pick
noncomputable section

/-- The real Weil energy with arbitrary unit complex coefficient phases. -/
def phaseEnergy {n : ℕ} (p a : Fin n → ℝ) (φ : Fin n → Circle) : ℝ :=
  ∑ i, ∑ j, weight p a i j * (conj (φ i : ℂ) * (φ j : ℂ)).re

/-- The phase expression is the real part of the literal complex Weil quadratic form. -/
theorem phaseEnergy_eq_quadratic {n : ℕ} (p a : Fin n → ℝ) (φ : Fin n → Circle) :
    phaseEnergy p a φ =
      (∑ i, ∑ j, conj (((|a i| : ℝ) : ℂ) * (φ i : ℂ)) * (((|a j| : ℝ) : ℂ) * (φ j : ℂ)) *
        (bareMixedEnergy (probe (node (p i))) (probe (node (p j))) : ℂ)).re := by
  simp only [phaseEnergy, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [weight, map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem unit_phase_gap (u v : Circle) :
    ‖(u : ℂ) - (v : ℂ)‖ ^ 2 = 2 - 2 * (conj (u : ℂ) * (v : ℂ)).re := by
  have hu : Complex.normSq (u : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Circle.norm_coe, one_pow]
  have hv : Complex.normSq (v : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Circle.norm_coe, one_pow]
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im] at hu hv ⊢
  nlinarith only [hu, hv]

/-- Exact diamagnetic loss, with all actual mixed Weil entries retained. -/
theorem aligned_sub_phaseEnergy {n : ℕ} (p a : Fin n → ℝ) (φ : Fin n → Circle) :
    alignedEnergy p a - phaseEnergy p a φ =
      (1 / 2) * ∑ i, ∑ j, weight p a i j * ‖(φ i : ℂ) - (φ j : ℂ)‖ ^ 2 := by
  unfold alignedEnergy sourceQuadratic phaseEnergy
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [unit_phase_gap]
  unfold weight
  ring

/-- Alignment always maximizes energy, even if the Weil matrix has negative directions. -/
theorem phaseEnergy_le_aligned {n : ℕ} (p a : Fin n → ℝ) (φ : Fin n → Circle) :
    phaseEnergy p a φ ≤ alignedEnergy p a := by
  have h := aligned_sub_phaseEnergy p a φ
  have hn : 0 ≤ ∑ i, ∑ j, weight p a i j * ‖(φ i : ℂ) - (φ j : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (weight_nonneg p a i j) (sq_nonneg _)
  linarith only [h, hn]

/-- Equality permits precisely a common phase on the nonzero coefficient support. -/
theorem phaseEnergy_eq_aligned_iff {n : ℕ} (p a : Fin n → ℝ) (φ : Fin n → Circle) :
    phaseEnergy p a φ = alignedEnergy p a ↔
      ∀ i j, a i ≠ 0 → a j ≠ 0 → φ i = φ j := by
  have hnon (i j : Fin n) :
      0 ≤ weight p a i j * ‖(φ i : ℂ) - (φ j : ℂ)‖ ^ 2 :=
    mul_nonneg (weight_nonneg p a i j) (sq_nonneg _)
  constructor
  · intro he
    have hz : (∑ i, ∑ j, weight p a i j * ‖(φ i : ℂ) - (φ j : ℂ)‖ ^ 2) = 0 := by
      have h := aligned_sub_phaseEnergy p a φ
      rw [he] at h
      linarith only [h]
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => Finset.sum_nonneg fun j _ => hnon i j)).mp hz
    intro i j hai haj
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => hnon i j)).mp (hi i (Finset.mem_univ i))
    have hw : 0 < weight p a i j :=
      mul_pos (mul_pos (abs_pos.mpr hai) (abs_pos.mpr haj)) (probeEntry_pos _ _)
    have heq := (mul_eq_zero.mp (hij j (Finset.mem_univ j))).resolve_left hw.ne'
    apply Subtype.ext
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp heq))
  · intro h
    have hz : (∑ i, ∑ j, weight p a i j * ‖(φ i : ℂ) - (φ j : ℂ)‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      by_cases hi : a i = 0
      · simp only [weight, hi, abs_zero, zero_mul]
      by_cases hj : a j = 0
      · simp only [weight, hj, abs_zero, mul_zero, zero_mul]
      rw [h i j hi hj, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    have he := aligned_sub_phaseEnergy p a φ
    rw [hz, mul_zero] at he
    exact (sub_eq_zero.mp he).symm

/-- Multiplying each coordinate by its own unit phase acts by diagonal congruence. -/
def phasedKernel {n : ℕ} (p : Fin n → ℝ) (φ : Fin n → Circle) (i j : Fin n) : ℂ :=
  (conj (φ i : ℂ) * (φ j : ℂ)) *
    (bareMixedEnergy (probe (node (p i))) (probe (node (p j))) : ℂ)

/-- The complete positive-entry kernel admits only common diagonal phase symmetries. -/
theorem phasedKernel_invariant_iff {n : ℕ} (p : Fin n → ℝ) (φ : Fin n → Circle) :
    (∀ i j, phasedKernel p φ i j =
      (bareMixedEnergy (probe (node (p i))) (probe (node (p j))) : ℂ)) ↔
      ∀ i j, φ i = φ j := by
  constructor
  · intro h i j
    have hk : (bareMixedEnergy (probe (node (p i))) (probe (node (p j))) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (probeEntry_pos _ _).ne'
    have hc : conj (φ i : ℂ) * (φ j : ℂ) = 1 := by
      apply mul_right_cancel₀ hk
      simpa only [phasedKernel, one_mul] using h i j
    have hu : conj (φ i : ℂ) * (φ i : ℂ) = 1 := by
      rw [Complex.conj_mul', Circle.norm_coe]
      norm_num
    apply Subtype.ext
    exact mul_left_cancel₀ ((map_ne_zero _).mpr (Circle.coe_ne_zero _)) (hu.trans hc.symm)
  · intro h i j
    unfold phasedKernel
    rw [h i j, Complex.conj_mul', Circle.norm_coe]
    norm_num

#print axioms aligned_sub_phaseEnergy
#print axioms phaseEnergy_eq_quadratic
#print axioms phaseEnergy_le_aligned
#print axioms phaseEnergy_eq_aligned_iff
#print axioms phasedKernel_invariant_iff
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
