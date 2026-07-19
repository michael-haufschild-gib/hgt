import GaloisForLFunctions.HTGeometry.ChamberLawPickWitness
import GaloisForLFunctions.HTGeometry.PickKernelChamberIdentity

/-!
# The chamber law for the Pick kernel of the chamber transform

The chamber law is proved for the scaled Gram.  That matrix is the Pick kernel of the chamber
member's regularized Herglotz transform, scaled by the squared height, and a positive real scaling
moves no negative directions.  So the law transfers verbatim: the negative index of the Pick kernel
of the transform is the Hamming distance of its coefficient sign pattern from the positive chamber.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory Matrix Finset

noncomputable section

open scoped Classical ComplexOrder

/-- The Pick denominator at two upper nodes is nonzero: its imaginary part is twice the height. -/
theorem sub_conj_upperNode_ne_zero {y : ℝ} (hy : y ≠ 0) (al am : ℝ) :
    upperNode al y - (starRingEnd ℂ) (upperNode am y) ≠ 0 := by
  intro h
  have him : (upperNode al y - (starRingEnd ℂ) (upperNode am y)).im = 2 * y := by
    simp [upperNode, Complex.sub_im]
    ring
  rw [h, Complex.zero_im] at him
  exact hy (by linarith)

/-- The Pick kernel of the chamber member's regularized Herglotz transform, at the nodes above the
atoms. -/
def chamberPickKernel {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ) (y : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun l m => (chamberHerglotz ν a c (upperNode (a l) y)
      - (starRingEnd ℂ) (chamberHerglotz ν a c (upperNode (a m) y)))
    / (upperNode (a l) y - (starRingEnd ℂ) (upperNode (a m) y))

/-- **The scaled Gram is the Pick kernel scaled by the squared height.** -/
theorem totalGram_eq_smul_chamberPickKernel {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ) {y : ℝ}
    (hy : y ≠ 0)
    (hreg : ∀ l : Fin d,
      Integrable (fun t => regularizedHerglotzKernel t (upperNode (a l) y)) ν) :
    totalGram ν a c y = ((y : ℂ) ^ 2) • chamberPickKernel ν a c y := by
  ext l m
  rw [Matrix.smul_apply, smul_eq_mul, chamberPickKernel, ← mul_div_assoc,
    eq_div_iff (sub_conj_upperNode_ne_zero hy (a l) (a m))]
  exact totalGram_mul_sub_eq_pick ν a c hy l m (hreg l) (hreg m)

/-- A positive real scaling preserves the negative directions of a Hermitian form. -/
theorem re_quadForm_smul_neg_iff {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) {y : ℝ} (hy : y ≠ 0)
    (x : Fin d → ℂ) :
    (star x ⬝ᵥ (((y : ℂ) ^ 2) • P).mulVec x).re < 0
      ↔ (star x ⬝ᵥ P.mulVec x).re < 0 := by
  have hsq : (0 : ℝ) < y ^ 2 := by positivity
  have hval : (star x ⬝ᵥ (((y : ℂ) ^ 2) • P).mulVec x)
      = ((y ^ 2 : ℝ) : ℂ) * (star x ⬝ᵥ P.mulVec x) := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    push_cast
    ring
  rw [hval, Complex.re_ofReal_mul]
  constructor
  · intro h
    by_contra hr
    have hr' : 0 ≤ (star x ⬝ᵥ P.mulVec x).re := not_lt.1 hr
    nlinarith
  · intro h
    exact mul_neg_of_pos_of_neg hsq h

/-- **The chamber law for the Pick kernel of the chamber transform.**  At all small heights the
negative index of the Pick kernel of the chamber member's regularized Herglotz transform is exactly
the Hamming distance of its coefficient sign pattern from the positive chamber. -/
theorem chamberLaw_chamberPickKernel {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ)
    (ha : Function.Injective a) {δ : ℝ} (hδ : 0 < δ) (hc : ∀ j, c j < 0 → c j ≤ -δ)
    (R : ℝ) (hR : 0 < R)
    (hdom : ∀ j : Fin d, Integrable (atomDominant (a j) R) ν)
    (hatom : ∀ j : Fin d, ν {a j} = 0)
    (hreg : ∀ (y : ℝ), y ≠ 0 → ∀ l : Fin d,
      Integrable (fun t => regularizedHerglotzKernel t (upperNode (a l) y)) ν) :
    ∀ᶠ y : ℝ in 𝓝[≠] 0,
      (∀ W : Submodule ℂ (Fin d → ℂ),
          (∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ (chamberPickKernel ν a c y).mulVec x).re < 0) →
          Module.finrank ℂ W ≤ hammingDist (signPattern c) (positiveChamber d))
        ∧ Module.finrank ℂ (negSupported c)
            = hammingDist (signPattern c) (positiveChamber d) := by
  filter_upwards [chamberLaw_totalGram_pick ν a c ha hδ hc R hR hdom hatom,
    self_mem_nhdsWithin] with y hy hy0
  obtain ⟨hup, hdim⟩ := hy
  refine ⟨fun W hW => hup W fun x hxW hx0 => ?_, hdim⟩
  rw [totalGram_eq_smul_chamberPickKernel ν a c hy0 (hreg y hy0),
    re_quadForm_smul_neg_iff _ hy0]
  exact hW x hxW hx0

end

end GaloisForLFunctions.HTGeometry
