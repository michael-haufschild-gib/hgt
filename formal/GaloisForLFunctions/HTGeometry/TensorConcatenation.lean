import GaloisForLFunctions.HTGeometry.WeakCutSynthesisCap
import GaloisForLFunctions.HTGeometry.GeometricSkeletonBrownRamp

/-!
# Concatenating circuits across a cut

Gates of the two halves act on disjoint factors, so a word of left gates followed by a word of right
gates moves the pair to the pair of moved factors.  The approximate complexity of a product state is
therefore at most the sum of the two factor complexities, at the larger of the two errors.

On the quantum side the product state is the coordinatewise product, whose norm is the product of
the norms; splitting the difference of two product states into two one-sided differences turns the
factor errors into an additive error for the pair.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

noncomputable section

/-! ## The product gate model -/

section ProductAction

variable {XA XB : Type*} [MetricSpace XA] [MetricSpace XB] {ΓA ΓB : Type*}

/-- Gates of the two halves acting on the pair, each on its own factor. -/
def prodAct (actA : ΓA → XA → XA) (actB : ΓB → XB → XB) :
    (ΓA ⊕ ΓB) → (XA × XB) → (XA × XB)
  | Sum.inl g, p => (actA g p.1, p.2)
  | Sum.inr g, p => (p.1, actB g p.2)

omit [MetricSpace XA] [MetricSpace XB] in
theorem wordAct_prodAct_inl (actA : ΓA → XA → XA) (actB : ΓB → XB → XB) (w : List ΓA)
    (p : XA × XB) :
    wordAct (prodAct actA actB) (w.map Sum.inl) p = (wordAct actA w p.1, p.2) := by
  induction w with
  | nil => simp [wordAct]
  | cons g w ih =>
    rw [List.map_cons, wordAct_cons, ih, wordAct_cons]
    rfl

omit [MetricSpace XA] [MetricSpace XB] in
theorem wordAct_prodAct_inr (actA : ΓA → XA → XA) (actB : ΓB → XB → XB) (w : List ΓB)
    (p : XA × XB) :
    wordAct (prodAct actA actB) (w.map Sum.inr) p = (p.1, wordAct actB w p.2) := by
  induction w with
  | nil => simp [wordAct]
  | cons g w ih =>
    rw [List.map_cons, wordAct_cons, ih, wordAct_cons]
    rfl

omit [MetricSpace XA] [MetricSpace XB] in
/-- **The concatenated word moves both factors.** -/
theorem wordAct_prodAct_append (actA : ΓA → XA → XA) (actB : ΓB → XB → XB)
    (wA : List ΓA) (wB : List ΓB) (p : XA × XB) :
    wordAct (prodAct actA actB) ((wA.map Sum.inl) ++ (wB.map Sum.inr)) p
      = (wordAct actA wA p.1, wordAct actB wB p.2) := by
  rw [wordAct_append, wordAct_prodAct_inr, wordAct_prodAct_inl]

/-- **`(8)`: circuits concatenate across the cut.**  A product state is prepared by the two factor
circuits, with the lengths adding and the error the larger of the two. -/
theorem approxComplexity_prodAct_le (actA : ΓA → XA → XA) (actB : ΓB → XB → XB)
    (chiA : XA) (chiB : XB) {psiA : XA} {psiB : XB} {etaA etaB : ℝ} {SA SB : ℕ}
    (hA : ∃ w : List ΓA, w.length ≤ SA ∧ dist psiA (wordAct actA w chiA) ≤ etaA)
    (hB : ∃ w : List ΓB, w.length ≤ SB ∧ dist psiB (wordAct actB w chiB) ≤ etaB) :
    approxComplexity (prodAct actA actB) (chiA, chiB) (max etaA etaB) (psiA, psiB) ≤ SA + SB := by
  obtain ⟨wA, hwA, hdA⟩ := hA
  obtain ⟨wB, hwB, hdB⟩ := hB
  refine Nat.sInf_le ⟨(wA.map Sum.inl) ++ (wB.map Sum.inr), ?_, ?_⟩
  · rw [List.length_append, List.length_map, List.length_map]
    omega
  · rw [wordAct_prodAct_append]
    rw [Prod.dist_eq]
    exact max_le_max hdA hdB

end ProductAction

/-! ## The tensor product in coordinates -/

section Tensor

variable {dA dB : Type*} [Fintype dA] [Fintype dB]

/-- The coordinatewise product of two state vectors. -/
private def tensorVec (ψ : EuclideanSpace ℂ dA) (φ : EuclideanSpace ℂ dB) :
    EuclideanSpace ℂ (dA × dB) :=
  WithLp.toLp 2 (fun p : dA × dB => ψ p.1 * φ p.2)

omit [Fintype dA] [Fintype dB] in
theorem tensorVec_apply (ψ : EuclideanSpace ℂ dA) (φ : EuclideanSpace ℂ dB) (p : dA × dB) :
    tensorVec ψ φ p = ψ p.1 * φ p.2 := rfl

/-- **The tensor norm is multiplicative.** -/
theorem norm_tensorVec (ψ : EuclideanSpace ℂ dA) (φ : EuclideanSpace ℂ dB) :
    ‖tensorVec ψ φ‖ = ‖ψ‖ * ‖φ‖ := by
  classical
  have hsq : ∑ p : dA × dB, ‖tensorVec ψ φ p‖ ^ 2
      = (∑ i, ‖ψ i‖ ^ 2) * (∑ j, ‖φ j‖ ^ 2) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    exact Finset.sum_congr rfl fun p _ => by
      rw [tensorVec_apply, norm_mul, mul_pow]
  have hA : ‖ψ‖ = Real.sqrt (∑ i, ‖ψ i‖ ^ 2) := EuclideanSpace.norm_eq ψ
  have hB : ‖φ‖ = Real.sqrt (∑ j, ‖φ j‖ ^ 2) := EuclideanSpace.norm_eq φ
  have hAB : ‖tensorVec ψ φ‖ = Real.sqrt (∑ p : dA × dB, ‖tensorVec ψ φ p‖ ^ 2) :=
    EuclideanSpace.norm_eq _
  rw [hAB, hsq, hA, hB, ← Real.sqrt_mul (Finset.sum_nonneg fun i _ => by positivity)]

omit [Fintype dA] [Fintype dB] in
theorem tensorVec_sub_left (ψ ψ' : EuclideanSpace ℂ dA) (φ : EuclideanSpace ℂ dB) :
    tensorVec ψ φ - tensorVec ψ' φ = tensorVec (ψ - ψ') φ := by
  ext p
  show tensorVec ψ φ p - tensorVec ψ' φ p = tensorVec (ψ - ψ') φ p
  rw [tensorVec_apply, tensorVec_apply, tensorVec_apply]
  show ψ p.1 * φ p.2 - ψ' p.1 * φ p.2 = (ψ p.1 - ψ' p.1) * φ p.2
  ring

omit [Fintype dA] [Fintype dB] in
theorem tensorVec_sub_right (ψ : EuclideanSpace ℂ dA) (φ φ' : EuclideanSpace ℂ dB) :
    tensorVec ψ φ - tensorVec ψ φ' = tensorVec ψ (φ - φ') := by
  ext p
  show tensorVec ψ φ p - tensorVec ψ φ' p = tensorVec ψ (φ - φ') p
  rw [tensorVec_apply, tensorVec_apply, tensorVec_apply]
  show ψ p.1 * φ p.2 - ψ p.1 * φ' p.2 = ψ p.1 * (φ p.2 - φ' p.2)
  ring

/-- **Factor errors add.**  For unit vectors the distance between two product states is at most the
sum of the two factor distances. -/
theorem norm_tensorVec_sub_le {ψ ψ' : EuclideanSpace ℂ dA} {φ φ' : EuclideanSpace ℂ dB}
    (hψ' : ‖ψ'‖ = 1) (hφ : ‖φ‖ = 1) :
    ‖tensorVec ψ φ - tensorVec ψ' φ'‖ ≤ ‖ψ - ψ'‖ + ‖φ - φ'‖ := by
  have hsplit : tensorVec ψ φ - tensorVec ψ' φ'
      = (tensorVec ψ φ - tensorVec ψ' φ) + (tensorVec ψ' φ - tensorVec ψ' φ') := by
    abel
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [tensorVec_sub_left, tensorVec_sub_right, norm_tensorVec, norm_tensorVec, hψ', hφ]
  simp

end Tensor

end

end GaloisForLFunctions.HTGeometry
