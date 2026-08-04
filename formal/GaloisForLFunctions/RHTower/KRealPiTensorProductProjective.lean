import GaloisForLFunctions.RHTower.KRealPiTensorProduct
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm

/-!
# Projective continuity of indexed Real tensor products

Componentwise conjugate-linear isometries act isometrically on the algebraic
indexed tensor product equipped with its projective seminorm.  The proof acts
on every finite tensor presentation entering the defining infimum, so it does
not assume finite dimensionality, completeness, or norm separation.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions.RHTower

variable {I : Type*} [Fintype I]
variable {E : I → Type*}
  [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]

/-- Conjugate every scalar and every tensor factor in a finite projective
presentation. -/
def kRealPiTensorLiftTransform
    (K : ∀ i, KRealStructure false (E i))
    (p : FreeAddMonoid (ℂ × ∀ i, E i)) :
    FreeAddMonoid (ℂ × ∀ i, E i) :=
  p.map fun y => (star y.1, fun i => (K i).sigma (y.2 i))

/-- The transformed presentation represents the componentwise Real image. -/
theorem kRealPiTensorLiftTransform_mem_lifts
    (K : ∀ i, KRealStructure false (E i))
    {x : PiTensorProduct ℂ E}
    {p : FreeAddMonoid (ℂ × ∀ i, E i)}
    (hp : p ∈ PiTensorProduct.lifts x) :
    kRealPiTensorLiftTransform K p ∈
      PiTensorProduct.lifts (kRealEvenPiTensorSigma K x) := by
  rw [PiTensorProduct.mem_lifts_iff] at hp ⊢
  rw [← hp]
  have hlist : ∀ l : List (ℂ × ∀ i, E i),
      (List.map (fun y => (starRingEnd ℂ) y.1 •
          PiTensorProduct.tprod ℂ (fun i => (K i).sigma (y.2 i))) l).sum =
        kRealEvenPiTensorSigma K
          (List.map (fun y => y.1 • PiTensorProduct.tprod ℂ y.2) l).sum := by
    intro l
    induction l with
    | nil => simp
    | cons y l ih =>
        rcases y with ⟨r, f⟩
        simp only [List.map_cons, List.sum_cons, map_add, map_smulₛₗ,
          kRealEvenPiTensorSigma_tprod, ih]
  unfold kRealPiTensorLiftTransform
  rw [FreeAddMonoid.toList_map, List.map_map]
  change (List.map (fun y => (starRingEnd ℂ) y.1 •
      PiTensorProduct.tprod ℂ (fun i => (K i).sigma (y.2 i))) p.toList).sum =
    kRealEvenPiTensorSigma K
      (List.map (fun y => y.1 • PiTensorProduct.tprod ℂ y.2) p.toList).sum
  exact hlist p.toList

/-- Projective presentation cost is invariant under componentwise
conjugate-linear isometries. -/
theorem kRealPiTensorLiftTransform_projectiveSeminormAux
    (K : ∀ i, KRealStructure false (E i))
    (hnorm : ∀ i (x : E i), ‖(K i).sigma x‖ = ‖x‖)
    (p : FreeAddMonoid (ℂ × ∀ i, E i)) :
    PiTensorProduct.projectiveSeminormAux
        (kRealPiTensorLiftTransform K p) =
      PiTensorProduct.projectiveSeminormAux p := by
  unfold kRealPiTensorLiftTransform PiTensorProduct.projectiveSeminormAux
  rw [FreeAddMonoid.toList_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro y hy
  rcases y with ⟨r, f⟩
  dsimp only [Function.comp_apply]
  rw [norm_star]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact hnorm i (f i)

/-- Componentwise Real action does not increase the projective seminorm. -/
theorem kRealEvenPiTensorSigma_norm_le
    (K : ∀ i, KRealStructure false (E i))
    (hnorm : ∀ i (x : E i), ‖(K i).sigma x‖ = ‖x‖)
    (x : PiTensorProduct ℂ E) :
    ‖kRealEvenPiTensorSigma K x‖ ≤ ‖x‖ := by
  rw [PiTensorProduct.norm_def, PiTensorProduct.norm_def]
  refine le_ciInf fun p => ?_
  exact ciInf_le_of_le
    (PiTensorProduct.bddBelow_projectiveSemiNormAux
      (kRealEvenPiTensorSigma K x))
    ⟨kRealPiTensorLiftTransform K p.1,
      kRealPiTensorLiftTransform_mem_lifts K p.2⟩
    (le_of_eq (kRealPiTensorLiftTransform_projectiveSeminormAux
      K hnorm p.1))

/-- Componentwise conjugate-linear isometries remain isometries for the exact
projective seminorm. -/
theorem kRealEvenPiTensorSigma_norm
    (K : ∀ i, KRealStructure false (E i))
    (hnorm : ∀ i (x : E i), ‖(K i).sigma x‖ = ‖x‖)
    (x : PiTensorProduct ℂ E) :
    ‖kRealEvenPiTensorSigma K x‖ = ‖x‖ := by
  apply le_antisymm (kRealEvenPiTensorSigma_norm_le K hnorm x)
  calc
    ‖x‖ = ‖kRealEvenPiTensorSigma K
        (kRealEvenPiTensorSigma K x)‖ := by
      rw [kRealEvenPiTensorSigma_sq]
    _ ≤ ‖kRealEvenPiTensorSigma K x‖ :=
      kRealEvenPiTensorSigma_norm_le K hnorm
        (kRealEvenPiTensorSigma K x)

/-- Projective conjugate-linear isometric involution on indexed tensor
powers. -/
def kRealEvenPiTensorIsometry
    (K : ∀ i, KRealStructure false (E i))
    (hnorm : ∀ i (x : E i), ‖(K i).sigma x‖ = ‖x‖) :
    PiTensorProduct ℂ E ≃ₗᵢ⋆[ℂ] PiTensorProduct ℂ E where
  toFun := kRealEvenPiTensorSigma K
  invFun := kRealEvenPiTensorSigma K
  left_inv := kRealEvenPiTensorSigma_sq K
  right_inv := kRealEvenPiTensorSigma_sq K
  map_add' := map_add (kRealEvenPiTensorSigma K)
  map_smul' := map_smulₛₗ (kRealEvenPiTensorSigma K)
  norm_map' := kRealEvenPiTensorSigma_norm K hnorm

end GaloisForLFunctions.RHTower
