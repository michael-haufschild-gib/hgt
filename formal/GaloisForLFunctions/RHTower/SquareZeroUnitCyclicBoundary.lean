import GaloisForLFunctions.RHTower.CyclicBarTensorOperators
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Square-zero unit classes before and after cyclic relations

Explicit full-tensor chain decompositions distinguish a nonzero Hochschild tangent class from
its zero image in ordinary cyclic degree one. The positive survivor is detected by an
augmentation derivation. This module does not assert vanishing in negative cyclic homology.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.SquareZeroCyclic
variable {A : Type*} [Ring A] [Algebra ℂ A]

def pair (a b : A) : CyclicBarTensor ℂ A 1 := PiTensorProduct.tprod ℂ ![a, b]
def triple (a b c : A) : CyclicBarTensor ℂ A 2 := PiTensorProduct.tprod ℂ ![a, b, c]

def boundaryTwo : CyclicBarTensor ℂ A 2 →ₗ[ℂ] CyclicBarTensor ℂ A 1 :=
  (cyclicBarFace (R := ℂ) (A := A) (0 : Fin 3) -
    cyclicBarFace (R := ℂ) (A := A) (1 : Fin 3)) +
  cyclicBarFace (R := ℂ) (A := A) (2 : Fin 3)

@[simp] theorem boundaryTwo_triple (a b c : A) :
    boundaryTwo (triple a b c) = pair (a*b) c - pair a (b*c) + pair (c*a) b := by
  simp only [boundaryTwo, triple, LinearMap.add_apply, LinearMap.sub_apply, cyclicBarFace_tprod]
  have h0 : cyclicBarFaceTuple (0 : Fin 3) ![a,b,c] = ![a*b,c] := by
    change cyclicBarFaceTuple (Fin.castSucc (0 : Fin 2)) _ = _
    rw [cyclicBarFaceTuple, Fin.lastCases_castSucc]
    ext j; fin_cases j <;> rfl
  have h1 : cyclicBarFaceTuple (1 : Fin 3) ![a,b,c] = ![a,b*c] := by
    change cyclicBarFaceTuple (Fin.castSucc (1 : Fin 2)) _ = _
    rw [cyclicBarFaceTuple, Fin.lastCases_castSucc]
    ext j; fin_cases j <;> rfl
  have h2 : cyclicBarFaceTuple (2 : Fin 3) ![a,b,c] = ![c*a,b] := by
    change cyclicBarFaceTuple (Fin.last 2) _ = _
    rw [cyclicBarFaceTuple, Fin.lastCases_last]
    ext j; fin_cases j <;> rfl
  rw [h0, h1, h2]
  rfl

private theorem pair_sub_left (a b c : A) : pair (a-b) c = pair a c - pair b c := by
  have h (z : A) : Function.update ![a,c] 0 z = ![z,c] := by
    ext i; fin_cases i <;> simp
  simpa only [pair, h] using
    (PiTensorProduct.tprod ℂ (s := fun _ : Fin 2 => A)).map_update_sub ![a,c] 0 a b

private theorem pair_add_right (a b c : A) : pair a (b+c) = pair a b + pair a c := by
  have h (z : A) : Function.update ![a,b] 1 z = ![a,z] := by
    ext i; fin_cases i <;> simp
  simpa only [pair, h] using
    (PiTensorProduct.tprod ℂ (s := fun _ : Fin 2 => A)).map_update_add ![a,b] 1 b c

@[simp] theorem pair_zero_right (a : A) : pair a 0 = 0 := by
  apply (PiTensorProduct.tprod ℂ).map_coord_zero (1 : Fin 2)
  rfl

@[simp] theorem rotate_pair (a b : A) : cyclicBarRotate (R := ℂ) 1 (pair a b) = pair b a := by
  rw [pair, cyclicBarRotate_tprod]
  have hrot : ((finRotate 2).symm : Fin 2 → Fin 2) = ![1,0] := by decide
  change PiTensorProduct.tprod ℂ (fun i => ![a,b] ((finRotate 2).symm i)) = _
  rw [hrot]
  congr 1
  ext i; fin_cases i <;> rfl


/-- Commuting pairs are cycles for the actual two cyclic-bar faces. -/
theorem pair_is_cycle (a b : A) (h : a*b = b*a) :
    cyclicBarFace (R := ℂ) (0 : Fin 2) (pair a b) =
      cyclicBarFace (R := ℂ) (1 : Fin 2) (pair a b) := by
  have h0 : cyclicBarFaceTuple (0 : Fin 2) ![a,b] = ![a*b] := by
    change cyclicBarFaceTuple (Fin.castSucc (0 : Fin 1)) _ = _
    rw [cyclicBarFaceTuple, Fin.lastCases_castSucc]
    ext j; fin_cases j; rfl
  have h1 : cyclicBarFaceTuple (1 : Fin 2) ![a,b] = ![b*a] := by
    change cyclicBarFaceTuple (Fin.last 1) _ = _
    rw [cyclicBarFaceTuple, Fin.lastCases_last]
    ext j; fin_cases j; rfl
  simp only [pair, cyclicBarFace_tprod, h0, h1, h]

/-- Exact chain representative of a square-zero unit, before imposing cyclic relations. -/
theorem unit_hochschild_decomposition (v : A) (hv : v*v=0) :
    pair (1-v) (1+v) = pair 1 v + boundaryTwo
      (triple 1 1 1 - triple v 1 1 - (1/2 : ℂ) • triple 1 v v) := by
  simp only [pair_sub_left, pair_add_right, map_sub, map_smul, boundaryTwo_triple,
    one_mul, mul_one, hv, pair_zero_right]
  have hhalf (x : CyclicBarTensor ℂ A 1) : (1/2 : ℂ) • (x+x) = x := by
    rw [← two_smul ℂ x, ← mul_smul]
    norm_num
  simp only [sub_self, zero_add, sub_zero, hhalf]
  abel

/-- Explicit boundary plus signed cyclic relation; no nil-invariance theorem is used. -/
theorem unit_cyclic_decomposition (v : A) (hv : v*v=0) :
    pair (1-v) (1+v) = (pair 1 v + pair v 1) + boundaryTwo
      (triple 1 1 1 - (2 : ℂ) • triple v 1 1 - (1/2 : ℂ) • triple 1 v v) := by
  simp only [pair_sub_left, pair_add_right, map_sub, map_smul, boundaryTwo_triple,
    one_mul, mul_one, hv, pair_zero_right]
  have hhalf (x : CyclicBarTensor ℂ A 1) : (1/2 : ℂ) • (x+x) = x := by
    rw [← two_smul ℂ x, ← mul_smul]
    norm_num
  simp only [sub_self, zero_add, sub_zero, hhalf, two_smul ℂ]
  abel

/-- Degree-one ordinary cyclic relations: Hochschild boundaries and signed rotations. -/
def cyclicRelations : Submodule ℂ (CyclicBarTensor ℂ A 1) :=
  LinearMap.range boundaryTwo ⊔
    LinearMap.range (LinearMap.id + (cyclicBarRotate (R := ℂ) (A := A) 1).toLinearMap)

theorem unit_mem_cyclicRelations (v : A) (hv : v*v=0) :
    pair (1-v) (1+v) ∈ cyclicRelations := by
  rw [unit_cyclic_decomposition v hv]
  apply Submodule.add_mem
  · apply (show LinearMap.range (LinearMap.id +
        (cyclicBarRotate (R := ℂ) (A := A) 1).toLinearMap) ≤ cyclicRelations from le_sup_right)
    exact ⟨pair 1 v, by simp only [LinearMap.add_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, rotate_pair]⟩
  · exact (show LinearMap.range boundaryTwo ≤ cyclicRelations (A := A) from le_sup_left) ⟨_, rfl⟩

/-- Hochschild functional supplied by an augmentation and a tangent functional. -/
def augmentationDetector (ε : A →ₐ[ℂ] ℂ) (δ : A →ₗ[ℂ] ℂ) :
    CyclicBarTensor ℂ A 1 →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift (MultilinearMap.mk'
    (fun x : Fin 2 → A => ε (x 0) * δ (x 1))
    (by intro x j a b; fin_cases j <;> simp [Function.update, add_mul, mul_add])
    (by intro x j c a; fin_cases j <;> simp [Function.update, mul_assoc, mul_left_comm]))

@[simp] theorem augmentationDetector_pair (ε : A →ₐ[ℂ] ℂ) (δ : A →ₗ[ℂ] ℂ) (a b : A) :
    augmentationDetector ε δ (pair a b) = ε a * δ b := by
  simp [augmentationDetector, pair]

theorem augmentationDetector_boundaryTwo (ε : A →ₐ[ℂ] ℂ) (δ : A →ₗ[ℂ] ℂ)
    (hδ : ∀ a b, δ (a*b) = ε a * δ b + δ a * ε b) :
    (augmentationDetector ε δ).comp boundaryTwo = 0 := by
  apply PiTensorProduct.ext
  ext x
  change augmentationDetector ε δ (boundaryTwo (PiTensorProduct.tprod ℂ x)) = 0
  have hx : x = ![x 0, x 1, x 2] := by ext i; fin_cases i <;> rfl
  rw [hx]
  change augmentationDetector ε δ (boundaryTwo (triple _ _ _)) = 0
  rw [boundaryTwo_triple]
  simp only [map_add, map_sub, augmentationDetector_pair, map_mul, hδ]
  ring

theorem augmentationDetector_unit (ε : A →ₐ[ℂ] ℂ) (δ : A →ₗ[ℂ] ℂ)
    (hδ1 : δ 1 = 0) (v : A) (hεv : ε v = 0) :
    augmentationDetector ε δ (pair (1-v) (1+v)) = δ v := by
  simp [hδ1, hεv]

/-- Nonzero tangent value certifies a genuine non-boundary in the full tensor complex. -/
theorem unit_not_mem_boundaryTwo_range (ε : A →ₐ[ℂ] ℂ) (δ : A →ₗ[ℂ] ℂ)
    (hδ : ∀ a b, δ (a*b) = ε a * δ b + δ a * ε b) (hδ1 : δ 1 = 0)
    (v : A) (hεv : ε v = 0) (hne : δ v ≠ 0) :
    pair (1-v) (1+v) ∉ LinearMap.range boundaryTwo := by
  rintro ⟨x, hx⟩
  apply hne
  rw [← augmentationDetector_unit ε δ hδ1 v hεv, ← hx]
  exact LinearMap.congr_fun (augmentationDetector_boundaryTwo ε δ hδ) x
end GaloisForLFunctions.RHTower.SquareZeroCyclic
