import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Tactic

/-!
# Reduced tensor coalgebra

Missing mathlib infrastructure needed by the NHG cyclic `A∞` cards.  This file constructs the
actual reduced tensor module `⊕ n ≥ 1, V^{⊗ n}` and its deconcatenation coproduct.  It also exposes
the tensor-length embeddings, cogenerator corestriction, exact split equivalences, and pure-tensor
formula used by later coderivation and coalgebra-map extensions.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.TensorCoalgebra

open scoped DirectSum TensorProduct

universe u v

/-- Positive tensor lengths. -/
abbrev PositiveNat := {n : ℕ // 0 < n}

/-- Reduced tensor module `⊕ n ≥ 1, V^{⊗ n}`. -/
abbrev Reduced (k : Type u) (V : Type v) [CommRing k] [AddCommGroup V] [Module k V] :=
  ⨁ n : PositiveNat, TensorPower k n.1 V

section

variable (k : Type u) [CommRing k]
variable (V : Type v) [AddCommGroup V] [Module k V]

/-- Embed one homogeneous tensor length into the reduced tensor module. -/
def ofTensor (n : PositiveNat) : TensorPower k n.1 V →ₗ[k] Reduced k V :=
  DirectSum.lof k PositiveNat (fun n : PositiveNat => TensorPower k n.1 V) n

/-- Tensor length one. -/
abbrev oneWeight : PositiveNat := ⟨1, by omega⟩

/-- Canonical equivalence between the first tensor power and the cogenerator module. -/
def tensorPowerOneEquiv : TensorPower k 1 V ≃ₗ[k] V :=
  PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : Fin 1 => V) 0

/-- Corestriction from the reduced tensor module to its cogenerators. -/
def cogenerator : Reduced k V →ₗ[k] V :=
  tensorPowerOneEquiv k V ∘ₗ
    DirectSum.component k PositiveNat (fun n : PositiveNat => TensorPower k n.1 V) oneWeight

@[simp]
theorem cogenerator_ofTensor_one (x : TensorPower k 1 V) :
    cogenerator k V (ofTensor k V oneWeight x) = tensorPowerOneEquiv k V x := by
  simp [cogenerator, ofTensor]

/-- Cast a tensor power into a split length and undo tensor concatenation. -/
noncomputable def splitAt (n i : ℕ) (hi : i ≤ n) :
    TensorPower k n V ≃ₗ[k] TensorPower k i V ⊗[k] TensorPower k (n - i) V :=
  (TensorPower.cast k V (Nat.add_sub_of_le hi).symm).trans
    (TensorPower.mulEquiv (R := k) (M := V)).symm

/-- Initial `i` entries of an `n`-tuple. -/
noncomputable def takePart {n i : ℕ} (hi : i ≤ n) (x : Fin n → V) : Fin i → V :=
  fun j => x (Fin.castLE hi j)

/-- Final `n-i` entries of an `n`-tuple. -/
noncomputable def dropPart {n i : ℕ} (hi : i ≤ n) (x : Fin n → V) : Fin (n - i) → V :=
  fun j => x (Fin.cast (Nat.add_sub_of_le hi) (Fin.natAdd i j))

/-- `splitAt` sends a pure tensor to its prefix tensored with its suffix. -/
theorem splitAt_tprod (n i : ℕ) (hi : i ≤ n) (x : Fin n → V) :
    splitAt k V n i hi (PiTensorProduct.tprod k x) =
      PiTensorProduct.tprod k (takePart V hi x) ⊗ₜ[k]
        PiTensorProduct.tprod k (dropPart V hi x) := by
  apply (TensorPower.mulEquiv (R := k) (M := V)).injective
  simp only [splitAt, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [← TensorPower.gMul_def, TensorPower.tprod_mul_tprod, TensorPower.cast_tprod]
  congr 1
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro q
    rw [Fin.append_left]
    simp only [Function.comp_apply, takePart]
    apply congrArg x
    apply Fin.ext
    simp
  · intro q
    rw [Fin.append_right]
    simp only [Function.comp_apply, dropPart]

/-- Left positive length at an internal cut. -/
abbrev cutLeft (n : PositiveNat) (i : Fin (n.1 - 1)) : PositiveNat :=
  ⟨i.1 + 1, Nat.succ_pos i.1⟩

/-- Right positive length at an internal cut. -/
abbrev cutRight (n : PositiveNat) (i : Fin (n.1 - 1)) : PositiveNat :=
  ⟨n.1 - (i.1 + 1), by omega⟩

theorem cut_lt (n : PositiveNat) (i : Fin (n.1 - 1)) : i.1 + 1 < n.1 := by
  omega

/-- One summand of deconcatenation at a specified internal cut. -/
noncomputable def cutMap (n : PositiveNat) (i : Fin (n.1 - 1)) :
    TensorPower k n.1 V →ₗ[k] Reduced k V ⊗[k] Reduced k V :=
  (TensorProduct.map
    (ofTensor k V (cutLeft n i))
    (ofTensor k V (cutRight n i))).comp
      (splitAt k V n.1 (i.1 + 1) (cut_lt n i).le).toLinearMap

/-- Exact pure-tensor formula for one deconcatenation cut. -/
theorem cutMap_tprod (n : PositiveNat) (i : Fin (n.1 - 1)) (x : Fin n.1 → V) :
    cutMap k V n i (PiTensorProduct.tprod k x) =
      ofTensor k V (cutLeft n i)
          (PiTensorProduct.tprod k (takePart V (cut_lt n i).le x)) ⊗ₜ[k]
        ofTensor k V (cutRight n i)
          (PiTensorProduct.tprod k (dropPart V (cut_lt n i).le x)) := by
  rw [cutMap, LinearMap.comp_apply]
  change TensorProduct.map _ _
    (splitAt k V n.1 (i.1 + 1) (cut_lt n i).le (PiTensorProduct.tprod k x)) = _
  have hsplit := splitAt_tprod k V n.1 (i.1 + 1) (cut_lt n i).le x
  rw [hsplit, TensorProduct.map_tmul]

/-- Deconcatenation on a fixed positive tensor length. -/
noncomputable def homogeneousComul (n : PositiveNat) :
    TensorPower k n.1 V →ₗ[k] Reduced k V ⊗[k] Reduced k V :=
  ∑ i : Fin (n.1 - 1), cutMap k V n i

/-- Reduced deconcatenation coproduct.  Length one is primitive in the reduced sense and therefore
has coproduct zero; length `n` is the sum over its `n-1` internal cuts. -/
noncomputable def comul : Reduced k V →ₗ[k] Reduced k V ⊗[k] Reduced k V :=
  DirectSum.toModule k PositiveNat (Reduced k V ⊗[k] Reduced k V) (homogeneousComul k V)

@[simp]
theorem comul_ofTensor (n : PositiveNat) (x : TensorPower k n.1 V) :
    comul k V (ofTensor k V n x) = homogeneousComul k V n x := by
  simp [comul, ofTensor]

/-- Full pure-tensor deconcatenation formula. -/
theorem comul_tprod (n : PositiveNat) (x : Fin n.1 → V) :
    comul k V (ofTensor k V n (PiTensorProduct.tprod k x)) =
      ∑ i : Fin (n.1 - 1),
        ofTensor k V (cutLeft n i)
            (PiTensorProduct.tprod k (takePart V (cut_lt n i).le x)) ⊗ₜ[k]
          ofTensor k V (cutRight n i)
            (PiTensorProduct.tprod k (dropPart V (cut_lt n i).le x)) := by
  rw [comul_ofTensor]
  simp [homogeneousComul, cutMap_tprod]

/-- Tensor length one has zero reduced coproduct. -/
@[simp]
theorem comul_weight_one (x : TensorPower k 1 V) :
    comul k V (ofTensor k V oneWeight x) = 0 := by
  rw [comul_ofTensor]
  simp only [homogeneousComul, oneWeight]
  have huniv : (Finset.univ : Finset (Fin 0)) = ∅ := by
    simp
  rw [huniv, Finset.sum_empty, LinearMap.zero_apply]

/-! ## Taylor insertions -/

/-- Insert one `r`-ary Taylor coefficient after `i` input tensors.  The output has tensor length
`n-r+1`.  This is the linear building block of the unique tensor-coalgebra coderivation with a
specified cogenerator corestriction. -/
noncomputable def insertTaylor (n r i : ℕ) (hr : r ≤ n) (hi : i ≤ n - r)
    (m : TensorPower k r V →ₗ[k] V) :
    TensorPower k n V →ₗ[k] TensorPower k (n - r + 1) V := by
  have hiTotal : i ≤ n := by omega
  have hrTail : r ≤ n - i := by omega
  have hout : i + (1 + (n - i - r)) = n - r + 1 := by omega
  let splitHead : TensorPower k n V →ₗ[k]
      TensorPower k i V ⊗[k] TensorPower k (n - i) V :=
    (splitAt k V n i hiTotal).toLinearMap
  let splitBody :
      (TensorPower k i V ⊗[k] TensorPower k (n - i) V) →ₗ[k]
        (TensorPower k i V ⊗[k]
          (TensorPower k r V ⊗[k] TensorPower k (n - i - r) V)) :=
    LinearMap.lTensor (TensorPower k i V)
      (splitAt k V (n - i) r hrTail).toLinearMap
  let applyTaylor :
      (TensorPower k i V ⊗[k]
          (TensorPower k r V ⊗[k] TensorPower k (n - i - r) V)) →ₗ[k]
        (TensorPower k i V ⊗[k] (V ⊗[k] TensorPower k (n - i - r) V)) :=
    LinearMap.lTensor (TensorPower k i V)
      (TensorProduct.map m (LinearMap.id (R := k) (M := TensorPower k (n - i - r) V)))
  let liftCogenerator :
      (TensorPower k i V ⊗[k] (V ⊗[k] TensorPower k (n - i - r) V)) →ₗ[k]
        (TensorPower k i V ⊗[k]
          (TensorPower k 1 V ⊗[k] TensorPower k (n - i - r) V)) :=
    LinearMap.lTensor (TensorPower k i V)
      (TensorProduct.map (tensorPowerOneEquiv k V).symm.toLinearMap
        (LinearMap.id (R := k) (M := TensorPower k (n - i - r) V)))
  let joinTail :
      (TensorPower k i V ⊗[k]
          (TensorPower k 1 V ⊗[k] TensorPower k (n - i - r) V)) →ₗ[k]
        (TensorPower k i V ⊗[k] TensorPower k (1 + (n - i - r)) V) :=
    LinearMap.lTensor (TensorPower k i V)
      (TensorPower.mulEquiv (R := k) (M := V) (n := 1) (m := n - i - r)).toLinearMap
  let joinHead :
      (TensorPower k i V ⊗[k] TensorPower k (1 + (n - i - r)) V) →ₗ[k]
        TensorPower k (i + (1 + (n - i - r))) V :=
    (TensorPower.mulEquiv (R := k) (M := V) (n := i)
      (m := 1 + (n - i - r))).toLinearMap
  exact (TensorPower.cast k V hout).toLinearMap ∘ₗ joinHead ∘ₗ joinTail ∘ₗ
    liftCogenerator ∘ₗ applyTaylor ∘ₗ splitBody ∘ₗ splitHead

end

end HTGeometry.NomologicalHomotopyGeometry.TensorCoalgebra
