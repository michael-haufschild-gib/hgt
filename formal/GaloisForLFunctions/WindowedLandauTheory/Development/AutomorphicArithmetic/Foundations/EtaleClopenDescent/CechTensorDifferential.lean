import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechTensorRealization

/-! The joined realization intertwines the tensor and Čech differentials
and carries the tensor grading to cardinality on the joined cover. -/

noncomputable section

open GlobalTheory.CechDR
open scoped TensorProduct

namespace GlobalTheory.WH

variable {k ι κ E M : Type} [Field k] [LinearOrder ι] [LinearOrder κ]
  [Fintype ι] [Fintype κ] [AddCommGroup E] [Module k E] [AddCommGroup M] [Module k M]
  {A : Finset ι → Submodule k E} {B : Finset κ → Submodule k M}
  (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t)
  (hB : ∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t)

local notation "G" => gradedCech A hA
local notation "G'" => gradedCech B hB

theorem tensorToJoined_differential (t : regularCochains A ⊗[k] regularCochains B) :
    tensorToJoined A B (tensorDifferential G G' t) =
      deltaL k (ι ⊕ₗ κ) (E ⊗[k] M) (tensorToJoined A B t) := by
  have e : (tensorToJoined A B).comp (tensorDifferential G G') =
      (deltaL k (ι ⊕ₗ κ) (E ⊗[k] M)).comp (tensorToJoined A B) := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, tensorDifferential, LinearMap.add_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, map_add, tensorToJoined_tmul]
    funext s
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    rw [deltaL_uni]
    simp only [Pi.add_apply, cechJoin, lft_uni, rgt_uni, gradedCech_d_apply, gradedCech_parity_apply,
      map_zsmul, LinearMap.smul_apply]
    have hL : deltaL k ι (E ⊗[k] M) (fun S => (TensorProduct.mk k E M (a.val S)) (b.val J)) I =
        (TensorProduct.mk k E M (deltaL k ι E a.val I)) (b.val J) := by
      rw [deltaL_apply, deltaL_apply]
      change ∑ i ∈ I, cubeSign I i • (TensorProduct.mk k E M).flip (b.val J) (a.val (I.erase i)) =
        (TensorProduct.mk k E M).flip (b.val J)
          (∑ i ∈ I, cubeSign I i • a.val (I.erase i))
      simp only [map_sum, map_zsmul]
    have hR : deltaL k κ (E ⊗[k] M) (fun S => (TensorProduct.mk k E M (a.val I)) (b.val S)) J =
        (TensorProduct.mk k E M (a.val I)) (deltaL k κ M b.val J) := by
      rw [deltaL_apply, deltaL_apply]
      simp only [map_sum, map_zsmul]
    rw [hL, hR]
  exact LinearMap.congr_fun e t

theorem tensorToJoined_projection (p q : ℕ) (t : regularCochains A ⊗[k] regularCochains B)
    (s : Finset (ι ⊕ₗ κ)) :
    tensorToJoined A B (TensorProduct.map ((G).π p) ((G').π q) t) s =
      if (lft s).card = p ∧ (rgt s).card = q then tensorToJoined A B t s else 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply, ite_self]
  | tmul a b =>
    rw [TensorProduct.map_tmul, tensorToJoined_tmul, tensorToJoined_tmul]
    simp only [cechJoin, gradedCech_projection_apply]
    by_cases hI : (lft s).card = p <;> by_cases hJ : (rgt s).card = q <;> simp [hI, hJ]
  | add u v hu hv =>
    rw [map_add, map_add, Pi.add_apply, hu, hv, map_add, Pi.add_apply]
    split_ifs <;> simp

omit [Fintype ι] [Fintype κ] in
private theorem card_joined (s : Finset (ι ⊕ₗ κ)) : s.card = (lft s).card + (rgt s).card := by
  conv_lhs => rw [← uni_lft_rgt s, card_uni]

theorem tensorToJoined_support {n : ℤ} {t : regularCochains A ⊗[k] regularCochains B}
    (ht : t ∈ tensorDegree G G' n) (s : Finset (ι ⊕ₗ κ)) (hs : (s.card : ℤ) ≠ n) :
    tensorToJoined A B t s = 0 := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, b, p, q, hp, hq, hdeg, rfl⟩ := ht
    have e := tensorToJoined_projection hA hB p q (a ⊗ₜ[k] b) s
    rw [TensorProduct.map_tmul, hp, hq] at e
    have hfalse : ¬ ((lft s).card = p ∧ (rgt s).card = q) :=
      fun h => hs (by rw [card_joined, h.1, h.2, hdeg])
    rwa [if_neg hfalse] at e
  | zero => simp
  | add u v _ _ hu hv => simp only [map_add, Pi.add_apply, hu, hv, add_zero]
  | smul c u _ hu => simp only [map_smul, Pi.smul_apply, hu, smul_zero]

theorem tensorDegree_of_joined_support {n : ℤ} (t : regularCochains A ⊗[k] regularCochains B)
    (ht : ∀ s : Finset (ι ⊕ₗ κ), (s.card : ℤ) ≠ n → tensorToJoined A B t s = 0) :
    t ∈ tensorDegree G G' n := by
  let z (p q : ℕ) := TensorProduct.map ((G).π p) ((G').π q) t
  have hz (p q : ℕ) (h : ((p + q : ℕ) : ℤ) = n) (u : regularCochains A ⊗[k] regularCochains B) :
      TensorProduct.map ((G).π p) ((G').π q) u ∈ tensorDegree G G' n := by
    induction u using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add u v hu hv => rw [map_add]; exact add_mem hu hv
    | tmul a b =>
      rw [TensorProduct.map_tmul]
      exact Submodule.subset_span ⟨_, _, p, q, (G).idem p a, (G').idem q b, h, rfl⟩
  have h₀ (p q : ℕ) (h : ((p + q : ℕ) : ℤ) ≠ n) : z p q = 0 := by
    apply tensorToJoined_injective A B
    funext s
    rw [map_zero, Pi.zero_apply]
    dsimp only [z]
    rw [tensorToJoined_projection hA hB]
    split_ifs with hI
    · exact ht s (by rw [card_joined, hI.1, hI.2]; exact h)
    · rfl
  have e : t = ∑ p ∈ Finset.range (G).N, ∑ q ∈ Finset.range (G').N, z p q := by
    apply tensorToJoined_injective A B
    funext s
    symm
    simp only [map_sum, Finset.sum_apply, z, tensorToJoined_projection hA hB]
    have hI : (lft s).card ∈ Finset.range (G).N :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _))
    have hJ : (rgt s).card ∈ Finset.range (G').N :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _))
    rw [Finset.sum_eq_single_of_mem _ hI, Finset.sum_eq_single_of_mem _ hJ]
    · simp
    · intro q _ hq
      simp [Ne.symm hq]
    · intro p _ hp
      simp [Ne.symm hp]
  rw [e]
  refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_
  by_cases h : ((p + q : ℕ) : ℤ) = n
  · exact hz p q h t
  · rw [h₀ p q h]
    exact zero_mem _

end GlobalTheory.WH
