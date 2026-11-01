import GaloisForLFunctions.HeckeKreinToeplitz.Index.CompletedColumnRepresentation
import GaloisForLFunctions.HeckeKreinToeplitz.Index.CommutingIndexOneIsometries
import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula

/-!
# Positive character hyperplanes for index-one kernels

Every Hermitian kernel of negative index at most one on an abelian group
has a character whose zero-mass hyperplane is positive. The completed
column representation has a common nonpositive eigenline. Pairing against
this line transforms by the reflected eigencharacter, and its orthogonal
hyperplane has nonnegative square.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [CommGroup G] {k : G → ℂ}

/-- Index at most one forces positivity on the zero-mass hyperplane of a character.
No boundedness, growth, freeness, or countability condition on the group kernel is needed. -/
theorem exists_positive_character_hyperplane_of_negIndex_le_one
    (hk : IsHermKernel k) (hi : negIndex k ≤ 1) :
    ∃ χ : G →* ℂ, ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
      charEval χ x c = 0 → 0 ≤ hermQuad (gram k x) c := by
  classical
  by_cases hp : IsPosDefKernel k
  · exact ⟨1, fun n x c _ => hp.2 n x c⟩
  obtain ⟨e, he⟩ := exists_negative_unit_column hk hp
  let H := NegativeColumn.Hilbert hk hi e he
  let T : G → (H × ℂ) ≃L[ℂ] (H × ℂ) := NegativeColumn.action hk hi e he
  let E : kernelColumnSpan k →ₗ[ℂ] (H × ℂ) := NegativeColumn.embedding hk hi e he
  have hT : ∀ a v w, IndexOne.pairing (T a v) (T a w) = IndexOne.pairing v w :=
    NegativeColumn.action_pairing hk hi e he
  have hmul (a b : G) (v : H × ℂ) : T (a * b) v = T a (T b v) :=
    NegativeColumn.action_mul hk hi e he a b v
  have hone (v : H × ℂ) : T 1 v = v := NegativeColumn.action_one hk hi e he v
  have hcomm (a b : G) (v : H × ℂ) : T a (T b v) = T b (T a v) := by
    rw [← hmul, ← hmul, mul_comm a b]
  obtain ⟨z, hz, hzT⟩ :=
    IndexOne.exists_common_normalized_nonpositive_eigenvector T hT hcomm
  let w : H × ℂ := (z, 1)
  have heigen (g : G) : T g w = (T g w).2 • w := by
    obtain ⟨a, _, ha⟩ := hzT g
    have hs : (T g w).2 = a := by
      simpa only [Prod.smul_snd, smul_eq_mul, mul_one] using congrArg Prod.snd ha
    rw [hs]
    exact ha
  let α : G →* ℂ :=
    { toFun := fun g => (T g w).2
      map_one' := by rw [hone]
      map_mul' := by
        intro a b
        conv_lhs => rw [hmul, heigen b, map_smul]
        change (T b w).2 * (T a w).2 = (T a w).2 * (T b w).2
        exact mul_comm _ _ }
  let L : (H × ℂ) →ₗ[ℂ] ℂ :=
    { toFun := IndexOne.pairing w
      map_add' := IndexOne.pairing_add_right w
      map_smul' := fun c v => IndexOne.pairing_smul_right c w v }
  have htransform (g : G) (v : H × ℂ) :
      L (T g v) = reflectChar α g * L v := by
    have h := hT g (T g⁻¹ w) v
    have hcancel : T g (T g⁻¹ w) = w := by rw [← hmul, mul_inv_cancel, hone]
    rw [hcancel] at h
    change IndexOne.pairing w (T g v) = conj ((T g⁻¹ w).2) * IndexOne.pairing w v
    rw [h]
    conv_lhs => rw [heigen g⁻¹]
    exact IndexOne.pairing_smul_left _ _ _
  have hpoint (g : G) :
      L (E (kernelColumnPoint k g)) =
        reflectChar α g * L (E (kernelColumnPoint k 1)) := by
    have h := htransform g (E (kernelColumnPoint k 1))
    change L (NegativeColumn.action hk hi e he g
      (NegativeColumn.embedding hk hi e he (kernelColumnPoint k 1))) = _ at h
    rw [NegativeColumn.action_point, mul_one] at h
    exact h
  refine ⟨reflectChar α, fun n x c hc => ?_⟩
  let v : kernelColumnSpan k := ∑ i, c i • kernelColumnPoint k (x i)
  have horth : IndexOne.pairing w (E v) = 0 := by
    change L (E v) = 0
    simp only [v, map_sum, map_smul, smul_eq_mul]
    calc
      ∑ i, c i * L (E (kernelColumnPoint k (x i))) =
          ∑ i, c i * (reflectChar α (x i) * L (E (kernelColumnPoint k 1))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun a : ℂ => c i * a) (hpoint (x i))
      _ = charEval (reflectChar α) x c * L (E (kernelColumnPoint k 1)) := by
        rw [charEval_apply, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        exact (mul_assoc _ _ _).symm
      _ = 0 := by rw [hc, zero_mul]
  have hw : w ≠ 0 := by
    intro h
    have hs := congrArg Prod.snd h
    exact one_ne_zero hs
  have hwq : (IndexOne.pairing w w).re ≤ 0 := by
    rw [IndexOne.pairing_self_nonpos_iff]
    simpa only [w, norm_one] using hz
  have hpos := IndexOne.nonneg_of_orthogonal_nonpositive hw hwq horth
  change 0 ≤ (IndexOne.pairing (NegativeColumn.embedding hk hi e he v)
    (NegativeColumn.embedding hk hi e he v)).re at hpos
  rw [NegativeColumn.embedding_pairing, kernelColumnPoint_sum_self_re hk] at hpos
  exact hpos

/-- A Hermitian abelian kernel has index at most one exactly when some character's
zero-mass hyperplane is positive. -/
theorem negIndex_le_one_iff_positive_character_hyperplane (hk : IsHermKernel k) :
    negIndex k ≤ 1 ↔ ∃ χ : G →* ℂ,
      ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
        charEval χ x c = 0 → 0 ≤ hermQuad (gram k x) c := by
  constructor
  · exact exists_positive_character_hyperplane_of_negIndex_le_one hk
  · rintro ⟨χ, hχ⟩
    rw [negIndex_le_iff]
    intro n x
    have h := ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker
      (gram k x) (fun _ : Fin 1 => charEval χ x)
      (fun c hc => hχ n x c (hc 0))
    simpa only [Fintype.card_fin, Nat.cast_one] using Nat.cast_le.mpr h

#print axioms exists_positive_character_hyperplane_of_negIndex_le_one
#print axioms negIndex_le_one_iff_positive_character_hyperplane

end GaloisForLFunctions.HeckeKreinToeplitz
