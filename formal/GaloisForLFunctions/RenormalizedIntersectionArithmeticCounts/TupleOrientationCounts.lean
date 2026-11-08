import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.OrientationQuotientCounts
import Mathlib.Data.Fintype.EquivFin

/-!
# Orientation quotient counts from distinct point configurations

Signed transporter counting identifies the difference of the actual
orientation-cover and ordinary tuple-orbit counts. Collisions cancel by
an odd swap. Each injective tuple has the sign of its support permutation,
and every n-point support has n! orderings. Canceling the symmetric-group
order gives the intrinsic orientation sum, including degrees zero and one.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset Equiv MulAction
variable {X : Type*} [Fintype X] (n : ℕ)
local instance : MulAction (Perm (Fin n)) (Fin n → X) :=
  permutationTupleAction X (Perm (Fin n)) (Fin n)

/-- Coordinatewise arithmetic motion on tuples commutes with label permutations. -/
def pointTupleMap (f : Perm X) : (Fin n → X) →[Perm (Fin n)] (Fin n → X) where
  toFun x i := f (x i)
  map_smul' _ _ := rfl

/-- The actual finite point support of an injectively ordered configuration. -/
def embeddingSupport (x : Fin n ↪ X) : {T : Finset X // T.card = n} :=
  ⟨univ.image x, by rw [card_image_of_injective _ x.injective, card_univ, Fintype.card_fin]⟩

/-- Orderings of a fixed actual point subset are precisely bijections from the label set. -/
def embeddingSupportFibreEquiv (T : {T : Finset X // T.card = n}) :
    {x : Fin n ↪ X // embeddingSupport n x = T} ≃ (Fin n ≃ T.val) where
  toFun x := Equiv.ofBijective
    (fun i => ⟨x.val i, by
      have h := congrArg Subtype.val x.property
      change univ.image x.val = T.val at h
      rw [← h]
      exact mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩)
    ⟨fun i j h => x.val.injective (congrArg Subtype.val h), by
      intro y
      have h := congrArg Subtype.val x.property
      change univ.image x.val = T.val at h
      have hy : y.val ∈ univ.image x.val := h.symm ▸ y.property
      obtain ⟨i, _, hi⟩ := mem_image.mp hy
      exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩, by
    apply Subtype.ext
    ext x
    simp only [embeddingSupport, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩⟩
  left_inv x := Subtype.ext (Function.Embedding.ext fun _ => rfl)
  right_inv e := Equiv.ext fun _ => rfl

omit [Fintype X] in
/-- Every n-point configuration has precisely n! injective orderings. -/
theorem embeddingSupportFibre_card (T : {T : Finset X // T.card = n}) :
    Nat.card {x : Fin n ↪ X // embeddingSupport n x = T} = n.factorial := by
  rw [Nat.card_congr (embeddingSupportFibreEquiv n T)]
  let e : (Fin n ≃ T.val) ≃ Perm (Fin n) :=
    (Equiv.refl (Fin n)).equivCongr (Finset.equivFinOfCardEq T.property)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

/-- Summing over distinct ordered points contributes exactly the symmetric-group order per support. -/
theorem sum_embeddingSupport (w : {T : Finset X // T.card = n} → ℤ) :
    (∑ x : Fin n ↪ X, w (embeddingSupport n x)) =
      (n.factorial : ℤ) * ∑ T : {T : Finset X // T.card = n}, w T := by
  calc
    _ = ∑ z : (T : {T : Finset X // T.card = n}) ×
        {x : Fin n ↪ X // embeddingSupport n x = T}, w z.1 :=
      (Fintype.sum_equiv (Equiv.sigmaFiberEquiv (embeddingSupport n)) _ _
        (fun z => congrArg w z.2.property.symm)).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp_rw [sum_const, card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
        embeddingSupportFibre_card]
      rw [mul_sum]

omit [Fintype X] in
/-- A repeated coordinate supplies an actual odd stabilizer, canceling signed transporters. -/
theorem pointTuple_transporterSum_collision (f : Perm X) (x : Fin n → X)
    (hx : ¬Function.Injective x) :
    transporterSignSum (pointTupleMap n f) Perm.sign x = 0 := by
  have hp : ∃ a b : Fin n, a ≠ b ∧ x a = x b := by
    by_contra h
    apply hx
    intro a b hab
    by_contra hne
    exact h ⟨a, b, hne, hab⟩
  obtain ⟨a, b, hab, heq⟩ := hp
  apply transporterSignSum_eq_zero_of_odd_stabilizer _ _ x (swap a b)
  · funext i
    change x (swap a b i) = x i
    by_cases ha : i = a
    · subst i
      simpa only [swap_apply_left] using heq.symm
    · by_cases hb : i = b
      · subst i
        simpa only [swap_apply_right] using heq
      · rw [swap_apply_of_ne_of_ne ha hb]
  · exact Perm.sign_swap hab

/-- Invariance of an actual finite point set under the arithmetic permutation. -/
def PointSubsetInvariant (f : Perm X) (T : Finset X) : Prop :=
  ∀ x, f x ∈ T ↔ x ∈ T

/-- Intrinsic orientation of an invariant point set; moving supports contribute zero. -/
def pointSubsetOrientation (f : Perm X) (T : Finset X) : ℤ :=
  if h : PointSubsetInvariant f T then (Perm.sign (f.subtypePerm h) : ℤ) else 0

omit [Fintype X] in
/-- Every actual tuple transporter preserves its point support, including repeated coordinates. -/
theorem pointTuple_transporter_support (f : Perm X) (x : Fin n → X)
    (g : Perm (Fin n)) (hg : g • x = pointTupleMap n f x) :
    PointSubsetInvariant f (univ.image x) := by
  intro p
  constructor
  · intro hp
    obtain ⟨i, _, hi⟩ := mem_image.mp hp
    have he := congrFun hg (g i)
    change x (g.symm (g i)) = f (x (g i)) at he
    rw [g.symm_apply_apply] at he
    exact mem_image.mpr ⟨g i, mem_univ _, f.injective (he.symm.trans hi)⟩
  · intro hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact mem_image.mpr ⟨g⁻¹ i, mem_univ _, congrFun hg i⟩

omit [Fintype X] in
/-- A support moved by Frobenius has no transporter contribution. -/
theorem pointTuple_transporterSum_unstable (f : Perm X) (x : Fin n → X)
    (hx : ¬PointSubsetInvariant f (univ.image x)) :
    transporterSignSum (pointTupleMap n f) Perm.sign x = 0 := by
  unfold transporterSignSum
  apply sum_eq_zero
  intro g _
  exact if_neg (fun hg => hx (pointTuple_transporter_support n f x g hg))

omit [Fintype X] in
/-- The unique transporter of distinct ordered points has the intrinsic support orientation. -/
theorem pointTuple_transporterSum_embedding (f : Perm X) (x : Fin n ↪ X) :
    transporterSignSum (pointTupleMap n f) Perm.sign x =
      pointSubsetOrientation f (embeddingSupport n x).val := by
  classical
  let T := embeddingSupport n x
  by_cases hT : PointSubsetInvariant f T.val
  · let e : Fin n ≃ T.val := embeddingSupportFibreEquiv n T ⟨x, rfl⟩
    let fT := f.subtypePerm hT
    let g : Perm (Fin n) := (e.trans fT.symm).trans e.symm
    have hg : g • (x : Fin n → X) = pointTupleMap n f x := by
      funext i
      change (e (g⁻¹ i)).val = f (e i).val
      change (e (e.symm (fT (e i)))).val = _
      rw [e.apply_symm_apply]
      rfl
    have hu (σ : Perm (Fin n)) (hσ : σ • (x : Fin n → X) = pointTupleMap n f x) : σ = g := by
      apply inv_injective
      apply Equiv.ext
      intro i
      apply x.injective
      exact (congrFun hσ i).trans (congrFun hg i).symm
    have hs : Perm.sign g = Perm.sign fT := by
      calc
        _ = Perm.sign fT⁻¹ := Perm.sign_eq_sign_of_equiv g fT⁻¹ e (fun i => by
          change e (e.symm (fT.symm (e i))) = fT.symm (e i)
          exact e.apply_symm_apply _)
        _ = _ := Perm.sign_inv fT
    rw [pointSubsetOrientation, dif_pos hT]
    unfold transporterSignSum
    rw [sum_eq_single g]
    · rw [if_pos hg, hs]
    · intro σ _ hσ
      exact if_neg (fun hh => hσ (hu σ hh))
    · simp
  · rw [pointSubsetOrientation, dif_neg hT]
    exact pointTuple_transporterSum_unstable n f x hT

private def injectiveTupleEmbeddingEquiv :
    {x : Fin n → X // Function.Injective x} ≃ (Fin n ↪ X) where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x, x.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Signed tuple transporters decompose into n! orderings of actual invariant point supports. -/
theorem sum_pointTuple_transporterSignSum (f : Perm X) :
    (∑ x : Fin n → X, transporterSignSum (pointTupleMap n f) Perm.sign x) =
      (n.factorial : ℤ) * ∑ T : {T : Finset X // T.card = n}, pointSubsetOrientation f T.val := by
  have hi : (∑ x : Fin n → X, transporterSignSum (pointTupleMap n f) Perm.sign x) =
      ∑ x : Fin n ↪ X, transporterSignSum (pointTupleMap n f) Perm.sign x := by
    calc
      _ = ∑ x ∈ univ.filter Function.Injective,
          transporterSignSum (pointTupleMap n f) Perm.sign x := by
        symm
        apply sum_subset (filter_subset _ _)
        intro x _ hx
        apply pointTuple_transporterSum_collision n f x
        simpa only [mem_filter, mem_univ, true_and] using hx
      _ = ∑ x : {x : Fin n → X // Function.Injective x},
          transporterSignSum (pointTupleMap n f) Perm.sign x.val :=
        sum_subtype _ (fun _ => by simp) _
      _ = _ := Fintype.sum_equiv (injectiveTupleEmbeddingEquiv n) _ _ (fun _ => rfl)
  rw [hi]
  simp_rw [pointTuple_transporterSum_embedding]
  exact sum_embeddingSupport n (fun T => pointSubsetOrientation f T.val)

/-- The difference of actual orientation-cover and ordinary orbit counts is the intrinsic subset sign sum. -/
theorem pointTuple_orientationCount_sub (f : Perm X) :
    (orientationFixedOrbitCount Perm.sign (pointTupleMap n f) : ℤ) -
      (equivariantFixedOrbits (pointTupleMap n f)).card =
        ∑ T : {T : Finset X // T.card = n}, pointSubsetOrientation f T.val := by
  have h := orientationFixedOrbitCount_mul Perm.sign (pointTupleMap n f)
  rw [sum_pointTuple_transporterSignSum, Fintype.card_perm, Fintype.card_fin] at h
  have hn : (n.factorial : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply mul_right_cancel₀ hn
  simpa only [mul_comm] using h

#print axioms pointTuple_transporterSum_embedding
#print axioms sum_pointTuple_transporterSignSum
#print axioms pointTuple_orientationCount_sub
#print axioms embeddingSupportFibreEquiv
#print axioms embeddingSupportFibre_card
#print axioms sum_embeddingSupport
#print axioms pointTuple_transporterSum_collision
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
