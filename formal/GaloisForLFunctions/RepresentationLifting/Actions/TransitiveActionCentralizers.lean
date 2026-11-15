import GaloisForLFunctions.RepresentationLifting.Actions.TransitiveAbelianActions

/-!
# Centralizers of transitive abelian actions

A permutation commuting with a transitive abelian action is a unique
translation modulo the action kernel. Evaluation at one point identifies
the centralizer with the labelled set. Consequently its cardinality is
the number of labels, and a commuting symmetry with any fixed point is
the identity. This supplies the automorphism count in Theorem 6.2 of
Kurnosov–Ríos Ortiz, https://arxiv.org/abs/2611.01210.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.TransitiveActions
variable {A X : Type*} [AddCommGroup A] {x₀ : X}

/-- Every symmetry commuting with a transitive abelian action is itself a translation. -/
theorem commutes_iff_translation (ρ : Transitive A X x₀) (τ : Equiv.Perm X) :
    (∀ a, Commute τ (ρ.val a).toMul) ↔ ∃ a, τ = (ρ.val a).toMul := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := ρ.property (τ x₀)
    change act ρ.val a x₀ = τ x₀ at ha
    refine ⟨a, ?_⟩
    ext x
    obtain ⟨b, rfl⟩ := ρ.property x
    have ht : τ (act ρ.val b x₀) = act ρ.val b (τ x₀) :=
      congrArg (fun e : Equiv.Perm X => e x₀) (h b).eq
    change τ (act ρ.val b x₀) = act ρ.val a (act ρ.val b x₀)
    rw [ht, ← ha, act_comm ρ.val b a]
  · rintro ⟨a, rfl⟩ b
    change (ρ.val a + ρ.val b).toMul = (ρ.val b + ρ.val a).toMul
    rw [← map_add, ← map_add, add_comm a b]

def Centralizer (ρ : Transitive A X x₀) :=
  {τ : Equiv.Perm X // ∀ a, Commute τ (ρ.val a).toMul}

private theorem centralizer_eval_injective (ρ : Transitive A X x₀) :
    Function.Injective (fun τ : Centralizer ρ => τ.val x₀) := by
  intro τ υ h
  change τ.val x₀ = υ.val x₀ at h
  apply Subtype.ext
  ext x
  obtain ⟨a, rfl⟩ := ρ.property x
  have ht : τ.val (act ρ.val a x₀) = act ρ.val a (τ.val x₀) :=
    congrArg (fun e : Equiv.Perm X => e x₀) (τ.property a).eq
  have hu : υ.val (act ρ.val a x₀) = act ρ.val a (υ.val x₀) :=
    congrArg (fun e : Equiv.Perm X => e x₀) (υ.property a).eq
  rw [ht, hu, h]

private theorem centralizer_eval_surjective (ρ : Transitive A X x₀) :
    Function.Surjective (fun τ : Centralizer ρ => τ.val x₀) := by
  intro x
  obtain ⟨a, ha⟩ := ρ.property x
  exact ⟨⟨(ρ.val a).toMul, (commutes_iff_translation ρ _).mpr ⟨a, rfl⟩⟩, ha⟩

/-- Evaluation at one label identifies the centralizer with the whole labelled set. -/
def centralizerEquiv (ρ : Transitive A X x₀) : Centralizer ρ ≃ X :=
  Equiv.ofBijective _ ⟨centralizer_eval_injective ρ, centralizer_eval_surjective ρ⟩

/-- A transitive abelian permutation action has exactly as many commuting symmetries as points. -/
theorem card_centralizer (ρ : Transitive A X x₀) : Nat.card (Centralizer ρ) = Nat.card X :=
  Nat.card_congr (centralizerEquiv ρ)

/-- A commuting symmetry with any fixed point is the identity. -/
theorem centralizer_fixedPoint_iff (ρ : Transitive A X x₀) (τ : Centralizer ρ) (x : X) :
    τ.val x = x ↔ τ.val = 1 := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := ρ.property x
    change act ρ.val a x₀ = x at ha
    have ht : τ.val (act ρ.val a x₀) = act ρ.val a (τ.val x₀) :=
      congrArg (fun e : Equiv.Perm X => e x₀) (τ.property a).eq
    have h₀ : τ.val x₀ = x₀ := by
      apply (ρ.val a).toMul.injective
      change act ρ.val a (τ.val x₀) = act ρ.val a x₀
      rw [← ht, ha, h]
    let identity : Centralizer ρ := ⟨1, fun a => by
      change (1 : Equiv.Perm X) * (ρ.val a).toMul = (ρ.val a).toMul * 1
      simp⟩
    have he : τ = identity := centralizer_eval_injective ρ h₀
    exact congrArg Subtype.val he
  · intro h
    rw [h]
    rfl

#print axioms commutes_iff_translation
#print axioms centralizerEquiv
#print axioms card_centralizer
#print axioms centralizer_fixedPoint_iff
end GaloisForLFunctions.RepresentationLifting.TransitiveActions
