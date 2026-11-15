import GaloisForLFunctions.RepresentationLifting.Actions.TransitiveAbelianActions
import GaloisForLFunctions.RepresentationLifting.Actions.PointedFiniteLabellings
import GaloisForLFunctions.RepresentationLifting.Actions.TransitiveActionCentralizers
import GaloisForLFunctions.RepresentationLifting.Lattices.RankTwoHermite

/-!
# Counting transitive commuting permutation pairs

An ordered commuting pair on `m` labels is an action of `ℤ²`. Transitivity
identifies the labels with the quotient by an index-`m` lattice. Fixing the
origin leaves `(m-1)!` labellings for each lattice, while Hermite coordinates
count the lattices by `σ₁(m)`. The common centralizer consists of joint powers
of the two permutations and has cardinality `m`. These are the permutation
and automorphism counts in Theorem 6.2 of Kurnosov–Ríos Ortiz,
https://arxiv.org/abs/2611.01210.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.TransitiveActions
open scoped BigOperators

/-- The integral parameter group for two commuting permutations. -/
abbrev RankTwo := Fin 2 → ℤ

def firstBasis : RankTwo := ![1, 0]
def secondBasis : RankTwo := ![0, 1]

theorem rankTwo_decompose (v : RankTwo) :
    v = v 0 • firstBasis + v 1 • secondBasis := by
  ext i
  fin_cases i <;> simp [firstBasis, secondBasis]

/-- Ordered pairs of commuting permutations. -/
def CommutingPairs (X : Type*) :=
  {p : Equiv.Perm X × Equiv.Perm X // Commute p.1 p.2}

/-- Joint integer powers realize the associated integral action. -/
def pairHom {X : Type*} (p : CommutingPairs X) : ActionHom RankTwo X where
  toFun v := Additive.ofMul (p.val.1 ^ v 0 * p.val.2 ^ v 1)
  map_zero' := by change p.val.1 ^ (0 : ℤ) * p.val.2 ^ (0 : ℤ) = 1; simp
  map_add' u v := by
    change p.val.1 ^ (u 0 + v 0) * p.val.2 ^ (u 1 + v 1) =
      (p.val.1 ^ u 0 * p.val.2 ^ u 1) * (p.val.1 ^ v 0 * p.val.2 ^ v 1)
    rw [zpow_add, zpow_add]
    calc
      _ = p.val.1 ^ u 0 * (p.val.1 ^ v 0 * p.val.2 ^ u 1) * p.val.2 ^ v 1 := by
        simp only [mul_assoc]
      _ = p.val.1 ^ u 0 * (p.val.2 ^ u 1 * p.val.1 ^ v 0) * p.val.2 ^ v 1 := by
        rw [(p.property.zpow_zpow (v 0) (u 1)).eq]
      _ = _ := by simp only [mul_assoc]

@[simp] theorem act_pairHom {X : Type*} (p : CommutingPairs X) (v : RankTwo) (x : X) :
    act (pairHom p) v x = (p.val.1 ^ v 0 * p.val.2 ^ v 1) x := rfl

/-- Evaluation on the two standard basis vectors recovers the generators. -/
def pairOfHom {X : Type*} (ρ : ActionHom RankTwo X) : CommutingPairs X :=
  ⟨((ρ firstBasis).toMul, (ρ secondBasis).toMul), by
    change (ρ firstBasis + ρ secondBasis).toMul = (ρ secondBasis + ρ firstBasis).toMul
    rw [← map_add, ← map_add, add_comm firstBasis secondBasis]⟩

theorem pairHom_pairOfHom {X : Type*} (ρ : ActionHom RankTwo X) : pairHom (pairOfHom ρ) = ρ := by
  apply AddMonoidHom.ext
  intro v
  have hv := congrArg ρ (rankTwo_decompose v)
  simp only [map_add, map_zsmul] at hv
  change (ρ firstBasis).toMul ^ v 0 * (ρ secondBasis).toMul ^ v 1 = (ρ v).toMul
  rw [hv]
  rfl

theorem pairOfHom_pairHom {X : Type*} (p : CommutingPairs X) : pairOfHom (pairHom p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · change p.val.1 ^ (1 : ℤ) * p.val.2 ^ (0 : ℤ) = p.val.1
    simp
  · change p.val.1 ^ (0 : ℤ) * p.val.2 ^ (1 : ℤ) = p.val.2
    simp

/-- Transitivity of two commuting permutations is the transitivity of their integral action. -/
theorem transitivity_pairHom_iff {X : Type*} (p : CommutingPairs X) (x₀ : X) :
    Function.Surjective (fun v => act (pairHom p) v x₀) ↔
      ∀ x, ∃ a b : ℤ, (p.val.1 ^ a * p.val.2 ^ b) x₀ = x := by
  constructor
  · intro h x
    obtain ⟨v, hv⟩ := h x
    exact ⟨v 0, v 1, hv⟩
  · intro h x
    obtain ⟨a, b, hab⟩ := h x
    exact ⟨![a, b], hab⟩

/-- Ordered commuting permutation pairs whose joint action reaches every label. -/
def TransitivePairs (X : Type*) (x₀ : X) :=
  {p : Equiv.Perm X × Equiv.Perm X //
    Commute p.1 p.2 ∧ ∀ x, ∃ a b : ℤ, (p.1 ^ a * p.2 ^ b) x₀ = x}

/-- Transitive integral actions and transitive commuting pairs contain exactly the same data. -/
def transitivePairEquiv {X : Type*} (x₀ : X) :
    Transitive RankTwo X x₀ ≃ TransitivePairs X x₀ where
  toFun ρ := ⟨(pairOfHom ρ.val).val, (pairOfHom ρ.val).property,
    (transitivity_pairHom_iff (pairOfHom ρ.val) x₀).mp
      (by rw [pairHom_pairOfHom]; exact ρ.property)⟩
  invFun p := ⟨pairHom ⟨p.val, p.property.1⟩,
    (transitivity_pairHom_iff ⟨p.val, p.property.1⟩ x₀).mpr p.property.2⟩
  left_inv ρ := Subtype.ext (pairHom_pairOfHom ρ.val)
  right_inv p := by
    apply Subtype.ext
    exact congrArg (fun q : CommutingPairs X => q.val)
      (pairOfHom_pairHom ⟨p.val, p.property.1⟩)

open GaloisForLFunctions.RepresentationLifting

/-- Each index-`n+1` kernel admits exactly `n!` pointed quotient labellings. -/
theorem card_transitiveActions (n : ℕ) :
    Nat.card (Transitive RankTwo (Fin (n + 1)) 0) =
      n.factorial * ∑ d ∈ (n + 1).divisors, d := by
  classical
  let Λ := {L : Submodule ℤ RankTwo // Nat.card (RankTwo ⧸ L) = Nat.card (Fin (n + 1))}
  let E : {L : Submodule ℤ RankTwo // Nat.card (RankTwo ⧸ L) = n + 1} ≃ Λ :=
    { toFun := fun L => ⟨L.val, L.property.trans (Nat.card_fin (n + 1)).symm⟩
      invFun := fun L => ⟨L.val, L.property.trans (Nat.card_fin (n + 1))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  letI : Fintype (RankTwoHermite.Parameters (n + 1)) := by
    unfold RankTwoHermite.Parameters
    infer_instance
  letI : Finite Λ := Finite.of_equiv (RankTwoHermite.Parameters (n + 1))
    ((RankTwoHermite.parametersEquiv n).trans ((RankTwoHermite.latticeEquiv n).trans E))
  letI : Fintype Λ := Fintype.ofFinite Λ
  letI : ∀ L : Λ, Finite (RankTwo ⧸ L.val) := fun L =>
    Nat.finite_of_card_ne_zero (fun h => Nat.succ_ne_zero n
      ((Nat.card_fin (n + 1)).symm.trans (L.property.symm.trans h)))
  rw [← Nat.card_congr (dataEquiv (A := RankTwo) (0 : Fin (n + 1)))]
  unfold Data
  change Nat.card (Σ L : Λ, {e : (RankTwo ⧸ L.val) ≃ Fin (n + 1) // e 0 = 0}) = _
  rw [Nat.card_sigma]
  calc
    (∑ L : Λ, Nat.card {e : (RankTwo ⧸ L.val) ≃ Fin (n + 1) // e 0 = 0}) =
        ∑ _L : Λ, n.factorial := by
      apply Finset.sum_congr rfl
      intro L _
      exact card_pointedEquiv _ 0 n (L.property.trans (Nat.card_fin (n + 1)))
    _ = Nat.card Λ * n.factorial := by simp [Nat.card_eq_fintype_card]
    _ = n.factorial * ∑ d ∈ (n + 1).divisors, d := by
      rw [← Nat.card_congr E, RankTwoHermite.card_sublattices]
      exact Nat.mul_comm _ _

/-- The labelled transitive commuting-pair count from the lattice classification. -/
theorem card_transitivePairs (n : ℕ) :
    Nat.card (TransitivePairs (Fin (n + 1)) 0) =
      n.factorial * ∑ d ∈ (n + 1).divisors, d := by
  rw [← Nat.card_congr (transitivePairEquiv (0 : Fin (n + 1))), card_transitiveActions]

/-- Commuting with the two generators is equivalent to commuting with the integral action. -/
theorem commutes_pairHom_iff {X : Type*} (p : CommutingPairs X) (υ : Equiv.Perm X) :
    (∀ v, Commute υ (pairHom p v).toMul) ↔ Commute υ p.val.1 ∧ Commute υ p.val.2 := by
  constructor
  · intro h
    constructor
    · simpa [pairHom, firstBasis] using h firstBasis
    · simpa [pairHom, secondBasis] using h secondBasis
  · rintro ⟨h₁, h₂⟩ v
    have hs : Commute υ (p.val.1 ^ v 0) := by
      simpa only [zpow_one] using h₁.zpow_zpow 1 (v 0)
    have ht : Commute υ (p.val.2 ^ v 1) := by
      simpa only [zpow_one] using h₂.zpow_zpow 1 (v 1)
    change υ * (p.val.1 ^ v 0 * p.val.2 ^ v 1) = (p.val.1 ^ v 0 * p.val.2 ^ v 1) * υ
    rw [← mul_assoc, hs.eq, mul_assoc, ht.eq, ← mul_assoc]

/-- The common centralizer of a transitive commuting pair consists exactly of its joint powers. -/
theorem commutes_pair_iff_joint_power {X : Type*} {x₀ : X}
    (p : TransitivePairs X x₀) (υ : Equiv.Perm X) :
    (Commute υ p.val.1 ∧ Commute υ p.val.2) ↔
      ∃ a b : ℤ, υ = p.val.1 ^ a * p.val.2 ^ b := by
  let ρ := (transitivePairEquiv x₀).symm p
  constructor
  · intro h
    have hc : ∀ v, Commute υ (ρ.val v).toMul :=
      (commutes_pairHom_iff ⟨p.val, p.property.1⟩ υ).mpr h
    obtain ⟨v, hv⟩ := (commutes_iff_translation ρ υ).mp hc
    exact ⟨v 0, v 1, hv⟩
  · rintro ⟨a, b, hab⟩
    apply (commutes_pairHom_iff ⟨p.val, p.property.1⟩ υ).mp
    exact (commutes_iff_translation ρ υ).mpr ⟨![a, b], hab⟩

/-- Evaluation identifies the common centralizer of a transitive pair with its labels. -/
def commonCentralizerEquiv {X : Type*} {x₀ : X} (p : TransitivePairs X x₀) :
    {υ : Equiv.Perm X // Commute υ p.val.1 ∧ Commute υ p.val.2} ≃ X := by
  let ρ := (transitivePairEquiv x₀).symm p
  let e : {υ : Equiv.Perm X // Commute υ p.val.1 ∧ Commute υ p.val.2} ≃ Centralizer ρ :=
    { toFun := fun υ => ⟨υ.val, (commutes_pairHom_iff ⟨p.val, p.property.1⟩ υ.val).mpr υ.property⟩
      invFun := fun υ => ⟨υ.val, (commutes_pairHom_iff ⟨p.val, p.property.1⟩ υ.val).mp υ.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.trans (centralizerEquiv ρ)

/-- A transitive commuting pair on `n+1` labels has `n+1` common commuting symmetries. -/
theorem card_commonCentralizer (n : ℕ) (p : TransitivePairs (Fin (n + 1)) 0) :
    Nat.card {υ : Equiv.Perm (Fin (n + 1)) // Commute υ p.val.1 ∧ Commute υ p.val.2} = n + 1 := by
  rw [Nat.card_congr (commonCentralizerEquiv p), Nat.card_fin]

#print axioms transitivePairEquiv
#print axioms card_transitiveActions
#print axioms card_transitivePairs
#print axioms commutes_pair_iff_joint_power
#print axioms card_commonCentralizer
end GaloisForLFunctions.RepresentationLifting.TransitiveActions
