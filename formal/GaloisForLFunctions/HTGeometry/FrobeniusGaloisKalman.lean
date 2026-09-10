import GaloisForLFunctions.HTGeometry.FrobeniusGaloisObservation
import Mathlib.Tactic.Tauto

/-!
# Kalman extension of observable properties

The powerset instance of the Kalman construction and its Frobenius lift from
arXiv:2609.09529, Theorem 4.6 and Proposition 4.14. A disjoint pair records
positive and negative information, ordered with the negative coordinate reversed.
-/
namespace GaloisForLFunctions.HTGeometry.FrobeniusGalois

/-- Consistent positive and negative information about states. -/
structure Twist (X : Type*) where
  pos : Set X
  neg : Set X
  consistent : ∀ x, x ∈ pos → x ∉ neg

namespace Twist
variable {X Y : Type*}

@[ext] theorem ext (a b : Twist X) (hp : a.pos = b.pos) (hn : a.neg = b.neg) : a = b := by
  cases a
  cases b
  cases hp
  cases hn
  rfl

instance : PartialOrder (Twist X) where
  le a b := a.pos ⊆ b.pos ∧ b.neg ⊆ a.neg
  le_refl a := ⟨fun _ h => h, fun _ h => h⟩
  le_trans a b c hab hbc := ⟨fun _ h => hbc.1 (hab.1 h), fun _ h => hab.2 (hbc.2 h)⟩
  le_antisymm a b hab hba := ext a b (Set.Subset.antisymm hab.1 hba.1)
    (Set.Subset.antisymm hba.2 hab.2)

def negate (a : Twist X) : Twist X :=
  ⟨a.neg, a.pos, fun x hn hp => a.consistent x hp hn⟩

def meet (a b : Twist X) : Twist X :=
  ⟨a.pos ∩ b.pos, a.neg ∪ b.neg, by
    intro x hp hn
    exact hn.elim (a.consistent x hp.1) (b.consistent x hp.2)⟩

def join (a b : Twist X) : Twist X :=
  ⟨a.pos ∪ b.pos, a.neg ∩ b.neg, by
    intro x hp hn
    exact hp.elim (fun h => a.consistent x h hn.1) (fun h => b.consistent x h hn.2)⟩

def bottom : Twist X := ⟨∅, Set.univ, fun _ h => False.elim h⟩
def top : Twist X := ⟨Set.univ, ∅, fun _ _ h => h⟩
def center : Twist X := ⟨∅, ∅, fun _ h => False.elim h⟩

def tensor (a b : Twist X) : Twist X :=
  ⟨a.pos ∩ b.pos, implication a.pos b.neg ∩ implication b.pos a.neg, by
    intro x hp hn
    exact b.consistent x hp.2 (hn.1.resolve_left (fun h => h hp.1))⟩

def residual (a b : Twist X) : Twist X :=
  ⟨implication a.pos b.pos ∩ implication b.neg a.neg, b.neg ∩ a.pos, by
    intro x hp hn
    exact b.consistent x (hp.1.resolve_left (fun h => h hn.2)) hn.1⟩

/-- The paper's lifted right adjoint. -/
def necessity (q : X → Y) (a : Twist X) : Twist X :=
  ⟨lower q a.pos, upper q a.neg, by
    rintro x hp ⟨y, hy, he⟩
    exact a.consistent y (hp y he) hy⟩

/-- The left adjoint is recovered by involution, as in Theorem 4.3. -/
def possibility (q : X → Y) (a : Twist X) : Twist X :=
  negate (necessity q (negate a))

theorem negate_negate (a : Twist X) : negate (negate a) = a := rfl

theorem adjunction (q : X → Y) : GaloisConnection (possibility q) (necessity q) := by
  intro a b
  change (upper q a.pos ⊆ b.pos ∧ b.neg ⊆ lower q a.neg) ↔
    (a.pos ⊆ lower q b.pos ∧ upper q b.neg ⊆ a.neg)
  rw [FrobeniusGalois.adjunction q a.pos b.pos,
    ← FrobeniusGalois.adjunction q b.neg a.neg]

theorem necessity_le (q : X → Y) (a : Twist X) : necessity q a ≤ a :=
  ⟨lower_subset q a.pos, subset_upper q a.neg⟩

theorem le_possibility (q : X → Y) (a : Twist X) : a ≤ possibility q a :=
  ⟨subset_upper q a.pos, lower_subset q a.neg⟩

theorem necessity_bottom (q : X → Y) : necessity q (bottom : Twist X) = bottom := by
  apply ext <;> simp [necessity, bottom, lower_empty, upper_univ]

theorem necessity_top (q : X → Y) : necessity q (top : Twist X) = top := by
  apply ext <;> simp [necessity, top, lower_univ, upper_empty]

theorem necessity_center (q : X → Y) : necessity q (center : Twist X) = center := by
  apply ext <;> simp [necessity, center, lower_empty, upper_empty]

theorem necessity_meet (q : X → Y) (a b : Twist X) :
    necessity q (meet a b) = meet (necessity q a) (necessity q b) := by
  apply ext <;> simp [necessity, meet, lower_inter, upper_union]

theorem necessity_necessity (q : X → Y) (a : Twist X) :
    necessity q (necessity q a) = necessity q a := by
  apply ext <;> simp [necessity, lower_idempotent, upper_idempotent]

theorem necessity_possibility (q : X → Y) (a : Twist X) :
    necessity q (possibility q a) = possibility q a := by
  apply ext <;> simp [necessity, possibility, negate, lower_upper, upper_lower]

theorem possibility_necessity (q : X → Y) (a : Twist X) :
    possibility q (necessity q a) = necessity q a := by
  apply ext <;> simp [necessity, possibility, negate, lower_upper, upper_lower]

theorem necessity_join_necessity (q : X → Y) (a b : Twist X) :
    necessity q (join (necessity q a) b) = join (necessity q a) (necessity q b) := by
  apply ext
  · exact lower_lower_union q a.pos b.pos
  · change upper q (upper q a.neg ∩ b.neg) = upper q a.neg ∩ upper q b.neg
    rw [Set.inter_comm, upper_inter_upper, Set.inter_comm]

theorem necessity_meet_center (q : X → Y) (a : Twist X) :
    necessity q (meet a center) = meet (necessity q a) center := by
  rw [necessity_meet, necessity_center]

theorem necessity_join_center (q : X → Y) (a : Twist X) :
    necessity q (join a center) = join (necessity q a) center := by
  apply ext <;> simp [necessity, join, center, upper_empty]

/-- Residual Frobenius compatibility on the twist, Theorem 4.6(8). -/
theorem necessity_residual_necessity (q : X → Y) (a b : Twist X) :
    necessity q (residual (necessity q a) b) =
      residual (necessity q a) (necessity q b) := by
  apply ext
  · change lower q (implication (lower q a.pos) b.pos ∩
        implication b.neg (upper q a.neg)) =
      implication (lower q a.pos) (lower q b.pos) ∩
        implication (upper q b.neg) (upper q a.neg)
    rw [lower_inter, lower_lower_implication, lower_implication_upper]
  · exact upper_inter_lower q b.neg a.pos

theorem necessity_fixed_residual (q : X → Y) (a b : Twist X) :
    necessity q (residual (necessity q a) (necessity q b)) =
      residual (necessity q a) (necessity q b) := by
  rw [necessity_residual_necessity, necessity_necessity]

/-- Positive properties embed above the center. -/
def positive (S : Set X) : Twist X := ⟨S, ∅, fun _ _ h => h⟩

theorem center_le_iff (a : Twist X) : center ≤ a ↔ a.neg = ∅ := by
  constructor
  · intro h
    exact Set.Subset.antisymm h.2 (fun _ h => False.elim h)
  · intro h
    exact ⟨fun _ h => False.elim h, h ▸ (fun _ h => h)⟩

/-- The concrete positive-cone representation of Proposition 4.14. -/
def positiveConeEquiv : Set X ≃ {a : Twist X // center ≤ a} where
  toFun S := ⟨positive S, (center_le_iff _).mpr rfl⟩
  invFun a := a.1.pos
  left_inv _ := rfl
  right_inv a := by
    apply Subtype.ext
    apply ext
    · rfl
    · exact ((center_le_iff a.1).mp a.2).symm

theorem necessity_positive (q : X → Y) (S : Set X) :
    necessity q (positive S) = positive (lower q S) := by
  apply ext <;> simp [necessity, positive, upper_empty]

theorem possibility_positive (q : X → Y) (S : Set X) :
    possibility q (positive S) = positive (upper q S) := by
  apply ext <;> simp [possibility, necessity, negate, positive, lower_empty]

/-- Both coordinates are recovered from the positive cone. -/
theorem join_center (a : Twist X) : join a center = positive a.pos := by
  apply ext <;> simp [join, center, positive]

/-- Every twist is uniquely determined by its two positive-cone projections. -/
theorem positive_projections_injective :
    Function.Injective (fun a : Twist X => (join a center, join (negate a) center)) := by
  intro a b h
  apply ext
  · simpa [join, center] using congrArg (fun p : Twist X × Twist X => p.1.pos) h
  · simpa [join, center, negate] using congrArg (fun p : Twist X × Twist X => p.2.pos) h

/-- The twist product and residual satisfy the actual residuation law. -/
theorem residuation (a b c : Twist X) : tensor a b ≤ c ↔ b ≤ residual a c := by
  classical
  constructor
  · intro h
    constructor
    · intro x hb
      constructor
      · by_cases ha : x ∈ a.pos
        · exact Or.inr (h.1 ⟨ha, hb⟩)
        · exact Or.inl ha
      · by_cases hc : x ∈ c.neg
        · exact Or.inr ((h.2 hc).2.resolve_left (fun hn => hn hb))
        · exact Or.inl hc
    · intro x hx
      exact (h.2 hx.1).1.resolve_left (fun hn => hn hx.2)
  · intro h
    constructor
    · intro x hx
      exact (h.1 hx.2).1.resolve_left (fun hn => hn hx.1)
    · intro x hc
      constructor
      · by_cases ha : x ∈ a.pos
        · exact Or.inr (h.2 ⟨hc, ha⟩)
        · exact Or.inl ha
      · by_cases hb : x ∈ b.pos
        · exact Or.inr ((h.1 hb).2.resolve_left (fun hn => hn hc))
        · exact Or.inl hb

theorem tensor_comm (a b : Twist X) : tensor a b = tensor b a := by
  apply ext <;> simp [tensor, Set.inter_comm]

theorem tensor_assoc (a b c : Twist X) :
    tensor (tensor a b) c = tensor a (tensor b c) := by
  apply ext <;> ext x
  · simp [tensor, and_assoc]
  · have ha := a.consistent x
    have hb := b.consistent x
    have hc := c.consistent x
    simp only [tensor, implication, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    tauto

theorem tensor_top (a : Twist X) : tensor a top = a := by
  apply ext
  · simp [tensor, top]
  · ext x
    have ha := a.consistent x
    simp only [tensor, top, implication, Set.mem_inter_iff, Set.mem_union,
      Set.mem_compl_iff, Set.mem_univ, Set.mem_empty_iff_false]
    tauto

/-- The bottom, rather than the excluded pair `(univ, univ)`, gives swap negation. -/
theorem residual_bottom (a : Twist X) : residual a bottom = negate a := by
  apply ext
  · ext x
    have ha := a.consistent x
    simp only [residual, bottom, negate, implication, Set.mem_inter_iff,
      Set.mem_union, Set.mem_compl_iff, Set.mem_empty_iff_false, Set.mem_univ]
    tauto
  · simp [residual, bottom, negate]

theorem necessity_residual_le (q : X → Y) (a b : Twist X) :
    necessity q (residual a b) ≤ residual (necessity q a) (necessity q b) := by
  classical
  constructor
  · intro x hx
    have hp := hx
    change x ∈ lower q (implication a.pos b.pos ∩ implication b.neg a.neg) at hp
    rw [lower_inter] at hp
    refine ⟨lower_implication_subset q a.pos b.pos hp.1, ?_⟩
    by_cases hn : x ∈ upper q b.neg
    · obtain ⟨y, hy, he⟩ := hn
      exact Or.inr ⟨y, (hp.2 y he).resolve_left (fun h => h hy), he⟩
    · exact Or.inl hn
  · rintro x ⟨⟨y, hy, he⟩, hp⟩
    exact ⟨y, ⟨hy, hp y he⟩, he⟩

theorem necessity_tensor_le (q : X → Y) (a b : Twist X) :
    tensor (necessity q a) (necessity q b) ≤ necessity q (tensor a b) := by
  classical
  constructor
  · intro x hx y hy
    exact ⟨hx.1 y hy, hx.2 y hy⟩
  · rintro x ⟨y, hy, he⟩
    constructor
    · by_cases hp : x ∈ lower q a.pos
      · exact Or.inr ⟨y, hy.1.resolve_left (fun hn => hn (hp y he)), he⟩
      · exact Or.inl hp
    · by_cases hp : x ∈ lower q b.pos
      · exact Or.inr ⟨y, hy.2.resolve_left (fun hn => hn (hp y he)), he⟩
      · exact Or.inl hp

/-- The differential law at the center holds for the full twist product. -/
theorem center_differential (a b : Twist X) :
    meet (tensor a b) center =
      join (tensor (meet a center) b) (tensor a (meet b center)) := by
  apply ext <;> ext x
  · simp [meet, tensor, join, center]
  · have ha := a.consistent x
    have hb := b.consistent x
    simp only [meet, tensor, join, center, implication, Set.mem_inter_iff,
      Set.mem_union, Set.mem_compl_iff, Set.mem_empty_iff_false]
    tauto

theorem positive_meet (S T : Set X) : meet (positive S) (positive T) = positive (S ∩ T) := by
  apply ext <;> simp [meet, positive]

theorem positive_join (S T : Set X) : join (positive S) (positive T) = positive (S ∪ T) := by
  apply ext <;> simp [join, positive]

/-- Positive-cone multiplication is the centered truncation of twist multiplication. -/
theorem positive_tensor (S T : Set X) :
    join (tensor (positive S) (positive T)) center = positive (S ∩ T) := by
  rw [join_center]
  rfl

theorem positive_residual (S T : Set X) :
    residual (positive S) (positive T) = positive (implication S T) := by
  apply ext <;> simp [residual, positive, implication]

/-- The CK gluing condition is exactly disjointness of the two positive properties. -/
theorem positive_gluing_iff (S T : Set X) :
    S ∩ T = ∅ ↔ ∃ a : Twist X,
      join a center = positive S ∧ join (negate a) center = positive T := by
  constructor
  · intro h
    let a : Twist X := ⟨S, T, fun x hs ht => by
      have hx : x ∈ S ∩ T := ⟨hs, ht⟩
      rw [h] at hx
      exact hx⟩
    exact ⟨a, join_center a, join_center (negate a)⟩
  · rintro ⟨a, hp, hn⟩
    have hs : a.pos = S := by simpa [join, center, positive] using congrArg Twist.pos hp
    have ht : a.neg = T := by
      simpa [join, center, positive, negate] using congrArg Twist.pos hn
    ext x
    constructor
    · rintro ⟨hx, hy⟩
      exact a.consistent x (hs ▸ hx) (ht ▸ hy)
    · exact False.elim

end Twist
end GaloisForLFunctions.HTGeometry.FrobeniusGalois
