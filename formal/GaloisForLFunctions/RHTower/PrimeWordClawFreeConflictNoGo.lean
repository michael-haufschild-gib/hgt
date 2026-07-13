import GaloisForLFunctions.RHTower.PrimeWordMatchingIncidenceNoGo

/-!
# Prime-support intersection creates claws exactly beyond the two-port regime

The raw conflict relation joins two finite supports when they intersect.  Three pairwise disjoint
leaves meeting one center inject three distinct witnesses into that center.  Hence a center of
cardinality at most two cannot support an induced claw.  The bound is sharp: the three-letter word
`[0,1,2]` and the three singleton words give the minimal claw.
-/

namespace GaloisForLFunctions.RHTower

/-- Two supports conflict when they intersect. -/
def supportConflict {α : Type*} [DecidableEq α] (s t : Finset α) : Prop :=
  ¬ Disjoint s t

/-- A named center and three leaves form an induced claw for support conflict. -/
def IsSupportConflictClaw {α : Type*} [DecidableEq α]
    (c a b d : Finset α) : Prop :=
  supportConflict c a ∧ supportConflict c b ∧ supportConflict c d ∧
    Disjoint a b ∧ Disjoint a d ∧ Disjoint b d

/-- Three pairwise compatible packets conflicting with one center force three distinct labels in
the center. -/
theorem supportConflict_claw_forces_three_le_card {α : Type*} [DecidableEq α]
    {c a b d : Finset α} (h : IsSupportConflictClaw c a b d) :
    3 ≤ c.card := by
  rcases h with ⟨hca, hcb, hcd, hab, had, hbd⟩
  rcases Finset.not_disjoint_iff.mp hca with ⟨x, hxc, hxa⟩
  rcases Finset.not_disjoint_iff.mp hcb with ⟨y, hyc, hyb⟩
  rcases Finset.not_disjoint_iff.mp hcd with ⟨z, hzc, hzd⟩
  have hxy : x ≠ y := by
    intro hxy
    subst y
    exact (Finset.disjoint_left.mp hab hxa) hyb
  have hxz : x ≠ z := by
    intro hxz
    subst z
    exact (Finset.disjoint_left.mp had hxa) hzd
  have hyz : y ≠ z := by
    intro hyz
    subst z
    exact (Finset.disjoint_left.mp hbd hyb) hzd
  have hsub : ({x, y, z} : Finset α) ⊆ c := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hxc
    · exact hyc
    · exact hzc
  calc
    3 = ({x, y, z} : Finset α).card := by simp [hxy, hxz, hyz]
    _ ≤ c.card := Finset.card_le_card hsub

/-- Positive two-port theorem: supports of cardinality at most two have claw-free intersection
neighborhoods. -/
theorem not_isSupportConflictClaw_of_card_le_two {α : Type*} [DecidableEq α]
    {c a b d : Finset α} (hc : c.card ≤ 2) :
    ¬ IsSupportConflictClaw c a b d := by
  intro h
  have hthree := supportConflict_claw_forces_three_le_card h
  omega

def supportClawCenter : List (Fin 3) := [0, 1, 2]
def supportClawLeaf0 : List (Fin 3) := [0]
def supportClawLeaf1 : List (Fin 3) := [1]
def supportClawLeaf2 : List (Fin 3) := [2]

/-- Sharp no-go: unrestricted prime-support intersection already contains the minimal claw. -/
theorem primeWordSupportConflict_explicit_claw :
    IsSupportConflictClaw
      (GaloisForLFunctions.primeWordSupport supportClawCenter)
      (GaloisForLFunctions.primeWordSupport supportClawLeaf0)
      (GaloisForLFunctions.primeWordSupport supportClawLeaf1)
      (GaloisForLFunctions.primeWordSupport supportClawLeaf2) := by
  simp [IsSupportConflictClaw, supportConflict, supportClawCenter, supportClawLeaf0,
    supportClawLeaf1, supportClawLeaf2, GaloisForLFunctions.primeWordSupport,
    Finset.disjoint_left]

/-- Any proposed raw word-conflict claw with a two-letter center is impossible. -/
theorem primeWordSupportConflict_no_claw_of_center_card_le_two {α : Type*} [DecidableEq α]
    {c a b d : List α}
    (hc : (GaloisForLFunctions.primeWordSupport c).card ≤ 2) :
    ¬ IsSupportConflictClaw
      (GaloisForLFunctions.primeWordSupport c)
      (GaloisForLFunctions.primeWordSupport a)
      (GaloisForLFunctions.primeWordSupport b)
      (GaloisForLFunctions.primeWordSupport d) :=
  not_isSupportConflictClaw_of_card_le_two hc

end GaloisForLFunctions.RHTower
