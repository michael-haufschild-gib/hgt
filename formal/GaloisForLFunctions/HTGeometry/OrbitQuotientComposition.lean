import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Orbits of a group on the orbit space of a normal subgroup

For a normal subgroup `N` of `G` acting on a set `S`, the group `G` acts on the `N`-orbit space,
and its orbits there are exactly the `G`-orbits on `S`.  This is the formal content of the
iterated descent `(S / N) / (G / N) = S / G`.
-/

namespace HTGeometry

open MulAction

variable {G S : Type*} [Group G] [MulAction G S] (N : Subgroup G) [N.Normal]

/-- A group acts on the orbit space of a normal subgroup. -/
instance orbitRelQuotientAction : MulAction G (orbitRel.Quotient N S) where
  smul g := Quotient.map (fun s => g • s) (by
    intro a b hab
    obtain ⟨n, hn⟩ := hab
    refine ⟨⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem ‹N.Normal› (n : G) n.2 g⟩, ?_⟩
    show (g * (n : G) * g⁻¹) • (g • b) = g • a
    rw [← hn]
    show (g * (n : G) * g⁻¹) • (g • b) = g • ((n : G) • b)
    rw [← mul_smul, ← mul_smul]
    congr 1
    rw [mul_assoc (g * (n : G)), inv_mul_cancel, mul_one])
  one_smul := by
    rintro ⟨s⟩
    show (Quotient.mk _ ((1 : G) • s) : orbitRel.Quotient N S) = Quotient.mk _ s
    rw [one_smul]
  mul_smul := by
    rintro g h ⟨s⟩
    show (Quotient.mk _ ((g * h) • s) : orbitRel.Quotient N S) = Quotient.mk _ (g • h • s)
    rw [mul_smul]

@[simp] theorem orbitRelQuotient_smul_mk (g : G) (s : S) :
    g • (Quotient.mk _ s : orbitRel.Quotient N S) = Quotient.mk _ (g • s) := rfl

/-- The projection from the `N`-orbit space to the `G`-orbit space. -/
def orbitQuotientProj : orbitRel.Quotient N S → orbitRel.Quotient G S :=
  Quotient.lift (fun s => (Quotient.mk _ s : orbitRel.Quotient G S)) (by
    intro a b hab
    obtain ⟨n, hn⟩ := hab
    refine Quotient.sound ⟨(n : G), hn⟩)

omit [N.Normal] in
@[simp] theorem orbitQuotientProj_mk (s : S) :
    orbitQuotientProj N (Quotient.mk _ s : orbitRel.Quotient N S)
      = (Quotient.mk _ s : orbitRel.Quotient G S) := rfl

/-- **The `G`-orbits on the `N`-orbit space are the `G`-orbits on `S`.** -/
def orbitQuotientQuotientEquiv :
    orbitRel.Quotient G (orbitRel.Quotient N S) ≃ orbitRel.Quotient G S where
  toFun := Quotient.lift (orbitQuotientProj N) (by
    rintro ⟨a⟩ ⟨b⟩ hab
    obtain ⟨g, hg⟩ := hab
    have hg' : (Quotient.mk _ (g • b) : orbitRel.Quotient N S) = Quotient.mk _ a := hg
    obtain ⟨n, hn⟩ := Quotient.exact hg'
    have hn' : (n : G) • a = g • b := hn
    refine Quotient.sound ⟨(n : G)⁻¹ * g, ?_⟩
    show ((n : G)⁻¹ * g) • b = a
    rw [mul_smul, ← hn', ← mul_smul, inv_mul_cancel, one_smul])
  invFun := Quotient.lift
    (fun s => (Quotient.mk _ (Quotient.mk _ s : orbitRel.Quotient N S) :
      orbitRel.Quotient G (orbitRel.Quotient N S))) (by
    intro a b hab
    obtain ⟨g, hg⟩ := hab
    have hg' : g • b = a := hg
    refine Quotient.sound ⟨g, ?_⟩
    show (Quotient.mk _ (g • b) : orbitRel.Quotient N S) = Quotient.mk _ a
    rw [hg'])
  left_inv := by
    rintro ⟨⟨s⟩⟩
    rfl
  right_inv := by
    rintro ⟨s⟩
    rfl

@[simp] theorem orbitQuotientQuotientEquiv_mk (s : S) :
    orbitQuotientQuotientEquiv N
        (Quotient.mk _ (Quotient.mk _ s : orbitRel.Quotient N S))
      = (Quotient.mk _ s : orbitRel.Quotient G S) := rfl

end HTGeometry
