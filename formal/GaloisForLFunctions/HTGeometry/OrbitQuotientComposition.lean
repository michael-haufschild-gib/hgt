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

/-! ## The slice theorem -/

section Slice

variable {G S : Type*} [Group G] [MulAction G S] (T : Set S) (H : Subgroup G)

/-- **Slice theorem, surjectivity.**  If every point is `G`-equivalent to a point of the slice,
the slice maps onto the orbit space. -/
theorem orbit_slice_surjective
    (hmeet : ∀ s : S, ∃ (g : G) (t : T), g • (t : S) = s) :
    Function.Surjective
      (fun t : T => (Quotient.mk _ (t : S) : orbitRel.Quotient G S)) := by
  rintro ⟨s⟩
  obtain ⟨g, t, hgt⟩ := hmeet s
  refine ⟨t, Quotient.sound ⟨g⁻¹, ?_⟩⟩
  show g⁻¹ • s = (t : S)
  rw [← hgt, ← mul_smul, inv_mul_cancel, one_smul]

/-- **Slice theorem, the fibres.**  If two points of the slice are `G`-equivalent only through
`H`, the fibres of the slice map are the `H`-orbits. -/
theorem orbit_slice_eq_iff
    (hsep : ∀ s t : T, (∃ g : G, g • (s : S) = (t : S)) → ∃ h : H, (h : G) • (s : S) = (t : S))
    (s t : T) :
    (Quotient.mk _ (s : S) : orbitRel.Quotient G S) = Quotient.mk _ (t : S)
      ↔ ∃ h : H, (h : G) • (s : S) = (t : S) := by
  constructor
  · intro hst
    obtain ⟨g, hg⟩ := Quotient.exact hst
    have hg' : g • (t : S) = (s : S) := hg
    obtain ⟨h, hh⟩ := hsep t s ⟨g, hg'⟩
    refine ⟨h⁻¹, ?_⟩
    show ((h : G))⁻¹ • (s : S) = (t : S)
    rw [← hh, ← mul_smul, inv_mul_cancel, one_smul]
  · rintro ⟨h, hh⟩
    refine Quotient.sound ⟨(h : G)⁻¹, ?_⟩
    show ((h : G))⁻¹ • (t : S) = (s : S)
    rw [← hh, ← mul_smul, inv_mul_cancel, one_smul]

end Slice

/-! ## Fibres of an equivariant map -/

section Fibre

variable {G S I : Type*} [Group G] [MulAction G S] [MulAction G I]
variable (p : S → I) (hp : ∀ (g : G) (s : S), p (g • s) = g • p s)

include hp

/-- Every point whose image lies in the orbit of `i` is `G`-equivalent to a point of the fibre
over `i`. -/
theorem orbit_fiber_exists {i : I} (s : S) (h : p s ∈ MulAction.orbit G i) :
    ∃ (g : G) (t : S), p t = i ∧ g • t = s := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, g⁻¹ • s, ?_, ?_⟩
  · rw [hp, ← hg, ← mul_smul, inv_mul_cancel, one_smul]
  · rw [← mul_smul, mul_inv_cancel, one_smul]

/-- Two points of the fibre over `i` are `G`-equivalent exactly when they are equivalent under the
stabiliser of `i`. -/
theorem orbit_fiber_eq_iff {i : I} (s t : S) (hs : p s = i) (ht : p t = i) :
    (Quotient.mk _ s : MulAction.orbitRel.Quotient G S) = Quotient.mk _ t
      ↔ ∃ h : MulAction.stabilizer G i, (h : G) • s = t := by
  constructor
  · intro hst
    obtain ⟨g, hg⟩ := Quotient.exact hst
    have hg' : g • t = s := hg
    have hgi : g • i = i := by
      calc g • i = g • p t := by rw [ht]
        _ = p (g • t) := (hp g t).symm
        _ = p s := by rw [hg']
        _ = i := hs
    refine ⟨⟨g⁻¹, ?_⟩, ?_⟩
    · refine MulAction.mem_stabilizer_iff.2 ?_
      rw [inv_smul_eq_iff, hgi]
    · show g⁻¹ • s = t
      rw [← hg', ← mul_smul, inv_mul_cancel, one_smul]
  · rintro ⟨h, hh⟩
    refine Quotient.sound ⟨(h : G)⁻¹, ?_⟩
    show ((h : G))⁻¹ • t = s
    rw [← hh, ← mul_smul, inv_mul_cancel, one_smul]

end Fibre

end HTGeometry
