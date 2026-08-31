import GaloisForLFunctions.HTGeometry.CohenMacaulayLifting

/-!
# Cohen–Macaulayness transports along a ring isomorphism

A ring isomorphism carries a ring-regular sequence to a ring-regular sequence — regularity is
membership in the nonzerodivisors of a quotient, and the quotients correspond under
`Ideal.quotientEquiv` — and it preserves the Krull dimension.  So it preserves the Cohen–Macaulay
property.

```text
isRegularOn_ringEquiv
isRingRegularSeq_map_ringEquiv
IsCohenMacaulayRing.of_ringEquiv     ** the transport **
```

This is what lets a Cohen–Macaulay computation performed on a convenient presentation — the
monomial subalgebra `rationalNormalCone`, say — be read back on the quotient presentation the
Hankel card uses.
-/

namespace GaloisForLFunctions.HTGeometry

universe u
variable {A B : Type u} [CommRing A] [CommRing B]

theorem isRegularOn_ringEquiv (e : A ≃+* B) {I : Ideal A} {x : A} (h : IsRegularOn I x) :
    IsRegularOn (I.map (e : A →+* B)) (e x) := by
  rw [IsRegularOn] at h ⊢
  have hmap := mem_nonZeroDivisors_of_ringEquiv
    (Ideal.quotientEquiv I (I.map (e : A →+* B)) e rfl) h
  rwa [Ideal.quotientEquiv_mk] at hmap

theorem isRingRegularSeq_map_ringEquiv (e : A ≃+* B) {rs : List A} (h : IsRingRegularSeq rs) :
    IsRingRegularSeq (rs.map (e : A →+* B)) := by
  constructor
  · intro i hi
    have hlen : rs.length = (rs.map (e : A →+* B)).length := by simp
    have hi' : i < rs.length := by rwa [hlen]
    have hreg := h.regular i hi'
    have htake : (rs.map (e : A →+* B)).take i = (rs.take i).map (e : A →+* B) := by
      simp [List.map_take]
    have hget : (rs.map (e : A →+* B))[i] = e rs[i] := by
      simp
    rw [htake, hget, ofList_map]
    exact isRegularOn_ringEquiv e hreg
  · intro htop
    apply h.proper
    have hmap : Ideal.ofList (rs.map (e : A →+* B)) = (Ideal.ofList rs).map (e : A →+* B) :=
      ofList_map _ _
    rw [hmap] at htop
    have := congrArg (Ideal.map (e.symm : B →+* A)) htop
    rw [Ideal.map_map] at this
    have hid : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by
      ext a; simp
    rw [hid, Ideal.map_id, Ideal.map_top] at this
    exact this

/-- **Cohen–Macaulayness transports along a ring isomorphism.** -/
theorem IsCohenMacaulayRing.of_ringEquiv (e : A ≃+* B) (h : IsCohenMacaulayRing A) :
    IsCohenMacaulayRing B := by
  obtain ⟨rs, hrs, hlen⟩ := h
  refine ⟨rs.map (e : A →+* B), isRingRegularSeq_map_ringEquiv e hrs, ?_⟩
  rw [List.length_map, hlen, ringKrullDim_eq_of_ringEquiv e]

end GaloisForLFunctions.HTGeometry
