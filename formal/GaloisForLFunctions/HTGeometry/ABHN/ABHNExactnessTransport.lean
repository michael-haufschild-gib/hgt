import GaloisForLFunctions.HTGeometry.ABHN.Specification

/-!
# Transport of the ABHN exactness contract

An identification of global and local terms which commutes with localization and with the local
invariant transports the full ABHN exactness contract.  This is the reusable bookkeeping layer
for future local invariant isomorphisms and alternative presentations of local Brauer data.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-- The exactness clause of an ABHN sequence is the local-global criterion for a zero invariant. -/
theorem ABHNExactness.localInvariant_eq_zero_iff_exists_global
    {G L : Type*} (globalToLocal : G → L) (localInvariant : L → RatModInt)
    (h : ABHNExactness G L globalToLocal localInvariant) (y : L) :
    localInvariant y = 0 ↔ ∃ x, globalToLocal x = y :=
  h.exact_globalToLocal_localInvariant y

/-- The injectivity clause of an ABHN sequence detects equality of global classes locally. -/
theorem ABHNExactness.globalToLocal_eq_iff
    {G L : Type*} (globalToLocal : G → L) (localInvariant : L → RatModInt)
    (h : ABHNExactness G L globalToLocal localInvariant) (x y : G) :
    globalToLocal x = globalToLocal y ↔ x = y :=
  ⟨fun hxy => h.globalToLocal_injective hxy, fun hxy => congrArg globalToLocal hxy⟩

/-- Transport ABHN exactness along commuting equivalences of its global and local terms. -/
theorem ABHNExactness.transport
    {G L G' L' : Type*} (globalToLocal : G → L) (localInvariant : L → RatModInt)
    (globalToLocal' : G' → L') (localInvariant' : L' → RatModInt)
    (globalEquiv : G ≃ G') (localEquiv : L ≃ L')
    (hglobal : ∀ x, localEquiv (globalToLocal x) = globalToLocal' (globalEquiv x))
    (hlocal : ∀ y, localInvariant' (localEquiv y) = localInvariant y)
    (h : ABHNExactness G L globalToLocal localInvariant) :
    ABHNExactness G' L' globalToLocal' localInvariant' := by
  refine
    { globalToLocal_injective := ?_
      exact_globalToLocal_localInvariant := ?_
      localInvariant_surjective := ?_ }
  · intro x y hxy
    apply globalEquiv.symm.injective
    apply h.globalToLocal_injective
    apply localEquiv.injective
    rw [hglobal, hglobal]
    simpa using hxy
  · intro y'
    constructor
    · intro hy'
      have hy : localInvariant (localEquiv.symm y') = 0 := by
        rw [← hlocal, localEquiv.apply_symm_apply]
        exact hy'
      obtain ⟨x, hx⟩ := h.exact_globalToLocal_localInvariant _ |>.mp hy
      refine ⟨globalEquiv x, ?_⟩
      rw [← hglobal, hx, localEquiv.apply_symm_apply]
    · rintro ⟨x', hx'⟩
      let x := globalEquiv.symm x'
      have hx : globalToLocal x = localEquiv.symm y' := by
        apply localEquiv.injective
        rw [hglobal]
        simpa [x] using hx'
      have hy : localInvariant (localEquiv.symm y') = 0 :=
        h.exact_globalToLocal_localInvariant _ |>.mpr ⟨x, hx⟩
      calc
        localInvariant' y' = localInvariant' (localEquiv (localEquiv.symm y')) := by
          rw [localEquiv.apply_symm_apply]
        _ = localInvariant (localEquiv.symm y') := hlocal _
        _ = 0 := hy
  · intro q
    obtain ⟨y, hy⟩ := h.localInvariant_surjective q
    exact ⟨localEquiv y, by rw [hlocal, hy]⟩

end GaloisForLFunctions.HTGeometry.ABHN
