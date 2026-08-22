import Mathlib.NumberTheory.RamificationInertia.Ramification

/-!
# The ramification index travels with an algebra isomorphism

Two sheets of a cover generate *different* subfields of the normal closure, so the places they cut
out live on different integral closures.  Comparing their ramification indices needs the invariance
of `Ideal.ramificationIdx'` under an algebra equivalence, which mathlib does not carry — it has
`Ideal.ramificationIdx_smul`, for a group acting on one fixed ring.

```text
Ideal.map_le_map_iff_ringEquiv     ideals compare the same way after transport
ramificationIdx'_algEquiv          ** e(ψ P / p) = e(P / p) **
```

The proof is immediate on the `sSup` definition: `algebraMap R S₂ = ψ ∘ algebraMap R S₁`, so the two
sets of exponents coincide.  The `Module.length` definition of `Ideal.ramificationIdx` would need a
localization comparison instead; `Ideal.ramificationIdx'_eq_ramificationIdx` converts afterwards,
under the Dedekind hypotheses it wants.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Ideals are compared the same way after transport along a ring equivalence. -/
theorem Ideal.map_le_map_iff_ringEquiv {S₁ S₂ : Type*} [CommRing S₁] [CommRing S₂]
    (ψ : S₁ ≃+* S₂) (I J : Ideal S₁) :
    I.map (ψ : S₁ →+* S₂) ≤ J.map (ψ : S₁ →+* S₂) ↔ I ≤ J := by
  constructor
  · intro h
    have h2 := Ideal.map_mono (f := (ψ.symm : S₂ →+* S₁)) h
    rwa [Ideal.map_map, Ideal.map_map, show (ψ.symm : S₂ →+* S₁).comp (ψ : S₁ →+* S₂)
      = RingHom.id S₁ from by ext x; simp, Ideal.map_id, Ideal.map_id] at h2
  · exact Ideal.map_mono

/-- **The ramification index is invariant under transport along an algebra equivalence.** -/
theorem ramificationIdx'_algEquiv {R S₁ S₂ : Type*} [CommRing R] [CommRing S₁] [CommRing S₂]
    [Algebra R S₁] [Algebra R S₂] (ψ : S₁ ≃ₐ[R] S₂) (p : Ideal R) (P : Ideal S₁) :
    Ideal.ramificationIdx' p (P.map (ψ : S₁ →+* S₂)) = Ideal.ramificationIdx' p P := by
  have hmap : Ideal.map (algebraMap R S₂) p
      = (Ideal.map (algebraMap R S₁) p).map (ψ : S₁ →+* S₂) := by
    rw [Ideal.map_map]
    congr 1
    ext x
    exact (ψ.commutes x).symm
  unfold Ideal.ramificationIdx'
  congr 1
  ext n
  simp only [Set.mem_setOf_eq, hmap, ← Ideal.map_pow]
  exact Ideal.map_le_map_iff_ringEquiv (ψ.toRingEquiv) _ _

end GaloisForLFunctions.HTGeometry
