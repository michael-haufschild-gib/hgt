import GaloisForLFunctions.HTGeometry.StableDifferentialCore

/-!
# Functoriality of stable differential cores

If one dynamical field maps into another and the map intertwines their endomorphisms, every
persistent observable of the factor remains persistent after pullback.  This is the formal core
of the Albanese/Manin lower bound for tails of higher-dimensional algebraic systems.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F]

/-- A commuting factor map intertwines every iterate. -/
theorem algHom_pow_intertwine
    (ι : E →ₐ[K] F) (ψ : E →ₐ[K] E) (φ : F →ₐ[K] F)
    (hcomm : ∀ x, φ (ι x) = ι (ψ x))
    (n : ℕ) (x : E) :
    (φ ^ n) (ι x) = ι ((ψ ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [AlgHom.coe_pow, Function.iterate_succ_apply']
      have ih' : (⇑φ)^[n] (ι x) = ι ((⇑ψ)^[n] x) := by
        simpa only [AlgHom.coe_pow] using ih
      rw [ih', hcomm]

/-- **Stable-core functoriality.**  Persistent observables of a factor system pull back to
persistent observables of any system mapping to that factor. -/
theorem map_stableRangeCore_le_of_intertwine
    (ι : E →ₐ[K] F) (ψ : E →ₐ[K] E) (φ : F →ₐ[K] F)
    (hcomm : ∀ x, φ (ι x) = ι (ψ x)) :
    IntermediateField.map ι (stableRangeCore ψ) ≤ stableRangeCore φ := by
  intro x hx
  rw [IntermediateField.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [mem_stableRangeCore_iff] at hy ⊢
  intro n
  obtain ⟨z, hz⟩ := hy n
  refine ⟨ι z, ?_⟩
  rw [algHom_pow_intertwine ι ψ φ hcomm n z, hz]

/-- **Commuting-symmetry invariance of the persistent core.**  Every algebraic symmetry commuting
with the constraint endomorphism preserves its stable range core exactly.  In particular, a
clock-scaling symmetry of an algebraic source constraint acts on the persistent observable
field, rather than merely on the ambient free clock. -/
theorem map_stableRangeCore_eq_of_commuting_algEquiv
    (φ : F →ₐ[K] F) (ρ : F ≃ₐ[K] F)
    (hcomm : ∀ x, φ (ρ x) = ρ (φ x)) :
    IntermediateField.map ρ.toAlgHom (stableRangeCore φ) = stableRangeCore φ := by
  apply le_antisymm
  · exact map_stableRangeCore_le_of_intertwine ρ.toAlgHom φ φ hcomm
  · intro x hx
    rw [IntermediateField.mem_map]
    refine ⟨ρ.symm x, ?_, ρ.apply_symm_apply x⟩
    have hcomm_symm : ∀ y, φ (ρ.symm y) = ρ.symm (φ y) := by
      intro y
      apply ρ.injective
      simpa using (hcomm (ρ.symm y)).symm
    have hle := map_stableRangeCore_le_of_intertwine ρ.symm.toAlgHom φ φ hcomm_symm
    apply hle
    rw [IntermediateField.mem_map]
    exact ⟨x, hx, rfl⟩

end

end GaloisForLFunctions.HTGeometry
