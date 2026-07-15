import GaloisForLFunctions.HTGeometry.StableDifferentialCore

open scoped Differential

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

/-- Membership in the persistent core is invariant under every commuting algebraic symmetry. -/
theorem stableRangeCore_symmetry_mem_iff
    (φ : F →ₐ[K] F) (ρ : F ≃ₐ[K] F)
    (hcomm : ∀ x, φ (ρ x) = ρ (φ x)) (x : F) :
    ρ x ∈ stableRangeCore φ ↔ x ∈ stableRangeCore φ := by
  constructor
  · intro hx
    have hcomm_symm : ∀ y, φ (ρ.symm y) = ρ.symm (φ y) := by
      intro y
      apply ρ.injective
      simpa using (hcomm (ρ.symm y)).symm
    have hle := map_stableRangeCore_le_of_intertwine ρ.symm.toAlgHom φ φ hcomm_symm
    have himage : ρ.symm (ρ x) ∈ stableRangeCore φ := by
      apply hle
      rw [IntermediateField.mem_map]
      exact ⟨ρ x, hx, rfl⟩
    simpa using himage
  · intro hx
    have hle := map_stableRangeCore_le_of_intertwine ρ.toAlgHom φ φ hcomm
    apply hle
    rw [IntermediateField.mem_map]
    exact ⟨x, hx, rfl⟩

/-- The restriction of a commuting symmetry to the persistent core. -/
def stableRangeCoreSymmetryAlgHom
    (φ : F →ₐ[K] F) (ρ : F ≃ₐ[K] F)
    (hcomm : ∀ x, φ (ρ x) = ρ (φ x)) :
    stableRangeCore φ →ₐ[K] stableRangeCore φ :=
  (ρ.toAlgHom.comp (stableRangeCore φ).val).codRestrict
    (stableRangeCore φ).toSubalgebra
    (fun x ↦ (stableRangeCore_symmetry_mem_iff φ ρ hcomm x).2 x.2)

/-- Restricting a commuting symmetry to the persistent core remains bijective. -/
theorem stableRangeCoreSymmetryAlgHom_bijective
    (φ : F →ₐ[K] F) (ρ : F ≃ₐ[K] F)
    (hcomm : ∀ x, φ (ρ x) = ρ (φ x)) :
    Function.Bijective (stableRangeCoreSymmetryAlgHom φ ρ hcomm) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply ρ.injective
    exact congrArg (fun z : stableRangeCore φ ↦ (z : F)) hxy
  · intro x
    have hpre : ρ.symm (x : F) ∈ stableRangeCore φ := by
      apply (stableRangeCore_symmetry_mem_iff φ ρ hcomm (ρ.symm x)).mp
      simpa only [ρ.apply_symm_apply] using x.2
    refine ⟨⟨ρ.symm x, hpre⟩, ?_⟩
    apply Subtype.ext
    exact ρ.apply_symm_apply x

/-- **Persistent-core symmetry theorem.**  Every algebraic symmetry commuting with a constraint
restricts to an algebraic symmetry of its persistent core.  Applied to clock dilation, this is the
formal action on which the scalar clock character is defined. -/
def stableRangeCoreSymmetryAlgEquiv
    (φ : F →ₐ[K] F) (ρ : F ≃ₐ[K] F)
    (hcomm : ∀ x, φ (ρ x) = ρ (φ x)) :
    stableRangeCore φ ≃ₐ[K] stableRangeCore φ :=
  AlgEquiv.ofBijective (stableRangeCoreSymmetryAlgHom φ ρ hcomm)
    (stableRangeCoreSymmetryAlgHom_bijective φ ρ hcomm)

/-- A constraint commuting with a clock symmetry preserves every clock character.  The later
projective-cocharacter classification turns this preservation law into eigen-current rigidity. -/
theorem algHom_preserves_character_of_commuting
    (φ : F →ₐ[K] F) (ρ : F ≃ₐ[K] F)
    (hcomm : ∀ x, φ (ρ x) = ρ (φ x))
    (q : F) (c : K) (hq : ρ q = algebraMap K F c * q) :
    ρ (φ q) = algebraMap K F c * φ q := by
  rw [← hcomm q, hq]
  simp

/-- **Fixed logarithmic-current theorem.**  If a differential endomorphism scales a nonzero
observable by a nonzero differential constant, its logarithmic derivative is fixed exactly.  This
is the formal kernel of the charged persistent core's static current quotient. -/
theorem logDeriv_fixed_of_eigenvector
    [Differential F] (φ : F →ₐ[K] F)
    (hderiv : ∀ x : F, φ x′ = (φ x)′)
    (q a : F) (hq0 : q ≠ 0) (ha : a ≠ 0) (ha' : a′ = 0)
    (hq : φ q = a * q) :
    φ (Differential.logDeriv q) = Differential.logDeriv q := by
  rw [Differential.logDeriv, map_div₀, hderiv, hq]
  rw [Derivation.leibniz, ha']
  simp only [smul_eq_mul, mul_zero, add_zero]
  field_simp [ha, hq0]

/-- **Unit clock-current theorem.**  Under a semilinear clock symmetry, the logarithmic derivative
of every nonzero homogeneous observable has the unit clock character, independently of the
observable's own character.  Thus higher generator charge records reconstruction holonomy rather
than a gap in the differential field's raw character spectrum. -/
theorem logDeriv_unit_character_of_semilinear
    [Differential F] (ρ : F ≃ₐ[K] F)
    (lambda q c : F) (hq0 : q ≠ 0) (hc : c ≠ 0) (hc' : c′ = 0)
    (hsemi : ∀ x : F, ρ x′ = lambda * (ρ x)′)
    (hq : ρ q = c * q) :
    ρ (Differential.logDeriv q) = lambda * Differential.logDeriv q := by
  rw [Differential.logDeriv, map_div₀, hsemi, hq]
  rw [Derivation.leibniz, hc']
  simp only [smul_eq_mul, mul_zero, add_zero]
  field_simp [hc, hq0]

/-- **Additive fixed-current theorem.**  If a differential endomorphism translates an observable
by a differential constant, its derivative is fixed exactly. -/
theorem deriv_fixed_of_translation
    [Differential F] (φ : F →ₐ[K] F)
    (hderiv : ∀ x : F, φ x′ = (φ x)′)
    (q b : F) (hb' : b′ = 0) (hq : φ q = q + b) :
    φ q′ = q′ := by
  rw [hderiv, hq, map_add, hb', add_zero]

/-- **Finite-holonomy fixed-observable theorem.**  A multiplicative eigenvector whose multiplier
has order dividing `N` yields the fixed observable `q ^ N`. -/
theorem pow_fixed_of_eigenvector
    (φ : F →ₐ[K] F) (q a : F) (N : ℕ)
    (hq : φ q = a * q) (haN : a ^ N = 1) :
    φ (q ^ N) = q ^ N := by
  rw [map_pow, hq, mul_pow, haN, one_mul]

end

end GaloisForLFunctions.HTGeometry
