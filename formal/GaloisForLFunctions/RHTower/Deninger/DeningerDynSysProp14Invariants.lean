import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysCor15Injective

/-!
# Proposition 1.4: the invariants of `ℤ̲κ / κ₀`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.4, the
lower isomorphism `ω : (ℤ̲κ / κ₀)^H ≅ W_rat (κ₀)`.

The comparison `W_rat (κ₀) → ℤ̲κ / κ₀` is injective, its values are `H`-invariant, and every
`H`-invariant element of `ℤ̲κ / κ₀` is a value, so it is a ring isomorphism onto the subring of
invariants.
-/

namespace RHTower

open MonoidAlgebra MulAction

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]
variable [Algebra.IsAlgebraic F E] [IsAlgClosed E] [IsAlgClosure F E]
variable [DecidableEq Eˣ] [DecidableEq (Polynomial (perfectClosure F E))]

/-- The subring of `H`-invariants of `ℤ̲κ / κ₀`. -/
def deningerInsepInvariants : Subring ↥(deningerInsepSubring F E q) where
  carrier := {x | ∀ σ : E ≃ₐ[F] E, σ • x = x}
  mul_mem' hx hy σ := by rw [smul_mul', hx σ, hy σ]
  one_mem' σ := smul_one σ
  add_mem' hx hy σ := by rw [smul_add, hx σ, hy σ]
  zero_mem' σ := smul_zero σ
  neg_mem' hx σ := by rw [smul_neg, hx σ]

omit [IsAlgClosed E] [IsAlgClosure F E] [DecidableEq Eˣ]
  [DecidableEq (Polynomial (perfectClosure F E))] in
@[simp] theorem deningerMem_insepInvariants {x : ↥(deningerInsepSubring F E q)} :
    x ∈ deningerInsepInvariants (F := F) (E := E) q ↔ ∀ σ : E ≃ₐ[F] E, σ • x = x := Iff.rfl

/-- **Deninger, Proposition 1.4.**  The image of `W_rat (κ₀)` in `ℤ̲κ / κ₀` is exactly the set of
`H`-invariants. -/
theorem deningerWittToInsep_mem_invariants_iff (x : ↥(deningerInsepSubring F E q)) :
    (∃ w : DeningerCanonicalRationalWittRing F, deningerWittToInsep q w = x)
      ↔ ∀ σ : E ≃ₐ[F] E, σ • x = x := by
  constructor
  · rintro ⟨w, rfl⟩ σ
    refine Subtype.ext ?_
    rw [deningerInsepSubring_smul_val, deningerWittToInsep_val]
    have hinjOmega : Function.Injective (deningerOmegaAddHom E) :=
      (deningerOmegaRingEquiv E).injective
    refine hinjOmega ?_
    have hsm : (σ • deningerWittToMonoidAlgebra w : MonoidAlgebra ℤ Eˣ)
        = deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E))
          (deningerWittToMonoidAlgebra w) := rfl
    have hcomm : ((σ : E →+* E).comp (algebraMap F E)) = algebraMap F E :=
      RingHom.ext fun a => σ.commutes a
    rw [hsm, ← deningerOmega_equivariant, deningerWittToMonoidAlgebra_omega,
      ← deningerCanonicalRationalWittMap_comp, hcomm]
  · intro hinv
    have hinv' : ∀ σ : E ≃ₐ[F] E,
        deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E))
          (x : MonoidAlgebra ℤ Eˣ) = (x : MonoidAlgebra ℤ Eˣ) := by
      intro σ
      have h := hinv σ
      have h' := congrArg (fun z : ↥(deningerInsepSubring F E q) =>
        (z : MonoidAlgebra ℤ Eˣ)) h
      rw [deningerInsepSubring_smul_val] at h'
      exact h'
    obtain ⟨w₀, hw₀⟩ := (deningerOmega_mem_image_iff q (x : MonoidAlgebra ℤ Eˣ)).2 ⟨hinv', x.2⟩
    refine ⟨w₀, ?_⟩
    refine Subtype.ext ?_
    rw [deningerWittToInsep_val]
    have hinjOmega : Function.Injective (deningerOmegaAddHom E) :=
      (deningerOmegaRingEquiv E).injective
    refine hinjOmega ?_
    rw [deningerWittToMonoidAlgebra_omega]
    exact hw₀

/-- The comparison `W_rat (κ₀) → (ℤ̲κ / κ₀)^H`. -/
def deningerWittInsepInvariantsHom :
    DeningerCanonicalRationalWittRing F →+* ↥(deningerInsepInvariants (F := F) (E := E) q) :=
  (deningerWittToInsep (F := F) (E := E) q).codRestrict
    (deningerInsepInvariants (F := F) (E := E) q)
    (fun w => (deningerWittToInsep_mem_invariants_iff q _).1 ⟨w, rfl⟩)

theorem deningerWittInsepInvariantsHom_val (w : DeningerCanonicalRationalWittRing F) :
    ((deningerWittInsepInvariantsHom (F := F) (E := E) q w :
        ↥(deningerInsepInvariants (F := F) (E := E) q)) : ↥(deningerInsepSubring F E q))
      = deningerWittToInsep q w := rfl

theorem deningerWittInsepInvariantsHom_bijective :
    Function.Bijective (deningerWittInsepInvariantsHom (F := F) (E := E) q) := by
  constructor
  · intro a b hab
    refine deningerWittToInsep_injective (F := F) (E := E) q ?_
    rw [← deningerWittInsepInvariantsHom_val q a, ← deningerWittInsepInvariantsHom_val q b, hab]
  · intro x
    obtain ⟨w, hw⟩ :=
      (deningerWittToInsep_mem_invariants_iff q (x : ↥(deningerInsepSubring F E q))).2 x.2
    exact ⟨w, Subtype.ext hw⟩

/-- **Deninger, Proposition 1.4.**  `ω : W_rat (κ₀) ≅ (ℤ̲κ / κ₀)^H`. -/
def deningerWittInsepInvariantsEquiv :
    DeningerCanonicalRationalWittRing F ≃+* ↥(deningerInsepInvariants (F := F) (E := E) q) :=
  RingEquiv.ofBijective (deningerWittInsepInvariantsHom (F := F) (E := E) q)
    (deningerWittInsepInvariantsHom_bijective q)

end

end RHTower
