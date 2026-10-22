import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysProp14Invariants

/-!
# Corollary 3.1: the `C`-valued points over an algebraically closed field

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 3.1, the
bijection (24)

`Hom (W_rat (κ (x₀)) , C) ≅ Hom (κ (x)ˣ , Cˣ) / G_x` .

A character of `κˣ` induces a homomorphism of `W_rat (κ₀)` by composing with `ω` and the
comparison `W_rat (κ₀) → ℤ̲κ`; every homomorphism arises this way by Corollary 1.6, and two
characters induce the same homomorphism exactly when they differ by an element of the Galois
group, again by Corollary 1.6.
-/

namespace RHTower

open MonoidAlgebra

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]
variable [Algebra.IsAlgebraic F E] [IsAlgClosed E] [IsAlgClosure F E]
variable [DecidableEq Eˣ] [DecidableEq (Polynomial (perfectClosure F E))]
variable {C : Type*} [Field C]

omit [Algebra.IsAlgebraic F E] [IsAlgClosure F E] [DecidableEq Eˣ]
  [DecidableEq (Polynomial (perfectClosure F E))] in
/-- The comparison `W_rat (κ₀) → ℤ̲κ` has `H`-invariant image. -/
theorem deningerWittToMonoidAlgebra_invariant (σ : E ≃ₐ[F] E)
    (w : DeningerCanonicalRationalWittRing F) :
    deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E))
        (deningerWittToMonoidAlgebra (F := F) (E := E) w)
      = deningerWittToMonoidAlgebra w := by
  have hinjOmega : Function.Injective (deningerOmegaAddHom E) :=
    (deningerOmegaRingEquiv E).injective
  refine hinjOmega ?_
  have hcomm : ((σ : E →+* E).comp (algebraMap F E)) = algebraMap F E :=
    RingHom.ext fun a => σ.commutes a
  rw [← deningerOmega_equivariant, deningerWittToMonoidAlgebra_omega,
    ← deningerCanonicalRationalWittMap_comp, hcomm]

omit [IsAlgClosed E] [DecidableEq Eˣ] in
/-- Relabelling the atoms of `ℤ̲κ` is the same as precomposing the character with the
relabelling. -/
theorem deningerCharToMonoidAlgebra_comp (f : Eˣ →* Cˣ) (φ : Eˣ →* Eˣ) :
    deningerCharToMonoidAlgebra (f.comp φ)
      = (deningerCharToMonoidAlgebra f).comp (deningerMonoidAlgebraMap φ) := by
  refine MonoidAlgebra.ringHom_ext ?_ ?_ <;> intro a <;>
    simp [deningerCharToMonoidAlgebra_single, deningerMonoidAlgebraMap_single]

/-- **Deninger, Corollary 3.1 (24).**  The homomorphism `W_rat (κ₀) → C` induced by a character of
`κˣ`. -/
def deningerCharToWittHom (f : Eˣ →* Cˣ) : DeningerCanonicalRationalWittRing F →+* C :=
  (deningerCharToMonoidAlgebra f).comp (deningerWittToMonoidAlgebra (F := F) (E := E))

omit [Algebra.IsAlgebraic F E] [IsAlgClosure F E] [DecidableEq Eˣ]
  [DecidableEq (Polynomial (perfectClosure F E))] in
theorem deningerCharToWittHom_apply (f : Eˣ →* Cˣ)
    (w : DeningerCanonicalRationalWittRing F) :
    deningerCharToWittHom (F := F) (E := E) f w
      = deningerCharToMonoidAlgebra f (deningerWittToMonoidAlgebra w) := rfl

omit [Algebra.IsAlgebraic F E] [IsAlgClosure F E] [DecidableEq Eˣ]
  [DecidableEq (Polynomial (perfectClosure F E))] in
/-- **Deninger, Corollary 3.1 (24).**  Relabelling a character by an element of the Galois group
does not change the induced homomorphism of `W_rat (κ₀)`. -/
theorem deningerCharToWittHom_comp_map (f : Eˣ →* Cˣ) (σ : E ≃ₐ[F] E) :
    deningerCharToWittHom (F := F) (E := E) (f.comp (Units.map ((σ : E →+* E) : E →* E)))
      = deningerCharToWittHom (F := F) (E := E) f := by
  refine RingHom.ext fun w => ?_
  rw [deningerCharToWittHom_apply, deningerCharToMonoidAlgebra_comp]
  show deningerCharToMonoidAlgebra f
      (deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E))
        (deningerWittToMonoidAlgebra w)) = _
  rw [deningerWittToMonoidAlgebra_invariant σ w, deningerCharToWittHom_apply]

variable [IsAlgClosed C]

include q in
/-- **Deninger, Corollary 3.1 (24), surjectivity.**  Every homomorphism `W_rat (κ₀) → C` into an
algebraically closed field comes from a character of `κˣ`. -/
theorem deningerCharToWittHom_surjective (φ : DeningerCanonicalRationalWittRing F →+* C) :
    ∃ f : Eˣ →* Cˣ, deningerCharToWittHom (F := F) (E := E) f = φ :=
  deningerCor15_surjective q φ

include q in
/-- **Deninger, Corollary 3.1 (24).**  Two characters of `κˣ` induce the same homomorphism of
`W_rat (κ₀)` exactly when they differ by an element of the Galois group. -/
theorem deningerCharToWittHom_eq_iff (f₁ f₂ : Eˣ →* Cˣ) :
    deningerCharToWittHom (F := F) (E := E) f₁ = deningerCharToWittHom (F := F) (E := E) f₂
      ↔ ∃ σ : E ≃ₐ[F] E, f₂ = f₁.comp (Units.map ((σ : E →+* E) : E →* E)) := by
  constructor
  · intro h
    set ψ₁ : ↥(deningerInsepSubring F E q) →+* C :=
      (deningerCharToMonoidAlgebra f₁).comp
        (algebraMap ↥(deningerInsepSubring F E q) (MonoidAlgebra ℤ Eˣ)) with hψ₁
    set ψ₂ : ↥(deningerInsepSubring F E q) →+* C :=
      (deningerCharToMonoidAlgebra f₂).comp
        (algebraMap ↥(deningerInsepSubring F E q) (MonoidAlgebra ℤ Eˣ)) with hψ₂
    have hres : ∀ w : DeningerCanonicalRationalWittRing F,
        ψ₁ (deningerWittToInsep q w) = ψ₂ (deningerWittToInsep q w) := by
      intro w
      have h1 : ψ₁ (deningerWittToInsep q w)
          = deningerCharToWittHom (F := F) (E := E) f₁ w := by
        rw [hψ₁]
        show deningerCharToMonoidAlgebra f₁
          ((deningerWittToInsep (F := F) (E := E) q w : ↥(deningerInsepSubring F E q)) :
            MonoidAlgebra ℤ Eˣ) = _
        rw [deningerWittToInsep_val, deningerCharToWittHom_apply]
      have h2 : ψ₂ (deningerWittToInsep q w)
          = deningerCharToWittHom (F := F) (E := E) f₂ w := by
        rw [hψ₂]
        show deningerCharToMonoidAlgebra f₂
          ((deningerWittToInsep (F := F) (E := E) q w : ↥(deningerInsepSubring F E q)) :
            MonoidAlgebra ℤ Eˣ) = _
        rw [deningerWittToInsep_val, deningerCharToWittHom_apply]
      rw [h1, h2, h]
    obtain ⟨σ, hσ⟩ := deningerCor15_injective q ψ₁ ψ₂ hres
    refine ⟨σ, ?_⟩
    have hchi : deningerCharToMonoidAlgebra f₂
        = deningerCharToMonoidAlgebra (f₁.comp (Units.map ((σ : E →+* E) : E →* E))) := by
      refine deningerInsepSubring_restrict_injective (F := F) (E := E) (q := q) _ _ ?_
      intro ξ hξ
      have hx := hσ ⟨ξ, hξ⟩
      have hleft : ψ₂ ⟨ξ, hξ⟩ = deningerCharToMonoidAlgebra f₂ ξ := rfl
      have hright : ψ₁ (σ • (⟨ξ, hξ⟩ : ↥(deningerInsepSubring F E q)))
          = deningerCharToMonoidAlgebra f₁
            (deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E)) ξ) := by
        rw [hψ₁]
        show deningerCharToMonoidAlgebra f₁
          ((σ • (⟨ξ, hξ⟩ : ↥(deningerInsepSubring F E q)) : ↥(deningerInsepSubring F E q)) :
            MonoidAlgebra ℤ Eˣ) = _
        rw [deningerInsepSubring_smul_val]
        rfl
      rw [hleft] at hx
      rw [hright] at hx
      rw [hx, deningerCharToMonoidAlgebra_comp]
      rfl
    exact (deningerMonoidAlgebraRingHomEquiv Eˣ C).symm.injective hchi
  · rintro ⟨σ, rfl⟩
    exact (deningerCharToWittHom_comp_map (F := F) (E := E) f₁ σ).symm

end

end RHTower
