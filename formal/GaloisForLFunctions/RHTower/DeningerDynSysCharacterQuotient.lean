import GaloisForLFunctions.RHTower.DeningerDynSysWittHomCharacters
import GaloisForLFunctions.RHTower.DeningerDynSysWittRingAction

/-!
# Homomorphisms out of the invariants as characters modulo the group

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 1.5(1) and
Corollary 3.1 (`t29n`).

Let `κ` be an algebraically closed field carrying a continuous action of a profinite group `G`.
Theorem 1.4 says that restriction to the invariants `W_rat (κ)^G` is a surjection on
homomorphisms into an algebraically closed field `C`, with two homomorphisms having the same
restriction exactly when they are `G`-conjugate.  Under the isomorphism `ω : ℤ̲κ ≅ W_rat (κ)` such
homomorphisms are the characters of `κˣ`, so

`Hom (W_rat (κ)^G , C) = Hom (κˣ , Cˣ) / G` .

Combined with `W_rat (κ)^{Aut_{κ₀} κ} = W_rat (κ₀^perf)` this is Deninger's description of the
`C`-valued points over the perfect closure.
-/

namespace RHTower

open DeningerWittRing

noncomputable section

variable {κ : Type*} [Field κ] [IsAlgClosed κ] {G : Type*} [Group G] [MulSemiringAction G κ]

omit [IsAlgClosed κ] in
/-- The `G`-action on the rational Witt ring sends Teichmüller elements to Teichmüller
elements. -/
theorem deningerSMul_teichmuller (σ : G) (a : κ) :
    σ • deningerCanonicalRationalWittTeichmuller a
      = deningerCanonicalRationalWittTeichmuller (σ • a) := by
  rw [smul_def, deningerCanonicalRationalWittMap_teichmuller]
  rfl

variable {C : Type*} [Field C]

/-- The character attached to a homomorphism precomposed with the action of `σ`. -/
theorem deningerWittRingHomEquivChar_smul (ψ : DeningerCanonicalRationalWittRing κ →+* C)
    (σ : G) (a : κˣ) :
    ((deningerWittRingHomEquivChar κ C ψ (Units.map (MulSemiringAction.toRingEquiv G κ σ :
        κ →* κ) a) : Cˣ) : C)
      = ψ (σ • deningerCanonicalRationalWittTeichmuller (a : κ)) := by
  rw [deningerWittRingHomEquivChar_apply, deningerSMul_teichmuller]
  rfl

variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace κ] [DiscreteTopology κ] [ContinuousSMul G κ]
variable [TopologicalSpace (DeningerCanonicalRationalWittRing κ)]
variable [DiscreteTopology (DeningerCanonicalRationalWittRing κ)]

/-- **Deninger, Corollary 1.5(1) / Corollary 3.1 (`t29n`), surjectivity.**  Every homomorphism of
the invariants `W_rat (κ)^G` into an algebraically closed field comes from a character of `κˣ`. -/
theorem deningerCharRestrict_surjective [IsAlgClosed C]
    (φ : FixedPoints.subring (DeningerCanonicalRationalWittRing κ) G →+* C) :
    ∃ f : κˣ →* Cˣ,
      ((deningerWittRingHomEquivChar κ C).symm f).comp
          (algebraMap (FixedPoints.subring (DeningerCanonicalRationalWittRing κ) G)
            (DeningerCanonicalRationalWittRing κ)) = φ := by
  obtain ⟨ψ, hψ⟩ := restrict_surjective (A := κ) (G := G) (C := C) φ
  refine ⟨deningerWittRingHomEquivChar κ C ψ, ?_⟩
  rw [(deningerWittRingHomEquivChar κ C).symm_apply_apply]
  exact hψ

/-- **Deninger, Corollary 1.5(1) / Corollary 3.1 (`t29n`), injectivity modulo `G`.**  Two
characters of `κˣ` induce the same homomorphism of `W_rat (κ)^G` exactly when they differ by the
action of an element of `G`. -/
theorem deningerCharRestrict_eq_iff (f₁ f₂ : κˣ →* Cˣ) :
    ((deningerWittRingHomEquivChar κ C).symm f₁).comp
          (algebraMap (FixedPoints.subring (DeningerCanonicalRationalWittRing κ) G)
            (DeningerCanonicalRationalWittRing κ))
        = ((deningerWittRingHomEquivChar κ C).symm f₂).comp
          (algebraMap (FixedPoints.subring (DeningerCanonicalRationalWittRing κ) G)
            (DeningerCanonicalRationalWittRing κ))
      ↔ ∃ g : G, ∀ w : DeningerCanonicalRationalWittRing κ,
          ((deningerWittRingHomEquivChar κ C).symm f₂) w
            = ((deningerWittRingHomEquivChar κ C).symm f₁) (g • w) :=
  restrict_eq_iff _ _

end

end RHTower
