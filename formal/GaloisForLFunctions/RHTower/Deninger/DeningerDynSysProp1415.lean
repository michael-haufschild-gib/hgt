import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysTiltLocalHom

/-!
# Proposition 14.15: locality of the completion and of the tilt

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 14.15.

For a local ring `A` whose maximal ideal contains `p`, both the `p`-adic completion `Â` and the
tilt `A♭ = lim_{( )^p} A / p A` are local, and all three rings have the same residue field.

Locality is already available (`deningerAdicCompletion_isLocalRing`,
`deningerPreTilt_isLocalRing`).  What is added here is the identification of the residue fields.
For the completion and for the reduction mod `p` this is the general fact that a surjection of
local rings induces an isomorphism on residue fields.  For the tilt one needs the zeroth
coefficient `A♭ → A / p A` to be surjective, which holds exactly when the `p`-th power map is
surjective on `A / p A`: iterating a section of it produces a compatible system of `p`-power
roots.  Mathlib has no surjectivity criterion for `Perfection.coeff`.
-/

namespace RHTower

open IsLocalRing Perfection

universe u

variable {p : ℕ} [Fact p.Prime]

/-- **Surjective `p`-th power map lifts to the perfection.**  If every element of `R` is a `p`-th
power then the zeroth coefficient of the perfection is surjective: iterating a section of the
`p`-th power map produces a compatible system of `p`-power roots. -/
theorem deningerPerfection_coeff_zero_surjective (R : Type u) [CommRing R] [CharP R p]
    (h : ∀ a : R, ∃ b : R, b ^ p = a) :
    Function.Surjective (Perfection.coeff R p 0) := by
  choose g hg using h
  intro a
  refine ⟨⟨fun k => g^[k] a, fun k => ?_⟩, rfl⟩
  show g^[k + 1] a ^ p = g^[k] a
  rw [Function.iterate_succ_apply']
  exact hg _

/-- **Deninger, Proposition 14.15(2).**  When the `p`-th power map is surjective on the reduction
`A / p A`, the zeroth coefficient identifies the residue field of the tilt with that of the
reduction. -/
theorem deningerPreTilt_residueField_bijective {R : Type u} [CommRing R] [IsLocalRing R]
    [Fact (¬ IsUnit (p : R))] (h : ∀ a : ModP R p, ∃ b : ModP R p, b ^ p = a) :
    letI := deningerIsLocalHom_of_surjective (PreTilt.coeff (O := R) (p := p) 0)
      (deningerPerfection_coeff_zero_surjective (ModP R p) h)
    Function.Bijective (IsLocalRing.ResidueField.map (PreTilt.coeff (O := R) (p := p) 0)) :=
  deningerResidueField_bijective_of_surjective _
    (deningerPerfection_coeff_zero_surjective (ModP R p) h)

/-- **Deninger, Proposition 14.15(2).**  Reduction modulo `p` identifies the residue field of a
local ring with that of its reduction. -/
theorem deningerModP_residueField_bijective {R : Type u} [CommRing R] [IsLocalRing R]
    [Fact (¬ IsUnit (p : R))] :
    letI := deningerIsLocalHom_of_surjective
      (Ideal.Quotient.mk (Ideal.span {(p : R)}) : R →+* ModP R p) Ideal.Quotient.mk_surjective
    Function.Bijective (IsLocalRing.ResidueField.map
      (Ideal.Quotient.mk (Ideal.span {(p : R)}) : R →+* ModP R p)) :=
  deningerResidueField_bijective_of_surjective _ Ideal.Quotient.mk_surjective

/-- **Deninger, Proposition 14.15(1).**  Evaluation at level one identifies the residue field of
the adic completion with that of the quotient, hence with that of the ring. -/
theorem deningerAdicCompletion_residueField_bijective {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hfg : I.FG) (hI : I ≤ IsLocalRing.maximalIdeal R) (hIne : I ≠ ⊤) :
    letI : IsLocalRing (AdicCompletion I R) := deningerAdicCompletion_isLocalRing I hfg hI
    letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    letI := deningerIsLocalHom_of_surjective (AdicCompletion.evalOneₐ I).toRingHom
      (AdicCompletion.evalOneₐ_surjective I)
    Function.Bijective (IsLocalRing.ResidueField.map (AdicCompletion.evalOneₐ I).toRingHom) := by
  letI : IsLocalRing (AdicCompletion I R) := deningerAdicCompletion_isLocalRing I hfg hI
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  letI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact deningerResidueField_bijective_of_surjective _ (AdicCompletion.evalOneₐ_surjective I)

end RHTower
