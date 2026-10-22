import Mathlib.RingTheory.Perfectoid.FontaineTheta

/-!
# Fontaine's `θ` and the Witt-vector factorization of a tilted map

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 14.13
(`t1110`), equations (120n) and (121n).

Given a ring homomorphism `χ♭ : A♭ → 𝒪♭` of tilts, Deninger's map `W_p (χ)` is the composition of
the induced map of Witt vectors with Fontaine's `θ`,

`W_p (χ) = θ ∘ W_p (χ♭) : W_p (A♭) → 𝒪` ,

and the multiplicative map `χ` factors through the Teichmüller embedding: on a Teichmüller
representative the composition is the untilt of the image, `W_p (χ) ([x]) = (χ♭ x)^♯`, which is
Deninger's description `χ = ♯ ∘ χ♭`.
-/

namespace RHTower

open WittVector PreTilt

universe u

variable {A O : Type u} [CommRing A] [CommRing O] {p : ℕ} [Fact p.Prime]
variable [Fact (¬ IsUnit (p : A))] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- **Deninger, Proposition 14.13 (`t1110`), equation (121n).**  The Witt-vector map attached to a
homomorphism of tilts: `W_p (χ) = θ ∘ W_p (χ♭)`. -/
noncomputable def deningerWittTilt (χ : PreTilt A p →+* PreTilt O p) :
    WittVector p (PreTilt A p) →+* O :=
  (fontaineTheta O p).comp (WittVector.map χ)

/-- **Deninger, Proposition 14.13 (`t1110`), equation (120n).**  On a Teichmüller representative
the Witt-vector map is the untilt of the image, so the multiplicative map `χ` factors as
`A♭ ≅ lim_{()^p} A → W_p (A♭) → 𝒪`. -/
theorem deningerWittTilt_teichmuller (χ : PreTilt A p →+* PreTilt O p) (x : PreTilt A p) :
    deningerWittTilt χ (teichmuller p x) = (χ x).untilt := by
  show fontaineTheta O p (WittVector.map χ (teichmuller p x)) = (χ x).untilt
  rw [WittVector.map_teichmuller, fontaineTheta_teichmuller]

end RHTower
