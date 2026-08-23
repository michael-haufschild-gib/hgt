import GaloisForLFunctions.RHTower.DeningerDynSysWittFatouScheme
import GaloisForLFunctions.RHTower.DeningerDynSysWittSheafSections

/-!
# Proposition 2.1(b), (c) for the sheaf `W_rat (𝒪_X)`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 2.1(b), (c),
stated for the actual sections of the sheafification.

Part (b): over a nonempty open of an integral scheme whose ring of sections is a Fatou domain, the
canonical map `W_rat (𝒪_X (U)) → W_rat (𝒪_X) (U)` is a ring isomorphism.

Part (c): for a Fatou scheme with function field `K`, a big Witt vector over `𝒪_X (U)` is a section
of `W_rat (𝒪_X)` over `U` exactly when its image in `W (K)` is a rational Witt vector.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

variable (X : Scheme.{u})

/-- **Deninger, Proposition 2.1(b).**  On an integral scheme, over an open whose sections form a
Fatou domain, `W_rat (𝒪_X (U)) = W_rat (𝒪_X) (U)`. -/
theorem deningerRationalWittUnit_bijective [IsIntegral X] {U : X.Opens} [Nonempty U]
    (hU : DeningerFatouDomain Γ(X, U)) :
    Function.Bijective ((deningerRationalWittUnit X.sheaf).app (op U)) := by
  refine ⟨deningerRationalWittPresheaf_toSheafify_injective X.sheaf (op U), fun s => ?_⟩
  obtain ⟨v, hv⟩ := (deningerWittLocallyRational_iff_rational X hU _).1
    (deningerRationalWittSheafToBigWitt_locallyRational X.sheaf s)
  refine ⟨v, deningerRationalWittSheafToBigWitt_injective X.sheaf U ?_⟩
  rw [deningerRationalWittSheafToBigWitt_unit]
  exact hv

/-- **Deninger, Proposition 2.1(b)**, as a ring isomorphism. -/
noncomputable def deningerRationalWittUnitRingEquiv [IsIntegral X] {U : X.Opens} [Nonempty U]
    (hU : DeningerFatouDomain Γ(X, U)) :
    DeningerCanonicalRationalWittRing Γ(X, U)
      ≃+* (deningerRationalWittSheaf X.sheaf).1.obj (op U) :=
  RingEquiv.ofBijective ((deningerRationalWittUnit X.sheaf).app (op U)).hom
    (deningerRationalWittUnit_bijective X hU)

/-- **Deninger, Proposition 2.1(c).**  For a Fatou scheme with function field `K`, the sections of
`W_rat (𝒪_X)` over a nonempty open `U` are exactly the big Witt vectors over `𝒪_X (U)` that become
rational over `K`, i.e. `W_rat (𝒪_X) (U) = W_rat (K) ∩ W (𝒪_X (U))` inside `W (K)`. -/
theorem deningerRationalWittSheafSection_iff_functionField [IsIntegral X]
    (hX : DeningerFatouScheme X) {U : X.Opens} [Nonempty U]
    (w : DeningerBigWittRing Γ(X, U)) :
    (∃ s : (deningerRationalWittSheaf X.sheaf).1.obj (op U),
        (deningerRationalWittSheafToBigWitt X.sheaf).app (op U) s = w)
      ↔ ∃ v : DeningerCanonicalRationalWittRing X.functionField,
          deningerCanonicalRationalWittEmbedding v
            = deningerBigWittRingMap (algebraMap Γ(X, U) X.functionField) w := by
  rw [← deningerWittLocallyRational_iff_functionField X hX w]
  constructor
  · rintro ⟨s, rfl⟩
    exact deningerRationalWittSheafToBigWitt_locallyRational X.sheaf s
  · exact deningerRationalWittSheafToBigWitt_surjective X.sheaf

end RHTower
