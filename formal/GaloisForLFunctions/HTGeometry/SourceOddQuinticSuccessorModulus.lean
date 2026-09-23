import GaloisForLFunctions.HTGeometry.PrimitiveRecordPolaritySelector

/-!
# Source-odd quintic successor modulus

For a labeled two-channel source polarity, an odd symmetric quintic has the coefficient pattern

`a x⁴y + b x²y³ + c y⁵`.

A source-preserving diagonal reparametrization and projective top-record rescaling act by

`(a,b,c) ↦ (λ a u⁴v, λ b u²v³, λ c v⁵)`.

This file proves, without division, that the cross product relation

`b'² a c = b² a' c'`

is invariant. Consequently normalized triples `(1,b,1)` with distinct squared middle
coefficients cannot be source-projectively equivalent.

This is unconditional commutative-ring algebra. It does not prove that physical successor laws
are quintic tensors, that distinct coefficient orbits interfere, or any statement about quantum
theory, time, spacetime, gravity, or gauge forces.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Coefficients of the source-odd binary quintic `a x⁴y + b x²y³ + c y⁵`. -/
structure SourceOddQuinticCoefficients (K : Type*) where
  lead : K
  middle : K
  tail : K

variable {K : Type*} [CommRing K]

/-- Diagonal source reparametrization `(x,y) ↦ (u x,v y)` together with projective
top-record scaling by `lam`. -/
def sourceOddQuinticReparam
    (lam u v : K)
    (q : SourceOddQuinticCoefficients K) :
    SourceOddQuinticCoefficients K where
  lead := lam * q.lead * u ^ (4 : ℕ) * v
  middle := lam * q.middle * u ^ (2 : ℕ) * v ^ (3 : ℕ)
  tail := lam * q.tail * v ^ (5 : ℕ)

/-- The division-free quintic cross product is invariant under every diagonal projective source
reparametrization. This is the polynomial form of preservation of `middle² / (lead * tail)`. -/
theorem sourceOddQuinticReparam_cross_invariant
    (lam u v : K)
    (q : SourceOddQuinticCoefficients K) :
    (sourceOddQuinticReparam lam u v q).middle ^ (2 : ℕ) * q.lead * q.tail =
      q.middle ^ (2 : ℕ) *
        (sourceOddQuinticReparam lam u v q).lead *
        (sourceOddQuinticReparam lam u v q).tail := by
  simp only [sourceOddQuinticReparam]
  ring

/-- Projective source equivalence of odd quintic coefficient triples. The nonzero hypotheses
encode invertible source-coordinate and top-record changes. -/
def SourceProjectivelyEquivalentOddQuintic
    (q r : SourceOddQuinticCoefficients K) : Prop :=
  ∃ lam u v : K,
    lam ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      r = sourceOddQuinticReparam lam u v q

/-- Source-projectively equivalent odd quintics obey the invariant cross-product relation. -/
theorem sourceProjectivelyEquivalentOddQuintic_cross_invariant
    {q r : SourceOddQuinticCoefficients K}
    (h : SourceProjectivelyEquivalentOddQuintic q r) :
    r.middle ^ (2 : ℕ) * q.lead * q.tail =
      q.middle ^ (2 : ℕ) * r.lead * r.tail := by
  rcases h with ⟨lam, u, v, _hlam, _hu, _hv, rfl⟩
  exact sourceOddQuinticReparam_cross_invariant lam u v q

/-- Normalized fully supported odd quintic coefficient triple `(1,b,1)`. -/
def normalizedSourceOddQuintic (b : K) : SourceOddQuinticCoefficients K where
  lead := 1
  middle := b
  tail := 1

/-- Equivalent normalized odd quintics have equal squared middle coefficients. -/
theorem normalizedSourceOddQuintic_sq_eq_of_projectivelyEquivalent
    {b d : K}
    (h : SourceProjectivelyEquivalentOddQuintic
      (normalizedSourceOddQuintic b)
      (normalizedSourceOddQuintic d)) :
    d ^ (2 : ℕ) = b ^ (2 : ℕ) := by
  have hinvariant :=
    sourceProjectivelyEquivalentOddQuintic_cross_invariant h
  simpa [normalizedSourceOddQuintic] using hinvariant

/-- Distinct squared middle coefficients give inequivalent normalized odd quintic successor
orbits. Thus source polarity and oddness do not select one quintic projective orbit. -/
theorem normalizedSourceOddQuintic_not_projectivelyEquivalent_of_sq_ne
    {b d : K}
    (hbd : d ^ (2 : ℕ) ≠ b ^ (2 : ℕ)) :
    ¬ SourceProjectivelyEquivalentOddQuintic
      (normalizedSourceOddQuintic b)
      (normalizedSourceOddQuintic d) := by
  intro h
  exact hbd (normalizedSourceOddQuintic_sq_eq_of_projectivelyEquivalent h)

end GaloisForLFunctions.HTGeometry
