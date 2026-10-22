import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Supplement 13.7: the residue datum of an `o`-valued point is determined

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Supplement 13.7.

A point of `X(o)` is a triple `(x , y₀ , P)`; the diagram (148) attaches to it a point
`y ∈ π⁻¹(y₀)` and a multiplicative map `P̃_y : κ(y) → k`.  Both are determined by the triple.

The prime cutting out `y` inside `𝒪_{X,y₀}` is the preimage of the maximal ideal of `o` under
`P_{y₀}` — this is equation (149) — because the residue map kills exactly the maximal ideal and
`P̃_y` vanishes only at zero.  The map `P̃_y` itself is determined because every element of
`κ (y) = Frac (𝒪_{X,y₀} / q)` is a quotient of two elements coming from `𝒪_{X,y₀}`, and `P̃_y` is
multiplicative and nonzero on the denominator.  Finally the prime cutting out `x` is contained in
the one cutting out `y`, since zero lies in the maximal ideal; this is `y ∈ closure {x}`.
-/

namespace RHTower

universe u

variable {R : Type u} [CommRing R] {O : Type u} [CommRing O] [IsLocalRing O]
variable (q : Ideal R) [q.IsPrime]
variable (κ : Type u) [Field κ] [Algebra (R ⧸ q) κ] [IsFractionRing (R ⧸ q) κ]

/-- The composite `R → R ⧸ q → κ`. -/
noncomputable def deningerQuotientToFraction : R →+* κ :=
  (algebraMap (R ⧸ q) κ).comp (Ideal.Quotient.mk q)

omit [q.IsPrime] in
theorem deningerQuotientToFraction_eq_zero_iff (f : R) :
    deningerQuotientToFraction q κ f = 0 ↔ f ∈ q := by
  show algebraMap (R ⧸ q) κ (Ideal.Quotient.mk q f) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ q) κ), Ideal.Quotient.eq_zero_iff_mem]

variable {q κ}

omit [q.IsPrime] in
/-- **Deninger, Supplement 13.7, equation (149).**  The prime cutting out `y` is the preimage of
the maximal ideal under the local multiplicative map. -/
theorem deningerSupplement137_mem_iff (P₀ : R →*₀ O)
    (Pt : κ →*₀ IsLocalRing.ResidueField O)
    (hcomm : ∀ f : R, Pt (deningerQuotientToFraction q κ f) = IsLocalRing.residue O (P₀ f))
    (hPt : ∀ z : κ, Pt z = 0 → z = 0) (f : R) :
    f ∈ q ↔ P₀ f ∈ IsLocalRing.maximalIdeal O := by
  rw [← deningerQuotientToFraction_eq_zero_iff q κ f]
  constructor
  · intro h
    have hz : IsLocalRing.residue O (P₀ f) = 0 := by rw [← hcomm f, h, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  · intro h
    have hz : IsLocalRing.residue O (P₀ f) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [← hcomm f] at hz
    exact hPt _ hz

/-- **Deninger, Supplement 13.7.**  The multiplicative map on `κ (y)` is determined by its
restriction along `R → κ (y)`: every element of `κ (y)` is a quotient of two images. -/
theorem deningerSupplement137_unique (φ : R → IsLocalRing.ResidueField O)
    (Pt₁ Pt₂ : κ →*₀ IsLocalRing.ResidueField O)
    (h₁ : ∀ f : R, Pt₁ (deningerQuotientToFraction q κ f) = φ f)
    (h₂ : ∀ f : R, Pt₂ (deningerQuotientToFraction q κ f) = φ f)
    (hPt₁ : ∀ z : κ, Pt₁ z = 0 → z = 0) :
    Pt₁ = Pt₂ := by
  refine DFunLike.ext _ _ fun z => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ q) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hbne : deningerQuotientToFraction q κ b ≠ 0 := by
    intro h
    rw [deningerQuotientToFraction_eq_zero_iff] at h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hb) (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hval : ∀ Pt : κ →*₀ IsLocalRing.ResidueField O,
      (∀ f : R, Pt (deningerQuotientToFraction q κ f) = φ f) →
      Pt (deningerQuotientToFraction q κ b) ≠ 0 →
      Pt (algebraMap (R ⧸ q) κ (Ideal.Quotient.mk q a)
          / algebraMap (R ⧸ q) κ (Ideal.Quotient.mk q b)) = φ a / φ b := by
    intro Pt hPt hne
    rw [map_div₀]
    show Pt (deningerQuotientToFraction q κ a) / Pt (deningerQuotientToFraction q κ b) = _
    rw [hPt a, hPt b]
  have hne₁ : Pt₁ (deningerQuotientToFraction q κ b) ≠ 0 := fun h => hbne (hPt₁ _ h)
  have hne₂ : Pt₂ (deningerQuotientToFraction q κ b) ≠ 0 := by
    rw [h₂ b, ← h₁ b]
    exact hne₁
  rw [hval Pt₁ h₁ hne₁, hval Pt₂ h₂ hne₂]

omit [q.IsPrime] in
/-- **Deninger, Supplement 13.7.**  The prime cutting out `x` is contained in the prime cutting
out `y`; that is, `y` lies in the closure of `x`. -/
theorem deningerSupplement137_le (P₀ : R →*₀ O) (p : Ideal R)
    (hp : ∀ f : R, P₀ f = 0 ↔ f ∈ p) (hq : ∀ f : R, P₀ f ∈ IsLocalRing.maximalIdeal O ↔ f ∈ q) :
    p ≤ q := by
  intro f hf
  refine (hq f).1 ?_
  rw [(hp f).2 hf]
  exact Ideal.zero_mem _

end RHTower
