import GaloisForLFunctions.HTGeometry.LogarithmicDerivativeObstruction
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# Realizing the jet polynomial ring inside a differential field

A differentially independent family gives an injective differential homomorphism from the jet
polynomial ring into a differential field.  It extends to the field of differential rational
functions, whose image is a differential subfield in which no element has a logarithmic derivative
of degree one — this is the hypothesis consumed by the Artin shortening.

Everything here is about an abstract differential field; the analytic realization is separate.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {ι : Type*} {L : Type*} [Field L] [Differential L]
  {f : ι → MvPolynomial ι ℂ} {g : MvPolynomial ι ℂ →+* L}

/-- The extension of a jet realization to the field of differential rational functions. -/
def jetFieldLift (hg : Function.Injective g) : FractionRing (MvPolynomial ι ℂ) →+* L :=
  IsFractionRing.lift hg

omit [Differential L] in
theorem jetFieldLift_algebraMap (hg : Function.Injective g) (p : MvPolynomial ι ℂ) :
    jetFieldLift hg (algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) p) = g p :=
  IsFractionRing.lift_algebraMap hg p

omit [Differential L] in
theorem jetFieldLift_injective (hg : Function.Injective g) :
    Function.Injective (jetFieldLift hg) :=
  (jetFieldLift hg).injective

/-- **The extension is differential.**  A realization commuting with the jet derivation extends to
one commuting with the derivation of differential rational functions, by the quotient rule. -/
theorem jetFieldLift_map_deriv (hg : Function.Injective g)
    (hd : ∀ p, g (jetLikeDerivation f p) = (g p)′) (x : FractionRing (MvPolynomial ι ℂ)) :
    jetFieldLift hg (jetFractionDerivation f x) = (jetFieldLift hg x)′ := by
  obtain ⟨a, b, hb, rfl⟩ :=
    IsFractionRing.div_surjective (A := MvPolynomial ι ℂ)
      (K := FractionRing (MvPolynomial ι ℂ)) x
  have hmap (p : MvPolynomial ι ℂ) :
      jetFieldLift hg (algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) p) = g p :=
    jetFieldLift_algebraMap hg p
  have hderiv (p : MvPolynomial ι ℂ) :
      jetFieldLift hg (jetFractionDerivation f
          (algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) p))
        = (g p)′ := by
    rw [jetFractionDerivation_algebraMap, hmap, hd]
  rw [Derivation.leibniz_div]
  simp only [map_sub, map_mul, map_pow, map_inv₀, map_div₀, smul_eq_mul]
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul]
  rw [hmap, hmap, hderiv, hderiv]

/-- The differential subfield of differential rational functions of the realized family. -/
def jetSubfield (hg : Function.Injective g) : Subfield L :=
  (jetFieldLift hg).fieldRange

omit [Differential L] in
theorem mem_jetSubfield (hg : Function.Injective g) (p : MvPolynomial ι ℂ) :
    g p ∈ jetSubfield hg :=
  ⟨algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) p, jetFieldLift_algebraMap hg p⟩

/-- The subfield of differential rational functions is closed under differentiation. -/
theorem jetSubfield_deriv_mem (hg : Function.Injective g)
    (hd : ∀ p, g (jetLikeDerivation f p) = (g p)′) :
    ∀ c ∈ jetSubfield hg, c′ ∈ jetSubfield hg := by
  rintro c ⟨x, rfl⟩
  exact ⟨jetFractionDerivation f x, jetFieldLift_map_deriv hg hd x⟩

/-- **No differential rational function of the family has a logarithmic derivative of degree one.**
This is the obstruction consumed by the Artin shortening, transported to the realized subfield. -/
theorem jetSubfield_logDeriv_impossible (hf : ∀ i, (f i).totalDegree ≤ 1)
    (hg : Function.Injective g) (hd : ∀ p, g (jetLikeDerivation f p) = (g p)′)
    {T : MvPolynomial ι ℂ} (hT : T ≠ 0) (hTdeg : T.totalDegree = 1)
    {c : L} (hcmem : c ∈ jetSubfield hg) (hc : c ≠ 0) :
    c′ ≠ g T * c := by
  obtain ⟨x, rfl⟩ := hcmem
  intro heq
  have hx : x ≠ 0 := by
    intro hcon
    rw [hcon, map_zero] at hc
    exact hc rfl
  refine jetFraction_logDeriv_impossible (f := f) hf hT hTdeg hx ?_
  refine jetFieldLift_injective hg ?_
  rw [jetFieldLift_map_deriv hg hd, map_mul, jetFieldLift_algebraMap]
  exact heq

end

end GaloisForLFunctions.HTGeometry
