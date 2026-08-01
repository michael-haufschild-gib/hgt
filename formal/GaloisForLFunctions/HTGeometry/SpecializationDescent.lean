import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Descent along a specialisation

Two specialisations of a subalgebra that agree at one element agree at every element of the
subalgebra lying in the subfield that element generates.  Equivalently, an element at which two such
specialisations differ does not lie in that subfield.

The point is that the denominator cannot be killed.  Writing the element as a fraction in the
generator and cancelling the greatest common divisor leaves numerator and denominator coprime, so a
Bézout identity prevents both specialised values from vanishing; and the element lying in the
subalgebra forces the numerator to vanish whenever the denominator does.  Hence the denominator
survives and the value of the fraction is determined.

This is the rational descent step: a witness in one fibre, taking two values at an element while the
generating data is unchanged, proves that the element is not a rational function of that data.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IntermediateField

variable {F L M : Type*} [Field F] [Field L] [Algebra F L] [Field M]

/-- **Two specialisations agreeing on the base and at an element agree on every polynomial in
it.**  The two maps are only required to agree on the base, not to fix it: a specialisation of a
family need not restrict to the identity on its parameters. -/
theorem eq_aeval_of_eq (O : Subalgebra F L) (π₁ π₂ : O →+* M)
    (hF : ∀ a : F, π₁ (algebraMap F O a) = π₂ (algebraMap F O a)) {g : O} (hg : π₁ g = π₂ g)
    (P : F[X]) : π₁ (aeval g P) = π₂ (aeval g P) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, map_mul, map_mul, map_pow, map_pow, hF a, hg]

/-- **A specialisation is determined on a simply generated subfield.** -/
theorem eq_of_mem_adjoin_simple (O : Subalgebra F L) (π₁ π₂ : O →+* M)
    (hF : ∀ a : F, π₁ (algebraMap F O a) = π₂ (algebraMap F O a)) {g : O}
    (hg : π₁ g = π₂ g) {v : O} (hv : (v : L) ∈ F⟮(g : L)⟯) :
    π₁ v = π₂ v := by
  classical
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff F (v : L)).1 hv
  have hvL : (v : L) ≠ 0 := fun hcon => hv0 (Subtype.ext hcon)
  have hB : (aeval (g : L) s : L) ≠ 0 := by
    intro hcon
    rw [hcon, div_zero] at hrs
    exact hvL hrs
  have hs0 : s ≠ 0 := by
    intro hcon
    rw [hcon, map_zero] at hB
    exact hB rfl
  set d := gcd r s with hd
  set r' := r / d with hr'
  set s' := s / d with hs'
  have hcop : IsCoprime r' s' := isCoprime_div_gcd_div_gcd hs0
  have hd0 : d ≠ 0 := fun hcon => hs0 ((gcd_eq_zero_iff r s).1 hcon).2
  have hdr : d * r' = r := EuclideanDomain.mul_div_cancel' hd0 (gcd_dvd_left r s)
  have hds : d * s' = s := EuclideanDomain.mul_div_cancel' hd0 (gcd_dvd_right r s)
  have hsplit : (aeval (g : L) d) * (aeval (g : L) s') = aeval (g : L) s := by
    rw [← map_mul, hds]
  have hD : (aeval (g : L) d : L) ≠ 0 := by
    intro hcon
    rw [hcon, zero_mul] at hsplit
    exact hB hsplit.symm
  have hS' : (aeval (g : L) s' : L) ≠ 0 := by
    intro hcon
    rw [hcon, mul_zero] at hsplit
    exact hB hsplit.symm
  have hfrac : (v : L) = (aeval (g : L) r') / (aeval (g : L) s') := by
    rw [hrs, ← hdr, ← hds, map_mul, map_mul, mul_div_mul_left _ _ hD]
  have hmulL : (v : L) * (aeval (g : L) s') = aeval (g : L) r' := by
    rw [hfrac, div_mul_cancel₀ _ hS']
  have hcoe : ∀ P : F[X], ((aeval g P : O) : L) = aeval (g : L) P := fun P =>
    Polynomial.aeval_subalgebra_coe P O g
  have hmul : v * aeval g s' = aeval g r' := by
    refine Subtype.ext ?_
    rw [Subalgebra.coe_mul, hcoe, hcoe]
    exact hmulL
  obtain ⟨u₁, u₂, hbez⟩ := hcop
  have hbezO : aeval g u₁ * aeval g r' + aeval g u₂ * aeval g s' = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, hbez, map_one]
  have hS'ne : π₁ (aeval g s') ≠ 0 := by
    intro hcon
    have hR' : π₁ (aeval g r') = 0 := by
      rw [← hmul, map_mul, hcon, mul_zero]
    have := congrArg π₁ hbezO
    rw [map_add, map_mul, map_mul, hcon, hR', mul_zero, mul_zero, add_zero, map_one] at this
    exact zero_ne_one this
  have h1 : π₁ v * π₁ (aeval g s') = π₁ (aeval g r') := by rw [← map_mul, hmul]
  have h2 : π₂ v * π₁ (aeval g s') = π₁ (aeval g r') := by
    rw [eq_aeval_of_eq O π₁ π₂ hF hg s', ← map_mul, hmul, eq_aeval_of_eq O π₁ π₂ hF hg r']
  exact mul_right_cancel₀ hS'ne (h1.trans h2.symm)

/-- **Rational descent.**  If two specialisations agree at an element but differ at another, the
second is not a rational function of the first. -/
theorem not_mem_adjoin_simple_of_ne (O : Subalgebra F L) (π₁ π₂ : O →+* M)
    (hF : ∀ a : F, π₁ (algebraMap F O a) = π₂ (algebraMap F O a)) {g v : O}
    (hg : π₁ g = π₂ g) (hne : π₁ v ≠ π₂ v) :
    (v : L) ∉ F⟮(g : L)⟯ :=
  fun hv => hne (eq_of_mem_adjoin_simple O π₁ π₂ hF hg hv)

/-- **The same for algebra maps**, where agreement on the base is automatic. -/
theorem not_mem_adjoin_simple_of_ne_algHom [Algebra F M] (O : Subalgebra F L)
    (π₁ π₂ : O →ₐ[F] M) {g v : O} (hg : π₁ g = π₂ g) (hne : π₁ v ≠ π₂ v) :
    (v : L) ∉ F⟮(g : L)⟯ :=
  not_mem_adjoin_simple_of_ne O π₁.toRingHom π₂.toRingHom
    (fun a => by simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]) hg hne

/-! ## A worked instance -/

section Instance

open MvPolynomial

variable (K : Type*) [Field K]

/-- The polynomial algebra in two variables, inside its fraction field. -/
noncomputable abbrev twoVarAlgebra : Subalgebra K (FractionRing (MvPolynomial (Fin 2) K)) :=
  (IsScalarTower.toAlgHom K (MvPolynomial (Fin 2) K)
    (FractionRing (MvPolynomial (Fin 2) K))).range

noncomputable def twoVarEquiv :
    MvPolynomial (Fin 2) K ≃ₐ[K] twoVarAlgebra K :=
  AlgEquiv.ofInjective _ (IsFractionRing.injective (MvPolynomial (Fin 2) K)
    (FractionRing (MvPolynomial (Fin 2) K)))

/-- Evaluation of the two variables at a point, as a map on the subalgebra. -/
noncomputable def twoVarEval (pt : Fin 2 → K) : twoVarAlgebra K →ₐ[K] K :=
  (MvPolynomial.aeval pt).comp (twoVarEquiv K).symm

theorem twoVarEval_gen (pt : Fin 2 → K) (i : Fin 2) :
    twoVarEval K pt (twoVarEquiv K (MvPolynomial.X i)) = pt i := by
  simp [twoVarEval]

/-- **The hypotheses of the descent are satisfiable and its conclusion is not vacuous.**  Two
evaluations agreeing at the first variable and differing at the second prove that the second variable
is not a rational function of the first. -/
theorem X_one_not_mem_adjoin_X_zero :
    ((twoVarEquiv K (MvPolynomial.X 1) : twoVarAlgebra K) :
        FractionRing (MvPolynomial (Fin 2) K)) ∉
      K⟮((twoVarEquiv K (MvPolynomial.X 0) : twoVarAlgebra K) :
        FractionRing (MvPolynomial (Fin 2) K))⟯ := by
  refine not_mem_adjoin_simple_of_ne_algHom (twoVarAlgebra K)
    (twoVarEval K ![0, 0]) (twoVarEval K ![0, 1]) ?_ ?_
  · rw [twoVarEval_gen, twoVarEval_gen]
    rfl
  · rw [twoVarEval_gen, twoVarEval_gen]
    simp

end Instance

end GaloisForLFunctions.HTGeometry
