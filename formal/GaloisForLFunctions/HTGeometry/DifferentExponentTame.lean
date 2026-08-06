import GaloisForLFunctions.HTGeometry.DifferentIdealMonogenic
import GaloisForLFunctions.HTGeometry.MinpolyDegreeUniformizer
import GaloisForLFunctions.HTGeometry.TameDifferentMonogenic

/-!
# The tame different exponent

For a finite extension of discrete valuation rings with trivial residue extension and ramification
index invertible at the place, the different is the `(e-1)`-st power of the maximal ideal.

Every input is now proved rather than assumed: the uniformizer generates the extension, so the
conductor is trivial and the generation hypothesis holds over the fraction field; its minimal
polynomial has degree the ramification index; and the tame computation gives the valuation of the
derivative there.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IsDiscreteValuationRing

section Span

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

/-- Generators of the same principal ideal have the same valuation. -/
theorem addVal_eq_of_span_singleton_eq {y z : B} (h : Ideal.span {y} = Ideal.span {z}) :
    addVal B y = addVal B z := by
  have h1 : z ∣ y := Ideal.span_singleton_le_span_singleton.mp (le_of_eq h)
  have h2 : y ∣ z := Ideal.span_singleton_le_span_singleton.mp (le_of_eq h.symm)
  exact le_antisymm (addVal_le_iff_dvd.mpr h2) (addVal_le_iff_dvd.mpr h1)

end Span

variable (A K : Type*) {L : Type*} {B : Type*}
variable [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [IsIntegrallyClosed A] [IsIntegralClosure B A L] [IsFractionRing B L]
variable [IsDedekindDomain B] [Module.IsTorsionFree A B]
variable [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Module.Finite A B]

/-- **The tame different exponent.**  The different of a finite extension of discrete valuation
rings with trivial residue extension and invertible ramification index is the `(e-1)`-st power of
the maximal ideal. -/
theorem differentIdeal_eq_span_pow {πA : A} (hπA : Irreducible πA) (e : ℕ) (he : 0 < e)
    (hram : addVal B (algebraMap A B πA) = (e : ℕ∞)) {x : B} (hx : addVal B x = 1)
    (hres : ∀ b : B, ∃ a : A, addVal B (b - algebraMap A B a) ≠ 0)
    (hdvd : algebraMap A B πA ∣ x ^ e) (htame : addVal B ((e : ℕ) : B) = 0)
    {g : A[X]} (hmonic : g.Monic) (hdeg : g.natDegree = e) (hroot : aeval x g = 0)
    (halg : IsAlgebraic K (algebraMap B L x)) :
    differentIdeal A B = Ideal.span {x ^ (e - 1)} := by
  have hadjA : Algebra.adjoin A ({x} : Set B) = ⊤ := adjoin_singleton_eq_top hπA hx e hres hdvd
  have hcond : conductor A x = ⊤ := conductor_eq_top_of_adjoin_eq_top hadjA
  have hadjK : Algebra.adjoin K ({algebraMap B L x} : Set L) = ⊤ :=
    adjoin_fraction_eq_top (A := A) halg hadjA
  have hint : IsIntegral A x := ⟨g, hmonic, hroot⟩
  have hdegmin : (minpoly A x).natDegree = e :=
    natDegree_minpoly_eq_ramificationIndex hπA e hram hx hmonic hdeg hroot
  have hmroot : eval x ((minpoly A x).map (algebraMap A B)) = 0 := by
    rw [← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval A x
  have hconv : aeval x (derivative (minpoly A x)) =
      eval x (derivative ((minpoly A x).map (algebraMap A B))) := by
    rw [Polynomial.derivative_map, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
  rw [differentIdeal_eq_span_aeval_derivative A K x hadjK hcond, hconv,
    span_eval_derivative_of_monic_uniformizer_root (algebraMap A B) hπA e he hram hx
      (minpoly.monic hint) hdegmin hmroot htame]


/-- **A generator of the different has valuation one less than the ramification index.**  This is
the form the ramification order law consumes: the Jacobian factor has order `e - 1`. -/
theorem addVal_generator_differentIdeal {πA : A} (hπA : Irreducible πA) (e : ℕ) (he : 0 < e)
    (hram : addVal B (algebraMap A B πA) = (e : ℕ∞)) {x : B} (hx : addVal B x = 1)
    (hres : ∀ b : B, ∃ a : A, addVal B (b - algebraMap A B a) ≠ 0)
    (hdvd : algebraMap A B πA ∣ x ^ e) (htame : addVal B ((e : ℕ) : B) = 0)
    {g : A[X]} (hmonic : g.Monic) (hdeg : g.natDegree = e) (hroot : aeval x g = 0)
    (halg : IsAlgebraic K (algebraMap B L x))
    {y : B} (hgen : differentIdeal A B = Ideal.span {y}) :
    addVal B y = ((e - 1 : ℕ) : ℕ∞) := by
  have h := differentIdeal_eq_span_pow A K hπA e he hram hx hres hdvd htame hmonic hdeg hroot halg
  rw [hgen] at h
  rw [addVal_eq_of_span_singleton_eq h, addVal_pow, hx]
  simp

end GaloisForLFunctions.HTGeometry
