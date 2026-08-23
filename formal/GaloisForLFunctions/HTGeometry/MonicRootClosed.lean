import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Rings in which every monic polynomial has a root

A commutative ring is *monic-root closed* if every monic polynomial of positive degree has a root
in it.  The integral closure of a ring in an algebraically closed field has this property, the
property passes to quotients, and the fraction field of a monic-root closed domain is
algebraically closed — the scaling `X ↦ X / d` by a common denominator turns a monic polynomial
over the fraction field into a monic polynomial over the ring.

Consequently every residue field of an integral closure in an algebraically closed field is
algebraically closed.
-/

namespace HTGeometry

open Polynomial

/-- A commutative ring is *monic-root closed* if every monic polynomial of positive degree has a
root in it. -/
def IsMonicRootClosed (R : Type*) [CommRing R] : Prop :=
  ∀ f : R[X], f.Monic → f.degree ≠ 0 → ∃ a : R, f.eval a = 0

/-- The integral closure of a ring in an algebraically closed field is monic-root closed: a root
of a monic polynomial over the integral closure lies in the field, is integral over the integral
closure, hence over the base. -/
theorem isMonicRootClosed_integralClosure (R C : Type*) [CommRing R] [Field C] [Algebra R C]
    [IsAlgClosed C] : IsMonicRootClosed (integralClosure R C) := by
  intro F hFmonic hdeg
  have hdeg' : (F.map (algebraMap (integralClosure R C) C)).degree ≠ 0 := by
    rw [hFmonic.degree_map]
    exact hdeg
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg'
  have hroot : Polynomial.eval₂ (algebraMap (integralClosure R C) C) α F = 0 := by
    have := hα
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at this
  have hint : IsIntegral (integralClosure R C) α := ⟨F, hFmonic, hroot⟩
  have hintR : IsIntegral R α := isIntegral_trans α hint
  refine ⟨⟨α, hintR⟩, Subtype.ext ?_⟩
  have hmapval : (algebraMap (integralClosure R C) C) (F.eval ⟨α, hintR⟩)
      = Polynomial.eval₂ (algebraMap (integralClosure R C) C) α F := by
    rw [← Polynomial.eval₂_at_apply]
    rfl
  simpa [hroot] using hmapval

/-- Quotients of a monic-root closed ring are monic-root closed. -/
theorem IsMonicRootClosed.quotient {R : Type*} [CommRing R] (h : IsMonicRootClosed R)
    (I : Ideal R) : IsMonicRootClosed (R ⧸ I) := by
  classical
  intro f hmonic hdeg
  rcases subsingleton_or_nontrivial (R ⧸ I) with hs | _
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨F, hFmap, hFdeg, hFmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective f) hmonic
  obtain ⟨a, ha⟩ := h F hFmonic (by rw [hFdeg]; exact hdeg)
  refine ⟨Ideal.Quotient.mk I a, ?_⟩
  rw [← hFmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha, map_zero]

/-- A monic-root closed field is algebraically closed. -/
theorem IsMonicRootClosed.isAlgClosed {R : Type*} [Field R] (h : IsMonicRootClosed R) :
    IsAlgClosed R :=
  IsAlgClosed.of_exists_root _ fun f hmonic hirr =>
    h f hmonic fun hd => hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 hd)

/-- The fraction field of a monic-root closed domain is algebraically closed: scaling the roots of
a monic polynomial by a common denominator produces a monic polynomial over the ring, and a root
of that one divided by the denominator is a root of the original. -/
theorem IsMonicRootClosed.isAlgClosed_fractionRing {R : Type*} [CommRing R] [IsDomain R]
    (h : IsMonicRootClosed R) (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    IsAlgClosed K := by
  classical
  refine IsAlgClosed.of_exists_root _ fun p hmonic hirr => ?_
  have hpdeg : p.degree ≠ 0 := fun hd =>
    hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 hd)
  have hpnat : p.natDegree ≠ 0 := by
    intro hn
    exact hpdeg (by rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hn]; rfl)
  set d : nonZeroDivisors R := IsLocalization.commonDenom (nonZeroDivisors R) p.support p.coeff
    with hd
  have hlifts : p.scaleRoots (algebraMap R K (d : R)) ∈ Polynomial.lifts (algebraMap R K) :=
    IsLocalization.scaleRoots_commonDenom_mem_lifts (nonZeroDivisors R) p
      (by rw [hmonic.leadingCoeff]; exact one_mem _)
  have hsmonic : (p.scaleRoots (algebraMap R K (d : R))).Monic :=
    (Polynomial.monic_scaleRoots_iff _).2 hmonic
  obtain ⟨q, hqmap, hqdeg, hqmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts hsmonic
  have hsnat : (p.scaleRoots (algebraMap R K (d : R))).natDegree = p.natDegree :=
    Polynomial.natDegree_scaleRoots _ _
  have hqnat : q.natDegree ≠ 0 := by rw [hqdeg, hsnat]; exact hpnat
  have hqdegne : q.degree ≠ 0 := by
    intro hz
    rw [Polynomial.degree_eq_natDegree hqmonic.ne_zero] at hz
    exact hqnat (by exact_mod_cast hz)
  obtain ⟨b, hb⟩ := h q hqmonic hqdegne
  have hdne : algebraMap R K (d : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) d.2
  refine ⟨algebraMap R K b / algebraMap R K (d : R), ?_⟩
  have hroot : (p.scaleRoots (algebraMap R K (d : R))).eval (algebraMap R K b) = 0 := by
    rw [← hqmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hb, map_zero]
  have hmul : algebraMap R K (d : R) * (algebraMap R K b / algebraMap R K (d : R))
      = algebraMap R K b := mul_div_cancel₀ _ hdne
  have hev := Polynomial.scaleRoots_eval_mul p
    (algebraMap R K b / algebraMap R K (d : R)) (algebraMap R K (d : R))
  rw [hmul, hroot] at hev
  have hpow : (algebraMap R K (d : R)) ^ p.natDegree ≠ 0 := pow_ne_zero _ hdne
  exact (mul_eq_zero.mp hev.symm).resolve_left hpow

/-- **The residue fields of an integral closure in an algebraically closed field are algebraically
closed.**  This is the statement that `κ (x)` is algebraically closed for every point `x` of the
normalization of a scheme in an algebraic closure of its function field. -/
theorem isAlgClosed_of_isFractionRing_quotient_integralClosure (R C : Type*) [CommRing R] [Field C]
    [Algebra R C] [IsAlgClosed C] (Q : Ideal (integralClosure R C)) [Q.IsPrime]
    (κ : Type*) [Field κ] [Algebra (integralClosure R C ⧸ Q) κ]
    [IsFractionRing (integralClosure R C ⧸ Q) κ] : IsAlgClosed κ :=
  ((isMonicRootClosed_integralClosure R C).quotient Q).isAlgClosed_fractionRing κ

end HTGeometry
