import Mathlib

/-!
# Adjoining a root of a separable polynomial preserves reducedness

For a commutative ring `A` and a monic polynomial `f ∈ A[X]` whose derivative is coprime to it,
`A[X]/(f)` is reduced as soon as `A` is.  This is the ring-theoretic atom behind
*geometric reducedness in characteristic zero*: an algebraic closure is a filtered union of finite
separable extensions, each of which is `A[X]/(f)` after base change, so a reduced algebra over a
field of characteristic zero stays reduced after base change to the algebraic closure.

Mathlib has the class `Algebra.IsGeometricallyReduced` but **no instance for a perfect base field**,
so this is a genuine gap.

The proof is prime by prime.  Reducing a nilpotent element modulo the monic `f` leaves a
representative of degree `< deg f`; over the fraction field of `A/P` the polynomial `f` stays monic
of the same degree and stays separable, hence squarefree, hence radical in a unique factorisation
domain; so `f` divides the representative there, and the degree bound forces the representative to
vanish.  Every coefficient therefore lies in every prime, hence in the nilradical, hence is zero.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **Reducedness is preserved by adjoining a root of a monic separable polynomial.** -/
theorem isReduced_adjoinRoot_of_separable {A : Type*} [CommRing A] [IsReduced A]
    {f : A[X]} (hmonic : f.Monic) (hsep : f.Separable) :
    IsReduced (AdjoinRoot f) := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · haveI := hA
    haveI : Subsingleton (AdjoinRoot f) := by
      constructor
      intro a b
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective (g := f) a
      obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective (g := f) b
      congr 1
      exact Subsingleton.elim p q
    infer_instance
  constructor
  intro ξ hξ
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective (g := f) ξ
  -- reduce the representative modulo the monic `f`
  have hred : AdjoinRoot.mk f p = AdjoinRoot.mk f (p %ₘ f) := by
    refine AdjoinRoot.mk_eq_mk.mpr ⟨p /ₘ f, ?_⟩
    have := Polynomial.modByMonic_add_div p f
    linear_combination -this
  rw [hred] at hξ ⊢
  set q : A[X] := p %ₘ f with hq
  obtain ⟨n, hn⟩ := hξ
  have hdvd : f ∣ q ^ n := by
    have hz : AdjoinRoot.mk f (q ^ n) = 0 := by rw [map_pow]; exact hn
    exact (AdjoinRoot.mk_eq_zero).mp hz
  -- every coefficient of `q` lies in every prime ideal
  have hcoeff : ∀ i : ℕ, ∀ P : Ideal A, P.IsPrime → q.coeff i ∈ P := by
    intro i P hP
    haveI := hP
    let K := FractionRing (A ⧸ P)
    let φ : A →+* K := (algebraMap (A ⧸ P) K).comp (Ideal.Quotient.mk P)
    have hinj : Function.Injective (algebraMap (A ⧸ P) K) :=
      IsFractionRing.injective (A ⧸ P) K
    have hφker : ∀ a : A, φ a = 0 → a ∈ P := by
      intro a h
      have h1 : (algebraMap (A ⧸ P) K) ((Ideal.Quotient.mk P) a) = 0 := h
      have h2 : (Ideal.Quotient.mk P) a = 0 := by
        apply hinj
        rw [h1, map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem).mp h2
    have hfmap : (f.map φ).Monic := hmonic.map φ
    have hsepmap : (f.map φ).Separable := hsep.map (f := φ)
    have hdvdmap : f.map φ ∣ (q.map φ) ^ n := by
      have hm := Polynomial.map_dvd φ hdvd
      rwa [Polynomial.map_pow] at hm
    have hrad : IsRadical (f.map φ) := (hsepmap.squarefree).isRadical
    have hdvd' : f.map φ ∣ q.map φ := hrad n _ hdvdmap
    have hqzero : q.map φ = 0 := by
      have hdeg : (q.map φ).degree < (f.map φ).degree := by
        have h1 : q.degree < f.degree := Polynomial.degree_modByMonic_lt p hmonic
        have h2 : (q.map φ).degree ≤ q.degree := Polynomial.degree_map_le
        have h3 : (f.map φ).degree = f.degree := hmonic.degree_map φ
        rw [h3]
        exact lt_of_le_of_lt h2 h1
      exact Polynomial.eq_zero_of_dvd_of_degree_lt hdvd' hdeg
    refine hφker _ ?_
    have hc := congrArg (fun r : K[X] => r.coeff i) hqzero
    simpa [Polynomial.coeff_map] using hc
  have hzero : q = 0 := by
    ext i
    have hmem : q.coeff i ∈ nilradical A := by
      rw [nilradical_eq_sInf]
      refine Submodule.mem_sInf.mpr ?_
      intro P hP
      simp only [Set.mem_setOf_eq] at hP
      exact hcoeff i P hP
    rw [nilradical_eq_zero A] at hmem
    simpa using hmem
  rw [hzero, map_zero]

end GaloisForLFunctions.HTGeometry
