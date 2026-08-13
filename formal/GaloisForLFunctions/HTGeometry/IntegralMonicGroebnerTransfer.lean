import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Integral transfer through monic Gröbner bases

This module isolates the coefficient-saturation mechanism needed for integral Hankel
determinantal ideals. A monic Gröbner basis over a ring remains a valid normal-form barrier after
an injective coefficient extension. Consequently, ideal membership contracts and primeness over
the larger coefficient ring descends without assuming flatness or torsion-freeness.
-/

namespace MonomialOrder

open MvPolynomial
open scoped MonomialOrder

variable {σ R S : Type*} [CommRing R] [CommRing S]

/-- Leading-degree formulation of the Gröbner basis property. -/
def IsGroebnerBasis (m : MonomialOrder σ) (B : Set (MvPolynomial σ R)) : Prop :=
  ∀ p ∈ Ideal.span B, p ≠ 0 → ∃ b ∈ B, m.degree b ≤ m.degree p

theorem degree_map_of_injective (m : MonomialOrder σ) (f : R →+* S)
    (hf : Function.Injective f) (p : MvPolynomial σ R) :
    m.degree (MvPolynomial.map f p) = m.degree p := by
  simp only [MonomialOrder.degree]
  rw [MvPolynomial.support_map_of_injective p hf]

theorem linearCombination_mem_span (B : Set (MvPolynomial σ R))
    (g : B →₀ MvPolynomial σ R) :
    Finsupp.linearCombination (MvPolynomial σ R)
      (fun b : B => (b : MvPolynomial σ R)) g ∈ Ideal.span B := by
  rw [Finsupp.linearCombination_apply]
  classical
  unfold Finsupp.sum
  apply Ideal.sum_mem
  intro b hb
  exact (Ideal.span B).mul_mem_left _ (Ideal.subset_span b.property)

/-- A polynomial in the span of a Gröbner basis cannot also be reduced unless it is zero. -/
theorem reduced_mem_span_eq_zero (m : MonomialOrder σ)
    (B : Set (MvPolynomial σ R))
    (hGB : m.IsGroebnerBasis B) (r : MvPolynomial σ R)
    (hr : r ∈ Ideal.span B)
    (hred : ∀ c ∈ r.support, ∀ b ∈ B, ¬m.degree b ≤ c) :
    r = 0 := by
  by_contra hr0
  obtain ⟨b, hbB, hb⟩ := hGB r hr hr0
  exact hred (m.degree r) (m.degree_mem_support hr0) b hbB hb

/-- **Monic coefficient contraction.** If the coefficient extension is injective and the mapped
generators are a Gröbner basis, mapped ideal membership already held over the source ring. -/
theorem mem_span_of_map_mem_span (m : MonomialOrder σ)
    (f : R →+* S) (hf : Function.Injective f)
    (B : Set (MvPolynomial σ R))
    (hmonic : ∀ b ∈ B, m.Monic b)
    (hGBmap : m.IsGroebnerBasis (MvPolynomial.map f '' B))
    (p : MvPolynomial σ R)
    (hp : MvPolynomial.map f p ∈
      Ideal.span (MvPolynomial.map f '' B)) :
    p ∈ Ideal.span B := by
  have hunit : ∀ b : B, IsUnit (m.leadingCoeff (b : MvPolynomial σ R)) := by
    intro b
    rw [(hmonic b b.property).leadingCoeff_eq_one]
    exact isUnit_one
  obtain ⟨g, r, hpr, _hgdeg, hred⟩ := m.div hunit p
  let q := Finsupp.linearCombination (MvPolynomial σ R)
    (fun b : B => (b : MvPolynomial σ R)) g
  have hq : q ∈ Ideal.span B := linearCombination_mem_span B g
  have hmapq : MvPolynomial.map f q ∈
      Ideal.span (MvPolynomial.map f '' B) := by
    rw [← Ideal.map_span]
    exact Ideal.mem_map_of_mem (MvPolynomial.map f) hq
  have hmapr : MvPolynomial.map f r ∈
      Ideal.span (MvPolynomial.map f '' B) := by
    have heq : MvPolynomial.map f r = MvPolynomial.map f p - MvPolynomial.map f q := by
      rw [hpr]
      simp only [map_add]
      ring
    rw [heq]
    exact (Ideal.span (MvPolynomial.map f '' B)).sub_mem hp hmapq
  have hredmap : ∀ c ∈ (MvPolynomial.map f r).support,
      ∀ b ∈ MvPolynomial.map f '' B, ¬m.degree b ≤ c := by
    intro c hc b hb
    obtain ⟨b0, hb0B, rfl⟩ := hb
    rw [MvPolynomial.support_map_of_injective r hf] at hc
    rw [m.degree_map_of_injective f hf b0]
    exact hred c hc ⟨b0, hb0B⟩
  have hmapr0 := reduced_mem_span_eq_zero m
    (MvPolynomial.map f '' B) hGBmap (MvPolynomial.map f r) hmapr hredmap
  have hr0 : r = 0 := by
    refine MvPolynomial.map_injective f hf ?_
    rw [hmapr0, map_zero]
  rw [hpr, hr0, add_zero]
  exact hq

/-- **Integral primeness transfer.** A monic Gröbner presentation whose coefficient extension is
prime is already prime before extending coefficients. -/
theorem span_isPrime_of_map (m : MonomialOrder σ)
    (f : R →+* S) (hf : Function.Injective f)
    (B : Set (MvPolynomial σ R))
    (hmonic : ∀ b ∈ B, m.Monic b)
    (hGBmap : m.IsGroebnerBasis (MvPolynomial.map f '' B))
    (hprime : (Ideal.span (MvPolynomial.map f '' B)).IsPrime) :
    (Ideal.span B).IsPrime := by
  rw [Ideal.isPrime_iff]
  constructor
  · intro htop
    have hmapone : MvPolynomial.map f (1 : MvPolynomial σ R) ∈
        Ideal.span (MvPolynomial.map f '' B) := by
      rw [← Ideal.map_span]
      exact Ideal.mem_map_of_mem (MvPolynomial.map f)
        (htop ▸ Submodule.mem_top (x := (1 : MvPolynomial σ R)))
    refine hprime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    simpa using hmapone
  · intro p q hpq
    have hmapmul : MvPolynomial.map f p * MvPolynomial.map f q ∈
        Ideal.span (MvPolynomial.map f '' B) := by
      rw [← map_mul]
      rw [← Ideal.map_span]
      exact Ideal.mem_map_of_mem (MvPolynomial.map f) hpq
    rcases hprime.mem_or_mem hmapmul with hp | hq
    · exact Or.inl (m.mem_span_of_map_mem_span f hf B hmonic hGBmap p hp)
    · exact Or.inr (m.mem_span_of_map_mem_span f hf B hmonic hGBmap q hq)

end MonomialOrder
