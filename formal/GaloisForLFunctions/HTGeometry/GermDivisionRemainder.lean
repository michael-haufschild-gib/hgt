import GaloisForLFunctions.HTGeometry.GermIrreducibleTransfer
import GaloisForLFunctions.HTGeometry.GermDivisionAlgebraic

/-!
# Division with remainder by a distinguished polynomial, and primality

Every germ — regular or not — can be divided by the distinguished polynomial of a *regular* germ.
That asymmetry is what makes primality provable without any coordinate change: the divisor is
distinguished, hence regular, while the dividend is arbitrary.

Reducing modulo the distinguished polynomial therefore lands in the polynomial ring, where
divisibility is polynomial divisibility.  Consequently a distinguished polynomial prime in
`ℂ{z'}[X]` has a prime germ: reduce both factors of a product, transfer the divisibility, split it
in the polynomial ring, and lift back.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Filter Topology

variable {n : ℕ}

/-- **Division with remainder by a distinguished polynomial.** -/
theorem exists_germ_division {d : ℕ} (hd : 0 < d) {α : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (hzero : ∀ j, j < d → germValueMap n (α j) = 0)
    (g : AnalyticGerm (0 : Fin (n + 1) → ℂ)) :
    ∃ (q : AnalyticGerm (0 : Fin (n + 1) → ℂ))
      (R : Polynomial (AnalyticGerm (0 : Fin n → ℂ))),
      R.degree < (d : ℕ) ∧ g = q * germEval n (distPoly d α) + germEval n R := by
  classical
  obtain ⟨F, hFA, hFeq⟩ := (germEval n (distPoly d α)).2
  have hFgerm : germEval n (distPoly d α) = analyticGermOf hFA := Subtype.ext hFeq.symm
  have hFreg : ¬ (fun z : ℂ => F (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0 := by
    have hne := germSlice_germEval_distPoly_ne_zero (α := α) hzero
    rw [hFgerm] at hne
    exact (germSlice_ne_zero_iff hFA).mp hne
  obtain ⟨G, hGA, hGeq⟩ := g.2
  have hGgerm : g = analyticGermOf hGA := Subtype.ext hGeq.symm
  obtain ⟨d', α', β', q', u', hu', hz', hprep', hdiv'⟩ := germ_division_algebraic hFA hGA hFreg
  have hprep : germEval n (distPoly d α) = germEval n (distPoly d' α') * u' := by
    rw [hFgerm, hprep', germEval_distPoly]
  have hd' : 0 < d' := by
    by_contra hc
    have hd'0 : d' = 0 := by omega
    refine not_isUnit_germEval_distPoly hd hzero ?_
    rw [hprep, hd'0, distPoly, lowDegreePoly, Finset.range_zero, Finset.sum_empty, pow_zero,
      add_zero, map_one, one_mul]
    exact hu'
  have hW : distPoly d α = distPoly d' α' :=
    distPoly_eq_of_unit_mul hd hd' hzero hz' hu' hprep
  have hdd : d = d' := by
    have := congrArg Polynomial.natDegree hW
    rwa [natDegree_distPoly, natDegree_distPoly] at this
  refine ⟨q', lowDegreePoly β' d', ?_, ?_⟩
  · rw [hdd]
    exact degree_lowDegreePoly_lt β' d'
  · rw [hGgerm, hdiv', germEval_lowDegreePoly, hW, germEval_distPoly]

/-- **Divisibility by a distinguished polynomial is the vanishing of the remainder.** -/
theorem dvd_iff_remainder_eq_zero {d : ℕ} (hd : 0 < d) {α : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (hzero : ∀ j, j < d → germValueMap n (α j) = 0)
    {g : AnalyticGerm (0 : Fin (n + 1) → ℂ)} {q : AnalyticGerm (0 : Fin (n + 1) → ℂ)}
    {R : Polynomial (AnalyticGerm (0 : Fin n → ℂ))} (hR : R.degree < (d : ℕ))
    (hg : g = q * germEval n (distPoly d α) + germEval n R) :
    germEval n (distPoly d α) ∣ g ↔ R = 0 := by
  have hind : GermIndependent d α := germIndependent_of_distinguished hd hzero
  constructor
  · rintro ⟨k, hk⟩
    refine eq_zero_of_germEval_eq_zero hind hR ?_
    have hrel : germEval n R
        = (k - q) * germEval n (distPoly d α) := by
      rw [hg] at hk
      linear_combination hk
    have hrel' : (-(k - q))
        * (germCoord n ^ d + ∑ j ∈ Finset.range d, germTail n (α j) * germCoord n ^ j)
        + ∑ j ∈ Finset.range d, germTail n (R.coeff j) * germCoord n ^ j = 0 := by
      rw [← germEval_eq_of_degree_lt hR, hrel, ← germEval_distPoly d α]
      ring
    have hcoeff := (hind _ _ hrel').2
    rw [germEval_eq_of_degree_lt hR]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hcoeff j (Finset.mem_range.mp hj), map_zero, zero_mul]
  · intro hR0
    refine ⟨q, ?_⟩
    rw [hg, hR0, map_zero, add_zero, mul_comm]

/-- **A distinguished polynomial prime in the polynomial ring has a prime germ.** -/
theorem prime_germEval_of_prime {d : ℕ} (hd : 0 < d) {α : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (hzero : ∀ j, j < d → germValueMap n (α j) = 0)
    (hp : Prime (distPoly d α)) : Prime (germEval n (distPoly d α)) := by
  have hind : GermIndependent d α := germIndependent_of_distinguished hd hzero
  refine ⟨?_, not_isUnit_germEval_distPoly hd hzero, ?_⟩
  · intro h0
    refine germSlice_germEval_distPoly_ne_zero hzero ?_
    rw [h0, map_zero]
  · intro g h hdvd
    obtain ⟨qg, Rg, hRgdeg, hgeq⟩ := exists_germ_division hd hzero g
    obtain ⟨qh, Rh, hRhdeg, hheq⟩ := exists_germ_division hd hzero h
    -- the product reduces to the product of the remainders
    obtain ⟨k, hk⟩ := hdvd
    have hprod : germEval n (Rg * Rh)
        = (k - (qg * qh * germEval n (distPoly d α) + qg * germEval n Rh
            + germEval n Rg * qh)) * germEval n (distPoly d α) := by
      rw [map_mul]
      have hgh : g * h = germEval n (distPoly d α) * k := hk
      rw [hgeq, hheq] at hgh
      linear_combination hgh
    have hdvdpoly : distPoly d α ∣ Rg * Rh := by
      refine (dvd_germEval_iff hind (Rg * Rh)).mp ?_
      refine ⟨k - (qg * qh * germEval n (distPoly d α) + qg * germEval n Rh
          + germEval n Rg * qh), ?_⟩
      rw [hprod]
      ring
    rcases hp.2.2 Rg Rh hdvdpoly with hg | hh
    · left
      obtain ⟨S, hS⟩ := hg
      refine ⟨qg + germEval n S, ?_⟩
      rw [hgeq, hS, map_mul]
      ring
    · right
      obtain ⟨S, hS⟩ := hh
      refine ⟨qh + germEval n S, ?_⟩
      rw [hheq, hS, map_mul]
      ring

end GaloisForLFunctions.HTGeometry
