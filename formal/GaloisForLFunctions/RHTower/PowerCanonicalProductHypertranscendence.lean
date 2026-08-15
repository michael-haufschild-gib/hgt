import GaloisForLFunctions.RHTower.BarnesTailAsymptoticExpansion
import GaloisForLFunctions.HTGeometry.AsymptoticPolynomialCoefficients

/-!
# The Barnes remainder of an irrational-power canonical product satisfies no algebraic
differential equation

For `s > 0` irrational let `W_s(z) = ∏_{n ≥ 1} E_{⌊1/s⌋}(-z/n^s)`, and let `R_s` be the remainder of
the Barnes expansion of `x W_s'(x)/W_s(x)`: the Euler logarithmic derivative with the leading power
`(π/s) csc(π/s) x^{1/s}`, the ascending polynomial part and the constant `ζ(0)` removed.

Read in `t = 1/x`, the Euler jets of `R_s` have the Euler jets of the formal Barnes tail
`R̂_s(t) = ∑_{k ≥ 1} (-1)^k ζ(-sk) t^k` as their Poincaré expansions at `0⁺`.  A relation with
polynomial coefficients holding near `0⁺` therefore passes to the formal series, where the two-sided
profile of `R̂_s` forbids it.

This is the card's chain with the exact-order theorem of Sibuya--Ramis replaced by the direct
obstruction on the tail.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

variable {s : ℝ}

/-- For irrational `s` the reciprocal `1/s` is not the genus, so the Barnes ladder applies. -/
theorem powerGenus_ne_inv_of_irrational (hs : 0 < s) (hirr : Irrational s) :
    ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 1 / s := by
  intro hc
  have hsg : s * ((HTGeometry.powerGenus s : ℕ) : ℝ) = 1 := by
    rw [hc]
    field_simp
  have hg0 : ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsg
    exact one_ne_zero hsg.symm
  refine hirr ⟨1 / ((HTGeometry.powerGenus s : ℕ) : ℚ), ?_⟩
  have hq : ((1 / ((HTGeometry.powerGenus s : ℕ) : ℚ) : ℚ) : ℝ)
      = 1 / ((HTGeometry.powerGenus s : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hq, eq_comm, eq_div_iff hg0]
  exact hsg

/-- **The Barnes remainder of an irrational-power canonical product is hypertranscendental.**  No
nonzero polynomial in the Euler jets, with coefficients polynomial in `t = 1/x`, vanishes near
`0⁺`. -/
theorem not_polynomial_relation_barnesEulerJet (hs : 0 < s) (hirr : Irrational s)
    {m : ℕ} (P : MvPolynomial (Fin (m + 1)) (Polynomial ℂ)) (hP0 : P ≠ 0)
    (hrel : ∀ᶠ t : ℝ in originRight,
      MvPolynomial.eval₂ (Polynomial.evalRingHom ((t : ℝ) : ℂ))
        (fun j : Fin (m + 1) => barnesEulerJet s (j : ℕ) t) P = 0) :
    False := by
  have hne := powerGenus_ne_inv_of_irrational hs hirr
  have hexp : ∀ j : Fin (m + 1),
      IsAsymptoticExpansion (fun t : ℝ => barnesEulerJet s (j : ℕ) t)
        (eulerJetVector (m := m) (barnesTailSeries s) j) := fun j =>
    isAsymptoticExpansion_barnesEulerJet hs hne (j : ℕ)
  have hsol : IsFormalEulerADESolution
      (MvPolynomial.map (Polynomial.coeToPowerSeries.ringHom) P) (barnesTailSeries s) :=
    isFormalEulerADESolution_map_of_eventually hexp hrel
  have hQa : IsAnalyticDifferentialPolynomial
      (MvPolynomial.map (Polynomial.coeToPowerSeries.ringHom) P) :=
    isAnalyticDifferentialPolynomial_map_coe P
  have hQ0 : MvPolynomial.map (Polynomial.coeToPowerSeries.ringHom) P ≠ 0 :=
    map_coe_ne_zero hP0
  exact not_isFormalEulerADESolution_barnesTail _ hQa hQ0 hs hirr hsol

end RHTower
