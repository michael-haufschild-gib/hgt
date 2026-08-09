import GaloisForLFunctions.HTGeometry.AffineTopColumn

/-!
# The head's contribution to the newest column

A univariate head `g` at the newest coordinate contributes

`E(g'/g) = (∏_(j<m) fac j)·[lead·P(g) + cnst·W(g)] / g²`,

with `W(g) = g''g − g'g'` and `P(g) = X·W(g) + g'g` — the same two polynomials as for a
polynomial-coefficient law, since the computation only ever sees the coefficients of the factor one
level down.  Both are two degrees below `g²`, so the whole contribution has degree `−2`.

A **rational** head is a difference of two univariate ones, and the scalar operator is linear, so
the rational case is the difference of two instances of the same bound.  That is what makes the
rational-coefficient family cost nothing extra here.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

namespace AffineFam

variable (E : AffineFam)

theorem topShift_sub (m : ℕ) (x y : CascadeField) :
    E.toPairFam.topShift m (x - y)
      = E.toPairFam.topShift m x - E.toPairFam.topShift m y := by
  simp only [PairFam.topShift, map_sub]
  ring

/-! ## The head's jets -/

theorem law_fact_top (g : Polynomial ℂ) (m : ℕ) :
    E.toPairFam.law (fact g m) = fact g.derivative m * E.toPairFam.jet m := by
  rw [derivation_fact, PairFam.law_fx]

theorem fpderiv_top_law_fact (g : Polynomial ℂ) (n : ℕ) :
    fpderiv (n + 1) (E.toPairFam.law (fact g (n + 1)))
      = fact g.derivative.derivative (n + 1) * E.toPairFam.jet (n + 1)
        + fact g.derivative (n + 1) * (E.toPairFam.jet n * E.lead n) := by
  rw [E.law_fact_top, Derivation.leibniz, fpderiv_fact_self,
    show fpderiv (n + 1) (E.toPairFam.jet (n + 1)) = E.toPairFam.response (n + 1) (n + 1) from rfl,
    E.response_top n]
  simp only [smul_eq_mul]
  ring

/-- **The head's contribution to the newest column.** -/
theorem topShift_logFactor {g : Polynomial ℂ} (hg : g ≠ 0) (n : ℕ) :
    E.toPairFam.topShift (n + 1) (logFactor g (n + 1))
      = E.toPairFam.jet n
          * (E.lead n * fact (headDefect g) (n + 1) + E.cnst n * fact (headWr g) (n + 1))
          / (fact g (n + 1)) ^ 2 := by
  have hne : fact g (n + 1) ≠ 0 := fact_ne_zero hg (n + 1)
  have hmem : fact g (n + 1) ∈ coordField (n + 1) := fact_mem_coordField (le_refl (n + 1)) g
  have hlf : logFactor g (n + 1)
      = fpderiv (n + 1) (fact g (n + 1)) / fact g (n + 1) := by
    rw [fpderiv_fact_self, logFactor]
  rw [hlf, E.toPairFam.topShift_logDeriv hmem hne, E.fpderiv_top_law_fact g n,
    E.law_fact_top, fpderiv_fact_self, E.jet_succ_eq n, fac,
    headDefect, headWr, fact_add, fact_mul, fact_sub, fact_mul, fact_mul, fact_mul, fact_X]
  field_simp
  ring

theorem topDegLE_topShift_logFactor (g : Polynomial ℂ) (n : ℕ) :
    TopDegLE (n + 1) (-2) (E.toPairFam.topShift (n + 1) (logFactor g (n + 1))) := by
  rcases eq_or_ne g 0 with rfl | hg
  · have hzero : logFactor (0 : Polynomial ℂ) (n + 1) = 0 := by
      rw [logFactor, Polynomial.derivative_zero, fact_zero_eq, zero_div]
    rw [hzero, PairFam.topShift]
    simp only [map_zero, mul_zero, add_zero]
    exact topDegLE_zero _ _
  rcases eq_or_ne g.derivative 0 with hgd | hgd
  · have hzero : logFactor g (n + 1) = 0 := by
      rw [logFactor, hgd, fact_zero_eq, zero_div]
    rw [hzero, PairFam.topShift]
    simp only [map_zero, mul_zero, add_zero]
    exact topDegLE_zero _ _
  · have hdeg : 1 ≤ g.natDegree := by
      by_contra hc
      have hg0 : g.natDegree = 0 := by omega
      obtain ⟨c, hc'⟩ := Polynomial.natDegree_eq_zero.mp hg0
      exact hgd (by rw [← hc', Polynomial.derivative_C])
    rw [E.topShift_logFactor hg n]
    have hP : TopDegLE (n + 1) (2 * (g.natDegree : ℤ) - 2)
        (fact (headDefect g) (n + 1)) := by
      refine TopDegLE.mono ?_ (topDegLE_fact (n + 1) (headDefect g))
      have := natDegree_headDefect_le hdeg
      omega
    have hW : TopDegLE (n + 1) (2 * (g.natDegree : ℤ) - 2) (fact (headWr g) (n + 1)) := by
      refine TopDegLE.mono ?_ (topDegLE_fact (n + 1) (headWr g))
      have := natDegree_headWr_le hdeg
      omega
    have hGinv : TopDegLE (n + 1) (-(2 * (g.natDegree : ℤ)))
        ((fact g (n + 1) ^ 2)⁻¹) := by
      have h1 := topDegLE_inv_fact (n + 1) hg
      have h2 := TopDegLE.mul h1 h1
      rw [← mul_inv, ← pow_two] at h2
      refine TopDegLE.mono ?_ h2
      omega
    have h1 : TopDegLE (n + 1) (2 * (g.natDegree : ℤ) - 2)
        (E.lead n * fact (headDefect g) (n + 1)) := by
      have := TopDegLE.mul (E.topFree_lead (by omega : n < n + 1)).topDegLE hP
      simpa using this
    have h2 : TopDegLE (n + 1) (2 * (g.natDegree : ℤ) - 2)
        (E.cnst n * fact (headWr g) (n + 1)) := by
      have := TopDegLE.mul (E.topFree_cnst (by omega : n < n + 1)).topDegLE hW
      simpa using this
    have hnum : TopDegLE (n + 1) (2 * (g.natDegree : ℤ) - 2)
        (E.toPairFam.jet n
          * (E.lead n * fact (headDefect g) (n + 1)
            + E.cnst n * fact (headWr g) (n + 1))) := by
      have := TopDegLE.mul (E.topFree_jet_top (by omega : n < n + 1)).topDegLE
        (TopDegLE.add h1 h2)
      simpa using this
    rw [div_eq_mul_inv]
    have := TopDegLE.mul hnum hGinv
    refine TopDegLE.mono ?_ this
    omega

/-- **A rational head contributes degree `−2` as well.** -/
theorem topDegLE_topShift_logRatFactor (g₁ g₂ : Polynomial ℂ) (n : ℕ) :
    TopDegLE (n + 1) (-2)
      (E.toPairFam.topShift (n + 1) (logRatFactor g₁ g₂ (n + 1))) := by
  rw [logRatFactor, E.topShift_sub]
  exact TopDegLE.sub (E.topDegLE_topShift_logFactor g₁ n)
    (E.topDegLE_topShift_logFactor g₂ n)

end AffineFam

end GaloisForLFunctions.HTGeometry
