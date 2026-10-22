import GaloisForLFunctions.HTGeometry.CohenMacaulayTransport
import GaloisForLFunctions.HTGeometry.PolynomialCohenMacaulay
import GaloisForLFunctions.RHTower.Deninger.DeningerHankelHigherRankGroebner

/-!
# The degenerate range of the Hankel stratification

A canonical `(r+1)`-minor of the Hankel matrix needs `2r + 1` coefficient coordinates: its column
offsets are strictly increasing, so the last one is at least `r`, and the bound `r + 1 + c j ≤ N`
forces `N ≥ 2r + 1`.  Below that window there are no minors at all, the secant ideal is zero, and
the secant variety is the whole coefficient space.

```text
finiteHankelMaximalMinorSetOver_eq_empty     no minors when N ≤ 2r
finiteHankelSecantIdeal_eq_bot               so the ideal is ⊥
isCohenMacaulayRing_hankelSecantQuotient_of_le
    ** the quotient is a polynomial ring, hence Cohen–Macaulay, for every r when N ≤ 2r **
```

This is the base case of the induction on the number of coefficients: `del(0)` of the chain complex
is the same complex on one fewer vertex, and the recursion bottoms out exactly here.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial RHTower

universe u
variable {K : Type u} [Field K]

/-- **Below the critical window there are no minors at all.**  A canonical `(r+1)`-minor needs
`2r + 1` coefficient coordinates. -/
theorem finiteHankelMaximalMinorSetOver_eq_empty (K : Type u) [Field K] {N r : ℕ}
    (hN : N ≤ 2 * r) :
    finiteHankelMaximalMinorSetOver K N (r + 1) = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, hbound, hc, rfl⟩
  have hlast : (r : ℕ) ≤ c (Fin.last r) := by
    have := fin_val_le_of_strictMono_nat (d := c) hc (Fin.last r)
    simpa using this
  have := hbound (Fin.last r)
  omega

/-- **The rank-`r` Hankel secant ideal is zero below the critical window.** -/
theorem finiteHankelSecantIdeal_eq_bot (K : Type u) [Field K] {N r : ℕ} (hN : N ≤ 2 * r) :
    finiteHankelSecantIdeal K N r = ⊥ := by
  rw [finiteHankelSecantIdeal, finiteHankelMaximalMinorSetOver_eq_empty K hN, Ideal.span_empty]

/-- **The degenerate range of the Hankel stratification is Cohen–Macaulay**: for `N ≤ 2r` the secant
variety is the whole coefficient space, so its coordinate ring is a polynomial ring. -/
theorem isCohenMacaulayRing_hankelSecantQuotient_of_le (K : Type u) [Field K] {N r : ℕ}
    (hN : N ≤ 2 * r) :
    IsCohenMacaulayRing (MvPolynomial (Fin N) K ⧸ finiteHankelSecantIdeal K N r) := by
  refine IsCohenMacaulayRing.of_ringEquiv ?_ (isCohenMacaulayRing_mvPolynomial K N)
  refine RingEquiv.trans ?_ (Ideal.quotEquivOfEq (finiteHankelSecantIdeal_eq_bot K hN)).symm
  exact (RingEquiv.quotientBot (MvPolynomial (Fin N) K)).symm

end GaloisForLFunctions.HTGeometry
