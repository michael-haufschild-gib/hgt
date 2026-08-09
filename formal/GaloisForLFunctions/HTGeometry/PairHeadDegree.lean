import GaloisForLFunctions.HTGeometry.PairHeadBorder

/-!
# The head's Wronskian and defect

The head factor `g(X_m)` contributes two univariate polynomials to the newest column of the
two-coordinate law:

`W(g) = g''·g − g'·g'`  and  `P(g) = X·W(g) + g'·g`.

Both are two degrees below `g²`.  For `W` that is the usual Wronskian drop.  For `P` it needs the
cancellation of the two leading terms, which is exactly the identity

`P(g) = R(g)'·g − g'·R(g)`,   `R(g) = X·g' − (deg g)·g`,

the same Wronskian shape one step further in: `R(g)` is the reduced polynomial whose degree already
drops by one, so its Wronskian against `g` drops by two.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-! ## A derivative against a polynomial -/

/-- A derivative of something of degree `d − 1` against something of degree `d` lands two below
`2d`.  The zero case is separate because `natDegree 0 = 0`. -/
theorem natDegree_derivative_mul_le {q r : Polynomial ℂ} {d : ℕ} (hq : q.natDegree ≤ d - 1)
    (hr : r.natDegree ≤ d) (hd : 1 ≤ d) : (q.derivative * r).natDegree ≤ 2 * d - 2 := by
  rcases eq_or_ne q.derivative 0 with hq0 | hq0
  · rw [hq0, zero_mul, Polynomial.natDegree_zero]
    omega
  · have hq1 : 1 ≤ q.natDegree := by
      by_contra hc
      have hq00 : q.natDegree = 0 := by omega
      obtain ⟨c, hc'⟩ := Polynomial.natDegree_eq_zero.mp hq00
      exact hq0 (by rw [← hc', Polynomial.derivative_C])
    have hd2 : 2 ≤ d := by omega
    have h1 : q.derivative.natDegree ≤ q.natDegree - 1 := Polynomial.natDegree_derivative_le q
    have h2 := Polynomial.natDegree_mul_le (p := q.derivative) (q := r)
    omega

/-! ## The head's Wronskian -/

/-- The Wronskian of the head against itself. -/
noncomputable def headWr (g : Polynomial ℂ) : Polynomial ℂ :=
  g.derivative.derivative * g - g.derivative * g.derivative

/-- The reduced head: the degree already drops by one. -/
noncomputable def headRed (g : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X * g.derivative - Polynomial.C ((g.natDegree : ℂ)) * g

/-- The head's defect in the newest column. -/
noncomputable def headDefect (g : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X * headWr g + g.derivative * g

theorem natDegree_headWr_le {g : Polynomial ℂ} (hg : 1 ≤ g.natDegree) :
    (headWr g).natDegree ≤ 2 * g.natDegree - 2 := by
  have h1 : (g.derivative.derivative * g).natDegree ≤ 2 * g.natDegree - 2 :=
    natDegree_derivative_mul_le (Polynomial.natDegree_derivative_le g) (le_refl _) hg
  have h2 : (g.derivative * g.derivative).natDegree ≤ 2 * g.natDegree - 2 := by
    have hd := Polynomial.natDegree_derivative_le g
    have := Polynomial.natDegree_mul_le (p := g.derivative) (q := g.derivative)
    omega
  have := Polynomial.natDegree_sub_le (g.derivative.derivative * g) (g.derivative * g.derivative)
  rw [headWr]
  omega

theorem natDegree_headRed_le {g : Polynomial ℂ} (hg : 1 ≤ g.natDegree) :
    (headRed g).natDegree ≤ g.natDegree - 1 := by
  have h := natDegree_reduced_le (Q := g) (v := Polynomial.X) hg Polynomial.natDegree_X
  rw [headRed]
  simpa using h

/-- **The head's defect is a Wronskian one step further in.** -/
theorem headDefect_eq (g : Polynomial ℂ) :
    headDefect g = (headRed g).derivative * g - g.derivative * headRed g := by
  have hd : (headRed g).derivative
      = g.derivative + Polynomial.X * g.derivative.derivative
        - Polynomial.C ((g.natDegree : ℂ)) * g.derivative := by
    rw [headRed, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X,
      Polynomial.derivative_C_mul]
    ring
  rw [hd, headRed, headDefect, headWr]
  ring

theorem natDegree_headDefect_le {g : Polynomial ℂ} (hg : 1 ≤ g.natDegree) :
    (headDefect g).natDegree ≤ 2 * g.natDegree - 2 := by
  have h1 : ((headRed g).derivative * g).natDegree ≤ 2 * g.natDegree - 2 :=
    natDegree_derivative_mul_le (natDegree_headRed_le hg) (le_refl _) hg
  have h2 : (g.derivative * headRed g).natDegree ≤ 2 * g.natDegree - 2 := by
    have hd := Polynomial.natDegree_derivative_le g
    have hr := natDegree_headRed_le hg
    have := Polynomial.natDegree_mul_le (p := g.derivative) (q := headRed g)
    omega
  have := Polynomial.natDegree_sub_le ((headRed g).derivative * g) (g.derivative * headRed g)
  rw [headDefect_eq]
  omega

end GaloisForLFunctions.HTGeometry
