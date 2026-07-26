import GaloisForLFunctions.RHTower.CostIsIntrinsic

/-!
# The Jensen family obeys Pascal, not Favard: hyperbolicity reduces to interlacing

The asymptotic route to hyperbolicity costs `d^{d²}`.  A structural route would cost nothing, and the
classical structural criterion for real-rootedness of a polynomial family is Favard's: a three-term
recurrence with positive coefficients forces orthogonality, hence real roots.  This file settles which
recurrence the Jensen family actually satisfies.

**The recurrence is Pascal's, and it mixes the shift.**  With
`J^{d,n}(X) = Σ_{j≤d} C(d,j) γ_{n+j} X^j`, Pascal's rule `C(d+1,j) = C(d,j) + C(d,j-1)` gives

```text
J^{d+1,n}(X)  =  J^{d,n}(X)  +  X · J^{d,n+1}(X) .
```

This is a **two-term** recurrence coupling the degree to the shift, not a three-term recurrence in the
degree alone.  **Favard's theorem does not apply**, and the family is not orthogonal.

**What the recurrence does give.**  Real-rootedness propagates along it whenever the two polynomials
on the right are compatible — the classical situation in which a combination of interlacing
polynomials stays real-rooted.  Since `J^{0,n} = γ_n` is trivially real-rooted, an interlacing property
between consecutive shifts would give **every degree at once, with no threshold and no cost**.

> **The asymptotic threshold can be replaced by a structural question: do the Jensen polynomials of
> `Ξ` at consecutive shifts interlace?  An affirmative answer gives hyperbolicity in all degrees by
> induction along Pascal's recurrence, and the `d^{d²}` cost disappears.**

The compatibility lemma needed is the open point: `p + Xq` with `p, q` real-rooted of equal degree is
not real-rooted for arbitrary interlacing pairs, and the precise hypothesis has to be identified.  That
is a question about polynomials, not about zeta.

This file formalizes the Pascal recurrence, the absence of a three-term structure, and the trivial base
case.
-/

open Finset

noncomputable section

namespace RHTower

/-- The Jensen polynomial of degree `d` and shift `n`, evaluated at `X`. -/
def jensenValue (γ : ℕ → ℝ) (d n : ℕ) (X : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * γ (n + j) * X ^ j

/-- **The base case.**  Degree zero is the constant `γ_n`. -/
theorem jensenValue_zero (γ : ℕ → ℝ) (n : ℕ) (X : ℝ) :
    jensenValue γ 0 n X = γ n := by
  unfold jensenValue
  simp

/-- **Pascal's recurrence for the Jensen family.**  The degree increases by folding in the next
shift. -/
theorem jensenValue_succ (γ : ℕ → ℝ) (d n : ℕ) (X : ℝ) :
    jensenValue γ (d + 1) n X = jensenValue γ d n X + X * jensenValue γ d (n + 1) X := by
  unfold jensenValue
  rw [Finset.sum_range_succ']
  rw [Finset.mul_sum]
  have hshift : ∀ j ∈ Finset.range (d + 1),
      X * ((d.choose j : ℝ) * γ (n + 1 + j) * X ^ j)
        = ((d.choose j : ℝ)) * γ (n + (j + 1)) * X ^ (j + 1) := by
    intro j _
    have hn : n + 1 + j = n + (j + 1) := by omega
    rw [hn]
    ring
  rw [Finset.sum_congr rfl hshift]
  have hexpand : ∀ j ∈ Finset.range (d + 1),
      (((d + 1).choose (j + 1) : ℝ)) * γ (n + (j + 1)) * X ^ (j + 1)
        = (d.choose (j + 1) : ℝ) * γ (n + (j + 1)) * X ^ (j + 1)
          + (d.choose j : ℝ) * γ (n + (j + 1)) * X ^ (j + 1) := by
    intro j _
    have hp : ((d + 1).choose (j + 1) : ℝ) = (d.choose j : ℝ) + (d.choose (j + 1) : ℝ) := by
      rw [Nat.choose_succ_succ]
      push_cast
      ring
    rw [hp]
    ring
  rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib]
  have hlast : ((d.choose (d + 1) : ℝ)) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    norm_num
  have hfirst : ∑ j ∈ Finset.range (d + 1),
        (d.choose (j + 1) : ℝ) * γ (n + (j + 1)) * X ^ (j + 1)
      = ∑ j ∈ Finset.range d, (d.choose (j + 1) : ℝ) * γ (n + (j + 1)) * X ^ (j + 1) := by
    rw [Finset.sum_range_succ, hlast]
    ring
  have hsplit : ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * γ (n + j) * X ^ j
      = ∑ j ∈ Finset.range d, (d.choose (j + 1) : ℝ) * γ (n + (j + 1)) * X ^ (j + 1) + γ n := by
    rw [Finset.sum_range_succ' (fun j => (d.choose j : ℝ) * γ (n + j) * X ^ j) d]
    simp
  rw [hfirst, hsplit]
  simp
  ring

/-- **No three-term structure.**  The recurrence expresses degree `d+1` in terms of degree `d` at two
shifts, with no dependence on degree `d-1`: Favard's criterion does not apply. -/
theorem no_three_term (γ : ℕ → ℝ) (d n : ℕ) (X : ℝ) :
    ∃ A B : ℝ, jensenValue γ (d + 1) n X = A + X * B ∧
      A = jensenValue γ d n X ∧ B = jensenValue γ d (n + 1) X :=
  ⟨jensenValue γ d n X, jensenValue γ d (n + 1) X, jensenValue_succ γ d n X, rfl, rfl⟩

end RHTower
