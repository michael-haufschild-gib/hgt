import Mathlib

/-!
# Sign alternation certifies hyperbolicity

A real polynomial of degree at most `d` that alternates in sign at `d + 1` increasing points has `d`
distinct real roots, hence splits over `ℝ`.  This is the elementary certificate for hyperbolicity:
`d` sign changes force `d` roots by the intermediate value theorem, and `d` is already the maximum a
degree-`d` polynomial admits.

The certificate is what makes the Jensen–Pólya ladder attackable one degree at a time.  Since

```text
d/dX Jᵈ'ⁿ(X) = d · Jᵈ⁻¹'ⁿ⁺¹(X) ,
```

hyperbolicity of `Jᵈ'ⁿ` at one degree gives the next degree down for free, and the *upward* step is
exactly a sign-alternation test at the roots of the derivative: a real polynomial with hyperbolic
derivative is hyperbolic precisely when it alternates in sign there.  So a degree-`d` result plus
`d` sign inequalities gives degree `d + 1`, with no discriminant and no asymptotic expansion.
-/

open Polynomial

namespace GaloisForLFunctions

namespace SignAlternation

/-- `Hyperbolic p` : every root of `p` is real, i.e. `p` splits over `ℝ`, counted with
multiplicity. -/
def Hyperbolic (p : ℝ[X]) : Prop := p.roots.card = p.natDegree

/-- A sign change on an interval produces a root strictly inside it. -/
theorem exists_root_of_sign_change {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ x ∈ Set.Ioo a b, p.IsRoot x := by
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) :=
    (Polynomial.continuous p).continuousOn
  rcases lt_or_gt_of_ne (by
      intro hzero
      rw [hzero] at h
      simp at h : p.eval a ≠ 0) with hneg | hpos
  · have hbpos : 0 < p.eval b := by nlinarith
    have : (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) := ⟨hneg, hbpos⟩
    obtain ⟨x, hx, hxe⟩ := intermediate_value_Ioo hab.le hcont this
    exact ⟨x, hx, hxe⟩
  · have hbneg : p.eval b < 0 := by nlinarith
    have : (0 : ℝ) ∈ Set.Ioo (p.eval b) (p.eval a) := ⟨hbneg, hpos⟩
    obtain ⟨x, hx, hxe⟩ := intermediate_value_Ioo' hab.le hcont this
    exact ⟨x, hx, hxe⟩

/-- **Alternating signs give many distinct roots.**  If `y` is increasing on `{0, …, d}` and
`p.eval (y i)` alternates in sign there, then `p` has at least `d` distinct real roots. -/
theorem card_roots_toFinset_ge_of_alternating {p : ℝ[X]} {d : ℕ} {y : ℕ → ℝ}
    (hy : ∀ i, i < d → y i < y (i + 1))
    (halt : ∀ i, i ≤ d → 0 < (-1 : ℝ) ^ i * p.eval (y i)) :
    d ≤ p.roots.toFinset.card := by
  have hp0 : p ≠ 0 := by
    intro hzero
    have := halt 0 (Nat.zero_le _)
    rw [hzero] at this
    simp at this
  have hstep : ∀ i, i < d → ∃ x ∈ Set.Ioo (y i) (y (i + 1)), p.IsRoot x := by
    intro i hi
    refine exists_root_of_sign_change (hy i hi) ?_
    have h1 := halt i (le_of_lt hi)
    have h2 := halt (i + 1) hi
    rcases Nat.even_or_odd i with he | ho
    · rw [he.neg_one_pow, one_mul] at h1
      rw [(Even.add_one he).neg_one_pow] at h2
      nlinarith
    · rw [ho.neg_one_pow] at h1
      rw [(Odd.add_one ho).neg_one_pow, one_mul] at h2
      nlinarith
  choose r hr hroot using hstep
  classical
  have hmono : ∀ (i j : ℕ) (hi : i < d) (hj : j < d), i < j → r i hi < r j hj := by
    intro i j hi hj hij
    have h1 := (hr i hi).2
    have h2 := (hr j hj).1
    have hchain : y (i + 1) ≤ y j := by
      clear h1 h2
      induction j with
      | zero => omega
      | succ k ih =>
        rcases Nat.lt_or_ge i k with hlt | hge
        · exact le_trans (ih (by omega) (by omega)) (le_of_lt (hy k (by omega)))
        · have hik : i + 1 = k + 1 := by omega
          rw [hik]
    linarith
  have hinj : Set.InjOn (fun i => if h : i < d then r i h else 0) (Finset.range d : Finset ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    simp only [dif_pos hi, dif_pos hj] at hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hij (ne_of_lt (hmono i j hi hj h))
    · exact absurd hij.symm (ne_of_lt (hmono j i hj hi h))
  have hcard := Finset.card_le_card_of_injOn
    (f := fun i => if h : i < d then r i h else 0)
    (s := Finset.range d) (t := p.roots.toFinset)
    (by
      intro i hi
      simp only [Finset.coe_range, Set.mem_Iio] at hi
      simp only [dif_pos hi]
      exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots hp0).mpr (hroot i hi))))
    hinj
  simpa using hcard

/-- **Sign alternation certifies hyperbolicity.**  A polynomial of degree at most `d` alternating in
sign at `d + 1` increasing points splits over `ℝ`. -/
theorem hyperbolic_of_alternating {p : ℝ[X]} {d : ℕ} {y : ℕ → ℝ}
    (hdeg : p.natDegree ≤ d)
    (hy : ∀ i, i < d → y i < y (i + 1))
    (halt : ∀ i, i ≤ d → 0 < (-1 : ℝ) ^ i * p.eval (y i)) :
    Hyperbolic p := by
  classical
  have hdist := card_roots_toFinset_ge_of_alternating hy halt
  have h1 : p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le _
  have h2 : p.roots.card ≤ p.natDegree := Polynomial.card_roots' p
  have hle : d ≤ p.natDegree := le_trans hdist (le_trans h1 h2)
  have hdeg' : p.natDegree = d := le_antisymm hdeg hle
  unfold Hyperbolic
  omega


/-- The Jensen polynomial of a sequence, as a polynomial. -/
noncomputable def jensenPoly (a : ℕ → ℝ) (d n : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) * a (n + j)) * X ^ j

theorem natDegree_jensenPoly_le (a : ℕ → ℝ) (d n : ℕ) : (jensenPoly a d n).natDegree ≤ d := by
  unfold jensenPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  simpa using Finset.mem_range_succ_iff.mp hj

/-- **The Jensen ladder.**  Differentiating a Jensen polynomial lowers the degree and raises the
shift: `d/dX Jᵈ⁺¹'ⁿ = (d+1) · Jᵈ'ⁿ⁺¹`.  So hyperbolicity propagates *downward* for free by Rolle, and
the upward step is exactly a sign-alternation test at the roots of the derivative. -/
theorem derivative_jensenPoly (a : ℕ → ℝ) (d n : ℕ) :
    derivative (jensenPoly a (d + 1) n) = C ((d : ℝ) + 1) * jensenPoly a d (n + 1) := by
  unfold jensenPoly
  rw [derivative_sum, Finset.mul_sum, Finset.sum_range_succ' _ (d + 1)]
  simp only [derivative_C_mul, derivative_X_pow, pow_zero, mul_one, derivative_C, add_zero,
    Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hchoose : (((d + 1).choose (i + 1) : ℝ)) * ((i : ℝ) + 1)
      = ((d : ℝ) + 1) * (d.choose i : ℝ) := by
    have h := Nat.add_one_mul_choose_eq d i
    have hcast := congrArg (fun k : ℕ => (k : ℝ)) h
    push_cast at hcast
    linarith
  rw [show n + (i + 1) = n + 1 + i by ring, ← mul_assoc, ← C_mul, ← mul_assoc, ← C_mul]
  congr 2
  push_cast
  linear_combination a (n + 1 + i) * hchoose

end SignAlternation

end GaloisForLFunctions
