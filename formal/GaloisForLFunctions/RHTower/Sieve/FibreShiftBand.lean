import GaloisForLFunctions.RHTower.Sieve.FibreDiagonalSum

/-!
# The off-diagonal lives at shifts of size `h`

The kernel is symmetric, and the multiplicative band `max/min ≤ 1 + h/√x` becomes an *additive*
band once the localisation `m, n ∈ [√x/2, √x + h]` is used:

```text
m, n in a common fibre  →  |m − n| ≤ h + h²/√x .
```

So the off-diagonal part of the bilinear form is

```text
∑_{k ≠ 0, |k| ≲ h} K(n+k, n)·∑_n μ(n)·μ(n+k) ,
```

a weighted sum of binary correlations of `μ` at shifts up to `h`.  That is the exact content of what
remains: not the individual correlations — those are Chowla, and open — but their average over
`|k| ≤ h` as `h → ∞`, which is what Matomäki–Radziwiłł prove.  The reduction is therefore faithful:
it lands on a statement of the right strength, neither weaker nor stronger than the theorem.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The kernel is symmetric. -/
theorem fibre_kernel_symm (x h : ℝ) (m n : ℕ) :
    (outerBlock x h).filter (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a)
      = (outerBlock x h).filter (fun a => n ∈ innerFibre x h a ∧ m ∈ innerFibre x h a) := by
  classical
  refine Finset.filter_congr fun a _ => ?_
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

/-- **Two members of a common fibre differ by at most `h + h²/√x`.** -/
theorem fibre_shift_band {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) {m n a : ℕ}
    (ha : a ∈ outerBlock x h) (hma : m ∈ innerFibre x h a) (hna : n ∈ innerFibre x h a) :
    |(m : ℝ) - (n : ℝ)| ≤ h + h ^ (2 : ℕ) / Real.sqrt x := by
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hmsupp := fibre_kernel_support hx ha hma
  have hnsupp := fibre_kernel_support hx ha hna
  -- the raw constraints
  rw [mem_innerFibre] at hma hna
  obtain ⟨-, hm1, hm2⟩ := hma
  obtain ⟨-, hn1, hn2⟩ := hna
  have hmR : ((a * m : ℕ) : ℝ) = (a : ℝ) * (m : ℝ) := by push_cast; ring
  have hnR : ((a * n : ℕ) : ℝ) = (a : ℝ) * (n : ℝ) := by push_cast; ring
  rw [hmR] at hm1 hm2
  rw [hnR] at hn1 hn2
  have ha0 : (0 : ℝ) < (a : ℝ) := by
    rw [mem_outerBlock] at ha
    exact lt_of_lt_of_le hs0 ha.2.1
  -- the one-sided comparisons
  have hmn : x * (m : ℝ) ≤ (x + h * Real.sqrt x) * (n : ℝ) := by
    nlinarith [hm2, hn1, ha0, (Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ)),
      (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
  have hnm : x * (n : ℝ) ≤ (x + h * Real.sqrt x) * (m : ℝ) := by
    nlinarith [hn2, hm1, ha0, (Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ)),
      (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
  -- convert to an additive gap using the localisation
  -- a one-sided gap bound, used twice
  have hgap : ∀ p q : ℕ, x * (q : ℝ) ≤ (x + h * Real.sqrt x) * (p : ℝ) →
      (p : ℝ) ≤ Real.sqrt x + h → (q : ℝ) - (p : ℝ) ≤ h + h ^ (2 : ℕ) / Real.sqrt x := by
    intro p q hpq hpb
    have hstep1 : x * ((q : ℝ) - (p : ℝ)) ≤ h * Real.sqrt x * (p : ℝ) := by nlinarith [hpq]
    have hstep2 : (q : ℝ) - (p : ℝ) ≤ h * (p : ℝ) / Real.sqrt x := by
      rw [le_div_iff₀ hs0]
      nlinarith [hstep1, hsq, hs0]
    have h1 : h * (p : ℝ) ≤ h * (Real.sqrt x + h) := mul_le_mul_of_nonneg_left hpb hh
    have h2 : h * (Real.sqrt x + h) / Real.sqrt x = h + h ^ (2 : ℕ) / Real.sqrt x := by
      field_simp
    have h3 : h * (p : ℝ) / Real.sqrt x ≤ h + h ^ (2 : ℕ) / Real.sqrt x := by
      calc h * (p : ℝ) / Real.sqrt x ≤ h * (Real.sqrt x + h) / Real.sqrt x :=
            div_le_div_of_nonneg_right h1 hs0.le
        _ = h + h ^ (2 : ℕ) / Real.sqrt x := h2
    linarith [hstep2, h3]
  rw [abs_le]
  constructor
  · linarith [hgap m n hnm hmsupp.2]
  · linarith [hgap n m hmn hnsupp.2]

end RHTower.Sieve

end
