import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Real multiplicative data see only square successor pairs

Real sources are twisted by completely multiplicative **signs** rather than phases. For a finite
set `S` of primes and a sign vector `s ∈ {±1}^S`, the sign twist is
`ε_s(n) = ∏_{p ∈ S} s_p^{v_p(n)}` (`primeSignTwist`). It is the `2`-torsion of the gauge torus.

* **Sign orthogonality** (`sum_primeSignTwist_mul`). Summed over all `2^{|S|}` sign vectors,
  `ε_s(m) ε_s(n)` gives `∏_{p ∈ S} (2 if v_p(m) + v_p(n) is even, else 0)`: the sign gauge pairs
  `m` with `n` exactly when `mn` has even exponents at every prime of `S`.
* **The sign-gauge mean of a successor correlation** (`sum_signTwisted_succCorr`). If `S` contains
  every prime below the horizon, the sign-gauge mean of `Σ_j a_j a_{j+h}` keeps exactly the
  **square pairs**: the `j` with `j(j+h)` a perfect square (`isSquare_of_squarePair`).
* **Square pairs are finite** (`two_mul_add_le_sq_of_squarePair`). If `j(j+h) = y²` with `h ≥ 1`,
  then `(2j + h − 2y)(2j + h + 2y) = h²`, so `2j + h ≤ h²`. For the successor `h = 1` there are none
  (`not_squarePair_one`).

Consequently (`sum_signTwisted_succCorr_eq_zero_of_large`, `sum_signTwisted_succCorr_one`) the
sign-gauge mean of every shift-`h` correlation over `j > h²/2`, and of the shift-one correlation
over all `j ≥ 1`, is zero: real multiplicative data determine a successor correlation only through
the finitely many square pairs of its shift. Every other pair is pure sign charge.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

/-! ### Sign twists and their orthogonality -/

/-- The sign twist `ε_s(n) = ∏_{p ∈ S} s_p^{v_p(n)}`. -/
def primeSignTwist (S : Finset ℕ) (s : S → ℤˣ) (n : ℕ) : ℤ :=
  ∏ p : S, ((s p : ℤˣ) : ℤ) ^ (n.factorization p)

/-- The sum of `t^k` over the two signs. -/
theorem sum_units_pow (k : ℕ) : ∑ t : ℤˣ, ((t : ℤ)) ^ k = if Even k then 2 else 0 := by
  rw [Fintype.sum_eq_add 1 (-1) (by decide) (fun u hu => by
    rcases Int.units_eq_one_or u with h | h
    · exact absurd h hu.1
    · exact absurd h hu.2)]
  rcases Nat.even_or_odd k with hk | hk
  · rw [if_pos hk]; simp [hk.neg_one_pow]
  · rw [if_neg (Nat.not_even_iff_odd.mpr hk)]; simp [hk.neg_one_pow]

/-- **Sign orthogonality.** -/
theorem sum_primeSignTwist_mul (S : Finset ℕ) (m n : ℕ) :
    ∑ s : S → ℤˣ, primeSignTwist S s m * primeSignTwist S s n =
      ∏ p : S, (if Even (m.factorization p + n.factorization p) then (2 : ℤ) else 0) := by
  classical
  have hprod : ∀ s : S → ℤˣ, primeSignTwist S s m * primeSignTwist S s n =
      ∏ p : S, ((s p : ℤˣ) : ℤ) ^ (m.factorization p + n.factorization p) := by
    intro s
    rw [primeSignTwist, primeSignTwist, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => (pow_add _ _ _).symm
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun (p : S) (t : ℤˣ) => ((t : ℤ)) ^ (m.factorization p + n.factorization p))]
  exact Finset.prod_congr rfl fun p _ => sum_units_pow _

/-- The product of the two-or-zero factors is `2^{|S|}` when every exponent is even, else `0`. -/
theorem prod_two_or_zero (S : Finset ℕ) (k : ℕ → ℕ) :
    ∏ p : S, (if Even (k p) then (2 : ℤ) else 0) =
      if ∀ p ∈ S, Even (k p) then 2 ^ S.card else 0 := by
  classical
  split_ifs with h
  · rw [Finset.prod_congr rfl fun p _ => if_pos (h p.1 p.2), Finset.prod_const, Finset.card_univ,
      Fintype.card_coe]
  · push Not at h
    obtain ⟨p, hp, hodd⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨p, hp⟩) (if_neg hodd)

/-! ### Square pairs -/

/-- `(j, j+h)` is a **square pair** if `j(j+h)` has even exponent at every prime. -/
def SquarePair (j h : ℕ) : Prop := ∀ p, Even ((j * (j + h)).factorization p)

/-- A number with even exponents everywhere is a perfect square. -/
theorem exists_sq_eq_of_even_factorization {n : ℕ} (hn : n ≠ 0)
    (he : ∀ p, Even (n.factorization p)) : ∃ y, y * y = n := by
  refine ⟨n.factorization.prod fun p k => p ^ (k / 2), ?_⟩
  rw [← Finsupp.prod_mul]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  refine Finset.prod_congr rfl fun p _ => ?_
  show p ^ (n.factorization p / 2) * p ^ (n.factorization p / 2) = p ^ n.factorization p
  rw [← pow_add]
  congr 1
  have := Nat.two_mul_div_two_of_even (he p)
  omega

theorem isSquare_of_squarePair {j h : ℕ} (hj : j ≠ 0) (hsq : SquarePair j h) :
    ∃ y, y * y = j * (j + h) :=
  exists_sq_eq_of_even_factorization (Nat.mul_ne_zero hj (by omega)) hsq

/-- **Square pairs are finite.** If `j(j+h) = y²` and `h ≥ 1`, then `2j + h ≤ h²`. -/
theorem two_mul_add_le_sq_of_eq {j h y : ℕ} (hh : 1 ≤ h) (hy : y * y = j * (j + h)) :
    2 * j + h ≤ h * h := by
  -- `(2j + h)² − (2y)² = h²` with `2y < 2j + h`
  have hlt : 2 * y < 2 * j + h := by
    by_contra hc
    push Not at hc
    have : (2 * j + h) * (2 * j + h) ≤ (2 * y) * (2 * y) := Nat.mul_le_mul hc hc
    nlinarith
  have key : (2 * j + h - 2 * y) * (2 * j + h + 2 * y) = h * h := by
    have e : (2 * j + h) * (2 * j + h) = (2 * y) * (2 * y) + h * h := by nlinarith
    have hsub : 2 * j + h - 2 * y + 2 * y = 2 * j + h := Nat.sub_add_cancel hlt.le
    nlinarith [hsub]
  have hpos : 1 ≤ 2 * j + h - 2 * y := by omega
  nlinarith [key, hpos]

theorem two_mul_add_le_sq_of_squarePair {j h : ℕ} (hj : j ≠ 0) (hh : 1 ≤ h)
    (hsq : SquarePair j h) : 2 * j + h ≤ h * h := by
  obtain ⟨y, hy⟩ := isSquare_of_squarePair hj hsq
  exact two_mul_add_le_sq_of_eq hh hy

/-- **No successor pair is a square pair.** -/
theorem not_squarePair_one {j : ℕ} (hj : j ≠ 0) : ¬ SquarePair j 1 := by
  intro hsq
  have := two_mul_add_le_sq_of_squarePair hj le_rfl hsq
  omega

/-! ### The sign-gauge mean of successor correlations -/

/-- The successor correlation of the sign-twisted source. -/
def signTwistedSuccCorr (S : Finset ℕ) (s : S → ℤˣ) (A : Finset ℕ) (h : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ j ∈ A, ((primeSignTwist S s j : ℤ) : ℝ) * a j * (((primeSignTwist S s (j + h) : ℤ) : ℝ) *
    a (j + h))

open scoped Classical in
/-- **The sign-gauge mean of a successor correlation keeps exactly the square pairs.** If `S`
contains every prime dividing some `j(j+h)`, `j ∈ A`, then summing over all sign vectors gives
`2^{|S|} Σ_{j ∈ A, square pair} a_j a_{j+h}`. -/
theorem sum_signTwisted_succCorr (S : Finset ℕ) (A : Finset ℕ) (hA : ∀ j ∈ A, j ≠ 0) (h : ℕ)
    (hS : ∀ j ∈ A, ∀ p, p.Prime → p ∣ j * (j + h) → p ∈ S) (a : ℕ → ℝ) :
    ∑ s : S → ℤˣ, signTwistedSuccCorr S s A h a =
      2 ^ S.card * ∑ j ∈ A with SquarePair j h, a j * a (j + h) := by
  classical
  simp only [signTwistedSuccCorr]
  rw [Finset.sum_comm, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 := hA j hj
  have hjh : j + h ≠ 0 := by omega
  have hterm : ∀ s : S → ℤˣ, ((primeSignTwist S s j : ℤ) : ℝ) * a j *
      (((primeSignTwist S s (j + h) : ℤ) : ℝ) * a (j + h)) =
      (((primeSignTwist S s j * primeSignTwist S s (j + h) : ℤ)) : ℝ) * (a j * a (j + h)) := by
    intro s; push_cast; ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Int.cast_sum, sum_primeSignTwist_mul,
    prod_two_or_zero S (fun p => j.factorization p + (j + h).factorization p)]
  have hiff : (∀ p ∈ S, Even (j.factorization p + (j + h).factorization p)) ↔ SquarePair j h := by
    have hfac : ∀ p, (j * (j + h)).factorization p = j.factorization p + (j + h).factorization p :=
      fun p => by rw [Nat.factorization_mul hj0 hjh]; rfl
    constructor
    · intro hS' p
      rw [hfac]
      by_cases hp : p ∈ S
      · exact hS' p hp
      · -- primes outside `S` do not divide `j(j+h)`
        have hzero : (j * (j + h)).factorization p = 0 := by
          by_contra hne
          have hpr : p.Prime := Nat.prime_of_mem_primeFactors
            (Finsupp.mem_support_iff.mpr hne |> (Nat.support_factorization _ ▸ ·))
          exact hp (hS j hj p hpr (Nat.dvd_of_factorization_pos hne))
        rw [← hfac, hzero]
        exact ⟨0, rfl⟩
    · intro hsq p _
      rw [← hfac]
      exact hsq p
  by_cases hsq : SquarePair j h
  · rw [if_pos (hiff.mpr hsq), if_pos hsq]
    push_cast
    ring
  · rw [if_neg (fun h' => hsq (hiff.mp h')), if_neg hsq]
    simp

/-- **Beyond `h²/2` every successor pair is pure sign charge.** -/
theorem sum_signTwisted_succCorr_eq_zero_of_large (S : Finset ℕ) (A : Finset ℕ) {h : ℕ}
    (hh : 1 ≤ h) (hA : ∀ j ∈ A, h * h < 2 * j + h)
    (hS : ∀ j ∈ A, ∀ p, p.Prime → p ∣ j * (j + h) → p ∈ S) (a : ℕ → ℝ) :
    ∑ s : S → ℤˣ, signTwistedSuccCorr S s A h a = 0 := by
  classical
  have hA0 : ∀ j ∈ A, j ≠ 0 := fun j hj => by
    have := hA j hj
    intro h0; rw [h0] at this; nlinarith
  rw [sum_signTwisted_succCorr S A hA0 h hS, Finset.sum_eq_zero, mul_zero]
  intro j hj
  obtain ⟨hjA, hsq⟩ := Finset.mem_filter.mp hj
  exact absurd (two_mul_add_le_sq_of_squarePair (hA0 j hjA) hh hsq) (not_le.mpr (hA j hjA))

/-- **The successor correlation has sign-gauge mean zero.** -/
theorem sum_signTwisted_succCorr_one (S : Finset ℕ) (A : Finset ℕ) (hA : ∀ j ∈ A, j ≠ 0)
    (hS : ∀ j ∈ A, ∀ p, p.Prime → p ∣ j * (j + 1) → p ∈ S) (a : ℕ → ℝ) :
    ∑ s : S → ℤˣ, signTwistedSuccCorr S s A 1 a = 0 := by
  classical
  rw [sum_signTwisted_succCorr S A hA 1 hS, Finset.sum_eq_zero, mul_zero]
  intro j hj
  obtain ⟨hjA, hsq⟩ := Finset.mem_filter.mp hj
  exact absurd hsq (not_squarePair_one (hA j hjA))

end GaloisForLFunctions.ArithmeticCorrelationGeometry
