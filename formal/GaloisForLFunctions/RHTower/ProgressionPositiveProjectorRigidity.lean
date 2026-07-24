import Mathlib

/-!
# Positive progression projector rigidity law

For a finite complex sequence `a`, encoded as the coefficient sequence of a polynomial
`A = ∑ a_n Xⁿ`, its Hermitian additive self-convolution is

```
H_a(N) = ∑_{m+n=N} a_m * conj (a_n),
```

realised here as the coefficient sequence of the polynomial `A · A⋆` where `A⋆` conjugates every
coefficient (`hermConv`).  The divisibility-progression projector at a real point `r` keeps only the
additive totals divisible by the modulus `q`:

```
P_{q,a}(r) = ∑_{q ∣ N} H_a(N) rᴺ.
```

The rigidity law classifies exactly which moduli make this projector nonnegative for every finite
complex sequence and every `r > 0`:

* `q = 1` gives `P_{1,a}(r) = |A(r)|²`;
* `q = 2` gives `P_{2,a}(r) = (|A(r)|² + |A(-r)|²) / 2`;
* for every `q ≥ 3` the two-monomial sequence `A_q = X - X^{q-1}` is an exact negative witness,
  `P_{q,a_q}(r) = -2 r^q`.

Hence `P_{q,·}(·) ≥ 0` universally iff `q = 1` or `q = 2`: parity is the only nontrivial universally
positive divisibility projector.
-/

open Polynomial Complex
open scoped ComplexOrder BigOperators

namespace RHTower

noncomputable section

/-- Hermitian additive self-convolution of the coefficient sequence of `A`, realised as `A · A⋆`
where `A⋆ = A.map conj` conjugates each coefficient.  Its `N`-th coefficient is
`∑_{m+n=N} a_m * conj (a_n)`. -/
def hermConv (A : ℂ[X]) : ℂ[X] := A * A.map (starRingEnd ℂ)

/-- The divisibility-progression projector as a linear functional on polynomials: sum the
coefficients whose degree is divisible by `q`, each weighted by `rᴺ`. -/
def divProj (q : ℕ) (r : ℝ) (p : ℂ[X]) : ℂ :=
  p.sum (fun N c => if q ∣ N then c * (r : ℂ) ^ N else 0)

/-- Positive progression projector `P_{q,a}(r) = ∑_{q ∣ N} H_a(N) rᴺ`. -/
def progProjector (q : ℕ) (A : ℂ[X]) (r : ℝ) : ℂ := divProj q r (hermConv A)

/-- The conjugated polynomial evaluates to the conjugate of the evaluation at the conjugate point. -/
private theorem eval_map_conj (A : ℂ[X]) (x : ℂ) :
    (A.map (starRingEnd ℂ)).eval x = (starRingEnd ℂ) (A.eval ((starRingEnd ℂ) x)) := by
  induction A using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.map_add, hp, hq]
  | monomial n a =>
      simp [Polynomial.map_monomial, Polynomial.eval_monomial, map_mul, map_pow]

/-- At a point fixed by conjugation (in particular every real point), the Hermitian
self-convolution evaluates to the squared modulus `|A(x)|²`. -/
theorem hermConv_eval_of_conj_fixed (A : ℂ[X]) {x : ℂ} (hx : (starRingEnd ℂ) x = x) :
    (hermConv A).eval x = ((Complex.normSq (A.eval x) : ℝ) : ℂ) := by
  unfold hermConv
  rw [Polynomial.eval_mul, eval_map_conj, hx, Complex.mul_conj]

/-- The projector functional is additive in its polynomial argument. -/
theorem divProj_add (q : ℕ) (r : ℝ) (p p' : ℂ[X]) :
    divProj q r (p + p') = divProj q r p + divProj q r p' := by
  unfold divProj
  exact Polynomial.sum_add_index _ _ _ (by intro i; simp) (by intro a b₁ b₂; split_ifs <;> ring)

/-- The projector functional on a single monomial. -/
theorem divProj_monomial (q : ℕ) (r : ℝ) (n : ℕ) (c : ℂ) :
    divProj q r (monomial n c) = if q ∣ n then c * (r : ℂ) ^ n else 0 := by
  unfold divProj
  rw [Polynomial.sum_monomial_index]; simp

/-- `q = 1`: the full projector is `|A(r)|²`. -/
theorem progProjector_one (A : ℂ[X]) (r : ℝ) :
    progProjector 1 A r = ((Complex.normSq (A.eval (r : ℂ)) : ℝ) : ℂ) := by
  unfold progProjector divProj
  simp only [one_dvd, if_true]
  rw [← Polynomial.eval_eq_sum]
  exact hermConv_eval_of_conj_fixed A (Complex.conj_ofReal r)

/-- `q = 1`: the projector is nonnegative for every sequence and every `r`. -/
theorem progProjector_one_nonneg (A : ℂ[X]) (r : ℝ) : 0 ≤ progProjector 1 A r := by
  rw [progProjector_one]
  exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)

/-- `q = 2`: the even projector equals the average of the two Hermitian evaluations. -/
theorem progProjector_two_eq (A : ℂ[X]) (r : ℝ) :
    progProjector 2 A r
      = ((hermConv A).eval (r : ℂ) + (hermConv A).eval (-(r : ℂ))) / 2 := by
  unfold progProjector divProj
  rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0), Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  simp only [Polynomial.sum_def]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N _
  rw [neg_pow]
  rcases Nat.even_or_odd N with hN | hN
  · rw [if_pos (even_iff_two_dvd.mp hN), hN.neg_one_pow]; ring
  · rw [if_neg (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hN),
        hN.neg_one_pow]; ring

/-- `q = 2`: the even projector is `(|A(r)|² + |A(-r)|²)/2`. -/
theorem progProjector_two (A : ℂ[X]) (r : ℝ) :
    progProjector 2 A r
      = ((Complex.normSq (A.eval (r : ℂ)) : ℝ) : ℂ) / 2
        + ((Complex.normSq (A.eval (-(r : ℂ))) : ℝ) : ℂ) / 2 := by
  rw [progProjector_two_eq, hermConv_eval_of_conj_fixed A (Complex.conj_ofReal r),
      hermConv_eval_of_conj_fixed A
        (show (starRingEnd ℂ) (-(r : ℂ)) = -(r : ℂ) by rw [map_neg, Complex.conj_ofReal])]
  ring

/-- `q = 2`: the projector is nonnegative for every sequence and every `r`. -/
theorem progProjector_two_nonneg (A : ℂ[X]) (r : ℝ) : 0 ≤ progProjector 2 A r := by
  rw [progProjector_two]
  have ha : (0 : ℂ) ≤ ((Complex.normSq (A.eval (r : ℂ)) : ℝ) : ℂ) / 2 := by
    rw [show ((Complex.normSq (A.eval (r : ℂ)) : ℝ) : ℂ) / 2
        = ((Complex.normSq (A.eval (r : ℂ)) / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.mpr (by have := Complex.normSq_nonneg (A.eval (r : ℂ)); linarith)
  have hb : (0 : ℂ) ≤ ((Complex.normSq (A.eval (-(r : ℂ))) : ℝ) : ℂ) / 2 := by
    rw [show ((Complex.normSq (A.eval (-(r : ℂ))) : ℝ) : ℂ) / 2
        = ((Complex.normSq (A.eval (-(r : ℂ))) / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.mpr (by have := Complex.normSq_nonneg (A.eval (-(r : ℂ))); linarith)
  exact add_nonneg ha hb

/-- The Hermitian self-convolution of the two-monomial witness `A_q = X - X^{q-1}` expands to the
three-term polynomial `X² - 2 X^q + X^{2q-2}`. -/
theorem hermConv_witness (q : ℕ) (hq : 3 ≤ q) :
    hermConv (X - X ^ (q - 1)) = monomial 2 1 + monomial q (-2) + monomial (2 * q - 2) 1 := by
  unfold hermConv
  have hmap : (X - X ^ (q - 1) : ℂ[X]).map (starRingEnd ℂ) = X - X ^ (q - 1) := by
    simp [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
  rw [hmap]
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have e1 : (X : ℂ[X]) * X = X ^ 2 := by ring
  have e2 : (X : ℂ[X]) * X ^ (m + 1 - 1) = X ^ (m + 1) := by
    rw [show m + 1 - 1 = m by omega, ← pow_succ']
  have e4 : (X ^ (m + 1 - 1) : ℂ[X]) * X ^ (m + 1 - 1) = X ^ (2 * (m + 1) - 2) := by
    rw [show m + 1 - 1 = m by omega, ← pow_add]; congr 1; omega
  rw [mul_sub, sub_mul, sub_mul, e1, e2,
      show (X ^ (m + 1 - 1) : ℂ[X]) * X = X * X ^ (m + 1 - 1) by ring, e2, e4]
  have hq2 : (monomial (m + 1) (-2 : ℂ))
      = - monomial (m + 1) (1 : ℂ) - monomial (m + 1) (1 : ℂ) := by
    rw [← map_neg, ← map_sub]; norm_num
  simp only [X_pow_eq_monomial]
  rw [hq2]; ring

/-- Exact negative witness: for every modulus `q ≥ 3`, the two-monomial sequence
`A_q = X - X^{q-1}` gives `P_{q,a_q}(r) = -2 r^q`. -/
theorem progProjector_witness (q : ℕ) (hq : 3 ≤ q) (r : ℝ) :
    progProjector q (X - X ^ (q - 1)) r = -2 * (r : ℂ) ^ q := by
  unfold progProjector
  rw [hermConv_witness q hq, divProj_add, divProj_add, divProj_monomial, divProj_monomial,
      divProj_monomial]
  have hd2 : ¬ q ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hd3 : ¬ q ∣ (2 * q - 2) := by
    intro h
    have hqq : q ∣ (2 * q) := ⟨2, by ring⟩
    have h2 : q ∣ 2 := by
      have := Nat.dvd_sub hqq h
      rwa [show 2 * q - (2 * q - 2) = 2 by omega] at this
    have := Nat.le_of_dvd (by norm_num) h2; omega
  rw [if_neg hd2, if_pos (dvd_refl q), if_neg hd3]; ring

/-- **Positive progression projector rigidity law.**  For `q ≥ 1`, the divisibility-progression
projector of a Hermitian additive self-convolution is nonnegative for every finite complex sequence
and every `r > 0` if and only if `q = 1` or `q = 2`. -/
theorem progressionPositiveProjectorRigidity (q : ℕ) (hq : 1 ≤ q) :
    (∀ (A : ℂ[X]) (r : ℝ), 0 < r → 0 ≤ progProjector q A r) ↔ (q = 1 ∨ q = 2) := by
  constructor
  · intro hpos
    by_contra hcon
    have hq3 : 3 ≤ q := by omega
    have h0 := hpos (X - X ^ (q - 1)) 1 one_pos
    rw [progProjector_witness q hq3, Complex.ofReal_one, one_pow, mul_one,
        show (-2 : ℂ) = ((-2 : ℝ) : ℂ) by norm_num] at h0
    exact absurd (Complex.zero_le_real.mp h0) (by norm_num)
  · rintro (rfl | rfl)
    · exact fun A r _ => progProjector_one_nonneg A r
    · exact fun A r _ => progProjector_two_nonneg A r

end

end RHTower
