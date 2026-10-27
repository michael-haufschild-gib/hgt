import GaloisForLFunctions.ArithmeticIntersectionTheory.TheTowerFormOfAPrime
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheDifferentOfATorsionOrbit

/-!
# The self-intersection dominates the tower

The renormalized torsion form is `−P(x) − Σ x_n² c(n)` (AET), the prime kernel with the
self-intersection `c(n) = I(n,n)/φ(n)` on the diagonal. On a `p`-ladder `c, cp, cp², …` the prime part is
bounded by the tower (`ladderForm_lower`): `−P ≤ (2q/(1 + q)) log p` with `q = p^{−1/2}`. The diagonal grows
linearly along the ladder: the `p`-part of the different gives `c(cp^j) ≥ (j − 1/(p − 1)) log p`
(`selfIntersection_ladder_ge`).

* **Index bound** (`renormalized_ladder_le`): on cycles of a ladder vanishing at the two lowest levels,
  `−P(x) − Σ x_j² c(cp^j) ≤ −((1 − q)/(1 + q)) log p |x|²`. The renormalized torsion form is negative
  definite above the second level: on every ladder its positive index is at most `2`.

The self-intersection — the discriminant — is what makes the renormalized form negative: adjunction
beats the local tower from the second level on. This is the arithmetic form of `Δ² < 0` for a curve
of genus `≥ 2`, read one prime at a time.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory

/-- **The diagonal grows along a ladder**: `c(cp^j) ≥ (j − 1/(p − 1)) log p` for `j ≥ 1`. -/
theorem selfIntersection_ladder_ge {p c j : ℕ} (hp : p.Prime) (hc : 0 < c) (hj : 1 ≤ j) :
    ((j : ℝ) - 1 / ((p : ℝ) - 1)) * Real.log p ≤ selfIntersection (c * p ^ j) := by
  have hn : 0 < c * p ^ j := Nat.mul_pos hc (pow_pos hp.pos j)
  have hpmem : p ∈ (c * p ^ j).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) c, hn.ne'⟩
  rw [selfIntersection_eq_sum_local hn]
  have hterm : ∀ ℓ ∈ (c * p ^ j).primeFactors,
      0 ≤ (((c * p ^ j).factorization ℓ : ℝ) - 1 / ((ℓ : ℝ) - 1)) * Real.log ℓ := by
    intro ℓ hℓ
    have hℓp : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
    have hv : (1 : ℝ) ≤ (c * p ^ j).factorization ℓ := by
      exact_mod_cast (hℓp.dvd_iff_one_le_factorization hn.ne').mp (Nat.dvd_of_mem_primeFactors hℓ)
    have hℓ2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓp.two_le
    have hinv : 1 / ((ℓ : ℝ) - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  refine le_trans ?_ (single_le_sum hterm hpmem)
  have hvp : (j : ℝ) ≤ (c * p ^ j).factorization p := by
    rw [Nat.factorization_mul hc.ne' (pow_ne_zero j hp.ne_zero), Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same]
    push_cast; linarith [(Nat.cast_nonneg (c.factorization p) : (0 : ℝ) ≤ _)]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))

/-- **The self-intersection dominates the tower above the second level.** On a `p`-ladder, for cycles
vanishing at levels `0` and `1`, the renormalized torsion form is at most
`−((1 − q)/(1 + q)) log p |x|²`. -/
theorem renormalized_ladder_le {p c : ℕ} (hp : p.Prime) (hc : 0 < c) (N : ℕ) (x : ℕ → ℝ)
    (hx0 : x 0 = 0) (hx1 : x 1 = 0) :
    (1 + 1 / Real.sqrt p) * (-ladderForm p c N x -
        ∑ j ∈ range N, x j ^ 2 * selfIntersection (c * p ^ j)) ≤
      -((1 - 1 / Real.sqrt p) * Real.log p * ∑ j ∈ range N, x j ^ 2) := by
  set q := 1 / Real.sqrt p
  have hq0 : 0 ≤ q := inv_sqrt_prime_nonneg p
  have hq1 : q < 1 := inv_sqrt_prime_lt_one hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  -- each nonzero level has self-intersection at least `log p`
  have hdiag : Real.log p * ∑ j ∈ range N, x j ^ 2 ≤
      ∑ j ∈ range N, x j ^ 2 * selfIntersection (c * p ^ j) := by
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    rcases Nat.lt_or_ge j 2 with hj | hj
    · interval_cases j <;> simp [hx0, hx1]
    · have h := selfIntersection_ladder_ge hp hc (by omega : 1 ≤ j)
      have hinv : 1 / ((p : ℝ) - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
      have : Real.log p ≤ selfIntersection (c * p ^ j) :=
        le_trans (by nlinarith) h
      nlinarith [sq_nonneg (x j)]
  have hlow := ladderForm_lower hp hc N x
  nlinarith [mul_le_mul_of_nonneg_left hdiag (by linarith : (0 : ℝ) ≤ 1 + q),
    sum_nonneg fun j (_ : j ∈ range N) => sq_nonneg (x j)]

end GaloisForLFunctions.ArithmeticIntersectionTheory
