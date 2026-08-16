import GaloisForLFunctions.RHTower.FiniteEulerInert

/-!
# Prime-loop connectivity versus the mixed-word obstruction

An isolated primitive loop of length `log p` has geometric orbit sum `-log(1 - p^{-s})`, so its
repetitions exponentiate to exactly the local Euler factor `(1 - p^{-s})^{-1}`, and a disjoint union
of prime loops reproduces every finite Euler product.

Joining two prime loops at a vertex creates the mixed closed word `pq`.  Its length is
`log p + log q = log (pq)`, its amplitude is the nonzero product of the two loop weights, and `pq` is
not a prime power — so the Riemann Euler product has no primitive factor there.  Forcing every mixed
amplitude to vanish leaves at most one active sector in each scalar block, which is the disconnected
model again.

## Main results

* `hasSum_primeLoopOrbit` — the geometric orbit expansion of one prime loop;
* `exp_primeLoopOrbit` — its exponential is the local Euler factor;
* `exp_sum_primeLoopOrbit` — a disjoint union reproduces the finite Euler product;
* `mixedWordLength`, `mixedWordWeight_ne_zero`, `not_isPrimePow_mul_of_ne` — the mixed word is
  primitive, nonzero, and unmatched in the Euler product;
* `eq_of_mixedWordWeight_eq_zero` — exact removal of mixed words block-diagonalizes the sectors.
-/

noncomputable section

namespace RHTower

open Complex

/-! ### The isolated prime loop -/

/-- The multiplier of a single traversal of the prime loop of length `log p`. -/
def primeLoopMultiplier (p : ℕ) (s : ℂ) : ℂ := Complex.exp (-(s * (Real.log p : ℂ)))

theorem eulerInvFactor_eq_one_sub (p : ℕ) (s : ℂ) :
    eulerInvFactor p s = 1 - primeLoopMultiplier p s := rfl

theorem norm_primeLoopMultiplier_lt_one {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    ‖primeLoopMultiplier p s‖ < 1 := by
  have hlog : 0 < Real.log p := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  rw [primeLoopMultiplier, Complex.norm_exp]
  refine Real.exp_lt_one_iff.mpr ?_
  simp only [neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith

/-- **The geometric orbit expansion of one prime loop.**  Summing the repetitions of the primitive
loop of length `log p` gives the local Euler logarithm. -/
theorem hasSum_primeLoopOrbit {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun m : ℕ => Complex.exp (-((m : ℂ) * s * (Real.log p : ℂ))) / (m : ℂ))
      (-Complex.log (eulerInvFactor p s)) := by
  have hz := norm_primeLoopMultiplier_lt_one hp hs
  have h := Complex.hasSum_taylorSeries_neg_log hz
  rw [← eulerInvFactor_eq_one_sub] at h
  refine h.congr_fun (fun m => ?_)
  congr 1
  rw [primeLoopMultiplier, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- **Exponentiating the orbit sum gives the local Euler factor.** -/
theorem exp_primeLoopOrbit {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : 0 < s.re) :
    Complex.exp (-Complex.log (eulerInvFactor p s)) = (eulerInvFactor p s)⁻¹ := by
  rw [Complex.exp_neg, Complex.exp_log (eulerInvFactor_ne_zero p hp hs)]

/-- **A disjoint union of prime loops reproduces the finite Euler product.** -/
theorem exp_sum_primeLoopOrbit (P : Finset ℕ) (hP : ∀ p ∈ P, 1 < p) {s : ℂ} (hs : 0 < s.re) :
    Complex.exp (∑ p ∈ P, -Complex.log (eulerInvFactor p s))
      = ∏ p ∈ P, (eulerInvFactor p s)⁻¹ := by
  rw [Complex.exp_sum]
  exact Finset.prod_congr rfl (fun p hp => exp_primeLoopOrbit (hP p hp) hs)

/-! ### The mixed word -/

/-- The length of the mixed closed word through the two prime loops. -/
theorem mixedWordLength {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    Real.log (p : ℝ) + Real.log (q : ℝ) = Real.log (((p * q : ℕ) : ℝ)) := by
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hq.ne')]

/-- **The mixed amplitude is nonzero.**  Positive scalar orbit sums cannot cancel it. -/
theorem mixedWordWeight_ne_zero {a : ℕ → ℂ} {p q : ℕ} (hp : a p ≠ 0) (hq : a q ≠ 0) :
    a p * a q ≠ 0 := mul_ne_zero hp hq

/-- **The composite is not a prime power.**  The Riemann Euler product has no primitive factor
indexed by `pq`. -/
theorem not_isPrimePow_mul_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ IsPrimePow (p * q) := by
  rintro ⟨r, k, hr, hk, hrk⟩
  have hrp : Nat.Prime r := hr.nat_prime
  have hdvdp : p ∣ r ^ k := by
    rw [hrk]
    exact Dvd.intro q rfl
  have hdvdq : q ∣ r ^ k := by
    rw [hrk]
    exact Dvd.intro_left p rfl
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hrp).mp (hp.dvd_of_dvd_pow hdvdp)
  have hqr : q = r := (Nat.prime_dvd_prime_iff_eq hq hrp).mp (hq.dvd_of_dvd_pow hdvdq)
  exact hpq (hpr.trans hqr.symm)

/-- **Exact removal of the mixed words block-diagonalizes the sectors.**  If every mixed length-two
amplitude vanishes, at most one sector of the scalar block is active. -/
theorem eq_of_mixedWordWeight_eq_zero {a : ℕ → ℂ}
    (h : ∀ p q : ℕ, p ≠ q → a p * a q = 0) {p q : ℕ} (hp : a p ≠ 0) (hq : a q ≠ 0) : p = q := by
  by_contra hpq
  exact mixedWordWeight_ne_zero hp hq (h p q hpq)

/-- **The dichotomy.**  A connected pair of prime loops with nonzero weights necessarily carries a
mixed primitive word absent from the Euler product; removing every mixed word forces a single active
sector. -/
theorem primeLoop_connectivity_dichotomy {a : ℕ → ℂ} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (a p ≠ 0 → a q ≠ 0 →
        a p * a q ≠ 0 ∧ Real.log (p : ℝ) + Real.log (q : ℝ) = Real.log (((p * q : ℕ) : ℝ))
          ∧ ¬ IsPrimePow (p * q))
      ∧ ((∀ u v : ℕ, u ≠ v → a u * a v = 0) → a p = 0 ∨ a q = 0) := by
  refine ⟨fun hap haq => ⟨mixedWordWeight_ne_zero hap haq,
    mixedWordLength hp.pos hq.pos, not_isPrimePow_mul_of_ne hp hq hpq⟩, fun hall => ?_⟩
  by_contra hcon
  push Not at hcon
  exact hpq (eq_of_mixedWordWeight_eq_zero hall hcon.1 hcon.2)

end RHTower
