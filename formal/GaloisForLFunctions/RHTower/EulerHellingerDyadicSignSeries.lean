import GaloisForLFunctions.RHTower.EulerHellingerDyadicLogIdentity

/-!
# The prime-power series for the sewing cost, and its sign

Expanding each finite Euler logarithm by `-log(1-x) = ∑_{k≥1} x^k/k` turns the reflected Hellinger
sewing cost into a manifestly signed prime-power series: for each prime the local contribution is

```text
ℓ_p(c) = 2 ∑_{k≥1} (p^(-k)/k) [ sinh(2ck log p) - 2 sinh(ck log p) ],
```

and every summand is positive for `c > 0` because

```text
sinh(2u) - 2 sinh u = 2 sinh u (cosh u - 1) > 0      (u > 0).
```

Hence the sewing cost is strictly positive for positive drift, strictly negative for negative drift
by oddness, and zero only at the lossless boundary: the essential Hellinger sewing cost has the sign
of the drift, with no cancellation between primes or between powers.
-/

namespace RHTower

noncomputable section

/-! ## The dyadic sinh step -/

/-- The dyadic sinh defect factors. -/
theorem sinh_two_mul_sub_two_sinh (u : ℝ) :
    Real.sinh (2 * u) - 2 * Real.sinh u = 2 * Real.sinh u * (Real.cosh u - 1) := by
  rw [Real.sinh_two_mul]
  ring

/-- **The dyadic sinh step is strictly positive.** -/
theorem sinh_two_mul_sub_two_sinh_pos {u : ℝ} (hu : 0 < u) :
    0 < Real.sinh (2 * u) - 2 * Real.sinh u := by
  rw [sinh_two_mul_sub_two_sinh]
  have h1 : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  have h2 : 1 < Real.cosh u := Real.one_lt_cosh.mpr (ne_of_gt hu)
  nlinarith

/-! ## The local prime-power series -/

/-- A prime power difference is a hyperbolic sine. -/
theorem rpow_sub_rpow_neg_eq_two_sinh {p : ℕ} (hp : p.Prime) (a : ℝ) :
    (p : ℝ) ^ a - (p : ℝ) ^ (-a) = 2 * Real.sinh (a * Real.log (p : ℝ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0, Real.sinh_eq]
  have e1 : Real.log (p : ℝ) * a = a * Real.log (p : ℝ) := by ring
  have e2 : Real.log (p : ℝ) * -a = -(a * Real.log (p : ℝ)) := by ring
  rw [e1, e2]
  ring

/-- The local Euler logarithm series. -/
theorem hasSum_neg_log_one_sub_rpow {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun k : ℕ => ((p : ℝ) ^ (-σ)) ^ (k + 1) / ((k : ℝ) + 1))
      (-Real.log (1 - (p : ℝ) ^ (-σ))) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlt : (p : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hgt : 0 < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp0 _
  refine Real.hasSum_pow_div_log_of_abs_lt_one ?_
  rw [abs_of_pos hgt]
  exact hlt

/-- The local term of the Euler logarithm series in prime-power coordinates. -/
theorem pow_rpow_neg_eq {p : ℕ} (hp : p.Prime) (σ : ℝ) (k : ℕ) :
    ((p : ℝ) ^ (-σ)) ^ (k + 1) = (p : ℝ) ^ (-σ * ((k : ℝ) + 1)) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) (k + 1), ← Real.rpow_mul hp0]
  congr 1
  push_cast
  ring

/-- The local reflected sewing logarithm at a prime. -/
def localSewingLog (p : ℕ) (c : ℝ) : ℝ :=
  (-Real.log (1 - (p : ℝ) ^ (-(1 - 2 * c)))) - (-Real.log (1 - (p : ℝ) ^ (-(1 + 2 * c))))
    - 2 * ((-Real.log (1 - (p : ℝ) ^ (-(1 - c)))) - (-Real.log (1 - (p : ℝ) ^ (-(1 + c)))))

/-- **The local prime-power series for the sewing cost.**  Every summand is a dyadic sinh step
weighted by a positive prime-power mass. -/
theorem hasSum_localSewingLog {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : |c| < 1 / 2) :
    HasSum (fun k : ℕ =>
        2 * ((p : ℝ) ^ (-((k : ℝ) + 1)) / ((k : ℝ) + 1)) *
          (Real.sinh (2 * (c * ((k : ℝ) + 1) * Real.log (p : ℝ)))
            - 2 * Real.sinh (c * ((k : ℝ) + 1) * Real.log (p : ℝ))))
      (localSewingLog p c) := by
  obtain ⟨hcl, hcu⟩ := abs_lt.mp hc
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have h1 := hasSum_neg_log_one_sub_rpow hp (σ := 1 - 2 * c) (by linarith)
  have h2 := hasSum_neg_log_one_sub_rpow hp (σ := 1 + 2 * c) (by linarith)
  have h3 := hasSum_neg_log_one_sub_rpow hp (σ := 1 - c) (by linarith)
  have h4 := hasSum_neg_log_one_sub_rpow hp (σ := 1 + c) (by linarith)
  have hcomb := (h1.sub h2).sub (((h3.sub h4).mul_left 2))
  refine hcomb.congr_fun ?_ |>.congr_fun (fun _ => rfl)
  intro k
  have hpow : ∀ σ : ℝ, ((p : ℝ) ^ (-σ)) ^ (k + 1) = (p : ℝ) ^ (-σ * ((k : ℝ) + 1)) :=
    fun σ => pow_rpow_neg_eq hp σ k
  have hsplit : ∀ a : ℝ,
      (p : ℝ) ^ (-(1 - a) * ((k : ℝ) + 1))
        = (p : ℝ) ^ (-((k : ℝ) + 1)) * (p : ℝ) ^ (a * ((k : ℝ) + 1)) := by
    intro a
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  have hsinh : ∀ a : ℝ,
      (p : ℝ) ^ (a * ((k : ℝ) + 1)) - (p : ℝ) ^ (-(a * ((k : ℝ) + 1)))
        = 2 * Real.sinh (a * ((k : ℝ) + 1) * Real.log (p : ℝ)) :=
    fun a => rpow_sub_rpow_neg_eq_two_sinh hp _
  have hneg : ∀ a : ℝ,
      (p : ℝ) ^ (-(1 + a) * ((k : ℝ) + 1))
        = (p : ℝ) ^ (-((k : ℝ) + 1)) * (p : ℝ) ^ (-(a * ((k : ℝ) + 1))) := by
    intro a
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have harg : 2 * c * ((k : ℝ) + 1) * Real.log (p : ℝ)
      = 2 * (c * ((k : ℝ) + 1) * Real.log (p : ℝ)) := by ring
  have h2c : (p : ℝ) ^ (2 * c * ((k : ℝ) + 1)) - (p : ℝ) ^ (-(2 * c * ((k : ℝ) + 1)))
      = 2 * Real.sinh (2 * (c * ((k : ℝ) + 1) * Real.log (p : ℝ))) := by
    rw [hsinh (2 * c), harg]
  have h1c : (p : ℝ) ^ (c * ((k : ℝ) + 1)) - (p : ℝ) ^ (-(c * ((k : ℝ) + 1)))
      = 2 * Real.sinh (c * ((k : ℝ) + 1) * Real.log (p : ℝ)) := hsinh c
  simp only [hpow, hsplit, hneg]
  linear_combination (-((p : ℝ) ^ (-((k : ℝ) + 1)) / ((k : ℝ) + 1))) * h2c
    + (2 * ((p : ℝ) ^ (-((k : ℝ) + 1)) / ((k : ℝ) + 1))) * h1c

/-! ## The sign of the local contribution -/

/-- **The local contribution is strictly positive for positive drift.** -/
theorem localSewingLog_pos {p : ℕ} (hp : p.Prime) {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    0 < localSewingLog p c := by
  have habs : |c| < 1 / 2 := by
    rw [abs_of_pos hc0]
    exact hc
  have hsum := hasSum_localSewingLog hp habs
  have hlogp : 0 < Real.log (p : ℝ) := by
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    exact Real.log_pos hp1
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hterm : ∀ k : ℕ,
      0 < 2 * ((p : ℝ) ^ (-((k : ℝ) + 1)) / ((k : ℝ) + 1)) *
        (Real.sinh (2 * (c * ((k : ℝ) + 1) * Real.log (p : ℝ)))
          - 2 * Real.sinh (c * ((k : ℝ) + 1) * Real.log (p : ℝ))) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hmass : (0 : ℝ) < (p : ℝ) ^ (-((k : ℝ) + 1)) := Real.rpow_pos_of_pos hp0 _
    have hu : 0 < c * ((k : ℝ) + 1) * Real.log (p : ℝ) := by positivity
    have hstep := sinh_two_mul_sub_two_sinh_pos hu
    have hcoef : 0 < 2 * ((p : ℝ) ^ (-((k : ℝ) + 1)) / ((k : ℝ) + 1)) := by positivity
    exact mul_pos hcoef hstep
  have hle := le_hasSum hsum 0 (fun j _ => (hterm j).le)
  exact lt_of_lt_of_le (hterm 0) hle

/-! ## The global sign -/

/-- The sewing cost is the finite sum of local contributions. -/
theorem logReflectedSewingBelow_eq_sum_localSewingLog {c : ℝ} (hc : |c| < 1 / 2) (N : ℕ) :
    logReflectedSewingBelow c N = ∑ p ∈ Nat.primesBelow N, localSewingLog p c := by
  obtain ⟨hcl, hcu⟩ := abs_lt.mp hc
  have key : ∀ f g h i : ℕ → ℝ,
      (∑ p ∈ Nat.primesBelow N, f p) - (∑ p ∈ Nat.primesBelow N, g p)
          - 2 * (∑ p ∈ Nat.primesBelow N, h p) + 2 * (∑ p ∈ Nat.primesBelow N, i p)
        = ∑ p ∈ Nat.primesBelow N, (f p - g p - 2 * h p + 2 * i p) := by
    intro f g h i
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
  rw [logReflectedSewingBelow_eq hc,
    primeEulerLogBelow_eq_sum (by linarith : (0:ℝ) < 1 - 2 * c) N,
    primeEulerLogBelow_eq_sum (by linarith : (0:ℝ) < 1 + 2 * c) N,
    primeEulerLogBelow_eq_sum (by linarith : (0:ℝ) < 1 - c) N,
    primeEulerLogBelow_eq_sum (by linarith : (0:ℝ) < 1 + c) N, key]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [localSewingLog]
  ring

/-- **The sewing cost has the sign of the drift.**  Positive drift gives strictly positive cost. -/
theorem logReflectedSewingBelow_pos {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) {N : ℕ} (hN : 2 < N) :
    0 < logReflectedSewingBelow c N := by
  have habs : |c| < 1 / 2 := by
    rw [abs_of_pos hc0]
    exact hc
  rw [logReflectedSewingBelow_eq_sum_localSewingLog habs N]
  refine Finset.sum_pos (fun p hp => localSewingLog_pos (Nat.prime_of_mem_primesBelow hp) hc0 hc) ?_
  exact ⟨2, Nat.mem_primesBelow.mpr ⟨hN, Nat.prime_two⟩⟩

/-- Negative drift gives strictly negative cost, by oddness. -/
theorem logReflectedSewingBelow_neg_of_neg {c : ℝ} (hc0 : c < 0) (hc : -(1 / 2) < c) {N : ℕ}
    (hN : 2 < N) : logReflectedSewingBelow c N < 0 := by
  have habs : |(-c)| < 1 / 2 := by
    rw [abs_of_pos (by linarith : (0:ℝ) < -c)]
    linarith
  have hpos : 0 < logReflectedSewingBelow (-c) N :=
    logReflectedSewingBelow_pos (by linarith) (by linarith) hN
  have habs2 : |c| < 1 / 2 := by
    rw [abs_of_neg hc0]
    linarith
  have hodd : logReflectedSewingBelow (-c) N = -logReflectedSewingBelow c N :=
    logReflectedSewingBelow_neg habs2 N
  rw [hodd] at hpos
  linarith

end

end RHTower
