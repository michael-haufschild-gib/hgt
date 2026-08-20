import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The critical abscissa of the random Euler observable

The random Euler observable on the boundary torus is

`𝓛(σ) = ∑_p ∑_{k ≥ 1} X_p^k p^{-kσ} / k`,

with one independent unimodular phase `X_p` per prime.  Its total second moment is

`V(σ) = ∑_p ∑_{k ≥ 1} p^{-2kσ} / k²`,

and this file proves the exact convergence threshold of `V` together with the two elementary
laws that place the threshold at `σ = 1/2` and fix the real-part normalisation.

* `summable_prime_rpow_neg_iff` — `∑_p p^{-t}` converges exactly when `t > 1`.  Above the
  threshold this is comparison with `ζ(t)`; below it, comparison with the divergent prime
  harmonic sum.  The `ζ`-comparison alone gives only the convergence half.
* `summable_eulerGradeSecondMoment_iff` — `V(σ) < ∞ ↔ σ > 1/2`.
* `summable_eulerHigherGradeSecondMoment` — the grades `k ≥ 2` are summable already for
  `σ > 1/4`, so they cannot move the threshold.
* `intervalIntegral_cos_twoPi_mul_cos_twoPi` — the circle characters have real parts with
  correlation exactly `δ_{kj}/2`; hence the real-part variance is exactly half the total second
  moment, which is the half-normalisation matching `log|ζ|` on the critical line.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ### The prime Dirichlet threshold -/

/-- Every prime is at least `2` as a real number. -/
theorem one_le_prime_cast (p : {p : ℕ // p.Prime}) : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
  exact_mod_cast p.2.one_lt.le

/-- Every prime is at least `2` as a real number. -/
theorem two_le_prime_cast (p : {p : ℕ // p.Prime}) : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by
  exact_mod_cast p.2.two_le

/-- **The prime Dirichlet threshold.**  The prime series `∑_p p^{-t}` converges exactly when
`t > 1`.  Above the threshold it is dominated by `ζ(t)`; at or below it the terms dominate
`p^{-1}`, whose prime sum diverges.  The `ζ`-comparison bounds only from above and therefore
supplies only the convergence half. -/
theorem summable_prime_rpow_neg_iff (t : ℝ) :
    (Summable fun p : {p : ℕ // p.Prime} => ((p : ℕ) : ℝ) ^ (-t)) ↔ 1 < t := by
  constructor
  · intro hs
    by_contra hle
    rw [not_lt] at hle
    have hcomp : Summable fun p : {p : ℕ // p.Prime} => (((p : ℕ) : ℝ))⁻¹ := by
      refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hs
      have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := one_le_prime_cast p
      have hkey : ((p : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ ((p : ℕ) : ℝ) ^ (-t) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      rwa [Real.rpow_neg (by positivity), Real.rpow_one] at hkey
    have hind : Summable ({p : ℕ | Nat.Prime p}.indicator fun n : ℕ => 1 / (n : ℝ)) := by
      rw [← summable_subtype_iff_indicator]
      exact hcomp.congr fun p => (one_div _).symm
    exact not_summable_one_div_on_primes hind
  · intro ht
    have h : Summable fun n : ℕ => (n : ℝ) ^ (-t) := by
      rw [Real.summable_nat_rpow]; linarith
    exact h.subtype _

/-! ### The total second moment -/

/-- The `(p, k)` block of the total second moment of the random Euler observable:
`p^{-2(k+1)σ} / (k+1)²`. -/
def eulerGradeSecondMoment (σ : ℝ) (q : {p : ℕ // p.Prime} × ℕ) : ℝ :=
  (((q.1 : ℕ) : ℝ) ^ (-(2 * σ))) ^ (q.2 + 1) / ((q.2 + 1 : ℕ) : ℝ) ^ 2

theorem eulerGradeSecondMoment_nonneg (σ : ℝ) (q : {p : ℕ // p.Prime} × ℕ) :
    0 ≤ eulerGradeSecondMoment σ q := by
  refine div_nonneg (pow_nonneg (Real.rpow_nonneg (by positivity) _) _) (by positivity)

/-- The block is the Dirichlet monomial `p^{-2kσ}` divided by `k²`, with `k = q.2 + 1`. -/
theorem eulerGradeSecondMoment_eq_rpow (σ : ℝ) (q : {p : ℕ // p.Prime} × ℕ) :
    eulerGradeSecondMoment σ q
      = ((q.1 : ℕ) : ℝ) ^ (-(2 * σ) * ((q.2 : ℝ) + 1)) / ((q.2 + 1 : ℕ) : ℝ) ^ 2 := by
  have hx : (0 : ℝ) ≤ ((q.1 : ℕ) : ℝ) := by positivity
  have h1 : ((q.2 : ℝ) + 1) = ((q.2 + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [eulerGradeSecondMoment, h1, Real.rpow_mul hx, Real.rpow_natCast]

/-- The base of the geometric grade expansion is at most `1/2` when `σ > 1/2`. -/
theorem prime_rpow_neg_le_half {σ : ℝ} (hσ : 1 / 2 < σ) (p : {p : ℕ // p.Prime}) :
    ((p : ℕ) : ℝ) ^ (-(2 * σ)) ≤ 1 / 2 := by
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) (two_le_prime_cast p)
  have h2 : (2 : ℝ) ^ (2 * σ) ≤ ((p : ℕ) : ℝ) ^ (2 * σ) :=
    Real.rpow_le_rpow (by norm_num) (two_le_prime_cast p) (by linarith)
  have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ (2 * σ) := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (show (1 : ℝ) ≤ 2 * σ by linarith)
    simpa using h
  rw [Real.rpow_neg hp0.le, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) (le_trans h1 h2)

/-- **The exact threshold of the total second moment.**  `V(σ) = ∑_p ∑_{k ≥ 1} p^{-2kσ}/k²` is
finite exactly when `σ > 1/2`. -/
theorem summable_eulerGradeSecondMoment_iff (σ : ℝ) :
    Summable (eulerGradeSecondMoment σ) ↔ 1 / 2 < σ := by
  constructor
  · intro hs
    have hslice : Summable fun p : {p : ℕ // p.Prime} => ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
      have hinj : Function.Injective fun p : {p : ℕ // p.Prime} => (p, (0 : ℕ)) :=
        fun a b hab => by simpa using congrArg Prod.fst hab
      have h := hs.comp_injective hinj
      simpa [Function.comp_def, eulerGradeSecondMoment] using h
    have := (summable_prime_rpow_neg_iff (2 * σ)).1 hslice
    linarith
  · intro hσ
    have hbase : Summable fun p : {p : ℕ // p.Prime} => ((p : ℕ) : ℝ) ^ (-(2 * σ)) :=
      (summable_prime_rpow_neg_iff (2 * σ)).2 (by linarith)
    have hgeom : Summable fun k : ℕ => ((1 : ℝ) / 2) ^ k :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hmaj : Summable fun q : {p : ℕ // p.Prime} × ℕ =>
        (((q.1 : ℕ) : ℝ) ^ (-(2 * σ))) * ((1 : ℝ) / 2) ^ q.2 :=
      hbase.mul_of_nonneg hgeom (fun p => Real.rpow_nonneg (by positivity) _)
        (fun k => by positivity)
    refine Summable.of_nonneg_of_le (eulerGradeSecondMoment_nonneg σ) (fun q => ?_) hmaj
    set y : ℝ := ((q.1 : ℕ) : ℝ) ^ (-(2 * σ)) with hy
    have hy0 : 0 ≤ y := Real.rpow_nonneg (by positivity) _
    have hyhalf : y ≤ 1 / 2 := prime_rpow_neg_le_half hσ q.1
    have hden : (1 : ℝ) ≤ ((q.2 + 1 : ℕ) : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ ((q.2 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by omega)
      nlinarith
    calc eulerGradeSecondMoment σ q = y ^ (q.2 + 1) / ((q.2 + 1 : ℕ) : ℝ) ^ 2 := rfl
      _ ≤ y ^ (q.2 + 1) := div_le_self (pow_nonneg hy0 _) hden
      _ = y * y ^ q.2 := by ring
      _ ≤ y * ((1 : ℝ) / 2) ^ q.2 := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0 hyhalf _) hy0

/-- **The grades `k ≥ 2` never reach the threshold.**  Their total second moment is already
finite for every `σ > 1/4`, so the transition at `σ = 1/2` is carried entirely by the grade-one
term. -/
theorem summable_eulerHigherGradeSecondMoment {σ : ℝ} (hσ : 1 / 4 < σ) :
    Summable fun q : {p : ℕ // p.Prime} × ℕ =>
      (((q.1 : ℕ) : ℝ) ^ (-(2 * σ))) ^ (q.2 + 2) / ((q.2 + 2 : ℕ) : ℝ) ^ 2 := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  set r : ℝ := (2 : ℝ) ^ (-(2 * σ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hr, Real.rpow_neg (by norm_num)]
    rw [inv_lt_one_iff₀]
    right
    have := Real.rpow_lt_rpow_of_exponent_lt (x := (2 : ℝ)) (by norm_num)
      (show (0 : ℝ) < 2 * σ by linarith)
    simpa using this
  have hbase : Summable fun p : {p : ℕ // p.Prime} => ((p : ℕ) : ℝ) ^ (-(4 * σ)) :=
    (summable_prime_rpow_neg_iff (4 * σ)).2 (by linarith)
  have hgeom : Summable fun k : ℕ => r ^ k := summable_geometric_of_lt_one hr0.le hr1
  have hmaj : Summable fun q : {p : ℕ // p.Prime} × ℕ =>
      (((q.1 : ℕ) : ℝ) ^ (-(4 * σ))) * r ^ q.2 :=
    hbase.mul_of_nonneg hgeom (fun p => Real.rpow_nonneg (by positivity) _)
      (fun k => by positivity)
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_) hmaj
  set y : ℝ := ((q.1 : ℕ) : ℝ) ^ (-(2 * σ)) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg (by positivity) _
  have hyr : y ≤ r := by
    rw [hy, hr, Real.rpow_neg (by positivity), Real.rpow_neg (by norm_num), ← one_div, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_le_rpow (by norm_num) (two_le_prime_cast q.1) (by linarith))
  have hysq : y ^ 2 = ((q.1 : ℕ) : ℝ) ^ (-(4 * σ)) := by
    have hx : (0 : ℝ) ≤ ((q.1 : ℕ) : ℝ) := by positivity
    rw [hy, ← Real.rpow_natCast (((q.1 : ℕ) : ℝ) ^ (-(2 * σ))) 2, ← Real.rpow_mul hx]
    congr 1
    push_cast
    ring
  have hden : (1 : ℝ) ≤ ((q.2 + 2 : ℕ) : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ ((q.2 + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by omega)
    nlinarith
  calc y ^ (q.2 + 2) / ((q.2 + 2 : ℕ) : ℝ) ^ 2 ≤ y ^ (q.2 + 2) :=
        div_le_self (pow_nonneg hy0 _) hden
    _ = y ^ 2 * y ^ q.2 := by ring
    _ ≤ y ^ 2 * r ^ q.2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0 hyr _) (by positivity)
    _ = (((q.1 : ℕ) : ℝ) ^ (-(4 * σ))) * r ^ q.2 := by rw [hysq]

/-! ### The exact real-part normalisation -/

/-- The mean of a nonconstant circle character over one period vanishes. -/
theorem intervalIntegral_cos_twoPi_intCast (m : ℤ) :
    (∫ θ in (0 : ℝ)..1, Real.cos (2 * Real.pi * (m : ℝ) * θ)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm]
    have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
    have hc : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hm'
    rw [intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1) Real.cos hc,
      integral_cos]
    have hsin : Real.sin (2 * Real.pi * (m : ℝ)) = 0 := by
      have h : (2 * Real.pi * (m : ℝ)) = ((2 * m : ℤ) : ℝ) * Real.pi := by push_cast; ring
      rw [h, Real.sin_int_mul_pi]
    simp [hsin]

/-- **Exact correlation of the real parts of the circle characters.**  For nonzero frequencies
the correlation is `1/2` on the diagonal and `0` off it; hence the real part of a mean-zero
circle observable carries exactly half of its total second moment. -/
theorem intervalIntegral_cos_twoPi_mul_cos_twoPi {k j : ℕ} (hk : k ≠ 0) (hj : j ≠ 0) :
    (∫ θ in (0 : ℝ)..1,
        Real.cos (2 * Real.pi * (k : ℝ) * θ) * Real.cos (2 * Real.pi * (j : ℝ) * θ))
      = if k = j then 1 / 2 else 0 := by
  have hprod : ∀ θ : ℝ,
      Real.cos (2 * Real.pi * (k : ℝ) * θ) * Real.cos (2 * Real.pi * (j : ℝ) * θ)
        = (Real.cos (2 * Real.pi * (((k : ℤ) - (j : ℤ) : ℤ) : ℝ) * θ)
            + Real.cos (2 * Real.pi * (((k : ℤ) + (j : ℤ) : ℤ) : ℝ) * θ)) / 2 := by
    intro θ
    have h1 : 2 * Real.pi * (((k : ℤ) - (j : ℤ) : ℤ) : ℝ) * θ
        = 2 * Real.pi * (k : ℝ) * θ - 2 * Real.pi * (j : ℝ) * θ := by push_cast; ring
    have h2 : 2 * Real.pi * (((k : ℤ) + (j : ℤ) : ℤ) : ℝ) * θ
        = 2 * Real.pi * (k : ℝ) * θ + 2 * Real.pi * (j : ℝ) * θ := by push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  have hint : ∀ m : ℤ, IntervalIntegrable
      (fun θ : ℝ => Real.cos (2 * Real.pi * (m : ℝ) * θ)) MeasureTheory.volume 0 1 := by
    intro m
    exact (Real.continuous_cos.comp (by fun_prop)).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
      (Real.cos (2 * Real.pi * (((k : ℤ) - (j : ℤ) : ℤ) : ℝ) * θ)
        + Real.cos (2 * Real.pi * (((k : ℤ) + (j : ℤ) : ℤ) : ℝ) * θ)) / 2)
      (fun θ _ => hprod θ)]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hint _) (hint _),
    intervalIntegral_cos_twoPi_intCast, intervalIntegral_cos_twoPi_intCast]
  have hsum : ((k : ℤ) + (j : ℤ)) ≠ 0 := by
    have hk' : 0 < (k : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hj' : 0 < (j : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hj
    omega
  by_cases hkj : k = j
  · have h1 : ((k : ℤ) - (j : ℤ)) = 0 := by rw [hkj]; ring
    rw [if_pos h1, if_neg hsum, if_pos hkj]
    norm_num
  · have hdiff : ((k : ℤ) - (j : ℤ)) ≠ 0 := by
      intro h
      exact hkj (by exact_mod_cast sub_eq_zero.mp h)
    rw [if_neg hdiff, if_neg hsum, if_neg hkj]
    norm_num

/-- The real part of a nonconstant circle character has mean square exactly `1/2`. -/
theorem intervalIntegral_cos_twoPi_sq {k : ℕ} (hk : k ≠ 0) :
    (∫ θ in (0 : ℝ)..1, Real.cos (2 * Real.pi * (k : ℝ) * θ) ^ 2) = 1 / 2 := by
  have h := intervalIntegral_cos_twoPi_mul_cos_twoPi hk hk
  rw [if_pos rfl] at h
  simpa [pow_two] using h

end GaloisForLFunctions.RHTower
