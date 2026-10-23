import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerPerturbationsOfTheSmoothPowerAreDecidedAtThePole

/-!
# The half-damped receiver is the logarithmic energy of the partial pole sums

Let `q(d) = d^{-1/2}` and let `k` lie in the critical Wiener algebra `Σ_j |k(j)| j^{-1/2} < ∞`.
Write `S_k(n) = Σ_{j ≤ n} k(j) j^{-1/2}` for the partial sums of the pole value `K(1/2)` and
`L_T(k) = Σ_{n ≤ T} S_k(n)²/(n+1)` for their logarithmic energy. Then the receiver of `k ⋆ q` is,
up to a bounded error, a multiple of `√L_T(k)`:

`|√E_T(k ⋆ q) − 2|Z| √L_T(k)| ≤ B`  at every cutoff `T`
(`abs_sqrt_weightPronicEnergy_dirichletConv_unit_half_sub_le`),

where `Z = lim_N (Σ_{d ≤ N} d^{-1/2} − 2√N) ≤ −1` (`halfZeta`). Hence `k ⋆ d^{-1/2}` is paid iff
`Σ_n S_k(n)²/(n+1) < ∞` (`receiverBounded_dirichletConv_unit_half_iff_summable_partialPoleSum`).

* **The smooth power at half damping.** By the Dirichlet hyperbola method at `s = ⌊√n⌋`
  (`sum_Icc_mul_div_eq_hyperbola`), `A_q(n) = 2Z√n + O(n^{1/4})` (`abs_halfRemainder_le`): the
  terms of order `n^{3/4}` cancel into `−(2/√s)(√n − s)²`, and the rest is controlled by the rate
  `0 ≤ H(N) − 2√N − Z ≤ N^{-1/2}` of the half-harmonic sums.
* **The convolution law.** `A_{k⋆q}(n) = Σ_{j ≤ n} k(j) A_q(⌊n/j⌋) + m_q A_k(n)`. The main terms add
  up to `2Z√n S_k(n)`; each dilated remainder is `O((n/j)^{1/4})` and has pronic norm `O(j^{-1/2})`
  (`pronicNorm_halfDilationRemainder_le`), so Minkowski bounds all remainders by the critical
  norm of `k`.

The receiver of a critical Wiener perturbation of the half-damped smooth power reads the kernel
only through the logarithmic mean square of its partial pole sums, a signed quantity: a nonzero pole
value makes it diverge, an absolutely `√log`-summable kernel with vanishing pole value makes it
converge, and a lacunary kernel whose partial pole sums stay at `−2^{-(R+1)}` on `[J_R, J_{R+1})`
makes it diverge.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Half-harmonic sums -/

/-- `x^{-1/2} = (√x)⁻¹`. -/
theorem rpow_neg_half_eq_inv_sqrt_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

/-- `(√(x+1))⁻¹ ≤ 2(√(x+1) − √x)`. -/
theorem inv_sqrt_succ_le_two_mul_sqrt_sub {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt (x + 1))⁻¹ ≤ 2 * (Real.sqrt (x + 1) - Real.sqrt x) := by
  have hb : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (x + 1) ^ 2 - Real.sqrt x ^ 2 = 1 := by
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt hx]; ring
  rw [inv_eq_one_div, div_le_iff₀ hb]
  nlinarith [sq_nonneg (Real.sqrt (x + 1) - Real.sqrt x)]

/-- `2(√(x+1) − √x) ≤ (√x)⁻¹` for `x > 0`. -/
theorem two_mul_sqrt_succ_sub_le_inv_sqrt {x : ℝ} (hx : 0 < x) :
    2 * (Real.sqrt (x + 1) - Real.sqrt x) ≤ (Real.sqrt x)⁻¹ := by
  have ha : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt (x + 1) ^ 2 - Real.sqrt x ^ 2 = 1 := by
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt hx.le]; ring
  rw [inv_eq_one_div, le_div_iff₀ ha]
  nlinarith [sq_nonneg (Real.sqrt (x + 1) - Real.sqrt x)]

/-- The half-harmonic sums `H(N) = Σ_{d ≤ N} d^{-1/2}`. -/
def halfHarmonic (N : ℕ) : ℝ := ∑ d ∈ Icc 1 N, (d : ℝ) ^ (-(1 / 2 : ℝ))

/-- The renormalized half-harmonic sums `g(N) = H(N) − 2√N`. -/
def halfHarmonicDefect (N : ℕ) : ℝ := halfHarmonic N - 2 * Real.sqrt N

theorem halfHarmonic_succ (N : ℕ) :
    halfHarmonic (N + 1) = halfHarmonic N + (Real.sqrt ((N : ℝ) + 1))⁻¹ := by
  rw [halfHarmonic, halfHarmonic, sum_Icc_succ_top (by omega),
    rpow_neg_half_eq_inv_sqrt_of_nonneg (x := ((N + 1 : ℕ) : ℝ)) (by positivity), Nat.cast_succ]

theorem halfHarmonicDefect_succ_le (N : ℕ) :
    halfHarmonicDefect (N + 1) ≤ halfHarmonicDefect N := by
  have h := inv_sqrt_succ_le_two_mul_sqrt_sub (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  rw [halfHarmonicDefect, halfHarmonicDefect, halfHarmonic_succ, Nat.cast_succ]
  linarith

theorem halfHarmonicDefect_sub_succ_le {N : ℕ} (hN : 1 ≤ N) :
    halfHarmonicDefect N - halfHarmonicDefect (N + 1) ≤
      (Real.sqrt N)⁻¹ - (Real.sqrt ((N : ℝ) + 1))⁻¹ := by
  have h := two_mul_sqrt_succ_sub_le_inv_sqrt (show (0 : ℝ) < N by exact_mod_cast hN)
  rw [halfHarmonicDefect, halfHarmonicDefect, halfHarmonic_succ, Nat.cast_succ]
  linarith

/-- The defect moves by at most `N^{-1/2} − M^{-1/2}` from `N` to `M`. -/
theorem halfHarmonicDefect_sub_le {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    halfHarmonicDefect N - halfHarmonicDefect M ≤ (Real.sqrt N)⁻¹ - (Real.sqrt M)⁻¹ := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    have h := halfHarmonicDefect_sub_succ_le (hN.trans hNM)
    rw [Nat.cast_succ]
    linarith

theorem halfHarmonicDefect_antitone : Antitone halfHarmonicDefect :=
  antitone_nat_of_succ_le halfHarmonicDefect_succ_le

theorem halfHarmonicDefect_one : halfHarmonicDefect 1 = -1 := by
  simp only [halfHarmonicDefect, halfHarmonic, Icc_self, sum_singleton, Nat.cast_one,
    Real.one_rpow, Real.sqrt_one]
  norm_num

theorem neg_two_le_halfHarmonicDefect (N : ℕ) : -2 ≤ halfHarmonicDefect (N + 1) := by
  have h := halfHarmonicDefect_sub_le le_rfl (show 1 ≤ N + 1 by omega)
  have h1 : 0 ≤ (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [halfHarmonicDefect_one, Nat.cast_one, Real.sqrt_one, inv_one] at h
  linarith

/-- The half-harmonic constant `Z = lim_N (H(N) − 2√N)`. -/
def halfZeta : ℝ := ⨅ N : ℕ, halfHarmonicDefect (N + 1)

theorem halfZeta_le {N : ℕ} (hN : 1 ≤ N) : halfZeta ≤ halfHarmonicDefect N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  exact ciInf_le ⟨-2, by rintro _ ⟨M, rfl⟩; exact neg_two_le_halfHarmonicDefect M⟩ M

/-- **The rate**: `H(N) − 2√N − N^{-1/2} ≤ Z ≤ H(N) − 2√N`. -/
theorem halfHarmonicDefect_sub_le_halfZeta {N : ℕ} (hN : 1 ≤ N) :
    halfHarmonicDefect N - (Real.sqrt N)⁻¹ ≤ halfZeta := by
  refine le_ciInf fun M => ?_
  rcases le_or_gt N (M + 1) with h | h
  · have h1 := halfHarmonicDefect_sub_le hN h
    have h2 : 0 ≤ (Real.sqrt ((M + 1 : ℕ) : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    linarith
  · have h1 := halfHarmonicDefect_antitone h.le
    have h2 : 0 ≤ (Real.sqrt (N : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    linarith

theorem halfZeta_le_neg_one : halfZeta ≤ -1 := by
  have h := halfZeta_le (le_refl 1)
  rwa [halfHarmonicDefect_one] at h

/-! ### The hyperbola method -/

/-- **The Dirichlet hyperbola identity.** With `s = ⌊√n⌋` and `F(N) = Σ_{d ≤ N} f(d)`,
`Σ_{d ≤ n} f(d)⌊n/d⌋ = Σ_{d ≤ s} f(d)⌊n/d⌋ + Σ_{m ≤ s} (F(⌊n/m⌋) − F(s))`: beyond `s`, `⌊n/d⌋`
counts the `m ≤ s` with `md ≤ n`. -/
theorem sum_Icc_mul_div_eq_hyperbola (f : ℕ → ℝ) (n : ℕ) :
    ∑ d ∈ Icc 1 n, f d * ((n / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 (Nat.sqrt n), f d * ((n / d : ℕ) : ℝ) +
        ∑ m ∈ Icc 1 (Nat.sqrt n),
          (∑ d ∈ Icc 1 (n / m), f d - ∑ d ∈ Icc 1 (Nat.sqrt n), f d) := by
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt n := ⟨_, rfl⟩
  rw [← hs]
  have hss : s * s ≤ n := by rw [hs]; exact Nat.sqrt_le n
  have hlt : n < (s + 1) * (s + 1) := by rw [hs]; exact Nat.lt_succ_sqrt n
  have hsn : s ≤ n := by rw [hs]; exact Nat.sqrt_le_self n
  have hsplit : Icc 1 n = Icc 1 s ∪ Ioc s n := by
    ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 s) (Ioc s n) :=
    disjoint_left.mpr fun d h1 h2 => by simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj]
  congr 1
  have hcount : ∀ d ∈ Ioc s n, f d * ((n / d : ℕ) : ℝ) =
      ∑ m ∈ Icc 1 s, if m * d ≤ n then f d else 0 := by
    intro d hd
    rw [mem_Ioc] at hd
    have hd0 : 0 < d := by omega
    have hds : n / d ≤ s := by
      have h1 : n < (s + 1) * d := lt_of_lt_of_le hlt (Nat.mul_le_mul_left (s + 1) (by omega))
      have h2 : n / d < s + 1 := (Nat.div_lt_iff_lt_mul hd0).mpr h1
      omega
    have hfil : (Icc 1 s).filter (fun m => m * d ≤ n) = Icc 1 (n / d) := by
      ext m
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, (Nat.le_div_iff_mul_le hd0).mpr h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hds⟩, (Nat.le_div_iff_mul_le hd0).mp h2⟩
    rw [← sum_filter, sum_const, nsmul_eq_mul, hfil, Nat.card_Icc, Nat.add_sub_cancel, mul_comm]
  rw [sum_congr rfl hcount, sum_comm]
  refine sum_congr rfl fun m hm => ?_
  rw [mem_Icc] at hm
  have hm0 : 0 < m := hm.1
  have hsm : s ≤ n / m := (Nat.le_div_iff_mul_le hm0).mpr ((Nat.mul_le_mul_left s hm.2).trans hss)
  rw [← sum_filter]
  have hfil : (Ioc s n).filter (fun d => m * d ≤ n) = Ioc s (n / m) := by
    ext d
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, (Nat.le_div_iff_mul_le hm0).mpr (by rw [Nat.mul_comm]; exact h2)⟩
    · rintro ⟨h1, h2⟩
      have h3 := (Nat.le_div_iff_mul_le hm0).mp h2
      exact ⟨⟨h1, h2.trans (Nat.div_le_self n m)⟩, by rw [Nat.mul_comm]; exact h3⟩
  rw [hfil]
  have hunion : Icc 1 (n / m) = Icc 1 s ∪ Ioc s (n / m) := by
    ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  rw [hunion, sum_union (disjoint_left.mpr fun d h1 h2 => by
    simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
  ring

/-! ### The prefix of the half-damped smooth power -/

/-- The remainder `R(N) = A_q(N) − 2Z√N` of the half-damped smooth power `q(d) = d^{-1/2}`. -/
def halfRemainder (N : ℕ) : ℝ :=
  weightCenteredPrefix (dampedSignWeight unitSign (1 / 2))
    (∑' d : ℕ, dampedSignWeight unitSign (1 / 2) d / d) N - 2 * halfZeta * Real.sqrt N

/-- **The half-damped smooth power has prefix `2Z√n + O(n^{1/4})`**: `|R(n)| ≤ 14 ⌊√n⌋^{1/2}`. -/
theorem abs_halfRemainder_le (n : ℕ) : |halfRemainder n| ≤ 14 * Real.sqrt (Nat.sqrt n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [halfRemainder, weightCenteredPrefix_zero]
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt n := ⟨_, rfl⟩
  rw [← hs]
  have hs1 : 1 ≤ s := by rw [hs]; exact Nat.sqrt_pos.mpr hn
  have hss : s * s ≤ n := by rw [hs]; exact Nat.sqrt_le n
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  obtain ⟨t, ht⟩ : ∃ t, t = Real.sqrt (s : ℝ) := ⟨_, rfl⟩
  rw [← ht]
  have ht1 : 1 ≤ t := by rw [ht]; exact Real.one_le_sqrt.mpr hsR
  have ht0 : 0 < t := by linarith
  have hts : t ^ 2 = s := by rw [ht]; exact Real.sq_sqrt (by positivity)
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (n : ℝ) := ⟨_, rfl⟩
  have hr2 : r ^ 2 = n := by rw [hr]; exact Real.sq_sqrt (Nat.cast_nonneg n)
  have hsr : (s : ℝ) ≤ r := by rw [hs, hr]; exact Real.nat_sqrt_le_real_sqrt
  have hrs : r < s + 1 := by rw [hs, hr]; exact Real.real_sqrt_lt_nat_sqrt_succ
  have hq : ∀ d : ℕ, dampedSignWeight unitSign (1 / 2) d = (d : ℝ) ^ (-(1 / 2 : ℝ)) := fun d => by
    simp only [dampedSignWeight, unitSign, one_mul]
  -- the prefix as a floor sum
  have hA : weightCenteredPrefix (dampedSignWeight unitSign (1 / 2))
      (∑' d : ℕ, dampedSignWeight unitSign (1 / 2) d / d) n =
      ∑ d ∈ Icc 1 n, (d : ℝ) ^ (-(1 / 2 : ℝ)) * ((n / d : ℕ) : ℝ) -
        (∑' d : ℕ, dampedSignWeight unitSign (1 / 2) d / d) * n := by
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor]
    simp only [hq]
  -- the hyperbola split
  have hhyp : ∑ d ∈ Icc 1 n, (d : ℝ) ^ (-(1 / 2 : ℝ)) * ((n / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 s, (d : ℝ) ^ (-(1 / 2 : ℝ)) * ((n / d : ℕ) : ℝ) +
        (∑ m ∈ Icc 1 s, halfHarmonic (n / m) - s * halfHarmonic s) := by
    have h := sum_Icc_mul_div_eq_hyperbola (fun d => (d : ℝ) ^ (-(1 / 2 : ℝ))) n
    rw [← hs, sum_sub_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at h
    exact h
  -- the head below `s`
  obtain ⟨E1, hE1⟩ : ∃ E1, E1 = ∑ d ∈ Icc 1 s,
      (d : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) / d - ((n / d : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hhead : ∑ d ∈ Icc 1 s, (d : ℝ) ^ (-(1 / 2 : ℝ)) * ((n / d : ℕ) : ℝ) =
      n * ∑ d ∈ Icc 1 s, (d : ℝ) ^ (-(1 / 2 : ℝ) - 1) - E1 := by
    rw [hE1, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    rw [Real.rpow_sub_one hd0.ne']
    ring
  have hE1_0 : 0 ≤ E1 := by
    rw [hE1]
    exact sum_nonneg fun d _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      (sub_nonneg.mpr Nat.cast_div_le)
  have hE1_le : E1 ≤ halfHarmonic s := by
    rw [hE1, halfHarmonic]
    refine sum_le_sum fun d hd => ?_
    have hd1 := (mem_Icc.mp hd).1
    have h1 := (abs_le.mp (abs_natDiv_sub_div_le n d (by omega))).1
    exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg d) _) (by linarith)
  -- the mean and its tail beyond `s`
  have hsum := summable_unit_weight (ε := 1 / 2) (by norm_num)
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = ∑' k : ℕ, ((s : ℝ) + 1 + (k : ℝ)) ^ (-(1 / 2 : ℝ) - 1) := ⟨_, rfl⟩
  have hmean : ∑' d : ℕ, dampedSignWeight unitSign (1 / 2) d / d =
      ∑ d ∈ Icc 1 s, (d : ℝ) ^ (-(1 / 2 : ℝ) - 1) + τ := by
    rw [← hsum.sum_add_tsum_nat_add (s + 1),
      sum_range_succ_eq_sum_Icc_one (f := fun d : ℕ => dampedSignWeight unitSign (1 / 2) d / d)
        (by simp) s, hτ]
    congr 1
    · refine sum_congr rfl fun d hd => ?_
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      rw [hq, Real.rpow_sub_one hd0.ne']
    · refine tsum_congr fun k => ?_
      have hcast : ((k + (s + 1) : ℕ) : ℝ) = (s : ℝ) + 1 + k := by push_cast; ring
      have hk0 : (0 : ℝ) < (s : ℝ) + 1 + k := by positivity
      rw [hq, hcast, Real.rpow_sub_one hk0.ne']
  have hτle : τ ≤ 2 / t := by
    have h := HTGeometry.tsum_shift_rpow_le (q := -(1 / 2 : ℝ)) (by norm_num) hs1
    rw [← hτ, rpow_neg_half_eq_inv_sqrt_of_nonneg (Nat.cast_nonneg s), ← ht] at h
    calc τ ≤ t⁻¹ / -(-(1 / 2 : ℝ)) := h
      _ = 2 / t := by ring
  have hτge : 2 / Real.sqrt ((s : ℝ) + 1) ≤ τ := by
    have h := HTGeometry.tsum_shift_rpow_ge (q := -(1 / 2 : ℝ)) (by norm_num) s
    rw [← hτ, rpow_neg_half_eq_inv_sqrt_of_nonneg (x := (s : ℝ) + 1) (by positivity)] at h
    calc 2 / Real.sqrt ((s : ℝ) + 1) = (Real.sqrt ((s : ℝ) + 1))⁻¹ / -(-(1 / 2 : ℝ)) := by ring
      _ ≤ τ := h
  have hβ : 2 / t - τ ≤ 1 / t ^ 3 := by
    have hb : t ≤ Real.sqrt ((s : ℝ) + 1) := by rw [ht]; exact Real.sqrt_le_sqrt (by linarith)
    have hb0 : 0 < Real.sqrt ((s : ℝ) + 1) := by linarith
    have hstep := two_mul_sqrt_succ_sub_le_inv_sqrt (show (0 : ℝ) < s by linarith)
    rw [← ht] at hstep
    have h2 : 2 * (Real.sqrt ((s : ℝ) + 1) - t) * t ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hstep ht0.le
      rwa [inv_mul_cancel₀ ht0.ne'] at h
    have h1 : 2 / t - 2 / Real.sqrt ((s : ℝ) + 1) ≤ 1 / t ^ 3 := by
      rw [div_sub_div _ _ ht0.ne' hb0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg t),
        mul_nonneg ht0.le (sub_nonneg.mpr hb)]
    linarith
  -- the long sum `Σ_{m ≤ s} H(⌊n/m⌋)`
  obtain ⟨E3, hE3⟩ : ∃ E3, E3 = ∑ m ∈ Icc 1 s,
      (halfHarmonic (n / m) - 2 * r * (m : ℝ) ^ (-(1 / 2 : ℝ)) - halfZeta) := ⟨_, rfl⟩
  have hsumH : ∑ m ∈ Icc 1 s, halfHarmonic (n / m) =
      E3 + 2 * r * halfHarmonic s + s * halfZeta := by
    have h2 : 2 * r * halfHarmonic s = ∑ m ∈ Icc 1 s, 2 * r * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [halfHarmonic, mul_sum]
    have h3 : (s : ℝ) * halfZeta = ∑ _m ∈ Icc 1 s, halfZeta := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    rw [h2, h3, hE3, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  have hE3_le : |E3| ≤ 2 * t := by
    have hterm : ∀ m ∈ Icc 1 s,
        |halfHarmonic (n / m) - 2 * r * (m : ℝ) ^ (-(1 / 2 : ℝ)) - halfZeta| ≤ 2 / t := by
      intro m hm
      obtain ⟨hm1, hms⟩ := mem_Icc.mp hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      have hsN : s ≤ n / m :=
        (Nat.le_div_iff_mul_le hm1).mpr ((Nat.mul_le_mul_left s hms).trans hss)
      have hN1 : 1 ≤ n / m := hs1.trans hsN
      have hNR : (0 : ℝ) < ((n / m : ℕ) : ℝ) := by exact_mod_cast hN1
      have hinv : (Real.sqrt ((n / m : ℕ) : ℝ))⁻¹ ≤ 1 / t := by
        rw [one_div, ht]
        exact inv_anti₀ (Real.sqrt_pos.mpr (by linarith))
          (Real.sqrt_le_sqrt (by exact_mod_cast hsN))
      have hg1 := halfZeta_le hN1
      have hg2 := halfHarmonicDefect_sub_le_halfZeta hN1
      rw [halfHarmonicDefect] at hg1 hg2
      have hrm : 2 * r * (m : ℝ) ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt ((n : ℝ) / m) := by
        rw [mul_assoc, rpow_neg_half_eq_inv_sqrt_of_nonneg hm0.le, hr, Real.sqrt_div' _ hm0.le,
          div_eq_mul_inv]
      have hle : ((n / m : ℕ) : ℝ) ≤ (n : ℝ) / m := Nat.cast_div_le
      have hlt : (n : ℝ) / m - ((n / m : ℕ) : ℝ) ≤ 1 := by
        have := (abs_le.mp (abs_natDiv_sub_div_le n m hm1)).1
        linarith
      have hf1 : Real.sqrt ((n / m : ℕ) : ℝ) ≤ Real.sqrt ((n : ℝ) / m) := Real.sqrt_le_sqrt hle
      have hf2 : Real.sqrt ((n : ℝ) / m) - Real.sqrt ((n / m : ℕ) : ℝ) ≤
          (Real.sqrt ((n / m : ℕ) : ℝ))⁻¹ := by
        have hsq1 := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) / m by positivity)
        have hsq2 := Real.sq_sqrt hNR.le
        have hpos : 0 < Real.sqrt ((n / m : ℕ) : ℝ) := Real.sqrt_pos.mpr hNR
        rw [inv_eq_one_div, le_div_iff₀ hpos]
        nlinarith [mul_nonneg (sub_nonneg.mpr hf1) (Real.sqrt_nonneg ((n : ℝ) / m))]
      have h2t : 2 / t = 2 * (1 / t) := by ring
      rw [hrm, abs_le]
      constructor <;> linarith
    rw [hE3]
    calc |∑ m ∈ Icc 1 s, (halfHarmonic (n / m) - 2 * r * (m : ℝ) ^ (-(1 / 2 : ℝ)) - halfZeta)|
        ≤ ∑ m ∈ Icc 1 s, |halfHarmonic (n / m) - 2 * r * (m : ℝ) ^ (-(1 / 2 : ℝ)) - halfZeta| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ Icc 1 s, 2 / t := sum_le_sum hterm
      _ = 2 * t := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← hts]
          field_simp
  -- the value at `s`
  have hHs1 := halfZeta_le hs1
  have hHs2 := halfHarmonicDefect_sub_le_halfZeta hs1
  rw [halfHarmonicDefect, ← ht] at hHs1 hHs2
  -- the exact expansion
  have hAexp : weightCenteredPrefix (dampedSignWeight unitSign (1 / 2))
      (∑' d : ℕ, dampedSignWeight unitSign (1 / 2) d / d) n =
      -E1 + E3 + (2 * r - s) * halfHarmonic s + s * halfZeta - τ * n := by
    linear_combination hA + hhyp + hhead - (n : ℝ) * hmean + hsumH
  have hfinal : weightCenteredPrefix (dampedSignWeight unitSign (1 / 2))
      (∑' d : ℕ, dampedSignWeight unitSign (1 / 2) d / d) n - 2 * halfZeta * r =
      -(2 / t * (r - s) ^ 2) + r ^ 2 * (2 / t - τ) - E1 + E3 +
        (2 * r - s) * (halfHarmonic s - 2 * t - halfZeta) := by
    rw [hAexp, ← hr2, ← hts]
    field_simp
    ring
  clear hA hhyp hhead hmean hsumH hAexp hE1 hE3 hτ hsum hq hτge
  -- the five error terms
  have hP1 : 0 ≤ 2 / t * (r - s) ^ 2 ∧ 2 / t * (r - s) ^ 2 ≤ 2 := by
    have h2t : 2 / t ≤ 2 := by rw [div_le_iff₀ ht0]; linarith only [ht1]
    have h0 : 0 ≤ r - s := by linarith only [hsr]
    have h1 : r - s ≤ 1 := by linarith only [hrs]
    have hsq : (r - s) ^ 2 ≤ 1 := by
      rw [sq]; exact (mul_le_mul h1 h1 h0 zero_le_one).trans (le_of_eq (one_mul 1))
    exact ⟨mul_nonneg (div_nonneg (by norm_num) ht0.le) (sq_nonneg _),
      (mul_le_mul h2t hsq (sq_nonneg _) (by norm_num)).trans (le_of_eq (mul_one 2))⟩
  have hβ0 : 0 ≤ 2 / t - τ := sub_nonneg.mpr hτle
  have hr4 : r ^ 2 ≤ 4 * t ^ 4 := by
    have h1 : r ≤ 2 * t ^ 2 := by linarith only [hrs, hsR, hts]
    have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
    calc r ^ 2 = r * r := sq r
      _ ≤ (2 * t ^ 2) * (2 * t ^ 2) := mul_le_mul h1 h1 hr0 (by positivity)
      _ = 4 * t ^ 4 := by ring
  have hP2 : 0 ≤ r ^ 2 * (2 / t - τ) ∧ r ^ 2 * (2 / t - τ) ≤ 4 * t := by
    refine ⟨mul_nonneg (sq_nonneg r) hβ0, ?_⟩
    calc r ^ 2 * (2 / t - τ) ≤ (4 * t ^ 4) * (1 / t ^ 3) :=
          mul_le_mul hr4 hβ hβ0 (by positivity)
      _ = 4 * t := by field_simp
  have hγ0 : 0 ≤ halfHarmonic s - 2 * t - halfZeta := by linarith only [hHs1]
  have hγ1 : halfHarmonic s - 2 * t - halfZeta ≤ t⁻¹ := by linarith only [hHs2]
  have hP5 : 0 ≤ (2 * r - s) * (halfHarmonic s - 2 * t - halfZeta) ∧
      (2 * r - s) * (halfHarmonic s - 2 * t - halfZeta) ≤ 4 * t := by
    have h1 : 0 ≤ 2 * r - s := by linarith only [hsr, (Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
    have h2 : 2 * r - s ≤ 4 * t ^ 2 := by linarith only [hrs, hsR, hts]
    refine ⟨mul_nonneg h1 hγ0, ?_⟩
    calc (2 * r - s) * (halfHarmonic s - 2 * t - halfZeta) ≤ (4 * t ^ 2) * t⁻¹ :=
          mul_le_mul h2 hγ1 hγ0 (by positivity)
      _ = 4 * t := by field_simp
  have hZ1 := halfZeta_le_neg_one
  have htinv : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
  have hE1t : E1 ≤ 2 * t := by linarith only [hE1_le, hHs2, hZ1, htinv]
  have hE3' := abs_le.mp hE3_le
  rw [halfRemainder, ← hr, hfinal, abs_le]
  constructor <;> linarith only [hP1.1, hP1.2, hP2.1, hP2.2, hP5.1, hP5.2, hE1_0, hE1t, hE3'.1,
    hE3'.2, ht1]

/-- `|R(N)| ≤ 14 N^{1/4}`. -/
theorem abs_halfRemainder_le_sqrt_sqrt (N : ℕ) :
    |halfRemainder N| ≤ 14 * Real.sqrt (Real.sqrt N) :=
  (abs_halfRemainder_le N).trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt Real.nat_sqrt_le_real_sqrt) (by norm_num))

/-! ### Convolutions with the half-damped smooth power -/

/-- The partial pole sums `S_k(n) = Σ_{j ≤ n} k(j) j^{-1/2}`. -/
def partialPoleSum (k : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ Icc 1 n, k j * (j : ℝ) ^ (-(1 / 2 : ℝ))

/-- The logarithmic energy of the partial pole sums, `L_T(k) = Σ_{n ≤ T} S_k(n)²/(n+1)`. -/
def poleSumEnergy (k : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, partialPoleSum k n ^ 2 / ((n : ℝ) + 1)

/-- The dilated remainder `R(⌊n/j⌋) − 2Z(√(n/j) − √⌊n/j⌋)`. -/
def halfDilationRemainder (n j : ℕ) : ℝ :=
  halfRemainder (n / j) -
    2 * halfZeta * (Real.sqrt n * (j : ℝ) ^ (-(1 / 2 : ℝ)) - Real.sqrt ((n / j : ℕ) : ℝ))

/-- **The prefix of `k ⋆ d^{-1/2}`**: `A_{k⋆q}(n) = 2Z√n S_k(n) + Σ_{j ≤ n} k(j) R_j(n) + m_q A_k(n)`. -/
theorem weightCenteredPrefix_dirichletConv_unit_half (k : ℕ → ℝ) (mk : ℝ) (n : ℕ) :
    weightCenteredPrefix (RHTower.dirichletConv k (dampedSignWeight unitSign (1 / 2)))
        (mk * ∑' d : ℕ, dampedSignWeight unitSign (1 / 2) d / d) n =
      2 * halfZeta * Real.sqrt n * partialPoleSum k n +
        ∑ j ∈ Icc 1 n, k j * halfDilationRemainder n j +
          (∑' d : ℕ, dampedSignWeight unitSign (1 / 2) d / d) * weightCenteredPrefix k mk n := by
  rw [weightCenteredPrefix_dirichletConv, partialPoleSum, mul_sum, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  simp only [halfDilationRemainder, halfRemainder]
  ring

/-- **Each dilated remainder has pronic norm `O(j^{-1/2})`**: it is `O((n/j)^{1/4})` beyond `j`. -/
theorem pronicNorm_halfDilationRemainder_le {j : ℕ} (hj : 1 ≤ j) (T : ℕ) :
    pronicNorm (fun n => if j ≤ n then halfDilationRemainder n j else 0) T ≤
      Real.sqrt 3 * (14 + 2 * |halfZeta|) * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
  set C := 14 + 2 * |halfZeta| with hC
  have hC0 : 0 ≤ C := by positivity
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  -- pointwise: `|R_j(n)| ≤ C (n/j)^{1/4}` beyond `j`
  have hpt : ∀ n : ℕ, j ≤ n →
      |halfDilationRemainder n j| ≤ C * Real.sqrt (Real.sqrt ((n : ℝ) / j)) := by
    intro n hjn
    have hN1 : 1 ≤ n / j := (Nat.le_div_iff_mul_le hj).mpr (by omega)
    have hNR : (1 : ℝ) ≤ ((n / j : ℕ) : ℝ) := by exact_mod_cast hN1
    have hle : ((n / j : ℕ) : ℝ) ≤ (n : ℝ) / j := Nat.cast_div_le
    have hw1 : 1 ≤ Real.sqrt (Real.sqrt ((n : ℝ) / j)) :=
      Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (hNR.trans hle))
    have hR := abs_halfRemainder_le_sqrt_sqrt (n / j)
    have hRw : Real.sqrt (Real.sqrt ((n / j : ℕ) : ℝ)) ≤ Real.sqrt (Real.sqrt ((n : ℝ) / j)) :=
      Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hle)
    have hrm : Real.sqrt n * (j : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt ((n : ℝ) / j) := by
      rw [rpow_neg_half_eq_inv_sqrt_of_nonneg hj0.le, Real.sqrt_div' _ hj0.le, div_eq_mul_inv]
    have hf1 : Real.sqrt ((n / j : ℕ) : ℝ) ≤ Real.sqrt ((n : ℝ) / j) := Real.sqrt_le_sqrt hle
    have hf2 : Real.sqrt ((n : ℝ) / j) - Real.sqrt ((n / j : ℕ) : ℝ) ≤ 1 := by
      have hlt : (n : ℝ) / j - ((n / j : ℕ) : ℝ) ≤ 1 := by
        have := (abs_le.mp (abs_natDiv_sub_div_le n j (by omega))).1
        linarith
      have hsq1 := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) / j by positivity)
      have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ ((n / j : ℕ) : ℝ) by positivity)
      have hb1 : 1 ≤ Real.sqrt ((n / j : ℕ) : ℝ) := Real.one_le_sqrt.mpr hNR
      nlinarith [mul_nonneg (sub_nonneg.mpr hf1)
        (show (0 : ℝ) ≤ Real.sqrt ((n : ℝ) / j) + Real.sqrt ((n / j : ℕ) : ℝ) - 2 by linarith)]
    rw [halfDilationRemainder, hrm]
    calc |halfRemainder (n / j) -
          2 * halfZeta * (Real.sqrt ((n : ℝ) / j) - Real.sqrt ((n / j : ℕ) : ℝ))|
        ≤ |halfRemainder (n / j)| +
            |2 * halfZeta| * |Real.sqrt ((n : ℝ) / j) - Real.sqrt ((n / j : ℕ) : ℝ)| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ 14 * Real.sqrt (Real.sqrt ((n : ℝ) / j)) +
            2 * |halfZeta| * Real.sqrt (Real.sqrt ((n : ℝ) / j)) := by
          rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
            abs_of_nonneg (sub_nonneg.mpr hf1)]
          gcongr
          · linarith
          · linarith
      _ = C * Real.sqrt (Real.sqrt ((n : ℝ) / j)) := by rw [hC]; ring
  -- the energy of the row
  have hsum : ∑ n ∈ Icc 1 T, (if j ≤ n then halfDilationRemainder n j else 0) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1)) ≤ 3 * C ^ 2 * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
    have hfil : ∑ n ∈ Icc 1 T, (if j ≤ n then halfDilationRemainder n j else 0) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) =
        ∑ n ∈ Icc j T, halfDilationRemainder n j ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [← sum_filter_add_sum_filter_not (Icc 1 T) (fun n => j ≤ n)]
      have h1 : ∑ n ∈ (Icc 1 T).filter (fun n => ¬ j ≤ n),
          (if j ≤ n then halfDilationRemainder n j else 0) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) = 0 :=
        sum_eq_zero fun n hn => by rw [if_neg (mem_filter.mp hn).2]; simp
      have h2 : (Icc 1 T).filter (fun n => j ≤ n) = Icc j T := by
        ext n; simp only [mem_filter, mem_Icc]; omega
      rw [h1, add_zero, h2]
      exact sum_congr rfl fun n hn => by rw [if_pos (mem_Icc.mp hn).1]
    rw [hfil]
    have hjε : 0 ≤ (j : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hj0.le _
    calc ∑ n ∈ Icc j T, halfDilationRemainder n j ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ∑ n ∈ Icc j T, C ^ 2 * (j : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) := by
          refine sum_le_sum fun n hn => ?_
          have hjn := (mem_Icc.mp hn).1
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hj.trans hjn
          have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
          have hW : Real.sqrt (Real.sqrt ((n : ℝ) / j)) ^ 2 =
              Real.sqrt n * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
            rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sqrt_div' _ hj0.le,
              rpow_neg_half_eq_inv_sqrt_of_nonneg hj0.le, div_eq_mul_inv]
          have hsq : halfDilationRemainder n j ^ 2 ≤
              C ^ 2 * (Real.sqrt n * (j : ℝ) ^ (-(1 / 2 : ℝ))) := by
            rw [← hW, ← mul_pow, ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hpt n hjn) 2
          have hsqrt : (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) * ((n : ℝ) * n) = Real.sqrt n := by
            rw [← mul_assoc, ← Real.rpow_add_one hn0.ne', ← Real.rpow_add_one hn0.ne',
              Real.sqrt_eq_rpow]
            norm_num
          rw [div_le_iff₀ hpr]
          calc halfDilationRemainder n j ^ 2 ≤ C ^ 2 * (Real.sqrt n * (j : ℝ) ^ (-(1 / 2 : ℝ))) :=
                hsq
            _ = C ^ 2 * (j : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) *
                  ((n : ℝ) * n) := by rw [← hsqrt]; ring
            _ ≤ C ^ 2 * (j : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) *
                  ((n : ℝ) * ((n : ℝ) + 1)) := by gcongr; linarith
      _ = C ^ 2 * (j : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ n ∈ Icc j T, (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) := by
          rw [mul_sum]
      _ ≤ C ^ 2 * (j : ℝ) ^ (-(1 / 2 : ℝ)) * ((1 + 1 / (1 / 2)) * (j : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_one_sub_le (by norm_num) hj T)
            (mul_nonneg (sq_nonneg C) hjε)
      _ = 3 * C ^ 2 * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by norm_num; ring
  rw [pronicNorm]
  calc Real.sqrt (∑ n ∈ Icc 1 T, (if j ≤ n then halfDilationRemainder n j else 0) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1))) ≤ Real.sqrt (3 * C ^ 2 * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 3 * C * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hC0,
          Real.sqrt_sq (Real.rpow_nonneg hj0.le _)]

/-- **The half-damped receiver is the logarithmic energy of the partial pole sums.** For a kernel
of the critical Wiener algebra there is `B` with
`|√E_T(k ⋆ d^{-1/2}) − 2|Z| √L_T(k)| ≤ B` at every cutoff `T`, `L_T(k) = Σ_{n ≤ T} S_k(n)²/(n+1)`. -/
theorem abs_sqrt_weightPronicEnergy_dirichletConv_unit_half_sub_le {k : ℕ → ℝ}
    (hk : CriticalWiener k) :
    ∃ B : ℝ, ∀ T : ℕ,
      |Real.sqrt (weightPronicEnergy (RHTower.dirichletConv k (dampedSignWeight unitSign (1 / 2)))
          (∑' d : ℕ, RHTower.dirichletConv k (dampedSignWeight unitSign (1 / 2)) d / d) T) -
        2 * |halfZeta| * Real.sqrt (poleSumEnergy k T)| ≤ B := by
  have hW : Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))) := hk
  set G := ∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) with hG
  set mq := ∑' d : ℕ, dampedSignWeight unitSign (1 / 2) d / d with hmq
  set mk := ∑' j : ℕ, k j / j with hmk
  set C := 14 + 2 * |halfZeta| with hC
  refine ⟨Real.sqrt 3 * C * G + |mq| * ((Real.sqrt 2 + 1) * G), fun T => ?_⟩
  have hq := summable_unit_weight (ε := 1 / 2) (by norm_num)
  have hmean : ∑' d : ℕ, RHTower.dirichletConv k (dampedSignWeight unitSign (1 / 2)) d / d =
      mk * mq :=
    (hasSum_dirichletConv_div hk.summable_abs_div.of_abs.hasSum hq.hasSum hk.summable_abs_div
      hq.abs).tsum_eq
  rw [hmean, weightPronicEnergy_eq_sq_pronicNorm, Real.sqrt_sq (pronicNorm_nonneg _ _)]
  -- the decomposition on the cutoff
  have hrep : ∀ n ∈ Icc 1 T,
      weightCenteredPrefix (RHTower.dirichletConv k (dampedSignWeight unitSign (1 / 2)))
        (mk * mq) n =
      2 * halfZeta * Real.sqrt n * partialPoleSum k n +
        (∑ j ∈ Icc 1 T, k j * (if j ≤ n then halfDilationRemainder n j else 0) +
          mq * weightCenteredPrefix k mk n) := by
    intro n hn
    have hnT := (mem_Icc.mp hn).2
    have hsum : ∑ j ∈ Icc 1 T, k j * (if j ≤ n then halfDilationRemainder n j else 0) =
        ∑ j ∈ Icc 1 n, k j * halfDilationRemainder n j := by
      simp_rw [mul_ite, mul_zero]
      rw [← sum_filter]
      congr 1
      ext j; simp only [mem_filter, mem_Icc]; omega
    rw [hsum, weightCenteredPrefix_dirichletConv_unit_half k mk n]
    ring
  -- the remainder is bounded by the critical norm
  have hρ : pronicNorm (fun n => ∑ j ∈ Icc 1 T, k j * (if j ≤ n then halfDilationRemainder n j else 0) +
      mq * weightCenteredPrefix k mk n) T ≤
      Real.sqrt 3 * C * G + |mq| * ((Real.sqrt 2 + 1) * G) := by
    refine (pronicNorm_add_le _ _ T).trans (add_le_add ?_ ?_)
    · refine (pronicNorm_sum_le (Icc 1 T)
        (fun j n => k j * (if j ≤ n then halfDilationRemainder n j else 0)) T).trans ?_
      calc ∑ j ∈ Icc 1 T, pronicNorm
            (fun n => k j * (if j ≤ n then halfDilationRemainder n j else 0)) T
          = ∑ j ∈ Icc 1 T, |k j| *
              pronicNorm (fun n => if j ≤ n then halfDilationRemainder n j else 0) T :=
            sum_congr rfl fun j _ => pronicNorm_smul _ _ _
        _ ≤ ∑ j ∈ Icc 1 T, |k j| * (Real.sqrt 3 * C * (j : ℝ) ^ (-(1 / 2 : ℝ))) :=
            sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
              (pronicNorm_halfDilationRemainder_le (mem_Icc.mp hj).1 T) (abs_nonneg _)
        _ = Real.sqrt 3 * C * ∑ j ∈ Icc 1 T, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
            rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
        _ ≤ Real.sqrt 3 * C * G :=
            mul_le_mul_of_nonneg_left (hW.sum_le_tsum _ fun j _ => by positivity) (by positivity)
    · rw [pronicNorm_smul]
      exact mul_le_mul_of_nonneg_left (pronicNorm_weightCenteredPrefix_le_critical hk T)
        (abs_nonneg _)
  -- the main term is the logarithmic energy of the partial pole sums
  have hmain : pronicNorm (fun n => 2 * halfZeta * Real.sqrt n * partialPoleSum k n) T =
      2 * |halfZeta| * Real.sqrt (poleSumEnergy k T) := by
    rw [pronicNorm, poleSumEnergy]
    have h : ∑ n ∈ Icc 1 T, (2 * halfZeta * Real.sqrt n * partialPoleSum k n) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) =
        (2 * |halfZeta|) ^ 2 * ∑ n ∈ Icc 1 T, partialPoleSum k n ^ 2 / ((n : ℝ) + 1) := by
      rw [mul_sum]
      refine sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hn0.le, sq_abs]
      field_simp
    rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have h1 := pronicNorm_add_le (fun n => 2 * halfZeta * Real.sqrt n * partialPoleSum k n)
    (fun n => ∑ j ∈ Icc 1 T, k j * (if j ≤ n then halfDilationRemainder n j else 0) +
      mq * weightCenteredPrefix k mk n) T
  rw [← pronicNorm_congr hrep] at h1
  have h2 : pronicNorm (fun n => 2 * halfZeta * Real.sqrt n * partialPoleSum k n) T ≤
      pronicNorm (weightCenteredPrefix
        (RHTower.dirichletConv k (dampedSignWeight unitSign (1 / 2))) (mk * mq)) T +
      pronicNorm (fun n => ∑ j ∈ Icc 1 T, k j * (if j ≤ n then halfDilationRemainder n j else 0) +
        mq * weightCenteredPrefix k mk n) T := by
    have h := pronicNorm_add_le (weightCenteredPrefix
        (RHTower.dirichletConv k (dampedSignWeight unitSign (1 / 2))) (mk * mq))
      (fun n => (-1) * (∑ j ∈ Icc 1 T, k j * (if j ≤ n then halfDilationRemainder n j else 0) +
        mq * weightCenteredPrefix k mk n)) T
    rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at h
    refine le_of_eq_of_le (pronicNorm_congr fun n hn => ?_) h
    rw [hrep n hn]
    ring
  rw [hmain] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- **The half-damped criterion on the critical Wiener algebra.** For `Σ_j |k(j)| j^{-1/2} < ∞`,
the receiver of `k ⋆ d^{-1/2}` is bounded if and only if the partial pole sums
`S_k(n) = Σ_{j ≤ n} k(j) j^{-1/2}` satisfy `Σ_n S_k(n)²/(n+1) < ∞`. -/
theorem receiverBounded_dirichletConv_unit_half_iff_summable_partialPoleSum {k : ℕ → ℝ}
    (hk : CriticalWiener k) :
    ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign (1 / 2))) ↔
      Summable (fun n : ℕ => partialPoleSum k n ^ 2 / ((n : ℝ) + 1)) := by
  obtain ⟨B, hB⟩ := abs_sqrt_weightPronicEnergy_dirichletConv_unit_half_sub_le hk
  set c := RHTower.dirichletConv k (dampedSignWeight unitSign (1 / 2)) with hc
  have hZ : 1 ≤ |halfZeta| := by
    have := halfZeta_le_neg_one
    rw [abs_of_neg (by linarith)]; linarith
  have hterm0 : ∀ n : ℕ, 0 ≤ partialPoleSum k n ^ 2 / ((n : ℝ) + 1) := fun n => by positivity
  have hrange : ∀ T : ℕ, ∑ n ∈ range (T + 1), partialPoleSum k n ^ 2 / ((n : ℝ) + 1) =
      poleSumEnergy k T := fun T =>
    sum_range_succ_eq_sum_Icc_one (by simp [partialPoleSum]) T
  have hL0 : ∀ T : ℕ, 0 ≤ poleSumEnergy k T := fun T => sum_nonneg fun n _ => hterm0 n
  have hE0 : ∀ T : ℕ, 0 ≤ weightPronicEnergy c (∑' d : ℕ, c d / d) T :=
    fun T => sum_nonneg fun n _ => by positivity
  constructor
  · rintro ⟨E, hE⟩
    refine summable_of_sum_range_le hterm0 (c := ((Real.sqrt E + B) / 2) ^ 2) fun T => ?_
    have h1 := (abs_le.mp (hB T)).1
    have h2 : Real.sqrt (weightPronicEnergy c (∑' d : ℕ, c d / d) T) ≤ Real.sqrt E :=
      Real.sqrt_le_sqrt (hE T)
    have h3 : 2 * Real.sqrt (poleSumEnergy k T) ≤ Real.sqrt E + B := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hZ) (Real.sqrt_nonneg (poleSumEnergy k T))]
    have h4 : Real.sqrt (poleSumEnergy k T) ≤ (Real.sqrt E + B) / 2 := by linarith
    calc ∑ n ∈ range T, partialPoleSum k n ^ 2 / ((n : ℝ) + 1)
        ≤ ∑ n ∈ range (T + 1), partialPoleSum k n ^ 2 / ((n : ℝ) + 1) :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.le_succ T))
            fun n _ _ => hterm0 n
      _ = Real.sqrt (poleSumEnergy k T) ^ 2 := by rw [hrange, Real.sq_sqrt (hL0 T)]
      _ ≤ ((Real.sqrt E + B) / 2) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h4 2
  · intro hs
    refine ⟨(2 * |halfZeta| * Real.sqrt (∑' n : ℕ, partialPoleSum k n ^ 2 / ((n : ℝ) + 1)) + B) ^ 2,
      fun T => ?_⟩
    have hL : poleSumEnergy k T ≤ ∑' n : ℕ, partialPoleSum k n ^ 2 / ((n : ℝ) + 1) := by
      rw [← hrange T]; exact hs.sum_le_tsum _ fun n _ => hterm0 n
    have h1 := (abs_le.mp (hB T)).2
    have h2 : 2 * |halfZeta| * Real.sqrt (poleSumEnergy k T) ≤
        2 * |halfZeta| * Real.sqrt (∑' n : ℕ, partialPoleSum k n ^ 2 / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hL) (by positivity)
    have h3 : Real.sqrt (weightPronicEnergy c (∑' d : ℕ, c d / d) T) ≤
        2 * |halfZeta| * Real.sqrt (∑' n : ℕ, partialPoleSum k n ^ 2 / ((n : ℝ) + 1)) + B := by
      linarith
    calc weightPronicEnergy c (∑' d : ℕ, c d / d) T =
          Real.sqrt (weightPronicEnergy c (∑' d : ℕ, c d / d) T) ^ 2 :=
          (Real.sq_sqrt (hE0 T)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
