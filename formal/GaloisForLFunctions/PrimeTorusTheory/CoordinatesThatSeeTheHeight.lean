import GaloisForLFunctions.PrimeTorusTheory.TheWallForAllPrimes

/-!
# Coordinates that see the height

The wall says that prime coordinates that return pay for nothing, and that the Euler factor `E(s) = ζ(2s − 1)/ζ(2s)` cannot be paid in the coordinates `p^{−s}` and `G` (`euler_test`). `two_point_inequality` says what a certificate must do instead: its coordinates must see the absolute height. Here is such a certificate, for the same function.

**Product decompositions** (`hasSum_of_product`). If `S = Π_n z_n` with `z_n` in the closed disc and `Σ_n |1 − z_n| < ∞`, then

`1 − S(x) conj S(y) = Σ_n (1 − z_n(x) conj z_n(y)) K_n(x, y)`, `K_n(x, y) = Π_{m<n} z_m(x) conj z_m(y)`,

with `K_n` of rank one, hence positive.

**The allocation of the Gamma factor** (`euler_test_has_height_certificate`). On `Re s > 2`, write `1/(s + 3) = Π_p (s + 3)^{−α_p}`, `Σ_p α_p = 1`, `α_p ∝ p^{−2}`. Let `E_p(s) = (1 − p^{−2s})/(1 − p^{1−2s})` be the Euler factor of `E` at `p`. The coordinates

`z_p(s) = (s + 3)^{−α_p} E_p(s)`

are in the disc, depend on the prime only through `p^{−2s}`, and tend to `0` vertically: they do not return. Their product is `E(s)/(s + 3)`, the function that has no decomposition in `p^{−s}` and `1/(s + 3)`. So each prime pays its own Euler factor out of its share of the Gamma factor.

**What this does not do.** A constant share needs `|E_p| ≤ |s + 3|^{α_p}` already at the bottom of the half-plane, so summing the shares this is size against base at `t = 0`. And without a condition tying the coordinates to the primes, non-returning coordinates carry no information: every zero-free Schur function `e^{−B}` is the product of its own roots `e^{−c_n B}` (`hasSum_of_exp`). So a useful certificate must state how a coordinate depends on `p^{−s}`.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

local notation "conj" => starRingEnd ℂ

/-- `|1 − a conj b| ≤ |1 − a| + |1 − b|` in the closed disc. -/
theorem norm_one_sub_mul_conj_le {a b : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖1 - a * conj b‖ ≤ ‖1 - a‖ + ‖1 - b‖ := by
  have e : 1 - a * conj b = (1 - a) + a * (1 - conj b) := by ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_mul]
  have h1 : ‖1 - conj b‖ = ‖1 - b‖ := by
    rw [← Complex.norm_conj (1 - b)]
    simp
  rw [h1]
  calc ‖a‖ * ‖1 - b‖ ≤ 1 * ‖1 - b‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ = _ := one_mul _

/-- **Product decompositions.** See the module docstring. -/
theorem hasSum_of_product {X : Type*} {z : ℕ → X → ℂ} {S : X → ℂ} (hz : ∀ n x, ‖z n x‖ ≤ 1)
    (hsum : ∀ x, Summable fun n => ‖1 - z n x‖)
    (hP : ∀ x, Tendsto (fun N => ∏ n ∈ Finset.range N, z n x) atTop (𝓝 (S x))) (x y : X) :
    HasSum (fun n => (1 - z n x * conj (z n y)) *
        ((∏ m ∈ Finset.range n, z m x) * conj (∏ m ∈ Finset.range n, z m y)))
      (1 - S x * conj (S y)) := by
  have hprod : ∀ w n, ‖∏ m ∈ Finset.range n, z m w‖ ≤ 1 := fun w n => by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun m _ => hz m w
  have hnorm : ∀ n, ‖(1 - z n x * conj (z n y)) *
      ((∏ m ∈ Finset.range n, z m x) * conj (∏ m ∈ Finset.range n, z m y))‖ ≤
      ‖1 - z n x‖ + ‖1 - z n y‖ := by
    intro n
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have h1 := hprod x n
    have h2 := hprod y n
    have h3 := norm_one_sub_mul_conj_le (a := z n x) (b := z n y) (hz n x)
    have h4 : ‖∏ m ∈ Finset.range n, z m x‖ * ‖∏ m ∈ Finset.range n, z m y‖ ≤ 1 := by
      have := norm_nonneg (∏ m ∈ Finset.range n, z m x)
      have := norm_nonneg (∏ m ∈ Finset.range n, z m y)
      nlinarith
    calc _ ≤ (‖1 - z n x‖ + ‖1 - z n y‖) * 1 :=
          mul_le_mul h3 h4 (by positivity) (by positivity)
      _ = _ := mul_one _
  have hsummable : Summable fun n => ‖(1 - z n x * conj (z n y)) *
      ((∏ m ∈ Finset.range n, z m x) * conj (∏ m ∈ Finset.range n, z m y))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm ((hsum x).add (hsum y))
  rw [hasSum_iff_tendsto_nat_of_summable_norm hsummable]
  -- The telescoping identity.
  have htel : ∀ N, ∑ n ∈ Finset.range N, (1 - z n x * conj (z n y)) *
      ((∏ m ∈ Finset.range n, z m x) * conj (∏ m ∈ Finset.range n, z m y)) =
      1 - (∏ m ∈ Finset.range N, z m x) * conj (∏ m ∈ Finset.range N, z m y) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.prod_range_succ, Finset.prod_range_succ, map_mul]
      ring
  simp_rw [htel]
  have hconj : Tendsto (fun N => conj (∏ m ∈ Finset.range N, z m y)) atTop (𝓝 (conj (S y))) :=
    (Complex.continuous_conj.tendsto _).comp (hP y)
  exact tendsto_const_nhds.sub ((hP x).mul hconj)

/-- Each kernel of a product decomposition is positive. -/
theorem twoPositive_product {X : Type*} (z : ℕ → X → ℂ) (n : ℕ) :
    TwoPositive fun x y => (∏ m ∈ Finset.range n, z m x) * conj (∏ m ∈ Finset.range n, z m y) :=
  twoPositive_rankOne fun x => ∏ m ∈ Finset.range n, z m x

/-- **Roots.** Without a condition tying the coordinates to the primes, every zero-free Schur function is a convergent product of its own roots. -/
theorem hasSum_of_exp {X : Type*} {B : X → ℂ} (hB : ∀ x, 0 ≤ (B x).re) {c : ℕ → ℝ} (hc0 : ∀ n, 0 ≤ c n)
    (hc : HasSum c 1) (x y : X) :
    HasSum (fun n => (1 - cexp (-((c n : ℂ) * B x)) * conj (cexp (-((c n : ℂ) * B y)))) *
        ((∏ m ∈ Finset.range n, cexp (-((c m : ℂ) * B x))) *
          conj (∏ m ∈ Finset.range n, cexp (-((c m : ℂ) * B y)))))
      (1 - cexp (-B x) * conj (cexp (-B y))) := by
  have hcle : ∀ n, c n ≤ 1 := fun n => le_hasSum hc n fun m _ => hc0 m
  have hs := hc.summable
  refine hasSum_of_product (z := fun n w => cexp (-((c n : ℂ) * B w))) (S := fun w => cexp (-B w))
    (fun n w => ?_) (fun w => ?_) (fun w => ?_) x y
  · rw [Complex.norm_exp]
    refine Real.exp_le_one_iff.mpr ?_
    simp only [Complex.neg_re, Complex.re_ofReal_mul]
    have := mul_nonneg (hc0 n) (hB w)
    linarith
  · have hle : ∀ n, ‖1 - cexp (-((c n : ℂ) * B w))‖ ≤ c n * (‖B w‖ * Real.exp ‖B w‖) := by
      intro n
      have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (-((c n : ℂ) * B w)) 1
      simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
        norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 n)] at h
      rw [norm_sub_rev]
      refine h.trans ?_
      have h1 : c n * ‖B w‖ ≤ ‖B w‖ := by
        have := mul_le_mul_of_nonneg_right (hcle n) (norm_nonneg (B w))
        linarith
      have h2 : Real.exp (c n * ‖B w‖) ≤ Real.exp ‖B w‖ := Real.exp_le_exp.mpr h1
      calc c n * ‖B w‖ * Real.exp (c n * ‖B w‖) ≤ c n * ‖B w‖ * Real.exp ‖B w‖ :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg (hc0 n) (norm_nonneg _))
        _ = _ := by ring
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle (hs.mul_right _)
  · have hexp : ∀ N, ∏ m ∈ Finset.range N, cexp (-((c m : ℂ) * B w)) =
        cexp (-(((∑ m ∈ Finset.range N, c m : ℝ) : ℂ) * B w)) := by
      intro N
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [Finset.sum_mul, Finset.sum_neg_distrib]
    simp_rw [hexp]
    have h1 : Tendsto (fun N => ∑ m ∈ Finset.range N, c m) atTop (𝓝 1) := hc.tendsto_sum_nat
    have h2 : Tendsto (fun N => ((∑ m ∈ Finset.range N, c m : ℝ) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp h1
    have h4 : Tendsto (fun N => cexp (-(((∑ m ∈ Finset.range N, c m : ℝ) : ℂ) * B w))) atTop
        (𝓝 (cexp (-(((1 : ℝ) : ℂ) * B w)))) :=
      (Complex.continuous_exp.tendsto _).comp ((h2.mul_const (B w)).neg)
    rw [Complex.ofReal_one, one_mul] at h4
    exact h4

/-! ### The shares of the Gamma factor -/

/-- The weight of a prime. -/
def shareWeight (n : ℕ) : ℝ := if n.Prime then 1 / (n : ℝ) ^ 2 else 0

theorem shareWeight_nonneg (n : ℕ) : 0 ≤ shareWeight n := by
  unfold shareWeight
  split_ifs <;> positivity

theorem shareWeight_le (n : ℕ) : shareWeight n ≤ 1 / (n : ℝ) ^ 2 := by
  unfold shareWeight
  split_ifs
  · exact le_rfl
  · positivity

theorem summable_shareWeight : Summable shareWeight :=
  Summable.of_nonneg_of_le shareWeight_nonneg shareWeight_le
    (Real.summable_one_div_nat_pow.mpr (by norm_num))

/-- The total weight. -/
def shareTotal : ℝ := ∑' n, shareWeight n

theorem shareTotal_pos : 0 < shareTotal := by
  have h2 : 0 < shareWeight 2 := by
    unfold shareWeight
    rw [if_pos Nat.prime_two]
    positivity
  exact summable_shareWeight.tsum_pos shareWeight_nonneg 2 h2

/-- The partial sums telescope below `1`. -/
theorem sum_shareWeight_le (N : ℕ) : ∑ n ∈ Finset.range (N + 2), shareWeight n ≤ 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero =>
    have h0 : shareWeight 0 = 0 := by simp [shareWeight, Nat.not_prime_zero]
    have h1 : shareWeight 1 = 0 := by simp [shareWeight, Nat.not_prime_one]
    simp [Finset.sum_range_succ, h0, h1]
  | succ n ih =>
    rw [show n + 1 + 2 = n + 2 + 1 by ring, Finset.sum_range_succ]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle := shareWeight_le (n + 2)
    have key : 1 / (((n + 2 : ℕ) : ℝ)) ^ 2 ≤ 1 / ((n : ℝ) + 1) - 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ hn.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem shareTotal_le_one : shareTotal ≤ 1 := by
  refine Real.tsum_le_of_sum_range_le shareWeight_nonneg fun N => ?_
  have h1 : ∑ n ∈ Finset.range N, shareWeight n ≤ ∑ n ∈ Finset.range (N + 2), shareWeight n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      fun n _ _ => shareWeight_nonneg n
  have h2 := sum_shareWeight_le N
  have h3 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  linarith

/-- The share of the Gamma factor. -/
def share (n : ℕ) : ℝ := shareWeight n / shareTotal

theorem share_nonneg (n : ℕ) : 0 ≤ share n :=
  div_nonneg (shareWeight_nonneg n) shareTotal_pos.le

theorem shareWeight_le_share (n : ℕ) : shareWeight n ≤ share n := by
  unfold share
  rw [le_div_iff₀ shareTotal_pos]
  have := mul_le_mul_of_nonneg_left shareTotal_le_one (shareWeight_nonneg n)
  linarith

theorem share_le (n : ℕ) : share n ≤ 1 / shareTotal * (1 / (n : ℝ) ^ 2) := by
  unfold share
  rw [div_eq_mul_inv, mul_comm, one_div]
  exact mul_le_mul_of_nonneg_left (shareWeight_le n) (inv_nonneg.mpr shareTotal_pos.le)

theorem hasSum_share : HasSum share 1 := by
  have h := summable_shareWeight.hasSum.div_const shareTotal
  have e : (∑' n, shareWeight n) / shareTotal = 1 := by
    change shareTotal / shareTotal = 1
    exact div_self shareTotal_pos.ne'
  rwa [e] at h

/-! ### The local factors -/

/-- The Euler factor of `ζ(2s − 1)/ζ(2s)` at `p`. -/
def eulerLocal (p : ℕ) (s : ℂ) : ℂ := (1 - (p : ℂ) ^ (-(2 * s))) * (1 - (p : ℂ) ^ (-(2 * s - 1)))⁻¹

/-- The size of the two powers on `Re s > 2`. -/
theorem norm_cpow_le {p : ℕ} (hp : p.Prime) {w : ℂ} {a : ℕ} (hw : (a : ℝ) ≤ w.re) :
    ‖(p : ℂ) ^ (-w)‖ ≤ (1 / (p : ℝ)) ^ a := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re, one_div, inv_pow, ← Real.rpow_natCast,
    ← Real.rpow_neg hp0.le]
  exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)

/-- The Euler factor is close to `1`, with `u = 1/p`. -/
theorem norm_eulerLocal_bounds {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 2 < s.re) :
    ‖eulerLocal p s‖ ≤ (1 + (1 / (p : ℝ)) ^ 4) / (1 - (1 / (p : ℝ)) ^ 3) ∧
      ‖1 - eulerLocal p s‖ ≤ 3 * (1 / (p : ℝ)) ^ 3 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set u : ℝ := 1 / (p : ℝ) with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
  have hx : ‖(p : ℂ) ^ (-(2 * s))‖ ≤ u ^ 4 := norm_cpow_le hp (by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    push_cast
    linarith)
  have hy : ‖(p : ℂ) ^ (-(2 * s - 1))‖ ≤ u ^ 3 := norm_cpow_le hp (by
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
      Complex.one_re]
    push_cast
    linarith)
  set x := (p : ℂ) ^ (-(2 * s)) with hxdef
  set y := (p : ℂ) ^ (-(2 * s - 1)) with hydef
  have hu3 : u ^ 3 ≤ 1 / 8 := by
    have := pow_le_pow_left₀ hu0.le hu1 3
    norm_num at this ⊢
    linarith
  have hu4 : u ^ 4 ≤ u ^ 3 := pow_le_pow_of_le_one hu0.le (by linarith) (by norm_num)
  have hden : 1 - u ^ 3 ≤ ‖1 - y‖ := by
    have h := norm_sub_norm_le (1 : ℂ) y
    rw [norm_one] at h
    linarith
  have hdpos : 0 < 1 - u ^ 3 := by linarith
  have hne : 1 - y ≠ 0 := by
    rw [← norm_pos_iff]
    linarith
  constructor
  · unfold eulerLocal
    rw [← hxdef, ← hydef, norm_mul, norm_inv, ← div_eq_mul_inv]
    refine div_le_div₀ (by positivity) ?_ hdpos hden
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]
    linarith
  · have e : 1 - eulerLocal p s = (x - y) * (1 - y)⁻¹ := by
      unfold eulerLocal
      rw [← hxdef, ← hydef]
      field_simp
      ring
    rw [e, norm_mul, norm_inv, ← div_eq_mul_inv, div_le_iff₀ (lt_of_lt_of_le hdpos hden)]
    have h1 : ‖x - y‖ ≤ u ^ 4 + u ^ 3 := (norm_sub_le _ _).trans (add_le_add hx hy)
    have h2' : 3 * u ^ 3 * (1 - u ^ 3) ≤ 3 * u ^ 3 * ‖1 - y‖ :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    nlinarith

/-- The Euler factors multiply to `ζ(2s − 1)/ζ(2s)`. -/
theorem tendsto_prod_eulerLocal {s : ℂ} (hs : 2 < s.re) :
    Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, eulerLocal p s) atTop
      (𝓝 (riemannZeta (2 * s - 1) / riemannZeta (2 * s))) := by
  have hre1 : 1 < (2 * s - 1).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
      Complex.one_re]
    linarith
  have hre2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have h1 := riemannZeta_eulerProduct hre1
  have h2 := riemannZeta_eulerProduct hre2
  have hne : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre2.le
  have h3 := (h2.inv₀ hne).mul h1
  rw [div_eq_mul_inv, mul_comm]
  refine h3.congr fun N => ?_
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  unfold eulerLocal
  rw [inv_inv]

/-! ### The coordinates -/

/-- The coordinate of `n`: the share of the Gamma factor times the Euler factor, at a prime. -/
def heightCoord (n : ℕ) (s : Plane 2) : ℂ :=
  if n.Prime then cexp (-((share n : ℂ) * Complex.log (s.1 + 3))) * eulerLocal n s.1 else 1

theorem five_lt_norm (s : Plane 2) : 5 < ‖s.1 + 3‖ := by
  have hs : (2 : ℝ) < s.1.re := s.2
  have := Complex.re_le_norm (s.1 + 3)
  simp only [Complex.add_re, Complex.re_ofNat] at this
  linarith

/-- The size of a share of the Gamma factor. -/
theorem norm_exp_share (n : ℕ) (s : Plane 2) :
    ‖cexp (-((share n : ℂ) * Complex.log (s.1 + 3)))‖ = Real.exp (-(share n * Real.log ‖s.1 + 3‖)) := by
  rw [Complex.norm_exp]
  simp only [Complex.neg_re, Complex.re_ofReal_mul, Complex.log_re]

/-- **The coordinates lie in the disc.** Each prime's share of the Gamma factor pays for its Euler factor. -/
theorem norm_heightCoord_le (n : ℕ) (s : Plane 2) : ‖heightCoord n s‖ ≤ 1 := by
  unfold heightCoord
  split_ifs with hp
  swap
  · simp
  have hs : (2 : ℝ) < s.1.re := s.2
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
  set u : ℝ := 1 / (n : ℝ) with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
  rw [norm_mul, norm_exp_share]
  have hE := (norm_eulerLocal_bounds hp hs).1
  rw [← hu] at hE
  have hshare : u ^ 2 ≤ share n := by
    have h := shareWeight_le_share n
    unfold shareWeight at h
    rw [if_pos hp] at h
    have e : u ^ 2 = 1 / (n : ℝ) ^ 2 := by
      rw [hu, div_pow, one_pow]
    rw [e]
    exact h
  have hlog5 : 1.3 ≤ Real.log ‖s.1 + 3‖ := by
    have h4 : Real.log 4 ≤ Real.log ‖s.1 + 3‖ :=
      Real.log_le_log (by norm_num) (by linarith [five_lt_norm s])
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_gt_d9
    linarith
  have hmass : 1.3 * u ^ 2 ≤ share n * Real.log ‖s.1 + 3‖ := by
    have hn := share_nonneg n
    calc 1.3 * u ^ 2 ≤ Real.log ‖s.1 + 3‖ * u ^ 2 := by gcongr
      _ ≤ Real.log ‖s.1 + 3‖ * share n := by
          exact mul_le_mul_of_nonneg_left hshare (by linarith)
      _ = _ := mul_comm _ _
  have hexp : Real.exp (-(share n * Real.log ‖s.1 + 3‖)) * (1 + 1.3 * u ^ 2) ≤ 1 := by
    have h1 : 1 + 1.3 * u ^ 2 ≤ Real.exp (1.3 * u ^ 2) := by
      have := Real.add_one_le_exp (1.3 * u ^ 2)
      linarith
    have h3 : Real.exp (-(share n * Real.log ‖s.1 + 3‖)) ≤ Real.exp (-(1.3 * u ^ 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc _ ≤ Real.exp (-(1.3 * u ^ 2)) * Real.exp (1.3 * u ^ 2) :=
          mul_le_mul h3 h1 (by positivity) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hu3 : u ^ 3 ≤ 1 / 8 := by
    have := pow_le_pow_left₀ hu0.le hu1 3
    norm_num at this ⊢
    linarith
  have hdpos : 0 < 1 - u ^ 3 := by linarith
  have hpoly : (1 + u ^ 4) / (1 - u ^ 3) ≤ 1 + 1.3 * u ^ 2 := by
    rw [div_le_iff₀ hdpos]
    have h1 : u ^ 2 ≤ 1 / 4 := by nlinarith
    have hu2 : 0 < u ^ 2 := by positivity
    have e : (1 + 1.3 * u ^ 2) * (1 - u ^ 3) - (1 + u ^ 4) =
        u ^ 2 * (1.3 - u - u ^ 2 - 1.3 * u ^ 3) := by ring
    have h4 : 0 ≤ 1.3 - u - u ^ 2 - 1.3 * u ^ 3 := by nlinarith
    have := mul_nonneg hu2.le h4
    linarith
  calc _ ≤ Real.exp (-(share n * Real.log ‖s.1 + 3‖)) * (1 + 1.3 * u ^ 2) :=
        mul_le_mul_of_nonneg_left (hE.trans hpoly) (Real.exp_pos _).le
    _ ≤ 1 := hexp

/-- The coordinates are summably close to `1`. -/
theorem summable_one_sub_heightCoord (s : Plane 2) : Summable fun n => ‖1 - heightCoord n s‖ := by
  have hs : (2 : ℝ) < s.1.re := s.2
  set C : ℝ := 1 / shareTotal * ‖Complex.log (s.1 + 3)‖ with hC
  have hC0 : 0 ≤ C := by
    have := shareTotal_pos
    positivity
  have hbound : ∀ n : ℕ, ‖1 - heightCoord n s‖ ≤ (C * Real.exp C + Real.exp C * 3) * (1 / (n : ℝ) ^ 2) := by
    intro n
    unfold heightCoord
    split_ifs with hp
    swap
    · simp only [sub_self, norm_zero]
      positivity
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
    set w : ℂ := -((share n : ℂ) * Complex.log (s.1 + 3)) with hw
    have hwn : ‖w‖ ≤ C * (1 / (n : ℝ) ^ 2) := by
      rw [hw, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (share_nonneg n), hC]
      have := mul_le_mul_of_nonneg_right (share_le n) (norm_nonneg (Complex.log (s.1 + 3)))
      linarith
    have hwC : ‖w‖ ≤ C := by
      refine hwn.trans ?_
      have : 1 / (n : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact h2
      nlinarith
    have hexpw : ‖1 - cexp w‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
      have h := Complex.norm_exp_sub_sum_le_norm_mul_exp w 1
      simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one] at h
      rwa [norm_sub_rev]
    have hexpC : Real.exp ‖w‖ ≤ Real.exp C := Real.exp_le_exp.mpr hwC
    have hE := (norm_eulerLocal_bounds hp hs).2
    have hun : (1 / (n : ℝ)) ^ 3 ≤ 1 / (n : ℝ) ^ 2 := by
      have h3 : (1 / (n : ℝ)) ^ 3 ≤ (1 / (n : ℝ)) ^ 2 := by
        refine pow_le_pow_of_le_one (by positivity) ?_ (by norm_num)
        rw [div_le_one (by exact_mod_cast hp.pos)]
        exact_mod_cast hp.one_lt.le
      have e2 : (1 / (n : ℝ)) ^ 2 = 1 / (n : ℝ) ^ 2 := by rw [div_pow, one_pow]
      rw [e2] at h3
      exact h3
    have e : 1 - cexp w * eulerLocal n s.1 = (1 - cexp w) + cexp w * (1 - eulerLocal n s.1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_exp]
    have hre : Real.exp w.re ≤ Real.exp C := by
      refine Real.exp_le_exp.mpr ?_
      exact (Complex.re_le_norm w).trans hwC
    have hx : 0 ≤ 1 / (n : ℝ) ^ 2 := by positivity
    calc _ ≤ ‖w‖ * Real.exp ‖w‖ + Real.exp C * (3 * (1 / (n : ℝ)) ^ 3) :=
          add_le_add hexpw (mul_le_mul hre hE (norm_nonneg _) (Real.exp_pos _).le)
      _ ≤ (C * (1 / (n : ℝ) ^ 2)) * Real.exp C + Real.exp C * (3 * (1 / (n : ℝ) ^ 2)) := by
          gcongr
      _ = _ := by ring
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
    ((Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _)

/-- The partial products split into the Gamma part and the Euler part. -/
theorem prod_heightCoord (N : ℕ) (s : Plane 2) :
    ∏ n ∈ Finset.range N, heightCoord n s =
      cexp (-(((∑ n ∈ Finset.range N, share n : ℝ) : ℂ) * Complex.log (s.1 + 3))) *
        ∏ p ∈ N.primesBelow, eulerLocal p s.1 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Finset.sum_range_succ, Nat.primesBelow_succ]
    unfold heightCoord
    by_cases hp : n.Prime
    · have hmem : n ∉ n.primesBelow := by
        simp [Nat.mem_primesBelow]
      rw [if_pos hp, if_pos hp, Finset.prod_insert hmem]
      have e : cexp (-((((∑ m ∈ Finset.range n, share m) + share n : ℝ) : ℂ) * Complex.log (s.1 + 3))) =
          cexp (-(((∑ m ∈ Finset.range n, share m : ℝ) : ℂ) * Complex.log (s.1 + 3))) *
            cexp (-((share n : ℂ) * Complex.log (s.1 + 3))) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [e]
      ring
    · have hzero : share n = 0 := by
        unfold share shareWeight
        rw [if_neg hp, zero_div]
      rw [if_neg hp, if_neg hp, hzero, mul_one, add_zero]

/-- The product of the coordinates is the function of the second test. -/
theorem tendsto_prod_heightCoord (s : Plane 2) :
    Tendsto (fun N => ∏ n ∈ Finset.range N, heightCoord n s) atTop (𝓝 (eulerTestS s)) := by
  have hs : (2 : ℝ) < s.1.re := s.2
  have hne : s.1 + 3 ≠ 0 := by
    rw [← norm_pos_iff]
    linarith [five_lt_norm s]
  simp_rw [prod_heightCoord]
  have h1 : Tendsto (fun N => ∑ n ∈ Finset.range N, share n) atTop (𝓝 1) := hasSum_share.tendsto_sum_nat
  have h2 : Tendsto (fun N => ((∑ n ∈ Finset.range N, share n : ℝ) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp h1
  have h3 : Tendsto (fun N => cexp (-(((∑ n ∈ Finset.range N, share n : ℝ) : ℂ) * Complex.log (s.1 + 3)))) atTop
      (𝓝 (cexp (-(((1 : ℝ) : ℂ) * Complex.log (s.1 + 3))))) :=
    (Complex.continuous_exp.tendsto _).comp ((h2.mul_const (Complex.log (s.1 + 3))).neg)
  have h4 := h3.mul (tendsto_prod_eulerLocal hs)
  have e : cexp (-(((1 : ℝ) : ℂ) * Complex.log (s.1 + 3))) *
      (riemannZeta (2 * s.1 - 1) / riemannZeta (2 * s.1)) = eulerTestS s := by
    unfold eulerTestS eulerTestG eulerFactor
    rw [Complex.ofReal_one, one_mul, Complex.exp_neg, Complex.exp_log hne, one_div]
  rw [e] at h4
  exact h4

/-- **The coordinates do not return.** -/
theorem tendsto_heightCoord {p : ℕ} (hp : p.Prime) (s : Plane 2) :
    Tendsto (fun τ => heightCoord p (vshift' s τ)) atTop (𝓝 0) := by
  have hs : ∀ τ, (2 : ℝ) < (vshift' s τ).1.re := fun τ => (vshift' s τ).2
  have hsharepos : 0 < share p := by
    unfold share shareWeight
    rw [if_pos hp]
    have := shareTotal_pos
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  have hnorm : Tendsto (fun τ : ℝ => ‖(vshift' s τ).1 + 3‖) atTop atTop := by
    refine tendsto_atTop_mono (f := fun τ : ℝ => τ + s.1.im) (fun τ => ?_)
      (tendsto_atTop_add_const_right _ _ tendsto_id)
    have h := Complex.abs_im_le_norm ((vshift' s τ).1 + 3)
    have him : ((vshift' s τ).1 + 3).im = s.1.im + τ := by
      simp [vshift']
    rw [him] at h
    have := le_abs_self (s.1.im + τ)
    linarith
  have hexp : Tendsto (fun τ : ℝ => Real.exp (-(share p * Real.log ‖(vshift' s τ).1 + 3‖))) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact tendsto_neg_atTop_atBot.comp ((Real.tendsto_log_atTop.comp hnorm).const_mul_atTop hsharepos)
  have hB : ∀ τ, ‖eulerLocal p (vshift' s τ).1‖ ≤ 2 := by
    intro τ
    have h := (norm_eulerLocal_bounds hp (hs τ)).1
    refine h.trans ?_
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hu0 : 0 < 1 / (p : ℝ) := by positivity
    have hu1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    have hu3 : (1 / (p : ℝ)) ^ 3 ≤ 1 / 8 := by
      have := pow_le_pow_left₀ hu0.le hu1 3
      norm_num at this ⊢
      linarith
    have hu4 : (1 / (p : ℝ)) ^ 4 ≤ 1 / 16 := by
      have := pow_le_pow_left₀ hu0.le hu1 4
      norm_num at this ⊢
      linarith
    rw [div_le_iff₀ (by linarith)]
    linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h2 := hexp.mul_const 2
  rw [zero_mul] at h2
  refine squeeze_zero (fun _ => norm_nonneg _) (fun τ => ?_) h2
  unfold heightCoord
  rw [if_pos hp, norm_mul, norm_exp_share]
  exact mul_le_mul_of_nonneg_left (hB τ) (Real.exp_pos _).le

/-- **A certificate for the second test.** The function `E(s)/(s + 3)` has no decomposition in the returning coordinates `p^{−s}` and `1/(s + 3)` (`euler_test`), and it has one in the coordinates
`(s + 3)^{−α_p} E_p(s)`, which lie in the disc and do not return. -/
theorem euler_test_has_height_certificate :
    (∀ n s, ‖heightCoord n s‖ ≤ 1) ∧
      (∀ p : ℕ, p.Prime → ∀ s, Tendsto (fun τ => heightCoord p (vshift' s τ)) atTop (𝓝 0)) ∧
      (∀ n, TwoPositive fun x y : Plane 2 => (∏ m ∈ Finset.range n, heightCoord m x) *
        conj (∏ m ∈ Finset.range n, heightCoord m y)) ∧
      ∀ x y : Plane 2, HasSum (fun n => (1 - heightCoord n x * conj (heightCoord n y)) *
        ((∏ m ∈ Finset.range n, heightCoord m x) * conj (∏ m ∈ Finset.range n, heightCoord m y)))
        (1 - eulerTestS x * conj (eulerTestS y)) :=
  ⟨norm_heightCoord_le, fun _ hp s => tendsto_heightCoord hp s, fun n => twoPositive_product _ n,
    fun x y => hasSum_of_product norm_heightCoord_le summable_one_sub_heightCoord tendsto_prod_heightCoord x y⟩

end

end GaloisForLFunctions.PrimeTorusTheory
