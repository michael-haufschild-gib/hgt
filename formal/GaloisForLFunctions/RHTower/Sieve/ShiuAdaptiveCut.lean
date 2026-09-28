import GaloisForLFunctions.RHTower.Sieve.ShiuSharp
import GaloisForLFunctions.RHTower.Sieve.ChernoffTails
import GaloisForLFunctions.RHTower.Sieve.IntervalMultiples
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Shiu's adaptive cut and Rankin's bound for tilted smooth sums

The ingredients of Shiu's bound for `t^{ω(n)}` in short intervals (`Sieve/ShiuOmegaTiltShortInterval`):
Rankin's bound for tilted sums over smooth numbers, the cut `n = b·a` at Shiu's level, the three
cases of the cut with their fibre bounds, and the grouped Rankin estimate for the third case.
-/

namespace RHTower.Sieve

open Finset Filter Topology

noncomputable section

/-- The telescoping majorant of `n^{-3/2}`. -/
theorem one_div_mul_sqrt_le_telescope {n : ℕ} (hn : 2 ≤ n) :
    1 / ((n : ℝ) * Real.sqrt n)
      ≤ 2 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt n) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set a : ℝ := Real.sqrt ((n : ℝ) - 1) with ha
  set b : ℝ := Real.sqrt n with hb
  have ha0 : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.2 (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have haa : a * a = (n : ℝ) - 1 := Real.mul_self_sqrt (by linarith)
  have hbb : b * b = (n : ℝ) := Real.mul_self_sqrt (by linarith)
  -- `1/a - 1/b = 1/(a b (a + b))`
  have hdiff : 1 / a - 1 / b = 1 / (a * b * (a + b)) := by
    field_simp
    nlinarith [haa, hbb]
  rw [hdiff, ← hbb, show b * b * b = (b * b) * b by ring]
  rw [div_le_iff₀ (by positivity), mul_comm, ← mul_assoc, mul_one_div,
    le_div_iff₀ (by positivity), one_mul]
  have h1 : a * b * (a + b) ≤ b * b * (b + b) := by
    have : a * b ≤ b * b := mul_le_mul_of_nonneg_right hab hb0.le
    exact mul_le_mul this (by linarith) (by positivity) (by positivity)
  nlinarith [h1]

/-- **`∑_{2 ≤ n ≤ N} n^{-3/2} ≤ 2`.** -/
theorem sum_inv_mul_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) * Real.sqrt n) ≤ 2 := by
  rcases Nat.lt_or_ge N 1 with hN | hN
  · have : N = 0 := by omega
    subst this
    simp
  have hstep : ∀ M : ℕ, 1 ≤ M → ∑ n ∈ Finset.Icc 2 M, 1 / ((n : ℝ) * Real.sqrt n)
      ≤ 2 * (1 - 1 / Real.sqrt M) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have htel := one_div_mul_sqrt_le_telescope (n := M + 1) (by omega)
        push_cast at htel ⊢
        rw [show ((M : ℝ) + 1 - 1) = (M : ℝ) by ring] at htel
        linarith
  refine (hstep N hN).trans ?_
  have : 0 ≤ 1 / Real.sqrt (N : ℝ) := by positivity
  linarith

/-- `exp x ≤ 1 + e x` for `0 ≤ x ≤ 1`. -/
theorem exp_le_one_add_e_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + Real.exp 1 * x := by
  have hconv := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ 1)
    (show (0 : ℝ) ≤ 1 - x by linarith) hx0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at hconv
  nlinarith [hconv]

/-- The additive constant of the tilted Rankin bound. -/
def rankinTiltConst : ℝ :=
  mertensSecondUpperConst + Real.exp 1 * (1 + Real.log 4 / 4) + 8

/-- The tilted Rankin weight `t^{ω(b)} b^{σ-1}`. -/
def rankinTiltWeight (t σ : ℝ) (b : ℕ) : ℝ := t ^ b.primeFactors.card * (b : ℝ) ^ (σ - 1)

theorem rankinTiltWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (σ : ℝ) (b : ℕ) :
    0 ≤ rankinTiltWeight t σ b :=
  mul_nonneg (pow_nonneg ht _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem rankinTiltWeight_mul (t σ : ℝ) {a b : ℕ} (hab : Nat.Coprime a b) :
    rankinTiltWeight t σ (a * b) = rankinTiltWeight t σ a * rankinTiltWeight t σ b := by
  rw [rankinTiltWeight, rankinTiltWeight, rankinTiltWeight, Nat.Coprime.primeFactors_mul hab,
    Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hab), pow_add, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

/-- The prime-power values of the tilted weight. -/
theorem rankinTiltWeight_prime_pow {t σ : ℝ} {p : ℕ} (hp : p.Prime) {i : ℕ} (hi : 1 ≤ i) :
    rankinTiltWeight t σ (p ^ i) = t * ((p : ℝ) ^ (σ - 1)) ^ i := by
  rw [rankinTiltWeight, Nat.primeFactors_prime_pow (by omega) hp, Finset.card_singleton, pow_one,
    Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
    ← Real.rpow_natCast ((p : ℝ) ^ (σ - 1)), ← Real.rpow_mul (Nat.cast_nonneg _),
    mul_comm (i : ℝ)]

/-- One Euler factor of the tilted Rankin sum. -/
theorem rankin_euler_factor_le {t σ : ℝ} (ht0 : 0 ≤ t) (hσ : σ ≤ 1 / 4)
    {p : ℕ} (hp : p.Prime) (Y : ℕ) :
    ∑ i ∈ Finset.range (Y + 1), rankinTiltWeight t σ (p ^ i)
      ≤ Real.exp (t * ((p : ℝ) ^ (σ - 1) + 4 * (1 / ((p : ℝ) * Real.sqrt p)))) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  set r : ℝ := (p : ℝ) ^ (σ - 1) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hp0.le _
  -- `r ≤ 3/4`
  have hr34 : r ≤ 3 / 4 := by
    have h1 : r ≤ (p : ℝ) ^ (-(3 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (p : ℝ) ^ (-(3 : ℝ) / 4) ≤ (2 : ℝ) ^ (-(3 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
    have h3 : (2 : ℝ) ^ (-(3 : ℝ) / 4) ≤ 3 / 4 := by
      have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(3 : ℝ) / 4) := Real.rpow_nonneg (by norm_num) _
      have h4 : ((2 : ℝ) ^ (-(3 : ℝ) / 4)) ^ (4 : ℕ) = 1 / 8 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
      refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by norm_num) ?_
      rw [h4]; norm_num
    linarith
  -- `r² ≤ p^{-3/2}`
  have hr2 : r ^ (2 : ℕ) ≤ 1 / ((p : ℝ) * Real.sqrt p) := by
    have h1 : r ^ (2 : ℕ) = (p : ℝ) ^ (2 * (σ - 1)) := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; ring_nf
    have h2 : (p : ℝ) ^ (2 * (σ - 1)) ≤ (p : ℝ) ^ (-(3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : (p : ℝ) ^ (-(3 : ℝ) / 2) = 1 / ((p : ℝ) * Real.sqrt p) := by
      rw [Real.sqrt_eq_rpow, show (-(3 : ℝ) / 2) = -(1 + 1 / 2) by ring, Real.rpow_neg hp0.le,
        Real.rpow_add hp0, Real.rpow_one, one_div, one_div]
    rw [h1]; linarith [h2, h3]
  -- the finite geometric sum
  have hsplit : ∑ i ∈ Finset.range (Y + 1), rankinTiltWeight t σ (p ^ i)
      = 1 + t * ∑ i ∈ Finset.range Y, r ^ (i + 1) := by
    rw [Finset.sum_range_succ', pow_zero,
      show rankinTiltWeight t σ 1 = 1 by simp [rankinTiltWeight], Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact rankinTiltWeight_prime_pow hp (by omega)
  have hgeom : ∑ i ∈ Finset.range Y, r ^ (i + 1) ≤ r + 4 * r ^ (2 : ℕ) := by
    have hfull : ∑ i ∈ Finset.range (Y + 1), r ^ i ≤ 1 / (1 - r) := by
      rw [geom_sum_eq (by linarith) (Y + 1)]
      have : 0 ≤ r ^ (Y + 1) := pow_nonneg hr0 _
      rw [show (r ^ (Y + 1) - 1) / (r - 1) = (1 - r ^ (Y + 1)) / (1 - r) by
        rw [← neg_div_neg_eq, neg_sub, neg_sub]]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hIco : ∑ i ∈ Finset.range Y, r ^ (i + 1) = ∑ i ∈ Finset.range (Y + 1), r ^ i - 1 := by
      rw [Finset.sum_range_succ', pow_zero]; ring
    rw [hIco]
    have h1 : 1 / (1 - r) - 1 = r + r ^ (2 : ℕ) / (1 - r) := by
      have hne : 1 - r ≠ 0 := by linarith
      field_simp
      ring
    have h2 : r ^ (2 : ℕ) / (1 - r) ≤ 4 * r ^ (2 : ℕ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg r, hr34]
    linarith
  rw [hsplit]
  have hstep : 1 + t * ∑ i ∈ Finset.range Y, r ^ (i + 1) ≤ 1 + t * (r + 4 * r ^ (2 : ℕ)) := by
    have := mul_le_mul_of_nonneg_left hgeom ht0
    linarith
  have hexp : 1 + t * (r + 4 * r ^ (2 : ℕ)) ≤ Real.exp (t * (r + 4 * r ^ (2 : ℕ))) := by
    have := Real.add_one_le_exp (t * (r + 4 * r ^ (2 : ℕ)))
    linarith
  refine hstep.trans (hexp.trans (Real.exp_le_exp.2 ?_))
  exact mul_le_mul_of_nonneg_left (by linarith) ht0

/-- **Rankin's bound for tilted sums over smooth numbers.** -/
theorem sum_smooth_rankinTilt_le {t : ℝ} (ht0 : 0 ≤ t) {W : ℕ} (hW : 4 ≤ Real.log W)
    (Y : ℕ) :
    ∑ b ∈ smoothUpTo (Nat.primesLE W) Y, rankinTiltWeight t (1 / Real.log W) b
      ≤ Real.exp (t * (logLog W + rankinTiltConst)) := by
  set σ : ℝ := 1 / Real.log W with hσdef
  have hL0 : 0 < Real.log W := by linarith
  have hW1 : (1 : ℝ) < (W : ℝ) := by
    by_contra h
    push Not at h
    have : Real.log (W : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h
    linarith
  have hW2 : 2 ≤ W := by
    have : (1 : ℕ) < W := by exact_mod_cast hW1
    omega
  have hσ0 : 0 ≤ σ := by rw [hσdef]; positivity
  have hσ14 : σ ≤ 1 / 4 := by
    rw [hσdef, div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have hbase := sum_smoothUpTo_le (g := rankinTiltWeight t σ) (rankinTiltWeight_nonneg ht0 σ)
    (by simp [rankinTiltWeight]) (fun a b hab => rankinTiltWeight_mul t σ hab) Y
    (Nat.primesLE W) (fun p hp => Nat.prime_of_mem_primesLE hp)
  refine hbase.trans ?_
  have hfac : ∏ p ∈ Nat.primesLE W, ∑ i ∈ Finset.range (Y + 1), rankinTiltWeight t σ (p ^ i)
      ≤ ∏ p ∈ Nat.primesLE W,
          Real.exp (t * ((p : ℝ) ^ (σ - 1) + 4 * (1 / ((p : ℝ) * Real.sqrt p)))) :=
    Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun i _ => rankinTiltWeight_nonneg ht0 σ _)
      (fun p hp => rankin_euler_factor_le ht0 hσ14 (Nat.prime_of_mem_primesLE hp) Y)
  refine hfac.trans ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ ht0
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  -- the first-order part
  have hfirst : ∑ p ∈ Nat.primesLE W, (p : ℝ) ^ (σ - 1)
      ≤ ∑ p ∈ Nat.primesLE W, (1 / (p : ℝ) + Real.exp 1 * σ * (Real.log p / (p : ℝ))) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp := Nat.prime_of_mem_primesLE hp
    have hpW : p ≤ W := (Nat.mem_primesLE.1 hp).1
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hlogp0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hlogpW : Real.log p ≤ Real.log W :=
      Real.log_le_log hp0 (by exact_mod_cast hpW)
    have hx1 : σ * Real.log p ≤ 1 := by
      rw [hσdef, div_mul_eq_mul_div, one_mul, div_le_one hL0]; exact hlogpW
    have hsplit : (p : ℝ) ^ (σ - 1) = Real.exp (σ * Real.log p) / (p : ℝ) := by
      rw [Real.rpow_sub hp0, Real.rpow_one, Real.rpow_def_of_pos hp0, mul_comm]
    rw [hsplit]
    have := exp_le_one_add_e_mul (mul_nonneg hσ0 hlogp0) hx1
    rw [div_le_iff₀ hp0]
    have e : (1 / (p : ℝ) + Real.exp 1 * σ * (Real.log p / (p : ℝ))) * (p : ℝ)
        = 1 + Real.exp 1 * (σ * Real.log p) := by
      field_simp
    rw [e]; exact this
  have hM1 := mertensS_le hW2
  have hM2 := mertensFirst_upper (n := W) (by omega)
  have hfirst' : ∑ p ∈ Nat.primesLE W, (1 / (p : ℝ) + Real.exp 1 * σ * (Real.log p / (p : ℝ)))
      ≤ logLog W + mertensSecondUpperConst + Real.exp 1 * (1 + Real.log 4 / 4) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hS : ∑ p ∈ Nat.primesLE W, 1 / (p : ℝ) = mertensS W := rfl
    rw [hS]
    have he : 0 ≤ Real.exp 1 * σ := by positivity
    have h1 : Real.exp 1 * σ * ∑ p ∈ Nat.primesLE W, Real.log p / (p : ℝ)
        ≤ Real.exp 1 * σ * (Real.log W + Real.log 4) := mul_le_mul_of_nonneg_left hM2 he
    have h2 : Real.exp 1 * σ * (Real.log W + Real.log 4)
        ≤ Real.exp 1 * (1 + Real.log 4 / 4) := by
      rw [hσdef]
      have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have : 1 / Real.log W * (Real.log W + Real.log 4) ≤ 1 + Real.log 4 / 4 := by
        rw [one_div_mul_eq_div, add_div, div_self hL0.ne']
        have : Real.log 4 / Real.log W ≤ Real.log 4 / 4 :=
          div_le_div_of_nonneg_left hlog4 (by norm_num) hW
        linarith
      calc Real.exp 1 * (1 / Real.log W) * (Real.log W + Real.log 4)
          = Real.exp 1 * (1 / Real.log W * (Real.log W + Real.log 4)) := by ring
        _ ≤ Real.exp 1 * (1 + Real.log 4 / 4) :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos 1).le
    linarith
  -- the second-order part
  have hsecond : ∑ p ∈ Nat.primesLE W, 1 / ((p : ℝ) * Real.sqrt p) ≤ 2 := by
    refine le_trans ?_ (sum_inv_mul_sqrt_le W)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    exact Finset.mem_Icc.2 ⟨hpp.two_le, (Nat.mem_primesLE.1 hp).1⟩
  rw [rankinTiltConst]
  linarith [hfirst, hfirst', hsecond]

/-! ## Shiu's adaptive cut -/

theorem smoothPart_self {n : ℕ} (hn : n ≠ 0) : smoothPart n n = n := by
  classical
  have h := Nat.prod_factorization_pow_eq_self hn
  rw [Finsupp.prod, Nat.support_factorization] at h
  rw [smoothPart]
  convert h using 2
  ext p
  simp only [Finset.mem_filter, and_iff_left_iff_imp]
  intro hp
  exact Nat.le_of_mem_primeFactors hp

theorem smoothPart_zero_left (n : ℕ) : smoothPart 0 n = 1 := by
  classical
  rw [smoothPart]
  convert Finset.prod_empty
  ext p
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, nonpos_iff_eq_zero]
  intro hp h0
  exact (Nat.prime_of_mem_primeFactors hp).ne_zero h0

/-- Raising the smoothness bound past a non-divisor changes nothing. -/
theorem smoothPart_succ_of_notMem {r n : ℕ} (hr : r + 1 ∉ n.primeFactors) :
    smoothPart (r + 1) n = smoothPart r n := by
  classical
  rw [smoothPart, smoothPart]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hle⟩
    refine ⟨hp, ?_⟩
    rcases Nat.lt_or_ge p (r + 1) with h | h
    · omega
    · have : p = r + 1 := by omega
      exact absurd (this ▸ hp) hr
  · rintro ⟨hp, hle⟩
    exact ⟨hp, by omega⟩

/-- Raising the smoothness bound past a prime factor multiplies by its full power. -/
theorem smoothPart_succ_of_mem {r n : ℕ} (hr : r + 1 ∈ n.primeFactors) :
    smoothPart (r + 1) n = smoothPart r n * (r + 1) ^ n.factorization (r + 1) := by
  classical
  rw [smoothPart, smoothPart]
  have hset : {p ∈ n.primeFactors | p ≤ r + 1}
      = insert (r + 1) {p ∈ n.primeFactors | p ≤ r} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hp, hle⟩
      rcases Nat.lt_or_ge p (r + 1) with h | h
      · exact Or.inr ⟨hp, by omega⟩
      · exact Or.inl (by omega)
    · rintro (h | ⟨hp, hle⟩)
      · exact ⟨h ▸ hr, h.le⟩
      · exact ⟨hp, by omega⟩
  rw [hset, Finset.prod_insert (by simp), mul_comm]

/-- `smoothPart` is monotone in the bound. -/
theorem smoothPart_mono_left {r s n : ℕ} (hrs : r ≤ s) : smoothPart r n ≤ smoothPart s n := by
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s _ ih =>
      by_cases hmem : s + 1 ∈ n.primeFactors
      · rw [smoothPart_succ_of_mem hmem]
        exact le_trans ih (Nat.le_mul_of_pos_right _ (pow_pos
          (Nat.prime_of_mem_primeFactors hmem).pos _))
      · rw [smoothPart_succ_of_notMem hmem]; exact ih

theorem exists_smoothPart_gt {z n : ℕ} (hzn : z < n) : ∃ r, z < smoothPart r n :=
  ⟨n, by rw [smoothPart_self (by omega)]; exact hzn⟩

open Classical in
/-- **Shiu's level.**  The least smoothness bound at which the smooth part of `n` exceeds `z`. -/
def shiuLevel (z n : ℕ) : ℕ := if h : z < n then Nat.find (exists_smoothPart_gt h) else 0

theorem shiuLevel_spec {z n : ℕ} (hzn : z < n) : z < smoothPart (shiuLevel z n) n := by
  classical
  rw [shiuLevel, dif_pos hzn]
  exact Nat.find_spec (exists_smoothPart_gt hzn)

theorem shiuLevel_pos {z n : ℕ} (hz : 1 ≤ z) (hzn : z < n) : 0 < shiuLevel z n := by
  have h := shiuLevel_spec hzn
  by_contra h0
  have : shiuLevel z n = 0 := by omega
  rw [this, smoothPart_zero_left] at h
  omega

theorem smoothPart_pred_shiuLevel_le {z n : ℕ} (hz : 1 ≤ z) (hzn : z < n) :
    smoothPart (shiuLevel z n - 1) n ≤ z := by
  classical
  have hpos := shiuLevel_pos hz hzn
  rw [shiuLevel, dif_pos hzn] at hpos ⊢
  have hlt : Nat.find (exists_smoothPart_gt hzn) - 1 < Nat.find (exists_smoothPart_gt hzn) := by
    omega
  have := Nat.find_min (exists_smoothPart_gt hzn) hlt
  omega

/-- **Shiu's level is a prime factor of `n`.** -/
theorem shiuLevel_mem_primeFactors {z n : ℕ} (hz : 1 ≤ z) (hzn : z < n) :
    shiuLevel z n ∈ n.primeFactors := by
  have hpos := shiuLevel_pos hz hzn
  have hspec := shiuLevel_spec hzn
  have hpred := smoothPart_pred_shiuLevel_le hz hzn
  by_contra hmem
  have heq : shiuLevel z n = (shiuLevel z n - 1) + 1 := by omega
  rw [heq] at hmem hspec
  rw [smoothPart_succ_of_notMem hmem] at hspec
  omega

/-! ## The two factors of the cut -/

/-- The factor of `n` below Shiu's level. -/
def shiuLow (z n : ℕ) : ℕ := smoothPart (shiuLevel z n - 1) n

/-- The factor of `n` from Shiu's level up. -/
def shiuHigh (z n : ℕ) : ℕ := roughPart (shiuLevel z n - 1) n

theorem shiuLow_mul_shiuHigh {z n : ℕ} (hn : n ≠ 0) : shiuLow z n * shiuHigh z n = n :=
  smoothPart_mul_roughPart hn _

theorem shiuLow_dvd (z n : ℕ) : shiuLow z n ∣ n := smoothPart_dvd _ _

theorem shiuLow_pos (z n : ℕ) : 0 < shiuLow z n := smoothPart_pos _ _

theorem shiuLow_le {z n : ℕ} (hz : 1 ≤ z) (hzn : z < n) : shiuLow z n ≤ z :=
  smoothPart_pred_shiuLevel_le hz hzn

/-- Every prime factor of the high factor is at least Shiu's level. -/
theorem le_of_mem_primeFactors_shiuHigh {z n p : ℕ} (hn : n ≠ 0)
    (hp : p ∈ (shiuHigh z n).primeFactors) : shiuLevel z n ≤ p := by
  rw [shiuHigh, primeFactors_roughPart hn] at hp
  have := (Finset.mem_filter.1 hp).2
  omega

/-- Every prime factor of the low factor is below Shiu's level. -/
theorem lt_of_mem_primeFactors_shiuLow {z n p : ℕ} (hn : n ≠ 0) (hpos : 0 < shiuLevel z n)
    (hp : p ∈ (shiuLow z n).primeFactors) : p < shiuLevel z n := by
  rw [shiuLow, primeFactors_smoothPart hn] at hp
  have := (Finset.mem_filter.1 hp).2
  omega

/-- The high factor has no prime factor below `w` when Shiu's level exceeds `w`. -/
theorem shiuHigh_rough {z n w : ℕ} (hn : n ≠ 0) (hw : w < shiuLevel z n) :
    ∀ p ∈ Nat.primesLE w, ¬ p ∣ shiuHigh z n := by
  intro p hp hdvd
  have hpp := Nat.prime_of_mem_primesLE hp
  have hmem : p ∈ (shiuHigh z n).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hpp, hdvd, (roughPart_pos _ _).ne'⟩
  have := le_of_mem_primeFactors_shiuHigh hn hmem
  have := (Nat.mem_primesLE.1 hp).1
  omega

/-- The distinct prime count of the low factor is at most that of `n`. -/
theorem card_primeFactors_shiuLow_le {z n : ℕ} (hn : n ≠ 0) :
    (shiuLow z n).primeFactors.card ≤ n.primeFactors.card := by
  have := card_primeFactors_roughPart_add hn (shiuLevel z n - 1)
  rw [shiuLow]; omega

/-- **The generic fibre bound.**  If every `n` of `S ⊆ (A, B]` has a divisor `β n ∈ T` whose
cofactor satisfies `R (β n)`, and `f n ≤ g (β n)`, then `∑_S f ≤ ∑_T g(b)·#{m ∈ (A/b, B/b] : R b m}`. -/
theorem sum_le_sum_fibre_count {A B : ℕ} {S T : Finset ℕ} {f g : ℕ → ℝ} (β : ℕ → ℕ)
    (R : ℕ → ℕ → Prop) [∀ b, DecidablePred (R b)] (hg : ∀ b ∈ T, 0 ≤ g b)
    (hS : S ⊆ Finset.Ioc A B) (hβT : ∀ n ∈ S, β n ∈ T) (hβpos : ∀ n ∈ S, 0 < β n)
    (hβdvd : ∀ n ∈ S, β n ∣ n) (hR : ∀ n ∈ S, R (β n) (n / β n))
    (hfg : ∀ n ∈ S, f n ≤ g (β n)) :
    ∑ n ∈ S, f n
      ≤ ∑ b ∈ T, g b * ((Finset.Ioc (A / b) (B / b)).filter (R b)).card := by
  classical
  calc ∑ n ∈ S, f n ≤ ∑ n ∈ S, g (β n) := Finset.sum_le_sum hfg
    _ = ∑ b ∈ T, ∑ n ∈ S with β n = b, g (β n) :=
        (Finset.sum_fiberwise_of_maps_to hβT _).symm
    _ = ∑ b ∈ T, g b * ((S.filter (fun n => β n = b)).card : ℝ) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_congr rfl (fun n hn => by rw [(Finset.mem_filter.1 hn).2]),
          Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ b ∈ T, g b * ((Finset.Ioc (A / b) (B / b)).filter (R b)).card := by
        refine Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left ?_ (hg b hb)
        refine Nat.cast_le.2 (Finset.card_le_card_of_injOn (fun n => n / b) ?_ ?_)
        · intro n hn
          obtain ⟨hnS, hnb⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hn)
          have hb0 : 0 < b := hnb ▸ hβpos n hnS
          have hdvd : b ∣ n := hnb ▸ hβdvd n hnS
          obtain ⟨hAn, hnB⟩ := Finset.mem_Ioc.1 (hS hnS)
          refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨?_, Nat.div_le_div_right hnB⟩, ?_⟩
          · rw [Nat.div_lt_iff_lt_mul hb0, Nat.div_mul_cancel hdvd]; exact hAn
          · have := hR n hnS; rw [hnb] at this; exact this
        · intro x hx y hy hxy
          obtain ⟨hxS, hxb⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
          obtain ⟨hyS, hyb⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
          have hxd : b ∣ x := hxb ▸ hβdvd x hxS
          have hyd : b ∣ y := hyb ▸ hβdvd y hyS
          have hx' : b * (x / b) = x := Nat.mul_div_cancel' hxd
          have hy' : b * (y / b) = y := Nat.mul_div_cancel' hyd
          have hq : x / b = y / b := hxy
          rw [← hx', ← hy', hq]

/-! ## The three cases -/

/-- The tilted weight `t^{ω(n)}`. -/
def omegaTilt (t : ℝ) (n : ℕ) : ℝ := t ^ n.primeFactors.card

theorem omegaTilt_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ omegaTilt t n := pow_nonneg ht _

theorem omegaTilt_le_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) : omegaTilt t n ≤ 1 :=
  pow_le_one₀ ht0 ht1

theorem omegaTilt_le_shiuLow {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z n : ℕ} (hn : n ≠ 0) :
    omegaTilt t n ≤ omegaTilt t (shiuLow z n) :=
  pow_le_pow_of_le_one ht0 ht1 (card_primeFactors_shiuLow_le hn)

theorem div_shiuLow_eq {z n : ℕ} (hn : n ≠ 0) : n / shiuLow z n = shiuHigh z n := by
  have h := shiuLow_mul_shiuHigh (z := z) hn
  exact Nat.div_eq_of_eq_mul_right (shiuLow_pos z n) h.symm

open Classical in
/-- **Case I: Shiu's level above `w`.**  The high factor is `w`-rough. -/
theorem shiu_caseI_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {A y z w : ℕ} (hz : 1 ≤ z)
    (hzA : z ≤ A) :
    ∑ n ∈ (Finset.Ioc A (A + y)).filter (fun n => w < shiuLevel z n), omegaTilt t n
      ≤ ∑ b ∈ Finset.Icc 1 z, omegaTilt t b
          * ((Finset.Ioc (A / b) ((A + y) / b)).filter
              (fun m => ∀ p ∈ Nat.primesLE w, ¬ p ∣ m)).card := by
  refine sum_le_sum_fibre_count (shiuLow z) (fun _ m => ∀ p ∈ Nat.primesLE w, ¬ p ∣ m)
    (fun b _ => omegaTilt_nonneg ht0 b) (Finset.filter_subset _ _) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hmem, -⟩ := Finset.mem_filter.1 hn
    have hzn : z < n := by have := (Finset.mem_Ioc.1 hmem).1; omega
    exact Finset.mem_Icc.2 ⟨shiuLow_pos z n, shiuLow_le hz hzn⟩
  · intro n _; exact shiuLow_pos z n
  · intro n _; exact shiuLow_dvd z n
  · intro n hn
    obtain ⟨hmem, hlev⟩ := Finset.mem_filter.1 hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Ioc.1 hmem).1; omega
    show ∀ p ∈ Nat.primesLE w, ¬ p ∣ n / shiuLow z n
    rw [div_shiuLow_eq hn0]
    exact shiuHigh_rough hn0 hlev
  · intro n hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hn).1).1; omega
    exact omegaTilt_le_shiuLow ht0 ht1 hn0

theorem exists_nat_pow_gt {q : ℕ} (hq : 2 ≤ q) (w : ℕ) : ∃ e : ℕ, w < q ^ e :=
  ⟨w, lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_left hq w)⟩

open Classical in
/-- The least power of `q` exceeding `w`. -/
def shiuPowExp (w q : ℕ) : ℕ := if h : 2 ≤ q then Nat.find (exists_nat_pow_gt h w) else 0

theorem lt_pow_shiuPowExp {w q : ℕ} (hq : 2 ≤ q) : w < q ^ shiuPowExp w q := by
  classical
  rw [shiuPowExp, dif_pos hq]; exact Nat.find_spec (exists_nat_pow_gt hq w)

theorem shiuPowExp_le {w q e : ℕ} (hq : 2 ≤ q) (he : w < q ^ e) : shiuPowExp w q ≤ e := by
  classical
  rw [shiuPowExp, dif_pos hq]; exact Nat.find_min' (exists_nat_pow_gt hq w) he

open Classical in
/-- **Case II: level and low factor both at most `w`.**  Then `n` is divisible by the least power
of a prime `q ≤ w` exceeding `w`. -/
theorem shiu_caseII_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {A y z w : ℕ} (hz : 1 ≤ z)
    (hzA : z ≤ A) (hwz : w * w ≤ z) :
    ∑ n ∈ (Finset.Ioc A (A + y)).filter
        (fun n => shiuLevel z n ≤ w ∧ shiuLow z n ≤ w), omegaTilt t n
      ≤ ∑ q ∈ Nat.primesLE w, ((y : ℝ) / ((q ^ shiuPowExp w q : ℕ) : ℝ) + 1) := by
  set S := (Finset.Ioc A (A + y)).filter (fun n => shiuLevel z n ≤ w ∧ shiuLow z n ≤ w) with hS
  have h1 : ∑ n ∈ S, omegaTilt t n ≤ (S.card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact Finset.sum_le_sum fun n _ => omegaTilt_le_one ht0 ht1 n
  refine h1.trans ?_
  have hsub : S ⊆ (Nat.primesLE w).biUnion
      (fun q => (Finset.Ioc A (A + y)).filter (fun n => q ^ shiuPowExp w q ∣ n)) := by
    intro n hn
    obtain ⟨hmem, hlev, hlow⟩ := Finset.mem_filter.1 hn
    have hAn := (Finset.mem_Ioc.1 hmem).1
    have hzn : z < n := by omega
    have hn0 : n ≠ 0 := by omega
    set q := shiuLevel z n with hq
    have hqpf : q ∈ n.primeFactors := shiuLevel_mem_primeFactors hz hzn
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqpf
    have hqpos : 0 < q := hqp.pos
    refine Finset.mem_biUnion.2 ⟨q, Nat.mem_primesLE.2 ⟨hlev, hqp⟩, Finset.mem_filter.2 ⟨hmem, ?_⟩⟩
    -- the smooth part at the level is the low factor times the full power of `q`
    have hsucc : smoothPart q n = shiuLow z n * q ^ n.factorization q := by
      have hq1 : q = (q - 1) + 1 := by omega
      have := smoothPart_succ_of_mem (r := q - 1) (n := n) (hq1 ▸ hqpf)
      rw [← hq1] at this
      rw [this, shiuLow, hq]
    have hspec : z < smoothPart q n := shiuLevel_spec hzn
    rw [hsucc] at hspec
    have hpow : w < q ^ n.factorization q := by
      by_contra hcon
      push Not at hcon
      have : shiuLow z n * q ^ n.factorization q ≤ w * w := Nat.mul_le_mul hlow hcon
      omega
    have he := shiuPowExp_le hqp.two_le hpow
    exact dvd_trans (pow_dvd_pow q he) (Nat.ordProj_dvd n q)
  have hcard : (S.card : ℝ) ≤ ∑ q ∈ Nat.primesLE w,
      (((Finset.Ioc A (A + y)).filter (fun n => q ^ shiuPowExp w q ∣ n)).card : ℝ) := by
    have := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    exact_mod_cast this
  refine hcard.trans (Finset.sum_le_sum fun q hq => ?_)
  have hqp := Nat.prime_of_mem_primesLE hq
  have hd : 0 < q ^ shiuPowExp w q := pow_pos hqp.pos _
  have habs := abs_card_filter_dvd_Ioc_sub_lt (q ^ shiuPowExp w q) A (A + y) hd (by omega)
  have hlen : (((A + y : ℕ) : ℝ) - (A : ℝ)) = (y : ℝ) := by push_cast; ring
  rw [hlen] at habs
  have := (abs_lt.1 habs).2
  linarith

/-- The largest prime factor (zero for `1`). -/
def largestPrime (b : ℕ) : ℕ := b.primeFactors.sup id

theorem le_largestPrime {b p : ℕ} (hp : p ∈ b.primeFactors) : p ≤ largestPrime b :=
  Finset.le_sup (f := id) hp

theorem largestPrime_lt_shiuLevel {z n : ℕ} (hn : n ≠ 0) (hpos : 0 < shiuLevel z n) :
    largestPrime (shiuLow z n) < shiuLevel z n := by
  rw [largestPrime, Finset.sup_lt_iff hpos]
  intro p hp
  exact lt_of_mem_primeFactors_shiuLow hn hpos hp

open Classical in
/-- **Case III: level at most `w`, low factor above `w`.**  The high factor has no prime factor up
to the largest prime of the low factor. -/
theorem shiu_caseIII_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {A y z w : ℕ} (hz : 1 ≤ z)
    (hzA : z ≤ A) :
    ∑ n ∈ (Finset.Ioc A (A + y)).filter
        (fun n => shiuLevel z n ≤ w ∧ w < shiuLow z n), omegaTilt t n
      ≤ ∑ b ∈ Finset.Ioc w z, omegaTilt t b
          * ((Finset.Ioc (A / b) ((A + y) / b)).filter
              (fun m => ∀ p ∈ Nat.primesLE (largestPrime b), ¬ p ∣ m)).card := by
  refine sum_le_sum_fibre_count (shiuLow z)
    (fun b m => ∀ p ∈ Nat.primesLE (largestPrime b), ¬ p ∣ m)
    (fun b _ => omegaTilt_nonneg ht0 b) (Finset.filter_subset _ _) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hmem, -, hlow⟩ := Finset.mem_filter.1 hn
    have hzn : z < n := by have := (Finset.mem_Ioc.1 hmem).1; omega
    exact Finset.mem_Ioc.2 ⟨hlow, shiuLow_le hz hzn⟩
  · intro n _; exact shiuLow_pos z n
  · intro n _; exact shiuLow_dvd z n
  · intro n hn
    obtain ⟨hmem, -, -⟩ := Finset.mem_filter.1 hn
    have hAn := (Finset.mem_Ioc.1 hmem).1
    have hzn : z < n := by omega
    have hn0 : n ≠ 0 := by omega
    have hpos := shiuLevel_pos hz hzn
    show ∀ p ∈ Nat.primesLE (largestPrime (shiuLow z n)), ¬ p ∣ n / shiuLow z n
    rw [div_shiuLow_eq hn0]
    exact shiuHigh_rough hn0 (largestPrime_lt_shiuLevel hn0 hpos)
  · intro n hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hn).1).1; omega
    exact omegaTilt_le_shiuLow ht0 ht1 hn0

open Classical in
/-- **The three cases cover the interval.** -/
theorem sum_omegaTilt_Ioc_eq_cases (t : ℝ) (A y z w : ℕ) :
    ∑ n ∈ Finset.Ioc A (A + y), omegaTilt t n
      = ∑ n ∈ (Finset.Ioc A (A + y)).filter (fun n => w < shiuLevel z n), omegaTilt t n
        + ∑ n ∈ (Finset.Ioc A (A + y)).filter
            (fun n => shiuLevel z n ≤ w ∧ shiuLow z n ≤ w), omegaTilt t n
        + ∑ n ∈ (Finset.Ioc A (A + y)).filter
            (fun n => shiuLevel z n ≤ w ∧ w < shiuLow z n), omegaTilt t n := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc A (A + y))
    (fun n => w < shiuLevel z n), add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Ioc A (A + y)).filter
    (fun n => ¬ w < shiuLevel z n)) (fun n => shiuLow z n ≤ w), Finset.filter_filter,
    Finset.filter_filter]
  congr 1
  · refine Finset.sum_congr (Finset.filter_congr fun n _ => ?_) fun _ _ => rfl
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · refine Finset.sum_congr (Finset.filter_congr fun n _ => ?_) fun _ _ => rfl
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩

/-! ## Rankin tails -/

/-- **Rankin tail.**  Over `W`-smooth `b > w` (up to any bound), `∑ t^{ω(b)}/b` is at most
`w^{-1/log W}·exp(t(log log W + C))`. -/
theorem sum_omegaTilt_div_tail_le {t : ℝ} (ht0 : 0 ≤ t) {W Y w : ℕ} (hW : 4 ≤ Real.log W)
    (hw : 1 ≤ w) (B : Finset ℕ) (hB : B ⊆ smoothUpTo (Nat.primesLE W) Y)
    (hBw : ∀ b ∈ B, w ≤ b) :
    ∑ b ∈ B, omegaTilt t b / (b : ℝ)
      ≤ (w : ℝ) ^ (-(1 / Real.log W)) * Real.exp (t * (logLog W + rankinTiltConst)) := by
  set σ : ℝ := 1 / Real.log W with hσdef
  have hσ0 : 0 ≤ σ := by rw [hσdef]; exact div_nonneg zero_le_one (by linarith)
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hterm : ∀ b ∈ B, omegaTilt t b / (b : ℝ)
      ≤ (w : ℝ) ^ (-σ) * rankinTiltWeight t σ b := by
    intro b hb
    have hbR : (0 : ℝ) < (b : ℝ) := by
      have := hBw b hb; exact_mod_cast (lt_of_lt_of_le hw this)
    have hwb : (w : ℝ) ≤ (b : ℝ) := by exact_mod_cast hBw b hb
    have hsplit : omegaTilt t b / (b : ℝ) = rankinTiltWeight t σ b * (b : ℝ) ^ (-σ) := by
      rw [omegaTilt, rankinTiltWeight, mul_assoc, ← Real.rpow_add hbR]
      rw [show σ - 1 + -σ = -1 by ring, Real.rpow_neg_one, div_eq_mul_inv]
    rw [hsplit, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hwR hwb (by linarith)) (rankinTiltWeight_nonneg ht0 σ b)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hwR.le _)
  refine le_trans ?_ (sum_smooth_rankinTilt_le ht0 hW Y)
  exact Finset.sum_le_sum_of_subset_of_nonneg hB fun b _ _ => rankinTiltWeight_nonneg ht0 σ b

theorem mem_smoothUpTo_of_le {W Y b : ℕ} (hb1 : 1 ≤ b) (hbY : b ≤ Y)
    (hsmooth : ∀ p ∈ b.primeFactors, p ≤ W) : b ∈ smoothUpTo (Nat.primesLE W) Y := by
  refine mem_smoothUpTo.2 ⟨⟨hb1, hbY⟩, fun p hp => ?_⟩
  exact Nat.mem_primesLE.2 ⟨hsmooth p hp, Nat.prime_of_mem_primeFactors hp⟩

/-- **The harmonic tilted sum up to `z`.** -/
theorem sum_Icc_omegaTilt_div_le {t : ℝ} (ht0 : 0 ≤ t) {z : ℕ} (hz : 4 ≤ Real.log z) :
    ∑ b ∈ Finset.Icc 1 z, omegaTilt t b / (b : ℝ)
      ≤ Real.exp (t * (logLog z + rankinTiltConst)) := by
  have h := sum_omegaTilt_div_tail_le (t := t) (W := z) (Y := z) (w := 1) ht0 hz le_rfl
    (Finset.Icc 1 z)
    (fun b hb => mem_smoothUpTo_of_le (Finset.mem_Icc.1 hb).1 (Finset.mem_Icc.1 hb).2
      (fun p hp => le_trans (Nat.le_of_mem_primeFactors hp) (Finset.mem_Icc.1 hb).2))
    (fun b hb => (Finset.mem_Icc.1 hb).1)
  simpa using h

/-- `(j+1) e^{-j/2} ≤ 4 e^{-j/4}`. -/
theorem succ_mul_exp_neg_half_le (j : ℕ) :
    ((j : ℝ) + 1) * Real.exp (-(j : ℝ) / 2) ≤ 4 * Real.exp (-(j : ℝ) / 4) := by
  have h1 : (j : ℝ) + 1 ≤ 4 * Real.exp ((j : ℝ) / 4) := by
    have := Real.add_one_le_exp ((j : ℝ) / 4)
    linarith
  have h2 : Real.exp (-(j : ℝ) / 2) = Real.exp (-(j : ℝ) / 4) * Real.exp (-(j : ℝ) / 4) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp ((j : ℝ) / 4) * Real.exp (-(j : ℝ) / 4) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  rw [h2]
  have he : 0 ≤ Real.exp (-(j : ℝ) / 4) := (Real.exp_pos _).le
  calc ((j : ℝ) + 1) * (Real.exp (-(j : ℝ) / 4) * Real.exp (-(j : ℝ) / 4))
      ≤ 4 * Real.exp ((j : ℝ) / 4) * (Real.exp (-(j : ℝ) / 4) * Real.exp (-(j : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg he he)
    _ = 4 * Real.exp (-(j : ℝ) / 4) * (Real.exp ((j : ℝ) / 4) * Real.exp (-(j : ℝ) / 4)) := by
        ring
    _ = 4 * Real.exp (-(j : ℝ) / 4) := by rw [h3, mul_one]

/-- `∑_{j ≥ 1} e^{-j/4} ≤ 5`. -/
theorem sum_exp_neg_quarter_le (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, Real.exp (-(j : ℝ) / 4) ≤ 5 := by
  set r : ℝ := Real.exp (-(1 : ℝ) / 4) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 4 / 5 := by
    have h := Real.add_one_le_exp ((1 : ℝ) / 4)
    rw [hr, show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) by ring, Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hterm : ∀ j ∈ Finset.Icc 1 J, Real.exp (-(j : ℝ) / 4) ≤ r ^ j := by
    intro j _
    rw [hr, ← Real.exp_nat_mul]; apply le_of_eq; congr 1; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsub : ∑ j ∈ Finset.Icc 1 J, r ^ j ≤ ∑ j ∈ Finset.range (J + 1), r ^ j :=
    Finset.sum_le_sum_of_subset_of_nonneg (by
      intro j hj; exact Finset.mem_range.2 (by have := (Finset.mem_Icc.1 hj).2; omega))
      (fun j _ _ => pow_nonneg hr0 j)
  refine hsub.trans ?_
  rw [geom_sum_eq (by linarith) (J + 1)]
  rw [show (r ^ (J + 1) - 1) / (r - 1) = (1 - r ^ (J + 1)) / (1 - r) by
    rw [← neg_div_neg_eq, neg_sub, neg_sub]]
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ r ^ (J + 1) := pow_nonneg hr0 _
  linarith

theorem four_le_log_55 : (4 : ℝ) ≤ Real.log 55 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 4 = Real.exp 1 ^ (4 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  have h2 := Real.exp_one_lt_d9
  have h3 : Real.exp 1 ^ (4 : ℕ) ≤ (2.7182818286 : ℝ) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 4
  refine h3.trans ?_
  norm_num

theorem two_le_largestPrime {b : ℕ} (hb : 2 ≤ b) : 2 ≤ largestPrime b := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.2 (by omega : 1 < b)
  exact le_trans (Nat.prime_of_mem_primeFactors hp).two_le (le_largestPrime hp)

theorem largestPrime_le (b : ℕ) : largestPrime b ≤ b := by
  rw [largestPrime, Finset.sup_le_iff]
  intro p hp
  exact Nat.le_of_mem_primeFactors hp

theorem le_largestPrime_of_mem {b p : ℕ} (hp : p ∈ b.primeFactors) : p ≤ largestPrime b :=
  le_largestPrime hp

/-- **The case-III sum.**  `∑_{w < b ≤ z} t^{ω(b)}/(b log P⁺(b))` is `O((log z)^{t-1})`, plus a
tail from the `55`-smooth `b`. -/
theorem sum_omegaTilt_div_log_largestPrime_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {w z : ℕ}
    (hw2 : 2 ≤ w) (hz : 4 ≤ Real.log z) (hwlog : Real.log z - 1 ≤ 2 * Real.log w) :
    ∑ b ∈ Finset.Ioc w z, omegaTilt t b / ((b : ℝ) * Real.log (largestPrime b))
      ≤ 20 * Real.exp (1 / 8) * Real.exp (t * (logLog z + rankinTiltConst)) / Real.log z
        + (1 / Real.log 2) * ((w : ℝ) ^ (-(1 / Real.log 55))
            * Real.exp (1 * (logLog 55 + rankinTiltConst))) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 < Real.log (z : ℝ) := by linarith
  have h55 := four_le_log_55
  have hbase : ∀ b ∈ Finset.Ioc w z, 2 ≤ b ∧ b ≤ z ∧ 2 ≤ largestPrime b := by
    intro b hb
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hb
    exact ⟨by omega, h2, two_le_largestPrime (by omega)⟩
  have hlogP : ∀ b ∈ Finset.Ioc w z, Real.log 2 ≤ Real.log (largestPrime b) := by
    intro b hb
    exact Real.log_le_log (by norm_num) (by exact_mod_cast (hbase b hb).2.2)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc w z) (fun b => largestPrime b < 55),
    add_comm]
  refine add_le_add ?_ ?_
  · -- the large largest primes, grouped by `⌊log z / log P⁺(b)⌋`
    set J : ℕ := ⌊Real.log z / Real.log 55⌋₊ with hJ
    set jf : ℕ → ℕ := fun b => ⌊Real.log z / Real.log (largestPrime b)⌋₊ with hjf
    set L := (Finset.Ioc w z).filter (fun b => ¬ largestPrime b < 55) with hL
    have hmaps : ∀ b ∈ L, jf b ∈ Finset.Icc 1 J := by
      intro b hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
      obtain ⟨hb2', hbz, -⟩ := hbase b hb1
      have hP55 : (55 : ℝ) ≤ (largestPrime b : ℝ) := by
        have : 55 ≤ largestPrime b := by omega
        exact_mod_cast this
      have hlogP55 : Real.log 55 ≤ Real.log (largestPrime b) := Real.log_le_log (by norm_num) hP55
      have hPz : Real.log (largestPrime b) ≤ Real.log z :=
        Real.log_le_log (by linarith) (by exact_mod_cast le_trans (largestPrime_le b) hbz)
      have hlogPpos : 0 < Real.log (largestPrime b) := by linarith
      refine Finset.mem_Icc.2 ⟨?_, ?_⟩
      · rw [hjf, Nat.one_le_floor_iff, le_div_iff₀ hlogPpos, one_mul]; exact hPz
      · exact Nat.floor_le_floor (div_le_div_of_nonneg_left hL0.le (by linarith) hlogP55)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hfib : ∀ j ∈ Finset.Icc 1 J,
        ∑ b ∈ L with jf b = j, omegaTilt t b / ((b : ℝ) * Real.log (largestPrime b))
          ≤ 4 * Real.exp (-(j : ℝ) / 4)
            * (Real.exp (1 / 8) * Real.exp (t * (logLog z + rankinTiltConst)) / Real.log z) := by
      intro j hj
      obtain ⟨hj1, hjJ⟩ := Finset.mem_Icc.1 hj
      have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
      set Wj : ℕ := ⌊Real.exp (Real.log z / j)⌋₊ with hWj
      set F := L.filter (fun b => jf b = j) with hF
      by_cases hne : F.Nonempty
      swap
      · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
        positivity
      obtain ⟨b₀, hb₀⟩ := hne
      -- every member of the fibre is `Wj`-smooth, with `1/log P⁺ ≤ (j+1)/log z`
      have hmem : ∀ b ∈ F, largestPrime b ≤ Wj
          ∧ 1 / Real.log (largestPrime b) ≤ ((j : ℝ) + 1) / Real.log z
          ∧ 55 ≤ largestPrime b := by
        intro b hb
        obtain ⟨hbL, hbj⟩ := Finset.mem_filter.1 hb
        obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hbL
        have hP55 : 55 ≤ largestPrime b := by omega
        have hP55R : (55 : ℝ) ≤ (largestPrime b : ℝ) := by exact_mod_cast hP55
        have hlogPpos : 0 < Real.log (largestPrime b) := by
          have := Real.log_le_log (by norm_num) hP55R; linarith
        have hjeq : ⌊Real.log z / Real.log (largestPrime b)⌋₊ = j := hbj
        have hfl : (j : ℝ) ≤ Real.log z / Real.log (largestPrime b) := by
          have := Nat.floor_le (div_nonneg hL0.le hlogPpos.le)
          rw [hjeq] at this; exact this
        have hlt : Real.log z / Real.log (largestPrime b) < (j : ℝ) + 1 := by
          have := Nat.lt_floor_add_one (Real.log z / Real.log (largestPrime b))
          rw [hjeq] at this; exact this
        refine ⟨?_, ?_, hP55⟩
        · refine Nat.le_floor ?_
          rw [← Real.exp_log (show (0 : ℝ) < (largestPrime b : ℝ) by linarith)]
          refine Real.exp_le_exp.2 ?_
          rw [le_div_iff₀ (by linarith), mul_comm, ← le_div_iff₀ hlogPpos]
          exact hfl
        · rw [div_le_div_iff₀ hlogPpos hL0, one_mul]
          rw [div_lt_iff₀ hlogPpos] at hlt
          linarith
      have hW55 : 55 ≤ Wj := le_trans (hmem b₀ hb₀).2.2 (hmem b₀ hb₀).1
      have hW55R : (55 : ℝ) ≤ (Wj : ℝ) := by exact_mod_cast hW55
      have hlogW : 4 ≤ Real.log Wj := le_trans h55 (Real.log_le_log (by norm_num) hW55R)
      have hWjle : Real.log Wj ≤ Real.log z / j := by
        have hWpos : (0 : ℝ) < (Wj : ℝ) := by linarith
        have := Nat.floor_le (Real.exp_pos (Real.log z / j)).le
        rw [← hWj] at this
        calc Real.log Wj ≤ Real.log (Real.exp (Real.log z / j)) := Real.log_le_log hWpos this
          _ = Real.log z / j := Real.log_exp _
      -- the fibre against the Rankin tail at `Wj`
      have hstep : ∑ b ∈ F, omegaTilt t b / ((b : ℝ) * Real.log (largestPrime b))
          ≤ ((j : ℝ) + 1) / Real.log z * ∑ b ∈ F, omegaTilt t b / (b : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun b hb => ?_
        obtain ⟨-, h2, -⟩ := hmem b hb
        have hbR : (0 : ℝ) < (b : ℝ) := by
          have := (hbase b (Finset.mem_filter.1 (Finset.mem_filter.1 hb).1).1).1
          exact_mod_cast (show 0 < b by omega)
        have hω := omegaTilt_nonneg ht0 b
        have e : omegaTilt t b / ((b : ℝ) * Real.log (largestPrime b))
            = omegaTilt t b / (b : ℝ) * (1 / Real.log (largestPrime b)) := by
          rw [mul_one_div, div_div]
        rw [e, mul_comm (((j : ℝ) + 1) / Real.log z)]
        exact mul_le_mul_of_nonneg_left h2 (div_nonneg hω hbR.le)
      have htail := sum_omegaTilt_div_tail_le (t := t) (W := Wj) (Y := z) (w := w) ht0 hlogW
        (by omega) F
        (fun b hb => by
          obtain ⟨hPW, -, -⟩ := hmem b hb
          have hb1 := (Finset.mem_filter.1 (Finset.mem_filter.1 hb).1).1
          obtain ⟨hb2, hbz, -⟩ := hbase b hb1
          exact mem_smoothUpTo_of_le (by omega) hbz
            (fun p hp => le_trans (le_largestPrime_of_mem hp) hPW))
        (fun b hb => by
          have := (Finset.mem_Ioc.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hb).1).1).1
          omega)
      -- the Rankin factor
      have hwpow : (w : ℝ) ^ (-(1 / Real.log Wj)) ≤ Real.exp (1 / 8 - (j : ℝ) / 2) := by
        have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast (show 0 < w by omega)
        rw [Real.rpow_def_of_pos hwR]
        refine Real.exp_le_exp.2 ?_
        have hlogW0 : 0 < Real.log Wj := by linarith
        have hσ : (j : ℝ) / Real.log z ≤ 1 / Real.log Wj := by
          rw [div_le_div_iff₀ hL0 hlogW0, one_mul]
          rw [le_div_iff₀ hj0] at hWjle
          linarith
        have hlogw : 0 ≤ Real.log w := Real.log_nonneg (by exact_mod_cast (show 1 ≤ w by omega))
        have hJle : (j : ℝ) ≤ Real.log z / 4 := by
          have h1 : (j : ℝ) ≤ Real.log z / Real.log 55 := by
            have := Nat.floor_le (div_nonneg hL0.le (by linarith : (0 : ℝ) ≤ Real.log 55))
            rw [← hJ] at this
            exact le_trans (by exact_mod_cast hjJ) this
          exact le_trans h1 (div_le_div_of_nonneg_left hL0.le (by norm_num) h55)
        have hkey : (j : ℝ) / Real.log z * Real.log w ≥ (j : ℝ) / 2 - 1 / 8 := by
          have : (j : ℝ) / Real.log z * Real.log w
              ≥ (j : ℝ) / Real.log z * ((Real.log z - 1) / 2) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have e : (j : ℝ) / Real.log z * ((Real.log z - 1) / 2)
              = (j : ℝ) / 2 - (j : ℝ) / (2 * Real.log z) := by field_simp
          have h2 : (j : ℝ) / (2 * Real.log z) ≤ 1 / 8 := by
            rw [div_le_iff₀ (by positivity)]; linarith
          linarith
        have := mul_le_mul_of_nonneg_right hσ hlogw
        nlinarith [hkey, this]
      have hexpW : Real.exp (t * (logLog Wj + rankinTiltConst))
          ≤ Real.exp (t * (logLog z + rankinTiltConst)) := by
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ ht0)
        have hlogW0 : 0 < Real.log Wj := by linarith
        have : logLog Wj ≤ logLog z := by
          rw [logLog, logLog]
          refine Real.log_le_log hlogW0 (le_trans hWjle ?_)
          exact div_le_self hL0.le hjR
        linarith
      have hcomb := succ_mul_exp_neg_half_le j
      calc ∑ b ∈ F, omegaTilt t b / ((b : ℝ) * Real.log (largestPrime b))
          ≤ ((j : ℝ) + 1) / Real.log z * ∑ b ∈ F, omegaTilt t b / (b : ℝ) := hstep
        _ ≤ ((j : ℝ) + 1) / Real.log z * (Real.exp (1 / 8 - (j : ℝ) / 2)
              * Real.exp (t * (logLog z + rankinTiltConst))) := by
            refine mul_le_mul_of_nonneg_left (htail.trans ?_) (by positivity)
            exact mul_le_mul hwpow hexpW (Real.exp_pos _).le (Real.exp_pos _).le
        _ = (((j : ℝ) + 1) * Real.exp (-(j : ℝ) / 2))
              * (Real.exp (1 / 8) * Real.exp (t * (logLog z + rankinTiltConst)) / Real.log z) := by
            rw [show (1 : ℝ) / 8 - (j : ℝ) / 2 = 1 / 8 + -(j : ℝ) / 2 by ring, Real.exp_add]
            ring
        _ ≤ 4 * Real.exp (-(j : ℝ) / 4)
              * (Real.exp (1 / 8) * Real.exp (t * (logLog z + rankinTiltConst)) / Real.log z) :=
            mul_le_mul_of_nonneg_right hcomb (by positivity)
    refine (Finset.sum_le_sum hfib).trans ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have := sum_exp_neg_quarter_le J
    have hpos : 0 ≤ Real.exp (1 / 8) * Real.exp (t * (logLog z + rankinTiltConst)) / Real.log z :=
      by positivity
    calc (4 * ∑ j ∈ Finset.Icc 1 J, Real.exp (-(j : ℝ) / 4))
          * (Real.exp (1 / 8) * Real.exp (t * (logLog z + rankinTiltConst)) / Real.log z)
        ≤ (4 * 5) * (Real.exp (1 / 8) * Real.exp (t * (logLog z + rankinTiltConst))
            / Real.log z) := mul_le_mul_of_nonneg_right (by linarith) hpos
      _ = 20 * Real.exp (1 / 8) * Real.exp (t * (logLog z + rankinTiltConst)) / Real.log z := by
          ring
  · -- the `55`-smooth low factors
    set Sm := (Finset.Ioc w z).filter (fun b => largestPrime b < 55) with hSm
    have hterm : ∀ b ∈ Sm, omegaTilt t b / ((b : ℝ) * Real.log (largestPrime b))
        ≤ (1 / Real.log 2) * (omegaTilt 1 b / (b : ℝ)) := by
      intro b hb
      have hb1 := (Finset.mem_filter.1 hb).1
      have hbR : (0 : ℝ) < (b : ℝ) := by
        have := (hbase b hb1).1; exact_mod_cast (show 0 < b by omega)
      have hlP := hlogP b hb1
      have hω : omegaTilt t b ≤ 1 := omegaTilt_le_one ht0 ht1 b
      have h1 : omegaTilt 1 b = 1 := by simp [omegaTilt]
      rw [h1]
      calc omegaTilt t b / ((b : ℝ) * Real.log (largestPrime b))
          ≤ 1 / ((b : ℝ) * Real.log 2) :=
            div_le_div₀ zero_le_one hω (by positivity)
              (mul_le_mul_of_nonneg_left hlP hbR.le)
        _ = 1 / Real.log 2 * (1 / (b : ℝ)) := by
            rw [one_div_mul_one_div, mul_comm]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact sum_omegaTilt_div_tail_le (t := 1) (W := 55) (Y := z) (w := w) zero_le_one
      (by exact_mod_cast h55) (by omega) Sm
      (fun b hb => by
        have hb1 := (Finset.mem_filter.1 hb).1
        obtain ⟨hb2, hbz, -⟩ := hbase b hb1
        exact mem_smoothUpTo_of_le (by omega) hbz (fun p hp =>
          le_of_lt (lt_of_le_of_lt (le_largestPrime_of_mem hp) (Finset.mem_filter.1 hb).2)))
      (fun b hb => by
        have := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hb).1).1; omega)

end

end RHTower.Sieve
