import GaloisForLFunctions.SurfaceOfSpecZ.TwoFrobeniiSeeEveryConfiguration
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-!
# Two Frobenii need an attained top at single degrees

`TwoFrobeniiSuffice` samples the degrees `pᵃqᵇ` and needs an attained maximal real part; the pairs
`log m − log n` of `TwoFrobeniiSeeEveryConfiguration` need none. In the positive-weight model of
`RHTower.WeilLagSingleBaseWolffConfiguration` the single degrees do not suffice:

**Theorem** (`exists_twoPrime_samples_bddBelow_nonattained`). For primes `p, q` and `Θ > 0` there are
depths `x_k ∈ (0, Θ)` increasing to `Θ` (not attained), ordinates `γ_k → ∞` and positive summable
weights `c_k` such that the symmetric samples

  `Φ(λ) = Σ_k c_k (e^{x_k λ} + e^{−x_k λ}) cos(γ_k λ)`

of the points `½ ± x_k ± iγ_k` satisfy `Φ(a log p + b log q) ≥ −2` for all `a, b ≥ 0`.

**Construction.** `x_k = Θ(1 − 2^{−(k+1)})`; weights and windows recursively,
`c_{k+1} = (c_k/16) e^{−ΘU_k}`, `U_{k+1} = max(U_k + 1, log(16/c_{k+1})/(x_{k+1} − x_k))`. On
`[U_k, U_{k+1}]` the quartets `k, k+1` dominate: the earlier ones by `e^{−(x_k − x_j)U_k} ≤ c_k/16`, the
later ones by `c_{k+2} = (c_{k+1}/16)e^{−ΘU_{k+1}}`. The ordinate `γ_k = 2πN_k/log p`, with
`|N_k log q/log p − r_k| ≤ 1/Q_k` by Dirichlet's approximation and `Q_k ≥ 6U_{k+1}/log q`, keeps
`γ_k (a log p + b log q)` within `π/3` of `2πℤ` for every degree up to `U_{k+1}`, so
`cos(γ_k λ) ≥ ½` there. Hence `Φ ≥ (3/8)(c_k e^{x_kλ} + c_{k+1}e^{x_{k+1}λ}) − Σ c ≥ −2`
(`samples_ge_of_resonant`).

**Finitely many Frobenii** (`exists_finPrimes_samples_bddBelow_nonattained`). The same holds at the
degrees `Π P_i^{a_i}` of any finite set of primes, with simultaneous Dirichlet approximation
(`HTGeometry.exists_simultaneous_dirichlet`) of the ratios `log P_i/log P_0`: no finitely generated
monoid of degrees removes the attained top, while the primes with their power-saving gaps do
(`TheGapMethodIterates`).
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

namespace TwoPrimeWolff

variable (Θ : ℝ)

/-- The depths `x_k = Θ(1 − 2^{−(k+1)})`. -/
def depth (k : ℕ) : ℝ := Θ * (1 - (1 / 2 : ℝ) ^ (k + 1))

/-- Weights and window starts, recursively. -/
def state : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | k + 1 =>
    ((state k).1 / 16 * Real.exp (-(Θ * (state k).2)),
      max ((state k).2 + 1)
        (Real.log (16 / ((state k).1 / 16 * Real.exp (-(Θ * (state k).2)))) /
          (Θ * (1 / 2 : ℝ) ^ (k + 2))))

/-- The weight `c_k`. -/
def weight (k : ℕ) : ℝ := (state Θ k).1

/-- The window start `U_k`. -/
def start (k : ℕ) : ℝ := (state Θ k).2

theorem weight_zero : weight Θ 0 = 1 := rfl

theorem start_zero : start Θ 0 = 0 := rfl

theorem weight_succ (k : ℕ) :
    weight Θ (k + 1) = weight Θ k / 16 * Real.exp (-(Θ * start Θ k)) := rfl

theorem start_succ (k : ℕ) :
    start Θ (k + 1) = max (start Θ k + 1)
      (Real.log (16 / weight Θ (k + 1)) / (Θ * (1 / 2 : ℝ) ^ (k + 2))) := rfl

theorem weight_pos (k : ℕ) : 0 < weight Θ k := by
  induction k with
  | zero => rw [weight_zero]; norm_num
  | succ k ih => rw [weight_succ]; positivity

theorem start_succ_ge (k : ℕ) : start Θ k + 1 ≤ start Θ (k + 1) := by
  rw [start_succ]; exact le_max_left _ _

theorem nat_le_start (k : ℕ) : (k : ℝ) ≤ start Θ k := by
  induction k with
  | zero => rw [start_zero]; simp
  | succ k ih => push_cast; linarith [start_succ_ge Θ k]

theorem start_nonneg (k : ℕ) : 0 ≤ start Θ k := (Nat.cast_nonneg k).trans (nat_le_start Θ k)

theorem start_mono {j k : ℕ} (hjk : j ≤ k) : start Θ j ≤ start Θ k := by
  induction k with
  | zero => rw [Nat.le_zero.mp hjk]
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · linarith [ih (Nat.lt_succ_iff.mp h), start_succ_ge Θ k]
    · rw [le_antisymm hjk h]

variable {Θ}

theorem weight_succ_le (hΘ : 0 ≤ Θ) (k : ℕ) : weight Θ (k + 1) ≤ weight Θ k / 16 := by
  rw [weight_succ]
  have h1 : Real.exp (-(Θ * start Θ k)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := mul_nonneg hΘ (start_nonneg Θ k); linarith)
  have h2 : 0 ≤ weight Θ k / 16 := by have := weight_pos Θ k; positivity
  calc weight Θ k / 16 * Real.exp (-(Θ * start Θ k)) ≤ weight Θ k / 16 * 1 :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = weight Θ k / 16 := mul_one _

theorem weight_add_le (hΘ : 0 ≤ Θ) (m i : ℕ) : weight Θ (m + i) ≤ weight Θ m * (1 / 16) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [← add_assoc]
    calc weight Θ (m + i + 1) ≤ weight Θ (m + i) / 16 := weight_succ_le hΘ _
      _ ≤ weight Θ m * (1 / 16) ^ i / 16 := by linarith
      _ = weight Θ m * (1 / 16) ^ (i + 1) := by ring

theorem summable_geom16 : Summable fun i : ℕ => (1 / 16 : ℝ) ^ i :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem tsum_geom16 : ∑' i : ℕ, (1 / 16 : ℝ) ^ i = 16 / 15 := by
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num

theorem summable_weight_add (hΘ : 0 ≤ Θ) (m : ℕ) : Summable fun i => weight Θ (m + i) :=
  Summable.of_nonneg_of_le (fun _ => (weight_pos Θ _).le) (weight_add_le hΘ m)
    (summable_geom16.mul_left _)

theorem summable_weight (hΘ : 0 ≤ Θ) : Summable (weight Θ) := by
  simpa using summable_weight_add hΘ 0

/-- **Tails.** `Σ_{i ≥ 0} c_{m+i} ≤ 2c_m`. -/
theorem tsum_weight_add_le (hΘ : 0 ≤ Θ) (m : ℕ) : ∑' i, weight Θ (m + i) ≤ 2 * weight Θ m := by
  calc ∑' i, weight Θ (m + i) ≤ ∑' i, weight Θ m * (1 / 16 : ℝ) ^ i :=
        Summable.tsum_le_tsum (weight_add_le hΘ m) (summable_weight_add hΘ m)
          (summable_geom16.mul_left _)
    _ = weight Θ m * (16 / 15) := by rw [tsum_mul_left, tsum_geom16]
    _ ≤ 2 * weight Θ m := by have := weight_pos Θ m; nlinarith

theorem tsum_weight_le (hΘ : 0 ≤ Θ) : ∑' k, weight Θ k ≤ 2 := by
  have := tsum_weight_add_le hΘ 0
  simp only [zero_add] at this
  rw [weight_zero] at this
  linarith

/-- **Heads.** `Σ_{j < k} c_j ≤ 2`. -/
theorem sum_range_weight_le (hΘ : 0 ≤ Θ) (k : ℕ) : ∑ j ∈ Finset.range k, weight Θ j ≤ 2 :=
  ((summable_weight hΘ).sum_le_tsum _ (fun j _ => (weight_pos Θ j).le)).trans (tsum_weight_le hΘ)

/-- **The window condition.** `e^{−(x_{k+1} − x_k) U_{k+1}} ≤ c_{k+1}/16`. -/
theorem exp_window_le (hΘ : 0 < Θ) (k : ℕ) :
    Real.exp (-(Θ * (1 / 2 : ℝ) ^ (k + 2) * start Θ (k + 1))) ≤ weight Θ (k + 1) / 16 := by
  have hd : 0 < Θ * (1 / 2 : ℝ) ^ (k + 2) := by positivity
  have hw := weight_pos Θ (k + 1)
  have h1 : Real.log (16 / weight Θ (k + 1)) / (Θ * (1 / 2 : ℝ) ^ (k + 2)) ≤ start Θ (k + 1) := by
    rw [start_succ]; exact le_max_right _ _
  rw [div_le_iff₀ hd] at h1
  have h2 : Real.exp (-(Θ * (1 / 2 : ℝ) ^ (k + 2) * start Θ (k + 1))) ≤
      Real.exp (-Real.log (16 / weight Θ (k + 1))) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-Real.log (16 / weight Θ (k + 1))) = weight Θ (k + 1) / 16 := by
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  exact h2.trans h3.le

theorem depth_pos (hΘ : 0 < Θ) (k : ℕ) : 0 < depth Θ k := by
  unfold depth
  have : (1 / 2 : ℝ) ^ (k + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have : 0 < 1 - (1 / 2 : ℝ) ^ (k + 1) := by linarith
  positivity

theorem depth_lt (hΘ : 0 < Θ) (k : ℕ) : depth Θ k < Θ := by
  unfold depth
  have : 0 < (1 / 2 : ℝ) ^ (k + 1) := by positivity
  nlinarith

theorem depth_le_of_le (hΘ : 0 ≤ Θ) {j k : ℕ} (hjk : j ≤ k) : depth Θ j ≤ depth Θ k := by
  unfold depth
  have : (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ (j + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  nlinarith

theorem strictMono_depth (hΘ : 0 < Θ) : StrictMono (depth Θ) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  unfold depth
  have : (1 / 2 : ℝ) ^ (k + 1 + 1) < (1 / 2 : ℝ) ^ (k + 1) :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
  nlinarith

/-- **The gap below `x_k`.** For `j < k`, `x_k − x_j ≥ Θ 2^{−(k+1)}`. -/
theorem depth_gap (hΘ : 0 ≤ Θ) {j k : ℕ} (hjk : j < k) :
    Θ * (1 / 2 : ℝ) ^ (k + 1) ≤ depth Θ k - depth Θ j := by
  unfold depth
  have h1 : (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ (j + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k / 2 := by rw [pow_succ]; ring
  nlinarith

theorem exists_depth_gt (hΘ : 0 < Θ) {β : ℝ} (hβ : β < Θ) : ∃ k, β < depth Θ k := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < (Θ - β) / Θ by
    exact div_pos (by linarith) hΘ) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨k, ?_⟩
  unfold depth
  have h1 : (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  rw [lt_div_iff₀ hΘ] at hk
  nlinarith

/-! ### Resonance -/

/-- **Dirichlet's approximation with a large multiplier.** For `L, Q ≥ 1` some `N ≥ L` has
`|Nα − r| ≤ 1/Q` for an integer `r`. -/
theorem exists_resonant (α : ℝ) {L Q : ℕ} (hL : 0 < L) (hQ : 0 < Q) :
    ∃ N : ℕ, L ≤ N ∧ ∃ r : ℤ, |(N : ℝ) * α - r| ≤ 1 / Q := by
  obtain ⟨j, m, hm0, -, hjm⟩ := Real.exists_int_int_abs_mul_sub_le α (n := L * Q)
    (Nat.mul_pos hL hQ)
  have hmt : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm0.le
    exact_mod_cast this
  refine ⟨L * m.toNat, Nat.le_mul_of_pos_right L (by omega), L * j, ?_⟩
  push_cast
  rw [hmt, show (L : ℝ) * m * α - L * j = L * (m * α - j) by ring, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ L)]
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc (L : ℝ) * |(m : ℝ) * α - j| ≤ L * (1 / ((L * Q : ℕ) + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hjm (by positivity)
    _ ≤ 1 / Q := by
        push_cast
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hQ']
        nlinarith

variable (Θ) (p q : ℕ)

/-- The window bound `Q_k = ⌈6U_{k+1}/log q⌉ + 1`. -/
def windowQ (k : ℕ) : ℕ := ⌈6 * start Θ (k + 1) / Real.log q⌉₊ + 1

/-- The multiplier `N_k ≥ k + 1`. -/
def freqN (k : ℕ) : ℕ :=
  Classical.choose (exists_resonant (Real.log q / Real.log p) (L := k + 1) (Q := windowQ Θ q k)
    (Nat.succ_pos k) (Nat.succ_pos _))

theorem freqN_spec (k : ℕ) : k + 1 ≤ freqN Θ p q k ∧ ∃ r : ℤ,
    |(freqN Θ p q k : ℝ) * (Real.log q / Real.log p) - r| ≤ 1 / windowQ Θ q k :=
  Classical.choose_spec (exists_resonant (Real.log q / Real.log p) (L := k + 1)
    (Q := windowQ Θ q k) (Nat.succ_pos k) (Nat.succ_pos _))

/-- The ordinate `γ_k = 2πN_k/log p`. -/
def freq (k : ℕ) : ℝ := 2 * Real.pi * freqN Θ p q k / Real.log p

variable {Θ p q}

/-- **Resonance.** For every degree `a log p + b log q ≤ U_{k+1}`, `cos(γ_k λ) ≥ ½`. -/
theorem half_le_cos_freq (hp : p.Prime) (hq : q.Prime) (k a b : ℕ)
    (hlam : (a : ℝ) * Real.log p + b * Real.log q ≤ start Θ (k + 1)) :
    1 / 2 ≤ Real.cos (freq Θ p q k * (a * Real.log p + b * Real.log q)) := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  obtain ⟨-, r, hr⟩ := freqN_spec Θ p q k
  set N := freqN Θ p q k
  set Q := windowQ Θ q k
  set ε := (N : ℝ) * (Real.log q / Real.log p) - r with hε
  have hQ0 : (0 : ℝ) < Q := by simp only [Q, windowQ]; positivity
  -- `γ_k λ = 2π b ε + (N a + b r)·2π`
  have hsplit : freq Θ p q k * (a * Real.log p + b * Real.log q) =
      2 * Real.pi * b * ε + (((N * a : ℕ) : ℤ) + b * r : ℤ) * (2 * Real.pi) := by
    simp only [freq, hε]
    push_cast
    field_simp
    ring
  rw [hsplit, Real.cos_add_int_mul_two_pi, ← Real.cos_abs]
  -- `|2π b ε| ≤ π/3`
  have hb : (b : ℝ) ≤ Q / 6 := by
    have h1 : (b : ℝ) * Real.log q ≤ start Θ (k + 1) := by
      have : 0 ≤ (a : ℝ) * Real.log p := by positivity
      linarith
    have h2 : 6 * start Θ (k + 1) / Real.log q ≤ (Q : ℝ) := by
      simp only [Q, windowQ]; push_cast
      linarith [Nat.le_ceil (6 * start Θ (k + 1) / Real.log q)]
    rw [div_le_iff₀ hlq] at h2
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
    nlinarith
  have hx : |2 * Real.pi * b * ε| ≤ Real.pi / 3 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * b)]
    calc 2 * Real.pi * b * |ε| ≤ 2 * Real.pi * b * (1 / Q) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ ≤ Real.pi / 3 := by
          rw [mul_one_div, div_le_iff₀ hQ0]
          nlinarith [Real.pi_pos]
  rw [← Real.cos_pi_div_three]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hx

theorem freq_ge (hp : p.Prime) (k : ℕ) : 2 * Real.pi * (k + 1) / Real.log p ≤ freq Θ p q k := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hN : ((k + 1 : ℕ) : ℝ) ≤ freqN Θ p q k := by exact_mod_cast (freqN_spec Θ p q k).1
  simp only [freq]
  push_cast at hN
  exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hlp.le

/-! ### The window argument -/

variable (γ : ℕ → ℝ)

/-- The main term of quartet `j` at `λ`, for ordinates `γ`. -/
def mainTerm (lam : ℝ) (j : ℕ) : ℝ :=
  weight Θ j * Real.exp (depth Θ j * lam) * Real.cos (γ j * lam)

theorem abs_mainTerm_le (lam : ℝ) (j : ℕ) :
    |mainTerm (Θ := Θ) γ lam j| ≤ weight Θ j * Real.exp (depth Θ j * lam) := by
  unfold mainTerm
  rw [abs_mul, abs_mul, abs_of_pos (weight_pos Θ j), abs_of_pos (Real.exp_pos _)]
  have := Real.abs_cos_le_one (γ j * lam)
  have h0 : 0 ≤ weight Θ j * Real.exp (depth Θ j * lam) := by
    have := weight_pos Θ j; positivity
  nlinarith

theorem weight_exp_le (hΘ : 0 < Θ) {lam : ℝ} (hlam : 0 ≤ lam) (j : ℕ) :
    weight Θ j * Real.exp (depth Θ j * lam) ≤ weight Θ j * Real.exp (Θ * lam) :=
  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (depth_lt hΘ j).le hlam)) (weight_pos Θ j).le

theorem summable_mainTerm (hΘ : 0 < Θ) {lam : ℝ} (hlam : 0 ≤ lam) :
    Summable (mainTerm (Θ := Θ) γ lam) :=
  Summable.of_norm_bounded ((summable_weight hΘ.le).mul_right (Real.exp (Θ * lam))) fun j => by
    rw [Real.norm_eq_abs]
    exact (abs_mainTerm_le (Θ := Θ) γ lam j).trans (weight_exp_le hΘ hlam j)

/-- **On the window `[U_k, U_{k+1}]` the main terms sum to a nonnegative number.** -/
theorem tsum_mainTerm_nonneg (hΘ : 0 < Θ) (k : ℕ) {lam : ℝ} (hlo : start Θ k ≤ lam)
    (hhi : lam ≤ start Θ (k + 1)) (hck : 1 / 2 ≤ Real.cos (γ k * lam))
    (hck1 : 1 / 2 ≤ Real.cos (γ (k + 1) * lam)) :
    0 ≤ ∑' j, mainTerm (Θ := Θ) γ lam j := by
  have hlam : 0 ≤ lam := (start_nonneg Θ k).trans hlo
  have hs := summable_mainTerm γ hΘ hlam
  set A := fun j => weight Θ j * Real.exp (depth Θ j * lam) with hAdef
  rw [← hs.sum_add_tsum_nat_add (k + 2), Finset.sum_range_succ, Finset.sum_range_succ]
  -- the two dominant quartets
  have hk : 1 / 2 * A k ≤ mainTerm (Θ := Θ) γ lam k := by
    have := hck
    simp only [hAdef, mainTerm]
    have h0 : 0 ≤ weight Θ k * Real.exp (depth Θ k * lam) := by
      have := weight_pos Θ k; positivity
    nlinarith
  have hk1 : 1 / 2 * A (k + 1) ≤ mainTerm (Θ := Θ) γ lam (k + 1) := by
    have := hck1
    simp only [hAdef, mainTerm]
    have h0 : 0 ≤ weight Θ (k + 1) * Real.exp (depth Θ (k + 1) * lam) := by
      have := weight_pos Θ (k + 1); positivity
    nlinarith
  -- the earlier quartets
  have hhead : -(1 / 8 * A k) ≤ ∑ j ∈ Finset.range k, mainTerm (Θ := Θ) γ lam j := by
    have hbound : ∀ j ∈ Finset.range k, A j ≤ Real.exp (depth Θ k * lam) * (weight Θ k / 16) *
        weight Θ j := by
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hgap := depth_gap hΘ.le hjk
      have hwin := exp_window_le hΘ k'
      have h1 : Real.exp (depth Θ j * lam) ≤
          Real.exp (depth Θ (k' + 1) * lam) * Real.exp (-(Θ * (1 / 2 : ℝ) ^ (k' + 2) * lam)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : (1 / 2 : ℝ) ^ (k' + 1 + 1) = (1 / 2) ^ (k' + 2) := by ring_nf
        rw [this] at hgap
        nlinarith
      have h2 : Real.exp (-(Θ * (1 / 2 : ℝ) ^ (k' + 2) * lam)) ≤ weight Θ (k' + 1) / 16 :=
        (Real.exp_le_exp.mpr (by
          have : 0 ≤ Θ * (1 / 2 : ℝ) ^ (k' + 2) := by positivity
          nlinarith)).trans hwin
      have hw := weight_pos Θ j
      calc A j = weight Θ j * Real.exp (depth Θ j * lam) := rfl
        _ ≤ weight Θ j * (Real.exp (depth Θ (k' + 1) * lam) *
              Real.exp (-(Θ * (1 / 2 : ℝ) ^ (k' + 2) * lam))) :=
            mul_le_mul_of_nonneg_left h1 hw.le
        _ ≤ weight Θ j * (Real.exp (depth Θ (k' + 1) * lam) * (weight Θ (k' + 1) / 16)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) hw.le
        _ = _ := by ring
    have hsum : ∑ j ∈ Finset.range k, A j ≤ 1 / 8 * A k := by
      calc ∑ j ∈ Finset.range k, A j ≤ ∑ j ∈ Finset.range k,
            Real.exp (depth Θ k * lam) * (weight Θ k / 16) * weight Θ j := Finset.sum_le_sum hbound
        _ = Real.exp (depth Θ k * lam) * (weight Θ k / 16) * ∑ j ∈ Finset.range k, weight Θ j := by
            rw [Finset.mul_sum]
        _ ≤ Real.exp (depth Θ k * lam) * (weight Θ k / 16) * 2 :=
            mul_le_mul_of_nonneg_left (sum_range_weight_le hΘ.le k)
              (by have := weight_pos Θ k; positivity)
        _ = 1 / 8 * A k := by simp only [hAdef]; ring
    have := Finset.sum_le_sum (s := Finset.range k) (f := fun j => -(A j))
      (g := fun j => mainTerm (Θ := Θ) γ lam j)
      fun j _ => neg_le_of_abs_le (abs_mainTerm_le (Θ := Θ) γ lam j)
    rw [Finset.sum_neg_distrib] at this
    linarith
  -- the later quartets
  have htail : -(1 / 8 * A (k + 1)) ≤
      ∑' i, mainTerm (Θ := Θ) γ lam (i + (k + 2)) := by
    have hst : Summable fun i => weight Θ (k + 2 + i) := summable_weight_add hΘ.le (k + 2)
    have hbound : ∀ i, |mainTerm (Θ := Θ) γ lam (i + (k + 2))| ≤
        Real.exp (depth Θ (k + 1) * lam) * Real.exp (Θ * start Θ (k + 1)) * weight Θ (k + 2 + i) := by
      intro i
      refine (abs_mainTerm_le (Θ := Θ) γ lam _).trans ?_
      rw [add_comm i (k + 2)]
      have h1 : Real.exp (depth Θ (k + 2 + i) * lam) ≤
          Real.exp (depth Θ (k + 1) * lam) * Real.exp (Θ * start Θ (k + 1)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hd := (depth_lt hΘ (k + 2 + i)).le
        have hd1 := (depth_pos hΘ (k + 1)).le
        nlinarith
      have := weight_pos Θ (k + 2 + i)
      nlinarith
    have hsum2 : Summable fun i => Real.exp (depth Θ (k + 1) * lam) *
        Real.exp (Θ * start Θ (k + 1)) * weight Θ (k + 2 + i) := hst.mul_left _
    have hlow : ∑' i, -(Real.exp (depth Θ (k + 1) * lam) * Real.exp (Θ * start Θ (k + 1)) *
        weight Θ (k + 2 + i)) ≤ ∑' i, mainTerm (Θ := Θ) γ lam (i + (k + 2)) :=
      Summable.tsum_le_tsum (fun i => neg_le_of_abs_le (hbound i)) hsum2.neg
        ((summable_nat_add_iff (k + 2)).mpr hs)
    rw [tsum_neg, tsum_mul_left] at hlow
    have htw := tsum_weight_add_le hΘ.le (k + 2)
    have hw2 : weight Θ (k + 2) = weight Θ (k + 1) / 16 * Real.exp (-(Θ * start Θ (k + 1))) :=
      weight_succ Θ (k + 1)
    have hee : Real.exp (Θ * start Θ (k + 1)) * Real.exp (-(Θ * start Θ (k + 1))) = 1 := by
      rw [← Real.exp_add]; simp
    have hE := Real.exp_pos (depth Θ (k + 1) * lam)
    have hE2 := Real.exp_pos (Θ * start Θ (k + 1))
    have key : Real.exp (depth Θ (k + 1) * lam) * Real.exp (Θ * start Θ (k + 1)) *
        ∑' i, weight Θ (k + 2 + i) ≤ 1 / 8 * A (k + 1) := by
      calc Real.exp (depth Θ (k + 1) * lam) * Real.exp (Θ * start Θ (k + 1)) *
            ∑' i, weight Θ (k + 2 + i)
          ≤ Real.exp (depth Θ (k + 1) * lam) * Real.exp (Θ * start Θ (k + 1)) *
            (2 * weight Θ (k + 2)) := mul_le_mul_of_nonneg_left htw (by positivity)
        _ = 1 / 8 * A (k + 1) := by
            rw [hw2]; simp only [hAdef]
            calc Real.exp (depth Θ (k + 1) * lam) * Real.exp (Θ * start Θ (k + 1)) *
                  (2 * (weight Θ (k + 1) / 16 * Real.exp (-(Θ * start Θ (k + 1)))))
                = 1 / 8 * (weight Θ (k + 1) * Real.exp (depth Θ (k + 1) * lam)) *
                    (Real.exp (Θ * start Θ (k + 1)) * Real.exp (-(Θ * start Θ (k + 1)))) := by ring
              _ = _ := by rw [hee, mul_one]
    linarith
  have hA0 : 0 ≤ A k := by have := weight_pos Θ k; simp only [hAdef]; positivity
  have hA1 : 0 ≤ A (k + 1) := by have := weight_pos Θ (k + 1); simp only [hAdef]; positivity
  linarith

/-- The reflected term of quartet `j` at `λ`. -/
def reflTerm (lam : ℝ) (j : ℕ) : ℝ :=
  weight Θ j * Real.exp (-(depth Θ j * lam)) * Real.cos (γ j * lam)

theorem abs_reflTerm_le (hΘ : 0 < Θ) {lam : ℝ} (hlam : 0 ≤ lam) (j : ℕ) :
    |reflTerm (Θ := Θ) γ lam j| ≤ weight Θ j := by
  unfold reflTerm
  rw [abs_mul, abs_mul, abs_of_pos (weight_pos Θ j), abs_of_pos (Real.exp_pos _)]
  have h1 : Real.exp (-(depth Θ j * lam)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := mul_nonneg (depth_pos hΘ j).le hlam; linarith)
  have h2 := Real.abs_cos_le_one (γ j * lam)
  have hw := weight_pos Θ j
  have h3 : 0 ≤ Real.exp (-(depth Θ j * lam)) := (Real.exp_pos _).le
  calc weight Θ j * Real.exp (-(depth Θ j * lam)) * |Real.cos (γ j * lam)|
      ≤ weight Θ j * 1 * 1 := by gcongr
    _ = weight Θ j := by ring

theorem summable_reflTerm (hΘ : 0 < Θ) {lam : ℝ} (hlam : 0 ≤ lam) :
    Summable (reflTerm (Θ := Θ) γ lam) :=
  Summable.of_norm_bounded (summable_weight hΘ.le) fun j => by
    rw [Real.norm_eq_abs]; exact abs_reflTerm_le γ hΘ hlam j

/-- Every `λ ≥ 0` lies in a window `[U_k, U_{k+1}]`. -/
theorem exists_window {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ k, start Θ k ≤ lam ∧ lam ≤ start Θ (k + 1) := by
  classical
  have hex : ∃ k, lam < start Θ (k + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt lam
    exact ⟨n, hn.trans_le ((nat_le_start Θ n).trans (start_mono Θ (Nat.le_succ n)))⟩
  refine ⟨Nat.find hex, ?_, (Nat.find_spec hex).le⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, start_zero]; exact hlam
  · obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    have := Nat.find_min hex (show m < Nat.find hex by omega)
    rw [hm]; exact not_lt.mp this

/-- **Resonant ordinates bound the samples below.** If `cos(γ_k λ) ≥ ½` whenever `λ ≤ U_{k+1}`, the
symmetric samples at `λ ≥ 0` are `≥ −2`. -/
theorem samples_ge_of_resonant (hΘ : 0 < Θ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hres : ∀ k, lam ≤ start Θ (k + 1) → 1 / 2 ≤ Real.cos (γ k * lam)) :
    -2 ≤ ∑' k, weight Θ k * (Real.exp (depth Θ k * lam) + Real.exp (-(depth Θ k * lam))) *
      Real.cos (γ k * lam) := by
  obtain ⟨k, hlo, hhi⟩ := exists_window (Θ := Θ) hlam
  have hmain := tsum_mainTerm_nonneg γ hΘ k hlo hhi (hres k hhi)
    (hres (k + 1) (hhi.trans (start_mono Θ (Nat.le_succ _))))
  have hsm := summable_mainTerm (Θ := Θ) γ hΘ hlam
  have hsr := summable_reflTerm (Θ := Θ) γ hΘ hlam
  have hsplit : (∑' k, weight Θ k * (Real.exp (depth Θ k * lam) + Real.exp (-(depth Θ k * lam))) *
      Real.cos (γ k * lam)) =
      ∑' j, mainTerm (Θ := Θ) γ lam j + ∑' j, reflTerm (Θ := Θ) γ lam j := by
    rw [← hsm.tsum_add hsr]
    refine tsum_congr fun j => ?_
    simp only [mainTerm, reflTerm]; ring
  rw [hsplit]
  have hrefl : -(∑' j, weight Θ j) ≤ ∑' j, reflTerm (Θ := Θ) γ lam j := by
    rw [← tsum_neg]
    exact Summable.tsum_le_tsum (fun j => neg_le_of_abs_le (abs_reflTerm_le γ hΘ hlam j))
      (summable_weight hΘ.le).neg hsr
  linarith [tsum_weight_le hΘ.le]

/-- **The symmetric samples at the degrees `pᵃqᵇ` are bounded below.** -/
theorem samples_ge (hp : p.Prime) (hq : q.Prime) (hΘ : 0 < Θ) (a b : ℕ) :
    -2 ≤ ∑' k, weight Θ k * (Real.exp (depth Θ k * (a * Real.log p + b * Real.log q)) +
      Real.exp (-(depth Θ k * (a * Real.log p + b * Real.log q)))) *
        Real.cos (freq Θ p q k * (a * Real.log p + b * Real.log q)) := by
  have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.one_lt.le)
  exact samples_ge_of_resonant (freq Θ p q) hΘ (by positivity)
    fun k hk => half_le_cos_freq hp hq k a b hk

/-! ### Finitely many primes -/

section Family

variable {m : ℕ} (P : Fin (m + 1) → ℕ)

/-- The ratios `log P_{i+1}/log P_0`. -/
def famRatio (i : Fin m) : ℝ := Real.log (P i.succ) / Real.log (P 0)

/-- **Simultaneous Dirichlet with a large multiplier.** -/
theorem exists_famResonant {L Q : ℕ} (hL : 0 < L) (hQ : 0 < Q) :
    ∃ N : ℕ, L ≤ N ∧ ∀ i : Fin m, ∃ r : ℤ, |(N : ℝ) * famRatio P i - r| ≤ 1 / Q := by
  obtain ⟨d, hd1, -, hd⟩ := GaloisForLFunctions.HTGeometry.exists_simultaneous_dirichlet
    (famRatio P) (Q := L * Q) (Nat.mul_pos hL hQ)
  refine ⟨L * d, Nat.le_mul_of_pos_right L hd1, fun i => ?_⟩
  obtain ⟨r, hr⟩ := hd i
  refine ⟨L * r, ?_⟩
  push_cast
  rw [show (L : ℝ) * d * famRatio P i - L * r = L * (d * famRatio P i - r) by ring, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ L)]
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  calc (L : ℝ) * |(d : ℝ) * famRatio P i - r| ≤ L * (1 / ((L * Q : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hr.le hL'.le
    _ = 1 / Q := by push_cast; field_simp

variable (Θ)

/-- The window bound `⌈6U_{k+1}/log 2⌉ + 1`. -/
def famQ (k : ℕ) : ℕ := ⌈6 * start Θ (k + 1) / Real.log 2⌉₊ + 1

/-- The multiplier for the family. -/
def famFreqN (k : ℕ) : ℕ :=
  Classical.choose (exists_famResonant P (L := k + 1) (Q := famQ Θ k) (Nat.succ_pos k)
    (Nat.succ_pos _))

theorem famFreqN_spec (k : ℕ) : k + 1 ≤ famFreqN Θ P k ∧ ∀ i : Fin m, ∃ r : ℤ,
    |(famFreqN Θ P k : ℝ) * famRatio P i - r| ≤ 1 / famQ Θ k :=
  Classical.choose_spec (exists_famResonant P (L := k + 1) (Q := famQ Θ k) (Nat.succ_pos k)
    (Nat.succ_pos _))

/-- The ordinates `γ_k = 2πN_k/log P_0`. -/
def famFreq (k : ℕ) : ℝ := 2 * Real.pi * famFreqN Θ P k / Real.log (P 0)

variable {P Θ}

/-- **Resonance for the family.** -/
theorem half_le_cos_famFreq (hP : ∀ i, (P i).Prime) (k : ℕ) (a : Fin (m + 1) → ℕ)
    (hlam : ∑ i, (a i : ℝ) * Real.log (P i) ≤ start Θ (k + 1)) :
    1 / 2 ≤ Real.cos (famFreq Θ P k * ∑ i, (a i : ℝ) * Real.log (P i)) := by
  have hl0 : 0 < Real.log (P 0) := Real.log_pos (by exact_mod_cast (hP 0).one_lt)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogP : ∀ i, Real.log 2 ≤ Real.log (P i) := fun i =>
    Real.log_le_log (by norm_num) (by exact_mod_cast (hP i).two_le)
  obtain ⟨-, hres⟩ := famFreqN_spec Θ P k
  choose r hr using hres
  set N := famFreqN Θ P k
  set Q := famQ Θ k
  have hQ0 : (0 : ℝ) < Q := by simp only [Q, famQ]; positivity
  set ε : Fin m → ℝ := fun i => (N : ℝ) * famRatio P i - r i with hε
  -- `γλ = 2π Σ_{i ≥ 1} a_i ε_i + (N a_0 + Σ a_i r_i)·2π`
  have hsplit : famFreq Θ P k * ∑ i, (a i : ℝ) * Real.log (P i) =
      2 * Real.pi * ∑ i : Fin m, (a i.succ : ℝ) * ε i +
        (((N * a 0 : ℕ) : ℤ) + ∑ i : Fin m, (a i.succ : ℤ) * r i : ℤ) * (2 * Real.pi) := by
    have hl0' : Real.log (P 0) ≠ 0 := hl0.ne'
    have hS : ∑ i : Fin m, (a i.succ : ℝ) * ε i =
        (N : ℝ) / Real.log (P 0) * ∑ i : Fin m, (a i.succ : ℝ) * Real.log (P i.succ) -
          ∑ i : Fin m, (a i.succ : ℝ) * (r i : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hε, famRatio]
      field_simp
    rw [Fin.sum_univ_succ, hS]
    simp only [famFreq]
    push_cast
    field_simp
    ring
  rw [hsplit, Real.cos_add_int_mul_two_pi, ← Real.cos_abs]
  -- `Σ_{i ≥ 1} a_i ≤ Q/6`
  have hsumA : (∑ i : Fin m, (a i.succ : ℝ)) ≤ Q / 6 := by
    have h1 : (∑ i : Fin m, (a i.succ : ℝ)) * Real.log 2 ≤ start Θ (k + 1) := by
      have : (∑ i : Fin m, (a i.succ : ℝ)) * Real.log 2 ≤ ∑ i, (a i : ℝ) * Real.log (P i) := by
        rw [Fin.sum_univ_succ, Finset.sum_mul]
        have h0 : 0 ≤ (a 0 : ℝ) * Real.log (P 0) := by positivity
        have : ∑ i : Fin m, (a i.succ : ℝ) * Real.log 2 ≤
            ∑ i : Fin m, (a i.succ : ℝ) * Real.log (P i.succ) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlogP _) (Nat.cast_nonneg _)
        linarith
      linarith
    have h2 : 6 * start Θ (k + 1) / Real.log 2 ≤ (Q : ℝ) := by
      simp only [Q, famQ]; push_cast
      linarith [Nat.le_ceil (6 * start Θ (k + 1) / Real.log 2)]
    rw [div_le_iff₀ hl2] at h2
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
    nlinarith
  have hx : |2 * Real.pi * ∑ i : Fin m, (a i.succ : ℝ) * ε i| ≤ Real.pi / 3 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    have hb : |∑ i : Fin m, (a i.succ : ℝ) * ε i| ≤ (∑ i : Fin m, (a i.succ : ℝ)) * (1 / Q) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hr i) (Nat.cast_nonneg _)
    calc 2 * Real.pi * |∑ i : Fin m, (a i.succ : ℝ) * ε i|
        ≤ 2 * Real.pi * ((∑ i : Fin m, (a i.succ : ℝ)) * (1 / Q)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ Real.pi / 3 := by
          rw [mul_one_div, mul_div_assoc', div_le_iff₀ hQ0]
          have : 0 ≤ ∑ i : Fin m, (a i.succ : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
          nlinarith [Real.pi_pos]
  rw [← Real.cos_pi_div_three]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hx

theorem famFreq_ge (hP : ∀ i, (P i).Prime) (k : ℕ) :
    2 * Real.pi * (k + 1) / Real.log (P 0) ≤ famFreq Θ P k := by
  have hl0 : 0 < Real.log (P 0) := Real.log_pos (by exact_mod_cast (hP 0).one_lt)
  have hN : ((k + 1 : ℕ) : ℝ) ≤ famFreqN Θ P k := by exact_mod_cast (famFreqN_spec Θ P k).1
  simp only [famFreq]
  push_cast at hN
  exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hl0.le

end Family

end TwoPrimeWolff

open TwoPrimeWolff in
/-- **Two Frobenii need an attained top at single degrees.** In the positive-weight model there are
points `½ ± x_k ± iγ_k` with depths increasing to `Θ` (not attained), ordinates tending to `∞` and
positive summable weights whose symmetric samples are bounded below at every degree `pᵃqᵇ`. -/
theorem exists_twoPrime_samples_bddBelow_nonattained {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {Θ : ℝ} (hΘ : 0 < Θ) :
    ∃ x γ c : ℕ → ℝ, StrictMono x ∧ (∀ k, 0 < x k ∧ x k < Θ) ∧ (∀ β < Θ, ∃ k, β < x k) ∧
      (∀ T : ℝ, {k | γ k ≤ T}.Finite) ∧ (∀ k, 0 < c k) ∧ Summable c ∧
      ∀ a b : ℕ, -2 ≤ ∑' k, c k * (Real.exp (x k * (a * Real.log p + b * Real.log q)) +
        Real.exp (-(x k * (a * Real.log p + b * Real.log q)))) *
          Real.cos (γ k * (a * Real.log p + b * Real.log q)) := by
  refine ⟨depth Θ, freq Θ p q, weight Θ, strictMono_depth hΘ,
    fun k => ⟨depth_pos hΘ k, depth_lt hΘ k⟩, fun β hβ => exists_depth_gt hΘ hβ, fun T => ?_,
    weight_pos Θ, summable_weight hΘ.le, samples_ge hp hq hΘ⟩
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  refine (Set.finite_Iic ⌊T * Real.log p / (2 * Real.pi)⌋₊).subset fun k hk => ?_
  have h1 := (freq_ge (Θ := Θ) (q := q) hp k).trans hk
  rw [div_le_iff₀ hlp] at h1
  have h2 : (k : ℝ) ≤ T * Real.log p / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  exact Nat.le_floor h2

open TwoPrimeWolff in
/-- **No finite set of Frobenii removes the attained top at single degrees.** For every finite family
of primes `P_0, …, P_m` there are points `½ ± x_k ± iγ_k` with depths increasing to `Θ` (not attained),
ordinates tending to `∞` and positive summable weights whose symmetric samples are bounded below at
every degree `Π P_i^{a_i}`. -/
theorem exists_finPrimes_samples_bddBelow_nonattained {m : ℕ} (P : Fin (m + 1) → ℕ)
    (hP : ∀ i, (P i).Prime) {Θ : ℝ} (hΘ : 0 < Θ) :
    ∃ x γ c : ℕ → ℝ, StrictMono x ∧ (∀ k, 0 < x k ∧ x k < Θ) ∧ (∀ β < Θ, ∃ k, β < x k) ∧
      (∀ T : ℝ, {k | γ k ≤ T}.Finite) ∧ (∀ k, 0 < c k) ∧ Summable c ∧
      ∀ a : Fin (m + 1) → ℕ, -2 ≤ ∑' k, c k *
        (Real.exp (x k * ∑ i, (a i : ℝ) * Real.log (P i)) +
          Real.exp (-(x k * ∑ i, (a i : ℝ) * Real.log (P i)))) *
          Real.cos (γ k * ∑ i, (a i : ℝ) * Real.log (P i)) := by
  refine ⟨depth Θ, famFreq Θ P, weight Θ, strictMono_depth hΘ,
    fun k => ⟨depth_pos hΘ k, depth_lt hΘ k⟩, fun β hβ => exists_depth_gt hΘ hβ, fun T => ?_,
    weight_pos Θ, summable_weight hΘ.le, fun a => ?_⟩
  · have hl0 : 0 < Real.log (P 0) := Real.log_pos (by exact_mod_cast (hP 0).one_lt)
    refine (Set.finite_Iic ⌊T * Real.log (P 0) / (2 * Real.pi)⌋₊).subset fun k hk => ?_
    have h1 := (famFreq_ge (Θ := Θ) hP k).trans hk
    rw [div_le_iff₀ hl0] at h1
    have h2 : (k : ℝ) ≤ T * Real.log (P 0) / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
    exact Nat.le_floor h2
  · have hnn : 0 ≤ ∑ i, (a i : ℝ) * Real.log (P i) := Finset.sum_nonneg fun i _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (hP i).one_lt.le))
    exact samples_ge_of_resonant (famFreq Θ P) hΘ hnn
      fun k hk => half_le_cos_famFreq hP k a hk

end GaloisForLFunctions.SurfaceOfSpecZ
