import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartSeparatesZetaFromItsLiouvilleTwin

/-!
# The finite part sees every flipped prime

A twin of `ζ` that flips the primes of a finite set `F`, `ε_F(n) = Π_{p ∈ F} (−1)^{v_p(n)}`, has
matching coefficient `1` (`finiteFlip_matching`): its polar divergence is that of `ζ`, so the
coupled renormalization does not separate the pair. This file computes the separation in the
finite part.

* **The flip deficit** (`finiteFlipDeficit`, `tendsto_finiteFlipDeficit`):
  `D_F(y) = Σ_{t ≤ y} (1 − ε_F(t))Λ(t)/t` counts the odd prime powers of `F` twice. It increases to a
  limit `δ_F`, mathematically `δ_F = 2 Σ_{p ∈ F} p log p/(p² − 1)`.
* **Every flipped prime counts** (`two_mul_log_div_le_finiteFlipLimit`): `δ_F ≥ 2 log p/p` for each
  `p ∈ F`, from the term `t = p`.
* **The Mertens limit of the twin** (`tendsto_finiteFlipMertensError`): `A_{ε_F}(y) = A(y) − D_F(y)`,
  so `A_{ε_F}(y) − log y → −γ − δ_F`.
* **Separation** (`exists_abs_finiteFlipForm_sub_zetaForm_add_le`): on every uniform step profile,
  `P_N(ε_F x) − P_N(x) = −2δ_F |x|² + o(mass)`. The divergences `ℓ²` cancel, and the finite part of
  the twin is lower by `2δ_F > 0` for every non-empty `F`.

* **Rigidity** (`finitePartLimit_le_and_eq_iff`, `exists_abs_gaugeForm_sub_zetaForm_sub_le`): for
  every sign gauge with matching coefficient `1` and a convergent Mertens error
  `A_ε(y) − log y → α`, `α ≤ −γ`, with equality only for `ε = 1`; so
  `P_N(εx) − P_N(x) = 2(α + γ)|x|² + o(mass)` with `α + γ < 0` for every such twin.

* **The mirror** (`liouvilleLimit_le_and_eq_iff`): every sign gauge with `κ = −1` and a convergent
  Mertens error `A_ε(y) + log y → α` has `α ≥ γ + τ`, with equality only for `ε = λ`.

So among the twins of `ζ` matched to the same polar divergence, `ζ` is the unique maximizer of the
finite part, and each flipped prime lowers it by at least `4 log p/p`. Matching cannot select `ζ`
within this family; the finite part does, with an explicit margin at every prime.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

variable {F : Finset ℕ}

theorem abs_finiteFlip (F : Finset ℕ) (t : ℕ) : |finiteFlip F t| = 1 := by
  rw [finiteFlip, abs_prod]
  exact prod_eq_one fun p _ => by rw [abs_pow, abs_neg, abs_one, one_pow]

/-- The **flip deficit** `D_F(y) = Σ_{t ≤ y} (1 − ε_F(t))Λ(t)/t`. -/
def finiteFlipDeficit (F : Finset ℕ) (y : ℕ) : ℝ :=
  ∑ t ∈ Icc 1 y, (1 - finiteFlip F t) * Λ t / t

theorem finiteFlipDeficit_term_nonneg (F : Finset ℕ) (t : ℕ) :
    0 ≤ (1 - finiteFlip F t) * Λ t / t := by
  have h := le_abs_self (finiteFlip F t)
  rw [abs_finiteFlip] at h
  exact div_nonneg (mul_nonneg (by linarith) vonMangoldt_nonneg) (Nat.cast_nonneg t)

theorem finiteFlipDeficit_mono (F : Finset ℕ) : Monotone (finiteFlipDeficit F) :=
  monotone_nat_of_le_succ fun y => by
    rw [finiteFlipDeficit, finiteFlipDeficit, sum_Icc_succ_top (by omega)]
    linarith [finiteFlipDeficit_term_nonneg F (y + 1)]

/-- `A_{ε_F}(y) = A(y) − D_F(y)`. -/
theorem gaugeMertensSum_finiteFlip_eq (F : Finset ℕ) (y : ℕ) :
    gaugeMertensSum (finiteFlip F) y = mertensSum y - finiteFlipDeficit F y := by
  rw [gaugeMertensSum, mertensSum, finiteFlipDeficit, ← sum_sub_distrib]
  exact sum_congr rfl fun t _ => by ring

/-- The flip deficit is bounded, since both Mertens sums are `log y + O(1)`. -/
theorem finiteFlipDeficit_le (hF : ∀ p ∈ F, p.Prime) (y : ℕ) :
    finiteFlipDeficit F y ≤
      2 * (Real.log 4 + 4) + 2 * ∑ p ∈ F, Real.log p / ((p : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · have : 0 ≤ ∑ p ∈ F, Real.log p / ((p : ℝ) - 1) := sum_nonneg fun p hp => by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (hF p hp).one_lt
      exact div_nonneg (Real.log_nonneg hp1.le) (by linarith)
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    simp only [finiteFlipDeficit, Finset.Icc_eq_empty_of_lt zero_lt_one, sum_empty]
    linarith
  have h1 := RHTower.Mertens.mertens_first y hy
  have h2 := (finiteFlip_matching hF).2 y hy
  rw [gaugeMertensSum_finiteFlip_eq, one_mul] at h2
  have hm : mertensSum y = ∑ t ∈ Icc 1 y, Λ t / t := rfl
  rw [← hm] at h1
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- The **flip limit** `δ_F = lim_y D_F(y)`. -/
def finiteFlipLimit (F : Finset ℕ) : ℝ := ⨆ y, finiteFlipDeficit F y

theorem tendsto_finiteFlipDeficit (hF : ∀ p ∈ F, p.Prime) :
    Tendsto (finiteFlipDeficit F) atTop (𝓝 (finiteFlipLimit F)) :=
  tendsto_atTop_ciSup (finiteFlipDeficit_mono F)
    ⟨_, by rintro _ ⟨y, rfl⟩; exact finiteFlipDeficit_le hF y⟩

/-- A flipped prime is flipped: `ε_F(p) = −1` for `p ∈ F`. -/
theorem finiteFlip_prime (hF : ∀ p ∈ F, p.Prime) {p : ℕ} (hp : p ∈ F) : finiteFlip F p = -1 := by
  rw [finiteFlip, prod_eq_single p]
  · rw [(hF p hp).factorization_self, pow_one]
  · intro p' hp' hne
    rw [(hF p hp).factorization, Finsupp.single_eq_of_ne hne, pow_zero]
  · intro h
    exact absurd hp h

/-- **Every flipped prime counts**: `δ_F ≥ 2 log p/p` for each `p ∈ F`. -/
theorem two_mul_log_div_le_finiteFlipLimit (hF : ∀ p ∈ F, p.Prime) {p : ℕ} (hp : p ∈ F) :
    2 * Real.log p / p ≤ finiteFlipLimit F := by
  have hbdd : BddAbove (Set.range (finiteFlipDeficit F)) :=
    ⟨_, by rintro _ ⟨y, rfl⟩; exact finiteFlipDeficit_le hF y⟩
  refine le_trans ?_ (le_ciSup hbdd p)
  have hterm : (1 - finiteFlip F p) * Λ p / p = 2 * Real.log p / p := by
    rw [finiteFlip_prime hF hp, vonMangoldt_apply_prime (hF p hp)]
    ring
  rw [← hterm]
  exact single_le_sum (f := fun t => (1 - finiteFlip F t) * Λ t / t)
    (fun t _ => finiteFlipDeficit_term_nonneg F t)
    (mem_Icc.mpr ⟨(hF p hp).one_le, le_rfl⟩)

/-- **The Mertens limit of the twin**: `A_{ε_F}(y) − log y → −γ − δ_F`. -/
theorem tendsto_finiteFlipMertensError (hF : ∀ p ∈ F, p.Prime) :
    Tendsto (gaugeMertensError (finiteFlip F) 1) atTop (𝓝 (-γ - finiteFlipLimit F)) := by
  refine (tendsto_mertensSum_sub_log.sub (tendsto_finiteFlipDeficit hF)).congr fun y => ?_
  rw [gaugeMertensError, gaugeMertensSum_finiteFlip_eq]
  ring

/-- **The finite part sees every flipped prime**: for every `η > 0` there is `C` such that every
uniform step profile has `|P_N(ε_F x) − P_N(x) + 2δ_F|x|²| ≤ 2 Σ_{i,j} |c_i| |c_j| (η H_{min} + C)`,
with `δ_F ≥ 2 log p/p` for each `p ∈ F`. -/
theorem exists_abs_finiteFlipForm_sub_zetaForm_add_le (hF : ∀ p ∈ F, p.Prime) {η : ℝ}
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, 1 ≤ M i) → (∀ i, M i ≤ N) →
      |atomicWeilForm N (fun n => finiteFlip F n * stepProfile c M n) -
          atomicWeilForm N (stepProfile c M) +
          2 * finiteFlipLimit F * ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2| ≤
        2 * ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C) := by
  obtain ⟨C₁, hC₁⟩ := exists_abs_gaugeForm_stepProfile_finitePart_le (finiteFlip_isSignGauge F)
    (by norm_num : |(1 : ℝ)| ≤ 1) (tendsto_finiteFlipMertensError hF) hη
  obtain ⟨C₂, hC₂⟩ := exists_abs_atomicWeilForm_stepProfile_finitePart_le hη
  refine ⟨max C₁ C₂, fun c M hM1 hM => ?_⟩
  have h1 := hC₁ c M hM1 hM
  have h2 := hC₂ c M hM1 hM
  have hmono : ∀ C' : ℝ, C' ≤ max C₁ C₂ →
      ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C') ≤
        ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + max C₁ C₂) :=
    fun C' hC' => sum_le_sum fun i _ => sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h1' := h1.trans (hmono C₁ (le_max_left _ _))
  have h2' := h2.trans (hmono C₂ (le_max_right _ _))
  rw [abs_le] at h1' h2' ⊢
  constructor <;> nlinarith [h1'.1, h1'.2, h2'.1, h2'.2]

/-! ### Rigidity: `ζ` maximizes the finite part -/

/-- The **gauge deficit** `D_ε(y) = Σ_{t ≤ y} (1 − ε(t))Λ(t)/t`. -/
def gaugeDeficit (ε : ℕ → ℝ) (y : ℕ) : ℝ := ∑ t ∈ Icc 1 y, (1 - ε t) * Λ t / t

theorem gaugeDeficit_term_nonneg {ε : ℕ → ℝ} (hε : IsSignGauge ε) (t : ℕ) :
    0 ≤ (1 - ε t) * Λ t / t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  have h1 : ε t * ε t = 1 := hε.mul_self ht.ne'
  have h2 : ε t ≤ 1 := by nlinarith [sq_nonneg (ε t - 1)]
  exact div_nonneg (mul_nonneg (by linarith) vonMangoldt_nonneg) (Nat.cast_nonneg t)

theorem gaugeDeficit_mono {ε : ℕ → ℝ} (hε : IsSignGauge ε) : Monotone (gaugeDeficit ε) :=
  monotone_nat_of_le_succ fun y => by
    rw [gaugeDeficit, gaugeDeficit, sum_Icc_succ_top (by omega)]
    linarith [gaugeDeficit_term_nonneg hε (y + 1)]

/-- A sign gauge that is `1` at every prime is `1` on every positive integer. -/
theorem IsSignGauge.eq_one_of_prime {ε : ℕ → ℝ} (hε : IsSignGauge ε)
    (hp : ∀ p : ℕ, p.Prime → ε p = 1) : ∀ n : ℕ, 1 ≤ n → ε n = 1 := by
  have h1 : ε 1 = 1 := by
    have hm := hε.mul (one_ne_zero) (one_ne_zero)
    have hs := hε.mul_self (one_ne_zero)
    rw [one_mul] at hm
    nlinarith
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases hn.eq_or_lt with rfl | hn2
    · exact h1
    have hmin := Nat.minFac_prime (show n ≠ 1 by omega)
    have hdvd := Nat.minFac_dvd n
    have hq : n / n.minFac < n := Nat.div_lt_self (by omega) hmin.one_lt
    have hq1 : 1 ≤ n / n.minFac := Nat.div_pos (Nat.minFac_le (by omega)) hmin.pos
    have hsplit : n = n.minFac * (n / n.minFac) := (Nat.mul_div_cancel' hdvd).symm
    rw [hsplit, hε.mul hmin.ne_zero (by omega), hp _ hmin, ih _ hq hq1, one_mul]

/-- **`ζ` maximizes the finite part**: if a sign gauge has `A_ε(y) − log y → α`, then `α ≤ −γ`, with
equality exactly for the Euler gauge `ε = 1`. -/
theorem finitePartLimit_le_and_eq_iff {ε : ℕ → ℝ} (hε : IsSignGauge ε) {α : ℝ}
    (hE : Tendsto (gaugeMertensError ε 1) atTop (𝓝 α)) :
    α ≤ -γ ∧ (α = -γ ↔ ∀ n : ℕ, 1 ≤ n → ε n = 1) := by
  -- `D_ε = (A − log) − (A_ε − log) → −γ − α`
  have hD : Tendsto (gaugeDeficit ε) atTop (𝓝 (-γ - α)) := by
    refine (tendsto_mertensSum_sub_log.sub hE).congr fun y => ?_
    rw [gaugeMertensError, gaugeMertensSum, mertensSum, gaugeDeficit]
    rw [one_mul, sub_sub_sub_cancel_right, ← sum_sub_distrib]
    exact sum_congr rfl fun t _ => by ring
  have hD0 : 0 ≤ -γ - α :=
    ge_of_tendsto hD (Eventually.of_forall fun y => sum_nonneg fun t _ =>
      gaugeDeficit_term_nonneg hε t)
  refine ⟨by linarith, ⟨fun hα => ?_, fun h1 => ?_⟩⟩
  · -- a monotone deficit with limit `0` vanishes, so `ε = 1` at every prime
    have hle : ∀ y, gaugeDeficit ε y ≤ 0 := by
      intro y
      have := (gaugeDeficit_mono hε).ge_of_tendsto hD y
      rw [hα] at this
      linarith
    refine hε.eq_one_of_prime fun p hp => ?_
    have hzero : gaugeDeficit ε p = 0 :=
      le_antisymm (hle p) (sum_nonneg fun t _ => gaugeDeficit_term_nonneg hε t)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => gaugeDeficit_term_nonneg hε t)).mp
      hzero p (mem_Icc.mpr ⟨hp.one_le, le_rfl⟩)
    rw [vonMangoldt_apply_prime hp] at hterm
    have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rcases (div_eq_zero_iff.mp hterm) with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · linarith
      · linarith
    · linarith
  · -- the Euler gauge has deficit `0`
    have hzero : ∀ y, gaugeDeficit ε y = 0 := fun y => sum_eq_zero fun t ht => by
      rw [h1 t (mem_Icc.mp ht).1, sub_self, zero_mul, zero_div]
    have hD' : Tendsto (gaugeDeficit ε) atTop (𝓝 0) := by
      rw [show gaugeDeficit ε = fun _ => 0 from funext hzero]
      exact tendsto_const_nhds
    have := tendsto_nhds_unique hD hD'
    linarith

/-- **Selection of `ζ` by the finite part**: for every sign gauge with matching coefficient `1` and a
convergent Mertens error `A_ε(y) − log y → α`, and every `η > 0`, there is `C` such that
`|P_N(εx) − P_N(x) − 2(α + γ)|x|²| ≤ 2 Σ_{i,j} |c_i| |c_j| (η H_{min} + C)` on uniform step profiles,
with `α + γ ≤ 0`, and `α + γ = 0` only for `ε = 1`. -/
theorem exists_abs_gaugeForm_sub_zetaForm_sub_le {ε : ℕ → ℝ} (hε : IsSignGauge ε) {α : ℝ}
    (hE : Tendsto (gaugeMertensError ε 1) atTop (𝓝 α)) {η : ℝ} (hη : 0 < η) :
    (α + γ ≤ 0 ∧ (α + γ = 0 ↔ ∀ n : ℕ, 1 ≤ n → ε n = 1)) ∧
    ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, 1 ≤ M i) → (∀ i, M i ≤ N) →
      |atomicWeilForm N (fun n => ε n * stepProfile c M n) - atomicWeilForm N (stepProfile c M) -
          2 * (α + γ) * ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2| ≤
        2 * ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C) := by
  obtain ⟨hle, hiff⟩ := finitePartLimit_le_and_eq_iff hε hE
  refine ⟨⟨by linarith, ⟨fun h => hiff.mp (by linarith), fun h => by linarith [hiff.mpr h]⟩⟩, ?_⟩
  obtain ⟨C₁, hC₁⟩ := exists_abs_gaugeForm_stepProfile_finitePart_le hε
    (by norm_num : |(1 : ℝ)| ≤ 1) hE hη
  obtain ⟨C₂, hC₂⟩ := exists_abs_atomicWeilForm_stepProfile_finitePart_le hη
  refine ⟨max C₁ C₂, fun c M hM1 hM => ?_⟩
  have h1 := hC₁ c M hM1 hM
  have h2 := hC₂ c M hM1 hM
  have hmono : ∀ C' : ℝ, C' ≤ max C₁ C₂ →
      ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C') ≤
        ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + max C₁ C₂) :=
    fun C' hC' => sum_le_sum fun i _ => sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h1' := h1.trans (hmono C₁ (le_max_left _ _))
  have h2' := h2.trans (hmono C₂ (le_max_right _ _))
  rw [abs_le] at h1' h2' ⊢
  constructor <;> nlinarith [h1'.1, h1'.2, h2'.1, h2'.2]

/-! ### The mirror: the Liouville twin minimizes the anti-matched finite part -/

/-- `ε(1) = 1`, from `ε(1) = ε(1)²` and `ε(1)² = 1`. -/
theorem IsSignGauge.one {ε : ℕ → ℝ} (hε : IsSignGauge ε) : ε 1 = 1 := by
  have hm := hε.mul (one_ne_zero) (one_ne_zero)
  have hs := hε.mul_self (one_ne_zero)
  rw [one_mul] at hm
  linarith

/-- `ε(p^k) = ε(p)^k`. -/
theorem IsSignGauge.pow {ε : ℕ → ℝ} (hε : IsSignGauge ε) {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    ε (p ^ k) = ε p ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, hε.one]
  | succ k ih => rw [pow_succ, hε.mul (pow_ne_zero k hp) hp, ih, pow_succ]

/-- Two sign gauges agreeing at every prime agree on every positive integer. -/
theorem IsSignGauge.eq_of_prime {ε ε' : ℕ → ℝ} (hε : IsSignGauge ε) (hε' : IsSignGauge ε')
    (h : ∀ p : ℕ, p.Prime → ε p = ε' p) : ∀ n : ℕ, 1 ≤ n → ε n = ε' n := by
  have hprod : IsSignGauge (fun n => ε n * ε' n) := by
    refine ⟨fun {m n} hm hn => ?_, fun {n} hn => ?_⟩
    · simp only [hε.mul hm hn, hε'.mul hm hn]
      ring
    · show ε n * ε' n * (ε n * ε' n) = 1
      rw [show ε n * ε' n * (ε n * ε' n) = (ε n * ε n) * (ε' n * ε' n) by ring,
        hε.mul_self hn, hε'.mul_self hn, one_mul]
  have h1 := hprod.eq_one_of_prime fun p hp => by
    show ε p * ε' p = 1
    rw [h p hp, hε'.mul_self hp.ne_zero]
  intro n hn
  have h2 : ε n * ε' n = 1 := h1 n hn
  calc ε n = ε n * (ε' n * ε' n) := by rw [hε'.mul_self (by omega), mul_one]
    _ = (ε n * ε' n) * ε' n := by ring
    _ = ε' n := by rw [h2, one_mul]

/-- On a prime power a sign gauge dominates Liouville: `λ(t) ≤ ε(t)` when `Λ(t) ≠ 0`, so the
anti-matched deficit `Σ (ε(t) − λ(t))Λ(t)/t` has non-negative terms. -/
theorem liouvilleGap_term_nonneg {ε : ℕ → ℝ} (hε : IsSignGauge ε) (t : ℕ) :
    0 ≤ (ε t - liouvilleSign t) * Λ t / t := by
  by_cases hΛ : Λ t = 0
  · simp [hΛ]
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff t).mp (vonMangoldt_ne_zero_iff.mp hΛ)
  rw [hε.pow hp.ne_zero, liouvilleSign_prime_pow hp]
  have hsq : ε p * ε p = 1 := hε.mul_self hp.ne_zero
  have hle : ((-1 : ℝ)) ^ k ≤ ε p ^ k := by
    rcases (mul_self_eq_one_iff.mp hsq) with h | h
    · rw [h, one_pow]
      rcases neg_one_pow_eq_or ℝ k with h' | h' <;> rw [h']
      norm_num
    · rw [h]
  exact div_nonneg (mul_nonneg (by linarith) vonMangoldt_nonneg) (Nat.cast_nonneg _)

/-- **The Liouville twin minimizes the anti-matched finite part**: if a sign gauge has
`A_ε(y) + log y → α`, then `α ≥ γ + τ`, with equality exactly for `ε = λ` on positive integers. -/
theorem liouvilleLimit_le_and_eq_iff {ε : ℕ → ℝ} (hε : IsSignGauge ε) {α : ℝ}
    (hE : Tendsto (gaugeMertensError ε (-1)) atTop (𝓝 α)) :
    γ + liouvilleEvenLimit ≤ α ∧
      (α = γ + liouvilleEvenLimit ↔ ∀ n : ℕ, 1 ≤ n → ε n = liouvilleSign n) := by
  set W : ℕ → ℝ := fun y => ∑ t ∈ Icc 1 y, (ε t - liouvilleSign t) * Λ t / t with hWdef
  have hW : Tendsto W atTop (𝓝 (α - (γ + liouvilleEvenLimit))) := by
    refine (hE.sub tendsto_liouvilleMertensError).congr fun y => ?_
    show gaugeMertensError ε (-1) y - gaugeMertensError liouvilleSign (-1) y =
      ∑ t ∈ Icc 1 y, (ε t - liouvilleSign t) * Λ t / t
    rw [gaugeMertensError, gaugeMertensError, gaugeMertensSum, gaugeMertensSum,
      sub_sub_sub_cancel_right, ← sum_sub_distrib]
    exact sum_congr rfl fun t _ => by ring
  have hWmono : Monotone W := monotone_nat_of_le_succ fun y => by
    simp only [hWdef]
    rw [sum_Icc_succ_top (by omega)]
    linarith [liouvilleGap_term_nonneg hε (y + 1)]
  have hW0 : 0 ≤ α - (γ + liouvilleEvenLimit) :=
    ge_of_tendsto hW (Eventually.of_forall fun y => sum_nonneg fun t _ =>
      liouvilleGap_term_nonneg hε t)
  refine ⟨by linarith, ⟨fun hα => ?_, fun h1 => ?_⟩⟩
  · have hle : ∀ y, W y ≤ 0 := by
      intro y
      have := hWmono.ge_of_tendsto hW y
      rw [hα, sub_self] at this
      exact this
    refine hε.eq_of_prime liouville_matching.1 fun p hp => ?_
    have hzero : W p = 0 :=
      le_antisymm (hle p) (sum_nonneg fun t _ => liouvilleGap_term_nonneg hε t)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => liouvilleGap_term_nonneg hε t)).mp
      hzero p (mem_Icc.mpr ⟨hp.one_le, le_rfl⟩)
    rw [vonMangoldt_apply_prime hp] at hterm
    have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rcases (div_eq_zero_iff.mp hterm) with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · linarith
      · linarith
    · linarith
  · have hzero : W = fun _ => 0 := funext fun y => sum_eq_zero fun t ht => by
      rw [h1 t (mem_Icc.mp ht).1, sub_self, zero_mul, zero_div]
    rw [hzero] at hW
    have := tendsto_nhds_unique hW tendsto_const_nhds
    linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
