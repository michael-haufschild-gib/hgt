import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ResiduePatternGaugesAreMatchedByTheirMean

/-!
# The matching coefficient is the logarithmic density

Every sign pattern on the primes, `g(p) = ±1`, extends to a gauge
`ε_g(n) = Π_p g(p)^{v_p(n)}` (`primeSignGauge`). This file shows that its polar matching coefficient
is the logarithmic density of the pattern, without any assumption on the pattern beyond that
density.

* **Primes and proper prime powers** (`gaugeMertensSum_primeSignGauge_eq`,
  `abs_primeSignRemainder_le`): `A_{ε_g}(y) = Σ_{p ≤ y} g(p) log p/p + R(y)` with
  `|R(y)| ≤ 8 + mertensTail`, since the proper prime powers are absolutely summable against `1/t`.
* **Density gives matching** (`tendsto_primeSignGauge_div_log`, `gaugeForm_primeSignGauge_soft`):
  if `Σ_{p ≤ y} g(p) log p/p = κ log y + o(log y)`, then `A_{ε_g}(y)/log y → κ`, `|κ| ≤ 1`, and on
  uniform step profiles `|P_N(ε_g x) − κ ℓ(x)²| ≤ (η log N + C_η) · mass`.
* **Flipped density** (`flipGauge_kappa`): flipping a set `S` of primes of logarithmic density `ϑ`,
  `Σ_{p ≤ y, p ∈ S} log p/p = ϑ log y + o(log y)`, gives `κ = 1 − 2ϑ`.

So the polar divergence of a sign twin of `ζ` is `(1 − 2ϑ) ℓ²`, with `ϑ` the logarithmic density
of its flipped primes: the coupled renormalization reads that one number from the pattern.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

variable {g : ℕ → ℝ}

/-- The **prime-sign gauge** `ε_g(n) = Π_p g(p)^{v_p(n)}`. -/
def primeSignGauge (g : ℕ → ℝ) (n : ℕ) : ℝ := n.factorization.prod fun p k => g p ^ k

theorem primeSignGauge_isSignGauge (hg : ∀ p, g p * g p = 1) : IsSignGauge (primeSignGauge g) := by
  refine ⟨fun {m n} hm hn => ?_, fun {n} _ => ?_⟩
  · rw [primeSignGauge, primeSignGauge, primeSignGauge, Nat.factorization_mul hm hn,
      Finsupp.prod_add_index']
    · intro p
      rw [pow_zero]
    · intro p a b
      rw [pow_add]
  · rw [primeSignGauge, ← Finsupp.prod_mul, Finsupp.prod]
    exact prod_eq_one fun p _ => by rw [← mul_pow, hg, one_pow]

theorem primeSignGauge_prime {p : ℕ} (hp : p.Prime) : primeSignGauge g p = g p := by
  rw [primeSignGauge, hp.factorization, Finsupp.prod_single_index]
  · exact pow_one _
  · exact pow_zero _

/-- The proper prime-power remainder `R(y) = Σ_{t ≤ y, t not prime} ε_g(t)Λ(t)/t`. -/
def primeSignRemainder (g : ℕ → ℝ) (y : ℕ) : ℝ :=
  ∑ t ∈ Icc 1 y, (if t.Prime then 0 else primeSignGauge g t * Λ t / t)

/-- **Primes and proper prime powers**: `A_{ε_g}(y) = Σ_{p ≤ y} g(p) log p/p + R(y)`. -/
theorem gaugeMertensSum_primeSignGauge_eq (y : ℕ) :
    gaugeMertensSum (primeSignGauge g) y =
      ∑ t ∈ Icc 1 y, (if t.Prime then g t * Real.log t / t else 0) + primeSignRemainder g y := by
  rw [gaugeMertensSum, primeSignRemainder, ← sum_add_distrib]
  refine sum_congr rfl fun t _ => ?_
  by_cases ht : t.Prime
  · rw [if_pos ht, if_pos ht, primeSignGauge_prime ht, vonMangoldt_apply_prime ht, add_zero]
  · rw [if_neg ht, if_neg ht, zero_add]

/-- The remainder is bounded: `|R(y)| ≤ 8 + mertensTail`. -/
theorem abs_primeSignRemainder_le (hg : ∀ p, g p * g p = 1) (y : ℕ) :
    |primeSignRemainder g y| ≤ 8 + RHTower.Mertens.mertensTail := by
  refine (abs_sum_le_sum_abs _ _).trans (le_trans (sum_le_sum fun t _ => ?_)
    (RHTower.Mertens.tail_bounded y))
  rw [RHTower.Mertens.notPrimeVonMangoldt]
  split_ifs with ht
  · simp
  · rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simp
    have he : |primeSignGauge g t| = 1 :=
      abs_eq_one_of_mul_self ((primeSignGauge_isSignGauge hg).mul_self ht0.ne')
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht0
    rw [abs_div, abs_mul, he, one_mul, abs_of_nonneg vonMangoldt_nonneg, abs_of_pos ht']

/-- **Density gives matching**: if `Σ_{p ≤ y} g(p) log p/p / log y → κ`, then
`A_{ε_g}(y)/log y → κ`. -/
theorem tendsto_primeSignGauge_div_log (hg : ∀ p, g p * g p = 1) {κ : ℝ}
    (hκ : Tendsto (fun y : ℕ =>
      (∑ t ∈ Icc 1 y, (if t.Prime then g t * Real.log t / t else 0)) / Real.log y) atTop (𝓝 κ)) :
    Tendsto (fun y : ℕ => gaugeMertensSum (primeSignGauge g) y / Real.log y) atTop (𝓝 κ) := by
  -- the bounded remainder vanishes against `log y`
  have hlog : Tendsto (fun y : ℕ => Real.log y) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun y : ℕ => primeSignRemainder g y / Real.log y) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      ((tendsto_const_nhds (x := 8 + RHTower.Mertens.mertensTail)).div_atTop hlog)
    filter_upwards [hlog.eventually_gt_atTop 0] with y hy
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy]
    exact div_le_div_of_nonneg_right (abs_primeSignRemainder_le hg y) hy.le
  have h := hκ.add hR
  rw [add_zero] at h
  refine h.congr fun y => ?_
  rw [gaugeMertensSum_primeSignGauge_eq, add_div]

/-- The matching coefficient of a sign pattern lies in `[−1, 1]`. -/
theorem abs_kappa_le_of_tendsto (hg : ∀ p, g p * g p = 1) {κ : ℝ}
    (hκ : Tendsto (fun y : ℕ =>
      (∑ t ∈ Icc 1 y, (if t.Prime then g t * Real.log t / t else 0)) / Real.log y) atTop (𝓝 κ)) :
    |κ| ≤ 1 := by
  -- `|Σ g log p/p| ≤ Σ log p/p ≤ log y + C`
  set C := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail) with hC
  have hlog : Tendsto (fun y : ℕ => Real.log y) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ y : ℕ in atTop,
      |(∑ t ∈ Icc 1 y, (if t.Prime then g t * Real.log t / t else 0)) / Real.log y| ≤
        1 + C / Real.log y := by
    filter_upwards [hlog.eventually_gt_atTop 0, eventually_ge_atTop 1] with y hy hy1
    have hm := RHTower.Mertens.mertens_first_prime y hy1
    have hsum : |∑ t ∈ Icc 1 y, (if t.Prime then g t * Real.log t / t else 0)| ≤
        ∑ n ∈ Finset.Icc 1 y with n.Prime, Real.log n / (n : ℝ) := by
      rw [sum_filter]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t _ => ?_)
      split_ifs with ht
      · rw [abs_div, abs_mul, abs_eq_one_of_mul_self (hg t), one_mul,
          abs_of_nonneg (Real.log_natCast_nonneg t), Nat.abs_cast]
      · simp
    rw [abs_div, abs_of_pos hy, div_le_iff₀ hy, add_mul, div_mul_cancel₀ _ hy.ne']
    rw [abs_le] at hm
    linarith [hm.2]
  have hlim : Tendsto (fun y : ℕ => 1 + C / Real.log y) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := C)).div_atTop hlog
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add this
  exact le_of_tendsto_of_tendsto hκ.abs hlim hbound

/-- **The soft law for a sign pattern of logarithmic density**: if
`Σ_{p ≤ y} g(p) log p/p / log y → κ`, then for every `η > 0` there is `C` with
`|P_N(ε_g x) − κ ℓ(x)²| ≤ (η log N + C) Σ_{i,j} |c_i| |c_j| H_{min(M_i, M_j)}`. -/
theorem gaugeForm_primeSignGauge_soft (hg : ∀ p, g p * g p = 1) {κ : ℝ}
    (hκ : Tendsto (fun y : ℕ =>
      (∑ t ∈ Icc 1 y, (if t.Prime then g t * Real.log t / t else 0)) / Real.log y) atTop (𝓝 κ)) :
    ∀ η > 0, ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, M i ≤ N) →
      (∀ i, 1 ≤ M i) →
      |atomicWeilForm N (fun n => primeSignGauge g n * stepProfile c M n) -
          κ * polarFunctional N (stepProfile c M) ^ 2| ≤
        (η * Real.log N + C) * ∑ i, ∑ j, |c i| * |c j| * harmonicSum (min (M i) (M j)) :=
  gaugeForm_stepProfile_of_tendsto (primeSignGauge_isSignGauge hg) (abs_kappa_le_of_tendsto hg hκ)
    (tendsto_primeSignGauge_div_log hg hκ)

/-- **Flipped density**: if the primes of `S` have logarithmic density `ϑ`, the gauge flipping
them has matching coefficient `1 − 2ϑ`. -/
theorem flipGauge_kappa (S : Set ℕ) [DecidablePred (· ∈ S)] {ϑ : ℝ}
    (hS : Tendsto (fun y : ℕ =>
      (∑ t ∈ Icc 1 y, (if t.Prime ∧ t ∈ S then Real.log t / t else 0)) / Real.log y) atTop
        (𝓝 ϑ)) :
    Tendsto (fun y : ℕ =>
      (∑ t ∈ Icc 1 y, (if t.Prime then (if t ∈ S then (-1 : ℝ) else 1) * Real.log t / t
        else 0)) / Real.log y) atTop (𝓝 (1 - 2 * ϑ)) := by
  -- Mertens for primes: `Σ_{p ≤ y} log p/p / log y → 1`
  have hlog : Tendsto (fun y : ℕ => Real.log y) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hP : Tendsto (fun y : ℕ =>
      (∑ t ∈ Icc 1 y, (if t.Prime then Real.log t / t else 0)) / Real.log y) atTop (𝓝 1) := by
    set C := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
    have hdiff : Tendsto (fun y : ℕ =>
        ((∑ t ∈ Icc 1 y, (if t.Prime then Real.log t / t else 0)) - Real.log y) / Real.log y)
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
        ((tendsto_const_nhds (x := C)).div_atTop hlog)
      filter_upwards [hlog.eventually_gt_atTop 0, eventually_ge_atTop 1] with y hy hy1
      have hm := RHTower.Mertens.mertens_first_prime y hy1
      rw [sum_filter] at hm
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy]
      exact div_le_div_of_nonneg_right hm hy.le
    have h := hdiff.add_const 1
    rw [zero_add] at h
    refine h.congr' ?_
    filter_upwards [hlog.eventually_gt_atTop 0] with y hy
    have hy' := hy.ne'
    field_simp
    ring
  have h := hP.sub (hS.const_mul 2)
  refine h.congr fun y => ?_
  rw [mul_div_assoc', ← sub_div]
  congr 1
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun t _ => ?_
  by_cases ht : t.Prime
  · by_cases hs : t ∈ S
    · rw [if_pos ht, if_pos (show t.Prime ∧ t ∈ S from ⟨ht, hs⟩), if_pos ht, if_pos hs]
      ring
    · rw [if_pos ht, if_neg (fun h : t.Prime ∧ t ∈ S => hs h.2), if_pos ht, if_neg hs]
      ring
  · rw [if_neg ht, if_neg (fun h : t.Prime ∧ t ∈ S => ht h.1), if_neg ht]
    ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
