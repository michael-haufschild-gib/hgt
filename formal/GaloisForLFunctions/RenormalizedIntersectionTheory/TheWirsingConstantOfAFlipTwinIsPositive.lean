import GaloisForLFunctions.RenormalizedIntersectionTheory.TheWirsingBoundForFlipTwins
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# The Wirsing constant of a flip twin is positive

For a sign gauge `ε` whose prime mean is `β log n + O(C)` with `β > 0`, the logarithmic sums
`L(N) = Σ_{n ≤ N} ε(n)/n` are unbounded above (`not_bddAbove_gaugeHarmonicSum`):

* if `L ≤ G`, Abel summation gives `Σ_{n ≤ N} ε(n) n^{−1−σ} ≤ G` for every `σ > 0`
  (`sum_twisted_rpow_le`), hence the Dirichlet series is at most `G`;
* the Euler product (`EulerProduct.eulerProduct_completely_multiplicative`) is at least
  `exp Σ_{p < X} ε(p) p^{−1−σ}`, since `(1 − x)^{−1} ≥ e^x`;
* Abel summation against the decreasing weight `t^{−σ}/log t` (`sum_primeWeight_mul_ge`) and
  `t^{−σ} ≥ e^{−1}` up to `t = e^{1/σ}` give `Σ_p ε(p) p^{−1−σ} ≥ (β/2e) log(1/σ) − O(1) → ∞`.

With a power error `O((1 + log n)^α)` in the prime mean, `α < β`, the same argument runs with sharp
constants (`not_le_rpow_gaugeHarmonicSum`): `L ≤ G(1 + log n)^α` gives a Dirichlet series
`≤ 2Gσ^{−α}` (`sum_twisted_rpow_le_rpow`), while Abel summation with the power-weighted error
(`exists_powerAbel_le`) and `k^{−σ} ≥ 1 − σ log k` give `Σ_p ε(p) p^{−1−σ} ≥ β log(1/σ) − O(1)`
(`exists_primeSum_rpow_ge_rpow`), so the Euler product is `≫ σ^{−β}`.

For a flip twin whose flipped primes have relative log density `κ` with error `O((1 + log n)^α)`,
`α < 1 − 2κ`, the Wirsing asymptotic `L(N) = c (log N)^{1−2κ} + O((log N)^α)` therefore has `c > 0`
(`exists_pos_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le`,
`exists_pos_mul_rpow_le_gaugeHarmonicSum_primeSetFlip`): the harmonic correlation
is `≍ (log N)^{−2κ}` from below as well as from above.
-/

open Finset Filter Topology
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (gaugeHarmonicSum)
open GaloisForLFunctions.ArithmeticCountingPositivity (primeSetFlip)
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (IsSignGauge)

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

section Abel

variable {ε : ℕ → ℝ}

theorem signGauge_map_one (hε : IsSignGauge ε) : ε 1 = 1 := by
  have h1 := hε.mul (m := 1) (n := 1) one_ne_zero one_ne_zero
  have h2 := hε.mul_self (n := 1) one_ne_zero
  rw [mul_one] at h1
  nlinarith

theorem primeMean_one (ε : ℕ → ℝ) : primeMean ε 1 = 0 := by
  unfold primeMean; rw [Icc_self, filter_singleton, if_neg Nat.not_prime_one, sum_empty]

theorem abs_signGauge_eq_one (hε : IsSignGauge ε) {n : ℕ} (hn : n ≠ 0) : |ε n| = 1 := by
  have h := hε.mul_self hn
  rcases mul_self_eq_one_iff.mp h with h' | h' <;> simp [h']

/-- **Abel summation against `n^{−σ}`.** If `L(n) ≤ G` for all `n` (and `G ≥ 0`), then
`Σ_{n ≤ N} ε(n) n^{−1−σ} ≤ G`: the invariant `T(N) + (G − L(N)) N^{−σ} ≤ G` survives each step since
`(N + 1)^{−σ} ≤ N^{−σ}`. -/
theorem sum_twisted_rpow_le {σ G : ℝ} (hσ : 0 < σ) (hG : 0 ≤ G)
    (hL : ∀ n, gaugeHarmonicSum ε n ≤ G) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ε n * (n : ℝ) ^ (-(1 + σ)) ≤ G := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [hG]
  have hinv : ∀ N, 1 ≤ N → ∑ n ∈ Icc 1 N, ε n * (n : ℝ) ^ (-(1 + σ)) +
      (G - gaugeHarmonicSum ε N) * (N : ℝ) ^ (-σ) ≤ G := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      simp only [Icc_self, sum_singleton, Nat.cast_one, Real.one_rpow, mul_one]
      unfold gaugeHarmonicSum
      simp
    | succ N hN ih =>
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
      have eT : ∑ n ∈ Icc 1 (N + 1), ε n * (n : ℝ) ^ (-(1 + σ)) =
          ∑ n ∈ Icc 1 N, ε n * (n : ℝ) ^ (-(1 + σ)) +
            ε (N + 1) * ((N : ℝ) + 1) ^ (-(1 + σ)) := by
        rw [sum_Icc_succ_top (by omega)]; push_cast; ring
      have eL : gaugeHarmonicSum ε (N + 1) = gaugeHarmonicSum ε N + ε (N + 1) / ((N : ℝ) + 1) := by
        unfold gaugeHarmonicSum; rw [sum_Icc_succ_top (by omega)]; push_cast; ring
      have epow : ((N : ℝ) + 1) ^ (-(1 + σ)) = ((N : ℝ) + 1) ^ (-σ) / ((N : ℝ) + 1) := by
        rw [show -(1 + σ) = -σ + -1 by ring, Real.rpow_add hN1, Real.rpow_neg_one]
        ring
      have hmono : ((N : ℝ) + 1) ^ (-σ) ≤ (N : ℝ) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by linarith)
      have hGL : 0 ≤ G - gaugeHarmonicSum ε N := sub_nonneg.mpr (hL N)
      rw [eT, eL, epow]
      push_cast
      have e : ∑ n ∈ Icc 1 N, ε n * (n : ℝ) ^ (-(1 + σ)) +
          ε (N + 1) * (((N : ℝ) + 1) ^ (-σ) / ((N : ℝ) + 1)) +
          (G - (gaugeHarmonicSum ε N + ε (N + 1) / ((N : ℝ) + 1))) * ((N : ℝ) + 1) ^ (-σ) =
          ∑ n ∈ Icc 1 N, ε n * (n : ℝ) ^ (-(1 + σ)) +
            (G - gaugeHarmonicSum ε N) * ((N : ℝ) + 1) ^ (-σ) := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hmono hGL]
  have h := hinv N hN
  have hp : 0 ≤ (G - gaugeHarmonicSum ε N) * (N : ℝ) ^ (-σ) :=
    mul_nonneg (sub_nonneg.mpr (hL N)) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  linarith

/-- **Abel summation of the prime terms against a decreasing weight.** If
`primeMean ε n ≥ β log n − C` and `g ≥ 0` decreases on `[2, ∞)`, then
`Σ_{2 ≤ k ≤ X, k prime} ε(k) (log k/k) g(k) ≥ β Σ_{2 ≤ k ≤ X} (log k − log(k−1)) g(k) − C g(2)`. -/
theorem sum_primeWeight_mul_ge {β C : ℝ}
    (hA : ∀ n : ℕ, 1 ≤ n → β * Real.log n - C ≤ primeMean ε n) {g : ℕ → ℝ}
    (hanti : ∀ k, 2 ≤ k → g (k + 1) ≤ g k) (hg0 : ∀ k, 2 ≤ k → 0 ≤ g k) {X : ℕ} (hX : 2 ≤ X) :
    β * ∑ k ∈ Icc 2 X, (Real.log k - Real.log ((k : ℝ) - 1)) * g k - C * g 2 ≤
      ∑ k ∈ Icc 2 X, (if k.Prime then ε k * Real.log k / k else 0) * g k := by
  set a : ℕ → ℝ := fun k => if k.Prime then ε k * Real.log k / k else 0
  have hstep : ∀ n, primeMean ε (n + 1) = primeMean ε n + a (n + 1) := fun n => by
    unfold primeMean; rw [sum_filter, sum_filter, sum_Icc_succ_top (by omega)]
  -- `Φ(X) = Σ a g − β Σ Δlog g − (A(X) − β log X) g(X) ≥ −C (g 2 − g X)`
  have hΦ : ∀ X, 2 ≤ X → -(C * (g 2 - g X)) ≤
      ∑ k ∈ Icc 2 X, a k * g k -
        β * ∑ k ∈ Icc 2 X, (Real.log k - Real.log ((k : ℝ) - 1)) * g k -
        (primeMean ε X - β * Real.log X) * g X := by
    intro X hX
    induction X, hX using Nat.le_induction with
    | base =>
      have h2 : primeMean ε 2 = a 2 := by rw [hstep 1, primeMean_one, zero_add]
      simp only [Icc_self, sum_singleton, h2, sub_self, mul_zero, neg_zero]
      norm_num
      linarith [show (a 2 - β * Real.log 2) * g 2 = a 2 * g 2 - β * (Real.log 2 * g 2) by ring]
    | succ X hX ih =>
      have hA' := hA X (by omega)
      have hg := hanti X hX
      rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), hstep X]
      push_cast
      rw [show (X : ℝ) + 1 - 1 = X by ring]
      nlinarith [mul_le_mul_of_nonneg_right (show primeMean ε X - β * Real.log X ≥ -C by linarith)
        (sub_nonneg.mpr hg)]
  have h := hΦ X hX
  have hA' := hA X (by omega)
  nlinarith [mul_le_mul_of_nonneg_right (show primeMean ε X - β * Real.log X ≥ -C by linarith)
    (hg0 X hX)]

/-- `Σ_{3 ≤ k ≤ K} (log k − log(k−1))/log k ≥ (1/2)(log log K − log log 2)`. -/
theorem sum_logIncrement_div_log_ge {K : ℕ} (hK : 2 ≤ K) :
    (Real.log (Real.log K) - Real.log (Real.log 2)) / 2 ≤
      ∑ k ∈ Icc 3 K, (Real.log k - Real.log ((k : ℝ) - 1)) / Real.log k := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [sum_Icc_succ_top (by omega)]
    push_cast
    rw [show (K : ℝ) + 1 - 1 = K by ring]
    have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
    have hu : 0 < Real.log K := Real.log_pos (by linarith)
    have huv : Real.log K ≤ Real.log ((K : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
    have hv : 0 < Real.log ((K : ℝ) + 1) := hu.trans_le huv
    have hv2 : Real.log ((K : ℝ) + 1) ≤ 2 * Real.log K := by
      rw [← Real.log_rpow (by linarith), Real.rpow_two]
      exact Real.log_le_log (by linarith) (by nlinarith)
    -- `log v − log u ≤ v/u − 1 = (v − u)/u ≤ 2(v − u)/v`
    have hll : Real.log (Real.log ((K : ℝ) + 1)) - Real.log (Real.log K) ≤
        2 * ((Real.log ((K : ℝ) + 1) - Real.log K) / Real.log ((K : ℝ) + 1)) := by
      rw [← Real.log_div hv.ne' hu.ne']
      refine (Real.log_le_sub_one_of_pos (div_pos hv hu)).trans ?_
      rw [div_sub_one hu.ne', mul_div_assoc', div_le_div_iff₀ hu hv]
      nlinarith
    linarith

end Abel

section Euler

variable {ε : ℕ → ℝ}

/-- `n ↦ ε(n) n^{−1−σ}` as a completely multiplicative function. -/
def twistedDirichletHom (hε : IsSignGauge ε) (σ : ℝ) : ℕ →*₀ ℝ where
  toFun n := if n = 0 then 0 else ε n * (n : ℝ) ^ (-(1 + σ))
  map_zero' := by simp
  map_one' := by simp [signGauge_map_one hε]
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [mul_eq_zero, hm, hn, or_self, if_false]
    rw [hε.mul hm hn, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring

theorem twistedDirichletHom_apply (hε : IsSignGauge ε) (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    twistedDirichletHom hε σ n = ε n * (n : ℝ) ^ (-(1 + σ)) := if_neg hn

theorem summable_norm_twistedDirichletHom (hε : IsSignGauge ε) {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n => ‖twistedDirichletHom hε σ n‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (Real.summable_nat_rpow.mpr (show -(1 + σ) < -1 by linarith))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [twistedDirichletHom]
    exact Real.rpow_nonneg le_rfl _
  rw [twistedDirichletHom_apply hε σ hn.ne', Real.norm_eq_abs, abs_mul, abs_signGauge_eq_one hε hn.ne',
    one_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]

/-- If `L ≤ G`, the twisted Dirichlet series at `1 + σ` is at most `G`. -/
theorem tsum_twistedDirichletHom_le (hε : IsSignGauge ε) {σ G : ℝ} (hσ : 0 < σ) (hG : 0 ≤ G)
    (hL : ∀ n, gaugeHarmonicSum ε n ≤ G) :
    ∑' n, twistedDirichletHom hε σ n ≤ G := by
  have hs := (summable_norm_twistedDirichletHom hε hσ).of_norm
  refine le_of_tendsto' hs.hasSum.tendsto_sum_nat fun N => ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa using hG
  have e : ∑ n ∈ range N, twistedDirichletHom hε σ n =
      ∑ n ∈ Icc 1 (N - 1), ε n * (n : ℝ) ^ (-(1 + σ)) := by
    rw [← Nat.sub_add_cancel hN, sum_range_succ', Nat.add_sub_cancel, sumIcc_eq_sumRange]
    simp only [map_zero, add_zero]
    exact sum_congr rfl fun i _ => by
      rw [twistedDirichletHom_apply hε σ (Nat.succ_ne_zero i)]
  rw [e]
  exact sum_twisted_rpow_le hσ hG hL (N - 1)

/-- **Euler lower bound**: the twisted Dirichlet series at `1 + σ` is at least
`exp Σ_{p < X} ε(p) p^{−1−σ}` whenever all larger cutoffs keep the prime sum above a level. -/
theorem exp_le_tsum_twistedDirichletHom (hε : IsSignGauge ε) {σ M : ℝ} (hσ : 0 < σ) {X₀ : ℕ}
    (hM : ∀ X, X₀ ≤ X → M ≤ ∑ p ∈ Nat.primesBelow X, ε p * (p : ℝ) ^ (-(1 + σ))) :
    Real.exp M ≤ ∑' n, twistedDirichletHom hε σ n := by
  have hT := EulerProduct.eulerProduct_completely_multiplicative
    (summable_norm_twistedDirichletHom hε hσ)
  refine ge_of_tendsto hT ?_
  filter_upwards [eventually_ge_atTop X₀] with X hX
  have hfac : ∀ p ∈ Nat.primesBelow X, Real.exp (ε p * (p : ℝ) ^ (-(1 + σ))) ≤
      (1 - twistedDirichletHom hε σ p)⁻¹ := by
    intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp).2
    rw [twistedDirichletHom_apply hε σ hpp.ne_zero]
    set x := ε p * (p : ℝ) ^ (-(1 + σ))
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hxlt : x < 1 := by
      have hpow : (p : ℝ) ^ (-(1 + σ)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
      have habs : |x| = (p : ℝ) ^ (-(1 + σ)) := by
        simp only [x, abs_mul, abs_signGauge_eq_one hε hpp.ne_zero, one_mul,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
      linarith [le_abs_self x]
    have h1 : 0 < 1 - x := by linarith
    rw [le_inv_comm₀ (Real.exp_pos _) h1, ← Real.exp_neg]
    linarith [Real.add_one_le_exp (-x)]
  calc Real.exp M ≤ Real.exp (∑ p ∈ Nat.primesBelow X, ε p * (p : ℝ) ^ (-(1 + σ))) :=
        Real.exp_le_exp.mpr (hM X hX)
    _ = ∏ p ∈ Nat.primesBelow X, Real.exp (ε p * (p : ℝ) ^ (-(1 + σ))) := Real.exp_sum _ _
    _ ≤ ∏ p ∈ Nat.primesBelow X, (1 - twistedDirichletHom hε σ p)⁻¹ :=
        prod_le_prod (fun _ _ => (Real.exp_pos _).le) hfac

end Euler

section Unbounded

variable {ε : ℕ → ℝ}

/-- **The prime sum at `σ = 1/log K` grows like `(β/2e) log log K`.** -/
theorem primeSum_rpow_ge {β C : ℝ} (hβ : 0 < β)
    (hA : ∀ n : ℕ, 1 ≤ n → β * Real.log n - C ≤ primeMean ε n) {K : ℕ} (hK : 3 ≤ K) {X : ℕ}
    (hX : K + 1 ≤ X) :
    β * (Real.exp (-1) * ((Real.log (Real.log K) - Real.log (Real.log 2)) / 2)) -
        C / Real.log 2 ≤
      ∑ p ∈ Nat.primesBelow X, ε p * (p : ℝ) ^ (-(1 + 1 / Real.log K)) := by
  set σ := 1 / Real.log K
  have hlK : 1 ≤ Real.log K := one_le_log_of_three_le hK
  have hσ : 0 < σ := by positivity
  set g : ℕ → ℝ := fun k => (k : ℝ) ^ (-σ) / Real.log k
  have hanti : ∀ k, 2 ≤ k → g (k + 1) ≤ g k := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hl : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    have hl' : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log hk0 (by push_cast; linarith)
    have hnum : ((k + 1 : ℕ) : ℝ) ^ (-σ) ≤ (k : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hk0 (by push_cast; linarith) (by linarith)
    exact div_le_div₀ (Real.rpow_nonneg hk0.le _) hnum hl hl'
  have hX2 : 2 ≤ X - 1 := by omega
  have hg0 : ∀ k, 2 ≤ k → 0 ≤ g k := fun k hk =>
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) (Real.log_natCast_nonneg k)
  have hAbel := sum_primeWeight_mul_ge hA hanti hg0 hX2
  -- the prime sum over `primesBelow X` is the Abel sum over `[2, X − 1]`
  have hsum : ∑ k ∈ Icc 2 (X - 1), (if k.Prime then ε k * Real.log k / k else 0) * g k =
      ∑ p ∈ Nat.primesBelow X, ε p * (p : ℝ) ^ (-(1 + σ)) := by
    have hset : Nat.primesBelow X = (Icc 2 (X - 1)).filter Nat.Prime := by
      ext p
      simp only [Nat.mem_primesBelow, mem_filter, mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2.two_le, by omega⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3⟩
    rw [hset, sum_filter]
    refine sum_congr rfl fun k hk => ?_
    split_ifs with hp
    · have hk0 : (0 : ℝ) < k := by exact_mod_cast hp.pos
      have hl : 0 < Real.log k := Real.log_pos (by exact_mod_cast hp.one_lt)
      simp only [g]
      rw [show -(1 + σ) = -1 + -σ by ring, Real.rpow_add hk0, Real.rpow_neg_one]
      field_simp
    · simp
  rw [← hsum]
  refine le_trans ?_ hAbel
  -- `Σ_{2 ≤ k < X} Δlog k · g(k) ≥ e^{−1} Σ_{3 ≤ k ≤ K} Δlog k/log k`
  have hg2 : g 2 ≤ 1 / Real.log 2 := by
    simp only [g]
    have h2 : (2 : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    push_cast
    exact div_le_div_of_nonneg_right h2 (Real.log_pos (by norm_num)).le
  have hC0 : 0 ≤ C := by
    have := hA 1 le_rfl
    rw [primeMean_one] at this
    simpa using this
  have hlow : Real.exp (-1) * ((Real.log (Real.log K) - Real.log (Real.log 2)) / 2) ≤
      ∑ k ∈ Icc 2 (X - 1), (Real.log k - Real.log ((k : ℝ) - 1)) * g k := by
    have hsub : Icc 3 K ⊆ Icc 2 (X - 1) := Icc_subset_Icc (by norm_num) (by omega)
    have hnn : ∀ k ∈ Icc 2 (X - 1), k ∉ Icc 3 K →
        0 ≤ (Real.log k - Real.log ((k : ℝ) - 1)) * g k := by
      intro k hk _
      have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
      refine mul_nonneg (sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith)))
        (div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg (by linarith)))
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub hnn)
    have hterm : ∀ k ∈ Icc 3 K, Real.exp (-1) * ((Real.log k - Real.log ((k : ℝ) - 1)) /
        Real.log k) ≤ (Real.log k - Real.log ((k : ℝ) - 1)) * g k := by
      intro k hk
      obtain ⟨hk3, hkK⟩ := mem_Icc.mp hk
      have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      have hl : 0 < Real.log k := Real.log_pos (by linarith)
      have hd : 0 ≤ Real.log k - Real.log ((k : ℝ) - 1) :=
        sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
      have hlk : Real.log k ≤ Real.log K :=
        Real.log_le_log (by linarith) (by exact_mod_cast hkK)
      have hpow : Real.exp (-1) ≤ (k : ℝ) ^ (-σ) := by
        rw [Real.rpow_def_of_pos (by linarith)]
        refine Real.exp_le_exp.mpr ?_
        have : Real.log k * σ ≤ 1 := by
          simp only [σ]; rw [mul_one_div, div_le_one (by linarith)]; exact hlk
        nlinarith
      simp only [g]
      rw [mul_div_assoc', mul_comm (Real.exp (-1)), mul_div_assoc', div_le_div_iff_of_pos_right hl]
      exact mul_le_mul_of_nonneg_left hpow hd
    calc Real.exp (-1) * ((Real.log (Real.log K) - Real.log (Real.log 2)) / 2)
        ≤ Real.exp (-1) * ∑ k ∈ Icc 3 K, (Real.log k - Real.log ((k : ℝ) - 1)) / Real.log k :=
          mul_le_mul_of_nonneg_left (sum_logIncrement_div_log_ge (by omega)) (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_sum]; exact sum_le_sum hterm
  have := mul_le_mul_of_nonneg_left hlow hβ.le
  have := mul_le_mul_of_nonneg_left hg2 hC0
  rw [mul_one_div] at this
  linarith

/-- **Unbounded harmonic sums.** A sign gauge with prime mean `β log n + O(C)`, `β > 0`, has
`L(N) = Σ_{n ≤ N} ε(n)/n` unbounded above. -/
theorem not_bddAbove_gaugeHarmonicSum (hε : IsSignGauge ε) {β C : ℝ} (hβ : 0 < β)
    (hA : ∀ n, 1 ≤ n → |primeMean ε n - β * Real.log n| ≤ C) (G : ℝ) :
    ∃ N, G < gaugeHarmonicSum ε N := by
  by_contra hcon
  push Not at hcon
  set G' := max G 1
  have hG' : 0 ≤ G' := (zero_le_one).trans (le_max_right _ _)
  have hL : ∀ n, gaugeHarmonicSum ε n ≤ G' := fun n => (hcon n).trans (le_max_left _ _)
  have hA' : ∀ n : ℕ, 1 ≤ n → β * Real.log n - C ≤ primeMean ε n := fun n hn => by
    have := (abs_le.mp (hA n hn)).1; linarith
  -- choose `K` with `(β/2e)(log log K − log log 2) − C/log 2 > log G'`
  have hll : Tendsto (fun K : ℕ => Real.log (Real.log K)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨K, hK3, hKbig⟩ := ((eventually_ge_atTop 3).and (hll.eventually_gt_atTop
    (Real.log (Real.log 2) + 2 * Real.exp 1 * (Real.log G' + C / Real.log 2 + 1) / β))).exists
  have hlK : 1 ≤ Real.log K := one_le_log_of_three_le hK3
  have hσ : 0 < 1 / Real.log K := by positivity
  have hup := tsum_twistedDirichletHom_le hε hσ hG' hL
  have hdown := exp_le_tsum_twistedDirichletHom hε hσ (X₀ := K + 1)
    (fun X hX => primeSum_rpow_ge hβ hA' hK3 hX)
  have hlevel : Real.log G' < β * (Real.exp (-1) * ((Real.log (Real.log K) -
      Real.log (Real.log 2)) / 2)) - C / Real.log 2 := by
    have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    have hepos : 0 < Real.exp 1 := Real.exp_pos 1
    have h1 : 2 * Real.exp 1 * (Real.log G' + C / Real.log 2 + 1) / β <
        Real.log (Real.log K) - Real.log (Real.log 2) := by linarith
    rw [div_lt_iff₀ hβ] at h1
    have h2 : Real.exp (-1) * (2 * Real.exp 1 * (Real.log G' + C / Real.log 2 + 1)) <
        Real.exp (-1) * ((Real.log (Real.log K) - Real.log (Real.log 2)) * β) :=
      mul_lt_mul_of_pos_left h1 (Real.exp_pos _)
    have h3 : Real.exp (-1) * (2 * Real.exp 1 * (Real.log G' + C / Real.log 2 + 1)) =
        2 * (Real.log G' + C / Real.log 2 + 1) := by
      rw [show Real.exp (-1) * (2 * Real.exp 1 * (Real.log G' + C / Real.log 2 + 1)) =
        (Real.exp (-1) * Real.exp 1) * (2 * (Real.log G' + C / Real.log 2 + 1)) by ring, he,
        one_mul]
    nlinarith
  have hexp : G' < Real.exp (β * (Real.exp (-1) * ((Real.log (Real.log K) -
      Real.log (Real.log 2)) / 2)) - C / Real.log 2) := by
    calc G' = Real.exp (Real.log G') := (Real.exp_log (by positivity)).symm
      _ < _ := Real.exp_lt_exp.mpr hlevel
  linarith

end Unbounded

section PowerError

/-- `Σ_{a ≤ k ≤ M} (F k − F (k − 1)) = F M − F (a − 1)`. -/
theorem sum_Icc_sub_pred (F : ℕ → ℝ) {a M : ℕ} (ha : 1 ≤ a) (haM : a - 1 ≤ M) :
    ∑ k ∈ Icc a M, (F k - F (k - 1)) = F M - F (a - 1) := by
  induction M, haM using Nat.le_induction with
  | base => rw [Icc_eq_empty (by omega), sum_empty, sub_self]
  | succ M hM ih =>
    rw [sum_Icc_succ_top (by omega), ih, Nat.add_sub_cancel]
    ring

theorem natCast_pred {k : ℕ} (hk : 1 ≤ k) : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
  rw [Nat.cast_sub hk, Nat.cast_one]

/-- `σ Δlog k · k^{−σ} ≤ (k − 1)^{−σ} − k^{−σ}`. -/
theorem logIncrement_mul_rpow_le {k : ℕ} (hk : 2 ≤ k) {σ : ℝ} :
    σ * ((Real.log k - Real.log ((k : ℝ) - 1)) * (k : ℝ) ^ (-σ)) ≤
      ((k : ℝ) - 1) ^ (-σ) - (k : ℝ) ^ (-σ) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < (k : ℝ) - 1),
    Real.rpow_def_of_pos (by linarith : (0 : ℝ) < k)]
  set y := σ * (Real.log k - Real.log ((k : ℝ) - 1))
  have hy : Real.exp (Real.log ((k : ℝ) - 1) * -σ) = Real.exp (Real.log k * -σ) * Real.exp y := by
    rw [← Real.exp_add]; congr 1; simp only [y]; ring
  rw [hy]
  have h1 := Real.add_one_le_exp y
  have he := Real.exp_pos (Real.log k * -σ)
  calc σ * ((Real.log k - Real.log ((k : ℝ) - 1)) * Real.exp (Real.log k * -σ)) =
        Real.exp (Real.log k * -σ) * y := by simp only [y]; ring
    _ ≤ Real.exp (Real.log k * -σ) * (Real.exp y - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) he.le
    _ = _ := by ring

/-- `x^α (1/x − 1/y) ≤ (x^{α−1} − y^{α−1})/(1 − α)` for `0 < x ≤ y`, `0 ≤ α < 1` (Bernoulli for the
exponent `1 − α`). -/
theorem rpow_mul_inv_sub_le {x y α : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    x ^ α * (1 / x - 1 / y) ≤ (x ^ (α - 1) - y ^ (α - 1)) / (1 - α) := by
  have hy : 0 < y := hx.trans_le hxy
  set t := x / y
  have ht0 : 0 < t := div_pos hx hy
  have ht1 : t ≤ 1 := (div_le_one hy).mpr hxy
  have hB : t ^ (1 - α) ≤ 1 + (1 - α) * (t - 1) := by
    have := rpow_one_add_le_one_add_mul_self (s := t - 1) (p := 1 - α) (by linarith) (by linarith)
      (by linarith)
    rwa [show 1 + (t - 1) = t by ring] at this
  have hyt : y = x / t := by simp only [t]; field_simp
  have hy' : y ^ (α - 1) = x ^ (α - 1) * t ^ (1 - α) := by
    rw [hyt, Real.div_rpow hx.le ht0.le, div_eq_mul_inv, ← Real.rpow_neg ht0.le, neg_sub]
  have hlhs : x ^ α * (1 / x - 1 / y) = x ^ (α - 1) * (1 - t) := by
    rw [Real.rpow_sub_one hx.ne']; simp only [t]; field_simp
  rw [hlhs, hy', le_div_iff₀ (by linarith)]
  have hxa : 0 < x ^ (α - 1) := Real.rpow_pos_of_pos hx _
  nlinarith [mul_le_mul_of_nonneg_left hB hxa.le]

/-- **The power-weighted Abel error is bounded**: for `0 ≤ α < 1` there is `E₀` with
`(1 + log X)^α g(X) + Σ_{2 ≤ k < X} (1 + log k)^α (g(k) − g(k + 1)) ≤ E₀` for `g(k) = k^{−σ}/log k`,
uniformly in `σ ∈ (0, 1]` and `X ≥ 2`. -/
theorem exists_powerAbel_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ E₀ : ℝ, ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ X : ℕ, 2 ≤ X →
      (1 + Real.log X) ^ α * ((X : ℝ) ^ (-σ) / Real.log X) +
        ∑ k ∈ Ico 2 X, (1 + Real.log k) ^ α *
          ((k : ℝ) ^ (-σ) / Real.log k - ((k + 1 : ℕ) : ℝ) ^ (-σ) / Real.log ((k + 1 : ℕ) : ℝ)) ≤
        E₀ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨3 + 3 / Real.log 2 + 2 / (1 - α), fun σ hσ hσ1 X hX => ?_⟩
  -- weights: `(1 + log k)^α ≤ 1 + log k`, `≤ 2 (log k)^α` for `k ≥ 3`
  have hw1 : ∀ k : ℕ, 1 ≤ k → (1 + Real.log k) ^ α ≤ 1 + Real.log k := fun k hk => by
    have h1 : 1 ≤ 1 + Real.log k := by linarith [Real.log_natCast_nonneg k]
    calc (1 + Real.log k) ^ α ≤ (1 + Real.log k) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 hα1.le
      _ = 1 + Real.log k := Real.rpow_one _
  have hw2 : ∀ k : ℕ, 3 ≤ k → (1 + Real.log k) ^ α ≤ 2 * Real.log k ^ α := fun k hk => by
    have hl := one_le_log_of_three_le hk
    calc (1 + Real.log k) ^ α ≤ (2 * Real.log k) ^ α := Real.rpow_le_rpow (by linarith) (by linarith) hα0
      _ = 2 ^ α * Real.log k ^ α := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 2 * Real.log k ^ α := mul_le_mul_of_nonneg_right
          (by calc (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1.le
                _ = 2 := Real.rpow_one 2) (Real.rpow_nonneg (by linarith) _)
  -- the boundary term
  have hbd : (1 + Real.log X) ^ α * ((X : ℝ) ^ (-σ) / Real.log X) ≤ 1 + 1 / Real.log 2 := by
    have hX2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
    have hlX : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
    have hlX0 : 0 < Real.log X := hl2.trans_le hlX
    have hp : (X : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hp0 : 0 ≤ (X : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
    calc (1 + Real.log X) ^ α * ((X : ℝ) ^ (-σ) / Real.log X) ≤
          (1 + Real.log X) * (1 / Real.log X) :=
          mul_le_mul (hw1 X (by omega)) (div_le_div_of_nonneg_right hp hlX0.le)
            (div_nonneg hp0 hlX0.le) (by linarith)
      _ = 1 / Real.log X + 1 := by field_simp
      _ ≤ 1 / Real.log 2 + 1 := by
          have := one_div_le_one_div_of_le hl2 hlX; linarith
      _ = 1 + 1 / Real.log 2 := by ring
  -- split each difference of `g`
  have hsplit : ∀ k ∈ Ico 2 X, (1 + Real.log k) ^ α *
      ((k : ℝ) ^ (-σ) / Real.log k - ((k + 1 : ℕ) : ℝ) ^ (-σ) / Real.log ((k + 1 : ℕ) : ℝ)) ≤
        (1 + Real.log k) ^ α * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) +
          2 * ((k : ℝ) ^ (-σ) - ((k + 1 : ℕ) : ℝ) ^ (-σ)) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Ico.mp hk).1
    have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hk1]
    have hl : 0 < Real.log k := Real.log_pos (by linarith)
    have hl' : Real.log k ≤ Real.log ((k : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
    have hl3 : 1 ≤ Real.log ((k : ℝ) + 1) := by
      have := one_le_log_of_three_le (show 3 ≤ k + 1 by have := (mem_Ico.mp hk).1; omega)
      simpa using this
    have hp : (k : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hp0 : 0 ≤ (k : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
    have hpk : ((k : ℝ) + 1) ^ (-σ) ≤ (k : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have hw := hw1 k (by have := (mem_Ico.mp hk).1; omega)
    have hw0 : 0 ≤ (1 + Real.log k) ^ α := Real.rpow_nonneg (by linarith) _
    have hdiff : 0 ≤ 1 / Real.log k - 1 / Real.log ((k : ℝ) + 1) :=
      sub_nonneg.mpr (one_div_le_one_div_of_le hl hl')
    have e : (k : ℝ) ^ (-σ) / Real.log k - ((k : ℝ) + 1) ^ (-σ) / Real.log ((k : ℝ) + 1) =
        (k : ℝ) ^ (-σ) * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) +
          ((k : ℝ) ^ (-σ) - ((k : ℝ) + 1) ^ (-σ)) / Real.log ((k : ℝ) + 1) := by
      field_simp; ring
    rw [e, mul_add]
    have h1 : (1 + Real.log k) ^ α * ((k : ℝ) ^ (-σ) * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1))) ≤
        (1 + Real.log k) ^ α * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) := by
      refine mul_le_mul_of_nonneg_left ?_ hw0
      calc (k : ℝ) ^ (-σ) * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) ≤
            1 * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_right hp hdiff
        _ = _ := one_mul _
    have h2 : (1 + Real.log k) ^ α * (((k : ℝ) ^ (-σ) - ((k : ℝ) + 1) ^ (-σ)) /
        Real.log ((k : ℝ) + 1)) ≤ 2 * ((k : ℝ) ^ (-σ) - ((k : ℝ) + 1) ^ (-σ)) := by
      have hratio : (1 + Real.log k) ^ α / Real.log ((k : ℝ) + 1) ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hd0 : 0 ≤ (k : ℝ) ^ (-σ) - ((k : ℝ) + 1) ^ (-σ) := by linarith
      calc (1 + Real.log k) ^ α * (((k : ℝ) ^ (-σ) - ((k : ℝ) + 1) ^ (-σ)) /
            Real.log ((k : ℝ) + 1)) =
            (1 + Real.log k) ^ α / Real.log ((k : ℝ) + 1) *
              ((k : ℝ) ^ (-σ) - ((k : ℝ) + 1) ^ (-σ)) := by ring
        _ ≤ 2 * ((k : ℝ) ^ (-σ) - ((k : ℝ) + 1) ^ (-σ)) := mul_le_mul_of_nonneg_right hratio hd0
    linarith
  refine (add_le_add hbd (sum_le_sum hsplit)).trans ?_
  rw [sum_add_distrib, ← mul_sum]
  -- the `σ`-telescoping part
  have htelσ : ∑ k ∈ Ico 2 X, ((k : ℝ) ^ (-σ) - ((k + 1 : ℕ) : ℝ) ^ (-σ)) ≤ 1 := by
    have h := Finset.sum_range_sub (fun j => -(((j + 2 : ℕ) : ℝ) ^ (-σ))) (X - 2)
    have e : ∑ k ∈ Ico 2 X, ((k : ℝ) ^ (-σ) - ((k + 1 : ℕ) : ℝ) ^ (-σ)) =
        ∑ j ∈ range (X - 2), (-(((j + 1 + 2 : ℕ) : ℝ) ^ (-σ)) - -(((j + 2 : ℕ) : ℝ) ^ (-σ))) := by
      rw [sum_Ico_eq_sum_range]
      refine sum_congr (by congr 1) fun j _ => ?_
      push_cast; ring_nf
    rw [e, h]
    have h1 : ((0 + 2 : ℕ) : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have h2 : 0 ≤ ((X - 2 + 2 : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  -- the `α`-telescoping part
  have htelα : ∑ k ∈ Ico 2 X, (1 + Real.log k) ^ α *
      (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤ 2 / Real.log 2 + 2 / (1 - α) := by
    rcases Nat.lt_or_ge X 3 with hX3 | hX3
    · have : Ico 2 X ⊆ {2} := fun k hk => by
        rw [mem_singleton]; have := mem_Ico.mp hk; omega
      refine (sum_le_sum_of_subset_of_nonneg this fun k hk _ => ?_).trans ?_
      · rw [mem_singleton] at hk
        subst hk
        refine mul_nonneg (Real.rpow_nonneg (by linarith [Real.log_natCast_nonneg 2]) _)
          (sub_nonneg.mpr (one_div_le_one_div_of_le (Real.log_pos (by norm_num))
            (Real.log_le_log (by norm_num) (by push_cast; norm_num))))
      · rw [sum_singleton]
        have h3 : 0 < Real.log ((2 + 1 : ℕ) : ℝ) := Real.log_pos (by norm_num)
        have hw := hw1 2 (by norm_num)
        have hle : (1 + Real.log ((2 : ℕ) : ℝ)) ≤ 2 := by
          have := Real.log_two_lt_d9; push_cast; linarith
        have hpos : 0 ≤ 1 / Real.log ((2 : ℕ) : ℝ) - 1 / Real.log ((2 + 1 : ℕ) : ℝ) := by
          refine sub_nonneg.mpr (one_div_le_one_div_of_le (by push_cast; exact hl2) ?_)
          exact Real.log_le_log (by norm_num) (by push_cast; norm_num)
        have hα2 : 0 < 2 / (1 - α) := div_pos two_pos (by linarith)
        calc (1 + Real.log ((2 : ℕ) : ℝ)) ^ α * (1 / Real.log ((2 : ℕ) : ℝ) -
              1 / Real.log ((2 + 1 : ℕ) : ℝ)) ≤ 2 * (1 / Real.log 2) := by
              refine mul_le_mul (hw.trans hle) ?_ hpos (by norm_num)
              push_cast
              have : 0 < 1 / Real.log ((2 : ℝ) + 1) := by
                have : 0 < Real.log ((2 : ℝ) + 1) := Real.log_pos (by norm_num)
                positivity
              linarith
          _ ≤ _ := by rw [mul_one_div]; linarith
    · have hsplit2 : Ico 2 X = insert 2 (Ico 3 X) := by
        ext k; simp only [mem_Ico, mem_insert]; omega
      rw [hsplit2, sum_insert (by simp)]
      have hfirst : (1 + Real.log ((2 : ℕ) : ℝ)) ^ α * (1 / Real.log ((2 : ℕ) : ℝ) -
          1 / Real.log ((2 + 1 : ℕ) : ℝ)) ≤ 2 / Real.log 2 := by
        have hw := hw1 2 (by norm_num)
        have hle : (1 + Real.log ((2 : ℕ) : ℝ)) ≤ 2 := by
          have := Real.log_two_lt_d9; push_cast; linarith
        have hpos : 0 ≤ 1 / Real.log ((2 : ℕ) : ℝ) - 1 / Real.log ((2 + 1 : ℕ) : ℝ) := by
          refine sub_nonneg.mpr (one_div_le_one_div_of_le (by push_cast; exact hl2) ?_)
          exact Real.log_le_log (by norm_num) (by push_cast; norm_num)
        calc _ ≤ 2 * (1 / Real.log ((2 : ℕ) : ℝ)) := by
              refine mul_le_mul (hw.trans hle) ?_ hpos (by norm_num)
              have : 0 < 1 / Real.log ((2 + 1 : ℕ) : ℝ) := by
                have : 0 < Real.log ((2 + 1 : ℕ) : ℝ) := Real.log_pos (by norm_num)
                positivity
              linarith
          _ = 2 / Real.log 2 := by push_cast; ring
      have hrest : ∑ k ∈ Ico 3 X, (1 + Real.log k) ^ α *
          (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤ 2 / (1 - α) := by
        set F : ℕ → ℝ := fun k => -(2 / (1 - α)) * Real.log ((k + 1 : ℕ) : ℝ) ^ (α - 1)
        have hterm : ∀ k ∈ Ico 3 X, (1 + Real.log k) ^ α *
            (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤ F k - F (k - 1) := by
          intro k hk
          have hk3 := (mem_Ico.mp hk).1
          have hl := one_le_log_of_three_le hk3
          have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
          have hl' : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
            Real.log_le_log (by linarith) (by push_cast; linarith)
          have hkey := rpow_mul_inv_sub_le (by linarith : 0 < Real.log k) hl' hα0 hα1
          have hdiff : 0 ≤ 1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ) :=
            sub_nonneg.mpr (one_div_le_one_div_of_le (by linarith) hl')
          have hk1 : (k - 1 + 1 : ℕ) = k := by omega
          simp only [F]
          rw [hk1]
          have hw := hw2 k hk3
          calc (1 + Real.log k) ^ α * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
                2 * Real.log k ^ α * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_right hw hdiff
            _ ≤ 2 * ((Real.log k ^ (α - 1) - Real.log ((k + 1 : ℕ) : ℝ) ^ (α - 1)) / (1 - α)) := by
                rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hkey (by norm_num)
            _ = _ := by field_simp; ring
        have hnn : ∀ k ∈ Ico 3 X, 0 ≤ F k - F (k - 1) := fun k hk => by
          have hk3 := (mem_Ico.mp hk).1
          have hl := one_le_log_of_three_le hk3
          have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
          have hl' : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
            Real.log_le_log (by linarith) (by push_cast; linarith)
          have hk1 : (k - 1 + 1 : ℕ) = k := by omega
          simp only [F]
          rw [hk1]
          have := Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < Real.log k) hl'
            (by linarith : α - 1 ≤ 0)
          have h2 : 0 ≤ 2 / (1 - α) := div_nonneg (by norm_num) (by linarith)
          nlinarith
        have hIcc : Ico 3 X = Icc 3 (X - 1) := by ext k; simp only [mem_Ico, mem_Icc]; omega
        calc _ ≤ ∑ k ∈ Ico 3 X, (F k - F (k - 1)) := sum_le_sum hterm
          _ = F (X - 1) - F 2 := by rw [hIcc, sum_Icc_sub_pred F (by norm_num) (by omega)]
          _ ≤ 2 / (1 - α) := by
              simp only [F]
              have h3 : (2 + 1 : ℕ) = 3 := rfl
              rw [h3]
              have hl3 : 1 ≤ Real.log ((3 : ℕ) : ℝ) := one_le_log_of_three_le le_rfl
              have hp3 : Real.log ((3 : ℕ) : ℝ) ^ (α - 1) ≤ 1 :=
                Real.rpow_le_one_of_one_le_of_nonpos hl3 (by linarith)
              have hpX : 0 ≤ Real.log ((X - 1 + 1 : ℕ) : ℝ) ^ (α - 1) :=
                Real.rpow_nonneg (Real.log_natCast_nonneg _) _
              have h2 : 0 ≤ 2 / (1 - α) := div_nonneg (by norm_num) (by linarith)
              have h4 := mul_le_mul_of_nonneg_left hp3 h2
              have h5 := mul_nonneg h2 hpX
              linarith
      linarith
  have e1 : (2 : ℝ) / Real.log 2 = 2 * (1 / Real.log 2) := by ring
  have e2 : (3 : ℝ) / Real.log 2 = 3 * (1 / Real.log 2) := by ring
  rw [e1] at htelα
  rw [e2]
  linarith

/-- **Abel summation with a power error.** If `primeMean ε n ≥ β log n − C (1 + log n)^α` and `g ≥ 0`
decreases on `[2, ∞)`, then `Σ_{2 ≤ k ≤ X, k prime} ε(k)(log k/k) g(k) ≥ β Σ Δlog k g(k) − C E(X)` with
`E(X) = (1 + log X)^α g(X) + Σ_{2 ≤ k < X} (1 + log k)^α (g(k) − g(k + 1))`. -/
theorem sum_primeWeight_mul_ge_rpow {ε : ℕ → ℝ} {β C α : ℝ}
    (hA : ∀ n : ℕ, 1 ≤ n → β * Real.log n - C * (1 + Real.log n) ^ α ≤ primeMean ε n)
    {g : ℕ → ℝ} (hanti : ∀ k, 2 ≤ k → g (k + 1) ≤ g k) (hg0 : ∀ k, 2 ≤ k → 0 ≤ g k) {X : ℕ}
    (hX : 2 ≤ X) :
    β * ∑ k ∈ Icc 2 X, (Real.log k - Real.log ((k : ℝ) - 1)) * g k -
        C * ((1 + Real.log X) ^ α * g X +
          ∑ k ∈ Ico 2 X, (1 + Real.log k) ^ α * (g k - g (k + 1))) ≤
      ∑ k ∈ Icc 2 X, (if k.Prime then ε k * Real.log k / k else 0) * g k := by
  set a : ℕ → ℝ := fun k => if k.Prime then ε k * Real.log k / k else 0
  have hstep : ∀ n, primeMean ε (n + 1) = primeMean ε n + a (n + 1) := fun n => by
    unfold primeMean; rw [sum_filter, sum_filter, sum_Icc_succ_top (by omega)]
  have hΦ : ∀ X : ℕ, 2 ≤ X → -(C * ∑ k ∈ Ico 2 X, (1 + Real.log k) ^ α * (g k - g (k + 1))) ≤
      ∑ k ∈ Icc 2 X, a k * g k -
        β * ∑ k ∈ Icc 2 X, (Real.log k - Real.log ((k : ℝ) - 1)) * g k -
        (primeMean ε X - β * Real.log X) * g X := by
    intro X hX
    induction X, hX using Nat.le_induction with
    | base =>
      have h2 : primeMean ε 2 = a 2 := by rw [hstep 1, primeMean_one, zero_add]
      simp only [Icc_self, sum_singleton, h2, Ico_self, sum_empty, mul_zero, neg_zero]
      norm_num
      linarith [show (a 2 - β * Real.log 2) * g 2 = a 2 * g 2 - β * (Real.log 2 * g 2) by ring]
    | succ X hX ih =>
      have hA' := hA X (by omega)
      have hg := hanti X hX
      rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), hstep X,
        sum_Ico_succ_top hX]
      push_cast
      rw [show (X : ℝ) + 1 - 1 = X by ring]
      nlinarith [mul_le_mul_of_nonneg_right
        (show primeMean ε X - β * Real.log X ≥ -(C * (1 + Real.log X) ^ α) by linarith)
        (sub_nonneg.mpr hg)]
  have h := hΦ X hX
  have hA' := hA X (by omega)
  nlinarith [mul_le_mul_of_nonneg_right
    (show primeMean ε X - β * Real.log X ≥ -(C * (1 + Real.log X) ^ α) by linarith) (hg0 X hX)]

/-- `Δlog k/log k ≥ Δ log log k − (Δlog k)²/(log k log(k − 1))` for `k ≥ 3`. -/
theorem logIncrement_div_log_ge {k : ℕ} (hk : 3 ≤ k) :
    Real.log (Real.log k) - Real.log (Real.log ((k : ℝ) - 1)) -
        (Real.log k - Real.log ((k : ℝ) - 1)) ^ 2 / (Real.log ((k : ℝ) - 1) * Real.log k) ≤
      (Real.log k - Real.log ((k : ℝ) - 1)) / Real.log k := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hu : 0 < Real.log ((k : ℝ) - 1) := Real.log_pos (by linarith)
  have huv : Real.log ((k : ℝ) - 1) ≤ Real.log k := Real.log_le_log (by linarith) (by linarith)
  have hv : 0 < Real.log k := hu.trans_le huv
  have h := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div hv.ne' hu.ne'] at h
  have e : Real.log k / Real.log ((k : ℝ) - 1) - 1 =
      (Real.log k - Real.log ((k : ℝ) - 1)) / Real.log k +
        (Real.log k - Real.log ((k : ℝ) - 1)) ^ 2 / (Real.log ((k : ℝ) - 1) * Real.log k) := by
    field_simp; ring
  linarith

/-- **The sharp logarithmic integral at `σ = 1/log K`**:
`Σ_{2 ≤ k ≤ X} Δlog k · k^{−σ}/log k ≥ log log K − C₁` for `3 ≤ K ≤ X`. -/
theorem sum_logIncrement_rpow_div_log_ge {K X : ℕ} (hK : 3 ≤ K) (hKX : K ≤ X) :
    Real.log (Real.log K) - (Real.log (Real.log 2) + 1 / Real.log 2 ^ 2 + 1) ≤
      ∑ k ∈ Icc 2 X, (Real.log k - Real.log ((k : ℝ) - 1)) *
        ((k : ℝ) ^ (-(1 / Real.log K)) / Real.log k) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlK : 1 ≤ Real.log K := one_le_log_of_three_le hK
  set σ := 1 / Real.log K
  have hσ0 : 0 < σ := by positivity
  set g : ℕ → ℝ := fun k => (Real.log k - Real.log ((k : ℝ) - 1)) * ((k : ℝ) ^ (-σ) / Real.log k)
  have hnn : ∀ k ∈ Icc 2 X, k ∉ Icc 3 K → 0 ≤ g k := fun k hk _ => by
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
    exact mul_nonneg (sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith)))
      (div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg (by linarith)))
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by norm_num) hKX) hnn)
  -- below `K`: `k^{−σ} ≥ 1 − σ log k`
  have hterm : ∀ k ∈ Icc 3 K, (Real.log (Real.log k) - Real.log (Real.log ((k : ℝ) - 1)) -
      (Real.log k - Real.log ((k : ℝ) - 1)) ^ 2 / (Real.log ((k : ℝ) - 1) * Real.log k)) -
        σ * (Real.log k - Real.log ((k : ℝ) - 1)) ≤ g k := by
    intro k hk
    have hk3 := (mem_Icc.mp hk).1
    have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    have hl : 0 < Real.log k := Real.log_pos (by linarith)
    have hd : 0 ≤ Real.log k - Real.log ((k : ℝ) - 1) :=
      sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
    have hpow : 1 - σ * Real.log k ≤ (k : ℝ) ^ (-σ) := by
      rw [Real.rpow_def_of_pos (by linarith)]
      have := Real.add_one_le_exp (Real.log k * -σ)
      linarith
    have h1 := logIncrement_div_log_ge hk3
    have e : (Real.log k - Real.log ((k : ℝ) - 1)) * ((1 - σ * Real.log k) / Real.log k) =
        (Real.log k - Real.log ((k : ℝ) - 1)) / Real.log k -
          σ * (Real.log k - Real.log ((k : ℝ) - 1)) := by
      field_simp
    have h2 : (Real.log k - Real.log ((k : ℝ) - 1)) * ((1 - σ * Real.log k) / Real.log k) ≤ g k :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow hl.le) hd
    linarith
  refine le_trans ?_ (sum_le_sum hterm)
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum]
  -- the three sums
  have hll : ∑ k ∈ Icc 3 K, (Real.log (Real.log k) - Real.log (Real.log ((k : ℝ) - 1))) =
      Real.log (Real.log K) - Real.log (Real.log 2) := by
    have h := sum_Icc_sub_pred (fun k => Real.log (Real.log k)) (a := 3) (M := K) (by norm_num)
      (by omega)
    rw [← show Real.log (Real.log ((2 : ℕ) : ℝ)) = Real.log (Real.log 2) by norm_num, ← h]
    refine sum_congr rfl fun k hk => ?_
    rw [natCast_pred (by have := (mem_Icc.mp hk).1; omega)]
  have hlog : ∑ k ∈ Icc 3 K, (Real.log k - Real.log ((k : ℝ) - 1)) ≤ Real.log K := by
    have h := sum_Icc_sub_pred (fun k => Real.log k) (a := 3) (M := K) (by norm_num) (by omega)
    have e : ∑ k ∈ Icc 3 K, (Real.log k - Real.log ((k : ℝ) - 1)) =
        ∑ k ∈ Icc 3 K, (Real.log k - Real.log ((k - 1 : ℕ) : ℝ)) :=
      sum_congr rfl fun k hk => by rw [natCast_pred (by have := (mem_Icc.mp hk).1; omega)]
    rw [e, h]
    have : 0 ≤ Real.log ((3 - 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    linarith
  have hsq : ∑ k ∈ Icc 3 K, (Real.log k - Real.log ((k : ℝ) - 1)) ^ 2 /
      (Real.log ((k : ℝ) - 1) * Real.log k) ≤ 1 / Real.log 2 ^ 2 := by
    set F : ℕ → ℝ := fun k => -(1 / Real.log 2 ^ 2) * (1 / ((k : ℝ) - 1))
    have hterm2 : ∀ k ∈ Icc 3 K, (Real.log k - Real.log ((k : ℝ) - 1)) ^ 2 /
        (Real.log ((k : ℝ) - 1) * Real.log k) ≤ F k - F (k - 1) := by
      intro k hk
      have hk3 := (mem_Icc.mp hk).1
      have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      have hu : Real.log 2 ≤ Real.log ((k : ℝ) - 1) := Real.log_le_log (by norm_num) (by linarith)
      have hv : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) (by linarith)
      have hd0 : 0 ≤ Real.log k - Real.log ((k : ℝ) - 1) :=
        sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
      have hd : Real.log k - Real.log ((k : ℝ) - 1) ≤ 1 / ((k : ℝ) - 1) := by
        have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith
        rw [← Real.log_div (by linarith) (by linarith)]
        refine (Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))).trans
          (le_of_eq ?_)
        field_simp; ring
      have hd2 : (Real.log k - Real.log ((k : ℝ) - 1)) ^ 2 ≤ (1 / ((k : ℝ) - 1)) ^ 2 :=
        pow_le_pow_left₀ hd0 hd 2
      have hden : Real.log 2 ^ 2 ≤ Real.log ((k : ℝ) - 1) * Real.log k := by
        rw [sq]; exact mul_le_mul hu hv hl2.le (hl2.le.trans hu)
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := natCast_pred (by omega)
      simp only [F]
      rw [hcast]
      have hsqb : (1 / ((k : ℝ) - 1)) ^ 2 ≤ 1 / ((k : ℝ) - 1 - 1) - 1 / ((k : ℝ) - 1) := by
        rw [div_sub_div _ _ (by linarith) (by linarith), div_pow, one_pow,
          div_le_div_iff₀ (pow_pos (by linarith) 2) (by nlinarith)]
        nlinarith
      calc (Real.log k - Real.log ((k : ℝ) - 1)) ^ 2 / (Real.log ((k : ℝ) - 1) * Real.log k) ≤
            (1 / ((k : ℝ) - 1)) ^ 2 / Real.log 2 ^ 2 :=
            div_le_div₀ (by positivity) hd2 (pow_pos hl2 2) hden
        _ ≤ (1 / ((k : ℝ) - 1 - 1) - 1 / ((k : ℝ) - 1)) / Real.log 2 ^ 2 :=
            div_le_div_of_nonneg_right hsqb (by positivity)
        _ = _ := by ring
    calc _ ≤ ∑ k ∈ Icc 3 K, (F k - F (k - 1)) := sum_le_sum hterm2
      _ = F K - F 2 := sum_Icc_sub_pred F (by norm_num) (by omega)
      _ ≤ 1 / Real.log 2 ^ 2 := by
          simp only [F]
          have hK1 : (0 : ℝ) < (K : ℝ) - 1 := by
            have : (3 : ℝ) ≤ K := by exact_mod_cast hK
            linarith
          have h2 : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
          rw [h2, div_one, mul_one]
          have : 0 ≤ 1 / Real.log 2 ^ 2 * (1 / ((K : ℝ) - 1)) :=
            mul_nonneg (by positivity) (one_div_nonneg.mpr hK1.le)
          linarith
  have hσlog : σ * ∑ k ∈ Icc 3 K, (Real.log k - Real.log ((k : ℝ) - 1)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hlog hσ0.le
    simp only [σ] at this ⊢
    rwa [one_div_mul_cancel (by linarith)] at this
  rw [hll]
  linarith

/-- **Abel summation of a growing bound against `n^{−σ}`.** If `L(n) ≤ G (1 + log n)^α` for all `n`,
`G ≥ 0`, `0 ≤ α ≤ 1`, `0 < σ ≤ 1`, then `Σ_{n ≤ N} ε(n) n^{−1−σ} ≤ 2 G σ^{−α}`. -/
theorem sum_twisted_rpow_le_rpow {ε : ℕ → ℝ} {σ G α : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hG : 0 ≤ G)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hL : ∀ n, gaugeHarmonicSum ε n ≤ G * (1 + Real.log n) ^ α)
    (N : ℕ) : ∑ n ∈ Icc 1 N, ε n * (n : ℝ) ^ (-(1 + σ)) ≤ 2 * G * σ ^ (-α) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Icc_eq_empty (by norm_num : ¬ (1 ≤ 0)), sum_empty]; positivity
  set Gσ := G * σ ^ (-α)
  have hGσ : 0 ≤ Gσ := mul_nonneg hG (Real.rpow_nonneg hσ.le _)
  -- `G (1 + log n)^α ≤ Gσ (1 + σ log n)`
  have hbound : ∀ n : ℕ, G * (1 + Real.log n) ^ α ≤ Gσ * (1 + σ * Real.log n) := fun n => by
    have hl := Real.log_natCast_nonneg n
    have h1 : (1 + Real.log n) ^ α = σ ^ (-α) * (σ * (1 + Real.log n)) ^ α := by
      rw [Real.mul_rpow hσ.le (by linarith), ← mul_assoc, ← Real.rpow_add hσ, neg_add_cancel,
        Real.rpow_zero, one_mul]
    have h2 : (σ * (1 + Real.log n)) ^ α ≤ (1 + σ * Real.log n) ^ α :=
      Real.rpow_le_rpow (by positivity) (by nlinarith) hα0
    have h3 : (1 + σ * Real.log n) ^ α ≤ 1 + σ * Real.log n := by
      have : 1 ≤ 1 + σ * Real.log n := by nlinarith
      calc (1 + σ * Real.log n) ^ α ≤ (1 + σ * Real.log n) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le this hα1
        _ = 1 + σ * Real.log n := Real.rpow_one _
    rw [h1]
    calc G * (σ ^ (-α) * (σ * (1 + Real.log n)) ^ α) = Gσ * (σ * (1 + Real.log n)) ^ α := by
          simp only [Gσ]; ring
      _ ≤ Gσ * (1 + σ * Real.log n) := mul_le_mul_of_nonneg_left (h2.trans h3) hGσ
  -- the invariant `T(N) + (Gσ(1 + σ log N) − L(N)) N^{−σ} ≤ Gσ (2 − N^{−σ})`
  have hinv : ∀ N, 1 ≤ N → ∑ n ∈ Icc 1 N, ε n * (n : ℝ) ^ (-(1 + σ)) +
      (Gσ * (1 + σ * Real.log N) - gaugeHarmonicSum ε N) * (N : ℝ) ^ (-σ) ≤
        Gσ * (2 - (N : ℝ) ^ (-σ)) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      simp only [Icc_self, sum_singleton, Nat.cast_one, Real.one_rpow, mul_one, Real.log_one,
        mul_zero, add_zero]
      unfold gaugeHarmonicSum
      simp only [Icc_self, sum_singleton, Nat.cast_one, div_one]
      linarith
    | succ N hN ih =>
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
      have eT : ∑ n ∈ Icc 1 (N + 1), ε n * (n : ℝ) ^ (-(1 + σ)) =
          ∑ n ∈ Icc 1 N, ε n * (n : ℝ) ^ (-(1 + σ)) +
            ε (N + 1) * ((N : ℝ) + 1) ^ (-(1 + σ)) := by
        rw [sum_Icc_succ_top (by omega)]; push_cast; ring
      have eL : gaugeHarmonicSum ε (N + 1) = gaugeHarmonicSum ε N + ε (N + 1) / ((N : ℝ) + 1) := by
        unfold gaugeHarmonicSum; rw [sum_Icc_succ_top (by omega)]; push_cast; ring
      have epow : ((N : ℝ) + 1) ^ (-(1 + σ)) = ((N : ℝ) + 1) ^ (-σ) / ((N : ℝ) + 1) := by
        rw [show -(1 + σ) = -σ + -1 by ring, Real.rpow_add hN1, Real.rpow_neg_one]
        ring
      have hmono : ((N : ℝ) + 1) ^ (-σ) ≤ (N : ℝ) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by linarith)
      have hGL : 0 ≤ Gσ * (1 + σ * Real.log N) - gaugeHarmonicSum ε N :=
        sub_nonneg.mpr ((hL N).trans (hbound N))
      have hstepσ := logIncrement_mul_rpow_le (k := N + 1) (by omega) (σ := σ)
      push_cast at hstepσ
      rw [show (N : ℝ) + 1 - 1 = N by ring] at hstepσ
      rw [eT, eL, epow]
      push_cast
      have e : ∑ n ∈ Icc 1 N, ε n * (n : ℝ) ^ (-(1 + σ)) +
          ε (N + 1) * (((N : ℝ) + 1) ^ (-σ) / ((N : ℝ) + 1)) +
          (Gσ * (1 + σ * Real.log ((N : ℝ) + 1)) -
            (gaugeHarmonicSum ε N + ε (N + 1) / ((N : ℝ) + 1))) * ((N : ℝ) + 1) ^ (-σ) =
          ∑ n ∈ Icc 1 N, ε n * (n : ℝ) ^ (-(1 + σ)) +
            (Gσ * (1 + σ * Real.log N) - gaugeHarmonicSum ε N) * ((N : ℝ) + 1) ^ (-σ) +
            Gσ * (σ * ((Real.log ((N : ℝ) + 1) - Real.log N) * ((N : ℝ) + 1) ^ (-σ))) := by ring
      rw [e]
      have h1 := mul_le_mul_of_nonneg_left hmono hGL
      have h2 := mul_le_mul_of_nonneg_left hstepσ hGσ
      nlinarith
  have h := hinv N hN
  have hp : 0 ≤ (Gσ * (1 + σ * Real.log N) - gaugeHarmonicSum ε N) * (N : ℝ) ^ (-σ) :=
    mul_nonneg (sub_nonneg.mpr ((hL N).trans (hbound N))) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hp2 : 0 ≤ Gσ * (N : ℝ) ^ (-σ) := mul_nonneg hGσ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  simp only [Gσ] at h hp hp2 ⊢
  nlinarith

/-- If `L(n) ≤ G (1 + log n)^α`, the twisted Dirichlet series at `1 + σ` is at most `2Gσ^{−α}`. -/
theorem tsum_twistedDirichletHom_le_rpow {ε : ℕ → ℝ} (hε : IsSignGauge ε) {σ G α : ℝ} (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hG : 0 ≤ G) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hL : ∀ n, gaugeHarmonicSum ε n ≤ G * (1 + Real.log n) ^ α) :
    ∑' n, twistedDirichletHom hε σ n ≤ 2 * G * σ ^ (-α) := by
  have hs := (summable_norm_twistedDirichletHom hε hσ).of_norm
  refine le_of_tendsto' hs.hasSum.tendsto_sum_nat fun N => ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [range_zero, sum_empty]; positivity
  have e : ∑ n ∈ range N, twistedDirichletHom hε σ n =
      ∑ n ∈ Icc 1 (N - 1), ε n * (n : ℝ) ^ (-(1 + σ)) := by
    rw [← Nat.sub_add_cancel hN, sum_range_succ', Nat.add_sub_cancel, sumIcc_eq_sumRange]
    simp only [map_zero, add_zero]
    exact sum_congr rfl fun i _ => by
      rw [twistedDirichletHom_apply hε σ (Nat.succ_ne_zero i)]
  rw [e]
  exact sum_twisted_rpow_le_rpow hσ hσ1 hG hα0 hα1 hL (N - 1)

/-- **The sharp prime sum.** If `primeMean ε n ≥ β log n − C (1 + log n)^α` with `0 ≤ α < 1`, there is
`C₂` with `Σ_{p < X} ε(p) p^{−1−σ} ≥ β log log K − C₂` at `σ = 1/log K`, for all `3 ≤ K < X`. -/
theorem exists_primeSum_rpow_ge_rpow {ε : ℕ → ℝ} {β C α : ℝ} (hβ : 0 ≤ β) (hα0 : 0 ≤ α)
    (hα1 : α < 1)
    (hA : ∀ n : ℕ, 1 ≤ n → β * Real.log n - C * (1 + Real.log n) ^ α ≤ primeMean ε n) :
    ∃ C₂ : ℝ, ∀ K : ℕ, 3 ≤ K → ∀ X : ℕ, K + 1 ≤ X →
      β * Real.log (Real.log K) - C₂ ≤
        ∑ p ∈ Nat.primesBelow X, ε p * (p : ℝ) ^ (-(1 + 1 / Real.log K)) := by
  obtain ⟨E₀, hE₀⟩ := exists_powerAbel_le hα0 hα1
  refine ⟨β * (Real.log (Real.log 2) + 1 / Real.log 2 ^ 2 + 1) + |C| * E₀, fun K hK X hX => ?_⟩
  set σ := 1 / Real.log K
  have hlK : 1 ≤ Real.log K := one_le_log_of_three_le hK
  have hσ : 0 < σ := by positivity
  have hσ1 : σ ≤ 1 := by simp only [σ]; rw [div_le_one (by linarith)]; exact hlK
  set g : ℕ → ℝ := fun k => (k : ℝ) ^ (-σ) / Real.log k
  have hanti : ∀ k, 2 ≤ k → g (k + 1) ≤ g k := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hl : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    have hl' : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log hk0 (by push_cast; linarith)
    have hnum : ((k + 1 : ℕ) : ℝ) ^ (-σ) ≤ (k : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hk0 (by push_cast; linarith) (by linarith)
    exact div_le_div₀ (Real.rpow_nonneg hk0.le _) hnum hl hl'
  have hg0 : ∀ k, 2 ≤ k → 0 ≤ g k := fun k _ =>
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) (Real.log_natCast_nonneg k)
  have hX2 : 2 ≤ X - 1 := by omega
  have hAbel := sum_primeWeight_mul_ge_rpow hA hanti hg0 hX2
  have hE := hE₀ σ hσ hσ1 (X - 1) hX2
  have hE0 : 0 ≤ (1 + Real.log ((X - 1 : ℕ) : ℝ)) ^ α * g (X - 1) +
      ∑ k ∈ Ico 2 (X - 1), (1 + Real.log k) ^ α * (g k - g (k + 1)) := by
    refine add_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith [Real.log_natCast_nonneg (X - 1)]) _)
      (hg0 _ hX2)) (sum_nonneg fun k hk => mul_nonneg
        (Real.rpow_nonneg (by linarith [Real.log_natCast_nonneg k]) _)
        (sub_nonneg.mpr (hanti k (mem_Ico.mp hk).1)))
  have hCE : C * ((1 + Real.log ((X - 1 : ℕ) : ℝ)) ^ α * g (X - 1) +
      ∑ k ∈ Ico 2 (X - 1), (1 + Real.log k) ^ α * (g k - g (k + 1))) ≤ |C| * E₀ :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) hE0).trans
      (mul_le_mul_of_nonneg_left hE (abs_nonneg C))
  have hsum : ∑ k ∈ Icc 2 (X - 1), (if k.Prime then ε k * Real.log k / k else 0) * g k =
      ∑ p ∈ Nat.primesBelow X, ε p * (p : ℝ) ^ (-(1 + σ)) := by
    have hset : Nat.primesBelow X = (Icc 2 (X - 1)).filter Nat.Prime := by
      ext p
      simp only [Nat.mem_primesBelow, mem_filter, mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2.two_le, by omega⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3⟩
    rw [hset, sum_filter]
    refine sum_congr rfl fun k hk => ?_
    split_ifs with hp
    · have hk0 : (0 : ℝ) < k := by exact_mod_cast hp.pos
      have hl : 0 < Real.log k := Real.log_pos (by exact_mod_cast hp.one_lt)
      simp only [g]
      rw [show -(1 + σ) = -1 + -σ by ring, Real.rpow_add hk0, Real.rpow_neg_one]
      field_simp
    · simp
  rw [← hsum]
  have hlow := sum_logIncrement_rpow_div_log_ge hK (show K ≤ X - 1 by omega)
  have hβlow := mul_le_mul_of_nonneg_left hlow hβ
  have e : ∑ k ∈ Icc 2 (X - 1), (Real.log k - Real.log ((k : ℝ) - 1)) *
      ((k : ℝ) ^ (-(1 / Real.log K)) / Real.log k) =
      ∑ k ∈ Icc 2 (X - 1), (Real.log k - Real.log ((k : ℝ) - 1)) * g k := rfl
  rw [e] at hβlow
  nlinarith

/-- **Power growth is impossible below the prime mean.** A sign gauge with prime mean
`β log n + O((1 + log n)^α)`, `0 ≤ α < β`, `α < 1`, has no bound `L(n) ≤ G (1 + log n)^α`. -/
theorem not_le_rpow_gaugeHarmonicSum {ε : ℕ → ℝ} (hε : IsSignGauge ε) {β C α : ℝ}
    (hα0 : 0 ≤ α) (hαβ : α < β) (hα1 : α < 1)
    (hA : ∀ n, 1 ≤ n → |primeMean ε n - β * Real.log n| ≤ C * (1 + Real.log n) ^ α) (G : ℝ) :
    ∃ N : ℕ, G * (1 + Real.log N) ^ α < gaugeHarmonicSum ε N := by
  by_contra hcon
  push Not at hcon
  set G' := max G 1
  have hG' : 0 ≤ G' := (zero_le_one).trans (le_max_right _ _)
  have hL : ∀ n, gaugeHarmonicSum ε n ≤ G' * (1 + Real.log n) ^ α := fun n =>
    (hcon n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by linarith [Real.log_natCast_nonneg n]) _))
  have hA' : ∀ n : ℕ, 1 ≤ n → β * Real.log n - C * (1 + Real.log n) ^ α ≤ primeMean ε n :=
    fun n hn => by have := (abs_le.mp (hA n hn)).1; linarith
  obtain ⟨C₂, hC₂⟩ := exists_primeSum_rpow_ge_rpow (by linarith) hα0 hα1 hA'
  -- `(log K)^{β − α} → ∞`
  have hgrow : Tendsto (fun K : ℕ => Real.log K ^ (β - α)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨K, hK3, hKbig⟩ := ((eventually_ge_atTop 3).and
    (hgrow.eventually_gt_atTop (2 * G' * Real.exp C₂))).exists
  have hlK : 1 ≤ Real.log K := one_le_log_of_three_le hK3
  have hσ : 0 < 1 / Real.log K := by positivity
  have hσ1 : 1 / Real.log K ≤ 1 := by rw [div_le_one (by linarith)]; exact hlK
  have hup := tsum_twistedDirichletHom_le_rpow hε hσ hσ1 hG' hα0 hα1.le hL
  have hdown := exp_le_tsum_twistedDirichletHom hε hσ (X₀ := K + 1) (fun X hX => hC₂ K hK3 X hX)
  -- `exp(β log log K − C₂) = e^{−C₂} (log K)^β` and `σ^{−α} = (log K)^α`
  have hlK0 : 0 < Real.log K := by linarith
  have e1 : Real.exp (β * Real.log (Real.log K) - C₂) = Real.log K ^ β * Real.exp (-C₂) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.rpow_def_of_pos hlK0, mul_comm β]
  have e2 : (1 / Real.log K) ^ (-α) = Real.log K ^ α := by
    rw [one_div, Real.inv_rpow hlK0.le, Real.rpow_neg hlK0.le, inv_inv]
  rw [e1] at hdown
  rw [e2] at hup
  have hsplit : Real.log K ^ β = Real.log K ^ α * Real.log K ^ (β - α) := by
    rw [← Real.rpow_add hlK0]; congr 1; ring
  have hpα : 0 < Real.log K ^ α := Real.rpow_pos_of_pos hlK0 α
  have hexp : 0 < Real.exp (-C₂) := Real.exp_pos _
  have hkey : Real.log K ^ (β - α) * Real.exp (-C₂) ≤ 2 * G' := by
    have h := hdown.trans hup
    rw [hsplit] at h
    have : Real.log K ^ α * (Real.log K ^ (β - α) * Real.exp (-C₂)) ≤ Real.log K ^ α * (2 * G') := by
      linarith
    exact le_of_mul_le_mul_left this hpα
  have hC2 : Real.exp C₂ * Real.exp (-C₂) = 1 := by rw [← Real.exp_add]; simp
  have : 2 * G' * Real.exp C₂ * Real.exp (-C₂) < Real.log K ^ (β - α) * Real.exp (-C₂) :=
    mul_lt_mul_of_pos_right hKbig hexp
  rw [mul_assoc, hC2, mul_one] at this
  linarith

end PowerError

section FlipTwin

/-- **The Wirsing constant of a flip twin is positive.** If
`Σ_{p ∈ P, p ≤ n} log p/p = κ log n + O((1 + log n)^α)` with `0 ≤ κ`, `0 ≤ α < 1 − 2κ`, then
`Σ_{n ≤ N} ω_P(n)/n = c (log N)^{1 − 2κ} + O((log N)^α)` with `c > 0`. -/
theorem exists_pos_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le (P : Set ℕ) {κ C α : ℝ}
    (hκ0 : 0 ≤ κ) (hα : 0 ≤ α) (hακ : α < 1 - 2 * κ)
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C * (1 + Real.log n) ^ α) :
    ∃ c G : ℝ, 0 < c ∧ ∀ N, 3 ≤ N →
      |gaugeHarmonicSum (primeSetFlip P) N - c * Real.log N ^ (1 - 2 * κ)| ≤ G * Real.log N ^ α := by
  obtain ⟨c, G, hcG⟩ := exists_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le_rpow P hκ0 hα hακ hP
  -- `c > 0`: otherwise `L ≤ max(2G, 2)(1 + log N)^α`
  have hc : 0 < c := by
    by_contra hc
    push Not at hc
    obtain ⟨N, hN⟩ := not_le_rpow_gaugeHarmonicSum (primeSetFlip_isSignGauge P) hα hακ
      (by linarith) (fun n hn => abs_primeMean_primeSetFlip_sub_le_rpow P hα hP hn) (max (2 * G) 2)
    have hP1 : 1 ≤ (1 + Real.log N) ^ α :=
      Real.one_le_rpow (by linarith [Real.log_natCast_nonneg N]) hα
    rcases lt_or_ge N 3 with h3 | h3
    · have hb := abs_gaugeHarmonicSum_le (primeSetFlip P) (abs_primeSetFlip_le P) N
      have hlN : Real.log N ≤ 1 := by
        rcases Nat.eq_zero_or_pos N with rfl | hN0
        · simp
        · rw [Real.log_le_iff_le_exp (by exact_mod_cast hN0)]
          have : (N : ℝ) ≤ 2 := by exact_mod_cast (show N ≤ 2 by omega)
          linarith [Real.add_one_le_exp (1 : ℝ)]
      have := (abs_le.mp hb).2
      have h2 : 2 ≤ max (2 * G) 2 * (1 + Real.log N) ^ α :=
        (le_max_right _ _).trans (le_mul_of_one_le_right ((zero_le_two).trans (le_max_right _ _)) hP1)
      linarith
    · have h := (abs_le.mp (hcG N h3)).2
      have hpow : 0 ≤ Real.log N ^ (1 - 2 * κ) :=
        Real.rpow_nonneg (Real.log_natCast_nonneg N) _
      have hlN : Real.log N ^ α ≤ (1 + Real.log N) ^ α :=
        Real.rpow_le_rpow (Real.log_natCast_nonneg N) (by linarith) hα
      have hG0 : 0 ≤ G := by
        have := (abs_nonneg _).trans (hcG N h3)
        have hp : 0 < Real.log N ^ α :=
          Real.rpow_pos_of_pos (by linarith [one_le_log_of_three_le h3]) α
        exact nonneg_of_mul_nonneg_left this hp
      have h2 : G * Real.log N ^ α ≤ max (2 * G) 2 * (1 + Real.log N) ^ α :=
        mul_le_mul (by linarith [le_max_left (2 * G) 2]) hlN (Real.rpow_nonneg (by
          linarith [one_le_log_of_three_le h3]) _) ((zero_le_two).trans (le_max_right _ _))
      nlinarith
  exact ⟨c, G, hc, hcG⟩

/-- The flip-twin harmonic sum is at least `c (log N)^{1 − 2κ}` eventually, `c > 0`. -/
theorem exists_pos_mul_rpow_le_gaugeHarmonicSum_primeSetFlip (P : Set ℕ) {κ C α : ℝ}
    (hκ0 : 0 ≤ κ) (hα : 0 ≤ α) (hακ : α < 1 - 2 * κ)
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C * (1 + Real.log n) ^ α) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      c * Real.log N ^ (1 - 2 * κ) ≤ gaugeHarmonicSum (primeSetFlip P) N := by
  obtain ⟨c, G, hc, hcG⟩ := exists_pos_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le P hκ0 hα hακ hP
  refine ⟨c / 2, by positivity, ?_⟩
  have hgrow : Tendsto (fun N : ℕ => Real.log N ^ (1 - 2 * κ - α)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((eventually_ge_atTop 3).and
    (hgrow.eventually_ge_atTop (2 * |G| / c)))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h3, hbig⟩ := hN₀ N hN
  have hℓ0 : 0 < Real.log N := by linarith [one_le_log_of_three_le h3]
  have h := (abs_le.mp (hcG N h3)).1
  rw [div_le_iff₀ hc] at hbig
  have hsplit : Real.log N ^ (1 - 2 * κ) = Real.log N ^ α * Real.log N ^ (1 - 2 * κ - α) := by
    rw [← Real.rpow_add hℓ0]; congr 1; ring
  have hpα : 0 < Real.log N ^ α := Real.rpow_pos_of_pos hℓ0 α
  have hGα : G * Real.log N ^ α ≤ |G| * Real.log N ^ α :=
    mul_le_mul_of_nonneg_right (le_abs_self G) hpα.le
  have hkey : 2 * |G| * Real.log N ^ α ≤ c * Real.log N ^ (1 - 2 * κ) := by
    rw [hsplit]
    have := mul_le_mul_of_nonneg_left hbig hpα.le
    nlinarith
  nlinarith

end FlipTwin

end GaloisForLFunctions.RenormalizedIntersectionTheory
