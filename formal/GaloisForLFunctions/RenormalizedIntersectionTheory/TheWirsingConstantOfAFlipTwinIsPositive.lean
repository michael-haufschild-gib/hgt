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

For a flip twin of relative log density `κ < 1/2` the Wirsing asymptotic `L(N) = c (log N)^{1−2κ} + O(1)`
therefore has `c > 0` (`exists_pos_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le`,
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

section FlipTwin

/-- **The Wirsing constant of a flip twin is positive.** If the flipped primes have relative
logarithmic density `κ < 1/2`, then `Σ_{n ≤ N} ω_P(n)/n = c (log N)^{1 − 2κ} + O(1)` with `c > 0`. -/
theorem exists_pos_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le (P : Set ℕ) {κ C : ℝ}
    (hκ : κ < 1 / 2) (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C) :
    ∃ c G : ℝ, 0 < c ∧ ∀ N, 3 ≤ N →
      |gaugeHarmonicSum (primeSetFlip P) N - c * Real.log N ^ (1 - 2 * κ)| ≤ G := by
  have hκ0 := nonneg_of_primeSetLogMass P hP
  have hβ : 0 < 1 - 2 * κ := by linarith
  obtain ⟨c, G, hcG⟩ := exists_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le P hκ hP
  -- `c > 0`: otherwise `L ≤ max(G, 1 + log 2)`
  have hc : 0 < c := by
    by_contra hc
    push Not at hc
    obtain ⟨N, hN⟩ := not_bddAbove_gaugeHarmonicSum (primeSetFlip_isSignGauge P) hβ
      (fun n hn => abs_primeMean_primeSetFlip_sub_le P hP hn) (max G 2)
    rcases lt_or_ge N 3 with h3 | h3
    · have hb := abs_gaugeHarmonicSum_le (primeSetFlip P) (abs_primeSetFlip_le P) N
      have hlN : Real.log N ≤ 1 := by
        rcases Nat.eq_zero_or_pos N with rfl | hN0
        · simp
        · rw [Real.log_le_iff_le_exp (by exact_mod_cast hN0)]
          have : (N : ℝ) ≤ 2 := by exact_mod_cast (show N ≤ 2 by omega)
          linarith [Real.add_one_le_exp (1 : ℝ)]
      have := (abs_le.mp hb).2
      have := le_max_right G 2
      linarith
    · have h := (abs_le.mp (hcG N h3)).2
      have hpow : 0 ≤ Real.log N ^ (1 - 2 * κ) :=
        Real.rpow_nonneg (Real.log_natCast_nonneg N) _
      have := le_max_left G 2
      nlinarith
  exact ⟨c, G, hc, hcG⟩

/-- The flip-twin harmonic sum is at least `c (log N)^{1 − 2κ}` eventually, `c > 0`. -/
theorem exists_pos_mul_rpow_le_gaugeHarmonicSum_primeSetFlip (P : Set ℕ) {κ C : ℝ}
    (hκ : κ < 1 / 2) (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      c * Real.log N ^ (1 - 2 * κ) ≤ gaugeHarmonicSum (primeSetFlip P) N := by
  have hκ0 := nonneg_of_primeSetLogMass P hP
  have hβ : 0 < 1 - 2 * κ := by linarith
  obtain ⟨c, G, hc, hcG⟩ := exists_pos_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le P hκ hP
  refine ⟨c / 2, by positivity, ?_⟩
  have hgrow : Tendsto (fun N : ℕ => Real.log N ^ (1 - 2 * κ)) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((eventually_ge_atTop 3).and
    (hgrow.eventually_ge_atTop (2 * G / c)))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h3, hbig⟩ := hN₀ N hN
  have h := (abs_le.mp (hcG N h3)).1
  rw [div_le_iff₀ hc] at hbig
  nlinarith

end FlipTwin

end GaloisForLFunctions.RenormalizedIntersectionTheory
