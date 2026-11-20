import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheHalfRateUnderTheRiemannHypothesis
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheParityNeutralRate
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheExtremalFakePrimeMeasure
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion

/-!
# The unconditional polynomial rate bracket, quadratic coefficient mass, and approximate duals

Combining the full-strip rate achievability theorem with the unconditional `20999 / 24000`
zero-free half-plane upgrades the unconditional producer and parity-neutral producer scales from
Vinogradov–Korobov sub-polynomial decay to explicit polynomial bounds, while the `k^{-2}`
coefficient moment removes exact moment equations from dual rate certificates:

* **Unconditional polynomial rates and bracket (`hasRate_sub_seven_eighths`,
  `hasParityNeutralRate_sub_seven_eighths`, `exists_polynomial_bracket_bestRate`).** Integer
  producers achieve `HasRate (fun K => K^{-a})` for all `0 < a < 3001 / 24000` (in particular
  `K^{-1/8}`), parity-neutral producers achieve `HasParityNeutralRate (fun K => K^{-a})` for all
  `0 < a < 3001 / 120000` (and `0 < a < (1 - Θ) / 5` on any zero-free half-plane `Re s > Θ`), and
  `bestRate K` lies eventually in `[c₁ / (√K (1 + log K)), K^{-a}]`.
* **Alphabet-independent quadratic coefficient mass (`IsProducer.quadraticMass_le`).** Every
  producer satisfies `∑_{k ∈ supp c} |c(k)| / k² ≤ 6 · stencilSlope c`, with no dependence on the
  alphabet bound `K` or the window `B`.
* **Inexact weak duality (`IsApproxFakePrimeMeasure.targetMass_sub_le_objective`,
  `IsApproxFakePrimeMeasure.le_mul_normSlope`).** Any nonnegative measure `u` whose residue moments
  approximate `log k` within `η / k` bounds `normSlope c m B` below by
  `mass(u) / ((1 - 1/B)(1 + 6η))`, specializing at `η = 0` to `IsFakePrimeMeasure.le_normSlope`.
* **Single-letter isolation by prime mass-moves (`primeMassMove_moment_eq`,
  `saw_primeMassMove_eq`, `primeMassMove_window_gain`).** For every odd prime `p ≥ 3`, the atomic
  move `τ_p = δ_{p-1} + δ_1 - δ_p` annihilates `r mod k` for all `k ≥ 2` with `k ≠ p`, evaluates to
  `p` at `k = p`, and gains `+1` (or `+2` at `p = B`) on `[1, B)`.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-! ### Part 1: Unconditional polynomial rates, parity-neutral rates, and `bestRate` bracket -/

/-- **Unconditional polynomial producer rate.** Integer floor producers achieve `K^{-a}` for every
`0 < a < 3001 / 24000` (`> 1 / 8`). -/
theorem hasRate_sub_seven_eighths {a : ℝ} (ha0 : 0 < a) (ha : a < 3001 / 24000) :
    HasRate fun K => (K : ℝ) ^ (-a) := by
  have hΘ := ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths
  exact hasRate_of_lt_one_sub_zetaZeroAbscissa ha0 (by linarith)

/-- Integer floor producers unconditionally achieve the rate `K^{-1/8}`. -/
theorem hasRate_one_eighth : HasRate fun K => (K : ℝ) ^ (-(1 / 8 : ℝ)) :=
  hasRate_sub_seven_eighths (by norm_num) (by norm_num)

/-- **Parity-neutral polynomial rate from any zero-free half-plane.** If `ζ(s) ≠ 0` on `Re s > Θ`
with `Θ ∈ [1/2, 1)`, then parity-neutral producers achieve `K^{-a}` for all `0 < a < (1 - Θ) / 5`. -/
theorem hasParityNeutralRate_of_zeroFree {Θ a : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzf : ∀ s : ℂ, Θ < s.re → riemannZeta s ≠ 0) (ha0 : 0 < a) (ha : a < (1 - Θ) / 5) :
    HasParityNeutralRate fun K => (K : ℝ) ^ (-a) := by
  set σ : ℝ := (5 * a + (1 - Θ)) / 2
  have hσ0 : 0 < σ := by dsimp [σ]; linarith
  have hσ_lt : σ < 1 - Θ := by dsimp [σ]; linarith
  obtain ⟨C, hC, hM⟩ := exists_mertens_power_of_zeroFree hΘ hΘ1 hzf hσ0 hσ_lt
  exact hasParityNeutralRate_of_power hC hσ0 (by linarith) hM (by dsimp [σ]; linarith)

/-- Under `RiemannHypothesis`, parity-neutral producers achieve `K^{-a}` for all `0 < a < 1 / 10`. -/
theorem hasParityNeutralRate_of_riemannHypothesis (hRH : RiemannHypothesis)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 10) :
    HasParityNeutralRate fun K => (K : ℝ) ^ (-a) := by
  have hzf : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → riemannZeta s ≠ 0 := by
    intro s hs
    by_cases hs1 : s.re < 1
    · exact (RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mp hRH) s hs hs1
    · exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hs1)
  exact hasParityNeutralRate_of_zeroFree le_rfl (by norm_num) hzf ha0 (by linarith)

/-- **Unconditional polynomial parity-neutral rate.** Parity-neutral integer producers achieve
`K^{-a}` for every `0 < a < 3001 / 120000` (`> 1 / 40`). -/
theorem hasParityNeutralRate_sub_seven_eighths {a : ℝ} (ha0 : 0 < a) (ha : a < 3001 / 120000) :
    HasParityNeutralRate fun K => (K : ℝ) ^ (-a) := by
  have hΘ := ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths
  refine hasParityNeutralRate_of_zeroFree (Θ := 20999 / 24000) (by norm_num) (by norm_num)
    (fun s hs => RHTower.riemannZeta_ne_zero_of_zetaZeroAbscissa_lt (hΘ.trans_lt hs)) ha0 ?_
  linarith

/-- Parity-neutral integer producers unconditionally achieve `K^{-1/40}`. -/
theorem hasParityNeutralRate_one_fortieth :
    HasParityNeutralRate fun K => (K : ℝ) ^ (-(1 / 40 : ℝ)) :=
  hasParityNeutralRate_sub_seven_eighths (by norm_num) (by norm_num)

/-- **Unconditional two-sided polynomial bracket on `bestRate K`.** There exists `c₁ > 0` such that
for every `0 < a < 3001 / 24000` and all sufficiently large `K`,
`c₁ / (√K (1 + log K)) ≤ bestRate K ≤ K^{-a}`. -/
theorem exists_polynomial_bracket_bestRate :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ a : ℝ, 0 < a → a < 3001 / 24000 →
      ∀ᶠ K : ℕ in atTop,
        c₁ / (√(K : ℝ) * (1 + Real.log (K : ℝ))) ≤ bestRate K ∧ bestRate K ≤ (K : ℝ) ^ (-a) := by
  obtain ⟨c₁, hc₁, hfloor⟩ :=
    exists_half_bracket_bestRate (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 3 / 5)
  refine ⟨c₁, hc₁, fun a ha0 ha => ?_⟩
  filter_upwards [hfloor, hasRate_sub_seven_eighths ha0 ha] with K ⟨hlo, _⟩ ⟨c, m, B, hP, hal, hr⟩
  have hbdd : BddBelow (rateSet K) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨_, _, _, hP', _, rfl⟩
    exact hP'.rate_pos.le
  exact ⟨hlo, (csInf_le hbdd ⟨c, m, B, hP, hal, rfl⟩).trans hr⟩

/-- Unconditional upper bound on the exact asymptotic exponent `zetaZeroAbscissa - 1` of
`log(bestRate K) / log K`. -/
theorem bestRate_asymptotic_exponent_le :
    RHTower.zetaZeroAbscissa - 1 ≤ -3001 / 24000 := by
  linarith [ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths]

/-! ### Part 2: Alphabet-independent quadratic coefficient mass -/

/-- The quadratic coefficient mass `∑_{k ∈ supp c} |c(k)| / k²`. -/
def quadraticMass (c : ℕ →₀ ℤ) : ℝ := ∑ k ∈ c.support, |(c k : ℝ)| / (k : ℝ) ^ 2

theorem quadraticMass_nonneg (c : ℕ →₀ ℤ) : 0 ≤ quadraticMass c :=
  sum_nonneg fun _ _ => div_nonneg (abs_nonneg _) (sq_nonneg _)

private lemma sum_Icc_inv_sq_le_two_sub {M : ℕ} (hM : 1 ≤ M) :
    ∑ j ∈ Icc 1 M, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 - 1 / (M : ℝ) := by
  induction M with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have hih := ih hn
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hstep : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ hnR.ne' hn1.ne', div_le_div_iff₀ (pow_pos hn1 2) (mul_pos hnR hn1)]
        nlinarith
      linarith

private lemma sum_Icc_inv_sq_le_two (M : ℕ) :
    ∑ j ∈ Icc 1 M, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hinv : 0 ≤ 1 / (M : ℝ) := by positivity
    linarith [sum_Icc_inv_sq_le_two_sub hM]

private lemma sum_multiples_inv_sq_le {d : ℕ} (hd : 0 < d) (K : ℕ) :
    ∑ k ∈ Icc 1 K, (if d ∣ k then (1 : ℝ) / (k : ℝ) ^ 2 else 0) ≤ 2 / (d : ℝ) ^ 2 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsplit : ∀ K : ℕ,
      ∑ k ∈ Icc 1 K, (if d ∣ k then (1 : ℝ) / (k : ℝ) ^ 2 else 0) =
        ∑ j ∈ Icc 1 (K / d), (1 : ℝ) / ((d * j : ℕ) : ℝ) ^ 2 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.succ_div]
      split_ifs with hdvd
      · obtain ⟨q, hq⟩ := hdvd
        have hq' : N / d + 1 = q := by
          have h1 : (N + 1) / d = q := by rw [hq]; exact Nat.mul_div_cancel_left q hd
          rw [Nat.succ_div, if_pos ⟨q, hq⟩] at h1
          exact h1
        rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 _), hq', hq]
      · simp
  rw [hsplit K]
  have hterm : ∀ j ∈ Icc 1 (K / d),
      (1 : ℝ) / ((d * j : ℕ) : ℝ) ^ 2 = (1 / (d : ℝ) ^ 2) * ((1 : ℝ) / (j : ℝ) ^ 2) := by
    intro j _
    push_cast
    ring
  rw [sum_congr rfl hterm, ← mul_sum]
  calc (1 / (d : ℝ) ^ 2) * ∑ j ∈ Icc 1 (K / d), (1 : ℝ) / (j : ℝ) ^ 2
      ≤ (1 / (d : ℝ) ^ 2) * 2 := mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le_two _) (by positivity)
    _ = 2 / (d : ℝ) ^ 2 := by ring

private lemma sum_increment_div_sq_le_pronic {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B)
    (K : ℕ) :
    ∑ d ∈ Icc 1 K, |(increment c d : ℝ)| / (d : ℝ) ^ 2 ≤
      3 * ∑ j ∈ range K,
        (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) * (stepWeight c (j + 1) : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ]
    have hsucc : (stepWeight c (K + 1) : ℝ) = stepWeight c K + increment c (K + 1) := by
      exact_mod_cast stepWeight_succ c K
    have hg1 : (0 : ℝ) ≤ stepWeight c (K + 1) := by exact_mod_cast hP.nonneg (K + 1)
    have hg0 : (0 : ℝ) ≤ stepWeight c K := by exact_mod_cast hP.nonneg K
    have habs : |(increment c (K + 1) : ℝ)| ≤ stepWeight c (K + 1) + stepWeight c K := by
      rw [abs_le]
      constructor <;> linarith
    have hcur : (stepWeight c (K + 1) : ℝ) / ((K + 1 : ℕ) : ℝ) ^ 2 ≤
        2 * ((1 / (((K : ℝ) + 1) * ((K : ℝ) + 2))) * (stepWeight c (K + 1) : ℝ)) := by
      push_cast
      have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      have hK2 : (0 : ℝ) < (K : ℝ) + 2 := by positivity
      rw [one_div_mul_eq_div, ← mul_div_assoc,
        div_le_div_iff₀ (pow_pos hK1 2) (mul_pos hK1 hK2)]
      nlinarith
    rcases Nat.eq_zero_or_pos K with rfl | hKpos
    · simp only [range_zero, sum_empty, mul_zero, zero_add, stepWeight_zero, Int.cast_zero,
        add_zero] at ih ⊢
      have hdiv1 : |(increment c 1 : ℝ)| / ((1 : ℕ) : ℝ) ^ 2 ≤
          (stepWeight c 1 : ℝ) / ((1 : ℕ) : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right (by simpa [stepWeight_zero] using habs) (by positivity)
      have hnn : 0 ≤ (1 / (((0 : ℝ) + 1) * ((0 : ℝ) + 2))) * (stepWeight c 1 : ℝ) := by positivity
      linarith
    · obtain ⟨r, rfl⟩ : ∃ r, K = r + 1 := ⟨K - 1, by omega⟩
      rw [Finset.sum_range_succ] at ih ⊢
      have hprev : (stepWeight c (r + 1) : ℝ) / ((r + 1 + 1 : ℕ) : ℝ) ^ 2 ≤
          (1 / (((r : ℝ) + 1) * ((r : ℝ) + 2))) * (stepWeight c (r + 1) : ℝ) := by
        push_cast
        have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
        have hr2 : (0 : ℝ) < (r : ℝ) + 1 + 1 := by positivity
        rw [show (r : ℝ) + 2 = (r : ℝ) + 1 + 1 by ring, one_div_mul_eq_div,
          div_le_div_iff₀ (pow_pos hr2 2) (mul_pos hr1 hr2)]
        nlinarith [hg0]
      have hsplit : |(increment c (r + 1 + 1) : ℝ)| / ((r + 1 + 1 : ℕ) : ℝ) ^ 2 ≤
          (stepWeight c (r + 1 + 1) : ℝ) / ((r + 1 + 1 : ℕ) : ℝ) ^ 2 +
            (stepWeight c (r + 1) : ℝ) / ((r + 1 + 1 : ℕ) : ℝ) ^ 2 := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right habs (by positivity)
      have hnn_last :
          0 ≤ (1 / (((r + 1 : ℕ) : ℝ) + 1) * (((r + 1 : ℕ) : ℝ) + 2)⁻¹) *
            (stepWeight c (r + 1 + 1) : ℝ) := by positivity
      have hnn_last' :
          0 ≤ (1 / ((((r + 1 : ℕ) : ℝ) + 1) * (((r + 1 : ℕ) : ℝ) + 2))) *
            (stepWeight c (r + 1 + 1) : ℝ) := by positivity
      linarith

/-- **Alphabet-independent quadratic coefficient mass law.** For every producer `(c, m, B)`,
`∑_{k ∈ supp c} |c(k)| / k² ≤ 6 · stencilSlope c`, with no dependence on `K` or `B`. -/
theorem IsProducer.quadraticMass_le {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) :
    quadraticMass c ≤ 6 * stencilSlope c := by
  classical
  set K : ℕ := c.support.sup id
  have hK : AlphabetLE c K := fun k hk => Finset.le_sup (f := id) hk
  have hsub := hP.support_subset_Icc hK
  have hstep1 : quadraticMass c ≤
      ∑ k ∈ Icc 1 K, ∑ d ∈ k.divisors, |(increment c d : ℝ)| * (1 / (k : ℝ) ^ 2) := by
    calc quadraticMass c
        ≤ ∑ k ∈ c.support, ∑ d ∈ k.divisors, |(increment c d : ℝ)| * (1 / (k : ℝ) ^ 2) := by
          refine sum_le_sum fun k hk => ?_
          have hk1 := (mem_Icc.mp (hsub hk)).1
          rw [← sum_mul, div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right (abs_coeff_le_sum_increment c hk1) (by positivity)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
          sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (by positivity)
  have hswap : ∑ k ∈ Icc 1 K, ∑ d ∈ k.divisors, |(increment c d : ℝ)| * (1 / (k : ℝ) ^ 2) =
      ∑ d ∈ Icc 1 K, |(increment c d : ℝ)| *
        ∑ k ∈ Icc 1 K, (if d ∣ k then (1 : ℝ) / (k : ℝ) ^ 2 else 0) := by
    have hdiv : ∀ k ∈ Icc 1 K,
        ∑ d ∈ k.divisors, |(increment c d : ℝ)| * (1 / (k : ℝ) ^ 2) =
          ∑ d ∈ Icc 1 K, if d ∣ k then |(increment c d : ℝ)| * (1 / (k : ℝ) ^ 2) else 0 := by
      intro k hk
      obtain ⟨hk1, hkK⟩ := mem_Icc.mp hk
      rw [← sum_filter]
      refine sum_congr ?_ fun _ _ => rfl
      ext d
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      exact ⟨fun ⟨hd, _⟩ => ⟨⟨Nat.pos_of_dvd_of_pos hd hk1, (Nat.le_of_dvd hk1 hd).trans hkK⟩, hd⟩,
        fun ⟨_, hd⟩ => ⟨hd, by omega⟩⟩
    rw [sum_congr rfl hdiv, sum_comm]
    refine sum_congr rfl fun d _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have hmult : ∑ d ∈ Icc 1 K, |(increment c d : ℝ)| *
      ∑ k ∈ Icc 1 K, (if d ∣ k then (1 : ℝ) / (k : ℝ) ^ 2 else 0) ≤
      2 * ∑ d ∈ Icc 1 K, |(increment c d : ℝ)| / (d : ℝ) ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun d hd => ?_
    have hd1 := (mem_Icc.mp hd).1
    calc |(increment c d : ℝ)| * ∑ k ∈ Icc 1 K, (if d ∣ k then (1 : ℝ) / (k : ℝ) ^ 2 else 0)
        ≤ |(increment c d : ℝ)| * (2 / (d : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_multiples_inv_sq_le hd1 K) (abs_nonneg _)
      _ = 2 * (|(increment c d : ℝ)| / (d : ℝ) ^ 2) := by ring
  have hpronic_partial :
      ∑ j ∈ range K, (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) * (stepWeight c (j + 1) : ℝ) ≤
        stencilSlope c :=
    sum_le_hasSum (range K)
      (fun j _ => mul_nonneg (by positivity) (by exact_mod_cast hP.nonneg (j + 1)))
      ((isFakePrimeMeasure_pronic K).hasSum_slope hP hK)
  have hinc_pronic := sum_increment_div_sq_le_pronic hP K
  linarith [hstep1, hswap, hmult, hinc_pronic, hpronic_partial]

/-- Normalized quadratic coefficient mass: `quadraticMass c / m ≤ 6 (1 + rate c m B)`. -/
theorem IsProducer.quadraticMass_div_le {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) :
    quadraticMass c / (m : ℝ) ≤ 6 * (1 + rate c m B) := by
  have hm := hP.m_pos
  have h1 := hP.one_sub_pos
  have h1_le : 1 - 1 / (B : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (B : ℝ) := by positivity
    linarith
  have hsl : stencilSlope c ≤ (m : ℝ) * (1 + rate c m B) := by
    have hns : stencilSlope c = normSlope c m B * ((m : ℝ) * (1 - 1 / (B : ℝ))) := by
      unfold normSlope
      exact (div_mul_cancel₀ _ (mul_pos hm h1).ne').symm
    have hrate_eq : normSlope c m B = 1 + rate c m B := by unfold rate; ring
    have hns_pos : 0 ≤ 1 + rate c m B := by linarith [hP.rate_pos]
    rw [hns, hrate_eq]
    calc (1 + rate c m B) * ((m : ℝ) * (1 - 1 / (B : ℝ)))
        ≤ (1 + rate c m B) * ((m : ℝ) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1_le hm.le) hns_pos
      _ = (m : ℝ) * (1 + rate c m B) := by ring
  rw [div_le_iff₀ hm]
  linarith [hP.quadraticMass_le, hsl]

/-! ### Part 3: Inexact weak duality for approximate fake prime measures -/

/-- A nonnegative measure on `r = j + 1` whose residue moments up to level `K` approximate `log k`
within `η / k`. -/
structure IsApproxFakePrimeMeasure (K : ℕ) (η : ℝ) (u : ℕ → ℝ) : Prop where
  nonneg : ∀ j, 0 ≤ u j
  summable_moment : ∀ k ∈ Icc 2 K, Summable fun j => u j * (((j + 1) % k : ℕ) : ℝ)
  moment_error : ∀ k ∈ Icc 2 K,
    |(∑' j, u j * (((j + 1) % k : ℕ) : ℝ)) - Real.log k| ≤ η / (k : ℝ)

/-- Every exact fake prime measure is an approximate fake prime measure with error `η = 0`. -/
theorem IsFakePrimeMeasure.isApproxFakePrimeMeasure {K : ℕ} {u : ℕ → ℝ}
    (hu : IsFakePrimeMeasure K u) : IsApproxFakePrimeMeasure K 0 u where
  nonneg := hu.nonneg
  summable_moment k hk :=
    (hu.moment k (mem_Icc.mpr ⟨by linarith [(mem_Icc.mp hk).1], (mem_Icc.mp hk).2⟩)).summable
  moment_error k hk := by
    have h := (hu.moment k (mem_Icc.mpr ⟨by linarith [(mem_Icc.mp hk).1], (mem_Icc.mp hk).2⟩)).tsum_eq
    simp [h]

/-- **Inexact weak duality for real LP weights.** Any approximate fake prime measure bounds
`objective q K` from below up to `η ∑_{k=2}^K |q_k| / k`. -/
theorem IsApproxFakePrimeMeasure.targetMass_sub_le_objective {K : ℕ} {η : ℝ} {u : ℕ → ℝ}
    (hu : IsApproxFakePrimeMeasure K η u) {S : Finset ℕ} {q : ℕ → ℝ}
    (hF : IsFeasible K S q) (hS : ∀ r ∈ S, 1 ≤ r) :
    targetMass u S - η * (∑ k ∈ Icc 2 K, |q k| / (k : ℝ)) ≤ objective q K := by
  classical
  have hsum_saw : HasSum (fun j => u j * saw q K (j + 1))
      (∑ k ∈ Icc 2 K, q k * ∑' j, u j * (((j + 1) % k : ℕ) : ℝ)) := by
    have hfun : (fun j => u j * saw q K (j + 1)) =
        fun j => ∑ k ∈ Icc 2 K, q k * (u j * (((j + 1) % k : ℕ) : ℝ)) := by
      funext j
      rw [saw, mul_sum]
      exact sum_congr rfl fun k _ => by ring
    rw [hfun]
    exact hasSum_sum fun k hk => (hu.summable_moment k hk).hasSum.mul_left (q k)
  have hinj : Set.InjOn (fun r : ℕ => r - 1) (S : Set ℕ) := by
    intro a ha b hb hab
    have h1 := hS a ha
    have h2 := hS b hb
    simp only at hab
    omega
  have hmass_le : targetMass u S ≤ ∑ k ∈ Icc 2 K, q k * ∑' j, u j * (((j + 1) % k : ℕ) : ℝ) := by
    rw [targetMass, ← sum_image hinj]
    refine le_trans ?_
      (sum_le_hasSum (S.image fun r => r - 1)
        (fun j _ => mul_nonneg (hu.nonneg j) (hF.saw_nonneg _)) hsum_saw)
    refine sum_le_sum fun j hj => ?_
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hj
    have hr1 := hS r hr
    rw [show r - 1 + 1 = r by omega]
    calc u (r - 1) = u (r - 1) * 1 := (mul_one _).symm
      _ ≤ u (r - 1) * saw q K r := mul_le_mul_of_nonneg_left (hF.target r hr) (hu.nonneg _)
  have hdiff : ∑ k ∈ Icc 2 K, q k * (∑' j, u j * (((j + 1) % k : ℕ) : ℝ)) - objective q K ≤
      η * ∑ k ∈ Icc 2 K, |q k| / (k : ℝ) := by
    rw [objective, ← sum_sub_distrib, mul_sum]
    refine sum_le_sum fun k hk => ?_
    have herr := hu.moment_error k hk
    have hprod : q k * (∑' j, u j * (((j + 1) % k : ℕ) : ℝ)) - q k * Real.log k ≤
        |q k| * |(∑' j, u j * (((j + 1) % k : ℕ) : ℝ)) - Real.log k| := by
      rw [← mul_sub, ← abs_mul]
      exact le_abs_self _
    calc q k * (∑' j, u j * (((j + 1) % k : ℕ) : ℝ)) - q k * Real.log k
        ≤ |q k| * (η / (k : ℝ)) :=
          hprod.trans (mul_le_mul_of_nonneg_left herr (abs_nonneg _))
      _ = η * (|q k| / (k : ℝ)) := by ring
  linarith

/-- **Alphabet-free inexact dual bound for integer producers.** If `u` is an approximate fake prime
measure of level `K` with tolerance `η ≥ 0`, then every producer `(c, m, B)` on `[1, K]` satisfies
`(∑_{j < B - 1} u j) / (1 - 1 / B) ≤ (1 + 6η) · normSlope c m B`. -/
theorem IsApproxFakePrimeMeasure.le_mul_normSlope {K : ℕ} {η : ℝ} {u : ℕ → ℝ}
    (hu : IsApproxFakePrimeMeasure K η u) (hη : 0 ≤ η)
    {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) (hK : AlphabetLE c K) :
    (∑ j ∈ range (B - 1), u j) / (1 - 1 / (B : ℝ)) ≤ (1 + 6 * η) * normSlope c m B := by
  classical
  have hsub := hP.support_subset_Icc hK
  set S2 : Finset ℕ := c.support.filter (fun k => 2 ≤ k)
  have hS2_sub : S2 ⊆ Icc 2 K := fun k hk => by
    obtain ⟨hks, hk2⟩ := mem_filter.mp hk
    exact mem_Icc.mpr ⟨hk2, (mem_Icc.mp (hsub hks)).2⟩
  have hstep_eq : ∀ r : ℕ,
      (stepWeight c r : ℝ) = ∑ k ∈ S2, (-(c k : ℝ) / k) * ((r % k : ℕ) : ℝ) := by
    intro r
    rw [stepWeight_eq_sum_mod hP.zero hP.balanced]
    symm
    refine sum_subset (filter_subset _ _) fun k hk hnot => ?_
    have hk1 := (mem_Icc.mp (hsub hk)).1
    have hk_eq1 : k = 1 := by
      by_contra hne
      exact hnot (mem_filter.mpr ⟨hk, by omega⟩)
    subst hk_eq1
    simp [Nat.mod_one]
  have hslope_eq : stencilSlope c = ∑ k ∈ S2, (-(c k : ℝ) / k) * Real.log k := by
    rw [stencilSlope]
    symm
    refine sum_subset (filter_subset _ _) fun k hk hnot => ?_
    have hk1 := (mem_Icc.mp (hsub hk)).1
    have hk_eq1 : k = 1 := by
      by_contra hne
      exact hnot (mem_filter.mpr ⟨hk, by omega⟩)
    subst hk_eq1
    simp
  have hhasSum : HasSum (fun j => u j * (stepWeight c (j + 1) : ℝ))
      (∑ k ∈ S2, (-(c k : ℝ) / k) * ∑' j, u j * (((j + 1) % k : ℕ) : ℝ)) := by
    have hfun : (fun j => u j * (stepWeight c (j + 1) : ℝ)) =
        fun j => ∑ k ∈ S2, (-(c k : ℝ) / k) * (u j * (((j + 1) % k : ℕ) : ℝ)) := by
      funext j
      rw [hstep_eq (j + 1), mul_sum]
      exact sum_congr rfl fun k _ => by ring
    rw [hfun]
    exact hasSum_sum fun k hk => (hu.summable_moment k (hS2_sub hk)).hasSum.mul_left _
  have hwin : (m : ℝ) * ∑ j ∈ range (B - 1), u j ≤
      ∑ k ∈ S2, (-(c k : ℝ) / k) * ∑' j, u j * (((j + 1) % k : ℕ) : ℝ) := by
    refine le_trans ?_
      (sum_le_hasSum (range (B - 1))
        (fun j _ => mul_nonneg (hu.nonneg j) (by exact_mod_cast hP.nonneg (j + 1))) hhasSum)
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    have hjB := mem_range.mp hj
    have hw : (m : ℝ) ≤ stepWeight c (j + 1) := by
      exact_mod_cast hP.window (j + 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
    calc (m : ℝ) * u j = u j * (m : ℝ) := mul_comm _ _
      _ ≤ u j * (stepWeight c (j + 1) : ℝ) := mul_le_mul_of_nonneg_left hw (hu.nonneg j)
  have herr_sum :
      (∑ k ∈ S2, (-(c k : ℝ) / k) * ∑' j, u j * (((j + 1) % k : ℕ) : ℝ)) - stencilSlope c ≤
        η * quadraticMass c := by
    rw [hslope_eq, ← sum_sub_distrib]
    have hle_S2 :
        ∑ k ∈ S2, ((-(c k : ℝ) / k) * (∑' j, u j * (((j + 1) % k : ℕ) : ℝ)) -
            (-(c k : ℝ) / k) * Real.log k) ≤
          ∑ k ∈ S2, η * (|(c k : ℝ)| / (k : ℝ) ^ 2) := by
      refine sum_le_sum fun k hk => ?_
      have herr := hu.moment_error k (hS2_sub hk)
      have hk_pos : (0 : ℝ) < (k : ℝ) := by
        exact_mod_cast (by linarith [(mem_Icc.mp (hS2_sub hk)).1] : 0 < k)
      have habs_q : |-(c k : ℝ) / (k : ℝ)| = |(c k : ℝ)| / (k : ℝ) := by
        rw [neg_div, abs_neg, abs_div, abs_of_pos hk_pos]
      have hp : (-(c k : ℝ) / k) * (∑' j, u j * (((j + 1) % k : ℕ) : ℝ)) -
          (-(c k : ℝ) / k) * Real.log k ≤
          (|(c k : ℝ)| / (k : ℝ)) * |(∑' j, u j * (((j + 1) % k : ℕ) : ℝ)) - Real.log k| := by
        rw [← mul_sub, ← habs_q, ← abs_mul]
        exact le_abs_self _
      calc (-(c k : ℝ) / k) * (∑' j, u j * (((j + 1) % k : ℕ) : ℝ)) -
              (-(c k : ℝ) / k) * Real.log k
          ≤ (|(c k : ℝ)| / (k : ℝ)) * (η / (k : ℝ)) :=
            hp.trans (mul_le_mul_of_nonneg_left herr (by positivity))
        _ = η * (|(c k : ℝ)| / (k : ℝ) ^ 2) := by ring
    refine hle_S2.trans ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        fun _ _ _ => div_nonneg (abs_nonneg _) (sq_nonneg _)) hη
  have hquad := mul_le_mul_of_nonneg_left hP.quadraticMass_le hη
  have hsl_bound : (m : ℝ) * ∑ j ∈ range (B - 1), u j ≤ (1 + 6 * η) * stencilSlope c := by
    linarith [hwin, herr_sum, hquad]
  have hm := hP.m_pos
  have h1 := hP.one_sub_pos
  rw [normSlope, mul_div_assoc', le_div_iff₀ (mul_pos hm h1), div_mul_eq_mul_div, div_le_iff₀ h1]
  calc (∑ j ∈ range (B - 1), u j) * ((m : ℝ) * (1 - 1 / (B : ℝ)))
      = ((m : ℝ) * ∑ j ∈ range (B - 1), u j) * (1 - 1 / (B : ℝ)) := by ring
    _ ≤ ((1 + 6 * η) * stencilSlope c) * (1 - 1 / (B : ℝ)) :=
        mul_le_mul_of_nonneg_right hsl_bound h1.le

/-! ### Part 4: Exact single-letter isolation of the prime mass-move `τ_p` -/

/-- **Kronecker-delta moment law for prime mass-moves.** For every odd prime `p ≥ 3` and every
modulus `k ≥ 2` (whether below, equal to, or above `p`), the atomic move `τ_p = δ_{p-1} + δ_1 - δ_p`
satisfies `((p - 1) mod k) + (1 mod k) - (p mod k) = p · δ_{k, p}`. -/
theorem primeMassMove_moment_eq {p k : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hk2 : 2 ≤ k) :
    (((p - 1) % k : ℕ) : ℝ) + ((1 % k : ℕ) : ℝ) - ((p % k : ℕ) : ℝ) =
      if k = p then (p : ℝ) else 0 := by
  have hmod1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  by_cases hkp : k = p
  · subst hkp
    rw [if_pos rfl, Nat.mod_eq_of_lt (by omega : k - 1 < k), hmod1, Nat.mod_self]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  · rw [if_neg hkp]
    have hnd : ¬ k ∣ p := fun hd => by
      rcases (Nat.dvd_prime hp).mp hd with rfl | rfl <;> omega
    have hpne : p % k ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    have hdiv := Nat.div_add_mod p k
    have hlt := Nat.mod_lt p (by omega : 0 < k)
    have hrew : p - 1 = (p % k - 1) + k * (p / k) := by omega
    have hmod_pred : (p - 1) % k = p % k - 1 := by
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hmod_pred, hmod1]
    have hpos : 1 ≤ p % k := by omega
    rw [Nat.cast_sub hpos]
    push_cast
    ring

/-- Action of the prime mass-move `τ_p` on any sawtooth sum `saw q K`: it isolates the single
letter `p` with weight `p · q_p`. -/
theorem saw_primeMassMove_eq (q : ℕ → ℝ) (K : ℕ) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    saw q K (p - 1) + saw q K 1 - saw q K p = if p ∈ Icc 2 K then (p : ℝ) * q p else 0 := by
  simp only [saw, ← sum_add_distrib, ← sum_sub_distrib]
  have hterm : ∀ k ∈ Icc 2 K,
      q k * (((p - 1) % k : ℕ) : ℝ) + q k * ((1 % k : ℕ) : ℝ) - q k * ((p % k : ℕ) : ℝ) =
        if k = p then (p : ℝ) * q p else 0 := by
    intro k hk
    have heq : q k * (((p - 1) % k : ℕ) : ℝ) + q k * ((1 % k : ℕ) : ℝ) - q k * ((p % k : ℕ) : ℝ) =
        q k * ((((p - 1) % k : ℕ) : ℝ) + ((1 % k : ℕ) : ℝ) - ((p % k : ℕ) : ℝ)) := by ring
    rw [heq, primeMassMove_moment_eq hp hp3 (mem_Icc.mp hk).1]
    split_ifs with hkp
    · subst hkp; ring
    · ring
  rw [sum_congr rfl hterm]
  by_cases hpK : p ∈ Icc 2 K
  · rw [if_pos hpK, sum_eq_single p]
    · simp
    · intro k _ hne; exact if_neg hne
    · intro habs; exact (habs hpK).elim
  · rw [if_neg hpK]
    refine sum_eq_zero fun k hk => if_neg ?_
    rintro rfl
    exact hpK hk

/-- Net window indicator gain of `τ_p = δ_{p-1} + δ_1 - δ_p` on `[1, B)` (`B ≥ 2`) for any odd
prime `p ≥ 3`: it equals `+2` at `p = B` and `+1` for all `p ≠ B`. -/
theorem primeMassMove_window_gain {B p : ℕ} (hB2 : 2 ≤ B) (hp3 : 3 ≤ p) :
    ((if p - 1 ∈ Ico 1 B then (1 : ℝ) else 0) + (if 1 ∈ Ico 1 B then (1 : ℝ) else 0) -
        (if p ∈ Ico 1 B then (1 : ℝ) else 0)) =
      if p = B then 2 else 1 := by
  have h1 : 1 ∈ Ico 1 B := mem_Ico.mpr ⟨le_rfl, hB2⟩
  rw [if_pos h1]
  by_cases hpB : p = B
  · subst hpB
    have hp_pred : p - 1 ∈ Ico 1 p := mem_Ico.mpr ⟨by omega, by omega⟩
    have hp_not : p ∉ Ico 1 p := fun h => by have := (mem_Ico.mp h).2; omega
    rw [if_pos rfl, if_pos hp_pred, if_neg hp_not]
    norm_num
  · rw [if_neg hpB]
    rcases lt_or_gt_of_ne hpB with hlt | hgt
    · have hp_pred : p - 1 ∈ Ico 1 B := mem_Ico.mpr ⟨by omega, by omega⟩
      have hp_in : p ∈ Ico 1 B := mem_Ico.mpr ⟨by omega, hlt⟩
      rw [if_pos hp_pred, if_pos hp_in]
      norm_num
    · have hp_pred_not : p - 1 ∉ Ico 1 B := fun h => by have := (mem_Ico.mp h).2; omega
      have hp_not : p ∉ Ico 1 B := fun h => by have := (mem_Ico.mp h).2; omega
      rw [if_neg hp_pred_not, if_neg hp_not]
      norm_num

#print axioms hasRate_sub_seven_eighths
#print axioms hasRate_one_eighth
#print axioms hasParityNeutralRate_of_zeroFree
#print axioms hasParityNeutralRate_sub_seven_eighths
#print axioms exists_polynomial_bracket_bestRate
#print axioms bestRate_asymptotic_exponent_le
#print axioms IsProducer.quadraticMass_le
#print axioms IsApproxFakePrimeMeasure.targetMass_sub_le_objective
#print axioms IsApproxFakePrimeMeasure.le_mul_normSlope
#print axioms primeMassMove_moment_eq
#print axioms saw_primeMassMove_eq
#print axioms primeMassMove_window_gain

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
