import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedMoebiusFirstMomentAndChebyshevTangentBridge
import GaloisForLFunctions.TransHorizonIncidenceMechanics.APoleOfOrderTwoNeedsAZeroOfOrderTwo
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FinitePerturbationsOfEveryPositiveWeightPretendingToOneAreDecidedAtThePole

/-!
# Double-zero kernels and finite perturbations of logarithmic weights at the pole

This module connects the Leibniz derivation law of `logWeight` under Dirichlet convolution
(`DampedMoebiusFirstMomentAndChebyshevTangentBridge`) with the Mellin double-pole lower bound
(`APoleOfOrderTwoNeedsAZeroOfOrderTwo`) and the critical Wiener factorization of multiplicative
weights pretending to one (`FinitePerturbationsOfEveryPositiveWeightPretendingToOneAreDecidedAtThePole`):

1. **Vector-space closure of `ReceiverBounded`** (`receiverBounded_add`, `receiverBounded_neg`,
   `receiverBounded_sub`): by Minkowski's inequality for `pronicNorm` and additivity of
   `weightCenteredPrefix`, bounded-receiver weights with summable divisor density form a real vector
   space.
2. **Exact antitone decomposition of `d^{-α} log d` and bounded logarithmic sign patterns**
   (`logDecayAux_antitone`, `receiverBounded_logWeight_dampedSign`): for every `α > 0`, the auxiliary
   profile `g_α(d) = d^{-α} (log d + 1/α)` is nonnegative and antitone on `d ≥ 1`, giving the exact
   antitone decomposition `d^{-α} log d = g_α(d) - (1/α) d^{-α}`. Abel summation and the hyperbola
   split at `D = ⌊n^{1/(2 + ε/2)}⌋` prove that `logWeight (dampedSignWeight s ε)` has bounded
   receiver at every damping `ε > 0` whenever `s` has bounded partial sums (in particular for `χ₄`
   and `fermiPattern`).
3. **The double-zero pole law (`↔`) for logarithmic weights** (`receiverBounded_dirichletConv_logWeight_unit_iff`,
   `receiverBounded_dirichletConv_logWeight_primesOne_iff`): by the Leibniz identity
   `k ⋆ logWeight c = logWeight (k ⋆ c) - (logWeight k) ⋆ c` and `poleValue (logWeight k) J ε = poleSlope k J ε`,
   a finite kernel `k` supported on `[1, J]` repairs `logWeight (dampedSignWeight b ε)` (for `b = 1`
   or any nonnegative bounded multiplicative `b` with `b(p) = 1` at the primes) at `0 < ε ≤ 1/2`
   **if and only if** `poleValue k J ε = 0 ∧ poleSlope k J ε = 0` (with sufficiency holding at every
   `ε > 0`).
4. **First-order vs. second-order Fermi kernels** (`fermiKernel_pays_unit_not_logWeight`,
   `receiverBounded_secondOrderFermi_logWeight_unit`): the first-order Fermi kernel
   `δ₁ - 2^{1-ε} δ₂` repairs `d^{-ε}` but fails to repair `d^{-ε} log d` at every `0 < ε ≤ 1/2`,
   whereas its convolution square `(δ₁ - 2^{1-ε} δ₂)^{⋆ 2}` vanishes to second order at the pole and
   repairs both `d^{-ε}` and `d^{-ε} log d` at every `ε > 0`.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

local notation "μR" => ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)

/-! ### 1. Vector-space closure of `ReceiverBounded` -/

/-- Negating a weight preserves receiver boundedness. -/
theorem receiverBounded_neg (c : ℕ → ℝ) :
    ReceiverBounded (fun d => -c d) ↔ ReceiverBounded c := by
  have h := receiverBounded_smul_iff (t := -1) (by norm_num) c
  simpa only [neg_one_mul] using h

/-- The sum of two bounded-receiver weights with summable divisor densities has bounded receiver. -/
theorem receiverBounded_add {c g : ℕ → ℝ}
    (hsc : Summable (fun d : ℕ => c d / d)) (hsg : Summable (fun d : ℕ => g d / d))
    (hc : ReceiverBounded c) (hg : ReceiverBounded g) :
    ReceiverBounded (fun d => c d + g d) := by
  obtain ⟨Ec, hEc⟩ := hc
  obtain ⟨Eg, hEg⟩ := hg
  set mc := ∑' d : ℕ, c d / d
  set mg := ∑' d : ℕ, g d / d
  have hmean : ∑' d : ℕ, (c d + g d) / d = mc + mg := by
    simp_rw [add_div]
    exact hsc.tsum_add hsg
  refine ⟨(Real.sqrt (max Ec 0) + Real.sqrt (max Eg 0)) ^ 2, fun T => ?_⟩
  rw [hmean, weightPronicEnergy_eq_sq_pronicNorm]
  have hAc : pronicNorm (weightCenteredPrefix c mc) T ≤ Real.sqrt (max Ec 0) :=
    Real.le_sqrt_of_sq_le ((weightPronicEnergy_eq_sq_pronicNorm c mc T ▸ hEc T).trans (le_max_left _ _))
  have hAg : pronicNorm (weightCenteredPrefix g mg) T ≤ Real.sqrt (max Eg 0) :=
    Real.le_sqrt_of_sq_le ((weightPronicEnergy_eq_sq_pronicNorm g mg T ▸ hEg T).trans (le_max_left _ _))
  have hadd : pronicNorm (weightCenteredPrefix (fun d => c d + g d) (mc + mg)) T ≤
      Real.sqrt (max Ec 0) + Real.sqrt (max Eg 0) := by
    rw [show weightCenteredPrefix (fun d => c d + g d) (mc + mg) =
        fun n => weightCenteredPrefix c mc n + weightCenteredPrefix g mg n from
      funext (weightCenteredPrefix_add c g mc mg)]
    exact (pronicNorm_add_le _ _ T).trans (add_le_add hAc hAg)
  exact pow_le_pow_left₀ (pronicNorm_nonneg _ T) hadd 2

/-- The difference of two bounded-receiver weights with summable divisor densities has bounded receiver. -/
theorem receiverBounded_sub {c g : ℕ → ℝ}
    (hsc : Summable (fun d : ℕ => c d / d)) (hsg : Summable (fun d : ℕ => g d / d))
    (hc : ReceiverBounded c) (hg : ReceiverBounded g) :
    ReceiverBounded (fun d => c d - g d) := by
  have hg' : ReceiverBounded (fun d => -g d) := (receiverBounded_neg g).mpr hg
  have hsg' : Summable (fun d : ℕ => -g d / d) := by
    simp_rw [neg_div]
    exact hsg.neg
  simpa only [sub_eq_add_neg] using receiverBounded_add hsc hsg' hc hg'

/-! ### 2. Antitone decomposition of `d^{-α} log d` and logarithmic sign patterns -/

/-- Auxiliary profile `g_α(d) = d^{-α} (log d + 1/α)`, which is nonnegative and antitone on `d ≥ 1`. -/
def logDecayAux (α : ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) ^ (-α) * (Real.log d + 1 / α)

/-- Exact decomposition `d^{-α} log d = g_α(d) - (1/α) d^{-α}`. -/
theorem rpow_neg_mul_log_eq_sub (α : ℝ) (d : ℕ) :
    (d : ℝ) ^ (-α) * Real.log d = logDecayAux α d - (1 / α) * (d : ℝ) ^ (-α) := by
  unfold logDecayAux; ring

theorem logDecayAux_nonneg {α : ℝ} (hα : 0 < α) (d : ℕ) : 0 ≤ logDecayAux α d := by
  unfold logDecayAux
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    (add_nonneg (Real.log_natCast_nonneg d) (by positivity))

/-- For `α > 0`, `logDecayAux α` is antitone on `d ≥ 1`: writing `u = d^α`,
`g_α(d) = (log u + 1)/(α u)` decreases since `log(u₂/u₁) ≤ u₂/u₁ - 1`. -/
theorem logDecayAux_antitone {α : ℝ} (hα : 0 < α) {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁) (hd₁₂ : d₁ ≤ d₂) :
    logDecayAux α d₂ ≤ logDecayAux α d₁ := by
  have hrepr : ∀ {d : ℕ}, 1 ≤ d →
      logDecayAux α d = (Real.log ((d : ℝ) ^ α) + 1) / (α * (d : ℝ) ^ α) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hα0 : α ≠ 0 := hα.ne'
    have hu0 : (d : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos hd0 α).ne'
    unfold logDecayAux
    rw [Real.rpow_neg hd0.le, Real.log_rpow hd0]
    field_simp
  have hd₂ : 1 ≤ d₂ := hd₁.trans hd₁₂
  rw [hrepr hd₂, hrepr hd₁]
  set u₁ := (d₁ : ℝ) ^ α
  set u₂ := (d₂ : ℝ) ^ α
  have hd₁0 : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
  have hd₂0 : (0 : ℝ) < d₂ := by exact_mod_cast hd₂
  have hu₁ : 0 < u₁ := Real.rpow_pos_of_pos hd₁0 α
  have hu₂ : 0 < u₂ := Real.rpow_pos_of_pos hd₂0 α
  have hu₁1 : 1 ≤ u₁ := Real.one_le_rpow (by exact_mod_cast hd₁) hα.le
  have hu₁₂ : u₁ ≤ u₂ := Real.rpow_le_rpow hd₁0.le (by exact_mod_cast hd₁₂) hα.le
  have hlog₁ : 0 ≤ Real.log u₁ := Real.log_nonneg hu₁1
  have hlog_div : Real.log u₂ - Real.log u₁ ≤ u₂ / u₁ - 1 := by
    rw [← Real.log_div hu₂.ne' hu₁.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hu₂ hu₁)
  have hmul : u₁ * (Real.log u₂ - Real.log u₁) ≤ u₂ - u₁ := by
    calc u₁ * (Real.log u₂ - Real.log u₁) ≤ u₁ * (u₂ / u₁ - 1) :=
          mul_le_mul_of_nonneg_left hlog_div hu₁.le
      _ = u₁ * (u₂ / u₁) - u₁ := by ring
      _ = u₂ - u₁ := by rw [mul_div_cancel₀ _ hu₁.ne']
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hu₁₂) hlog₁]

/-- Abel's inequality on a block for `d^{-α} log d`: bounded partial sums against `(i+k)^{-α} log(i+k)`. -/
theorem abs_sum_block_rpow_log_le {s : ℕ → ℝ} {B α : ℝ} (hB : 0 ≤ B) (hα : 0 < α)
    (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) {k : ℕ} (hk : 1 ≤ k) (K : ℕ) :
    |∑ i ∈ range K, ((i + k : ℕ) : ℝ) ^ (-α) * Real.log (i + k : ℕ) * s (i + k)| ≤
      2 * B * (k : ℝ) ^ (-α) * (Real.log k + 2 / α) := by
  have haux := abs_sum_range_mul_antitone_le (fun i => s (i + k))
    (fun i => logDecayAux α (i + k)) K (by linarith : 0 ≤ 2 * B)
    (fun i => logDecayAux_nonneg hα (i + k))
    (fun i j hij => logDecayAux_antitone hα (by omega) (by omega))
    (fun K' _ => by
      rw [dampedSign_sum_range_shift_eq_sub]
      calc _ ≤ |∑ d ∈ range (k + K'), s d| + |∑ d ∈ range k, s d| := abs_sub _ _
        _ ≤ 2 * B := by linarith [hS (k + K'), hS k])
  simp only [zero_add] at haux
  have hrpow := abs_sum_block_rpow_le hB hα.le hS hk K
  have hdecomp : ∑ i ∈ range K, ((i + k : ℕ) : ℝ) ^ (-α) * Real.log (i + k : ℕ) * s (i + k) =
      (∑ i ∈ range K, logDecayAux α (i + k) * s (i + k)) -
        (1 / α) * ∑ i ∈ range K, ((i + k : ℕ) : ℝ) ^ (-α) * s (i + k) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [rpow_neg_mul_log_eq_sub α (i + k)]
    ring
  rw [hdecomp]
  have hα0 : 0 ≤ 1 / α := by positivity
  calc |∑ i ∈ range K, logDecayAux α (i + k) * s (i + k) -
        (1 / α) * ∑ i ∈ range K, ((i + k : ℕ) : ℝ) ^ (-α) * s (i + k)|
      ≤ |∑ i ∈ range K, logDecayAux α (i + k) * s (i + k)| +
          (1 / α) * |∑ i ∈ range K, ((i + k : ℕ) : ℝ) ^ (-α) * s (i + k)| := by
        refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul, abs_of_nonneg hα0]
    _ ≤ 2 * B * logDecayAux α k + (1 / α) * (2 * B * (k : ℝ) ^ (-α)) :=
        add_le_add haux (mul_le_mul_of_nonneg_left hrpow hα0)
    _ = 2 * B * (k : ℝ) ^ (-α) * (Real.log k + 2 / α) := by
        unfold logDecayAux; ring

/-- Majorant comparing `k^{-α} (log k + 2/α)` to `(4/ε) k^{ε/2 - α}` for `α ≥ ε > 0`. -/
theorem rpow_neg_mul_log_add_two_div_le {ε α : ℝ} (hε : 0 < ε) (hα : ε ≤ α) {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) ^ (-α) * (Real.log k + 2 / α) ≤ (4 / ε) * (k : ℝ) ^ (ε / 2 - α) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hη : 0 < ε / 2 := by linarith
  have hlog : Real.log k ≤ (2 / ε) * (k : ℝ) ^ (ε / 2) := by
    have h := Real.log_le_rpow_div hk0.le hη
    calc Real.log k ≤ (k : ℝ) ^ (ε / 2) / (ε / 2) := h
      _ = (2 / ε) * (k : ℝ) ^ (ε / 2) := by ring
  have htwo : 2 / α ≤ (2 / ε) * (k : ℝ) ^ (ε / 2) := by
    have h1 : 2 / α ≤ 2 / ε := div_le_div_of_nonneg_left (by norm_num) hε hα
    have h2 : (1 : ℝ) ≤ (k : ℝ) ^ (ε / 2) := Real.one_le_rpow hk1 hη.le
    calc 2 / α ≤ (2 / ε) * 1 := by linarith
      _ ≤ (2 / ε) * (k : ℝ) ^ (ε / 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsum_le : Real.log k + 2 / α ≤ (4 / ε) * (k : ℝ) ^ (ε / 2) := by
    calc Real.log k + 2 / α ≤ (2 / ε) * (k : ℝ) ^ (ε / 2) + (2 / ε) * (k : ℝ) ^ (ε / 2) :=
          add_le_add hlog htwo
      _ = (4 / ε) * (k : ℝ) ^ (ε / 2) := by ring
  calc (k : ℝ) ^ (-α) * (Real.log k + 2 / α)
      ≤ (k : ℝ) ^ (-α) * ((4 / ε) * (k : ℝ) ^ (ε / 2)) :=
        mul_le_mul_of_nonneg_left hsum_le (Real.rpow_nonneg hk0.le _)
    _ = (4 / ε) * ((k : ℝ) ^ (-α) * (k : ℝ) ^ (ε / 2)) := by ring
    _ = (4 / ε) * (k : ℝ) ^ (ε / 2 - α) := by
        rw [← Real.rpow_add hk0, show -α + ε / 2 = ε / 2 - α by ring]

/-- Abel's inequality on an infinite tail for `(i+k)^{-α} log(i+k) s(i+k)` when `α > 1`. -/
theorem abs_tsum_tail_rpow_log_le {s : ℕ → ℝ} {B α : ℝ} (hB : 0 ≤ B) (hα : 1 < α)
    (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun i : ℕ => ((i + k : ℕ) : ℝ) ^ (-α) * Real.log (i + k : ℕ) * s (i + k)) ∧
      |∑' i : ℕ, ((i + k : ℕ) : ℝ) ^ (-α) * Real.log (i + k : ℕ) * s (i + k)| ≤
        2 * B * (k : ℝ) ^ (-α) * (Real.log k + 2 / α) := by
  have hs1 : ∀ d, |s d| ≤ 2 * B := fun d => by
    have : s d = ∑ e ∈ range (d + 1), s e - ∑ e ∈ range d, s e := by rw [Finset.sum_range_succ]; ring
    rw [this]
    calc _ ≤ |∑ e ∈ range (d + 1), s e| + |∑ e ∈ range d, s e| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hS (d + 1), hS d]
  set δ := (α - 1) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hp : Summable (fun i : ℕ => ((i + k : ℕ) : ℝ) ^ (-(α - δ))) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(α - δ))) k).mpr
      (Real.summable_nat_rpow.mpr (by simp only [δ]; linarith))
  have hsum : Summable (fun i : ℕ => ((i + k : ℕ) : ℝ) ^ (-α) * Real.log (i + k : ℕ) * s (i + k)) := by
    refine (hp.mul_left (2 * B / δ)).of_norm_bounded fun i => ?_
    have hik : (0 : ℝ) < (i + k : ℕ) := by exact_mod_cast (show 0 < i + k by omega)
    have hlog := Real.log_le_rpow_div hik.le hδ
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hik.le _),
      abs_of_nonneg (Real.log_natCast_nonneg _)]
    calc ((i + k : ℕ) : ℝ) ^ (-α) * Real.log (i + k : ℕ) * |s (i + k)|
        ≤ ((i + k : ℕ) : ℝ) ^ (-α) * (((i + k : ℕ) : ℝ) ^ δ / δ) * (2 * B) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hik.le _))
            (hs1 _) (abs_nonneg _) (by positivity)
      _ = 2 * B / δ * (((i + k : ℕ) : ℝ) ^ (-α) * ((i + k : ℕ) : ℝ) ^ δ) := by ring
      _ = 2 * B / δ * ((i + k : ℕ) : ℝ) ^ (-(α - δ)) := by
          rw [← Real.rpow_add hik, show -α + δ = -(α - δ) by ring]
  refine ⟨hsum, ?_⟩
  exact le_of_tendsto' hsum.hasSum.tendsto_sum_nat.abs
    fun K => abs_sum_block_rpow_log_le hB (by linarith) hS hk K

theorem logWeight_dampedSignWeight_div {s : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    logWeight (dampedSignWeight s ε) d / d = (d : ℝ) ^ (-(1 + ε)) * Real.log d * s d := by
  unfold logWeight
  rw [mul_div_right_comm, dampedSignWeight_div hε]
  ring

theorem summable_logWeight_dampedSignWeight_div {s : ℕ → ℝ} {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) :
    Summable (fun d : ℕ => logWeight (dampedSignWeight s ε) d / d) := by
  have h := (abs_tsum_tail_rpow_log_le hB (by linarith : 1 < 1 + ε) hS (le_refl 1)).1
  refine (summable_nat_add_iff 1).mp ?_
  exact h.congr fun i => (logWeight_dampedSignWeight_div hε (i + 1)).symm

/-- **The hyperbola bound for logarithmic sign weights.** For partial sums of `s` bounded by `B`
and every split `1 ≤ D ≤ n`,
`|A_{logWeight(s d^{-ε})}(n)| ≤ (2B/ε) D + (16B/ε) n (D+1)^{-(1 + ε/2)}`. -/
theorem abs_weightCenteredPrefix_logWeight_dampedSign_le {s : ℕ → ℝ} {B ε : ℝ} (hB : 0 ≤ B)
    (hε : 0 < ε) (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) {n D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n) :
    |weightCenteredPrefix (logWeight (dampedSignWeight s ε))
        (∑' d : ℕ, logWeight (dampedSignWeight s ε) d / d) n| ≤
      2 * (B / ε) * D + 16 * (B / ε) * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε / 2)) := by
  set c := logWeight (dampedSignWeight s ε)
  have hs1 : ∀ d, |s d| ≤ 2 * B := fun d => by
    have : s d = ∑ e ∈ range (d + 1), s e - ∑ e ∈ range d, s e := by rw [Finset.sum_range_succ]; ring
    rw [this]
    calc _ ≤ |∑ e ∈ range (d + 1), s e| + |∑ e ∈ range d, s e| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hS (d + 1), hS d]
  have hsum := summable_logWeight_dampedSignWeight_div hB hε hS
  have hmean : ∑' d : ℕ, c d / d = ∑ d ∈ Icc 1 D, c d / d +
      ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) := by
    rw [← hsum.sum_add_tsum_nat_add (D + 1), dampedSign_sum_range_succ_eq_add_Icc]
    simp [c, logWeight, dampedSignWeight]
  have hsplit : ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) + ∑ d ∈ Ioc D n, c d * ((n / d : ℕ) : ℝ) := by
    have h1 : Icc 1 n = Ioc 0 n := by ext d; simp only [mem_Icc, mem_Ioc]; omega
    have h2 : Icc 1 D = Ioc 0 D := by ext d; simp only [mem_Icc, mem_Ioc]; omega
    rw [h1, h2, sum_Ioc_consecutive _ (Nat.zero_le D) hDn]
  have hlong : ∑ d ∈ Ioc D n, c d * ((n / d : ℕ) : ℝ) =
      ∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d := by
    have hcount : ∀ d, c d * ((n / d : ℕ) : ℝ) = ∑ _k ∈ Icc 1 (n / d), c d := fun d => by
      rw [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_comm]; simp
    simp_rw [hcount]
    refine sum_comm' fun d k => ?_
    simp only [mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨⟨hDd, hdn⟩, hk1, hkd⟩
      have hd0 : 0 < d := by omega
      have hkd' : k * d ≤ n := (Nat.le_div_iff_mul_le hd0).mp hkd
      refine ⟨⟨hDd, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [mul_comm k d])⟩,
        hk1, le_trans hkd (Nat.div_le_self n d)⟩
    · rintro ⟨⟨hDd, hdk⟩, hk1, hkn⟩
      have hd0 : 0 < d := by omega
      have hdk' : d * k ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hdk
      refine ⟨⟨hDd, le_trans hdk (Nat.div_le_self n k)⟩, hk1,
        (Nat.le_div_iff_mul_le hd0).mpr (by linarith [mul_comm k d])⟩
  -- piece (a): short moduli, using `(d : ℝ)^{-ε} log d ≤ 1/ε`
  have ha : |∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d| ≤
      2 * (B / ε) * D := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Icc 1 D, |c d * ((n / d : ℕ) : ℝ) - n * (c d / d)| ≤ 2 * (B / ε) := by
      intro d hd
      rw [mem_Icc] at hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hfl1 : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
      have hfl2 : (n : ℝ) / d - 1 < ((n / d : ℕ) : ℝ) := by
        have h := Nat.lt_div_mul_add (a := n) (show 0 < d by omega)
        have h' : (n : ℝ) < ((n / d : ℕ) : ℝ) * d + d := by exact_mod_cast h
        rw [div_sub_one hd0.ne', div_lt_iff₀ hd0]; linarith
      have hlogpow : (d : ℝ) ^ (-ε) * Real.log d ≤ 1 / ε := by
        have hlog := Real.log_le_rpow_div hd0.le hε
        calc (d : ℝ) ^ (-ε) * Real.log d ≤ (d : ℝ) ^ (-ε) * ((d : ℝ) ^ ε / ε) :=
              mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hd0.le _)
          _ = ((d : ℝ) ^ (-ε) * (d : ℝ) ^ ε) / ε := by ring
          _ = 1 / ε := by rw [← Real.rpow_add hd0, neg_add_cancel, Real.rpow_zero]
      have hc : |c d| ≤ 2 * (B / ε) := by
        rw [show c d = s d * ((d : ℝ) ^ (-ε) * Real.log d) by
          simp only [c, logWeight, dampedSignWeight]; ring,
          abs_mul, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_natCast_nonneg d))]
        calc |s d| * ((d : ℝ) ^ (-ε) * Real.log d) ≤ (2 * B) * (1 / ε) :=
              mul_le_mul (hs1 d) hlogpow
                (mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_natCast_nonneg d)) (by linarith)
          _ = 2 * (B / ε) := by ring
      have heq : c d * ((n / d : ℕ) : ℝ) - n * (c d / d) = c d * (((n / d : ℕ) : ℝ) - n / d) := by
        field_simp
      rw [heq, abs_mul]
      have hfr : |((n / d : ℕ) : ℝ) - n / d| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      calc |c d| * |((n / d : ℕ) : ℝ) - n / d| ≤ 2 * (B / ε) * 1 :=
            mul_le_mul hc hfr (abs_nonneg _) (by positivity)
        _ = 2 * (B / ε) := mul_one _
    calc ∑ d ∈ Icc 1 D, |c d * ((n / d : ℕ) : ℝ) - n * (c d / d)| ≤ ∑ _d ∈ Icc 1 D, 2 * (B / ε) :=
          sum_le_sum hterm
      _ = 2 * (B / ε) * D := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  -- piece (b): long moduli
  have hb : |∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d| ≤
      8 * (B / ε) * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε / 2)) := by
    have hblock : ∀ k ∈ Icc 1 n, |∑ d ∈ Ioc D (n / k), c d| ≤
        (if D + 1 ≤ n / k then 8 * (B / ε) * ((D + 1 : ℕ) : ℝ) ^ (-(ε / 2)) else 0) := by
      intro k _
      split_ifs with h
      · obtain ⟨K, hK⟩ : ∃ K, n / k = D + K := ⟨n / k - D, by omega⟩
        rw [hK, dampedSign_sum_Ioc_eq_sum_range_shift]
        have hab := abs_sum_block_rpow_log_le hB hε hS (k := D + 1) (by omega) K
        have hmaj := rpow_neg_mul_log_add_two_div_le hε le_rfl (k := D + 1) (by omega)
        have hterm_eq : ∑ i ∈ range K, c (i + (D + 1)) =
            ∑ i ∈ range K, ((i + (D + 1) : ℕ) : ℝ) ^ (-ε) * Real.log (i + (D + 1) : ℕ) *
              s (i + (D + 1)) :=
          sum_congr rfl fun i _ => by simp only [c, logWeight, dampedSignWeight]; ring
        rw [hterm_eq]
        calc |∑ i ∈ range K, ((i + (D + 1) : ℕ) : ℝ) ^ (-ε) * Real.log (i + (D + 1) : ℕ) *
              s (i + (D + 1))|
            ≤ 2 * B * (((D + 1 : ℕ) : ℝ) ^ (-ε) * (Real.log (D + 1 : ℕ) + 2 / ε)) := by
              linarith [hab]
          _ ≤ 2 * B * ((4 / ε) * ((D + 1 : ℕ) : ℝ) ^ (ε / 2 - ε)) :=
              mul_le_mul_of_nonneg_left hmaj (by linarith)
          _ = 8 * (B / ε) * ((D + 1 : ℕ) : ℝ) ^ (-(ε / 2)) := by
              rw [show ε / 2 - ε = -(ε / 2) by ring]; ring
      · rw [Ioc_eq_empty (by omega), sum_empty, abs_zero]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hblock).trans ?_)
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hcard : ((filter (fun k => D + 1 ≤ n / k) (Icc 1 n)).card : ℝ) ≤ (n : ℝ) / (D + 1) := by
      have hsub : filter (fun k => D + 1 ≤ n / k) (Icc 1 n) ⊆ Icc 1 (n / (D + 1)) := by
        intro k hk
        simp only [mem_filter, mem_Icc] at hk ⊢
        refine ⟨hk.1.1, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
        have := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hk.2
        linarith [mul_comm k (D + 1)]
      calc ((filter (fun k => D + 1 ≤ n / k) (Icc 1 n)).card : ℝ) ≤ (Icc 1 (n / (D + 1))).card := by
            exact_mod_cast card_le_card hsub
        _ = ((n / (D + 1) : ℕ) : ℝ) := by rw [Nat.card_Icc]; simp
        _ ≤ (n : ℝ) / (D + 1) := by
            have := Nat.cast_div_le (α := ℝ) (m := n) (n := D + 1)
            push_cast at this; exact this
    have hD1 : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) := by positivity
    have hpow : ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε / 2)) =
        ((D + 1 : ℕ) : ℝ) ^ (-(ε / 2)) / ((D + 1 : ℕ) : ℝ) := by
      rw [show -(1 + ε / 2) = -(ε / 2) - 1 by ring, Real.rpow_sub_one hD1.ne']
    rw [hpow]
    have hB2 : 0 ≤ 8 * (B / ε) * ((D + 1 : ℕ) : ℝ) ^ (-(ε / 2)) := by positivity
    calc ((filter (fun k => D + 1 ≤ n / k) (Icc 1 n)).card : ℝ) *
          (8 * (B / ε) * ((D + 1 : ℕ) : ℝ) ^ (-(ε / 2)))
        ≤ (n : ℝ) / (D + 1) * (8 * (B / ε) * ((D + 1 : ℕ) : ℝ) ^ (-(ε / 2))) :=
          mul_le_mul_of_nonneg_right hcard hB2
      _ = 8 * (B / ε) * n * (((D + 1 : ℕ) : ℝ) ^ (-(ε / 2)) / ((D + 1 : ℕ) : ℝ)) := by
          push_cast; ring
  -- piece (c): the tail
  have hc : |(n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ)| ≤
      8 * (B / ε) * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε / 2)) := by
    have ht := (abs_tsum_tail_rpow_log_le hB (by linarith : 1 < 1 + ε) hS (k := D + 1) (by omega)).2
    have hmaj := rpow_neg_mul_log_add_two_div_le hε (by linarith : ε ≤ 1 + ε) (k := D + 1) (by omega)
    have heq : ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) =
        ∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * Real.log (i + (D + 1) : ℕ) *
          s (i + (D + 1)) :=
      tsum_congr fun i => logWeight_dampedSignWeight_div hε (i + (D + 1))
    rw [heq, abs_mul, Nat.abs_cast]
    have ht' : |∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * Real.log (i + (D + 1) : ℕ) *
        s (i + (D + 1))| ≤ 8 * (B / ε) * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε / 2)) := by
      calc |∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * Real.log (i + (D + 1) : ℕ) *
            s (i + (D + 1))|
          ≤ 2 * B * (((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) * (Real.log (D + 1 : ℕ) + 2 / (1 + ε))) := by
            linarith [ht]
        _ ≤ 2 * B * ((4 / ε) * ((D + 1 : ℕ) : ℝ) ^ (ε / 2 - (1 + ε))) :=
            mul_le_mul_of_nonneg_left hmaj (by linarith)
        _ = 8 * (B / ε) * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε / 2)) := by
            rw [show ε / 2 - (1 + ε) = -(1 + ε / 2) by ring]; ring
    calc (n : ℝ) * |∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * Real.log (i + (D + 1) : ℕ) *
          s (i + (D + 1))|
        ≤ (n : ℝ) * (8 * (B / ε) * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε / 2))) :=
          mul_le_mul_of_nonneg_left ht' (Nat.cast_nonneg n)
      _ = 8 * (B / ε) * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε / 2)) := by ring
  -- assemble
  have hA : weightCenteredPrefix c (∑' d : ℕ, c d / d) n =
      (∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d) +
        ∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d -
          (n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) := by
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, hsplit, hlong, hmean]
    ring
  rw [hA]
  calc _ ≤ |∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d| +
        |∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d| +
          |(n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- **Power-saving bound for logarithmic sign weights.**
`|A_{logWeight(s d^{-ε})}(n)| ≤ (18B/ε) n^{1/(2 + ε/2)}` for every `n ≥ 1`. -/
theorem abs_weightCenteredPrefix_logWeight_dampedSign_le_rpow {s : ℕ → ℝ} {B ε : ℝ} (hB : 0 ≤ B)
    (hε : 0 < ε) (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) {n : ℕ} (hn : 1 ≤ n) :
    |weightCenteredPrefix (logWeight (dampedSignWeight s ε))
        (∑' d : ℕ, logWeight (dampedSignWeight s ε) d / d) n| ≤
      18 * (B / ε) * (n : ℝ) ^ (1 / (2 + ε / 2)) := by
  set θ := 1 / (2 + ε / 2)
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set D := ⌊(n : ℝ) ^ θ⌋₊
  have hx1 : (1 : ℝ) ≤ (n : ℝ) ^ θ := Real.one_le_rpow hn1 hθ0.le
  have hD1 : 1 ≤ D := (Nat.one_le_floor_iff _).mpr hx1
  have hDn : D ≤ n := Nat.floor_le_of_le (by
    calc (n : ℝ) ^ θ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hθ1
      _ = n := Real.rpow_one _)
  have hDle : (D : ℝ) ≤ (n : ℝ) ^ θ := Nat.floor_le (by positivity)
  have hDlt : (n : ℝ) ^ θ < ((D + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one _
  have hmain := abs_weightCenteredPrefix_logWeight_dampedSign_le hB hε hS hD1 hDn
  have hxpos : 0 < (n : ℝ) ^ θ := by positivity
  have hpow : ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε / 2)) ≤ ((n : ℝ) ^ θ) ^ (-(1 + ε / 2)) :=
    Real.rpow_le_rpow_of_nonpos hxpos hDlt.le (by linarith)
  have hid : (n : ℝ) * ((n : ℝ) ^ θ) ^ (-(1 + ε / 2)) = (n : ℝ) ^ θ := by
    rw [← Real.rpow_mul hn0.le]
    have h1 : (n : ℝ) * (n : ℝ) ^ (θ * -(1 + ε / 2)) = (n : ℝ) ^ (1 + θ * -(1 + ε / 2)) := by
      rw [Real.rpow_add hn0, Real.rpow_one]
    rw [h1]
    congr 1
    have : (2 + ε / 2) ≠ 0 := by linarith
    simp only [θ]
    field_simp
    ring
  have hBε : 0 ≤ B / ε := div_nonneg hB hε.le
  calc _ ≤ 2 * (B / ε) * D + 16 * (B / ε) * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε / 2)) := hmain
    _ ≤ 2 * (B / ε) * (n : ℝ) ^ θ + 16 * (B / ε) * (n * ((n : ℝ) ^ θ) ^ (-(1 + ε / 2))) := by
        have h1 := mul_le_mul_of_nonneg_left hDle (by linarith : 0 ≤ 2 * (B / ε))
        have h2 := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 16 * (B / ε) * n)
        nlinarith
    _ = 18 * (B / ε) * (n : ℝ) ^ θ := by rw [hid]; ring

/-- **Bounded sign patterns twisted by `log d` pay the receiver at every damping `ε > 0`.** -/
theorem weightPronicEnergy_logWeight_dampedSign_le {s : ℕ → ℝ} {B ε : ℝ} (hB : 0 ≤ B)
    (hε : 0 < ε) (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) (T : ℕ) :
    weightPronicEnergy (logWeight (dampedSignWeight s ε))
        (∑' d : ℕ, logWeight (dampedSignWeight s ε) d / d) T ≤
      324 * (B / ε) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (2 * (1 / (2 + ε / 2)) - 2) := by
  set θ := 1 / (2 + ε / 2)
  have hθ : 2 * θ - 2 < -1 := by
    have : θ < 1 / 2 := by
      simp only [θ]; rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (2 * θ - 2)) := Real.summable_nat_rpow.mpr hθ
  unfold weightPronicEnergy
  have hterm : ∀ n ∈ Icc 1 T,
      weightCenteredPrefix (logWeight (dampedSignWeight s ε))
          (∑' d : ℕ, logWeight (dampedSignWeight s ε) d / d) n ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) ≤ 324 * (B / ε) ^ 2 * (n : ℝ) ^ (2 * θ - 2) := by
    intro n hn
    rw [mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hA := abs_weightCenteredPrefix_logWeight_dampedSign_le_rpow hB hε hS hn.1
    have hA2 : weightCenteredPrefix (logWeight (dampedSignWeight s ε))
        (∑' d : ℕ, logWeight (dampedSignWeight s ε) d / d) n ^ 2
        ≤ (18 * (B / ε) * (n : ℝ) ^ θ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
    have hrp : ((n : ℝ) ^ θ) ^ 2 / ((n : ℝ) * (n : ℝ)) = (n : ℝ) ^ (2 * θ - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, Real.rpow_sub hn0, Real.rpow_two]
      norm_num
      ring_nf
    calc _ ≤ (18 * (B / ε) * (n : ℝ) ^ θ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
          div_le_div_of_nonneg_right hA2 (by positivity)
      _ ≤ (18 * (B / ε) * (n : ℝ) ^ θ) ^ 2 / ((n : ℝ) * (n : ℝ)) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
      _ = 324 * (B / ε) ^ 2 * (((n : ℝ) ^ θ) ^ 2 / ((n : ℝ) * (n : ℝ))) := by ring
      _ = 324 * (B / ε) ^ 2 * (n : ℝ) ^ (2 * θ - 2) := by rw [hrp]
  calc _ ≤ ∑ n ∈ Icc 1 T, 324 * (B / ε) ^ 2 * (n : ℝ) ^ (2 * θ - 2) := sum_le_sum hterm
    _ = 324 * (B / ε) ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (2 * θ - 2) := by rw [mul_sum]
    _ ≤ 324 * (B / ε) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (2 * θ - 2) :=
        mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) (by positivity)

/-- **Unconditional receiver boundedness of `logWeight (dampedSignWeight s ε)` for every `ε > 0`.** -/
theorem receiverBounded_logWeight_dampedSign {s : ℕ → ℝ} {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) :
    ReceiverBounded (logWeight (dampedSignWeight s ε)) :=
  ⟨_, weightPronicEnergy_logWeight_dampedSign_le hB hε hS⟩

/-- Unconditional receiver boundedness of `χ₄(d) d^{-ε} log d` at every damping `ε > 0`. -/
theorem receiverBounded_logWeight_chiFour {ε : ℝ} (hε : 0 < ε) :
    ReceiverBounded (logWeight (dampedSignWeight chiFour ε)) :=
  receiverBounded_logWeight_dampedSign zero_le_one hε abs_sum_range_chiFour_le

/-- Unconditional receiver boundedness of `fermiPattern(d) d^{-ε} log d` at every damping `ε > 0`. -/
theorem receiverBounded_logWeight_fermiPattern {ε : ℝ} (hε : 0 < ε) :
    ReceiverBounded (logWeight (dampedSignWeight fermiPattern ε)) :=
  receiverBounded_logWeight_dampedSign zero_le_one hε abs_sum_range_fermiPattern_le

/-! ### 3. The double-zero pole law (`↔`) for logarithmic weights -/

/-- Rearranged Leibniz identity for `logWeight`:
`k ⋆ (logWeight c) = logWeight (k ⋆ c) - (logWeight k) ⋆ c`. -/
theorem dirichletConv_logWeight_eq_sub (k c : ℕ → ℝ) (n : ℕ) :
    RHTower.dirichletConv k (logWeight c) n =
      logWeight (RHTower.dirichletConv k c) n - RHTower.dirichletConv (logWeight k) c n := by
  linarith [logWeight_dirichletConv k c n]

/-- The pole value of `logWeight k` is the pole slope of `k`. -/
theorem poleValue_logWeight_eq_poleSlope (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) :
    poleValue (logWeight k) J ε = poleSlope k J ε :=
  rfl

theorem logWeight_support {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) :
    ∀ j, J < j → logWeight k j = 0 := fun j hj => by
  simp [logWeight, hkJ j hj]

/-- For any `ε > 0`, a finite kernel with vanishing `poleValue` repairs `d^{-ε}`. -/
theorem receiverBounded_dirichletConv_unit_of_poleValue_eq_zero {ε : ℝ} (hε : 0 < ε)
    {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) (hK : poleValue k J ε = 0) :
    ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) := by
  rw [show RHTower.dirichletConv k (dampedSignWeight unitSign ε) =
      dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) unitSign) ε from
    funext (dirichletConv_damped_eq k unitSign ε)]
  exact exists_weightPronicEnergy_dampedSign_le (sum_nonneg fun j _ => abs_nonneg _) hε
    (abs_sum_range_dirichletConv_unit_le hkJ hK)

/-- Absolute divisor-density summability of `k ⋆ d^{-ε}` for any finite kernel `k` and `ε > 0`. -/
theorem summable_abs_dirichletConv_unit_div {ε : ℝ} (hε : 0 < ε)
    {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) :
    Summable (fun d : ℕ => |RHTower.dirichletConv k (dampedSignWeight unitSign ε) d / d|) := by
  set L := ∑ j ∈ Icc 1 J, |undampedKernel k ε j|
  have hsign : ∀ d, |RHTower.dirichletConv (undampedKernel k ε) unitSign d| ≤ L := fun d => by
    unfold RHTower.dirichletConv
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ d.divisors, |undampedKernel k ε j * unitSign (d / j)| ≤
          ∑ j ∈ d.divisors.filter (· ≤ J), |undampedKernel k ε j| := by
          rw [sum_filter]
          refine sum_le_sum fun j _ => ?_
          split_ifs with hj
          · rw [unitSign, mul_one]
          · rw [undampedKernel_support hkJ ε j (by omega), zero_mul, abs_zero]
      _ ≤ L := sum_le_sum_of_subset_of_nonneg (fun j hj => by
            obtain ⟨hjd, hjJ⟩ := mem_filter.mp hj
            exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hjd, hjJ⟩) fun _ _ _ => abs_nonneg _
  rw [show RHTower.dirichletConv k (dampedSignWeight unitSign ε) =
      dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) unitSign) ε from
    funext (dirichletConv_damped_eq k unitSign ε)]
  refine ((Real.summable_nat_rpow.mpr (show -(1 + ε) < -1 by linarith)).mul_left L).of_nonneg_of_le
    (fun _ => abs_nonneg _) fun d => ?_
  rw [dampedSignWeight_div hε, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _),
    mul_comm]
  exact mul_le_mul_of_nonneg_right (hsign d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

/-- Absolute divisor-density summability of `k ⋆ (d^{-ε} log d)` for any finite kernel `k` and `ε > 0`. -/
theorem summable_abs_dirichletConv_logWeight_unit_div {ε : ℝ} (hε : 0 < ε)
    {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) :
    Summable (fun d : ℕ =>
      |RHTower.dirichletConv k (logWeight (dampedSignWeight unitSign ε)) d / d|) := by
  set L := ∑ j ∈ Icc 1 J, |undampedKernel k ε j|
  have hsign : ∀ d, |RHTower.dirichletConv (undampedKernel k ε) unitSign d| ≤ L := fun d => by
    unfold RHTower.dirichletConv
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ d.divisors, |undampedKernel k ε j * unitSign (d / j)| ≤
          ∑ j ∈ d.divisors.filter (· ≤ J), |undampedKernel k ε j| := by
          rw [sum_filter]
          refine sum_le_sum fun j _ => ?_
          split_ifs with hj
          · rw [unitSign, mul_one]
          · rw [undampedKernel_support hkJ ε j (by omega), zero_mul, abs_zero]
      _ ≤ L := sum_le_sum_of_subset_of_nonneg (fun j hj => by
            obtain ⟨hjd, hjJ⟩ := mem_filter.mp hj
            exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hjd, hjJ⟩) fun _ _ _ => abs_nonneg _
  set u := dampedSignWeight unitSign ε
  have hclass : DampedClass L ε (RHTower.dirichletConv k u) := fun d => by
    rw [dirichletConv_damped_eq k unitSign ε d, dampedSignWeight, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_mul_of_nonneg_right (hsign d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hs1 : Summable (fun d : ℕ => |logWeight (RHTower.dirichletConv k u) d / d|) := by
    refine (summable_abs_mul_log_div_of_dampedClass hε hclass).congr fun d => ?_
    rw [logWeight, abs_div, abs_mul, Nat.abs_cast, abs_of_nonneg (Real.log_natCast_nonneg d)]
  have hs2 : Summable (fun d : ℕ => |RHTower.dirichletConv (logWeight k) u d / d|) :=
    summable_abs_dirichletConv_unit_div hε (logWeight_support hkJ)
  refine (hs1.add hs2).of_nonneg_of_le (fun _ => abs_nonneg _) fun d => ?_
  rw [dirichletConv_logWeight_eq_sub, sub_div]
  exact abs_sub _ _

/-- **Sufficiency at every `ε > 0`**: if `poleValue k J ε = 0` and `poleSlope k J ε = 0`, then
`k ⋆ logWeight (dampedSignWeight unitSign ε)` has bounded receiver. -/
theorem receiverBounded_dirichletConv_logWeight_unit_of_poleValue_and_poleSlope_eq_zero
    {ε : ℝ} (hε : 0 < ε) {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0)
    (hK : poleValue k J ε = 0) (hK' : poleSlope k J ε = 0) :
    ReceiverBounded (RHTower.dirichletConv k (logWeight (dampedSignWeight unitSign ε))) := by
  set u := dampedSignWeight unitSign ε
  have hdecomp : RHTower.dirichletConv k (logWeight u) =
      fun n => logWeight (RHTower.dirichletConv k u) n -
        RHTower.dirichletConv (logWeight k) u n :=
    funext (dirichletConv_logWeight_eq_sub k u)
  rw [hdecomp]
  have hku : RHTower.dirichletConv k u =
      dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) unitSign) ε :=
    funext (dirichletConv_damped_eq k unitSign ε)
  have hB1 : ReceiverBounded (logWeight (RHTower.dirichletConv k u)) := by
    rw [hku]
    exact receiverBounded_logWeight_dampedSign (sum_nonneg fun j _ => abs_nonneg _) hε
      (abs_sum_range_dirichletConv_unit_le hkJ hK)
  have hs1 : Summable (fun d : ℕ => logWeight (RHTower.dirichletConv k u) d / d) := by
    rw [hku]
    exact summable_logWeight_dampedSignWeight_div (sum_nonneg fun j _ => abs_nonneg _) hε
      (abs_sum_range_dirichletConv_unit_le hkJ hK)
  have hB2 : ReceiverBounded (RHTower.dirichletConv (logWeight k) u) :=
    receiverBounded_dirichletConv_unit_of_poleValue_eq_zero hε (logWeight_support hkJ)
      (by rw [poleValue_logWeight_eq_poleSlope, hK'])
  have hs2 : Summable (fun d : ℕ => RHTower.dirichletConv (logWeight k) u d / d) :=
    (summable_abs_dirichletConv_unit_div hε (logWeight_support hkJ)).of_abs
  exact receiverBounded_sub hs1 hs2 hB1 hB2

/-- **Finite perturbations of the logarithmic smooth power are decided by value and slope at the pole.**
For `0 < ε ≤ 1/2` and any kernel `k` supported on `[1, J]`, the receiver of
`k ⋆ logWeight (dampedSignWeight unitSign ε)` is bounded if and only if
`poleValue k J ε = 0 ∧ poleSlope k J ε = 0`. -/
theorem receiverBounded_dirichletConv_logWeight_unit_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) :
    ReceiverBounded (RHTower.dirichletConv k (logWeight (dampedSignWeight unitSign ε))) ↔
      poleValue k J ε = 0 ∧ poleSlope k J ε = 0 := by
  have heq : logWeight (dampedSignWeight unitSign ε) = fun d : ℕ => Real.log d * (d : ℝ) ^ (-ε) := by
    funext d; simp only [logWeight, dampedSignWeight, unitSign]; ring
  constructor
  · intro hB
    rw [heq] at hB
    exact poleValue_eq_zero_and_poleSlope_eq_zero_of_receiverBounded_log hε hε2 hkJ hB
  · rintro ⟨hK, hK'⟩
    exact receiverBounded_dirichletConv_logWeight_unit_of_poleValue_and_poleSlope_eq_zero
      hε hkJ hK hK'

/-- If `dampedSignWeight g (ε / 2)` is in `CriticalWiener`, then so is `logWeight (dampedSignWeight g ε)`. -/
theorem criticalWiener_logWeight_of_half {g : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hg : CriticalWiener (dampedSignWeight g (ε / 2))) :
    CriticalWiener (logWeight (dampedSignWeight g ε)) := by
  have hη : 0 < ε / 2 := by linarith
  refine (hg.mul_left (2 / ε)).of_nonneg_of_le
    (fun q => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)) fun q => ?_
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [logWeight, dampedSignWeight]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log q ≤ (2 / ε) * (q : ℝ) ^ (ε / 2) := by
    calc Real.log q ≤ (q : ℝ) ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div hq0.le hη
      _ = (2 / ε) * (q : ℝ) ^ (ε / 2) := by ring
  simp only [logWeight, dampedSignWeight]
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hq0.le _),
    abs_of_nonneg (Real.rpow_nonneg hq0.le _), abs_of_nonneg (Real.log_natCast_nonneg q)]
  calc |g q| * (q : ℝ) ^ (-ε) * Real.log q * (q : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ |g q| * (q : ℝ) ^ (-ε) * ((2 / ε) * (q : ℝ) ^ (ε / 2)) * (q : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (by positivity))
          (Real.rpow_nonneg hq0.le _)
    _ = 2 / ε * (|g q| * ((q : ℝ) ^ (-ε) * (q : ℝ) ^ (ε / 2)) * (q : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
    _ = 2 / ε * (|g q| * (q : ℝ) ^ (-(ε / 2)) * (q : ℝ) ^ (-(1 / 2 : ℝ))) := by
        rw [← Real.rpow_add hq0, show -ε + ε / 2 = -(ε / 2) by ring]

/-- **Universal double-pole law for logarithmic weights pretending to one.**
Let `b ≥ 0` be multiplicative with `b(p) = 1` at every prime and `|b| ≤ B`. For `0 < ε ≤ 1/2`
and any kernel `k` supported on `[1, J]`, the receiver of `k ⋆ logWeight (dampedSignWeight b ε)`
is bounded **if and only if** `poleValue k J ε = 0 ∧ poleSlope k J ε = 0`. -/
theorem receiverBounded_dirichletConv_logWeight_primesOne_iff {b : ArithmeticFunction ℝ}
    (hb : b.IsMultiplicative) (hb0 : ∀ n, 0 ≤ b n) (hbp : ∀ p : ℕ, p.Prime → b p = 1) {B : ℝ}
    (hB : ∀ n, |b n| ≤ B) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ} {J : ℕ}
    (hkJ : ∀ j, J < j → k j = 0) :
    ReceiverBounded (RHTower.dirichletConv k (logWeight (dampedSignWeight ⇑b ε))) ↔
      poleValue k J ε = 0 ∧ poleSlope k J ε = 0 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1)
  constructor
  · intro hR
    have hD : 0 < RHTower.Sieve.squarefreeDensity := by
      rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
    have hdom : ∀ d, oddSqfWeight ε d ≤ dampedSignWeight ⇑b ε d := fun d => by
      unfold oddSqfWeight dampedSignWeight
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      rw [oddSqfAF_apply]
      split_ifs with h
      · rw [eq_one_of_squarefree_of_primes_one hb hbp h.2]
      · exact hb0 d
    have hdrift : ∀ᶠ n : ℕ in atTop,
        RHTower.Sieve.squarefreeDensity / 3 * (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε) *
          Real.log n ≤
          (n : ℝ) * ∑ d ∈ Ioc n (2 * n), logWeight (dampedSignWeight ⇑b ε) d / d := by
      filter_upwards [eventually_oddSqfWeight_drift hε, eventually_ge_atTop 1] with n hn hn1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      have h1 := mul_le_mul_of_nonneg_right hn hlogn
      refine h1.trans ?_
      rw [mul_assoc, Finset.sum_mul]
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun d hd => ?_) hn0.le
      have hd1 : (n : ℝ) ≤ d := by exact_mod_cast (mem_Ioc.mp hd).1.le
      have hlogd : Real.log n ≤ Real.log d := Real.log_le_log hn0 hd1
      unfold logWeight
      rw [mul_div_right_comm]
      exact mul_le_mul (div_le_div_of_nonneg_right (hdom d) (Nat.cast_nonneg d)) hlogd hlogn
        (div_nonneg (mul_nonneg (hb0 d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)) (Nat.cast_nonneg d))
    refine poleValue_eq_zero_and_poleSlope_eq_zero_of_receiverBounded hε hε2
      (fun d => mul_nonneg (mul_nonneg (hb0 d) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
        (Real.log_natCast_nonneg d))
      (fun η hη hηε => ⟨B / η, fun d => ?_⟩)
      (by positivity) hdrift hkJ hR
    show |logWeight (dampedSignWeight ⇑b ε) d| ≤ (B / η) * (d : ℝ) ^ (-(ε - η))
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [logWeight, dampedSignWeight]; positivity
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hlog := Real.log_le_rpow_div hd0.le hη
    simp only [logWeight, dampedSignWeight]
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hd0.le _),
      abs_of_nonneg (Real.log_natCast_nonneg d)]
    calc |b d| * (d : ℝ) ^ (-ε) * Real.log d
        ≤ B * (d : ℝ) ^ (-ε) * ((d : ℝ) ^ η / η) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hB d) (Real.rpow_nonneg hd0.le _)) hlog
            (Real.log_natCast_nonneg d) (by positivity)
      _ = B / η * ((d : ℝ) ^ (-ε) * (d : ℝ) ^ η) := by ring
      _ = B / η * (d : ℝ) ^ (-(ε - η)) := by
          rw [← Real.rpow_add hd0, show -ε + η = -(ε - η) by ring]
  · rintro ⟨hK, hK'⟩
    set g := b * μR
    have hg : g.IsMultiplicative := hb.mul ArithmeticFunction.isMultiplicative_moebius.intCast
    have hgp : ∀ p : ℕ, p.Prime → g p = 0 := fun p hp => by
      have := mul_moebius_apply_prime_pow b hp 0
      rwa [zero_add, pow_one, pow_zero, hb.map_one, hbp p hp, sub_self] at this
    have hgk : ∀ p : ℕ, p.Prime → ∀ m : ℕ, 2 ≤ m → |g (p ^ m)| ≤ (2 * B + 1) * m :=
      fun p hp m hm => (abs_mul_moebius_apply_le hb hB hp m).trans
        (le_mul_of_one_le_right (by linarith) (by exact_mod_cast (by omega : 1 ≤ m)))
    have hW : CriticalWiener (dampedSignWeight ⇑g ε) :=
      criticalWiener_of_multiplicative hg hgp (by linarith) hgk hε
    have hW_log : CriticalWiener (logWeight (dampedSignWeight ⇑g ε)) :=
      criticalWiener_logWeight_of_half hε
        (criticalWiener_of_multiplicative hg hgp (by linarith) hgk (by linarith : 0 < ε / 2))
    have hbg : b = g * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) := by
      simp only [g]; rw [mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
    have hbase : dampedSignWeight ⇑b ε =
        RHTower.dirichletConv (dampedSignWeight ⇑g ε) (dampedSignWeight unitSign ε) := by
      funext n
      rw [← dampedSignWeight_zeta hε.ne', ← dampedSignWeight_dirichletConv]
      conv_lhs => rw [hbg]
      simp only [dampedSignWeight, mul_apply_eq_dirichletConv]
    set gε := dampedSignWeight ⇑g ε
    set uε := dampedSignWeight unitSign ε
    have hsplit : RHTower.dirichletConv k (logWeight (dampedSignWeight ⇑b ε)) =
        fun n => RHTower.dirichletConv (logWeight gε) (RHTower.dirichletConv k uε) n +
          RHTower.dirichletConv gε (RHTower.dirichletConv k (logWeight uε)) n := by
      funext n
      rw [hbase, show logWeight (RHTower.dirichletConv gε uε) =
          (fun m => RHTower.dirichletConv (logWeight gε) uε m +
            RHTower.dirichletConv gε (logWeight uε) m) from
        funext (logWeight_dirichletConv gε uε)]
      have hadd : RHTower.dirichletConv k
          (fun m => RHTower.dirichletConv (logWeight gε) uε m +
            RHTower.dirichletConv gε (logWeight uε) m) n =
          RHTower.dirichletConv k (RHTower.dirichletConv (logWeight gε) uε) n +
            RHTower.dirichletConv k (RHTower.dirichletConv gε (logWeight uε)) n := by
        unfold RHTower.dirichletConv
        simp_rw [mul_add, sum_add_distrib]
      rw [hadd, dirichletConv_left_comm k (logWeight gε) uε,
        dirichletConv_left_comm k gε (logWeight uε)]
    rw [hsplit]
    have hku_abs := summable_abs_dirichletConv_unit_div hε hkJ
    have hku_B := receiverBounded_dirichletConv_unit_of_poleValue_eq_zero hε hkJ hK
    have hterm1_B : ReceiverBounded
        (RHTower.dirichletConv (logWeight gε) (RHTower.dirichletConv k uε)) :=
      receiverBounded_dirichletConv hW_log hku_abs hku_B
    have hterm1_sum : Summable (fun n : ℕ =>
        RHTower.dirichletConv (logWeight gε) (RHTower.dirichletConv k uε) n / n) :=
      (hasSum_dirichletConv_div hW_log.summable_abs_div.of_abs.hasSum hku_abs.of_abs.hasSum
        hW_log.summable_abs_div hku_abs).summable
    have hklu_abs := summable_abs_dirichletConv_logWeight_unit_div hε hkJ
    have hklu_B := receiverBounded_dirichletConv_logWeight_unit_of_poleValue_and_poleSlope_eq_zero
      hε hkJ hK hK'
    have hterm2_B : ReceiverBounded
        (RHTower.dirichletConv gε (RHTower.dirichletConv k (logWeight uε))) :=
      receiverBounded_dirichletConv hW hklu_abs hklu_B
    have hterm2_sum : Summable (fun n : ℕ =>
        RHTower.dirichletConv gε (RHTower.dirichletConv k (logWeight uε)) n / n) :=
      (hasSum_dirichletConv_div hW.summable_abs_div.of_abs.hasSum hklu_abs.of_abs.hasSum
        hW.summable_abs_div hklu_abs).summable
    exact receiverBounded_add hterm1_sum hterm2_sum hterm1_B hterm2_B

/-! ### 4. First-order vs. second-order Fermi kernels at the double pole -/

/-- The second-order Fermi kernel `(δ₁ - 2^{1-ε} δ₂)^{⋆ 2} = δ₁ - 2·2^{1-ε} δ₂ + 2^{2(1-ε)} δ₄`. -/
def secondOrderFermiKernel (ε : ℝ) (j : ℕ) : ℝ :=
  if j = 1 then 1
  else if j = 2 then -2 * (2 : ℝ) ^ (1 - ε)
  else if j = 4 then (2 : ℝ) ^ (2 * (1 - ε))
  else 0

theorem fermiKernel_support (ε : ℝ) : ∀ j, 2 < j → fermiKernel ε j = 0 := fun j hj => by
  simp [fermiKernel, show j ≠ 1 by omega, show j ≠ 2 by omega]

theorem secondOrderFermiKernel_support (ε : ℝ) :
    ∀ j, 4 < j → secondOrderFermiKernel ε j = 0 := fun j hj => by
  simp [secondOrderFermiKernel, show j ≠ 1 by omega, show j ≠ 2 by omega, show j ≠ 4 by omega]

/-- `secondOrderFermiKernel ε` is the Dirichlet convolution square of `fermiKernel ε`. -/
theorem secondOrderFermiKernel_eq_dirichletConv (ε : ℝ) :
    secondOrderFermiKernel ε = RHTower.dirichletConv (fermiKernel ε) (fermiKernel ε) := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [secondOrderFermiKernel, RHTower.dirichletConv]
  rw [dirichletConv_twoPoint (fun j h1 h2 => by simp [fermiKernel, h1, h2]) _ hn]
  have hk1 : fermiKernel ε 1 = 1 := by simp [fermiKernel]
  have hk2 : fermiKernel ε 2 = -(2 : ℝ) ^ (1 - ε) := by simp [fermiKernel]
  rw [hk1, hk2, one_mul]
  by_cases h1 : n = 1
  · subst h1; simp [secondOrderFermiKernel, fermiKernel]
  by_cases h2 : n = 2
  · subst h2; simp [secondOrderFermiKernel, fermiKernel]; ring
  by_cases h4 : n = 4
  · subst h4
    have hpow : (2 : ℝ) ^ (1 - ε) * (2 : ℝ) ^ (1 - ε) = (2 : ℝ) ^ (2 * (1 - ε)) := by
      rw [← Real.rpow_add two_pos]; congr 1; ring
    simp [secondOrderFermiKernel, fermiKernel]
    linarith [hpow]
  · have hn2 : fermiKernel ε n = 0 := by simp [fermiKernel, h1, h2]
    have hso : secondOrderFermiKernel ε n = 0 := by simp [secondOrderFermiKernel, h1, h2, h4]
    rw [hso, hn2, zero_add]
    split_ifs with hdvd
    · have hdiv1 : n / 2 ≠ 1 := by omega
      have hdiv2 : n / 2 ≠ 2 := by omega
      simp [fermiKernel, hdiv1, hdiv2]
    · rfl

theorem poleValue_fermiKernel (ε : ℝ) : poleValue (fermiKernel ε) 2 ε = 0 := by
  have hinv : (2 : ℝ) ^ (1 - ε) * (2 : ℝ) ^ (-(1 - ε)) = 1 := by
    rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
  rw [poleValue, show Icc 1 2 = ({1, 2} : Finset ℕ) by decide, sum_pair (by norm_num)]
  simp only [fermiKernel, ↓reduceIte, Nat.cast_one, Real.one_rpow, mul_one,
    show (2 : ℕ) ≠ 1 by decide, Nat.cast_ofNat, neg_mul, hinv]
  ring

theorem poleSlope_fermiKernel (ε : ℝ) : poleSlope (fermiKernel ε) 2 ε = -Real.log 2 := by
  have hinv : (2 : ℝ) ^ (1 - ε) * (2 : ℝ) ^ (-(1 - ε)) = 1 := by
    rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
  rw [poleSlope, show Icc 1 2 = ({1, 2} : Finset ℕ) by decide, sum_pair (by norm_num)]
  simp only [fermiKernel, ↓reduceIte, Nat.cast_one, Real.log_one, mul_zero, zero_mul, zero_add,
    show (2 : ℕ) ≠ 1 by decide, Nat.cast_ofNat]
  calc -(2 : ℝ) ^ (1 - ε) * Real.log 2 * (2 : ℝ) ^ (-(1 - ε))
      = -Real.log 2 * ((2 : ℝ) ^ (1 - ε) * (2 : ℝ) ^ (-(1 - ε))) := by ring
    _ = -Real.log 2 := by rw [hinv, mul_one]

theorem poleValue_secondOrderFermiKernel (ε : ℝ) :
    poleValue (secondOrderFermiKernel ε) 4 ε = 0 := by
  have hinv2 : (2 : ℝ) ^ (1 - ε) * (2 : ℝ) ^ (-(1 - ε)) = 1 := by
    rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
  have hinv4 : (2 : ℝ) ^ (2 * (1 - ε)) * (4 : ℝ) ^ (-(1 - ε)) = 1 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul two_pos.le,
      ← Real.rpow_add two_pos, show 2 * (1 - ε) + 2 * -(1 - ε) = 0 by ring, Real.rpow_zero]
  rw [poleValue, show Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  simp only [sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 4} : Finset ℕ)),
    sum_insert (by decide : (2 : ℕ) ∉ ({3, 4} : Finset ℕ)),
    sum_insert (by decide : (3 : ℕ) ∉ ({4} : Finset ℕ)), sum_singleton,
    secondOrderFermiKernel, ↓reduceIte, show (2 : ℕ) ≠ 1 by decide,
    show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, show (3 : ℕ) ≠ 4 by decide,
    show (4 : ℕ) ≠ 1 by decide, show (4 : ℕ) ≠ 2 by decide,
    Nat.cast_one, Real.one_rpow, mul_one, zero_mul, zero_add, Nat.cast_ofNat]
  calc 1 + (-2 * (2 : ℝ) ^ (1 - ε) * (2 : ℝ) ^ (-(1 - ε)) +
        (2 : ℝ) ^ (2 * (1 - ε)) * (4 : ℝ) ^ (-(1 - ε)))
      = 1 + (-2 * ((2 : ℝ) ^ (1 - ε) * (2 : ℝ) ^ (-(1 - ε))) +
        (2 : ℝ) ^ (2 * (1 - ε)) * (4 : ℝ) ^ (-(1 - ε))) := by ring
    _ = 0 := by rw [hinv2, hinv4]; ring

theorem poleSlope_secondOrderFermiKernel (ε : ℝ) :
    poleSlope (secondOrderFermiKernel ε) 4 ε = 0 := by
  have hinv2 : (2 : ℝ) ^ (1 - ε) * (2 : ℝ) ^ (-(1 - ε)) = 1 := by
    rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
  have hinv4 : (2 : ℝ) ^ (2 * (1 - ε)) * (4 : ℝ) ^ (-(1 - ε)) = 1 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul two_pos.le,
      ← Real.rpow_add two_pos, show 2 * (1 - ε) + 2 * -(1 - ε) = 0 by ring, Real.rpow_zero]
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow, Nat.cast_ofNat]
  rw [poleSlope, show Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  simp only [sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 4} : Finset ℕ)),
    sum_insert (by decide : (2 : ℕ) ∉ ({3, 4} : Finset ℕ)),
    sum_insert (by decide : (3 : ℕ) ∉ ({4} : Finset ℕ)), sum_singleton,
    secondOrderFermiKernel, ↓reduceIte, show (2 : ℕ) ≠ 1 by decide,
    show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, show (3 : ℕ) ≠ 4 by decide,
    show (4 : ℕ) ≠ 1 by decide, show (4 : ℕ) ≠ 2 by decide,
    Nat.cast_one, Real.log_one, mul_zero, zero_mul, zero_add, Nat.cast_ofNat, hlog4]
  calc -2 * (2 : ℝ) ^ (1 - ε) * Real.log 2 * (2 : ℝ) ^ (-(1 - ε)) +
        (2 : ℝ) ^ (2 * (1 - ε)) * (2 * Real.log 2) * (4 : ℝ) ^ (-(1 - ε))
      = -2 * Real.log 2 * ((2 : ℝ) ^ (1 - ε) * (2 : ℝ) ^ (-(1 - ε))) +
        2 * Real.log 2 * ((2 : ℝ) ^ (2 * (1 - ε)) * (4 : ℝ) ^ (-(1 - ε))) := by ring
    _ = 0 := by rw [hinv2, hinv4]; ring

/-- **The first-order Fermi kernel repairs `d^{-ε}` but fails to repair `d^{-ε} log d` on `(0, 1/2]`.** -/
theorem fermiKernel_pays_unit_not_logWeight {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ReceiverBounded (RHTower.dirichletConv (fermiKernel ε) (dampedSignWeight unitSign ε)) ∧
      ¬ ReceiverBounded
        (RHTower.dirichletConv (fermiKernel ε) (logWeight (dampedSignWeight unitSign ε))) := by
  refine ⟨receiverBounded_dirichletConv_unit_of_poleValue_eq_zero hε (fermiKernel_support ε)
    (poleValue_fermiKernel ε), ?_⟩
  rw [receiverBounded_dirichletConv_logWeight_unit_iff hε hε2 (fermiKernel_support ε),
    poleSlope_fermiKernel ε]
  rintro ⟨-, hslope⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- **The second-order Fermi kernel `(δ₁ - 2^{1-ε} δ₂)^{⋆ 2}` repairs both `d^{-ε}` and `d^{-ε} log d`
at every damping `ε > 0`.** -/
theorem receiverBounded_secondOrderFermi_unit_and_logWeight {ε : ℝ} (hε : 0 < ε) :
    ReceiverBounded
      (RHTower.dirichletConv (secondOrderFermiKernel ε) (dampedSignWeight unitSign ε)) ∧
    ReceiverBounded
      (RHTower.dirichletConv (secondOrderFermiKernel ε)
        (logWeight (dampedSignWeight unitSign ε))) :=
  ⟨receiverBounded_dirichletConv_unit_of_poleValue_eq_zero hε
      (secondOrderFermiKernel_support ε) (poleValue_secondOrderFermiKernel ε),
   receiverBounded_dirichletConv_logWeight_unit_of_poleValue_and_poleSlope_eq_zero hε
      (secondOrderFermiKernel_support ε)
      (poleValue_secondOrderFermiKernel ε) (poleSlope_secondOrderFermiKernel ε)⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
