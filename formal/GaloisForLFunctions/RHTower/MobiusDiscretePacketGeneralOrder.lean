import GaloisForLFunctions.RHTower.MobiusReciprocalDiscretePacketBridge
import GaloisForLFunctions.RHTower.MobiusCofinalCubicEnergyCriterion

/-!
# All-order discrete Möbius packet identity

Let `b_k = Σ_{1 ≤ n ≤ N} μ(n) (n+1)^{-1-δ} q_n^k` with `q_n = (n-1)/(n+1)` (the order-one packet
`MobiusPacketDifference.packet N (1+δ)`), and `Δ₂^m b_k = Σ_{h ≤ m} (-1)^h C(m,h) b_{k+2h}`.
For every `m ≥ 0` and `δ ≥ 0` the order-`(m+1+δ)` Route L source energy is

`Σ_{a,b ≤ N} μ(a)μ(b) (ab)^m / (a+b)^{2m+1+δ} = 2^{1+δ-2m} Σ_k C(2m+δ+k, k) (Δ₂^m b_k)²`,

a sum of nonnegative terms.  The generic Gamma--Hankel packet expansion applies to the source
`μ(n) n^m`; the identity `1 - q_n² = 4n/(n+1)²` turns the source weight `n^m (n+1)^{-2m}` into
`4^{-m} (1 - q_n²)^m`, and the binomial theorem expands it into the step-two difference.
At `m = 2` this is the cubic identity with constant `2^{δ-3}`.
-/

open Finset

noncomputable section

namespace RHTower.DiscretePacket

open MobiusPacketDifference MobiusRenewalPacketEnergy

/-- Step-two finite difference `Δ₂^m b_k = Σ_{h ≤ m} (-1)^h C(m,h) b_{k+2h}`. -/
def stepTwoDifference (m : ℕ) (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ h ∈ range (m + 1), (-1 : ℝ) ^ h * (m.choose h : ℝ) * b (k + 2 * h)

theorem stepTwoDifference_two (b : ℕ → ℝ) (k : ℕ) :
    stepTwoDifference 2 b k = b k - 2 * b (k + 2) + b (k + 4) := by
  simp [stepTwoDifference, Finset.sum_range_succ]
  ring

/-- Shifted order-`(m+1)` Möbius coefficient `μ(n+1) (n+1)^m`. -/
def orderShiftedCoefficient (m n : ℕ) : ℝ :=
  shiftedMobiusRealCoefficient n * ((n : ℝ) + 1) ^ m

theorem one_sub_node_sq (n : ℕ) :
    1 - node n ^ 2 = 4 * ((n : ℝ) + 1) / ((n : ℝ) + 2) ^ 2 := by
  unfold node
  field_simp
  ring

/-- `(n+1)^m (n+2)^{-(2m+1+δ)} = (n+2)^{-(1+δ)} (1 - q²)^m / 4^m`. -/
theorem order_atom_factor (m n : ℕ) (δ : ℝ) :
    ((n : ℝ) + 1) ^ m * weight (2 * m + 1 + δ) n =
      weight (1 + δ) n * ((1 - node n ^ 2) ^ m / 4 ^ m) := by
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  unfold weight
  rw [one_sub_node_sq, show -(2 * (m : ℝ) + 1 + δ) = -(1 + δ) + -((2 * m : ℕ) : ℝ) by
      push_cast; ring,
    Real.rpow_add hn, Real.rpow_neg hn.le ((2 * m : ℕ) : ℝ), Real.rpow_natCast, pow_mul]
  field_simp
  rw [← mul_pow, ← mul_pow]
  congr 1
  field_simp

theorem one_sub_node_sq_pow (m n : ℕ) :
    (1 - node n ^ 2) ^ m =
      ∑ h ∈ range (m + 1), (-1 : ℝ) ^ h * (m.choose h : ℝ) * node n ^ (2 * h) := by
  rw [sub_eq_neg_add, add_pow]
  apply sum_congr rfl
  intro h _
  rw [one_pow, mul_one, neg_pow, ← pow_mul]
  ring

/-- **Packet identity.**  The order-`(m+1)` source packet is `4^{-m} Δ₂^m b_k`. -/
theorem orderPacket_eq_stepTwoDifference (m N k : ℕ) (δ : ℝ) :
    sourcePacket (orderShiftedCoefficient m) N (2 * m + 1 + δ) k =
      stepTwoDifference m (packet N (1 + δ)) k / 4 ^ m := by
  have hatom (n : ℕ) :
      orderShiftedCoefficient m n * weight (2 * m + 1 + δ) n * node n ^ k =
        ∑ h ∈ range (m + 1), (-1 : ℝ) ^ h * (m.choose h : ℝ) *
          (coefficient (1 + δ) n * node n ^ (k + 2 * h)) / 4 ^ m := by
    unfold orderShiftedCoefficient coefficient
    calc _ = shiftedMobiusRealCoefficient n * (((n : ℝ) + 1) ^ m * weight (2 * m + 1 + δ) n) *
          node n ^ k := by ring
      _ = shiftedMobiusRealCoefficient n * (weight (1 + δ) n * ((1 - node n ^ 2) ^ m / 4 ^ m)) *
          node n ^ k := by rw [order_atom_factor]
      _ = _ := by
        rw [one_sub_node_sq_pow, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        apply sum_congr rfl
        intro h _
        rw [pow_add]
        ring
  unfold sourcePacket stepTwoDifference packet
  rw [Finset.sum_div]
  simp_rw [Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro n _
  exact hatom n

private theorem sum_Icc_one_eq_range_succ (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n) = ∑ n ∈ range N, f (n + 1) := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 N 1]
  rfl

/-- The order-`(m+1)` coefficient energy is Route L's order-`(m+1+δ)` source. -/
theorem orderGammaHankelEnergy_eq_routeL (m N : ℕ) (δ : ℝ) :
    finiteGammaHankelEnergy (orderShiftedCoefficient m) N (2 * m + 1 + δ) =
      Real.Gamma (2 * m + 1 + δ) * finiteGeneralReciprocalEnergy (m + 1 + δ) δ N := by
  unfold finiteGammaHankelEnergy finiteGeneralReciprocalEnergy
  congr 1
  rw [sum_Icc_one_eq_range_succ]
  apply sum_congr rfl
  intro a _
  rw [sum_Icc_one_eq_range_succ]
  apply sum_congr rfl
  intro b _
  unfold generalReciprocalMomentKernel orderShiftedCoefficient shiftedMobiusRealCoefficient
    mobiusRealCoefficient
  rw [show (m : ℝ) + 1 + δ - 1 - δ = ((m : ℕ) : ℝ) by ring, Real.rpow_natCast,
    show 2 * ((m : ℝ) + 1 + δ) - 1 - δ = 2 * m + 1 + δ by ring]
  push_cast
  rw [show (a : ℝ) + 1 + ((b : ℝ) + 1) = (a : ℝ) + b + 2 by ring, mul_pow]
  ring

/-- **Identity (1).**  `B_{m+1+δ,δ}(N) = 2^{1+δ-2m} Σ_k C(2m+δ+k,k) (Δ₂^m b_k)²`. -/
theorem routeLOrderEnergy_eq_stepTwoDifference (m N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    finiteGeneralReciprocalEnergy (m + 1 + δ) δ N =
      2 ^ (1 + δ - 2 * m) * ∑' k : ℕ, binomialWeight (2 * m + 1 + δ) k *
        stepTwoDifference m (packet N (1 + δ)) k ^ 2 := by
  have hr : (0 : ℝ) < 2 * m + 1 + δ := by positivity
  have hg : Real.Gamma (2 * m + 1 + δ) ≠ 0 := (Real.Gamma_pos_of_pos hr).ne'
  apply mul_left_cancel₀ hg
  rw [← orderGammaHankelEnergy_eq_routeL, finiteGammaHankelEnergy_packetExpansion]
  simp_rw [orderPacket_eq_stepTwoDifference, div_pow]
  have hsplit : ∀ k : ℕ, binomialWeight (2 * m + 1 + δ) k *
      (stepTwoDifference m (packet N (1 + δ)) k ^ 2 / (4 ^ m) ^ 2) =
        (((4 : ℝ) ^ m) ^ 2)⁻¹ * (binomialWeight (2 * m + 1 + δ) k *
          stepTwoDifference m (packet N (1 + δ)) k ^ 2) := fun k => by ring
  simp_rw [hsplit]
  rw [tsum_mul_left]
  have h2 : (2 : ℝ) ^ (2 * (m : ℝ) + 1 + δ) =
      2 ^ (1 + δ - 2 * m) * ((4 : ℝ) ^ m) ^ 2 := by
    rw [show 2 * (m : ℝ) + 1 + δ = (1 + δ - 2 * m) + ((4 * m : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add (by norm_num), Real.rpow_natCast]
    rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  rw [h2]
  have h4 : ((4 : ℝ) ^ m) ^ 2 ≠ 0 := by positivity
  field_simp

/-- Every summand of identity (1) is nonnegative. -/
theorem stepTwoEnergyTerm_nonneg (m N k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ binomialWeight (2 * m + 1 + δ) k * stepTwoDifference m (packet N (1 + δ)) k ^ 2 :=
  mul_nonneg (binomialWeight_nonneg (by positivity) k) (sq_nonneg _)

/-- **Identity (2).**  The cubic source is `2^{δ-3} Σ_k C(4+δ+k,k) (b_k - 2b_{k+2} + b_{k+4})²`. -/
theorem routeLCubicEnergy_eq_stepTwo (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    finiteGeneralReciprocalEnergy (3 + δ) δ N =
      2 ^ (δ - 3) * ∑' k : ℕ, binomialWeight (5 + δ) k *
        (packet N (1 + δ) k - 2 * packet N (1 + δ) (k + 2) + packet N (1 + δ) (k + 4)) ^ 2 := by
  have h := routeLOrderEnergy_eq_stepTwoDifference 2 N hδ
  simp_rw [stepTwoDifference_two] at h
  norm_num at h
  rw [h, show (1 : ℝ) + δ - 4 = δ - 3 by ring]

/-- The one-atom value: at cutoff one the cubic source is the `(1,1)` kernel `2^{-5-δ}`. -/
theorem routeLCubicEnergy_one (δ : ℝ) :
    finiteGeneralReciprocalEnergy (3 + δ) δ 1 = 2 ^ (-(5 + δ)) := by
  unfold finiteGeneralReciprocalEnergy generalReciprocalMomentKernel mobiusRealCoefficient
  simp only [Finset.Icc_self, Finset.sum_singleton, ArithmeticFunction.moebius_apply_one]
  norm_num
  rw [show 2 * (3 + δ) - 1 - δ = 5 + δ by ring, show -δ + -5 = -(5 + δ) by ring,
    Real.rpow_neg (by norm_num)]

/-- The order-one packets at cutoff one: `b_0 = 2^{-1-δ}` and `b_k = 0` for `k > 0`. -/
theorem packet_one (δ : ℝ) (k : ℕ) :
    packet 1 (1 + δ) k = if k = 0 then 2 ^ (-(1 + δ)) else 0 := by
  unfold packet coefficient weight node shiftedMobiusRealCoefficient
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · simp [hk.ne', zero_pow hk.ne']

/-- A bounded return of the weighted step-two packet norm, on shifts cofinal at zero,
implies RH. -/
theorem riemannHypothesis_of_stepTwoPacketFrequentlyBounded
    (h : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 2 * ε ∧ ∃ C : ℝ,
      ∃ᶠ N : ℕ in Filter.atTop, 2 ^ (δ - 3) * ∑' k : ℕ, binomialWeight (5 + δ) k *
        (packet N (1 + δ) k - 2 * packet N (1 + δ) (k + 2) + packet N (1 + δ) (k + 4)) ^ 2
          ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_routeLCofinalCubicEnergyFrequentlyBounded
  intro ε hε
  obtain ⟨δ, hδ, hδε, C, hC⟩ := h ε hε
  refine ⟨δ, hδ, hδε, C, hC.mono fun N hN => ?_⟩
  rwa [routeLCubicEnergy_eq_stepTwo N hδ.le]

end RHTower.DiscretePacket
