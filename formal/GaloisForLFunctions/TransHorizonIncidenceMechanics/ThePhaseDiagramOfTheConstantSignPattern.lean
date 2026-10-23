import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheQuarterLawOfTheConstantSignPatternOnTheFullRange
import GaloisForLFunctions.TransHorizonIncidenceMechanics.APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusAndLiouvilleReceiversAreEquivalent
import GaloisForLFunctions.TransHorizonIncidenceMechanics.UnsignedMajorantsAndSignBlindDataStopAtHalfDamping

/-!
# The phase diagram of the constant-sign pattern

For `z ∈ [−1, 1]` and `ε > 0` let `c_{z,ε}(d) = z^{Ω(d)} d^{-ε}`. Its receiver is decided on the whole
`(z, ε)` plane (`receiverBounded_constantSign_damped_iff`):

`c_{z,ε}` is paid  ⟺  `ε > 1/2`, or `ε = 1/2` and `z < 1/2`, or `z = 0`, or `z = −1` and the
damped Möbius weight `μ(d) d^{-ε}` is paid.

* Above half damping one constant pays the whole damped class.
* At half damping the quarter law of the constant-sign pattern: paid iff `z < 1/2`.
* Below half damping the prime mean of `z^{Ω}` is `ν = z`
  (`|Σ_p z p^{-w} − z log(1/(w − 1))| ≤ |z| (2S + log(3/2))`), and a paid weight has `ν ∈ {0, −1}`
  (`not_receiverBounded_of_primeMean`); `z = 0` is the unit mass `δ_1`, whose centred prefix vanishes
  identically, and `z = −1` is the Liouville weight, paid exactly when the Möbius weight is.

So below half damping the only nontrivial point of the diagram is the Liouville line `z = −1`, whose
admissible dampings are those of the Möbius receiver, i.e. the zero width `Θ − 1/2`.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- At `z = −1` the constant-sign pattern is the Liouville function. -/
theorem constantSignHom_neg_one (n : ℕ) : constantSignHom (-1) n = RHTower.liouvilleR n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [constantSignHom, RHTower.liouvilleR]
  · simp [constantSignHom, RHTower.liouvilleR, hn, ArithmeticFunction.liouville_apply hn]

/-- At `z = 0` the constant-sign pattern is the unit mass at `1`. -/
theorem constantSignHom_zero_apply (n : ℕ) :
    constantSignHom 0 n = if n = 1 then 1 else 0 := by
  simp only [constantSignHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [if_neg hn]
  by_cases h1 : n = 1
  · subst h1; simp
  rw [if_neg h1, zero_pow]
  intro h
  rcases ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp h with h' | h'
  · exact hn h'
  · exact h1 h'

/-- **`z = 0` is paid at every damping**: the weight is `δ_1` and its centred prefix vanishes. -/
theorem receiverBounded_constantSign_zero (ε : ℝ) :
    ReceiverBounded (dampedSignWeight (constantSignHom 0) ε) := by
  have hc : ∀ d : ℕ, dampedSignWeight (constantSignHom 0) ε d = if d = 1 then 1 else 0 := by
    intro d
    simp only [dampedSignWeight, constantSignHom_zero_apply]
    split_ifs with h
    · subst h; simp
    · simp
  have hm : ∑' d : ℕ, dampedSignWeight (constantSignHom 0) ε d / d = 1 := by
    rw [tsum_eq_single 1 fun d hd => by simp [hc, hd]]
    simp [hc]
  refine ⟨0, fun T => ?_⟩
  have hA : ∀ n, weightCenteredPrefix (dampedSignWeight (constantSignHom 0) ε)
      (∑' d : ℕ, dampedSignWeight (constantSignHom 0) ε d / d) n = 0 := by
    intro n
    rw [hm, weightCenteredPrefix]
    have hj : ∀ j ∈ Icc 1 n, ∑ d ∈ j.divisors, dampedSignWeight (constantSignHom 0) ε d = 1 := by
      intro j hj
      simp only [hc]
      rw [Finset.sum_ite_eq' j.divisors 1 (fun _ => (1 : ℝ)), if_pos]
      exact Nat.one_mem_divisors.mpr (by have := (Finset.mem_Icc.mp hj).1; omega)
    rw [Finset.sum_congr rfl hj, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp
  simp [weightPronicEnergy, hA]

/-- **Below half damping only the prime means `0` and `−1` survive**: for `0 < ε < 1/2` and
`z ∈ [−1, 1] ∖ {0, −1}` the weight `z^{Ω(d)} d^{-ε}` is unpaid. -/
theorem not_receiverBounded_constantSign_lt_half {z ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hz : -1 ≤ z) (hz1 : z ≤ 1) (h0 : z ≠ 0) (hm1 : z ≠ -1) :
    ¬ ReceiverBounded (dampedSignWeight (constantSignHom z) ε) := by
  have hzabs : |z| ≤ 1 := abs_le.mpr ⟨hz, hz1⟩
  set S₂ := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)
  refine not_receiverBounded_of_primeMean hε hε2 (constantSignHom z)
    (fun p hp => by rw [constantSignHom_prime z hp]; exact hzabs) (ν := z)
    (B := |z| * (2 * S₂ + Real.log (3 / 2))) (fun n hn => ?_) fun w hw hw2 => ?_
  · -- `z = −n` forces `n ∈ {0, 1}`, both excluded
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · exact h0 (by simpa using hn)
      · exact hm1 (by simpa using hn)
    · have : (2 : ℝ) ≤ n := by exact_mod_cast h
      linarith
  · have hsum : ∑' p : Nat.Primes, constantSignHom z p * ((p : ℕ) : ℝ) ^ (-w) =
        z * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-w) := by
      rw [← tsum_mul_left]
      exact tsum_congr fun p => by rw [constantSignHom_prime z p.2]
    rw [hsum, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_tsum_primes_rpow_sub_log_le hw hw2) (abs_nonneg z)

/-- At `z = −1` the damped constant-sign weight is the damped Liouville weight. -/
theorem dampedSignWeight_constantSignHom_neg_one (ε : ℝ) :
    dampedSignWeight (constantSignHom (-1)) ε = dampedSignWeight RHTower.liouvilleR ε := by
  funext d
  simp only [dampedSignWeight, constantSignHom_neg_one]

/-- **The phase diagram of the constant-sign pattern.** For `z ∈ [−1, 1]` and `ε > 0`, the weight
`z^{Ω(d)} d^{-ε}` is paid exactly when `ε > 1/2`, or `ε = 1/2` and `z < 1/2`, or `z = 0`, or `z = −1`
and the damped Möbius weight `μ(d) d^{-ε}` is paid. -/
theorem receiverBounded_constantSign_damped_iff {z ε : ℝ} (hz : -1 ≤ z) (hz1 : z ≤ 1)
    (hε : 0 < ε) :
    ReceiverBounded (dampedSignWeight (constantSignHom z) ε) ↔
      1 / 2 < ε ∨ (ε = 1 / 2 ∧ z < 1 / 2) ∨ z = 0 ∨
        (z = -1 ∧ ReceiverBounded (pmPowerDampedRealWeight ε)) := by
  have hzabs : |z| ≤ 1 := abs_le.mpr ⟨hz, hz1⟩
  constructor
  · intro hpaid
    rcases lt_trichotomy ε (1 / 2) with hlt | heq | hgt
    · by_cases h0 : z = 0
      · exact Or.inr (Or.inr (Or.inl h0))
      by_cases hm1 : z = -1
      · subst hm1
        refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
        rw [dampedSignWeight_constantSignHom_neg_one] at hpaid
        exact (receiverBounded_moebius_iff_liouville hε).mpr hpaid
      · exact absurd hpaid (not_receiverBounded_constantSign_lt_half hε hlt hz hz1 h0 hm1)
    · subst heq
      exact Or.inr (Or.inl ⟨rfl, (receiverBounded_constantSign_iff_full hz hz1).mp hpaid⟩)
    · exact Or.inl hgt
  · rintro (hgt | ⟨rfl, hzh⟩ | rfl | ⟨rfl, hM⟩)
    · obtain ⟨E, hE⟩ := (uniformReceiverBound_iff_half_lt (K := 1) one_pos hε).mpr hgt
      refine ⟨E, hE _ fun d => ?_⟩
      rw [dampedSignWeight, one_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _)
        (abs_constantSignHom_le hzabs d)
    · exact (receiverBounded_constantSign_iff_full hz hz1).mpr hzh
    · exact receiverBounded_constantSign_zero ε
    · rw [dampedSignWeight_constantSignHom_neg_one]
      exact (receiverBounded_moebius_iff_liouville hε).mp hM

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
