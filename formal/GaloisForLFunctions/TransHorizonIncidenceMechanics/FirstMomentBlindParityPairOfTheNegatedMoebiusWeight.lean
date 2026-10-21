import GaloisForLFunctions.TransHorizonIncidenceMechanics.FirstPronicMomentOrdersPositivePairs

/-!
# A parity pair that the first pronic moment cannot see

Negate the damped Möbius weight and restore its mean: `c_b = 2ρ_ε δ₁ − μ(d)d^{-ε}`. Then
`W_{c_b}(1) = ρ_ε` and `W_{c_b}(e) = −w_ε(e)` for `e ≥ 2`, while the parity twin has
`W_{c'}(e) = μ(e) w_ε(e)`. On a prime `μ(p) = −1`, and on the higher prime powers `w_ε` vanishes, so
the two weights have **the same Ramanujan coefficient at every prime power** — hence, by the
first-moment law, the same first pronic moment `−Σ_e Λ(e) W(e)` — and the same amplitude at every
modulus. Since `A_{c_b} = −A_{μd^{-ε}}`, the receiver of `c_b` is the Möbius receiver: bounded at half
damping, while the twin's diverges.

This realises the equality case of the first-moment ordering: the parity of the pair lives entirely
on the composite moduli. At `e = pq` the signs are opposite, `W_{c_b}(pq) < 0 < W_{c'}(pq)`; the first
observable that can see the pair is supported on `ω(e) ≥ 2` (the weight `Λ ⋆ Λ`).
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- The unit mass `δ₁`. -/
def unitMass (d : ℕ) : ℝ := if d = 1 then 1 else 0

theorem weightRamanujanCoeff_unitMass (e : ℕ) :
    weightRamanujanCoeff unitMass e = if e = 1 then 1 else 0 := by
  unfold weightRamanujanCoeff unitMass
  split_ifs with he
  · subst he
    rw [tsum_eq_single 1 fun k hk => by simp [hk]]
    simp
  · have : ∀ k : ℕ, e * k ≠ 1 := fun k hk => he (Nat.eq_one_of_mul_eq_one_right hk)
    simp [this]

theorem summable_unitMass_mul (e : ℕ) :
    Summable (fun k : ℕ => unitMass (e * k) / ((e * k : ℕ) : ℝ)) := by
  refine summable_of_ne_finset_zero (s := {1}) fun k hk => ?_
  have hk1 : k ≠ 1 := by simpa using hk
  have : e * k ≠ 1 := fun h => hk1 (Nat.eq_one_of_mul_eq_one_left h)
  simp [unitMass, this]

/-- The negated damped Möbius weight with restored mean, `2ρ_ε δ₁ − μ(d)d^{-ε}`. -/
def negatedMoebiusWeight (ε : ℝ) (d : ℕ) : ℝ :=
  2 * dampedDensity ε * unitMass d - pmPowerDampedRealWeight ε d

theorem weightRamanujanCoeff_negatedMoebius {ε : ℝ} (hε : 0 < ε) {e : ℕ} (he : 0 < e) :
    weightRamanujanCoeff (negatedMoebiusWeight ε) e =
      2 * dampedDensity ε * (if e = 1 then 1 else 0) - dampedRamanujanCoeff ε e := by
  have hμ := hasSum_dampedRamanujanCoeff hε he
  unfold weightRamanujanCoeff negatedMoebiusWeight
  simp_rw [sub_div, mul_div_assoc]
  rw [((summable_unitMass_mul e).mul_left _).tsum_sub hμ.summable, tsum_mul_left, hμ.tsum_eq]
  congr 2
  exact weightRamanujanCoeff_unitMass e

theorem hasSum_negatedMoebiusWeight_div {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun d : ℕ => negatedMoebiusWeight ε d / d) (dampedDensity ε) := by
  have hu : HasSum (fun d : ℕ => unitMass d / d) 1 := by
    have h := hasSum_ite_eq (1 : ℕ) (1 : ℝ)
    refine h.congr_fun fun d => ?_
    by_cases hd : d = 1 <;> simp [unitMass, hd]
  have h := (hu.mul_left (2 * dampedDensity ε)).sub (hasSum_pmPowerDampedRealWeight_div hε)
  rw [show 2 * dampedDensity ε * 1 - dampedDensity ε = dampedDensity ε by ring] at h
  refine h.congr_fun fun d => ?_
  simp only [negatedMoebiusWeight]; ring

/-- `A_{c_b} = −A_{μd^{-ε}}`: the negated weight has the Möbius receiver. -/
theorem weightCenteredPrefix_negatedMoebius (ε : ℝ) (n : ℕ) :
    weightCenteredPrefix (negatedMoebiusWeight ε) (dampedDensity ε) n =
      -weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n := by
  have hu : ∀ j ∈ Icc 1 n, ∑ d ∈ j.divisors, unitMass d = 1 := fun j hj => by
    have hj : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
    rw [Finset.sum_eq_single 1 (fun d _ hd => by simp [unitMass, hd]) (fun h => absurd
      (Nat.one_mem_divisors.mpr hj) h)]
    simp [unitMass]
  unfold weightCenteredPrefix negatedMoebiusWeight
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl hu]
  simp only [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one]
  ring

theorem weightPronicEnergy_negatedMoebius (ε : ℝ) (T : ℕ) :
    weightPronicEnergy (negatedMoebiusWeight ε) (dampedDensity ε) T =
      weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T := by
  unfold weightPronicEnergy
  simp_rw [weightCenteredPrefix_negatedMoebius, neg_sq]

/-- The two weights agree at every prime power: `W_{c_b}(e) = W_{c'}(e)` whenever `Λ(e) ≠ 0`. -/
theorem weightRamanujanCoeff_negatedMoebius_eq_twin {ε : ℝ} (hε : 0 < ε) {e : ℕ}
    (he : IsPrimePow e) :
    weightRamanujanCoeff (negatedMoebiusWeight ε) e = weightRamanujanCoeff (parityTwinWeight ε) e := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp he
  have hpk : p ^ k ≠ 1 := (Nat.one_lt_pow hk.ne' hp.one_lt).ne'
  rw [weightRamanujanCoeff_negatedMoebius hε (pow_pos hp.pos k), if_neg hpk,
    weightRamanujanCoeff_parityTwin hε, ArithmeticFunction.moebius_apply_prime_pow hp hk.ne']
  split_ifs with hk1
  · push_cast; ring
  · rw [dampedRamanujanCoeff_eq_closed hε, ArithmeticFunction.moebius_apply_prime_pow hp hk.ne',
      if_neg hk1]
    simp

/-- **Identical amplitudes.** `|W_{c_b}(e)| = |W_{c'}(e)|` at every modulus. -/
theorem abs_weightRamanujanCoeff_negatedMoebius {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    |weightRamanujanCoeff (negatedMoebiusWeight ε) e| =
      |weightRamanujanCoeff (parityTwinWeight ε) e| := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp [weightRamanujanCoeff]
  rw [weightRamanujanCoeff_negatedMoebius hε he, abs_weightRamanujanCoeff_parityTwin hε he,
    weightRamanujanCoeff_pmPowerDamped hε he]
  split_ifs with h1
  · subst h1
    rw [dampedRamanujanCoeff_one hε, show 2 * dampedDensity ε * 1 - dampedDensity ε =
      dampedDensity ε by ring]
  · rw [mul_zero, zero_sub, abs_neg]

theorem negatedMoebiusWeight_mem_dampedClass {ε : ℝ} (hε : 0 < ε) :
    DampedClass (2 * dampedDensity ε + 1) ε (negatedMoebiusWeight ε) := fun d => by
  have hρ : 0 < dampedDensity ε := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  have hμ : |moebiusReal d| ≤ 1 := by
    unfold moebiusReal
    rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]
  have hp : 0 ≤ (d : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  unfold negatedMoebiusWeight unitMass pmPowerDampedRealWeight
  split_ifs with h1
  · subst h1
    simp only [Nat.cast_one, Real.one_rpow, mul_one]
    calc |2 * dampedDensity ε - moebiusReal 1| ≤ |2 * dampedDensity ε| + |moebiusReal 1| :=
          abs_sub _ _
      _ ≤ 2 * dampedDensity ε + 1 := by rw [abs_of_pos (by linarith)]; linarith
  · rw [mul_zero, zero_sub, abs_neg, abs_mul, abs_of_nonneg hp]
    calc |moebiusReal d| * (d : ℝ) ^ (-ε) ≤ 1 * (d : ℝ) ^ (-ε) := mul_le_mul_of_nonneg_right hμ hp
      _ ≤ (2 * dampedDensity ε + 1) * (d : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (by linarith) hp

theorem parityTwinWeight_mem_dampedClass {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, DampedClass K (ε / 2) (parityTwinWeight ε) := by
  obtain ⟨C, hC0, hC⟩ := exists_parityTwinShape_le hε
  have hU := parityTwinCoprimeMass_one_pos hε
  have hρ : 0 < dampedDensity ε := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  refine ⟨dampedDensity ε / parityTwinCoprimeMass ε 1 * C, fun d => ?_⟩
  rw [abs_of_nonneg (parityTwinWeight_nonneg hε d)]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [parityTwinWeight, Real.zero_rpow (show -(ε / 2) ≠ 0 by linarith)]
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hdiv := parityTwinWeight_div ε d
    have hw : parityTwinWeight ε d = d * (dampedDensity ε / parityTwinCoprimeMass ε 1 *
        parityTwinShape ε d) := by
      rw [← hdiv]; field_simp
    rw [hw]
    have hs := hC d hd
    have hpow : (d : ℝ) * (d : ℝ) ^ (-1 - ε / 2) = (d : ℝ) ^ (-(ε / 2)) := by
      rw [mul_comm, ← Real.rpow_add_one hd0.ne']; ring_nf
    calc (d : ℝ) * (dampedDensity ε / parityTwinCoprimeMass ε 1 * parityTwinShape ε d) ≤
          (d : ℝ) * (dampedDensity ε / parityTwinCoprimeMass ε 1 * (C * (d : ℝ) ^ (-1 - ε / 2))) := by
          gcongr
      _ = dampedDensity ε / parityTwinCoprimeMass ε 1 * C * ((d : ℝ) * (d : ℝ) ^ (-1 - ε / 2)) := by
          ring
      _ = _ := by rw [hpow]

/-- **The first-moment-blind parity pair.** For `0 < ε ≤ 1/2`, the negated Möbius weight
`2ρ_ε δ₁ − μ(d)d^{-ε}` and the parity twin `c'_ε` have equal Ramanujan amplitudes at every modulus,
equal coefficients at every prime power, equal first pronic moments and opposite signs at every
`e = pq`; the first has the Möbius receiver, the second a divergent one. -/
theorem firstMomentBlind_parityPair {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ e : ℕ, |weightRamanujanCoeff (negatedMoebiusWeight ε) e| =
        |weightRamanujanCoeff (parityTwinWeight ε) e|) ∧
    (∀ e : ℕ, IsPrimePow e → weightRamanujanCoeff (negatedMoebiusWeight ε) e =
        weightRamanujanCoeff (parityTwinWeight ε) e) ∧
    firstPronicMoment (negatedMoebiusWeight ε) = firstPronicMoment (parityTwinWeight ε) ∧
    (∀ p r : ℕ, p.Prime → r.Prime → p ≠ r →
        weightRamanujanCoeff (negatedMoebiusWeight ε) (p * r) < 0 ∧
          0 < weightRamanujanCoeff (parityTwinWeight ε) (p * r)) ∧
    (∀ T : ℕ, weightPronicEnergy (negatedMoebiusWeight ε) (dampedDensity ε) T =
        weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T) ∧
    Tendsto (fun T => weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T) atTop atTop := by
  refine ⟨abs_weightRamanujanCoeff_negatedMoebius hε, fun e he =>
    weightRamanujanCoeff_negatedMoebius_eq_twin hε he, ?_, ?_, weightPronicEnergy_negatedMoebius ε,
    tendsto_weightPronicEnergy_parityTwin hε hε2⟩
  · obtain ⟨K, hK⟩ := parityTwinWeight_mem_dampedClass hε
    unfold firstPronicMoment
    rw [(hasSum_firstPronicMoment hε (negatedMoebiusWeight_mem_dampedClass hε)).tsum_eq,
      (hasSum_firstPronicMoment (by linarith : 0 < ε / 2) hK).tsum_eq]
    congr 1
    refine tsum_congr fun e => ?_
    by_cases he : IsPrimePow e
    · rw [weightRamanujanCoeff_negatedMoebius_eq_twin hε he]
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr he, zero_mul, zero_mul]
  · intro p r hp hr hne
    have hcop : Nat.gcd p r = 1 := (Nat.coprime_primes hp hr).mpr hne
    have hμ : (ArithmeticFunction.moebius (p * r) : ℝ) = 1 := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_prime hr]
      norm_num
    have hpr : 0 < p * r := Nat.mul_pos hp.pos hr.pos
    have hpr1 : p * r ≠ 1 := by
      have := Nat.mul_le_mul hp.two_le hr.two_le; omega
    have hD := RHTower.pmPowerDampedRamanujanDenominator_pos hε (p * r)
    have hρ : 0 < dampedDensity ε := RHTower.pmPowerDampedDivisorDensity_re_pos hε
    have hw : 0 < dampedRamanujanCoeff ε (p * r) := by
      rw [dampedRamanujanCoeff_eq_closed hε, hμ, mul_one]; positivity
    refine ⟨?_, ?_⟩
    · rw [weightRamanujanCoeff_negatedMoebius hε hpr, if_neg hpr1]; linarith
    · rw [weightRamanujanCoeff_parityTwin hε, hμ, one_mul]; exact hw

/-- **At half damping the first-moment-blind pair is unconditional**: `2ρδ₁ − μ(d)d^{-1/2}` has
bounded receiver. -/
theorem receiverBounded_negatedMoebius_half : ReceiverBounded (negatedMoebiusWeight (1 / 2)) := by
  obtain ⟨B, hB⟩ := receiverBounded_pmPowerDamped_half
  refine ⟨B, fun T => ?_⟩
  rw [(hasSum_negatedMoebiusWeight_div (by norm_num)).tsum_eq, weightPronicEnergy_negatedMoebius]
  have := hB T
  rwa [(hasSum_pmPowerDampedRealWeight_div (by norm_num : (0 : ℝ) < 1 / 2)).tsum_eq] at this

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
