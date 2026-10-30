import GaloisForLFunctions.RHTower.DirichletCharacterUniformSums
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PrimeResidueSourcesHaveQuantitativeLogDecay

/-!
# Actual residue-prime sources on growing conductor families

A single source horizon controls every signed residue pattern over all moduli
bounded by a fixed power of its logarithm. Reduced classes come from the actual
character sums. Nonunit classes and proper prime powers remain in the estimate.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory _root_.RHTower

private theorem primeClassKappa_indicator {q : ℕ} [NeZero q] (a : ZMod q) :
    primeClassKappa q (primeResidueIndicator a) =
      if IsUnit a then 1 / (q.totient : ℝ) else 0 := by
  classical
  unfold primeClassKappa
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [if_pos u.isUnit]
    congr 1
    calc
      _ = primeResidueIndicator (u : ZMod q) (u : ZMod q) := by
        apply sum_eq_single u
        · intro v _ hv
          exact if_neg (fun h => hv (Units.val_injective h))
        · intro hu
          exact False.elim (hu (mem_univ u))
      _ = 1 := if_pos rfl
  · rw [if_neg ha]
    have hz : ∀ u : (ZMod q)ˣ, primeResidueIndicator a u = 0 := by
      intro u
      apply if_neg
      intro h
      exact ha (h ▸ u.isUnit)
    simp only [hz, sum_const_zero, zero_div]

private theorem abs_residueMangoldtReading_sub_theta {q : ℕ} (a : ZMod q) (X : ℝ) :
    |residueMangoldtReading q (primeResidueIndicator a) X - primeProgressionTheta q a X| ≤
      Chebyshev.psi X - Chebyshev.theta X := by
  classical
  have hset : Icc 1 ⌊X⌋₊ = Ioc 0 ⌊X⌋₊ := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [residueMangoldtReading, primeProgressionTheta, hset, sum_filter, sum_filter,
    ← sum_sub_distrib, Chebyshev.psi_sub_theta_eq_sum_not_prime, sum_filter]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n _
  by_cases hp : n.Prime <;> by_cases ha : (n : ZMod q) = a
  · simp only [primeResidueIndicator, hp, ha, not_true_eq_false, ↓reduceIte, one_mul,
      ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self, abs_zero, le_refl]
  · simp only [primeResidueIndicator, hp, ha, not_true_eq_false, ↓reduceIte,
      zero_mul, sub_zero, abs_zero, le_refl]
  · simp only [primeResidueIndicator, hp, ha, not_false_eq_true, ↓reduceIte, one_mul, sub_zero,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, le_refl]
  · simp only [primeResidueIndicator, hp, ha, not_false_eq_true, ↓reduceIte,
      zero_mul, sub_zero, abs_zero]
    exact ArithmeticFunction.vonMangoldt_nonneg

private theorem primeProgressionTheta_nonunit_le {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : ¬ IsUnit a) (X : ℝ) : primeProgressionTheta q a X ≤ Chebyshev.theta q := by
  classical
  have hsub : ((Ioc 0 ⌊X⌋₊).filter Nat.Prime).filter (fun p : ℕ => (p : ZMod q) = a) ⊆
      (Ioc 0 q).filter Nat.Prime := by
    intro p hp
    obtain ⟨hp, heq⟩ := mem_filter.mp hp
    have hprime := (mem_filter.mp hp).2
    have hn : ¬ IsUnit (p : ZMod q) := fun h => ha (heq ▸ h)
    have hd : p ∣ q := hprime.dvd_iff_not_coprime.mpr
      (fun h => hn ((ZMod.isUnit_iff_coprime p q).mpr h))
    exact mem_filter.mpr ⟨mem_Ioc.mpr
      ⟨hprime.pos, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hd⟩, hprime⟩
  unfold primeProgressionTheta
  calc
    _ ≤ ∑ p ∈ (Ioc 0 q).filter Nat.Prime, Real.log p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
        Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le))
    _ = _ := by simp only [Chebyshev.theta, Nat.floor_natCast]

private theorem primeProgressionTheta_nonneg (q : ℕ) (a : ZMod q) (X : ℝ) :
    0 ≤ primeProgressionTheta q a X := by
  unfold primeProgressionTheta
  exact sum_nonneg fun p hp => Real.log_nonneg
    (by exact_mod_cast (mem_filter.mp (mem_filter.mp hp).1).2.one_le)

/-- One physical rate controls all residue indicators, including nonunit
prime powers, for every modulus in the growing family. -/
theorem exists_conductor_uniform_residueMangoldtReading_indicator_power_log
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ a C Y : ℝ, 0 < a ∧ 0 ≤ C ∧ 3 ≤ Y ∧
      ∀ X : ℝ, Y ≤ X → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log X ^ A →
        ∀ r : ZMod q,
          |residueMangoldtReading q (primeResidueIndicator r) X -
              primeClassKappa q (primeResidueIndicator r) * X| ≤
            C * X * Real.exp (-(a * Real.log X ^ ((1 : ℝ) / 10))) := by
  obtain ⟨a, C, Y, ha, hC, hY, htheta⟩ := exists_conductor_uniform_primeProgressionTheta_power_log hA
  obtain ⟨Z, hZ, hproper⟩ := sqrt_log_le_power_log_decay ha
  obtain ⟨D, V, hD, hV, hmodulus⟩ := exists_conductor_theta_power_log A ha
  let Y₀ := max Y (max Z V)
  refine ⟨a, C + D + 1, Y₀, ha, by positivity, hY.trans (le_max_left _ _), ?_⟩
  intro X hX q _ hq r
  have hXY : Y ≤ X := (le_max_left _ _).trans hX
  have hXZ : Z ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hXV : V ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hX3 : 3 ≤ X := hY.trans hXY
  have hX0 : 0 < X := by linarith only [hX3]
  let R := X * Real.exp (-(a * Real.log X ^ ((1 : ℝ) / 10)))
  have hR : 0 ≤ R := mul_nonneg hX0.le (Real.exp_nonneg _)
  have hproperR : Chebyshev.psi X - Chebyshev.theta X ≤ R :=
    (Chebyshev.psi_sub_theta_le (by linarith only [hX3])).trans (hproper X hXZ)
  have hmain : |primeProgressionTheta q r X - primeClassKappa q (primeResidueIndicator r) * X| ≤
      (C + D) * R := by
    rw [primeClassKappa_indicator]
    by_cases hr : IsUnit r
    · rw [if_pos hr]
      have ht := htheta X hXY q hq r hr
      rw [show (1 / (q.totient : ℝ)) * X = X / q.totient from by ring]
      have hCR := mul_le_mul_of_nonneg_right (show C ≤ C + D by linarith only [hD]) hR
      exact ht.trans (by simpa only [R, mul_assoc] using hCR)
    · rw [if_neg hr, zero_mul, sub_zero, abs_of_nonneg (primeProgressionTheta_nonneg q r X)]
      have hDR := hmodulus X hXV q hq
      have hmore := mul_le_mul_of_nonneg_right (show D ≤ C + D by linarith only [hC]) hR
      exact (primeProgressionTheta_nonunit_le hr X).trans
        (hDR.trans (by simpa only [R, mul_assoc] using hmore))
  have he := (abs_residueMangoldtReading_sub_theta r X).trans hproperR
  have htri := abs_sub_le
    (residueMangoldtReading q (primeResidueIndicator r) X) (primeProgressionTheta q r X)
    (primeClassKappa q (primeResidueIndicator r) * X)
  change _ ≤ (C + D + 1) * X * Real.exp (-(a * Real.log X ^ ((1 : ℝ) / 10)))
  dsimp only [R] at he hmain
  nlinarith only [htri, he, hmain]

private theorem tendsto_powerLogError_mul_log_pow (C : ℝ) {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun X : ℝ => C * (Real.log X) ^ k *
      Real.exp (-(a * Real.log X ^ ((1 : ℝ) / 10)))) atTop (𝓝 0) := by
  have ht : Tendsto (fun X : ℝ => (Real.log X) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hd := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * k : ℝ) a ha).comp ht
  have hb : Tendsto (fun X : ℝ => C * ((Real.log X) ^ ((1 : ℝ) / 10)) ^ (10 * k : ℝ) *
      Real.exp (-(a * (Real.log X) ^ ((1 : ℝ) / 10)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_assoc, mul_zero, neg_mul] using hd.const_mul C
  apply hb.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with X hX
  rw [← Real.rpow_mul hX.le]
  simp only [show (1 : ℝ) / 10 * (10 * k : ℝ) = (k : ℝ) by ring, Real.rpow_natCast]

private theorem residueMangoldtReading_eq_indicator_sum {q : ℕ} [NeZero q]
    (F : ZMod q → ℝ) (X : ℝ) :
    residueMangoldtReading q F X =
      ∑ r : ZMod q, F r * residueMangoldtReading q (primeResidueIndicator r) X := by
  symm
  simp only [residueMangoldtReading, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun n _ => ?_
  simp only [primeResidueIndicator, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  rw [sum_ite_eq, if_pos (mem_univ _)]

/-- Every inverse-logarithmic source rate has one horizon simultaneously for
all allowed moduli, all larger endpoints, and every signed residue pattern. -/
theorem eventually_conductor_uniform_residueMangoldtReading_log_error
    {A : ℝ} (hA : 0 ≤ A) (k : ℕ) :
    ∀ᶠ Y : ℝ in atTop, 1 < Real.log Y ∧ ∀ X : ℝ, Y ≤ X →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log Y ^ A → ∀ F : ZMod q → ℝ,
        |residueMangoldtReading q F X - primeClassKappa q F * X| ≤
          (X / (Real.log Y) ^ k) * ∑ r : ZMod q, |F r| := by
  obtain ⟨a, C, Z, ha, hC, hZ, hbound⟩ :=
    exists_conductor_uniform_residueMangoldtReading_indicator_power_log hA
  filter_upwards [(tendsto_powerLogError_mul_log_pow C ha k).eventually_le_const
    (by norm_num : (0 : ℝ) < 1), Real.tendsto_log_atTop.eventually_gt_atTop 1,
    eventually_ge_atTop Z] with Y hsmall hlog hYZ
  refine ⟨hlog, ?_⟩
  intro X hYX q _ hq F
  have hY3 : 3 ≤ Y := hZ.trans hYZ
  have hY0 : 0 < Y := by linarith only [hY3]
  have hX0 : 0 ≤ X := (hY0.trans_le hYX).le
  have hlog0 : 0 < Real.log Y := by linarith only [hlog]
  have hmono : Real.exp (-(a * Real.log X ^ ((1 : ℝ) / 10))) ≤
      Real.exp (-(a * Real.log Y ^ ((1 : ℝ) / 10))) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hlog0.le (Real.log_le_log hY0 hYX) (by norm_num)) ha.le))
  have hqX : (q : ℝ) ≤ Real.log X ^ A := hq.trans
    (Real.rpow_le_rpow hlog0.le (Real.log_le_log hY0 hYX) hA)
  have hsingle (r : ZMod q) :
      |residueMangoldtReading q (primeResidueIndicator r) X -
        primeClassKappa q (primeResidueIndicator r) * X| ≤ X / (Real.log Y) ^ k := by
    have h := (hbound X (hYZ.trans hYX) q hqX r).trans
      (mul_le_mul_of_nonneg_left hmono (mul_nonneg hC hX0))
    have hscaled := mul_le_mul_of_nonneg_left hsmall hX0
    apply h.trans
    apply (le_div_iff₀ (pow_pos hlog0 k)).mpr
    nlinarith only [hscaled]
  have heq : residueMangoldtReading q F X - primeClassKappa q F * X =
      ∑ r : ZMod q, F r * (residueMangoldtReading q (primeResidueIndicator r) X -
        primeClassKappa q (primeResidueIndicator r) * X) := by
    rw [residueMangoldtReading_eq_indicator_sum, primeClassKappa_eq_indicator_sum,
      sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun r _ => by ring
  rw [heq, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro r _
  rw [abs_mul, mul_comm (X / (Real.log Y) ^ k)]
  exact mul_le_mul_of_nonneg_left (hsingle r) (abs_nonneg _)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_conductor_uniform_residueMangoldtReading_indicator_power_log
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_conductor_uniform_residueMangoldtReading_log_error
