import GaloisForLFunctions.RenormalizedIntersectionTheory.ThePositiveDivisorMeanControlsTheSignedPrimitive
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Exact finite prime removal for divisor Dirichlet series

The divisor convolution has Dirichlet series `ζ(s)F(s)`. Absolute convergence
justifies the product, and the Euler product removes finitely many prime factors
without replacing their signs by absolute values.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity

/-- The real Dirichlet coefficient at `1 + σ`, with the zero index suppressed. -/
def realDirichletTerm (ω : ℕ → ℝ) (σ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ω n * (n : ℝ) ^ (-(1 + σ))

/-- Bounded real coefficients give absolute convergence to the right of one. -/
theorem summable_norm_realDirichletTerm {ω : ℕ → ℝ} (hbd : ∀ n, |ω n| ≤ 1)
    {σ : ℝ} (hσ : 0 < σ) : Summable (fun n => ‖realDirichletTerm ω σ n‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (Real.summable_nat_rpow.mpr (show -(1 + σ) < -1 by linarith only [hσ]))
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [realDirichletTerm] using
      (Real.rpow_nonneg (show (0 : ℝ) ≤ 0 from le_rfl) (-(1 + σ)))
  rw [realDirichletTerm, if_neg hn, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hbd n)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

private def contractionDirichletHom {ω : ℕ → ℝ} (h1 : ω 1 = 1)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → ω (m * n) = ω m * ω n) (σ : ℝ) : ℕ →*₀ ℝ where
  toFun := realDirichletTerm ω σ
  map_zero' := by simp [realDirichletTerm]
  map_one' := by simp [realDirichletTerm, h1]
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm, realDirichletTerm]
    by_cases hn : n = 0
    · simp [hn, realDirichletTerm]
    simp only [realDirichletTerm, mul_eq_zero, hm, hn, or_self, if_false]
    rw [hmul m n hm hn, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring

private theorem real_convolution_hasSum {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) :
    HasSum (fun n : ℕ => ∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2)
      ((∑' n, f n) * ∑' n, g n) := by
  have hsum := summable_mul_of_summable_norm hf.norm hg.norm
  have h := (hf.hasSum.mul hg.hasSum hsum).tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  have heq : (fun n : ℕ => ∑' (b : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n}),
      f b.val.1 * g b.val.2) =
      (fun n : ℕ => ∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2) := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [Nat.divisorsAntidiagonal_zero, sum_empty]
      have hz : ∀ b : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {(0 : ℕ)},
          f b.val.1 * g b.val.2 = 0 := by
        rintro ⟨⟨a, b⟩, hab⟩
        have hab' : a * b = 0 := hab
        rcases mul_eq_zero.mp hab' with ha | hb
        · simp only [ha, hf0, zero_mul]
        · simp only [hb, hg0, mul_zero]
      simp only [hz, tsum_zero]
    · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n} =
          (n.divisorsAntidiagonal : Set (ℕ × ℕ)) by ext p; simp [hn]]
      exact Finset.tsum_subtype' n.divisorsAntidiagonal (fun p => f p.1 * g p.2)
  rw [heq] at h
  exact h

/-- The divisor convolution has the product Dirichlet series, with convergence
proved from the coefficient bound. Complete multiplicativity is not required. -/
theorem hasSum_realDivisorDirichletTerm {ω : ℕ → ℝ} (hbd : ∀ n, |ω n| ≤ 1)
    {σ : ℝ} (hσ : 0 < σ) :
    HasSum (realDirichletTerm (signDivisorCount ω) σ)
      ((∑' n, realDirichletTerm ω σ n) * ∑' n, realDirichletTerm (fun _ => 1) σ n) := by
  have hf := (summable_norm_realDirichletTerm hbd hσ).of_norm
  have hg := (summable_norm_realDirichletTerm (ω := fun _ => 1) (fun _ => by norm_num) hσ).of_norm
  have h := real_convolution_hasSum hf hg
    (by simp [realDirichletTerm])
    (by simp [realDirichletTerm])
  have heq : realDirichletTerm (signDivisorCount ω) σ =
      (fun n : ℕ => ∑ p ∈ n.divisorsAntidiagonal,
        realDirichletTerm ω σ p.1 * realDirichletTerm (fun _ => 1) σ p.2) := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [realDirichletTerm]
    rw [realDirichletTerm, if_neg hn, signDivisorCount, sum_mul,
      ← Nat.sum_divisorsAntidiagonal (fun d _ => ω d * (n : ℝ) ^ (-(1 + σ)))]
    refine sum_congr rfl fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
    simp only [realDirichletTerm, if_neg hp1, if_neg hp2, one_mul]
    have hprod : (n : ℝ) = (p.1 : ℝ) * (p.2 : ℝ) := by
      exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1.symm
    rw [hprod, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  rw [← heq] at h
  exact h

/-- Removing finitely many primes multiplies a real completely multiplicative
Dirichlet series by their inverse Euler factors. -/
theorem realDirichletSeries_roughGauge_eq {ω : ℕ → ℝ} (h1 : ω 1 = 1)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → ω (m * n) = ω m * ω n)
    (hbd : ∀ n, |ω n| ≤ 1) {σ : ℝ} (hσ : 0 < σ) (Q : ℕ) :
    (∑' n, realDirichletTerm (roughGauge Q ω) σ n) =
      (∑' n, realDirichletTerm ω σ n) *
        ∏ p ∈ Nat.primesBelow Q, (1 - ω p * (p : ℝ) ^ (-(1 + σ))) := by
  have hr1 : roughGauge Q ω 1 = 1 := by simpa [roughGauge] using h1
  let f := contractionDirichletHom h1 hmul σ
  let r := contractionDirichletHom hr1 (roughGauge_mul hmul Q) σ
  let H := ∏ p ∈ Nat.primesBelow Q, (1 - f p)
  have hf : Summable (fun n => ‖f n‖) := summable_norm_realDirichletTerm hbd hσ
  have hr : Summable (fun n => ‖r n‖) :=
    summable_norm_realDirichletTerm (abs_roughGauge_le hbd Q) hσ
  have hT := EulerProduct.eulerProduct_completely_multiplicative hf
  have hR := EulerProduct.eulerProduct_completely_multiplicative hr
  have hfp (p : ℕ) (hp : p.Prime) : f p = ω p * (p : ℝ) ^ (-(1 + σ)) :=
    if_neg hp.ne_zero
  have hrp (p : ℕ) (hp : p.Prime) : r p =
      (if Q ≤ p then ω p else 0) * (p : ℝ) ^ (-(1 + σ)) := by
    change realDirichletTerm (roughGauge Q ω) σ p = _
    rw [realDirichletTerm, if_neg hp.ne_zero, roughGauge_prime hp]
  have hne (p : ℕ) (hp : p.Prime) : 1 - f p ≠ 0 := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hpw := Real.rpow_lt_one_of_one_lt_of_neg hp1
      (show -(1 + σ) < 0 by linarith only [hσ])
    have hle := mul_le_mul_of_nonneg_right (abs_le.mp (hbd p)).2
      (Real.rpow_nonneg (Nat.cast_nonneg p) (-(1 + σ)))
    rw [hfp p hp]
    have hpos : 0 < 1 - ω p * (p : ℝ) ^ (-(1 + σ)) := by
      nlinarith only [hle, hpw]
    exact hpos.ne'
  have hlimit : Tendsto (fun X => ∏ p ∈ Nat.primesBelow X, (1 - r p)⁻¹) atTop
      (𝓝 ((∑' n, f n) * H)) := by
    apply (hT.mul_const H).congr'
    filter_upwards [eventually_ge_atTop Q] with X hQX
    have hsub : Nat.primesBelow Q ⊆ Nat.primesBelow X := by
      intro p hp
      obtain ⟨hpQ, hpp⟩ := Nat.mem_primesBelow.mp hp
      exact Nat.mem_primesBelow.mpr ⟨hpQ.trans_le hQX, hpp⟩
    have hhead : H = ∏ p ∈ Nat.primesBelow X, if p < Q then 1 - f p else 1 := by
      calc
        H = ∏ p ∈ Nat.primesBelow Q, if p < Q then 1 - f p else 1 := by
          exact prod_congr rfl fun p hp => (if_pos (Nat.mem_primesBelow.mp hp).1).symm
        _ = _ := prod_subset hsub fun p hp hpQ => if_neg fun h =>
          hpQ (Nat.mem_primesBelow.mpr ⟨h, (Nat.mem_primesBelow.mp hp).2⟩)
    rw [hhead, ← prod_mul_distrib]
    refine prod_congr rfl fun p hp => ?_
    have hpp := (Nat.mem_primesBelow.mp hp).2
    by_cases hpQ : p < Q
    · rw [if_pos hpQ, inv_mul_cancel₀ (hne p hpp), hrp p hpp,
        if_neg (Nat.not_le.mpr hpQ), zero_mul, sub_zero, inv_one]
    · rw [if_neg hpQ, mul_one, hrp p hpp, if_pos (Nat.le_of_not_gt hpQ), hfp p hpp]
  have h := tendsto_nhds_unique hR hlimit
  change (∑' n, realDirichletTerm (roughGauge Q ω) σ n) =
    (∑' n, realDirichletTerm ω σ n) * H at h
  have hH : H = ∏ p ∈ Nat.primesBelow Q, (1 - ω p * (p : ℝ) ^ (-(1 + σ))) :=
    prod_congr rfl fun p hp => by rw [hfp p (Nat.mem_primesBelow.mp hp).2]
  rwa [hH] at h

/-- The positive divisor convolution retains the exact finite Euler head under
rough prime removal. Both series converge absolutely. -/
theorem realDivisorDirichletSeries_roughGauge_eq {ω : ℕ → ℝ} (h1 : ω 1 = 1)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → ω (m * n) = ω m * ω n)
    (hbd : ∀ n, |ω n| ≤ 1) {σ : ℝ} (hσ : 0 < σ) (Q : ℕ) :
    Summable (realDirichletTerm (signDivisorCount (roughGauge Q ω)) σ) ∧
      (∑' n, realDirichletTerm (signDivisorCount (roughGauge Q ω)) σ n) =
        (∑' n, realDirichletTerm (signDivisorCount ω) σ n) *
          ∏ p ∈ Nat.primesBelow Q, (1 - ω p * (p : ℝ) ^ (-(1 + σ))) := by
  have hr := hasSum_realDivisorDirichletTerm (abs_roughGauge_le hbd Q) hσ
  refine ⟨hr.summable, ?_⟩
  rw [hr.tsum_eq, (hasSum_realDivisorDirichletTerm hbd hσ).tsum_eq,
    realDirichletSeries_roughGauge_eq h1 hmul hbd hσ Q]
  ring

end GaloisForLFunctions.RenormalizedIntersectionTheory
