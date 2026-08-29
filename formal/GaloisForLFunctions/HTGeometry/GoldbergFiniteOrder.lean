import GaloisForLFunctions.HTGeometry.GoldbergCentralIndex
import GaloisForLFunctions.HTGeometry.MaximumModulusLocalGrowth
import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard
import GaloisForLFunctions.HTGeometry.EntireOrderTwoSeries

/-!
# Gol'dberg's theorem: an entire solution of a first-order algebraic ODE has finite order

A polynomial bound on the central index bounds the maximum term, and the maximum modulus is the
maximum term times a factor linear in the central index.  The resulting envelope is exactly the
finite-order envelope consumed by Hadamard's zero-free factorization.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Finset Set

variable {a : ℕ → ℂ}

/-- **A polynomial central index gives a finite-order envelope.** -/
theorem finiteOrderEnvelope_of_centralIndex_le_pow (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {C : ℝ} {K : ℕ} (hC : 0 < C)
    (hν : ∀ᶠ t : ℝ in atTop, ((centralIndex a t : ℕ) : ℝ) ≤ C * t ^ K) :
    FiniteOrderEnvelope (coeffFun a) := by
  classical
  -- the central index is below a pure power
  have hνrpow : ∀ᶠ t : ℝ in atTop, ((centralIndex a t : ℕ) : ℝ) ≤ t ^ ((K : ℝ) + 1) := by
    filter_upwards [hν, eventually_ge_atTop (max C 1)] with t h1 h2
    have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right C 1) h2
    have htC : C ≤ t := le_trans (le_max_left C 1) h2
    have htpos : (0 : ℝ) < t := by linarith
    have hpow : t ^ ((K : ℝ) + 1) = t ^ K * t := by
      rw [Real.rpow_add htpos, Real.rpow_natCast, Real.rpow_one]
    rw [hpow]
    have hnn : (0 : ℝ) ≤ t ^ K := by positivity
    nlinarith [h1, htC, hnn]
  -- hence the maximum term is below a pure power
  have hmax : ∀ᶠ r : ℝ in atTop, Real.log (maxTerm a r) ≤ r ^ ((K : ℝ) + 2) :=
    log_maxTerm_le_rpow_of_centralIndex_le_rpow ha hn₀ (by positivity)
      (by linarith : (K : ℝ) + 1 < (K : ℝ) + 2) hνrpow
  -- the maximum modulus is the maximum term times a factor linear in the central index
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (hmax.and (hν.and (eventually_ge_atTop (1 : ℝ))))
  set R₁ : ℝ := max R₀ 1 with hR₁
  have hR₁1 : (1 : ℝ) ≤ R₁ := le_max_right _ _
  have hR₁pos : (0 : ℝ) < R₁ := by linarith
  have hbig : ∀ r : ℝ, R₁ ≤ r →
      Real.log (maxTerm a r) ≤ r ^ ((K : ℝ) + 2)
        ∧ ((centralIndex a r : ℕ) : ℝ) ≤ C * r ^ K := by
    intro r hr
    have h := hR₀ r (le_trans (le_max_left R₀ 1) hr)
    exact ⟨h.1, h.2.1⟩
  set Cbig : ℝ := 1 + (C * 2 ^ K + 2) with hCbig
  set M₁ : ℝ := max (coeffSum a R₁) ‖coeffFun a 0‖ with hM₁
  have hM₁0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (le_max_right _ _)
  refine ⟨max Cbig (Real.log (max M₁ 1)), K + 2, ?_, ?_⟩
  · refine le_max_of_le_left ?_
    rw [hCbig]
    positivity
  intro z
  have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by
    have := norm_nonneg z
    linarith
  have hpowbase : (1 : ℝ) ≤ (1 + ‖z‖) ^ (K + 2) := one_le_pow₀ hbase
  by_cases hz : R₁ ≤ ‖z‖
  · have hzpos : (0 : ℝ) < ‖z‖ := by linarith
    have h1 : ‖coeffFun a z‖ ≤ coeffSum a ‖z‖ := norm_coeffFun_le ha hzpos
    have h2 : coeffSum a ‖z‖ ≤ maxTerm a ‖z‖ * ((centralIndex a (2 * ‖z‖) : ℝ) + 2) :=
      coeffSum_le_maxTerm_mul_two ha hn₀ hzpos
    obtain ⟨hlog, -⟩ := hbig ‖z‖ hz
    obtain ⟨-, -, hmaxpos⟩ := exists_maxTerm_eq ha hzpos hn₀
    have hmaxle : maxTerm a ‖z‖ ≤ Real.exp (‖z‖ ^ ((K : ℝ) + 2)) := by
      have := Real.exp_le_exp.mpr hlog
      rwa [Real.exp_log hmaxpos] at this
    have hz2 : R₁ ≤ 2 * ‖z‖ := by linarith
    obtain ⟨-, hνz⟩ := hbig (2 * ‖z‖) hz2
    have hνle : ((centralIndex a (2 * ‖z‖) : ℕ) : ℝ) + 2 ≤ (C * 2 ^ K + 2) * (1 + ‖z‖) ^ K := by
      have hpow : (2 * ‖z‖) ^ K ≤ 2 ^ K * (1 + ‖z‖) ^ K := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ K
        linarith
      have hone : (1 : ℝ) ≤ (1 + ‖z‖) ^ K := one_le_pow₀ hbase
      nlinarith [hνz, hpow, hone, hC]
    -- combine
    have hrpowle : ‖z‖ ^ ((K : ℝ) + 2) ≤ (1 + ‖z‖) ^ (K + 2) := by
      have h1' : ‖z‖ ^ ((K : ℝ) + 2) = ‖z‖ ^ (K + 2) := by
        rw [show ((K : ℝ) + 2) = ((K + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      rw [h1']
      exact pow_le_pow_left₀ (norm_nonneg z) (by linarith) (K + 2)
    have hlinle : (C * 2 ^ K + 2) * (1 + ‖z‖) ^ K
        ≤ Real.exp ((C * 2 ^ K + 2) * (1 + ‖z‖) ^ (K + 2)) := by
      refine le_trans ?_ (Real.add_one_le_exp ((C * 2 ^ K + 2) * (1 + ‖z‖) ^ (K + 2)))
      have hmono : (1 + ‖z‖) ^ K ≤ (1 + ‖z‖) ^ (K + 2) :=
        pow_le_pow_right₀ hbase (by omega)
      have hc0 : (0 : ℝ) ≤ C * 2 ^ K + 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hmono hc0]
    calc ‖coeffFun a z‖ ≤ maxTerm a ‖z‖ * (((centralIndex a (2 * ‖z‖) : ℕ) : ℝ) + 2) :=
          le_trans h1 h2
      _ ≤ Real.exp (‖z‖ ^ ((K : ℝ) + 2)) * ((C * 2 ^ K + 2) * (1 + ‖z‖) ^ K) := by
          refine mul_le_mul hmaxle hνle (by positivity) (le_of_lt (Real.exp_pos _))
      _ ≤ Real.exp ((1 + ‖z‖) ^ (K + 2))
            * Real.exp ((C * 2 ^ K + 2) * (1 + ‖z‖) ^ (K + 2)) := by
          refine mul_le_mul (Real.exp_le_exp.mpr hrpowle) hlinle ?_ (le_of_lt (Real.exp_pos _))
          positivity
      _ = Real.exp (Cbig * (1 + ‖z‖) ^ (K + 2)) := by
          rw [← Real.exp_add, hCbig]
          ring_nf
      _ ≤ Real.exp (max Cbig (Real.log (max M₁ 1)) * (1 + ‖z‖) ^ (K + 2)) := by
          refine Real.exp_le_exp.mpr ?_
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · push_neg at hz
    have hsmall : ‖coeffFun a z‖ ≤ M₁ := by
      by_cases hz0 : ‖z‖ = 0
      · have : z = 0 := by simpa using hz0
        rw [this]
        exact le_max_right _ _
      · have hzpos : (0 : ℝ) < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz0)
        refine le_trans (norm_coeffFun_le ha hzpos) ?_
        exact le_trans (coeffSum_mono ha hzpos (le_of_lt hz)) (le_max_left _ _)
    have hM1 : M₁ ≤ max M₁ 1 := le_max_left _ _
    have hMpos : (0 : ℝ) < max M₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hlogM : max M₁ 1 = Real.exp (Real.log (max M₁ 1)) := (Real.exp_log hMpos).symm
    calc ‖coeffFun a z‖ ≤ max M₁ 1 := le_trans hsmall hM1
      _ = Real.exp (Real.log (max M₁ 1)) := hlogM
      _ ≤ Real.exp (max Cbig (Real.log (max M₁ 1)) * (1 + ‖z‖) ^ (K + 2)) := by
          refine Real.exp_le_exp.mpr ?_
          have hlogpos : 0 ≤ Real.log (max M₁ 1) := Real.log_nonneg (le_max_right _ _)
          have hle : Real.log (max M₁ 1) ≤ max Cbig (Real.log (max M₁ 1)) := le_max_right _ _
          nlinarith [hpowbase, hlogpos, hle]

/-! ## The Taylor bridge -/

/-- The Taylor coefficients of an entire function satisfy the decay hypothesis. -/
theorem entireCoeffs_taylorCoeff {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    EntireCoeffs (taylorCoeff f) := by
  intro r hr
  have hsum := (hasSum_taylorCoeff hf ((r : ℝ) : ℂ)).summable
  have hzero := hsum.tendsto_atTop_zero
  have hnorm : Filter.Tendsto (fun n => ‖taylorCoeff f n * ((r : ℝ) : ℂ) ^ n‖) atTop (nhds 0) := by
    simpa using hzero.norm
  refine hnorm.congr fun n => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.le]

/-- An entire function is the coefficient sum of its Taylor coefficients. -/
theorem coeffFun_taylorCoeff {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    coeffFun (taylorCoeff f) = f := by
  funext z
  rw [coeffFun_eq_tsum]
  exact (hasSum_taylorCoeff hf z).tsum_eq

/-- A function with finitely many nonzero Taylor coefficients has a finite-order envelope. -/
theorem finiteOrderEnvelope_of_eventually_taylorCoeff_eq_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {M : ℕ} (hM : ∀ n, M ≤ n → taylorCoeff f n = 0) :
    FiniteOrderEnvelope f := by
  classical
  set a : ℕ → ℂ := taylorCoeff f with ha
  set B : ℝ := ∑ n ∈ Finset.range M, ‖a n‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun n _ => norm_nonneg _
  have hfin : ∀ z : ℂ, ‖f z‖ ≤ B * (1 + ‖z‖) ^ M := by
    intro z
    have hsum := hasSum_taylorCoeff hf z
    have hfinsum : HasSum (fun n => a n * z ^ n) (∑ n ∈ Finset.range M, a n * z ^ n) := by
      refine hasSum_sum_of_ne_finset_zero ?_
      intro n hn
      have hMn : M ≤ n := by
        by_contra hcon
        exact hn (Finset.mem_range.mpr (Nat.lt_of_not_le hcon))
      rw [hM n hMn, zero_mul]
    have heq : f z = ∑ n ∈ Finset.range M, a n * z ^ n := hsum.unique hfinsum
    rw [heq]
    calc ‖∑ n ∈ Finset.range M, a n * z ^ n‖ ≤ ∑ n ∈ Finset.range M, ‖a n * z ^ n‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range M, ‖a n‖ * (1 + ‖z‖) ^ M := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [norm_mul, norm_pow]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          calc ‖z‖ ^ n ≤ (1 + ‖z‖) ^ n :=
                pow_le_pow_left₀ (norm_nonneg z) (by linarith) n
            _ ≤ (1 + ‖z‖) ^ M := by
                refine pow_le_pow_right₀ (by linarith [norm_nonneg z]) ?_
                exact le_of_lt (Finset.mem_range.mp hn)
      _ = B * (1 + ‖z‖) ^ M := by rw [← Finset.sum_mul, hB]
  refine ⟨B + 1, M, by linarith, fun z => ?_⟩
  have hpow : (1 : ℝ) ≤ (1 + ‖z‖) ^ M := one_le_pow₀ (by linarith [norm_nonneg z])
  calc ‖f z‖ ≤ B * (1 + ‖z‖) ^ M := hfin z
    _ ≤ (B + 1) * (1 + ‖z‖) ^ M + 1 := by nlinarith [hpow, hB0]
    _ ≤ Real.exp ((B + 1) * (1 + ‖z‖) ^ M) := Real.add_one_le_exp _

/-! ## Gol'dberg's theorem -/

/-- **Gol'dberg's theorem.**  An entire solution of a first-order algebraic differential relation
whose top symbol has positive degree in the derivative has a finite-order growth envelope. -/
theorem finiteOrderEnvelope_of_algebraic_relation {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {n₀ : ℕ} (hn₀ : taylorCoeff f n₀ ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d m : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ, ∑ p ∈ S, (A p).eval w * f w ^ p.1 * deriv f w ^ p.2 = 0)
    (hm : 1 ≤ m) (hmd : m ≤ d) (hmem : (d - m, m) ∈ S)
    (htopdeg : ∀ p ∈ S, p.1 + p.2 = d → p.2 ≤ m)
    (hAne : A (d - m, m) ≠ 0) :
    FiniteOrderEnvelope f := by
  classical
  have ha : EntireCoeffs (taylorCoeff f) := entireCoeffs_taylorCoeff hf
  have hfeq : coeffFun (taylorCoeff f) = f := coeffFun_taylorCoeff hf
  by_cases htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ taylorCoeff f n ≠ 0
  · have hrel' : ∀ w : ℂ, ∑ p ∈ S, (A p).eval w * (coeffFun (taylorCoeff f) w) ^ p.1
        * (deriv (coeffFun (taylorCoeff f)) w) ^ p.2 = 0 := by
      intro w
      rw [hfeq]
      exact hrel w
    obtain ⟨C, K, hC, hbound⟩ :=
      exists_centralIndex_le_pow_of_relation ha hn₀ htrans hdeg hrel' hm hmd hmem htopdeg hAne
    have henv := finiteOrderEnvelope_of_centralIndex_le_pow ha hn₀ hC hbound
    rwa [hfeq] at henv
  · push_neg at htrans
    obtain ⟨M, hM⟩ := htrans
    exact finiteOrderEnvelope_of_eventually_taylorCoeff_eq_zero hf hM

end GaloisForLFunctions.HTGeometry
