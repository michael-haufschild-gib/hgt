import GaloisForLFunctions.RHTower.LiEvenCrossEulerMassSeries
import GaloisForLFunctions.RHTower.LiEvenCrossRealEulerJetBridge
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Exact mass series for every actual LI Euler jet

At each fixed derivative order, the actual source mass series can be
differentiated after exponential transport. Absolute convergence at mass `3/4`
and the window `|t| < log 2` provide summable geometric slack. No estimate
uniform over growing derivative orders is used in this termwise identity.
-/

open Filter Topology Metric

namespace RHTower

noncomputable section

private def liMassExpTerm (a : ℕ → ℝ) (v : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  a n * v ^ (n + 1) * Real.exp (((n + 1 : ℕ) : ℝ) * t)

private theorem liMassExpTerm_iteratedDeriv (a : ℕ → ℝ) (v : ℝ) (n k : ℕ) (t : ℝ) :
    iteratedDeriv k (liMassExpTerm a v n) t =
      a n * v ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k *
        Real.exp (((n + 1 : ℕ) : ℝ) * t) := by
  change iteratedDeriv k
    ((a n * v ^ (n + 1)) • (fun t : ℝ => Real.exp (((n + 1 : ℕ) : ℝ) * t))) t = _
  rw [iteratedDeriv_const_smul_field, iteratedDeriv_exp_const_mul, smul_eq_mul]
  ring

private theorem liMassExp_window_mass_le_half {v t : ℝ}
    (hv : 0 < v) (hvquarter : v ≤ 1 / 4)
    (ht : t ∈ Metric.ball (0 : ℝ) (Real.log 2)) :
    v * Real.exp t ≤ 1 / 2 := by
  have htlog : t < Real.log 2 := by
    have ht' : |t| < Real.log 2 := by simpa [Real.dist_eq] using ht
    exact (le_abs_self t).trans_lt ht'
  have hexp : Real.exp t ≤ 2 := by
    have h := Real.exp_le_exp.mpr htlog.le
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  nlinarith [Real.exp_pos t]

private theorem liMassExp_local_jet {a : ℕ → ℝ} {v : ℝ}
    (hv : 0 < v) (hvquarter : v ≤ 1 / 4)
    (ha : Summable (fun n => ‖a n‖ * (3 / 4 : ℝ) ^ (n + 1))) (m : ℕ) :
    (iteratedDeriv m (fun t : ℝ => ∑' n, liMassExpTerm a v n t) 0 =
      ∑' n, a n * v ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ m) ∧
      Summable (fun n => a n * v ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ m) := by
  let s := Metric.ball (0 : ℝ) (Real.log 2)
  let u : ℕ → ℕ → ℝ := fun k n =>
    (‖a n‖ * (3 / 4 : ℝ) ^ (n + 1)) *
      (((n + 1 : ℕ) : ℝ) ^ k * (2 / 3 : ℝ) ^ (n + 1))
  have hs : IsOpen s := isOpen_ball
  have hzero : (0 : ℝ) ∈ s := Metric.mem_ball_self (Real.log_pos (by norm_num))
  have hu : ∀ k, Summable (u k) := by
    intro k
    have hp : Summable (fun n : ℕ => (n : ℝ) ^ k * (2 / 3 : ℝ) ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one k (by norm_num)
    have hps : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * (2 / 3 : ℝ) ^ (n + 1)) := by
      simpa [Function.comp_def] using hp.comp_injective Nat.succ_injective
    have hprod := ha.mul_of_nonneg hps (fun _ => by positivity) (fun _ => by positivity)
    simpa [u, Function.comp_def] using hprod.comp_injective
      (show Function.Injective (fun n : ℕ => (n, n)) from fun _ _ h => congrArg Prod.fst h)
  have hbound : ∀ k n t, t ∈ s → ‖iteratedDeriv k (liMassExpTerm a v n) t‖ ≤ u k n := by
    intro k n t ht
    have hmass := liMassExp_window_mass_le_half hv hvquarter ht
    have hpow : (1 / 2 : ℝ) ^ (n + 1) =
        (3 / 4 : ℝ) ^ (n + 1) * (2 / 3 : ℝ) ^ (n + 1) := by
      rw [← mul_pow]
      norm_num
    calc
      ‖iteratedDeriv k (liMassExpTerm a v n) t‖ =
          ‖a n‖ * ((n + 1 : ℕ) : ℝ) ^ k * (v * Real.exp t) ^ (n + 1) := by
        rw [liMassExpTerm_iteratedDeriv]
        simp only [norm_mul, norm_pow, Real.norm_of_nonneg hv.le,
          Real.norm_of_nonneg (Nat.cast_nonneg (n + 1)),
          Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_nat_mul, mul_pow]
        ring
      _ ≤ ‖a n‖ * ((n + 1 : ℕ) : ℝ) ^ k * (1 / 2 : ℝ) ^ (n + 1) := by
        gcongr
      _ = u k n := by rw [hpow]; dsimp [u]; ring
  have hwithin : ∀ k, SummableLocallyUniformlyOn
      (fun n => iteratedDerivWithin k (liMassExpTerm a v n) s) s := by
    intro k
    apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
    apply HasSumUniformlyOn.hasSumLocallyUniformlyOn
    apply HasSumUniformlyOn.of_norm_le_summable (hu k)
    intro n t ht
    rw [iteratedDerivWithin_of_isOpen hs ht]
    exact hbound k n t ht
  have hdiff : ∀ n k t, t ∈ s →
      DifferentiableAt ℝ (iteratedDerivWithin k (liMassExpTerm a v n) s) t := by
    intro n k t ht
    apply DifferentiableOn.differentiableAt _ (hs.mem_nhds ht)
    suffices DifferentiableOn ℝ (iteratedDeriv k (liMassExpTerm a v n)) s by
      apply this.congr (iteratedDerivWithin_of_isOpen hs)
    have heq : iteratedDeriv k (liMassExpTerm a v n) = fun t =>
        a n * v ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k *
          Real.exp (((n + 1 : ℕ) : ℝ) * t) := funext (liMassExpTerm_iteratedDeriv a v n k)
    rw [heq]
    fun_prop
  constructor
  · rw [← iteratedDerivWithin_of_isOpen hs hzero, iteratedDerivWithin_tsum m hs hzero]
    · apply tsum_congr
      intro n
      rw [iteratedDerivWithin_of_isOpen hs hzero, liMassExpTerm_iteratedDeriv]
      simp
    · intro t ht
      exact Summable.of_norm_bounded (hu 0) (fun n => by
        simpa only [iteratedDeriv_zero] using hbound 0 n t ht)
    · exact fun k _ _ => hwithin k
    · exact fun n k t _ ht => hdiff n k t ht
  · have hsum := Summable.of_norm_bounded (hu m) (fun n => hbound m n 0 hzero)
    simpa only [liMassExpTerm_iteratedDeriv, mul_zero, Real.exp_zero, mul_one] using hsum

private theorem realLogMassCurrent_eventuallyEq_massExpSeries
    {v : ℝ} (hv : 0 < v) (hvquarter : v ≤ 1 / 4) :
    liEvenCrossRealLogMassFirstCurrent v =ᶠ[𝓝 0]
      (fun t : ℝ => ∑' n, liMassExpTerm liEvenCrossEulerMassCoeff v n t) := by
  have hball : Metric.ball (0 : ℝ) (Real.log 2) ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds _ (Real.log_pos (by norm_num))
  filter_upwards [hball] with t ht
  have hmass : v * Real.exp t < 1 :=
    (liMassExp_window_mass_le_half hv hvquarter ht).trans_lt (by norm_num)
  have hsource := liEvenCrossCassiniLogMassCurrent_eq_massSeries
    (mul_pos hv (Real.exp_pos t)) hmass
  have hcast :
      (∑' n, (liEvenCrossEulerMassCoeff n : ℂ) *
        ((v * Real.exp t : ℝ) : ℂ) ^ (n + 1)) =
      ((∑' n, liEvenCrossEulerMassCoeff n * (v * Real.exp t) ^ (n + 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    simp
  rw [hcast] at hsource
  have hre := congrArg Complex.re hsource
  rw [liEvenCrossRealLogMassFirstCurrent_eq_re_complex hv]
  have he : (v : ℂ) * Complex.exp (t : ℂ) = ((v * Real.exp t : ℝ) : ℂ) := by
    simp [Complex.ofReal_exp]
  change (liEvenCrossCassiniLogMassCurrent ((v : ℂ) * Complex.exp (t : ℂ))).re = _
  rw [he, hre]
  apply tsum_congr
  intro n
  simp only [liMassExpTerm, Real.exp_nat_mul, mul_pow]
  ring

/-- Every fixed real log-mass derivative has the exact source mass-series formula. -/
theorem liEvenCrossRealLogMassFirstCurrent_iteratedDeriv_eq_massSeries
    {v : ℝ} (hv : 0 < v) (hvquarter : v ≤ 1 / 4) (m : ℕ) :
    iteratedDeriv m (liEvenCrossRealLogMassFirstCurrent v) 0 =
      ∑' n, liEvenCrossEulerMassCoeff n * v ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ m := by
  rw [(realLogMassCurrent_eventuallyEq_massExpSeries hv hvquarter).iteratedDeriv_eq m]
  exact (liMassExp_local_jet hv hvquarter
    (summable_norm_liEvenCrossEulerMassCoeff_mul_pow
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)) m).1

/-- The actual even Euler jet, with the source's original coefficient normalization. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_eq_coeff_massSeries
    {v : ℝ} (hv : 0 < v) (hvquarter : v ≤ 1 / 4) (k : ℕ) :
    liEvenCrossFirstCurrentEvenEulerJet v k =
      ∑' n, liEvenCrossEulerMassCoeff n * v ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (2 * k) := by
  rw [← liEvenCrossRealLogMassFirstCurrent_even_deriv_eq_eulerJet hv]
  exact liEvenCrossRealLogMassFirstCurrent_iteratedDeriv_eq_massSeries hv hvquarter (2 * k)

/-- **Exact actual-source jet series:** intrinsic Xi-copy normalization is retained. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_eq_massSeries
    {v : ℝ} (hv : 0 < v) (hvquarter : v ≤ 1 / 4) (k : ℕ) :
    liEvenCrossFirstCurrentEvenEulerJet v k =
      ∑' n, 2 * (-1 : ℝ) ^ n * ((n + 1 : ℕ) : ℝ) ^ (2 * k + 2) *
        normalizedPrimeArchMoment n * v ^ (n + 1) := by
  rw [liEvenCrossFirstCurrentEvenEulerJet_eq_coeff_massSeries hv hvquarter]
  apply tsum_congr
  intro n
  simp only [liEvenCrossEulerMassCoeff, pow_add]
  ring

/-- Absolute weighted-jet summability permits exact finite-prefix and tail decompositions. -/
theorem summable_liEvenCrossFirstCurrentEvenEulerJet_massSeries
    {v : ℝ} (hv : 0 < v) (hvquarter : v ≤ 1 / 4) (k : ℕ) :
    Summable (fun n => (-1 : ℝ) ^ n * ((n + 1 : ℕ) : ℝ) ^ (2 * k + 2) *
      normalizedPrimeArchMoment n * v ^ (n + 1)) := by
  have hs := (liMassExp_local_jet hv hvquarter
    (summable_norm_liEvenCrossEulerMassCoeff_mul_pow
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)) (2 * k)).2
  refine (hs.mul_left (1 / 2 : ℝ)).congr fun n => ?_
  simp only [liEvenCrossEulerMassCoeff, pow_add]
  ring

end

end RHTower
