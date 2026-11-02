import GaloisForLFunctions.RenormalizedIntersectionTheory.ThePositiveDivisorMeanControlsItsLaplaceTransform
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheRoughFlipHasAPositiveDivisorMean
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheFiniteEulerHeadControlsPrimeRemoval
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheDivisorDirichletSeriesRetainsPrimeRemoval
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheSparseFlipHasAnEventuallyPositiveHarmonicMean

/-!
# Uniform rough means at zero prime density

The positive Laplace comparison survives finite Euler-head removal. The universal
signed-to-positive inequality then bounds every rough harmonic mean by the original
signed mean divided by the rough logarithm and finite flip density.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

private theorem logarithmicLaplaceTerm_eq_realDirichletTerm (g : ℕ → ℝ) (u : ℝ) :
    logarithmicLaplaceTerm g u = realDirichletTerm g (1 / u) := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [logarithmicLaplaceTerm, realDirichletTerm]
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [logarithmicLaplaceTerm, realDirichletTerm, if_neg hn,
    show -(1 + 1 / u) = -1 + -(1 / u) by ring,
    Real.rpow_add hn0, Real.rpow_neg_one, Real.rpow_def_of_pos hn0,
    show Real.log n * -(1 / u) = -(Real.log n / u) by ring]
  ring

private theorem realDirichletTerm_nonneg {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n)
    (σ : ℝ) (n : ℕ) : 0 ≤ realDirichletTerm g σ n := by
  unfold realDirichletTerm
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

private theorem realHarmonicMean_le_dirichletSeries {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n)
    {u : ℝ} (hu : 0 < u) (hsum : Summable (realDirichletTerm g (1 / u))) :
    realLogHarmonicSum g u ≤ Real.exp 1 * ∑' n, realDirichletTerm g (1 / u) n := by
  have hfinite : realLogHarmonicSum g u ≤ Real.exp 1 *
      ∑ n ∈ Icc 1 ⌊Real.exp u⌋₊, realDirichletTerm g (1 / u) n := by
    change (∑ n ∈ Icc 1 ⌊Real.exp u⌋₊, g n / n) ≤ _
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hlog : Real.log n ≤ u := (Real.log_le_iff_le_exp hn0).mpr
      ((Nat.le_floor_iff (Real.exp_pos u).le).mp (mem_Icc.mp hn).2)
    have hquot : Real.log n / u ≤ 1 := (div_le_one hu).mpr hlog
    have hweight : 1 ≤ Real.exp 1 * Real.exp (-(Real.log n / u)) := by
      rw [← Real.exp_add]
      have h := Real.exp_le_exp.mpr (show 0 ≤ 1 + -(Real.log n / u) by linarith only [hquot])
      simpa only [Real.exp_zero] using h
    calc
      g n / n ≤ (g n / n) * (Real.exp 1 * Real.exp (-(Real.log n / u))) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hweight
          (div_nonneg (hg n) hn0.le)
      _ = Real.exp 1 * realDirichletTerm g (1 / u) n := by
        rw [← logarithmicLaplaceTerm_eq_realDirichletTerm g u]
        unfold logarithmicLaplaceTerm
        ring
  exact hfinite.trans (mul_le_mul_of_nonneg_left
    (hsum.sum_le_tsum _ (fun n _ => realDirichletTerm_nonneg hg _ n)) (Real.exp_pos _).le)

private theorem realLogHarmonicSum_log_nat (g : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    realLogHarmonicSum g (Real.log N) = gaugeHarmonicSum g N := by
  rw [realLogHarmonicSum, Real.exp_log (by exact_mod_cast hN)]
  simp

/-- Under zero logarithmic prime density, rough signed means are uniformly controlled
by the original signed mean and the finite flip density, with an absolute additive error. -/
theorem exists_eventually_uniform_zeroDensity_roughMean_bound (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 3 ≤ Q → Q ≤ N →
      |gaugeHarmonicSum (roughGauge Q (primeSetFlip P)) N| ≤
        A * (gaugeHarmonicSum (primeSetFlip P) N /
          (Real.log Q * flipDensityBelow (primeSetFlip P) Q)) + B := by
  obtain ⟨C₁, U, hC₁, hU, hLaplace⟩ := exists_positiveDivisorMean_laplace_comparison P hP
  obtain ⟨C₂, hC₂, hHead⟩ := exists_uniform_tiltedPrimeRemovalFactor_le
  let A := 2 * Real.exp 1 * C₁ * C₂
  let B := 2 * (4 + 3 * (Real.log 4 + 4))
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 < B := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [B]
    linarith only [h]
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrec := (Metric.tendsto_nhds.mp
    (tendsto_signedMean_mul_log_div_positiveDivisorMean P hP)) 1 (by norm_num)
  refine ⟨A, B, hA, hB, ?_⟩
  filter_upwards [hrec, hlog.eventually (eventually_ge_atTop U),
    eventually_ge_atTop (3 : ℕ)] with N hrecN hUN hN Q hQ hQN
  let ω := primeSetFlip P
  let G := gaugeHarmonicSum (signDivisorCount ω) N
  let GR := gaugeHarmonicSum (signDivisorCount (roughGauge Q ω)) N
  let S := gaugeHarmonicSum ω N
  let u := Real.log N
  let d := Real.log Q * flipDensityBelow ω Q
  have hu1 : 1 ≤ u := hU.trans hUN
  have hu : 0 < u := zero_lt_one.trans_le hu1
  have hN1 : 1 ≤ N := by omega
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQu : Real.log Q ≤ u := Real.log_le_log hQ0 (by exact_mod_cast hQN)
  have hbd : ∀ n, |ω n| ≤ 1 := abs_primeSetFlip_le P
  have hd : 0 < d := mul_pos (zero_lt_one.trans_le (one_le_log_of_three_le hQ))
    (flipDensityBelow_pos_le_one hbd Q).1
  have hG : 0 < G := by
    have h := one_le_realLogHarmonicSum_signDivisorCount (primeSetFlip_isSignGauge P)
      (Real.log_natCast_nonneg N)
    rw [realLogHarmonicSum_log_nat _ hN1] at h
    exact zero_lt_one.trans_le h
  have hGS : G / u ≤ S := by
    rw [Real.dist_eq] at hrecN
    change |S * u / G - 2| < 1 at hrecN
    have hratio : 1 ≤ S * u / G := by linarith only [(abs_lt.mp hrecN).1]
    have h := (le_div_iff₀ hG).mp hratio
    exact (div_le_iff₀ hu).mpr (by simpa only [one_mul] using h)
  obtain ⟨_, hOriginal⟩ := hLaplace u hUN
  rw [logarithmicLaplaceTerm_eq_realDirichletTerm] at hOriginal
  change (∑' n, realDirichletTerm (signDivisorCount ω) (1 / u) n) ≤
    C₁ * realLogHarmonicSum (signDivisorCount ω) (Real.log N) at hOriginal
  rw [realLogHarmonicSum_log_nat _ hN1] at hOriginal
  have hremove := realDivisorDirichletSeries_roughGauge_eq
    (signGauge_map_one (primeSetFlip_isSignGauge P))
    (fun _ _ hm hn => (primeSetFlip_isSignGauge P).mul hm hn) hbd
    (show 0 < 1 / u by positivity) Q
  have htrunc := realHarmonicMean_le_dirichletSeries (roughFlipDivisorCount_nonneg P Q) hu hremove.1
  change realLogHarmonicSum (signDivisorCount (roughGauge Q ω)) (Real.log N) ≤ _ at htrunc
  rw [realLogHarmonicSum_log_nat _ hN1, hremove.2] at htrunc
  have hhead := hHead ω hbd Q hQ u hu1 hQu
  have hhead0 := (tiltedPrimeRemovalFactor_pos hbd Q hu).le
  change 0 ≤ ∏ p ∈ Nat.primesBelow Q, (1 - ω p * (p : ℝ) ^ (-(1 + 1 / u))) at hhead0
  change (∏ p ∈ Nat.primesBelow Q, (1 - ω p * (p : ℝ) ^ (-(1 + 1 / u)))) ≤ C₂ / d at hhead
  have hseries : GR ≤ Real.exp 1 * ((C₁ * G) * (C₂ / d)) := by
    refine htrunc.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    exact (mul_le_mul_of_nonneg_right hOriginal hhead0).trans
      (mul_le_mul_of_nonneg_left hhead (mul_nonneg hC₁.le hG.le))
  have hrough := abs_roughFlipHarmonicSum_le_divisorMean P Q hN
  change |gaugeHarmonicSum (roughGauge Q ω) N| ≤ 2 * (GR / u) + B at hrough
  refine hrough.trans (add_le_add ?_ le_rfl)
  calc
    2 * (GR / u) ≤ 2 * ((Real.exp 1 * ((C₁ * G) * (C₂ / d))) / u) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hseries hu.le) (by norm_num)
    _ = (A / d) * (G / u) := by dsimp only [A]; ring
    _ ≤ (A / d) * S := mul_le_mul_of_nonneg_left hGS (div_nonneg hA.le hd.le)
    _ = A * (S / d) := by ring

end GaloisForLFunctions.RenormalizedIntersectionTheory
