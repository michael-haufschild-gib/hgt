import GaloisForLFunctions.RHTower.SummableDivisorHarmonicMean
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower

noncomputable section

/-- Harmonic Toeplitz mean sampled at complementary quotients. -/
def harmonicQuotientMean (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, a (N / d) / (d : ℝ)

/-- A bounded convergent sequence has the same limit under the complementary-quotient
harmonic Toeplitz mean. -/
theorem tendsto_harmonicQuotientMean_div_log (a : ℕ → ℝ) (L C : ℝ)
    (ha : Tendsto a atTop (𝓝 L)) (hbound : ∀ n, |a n| ≤ C) :
    Tendsto (fun N : ℕ => harmonicQuotientMean a N / Real.log N) atTop (𝓝 L) := by
  have hC : 0 ≤ C := (abs_nonneg (a 0)).trans (hbound 0)
  let B : ℝ := C + |L|
  have hB : 0 ≤ B := add_nonneg hC (abs_nonneg L)
  have hratio := GaloisForLFunctions.tendsto_harmonic_div_log
  have herr : Tendsto (fun N : ℕ =>
      (∑ d ∈ Finset.Icc 1 N, (a (N / d) - L) / (d : ℝ)) / Real.log N)
      atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    let δ : ℝ := ε / 8
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hnear : ∀ᶠ n : ℕ in atTop, dist (a n) L < δ :=
      ha.eventually (Metric.ball_mem_nhds L hδ)
    rw [eventually_atTop] at hnear
    obtain ⟨K0, hK0⟩ := hnear
    let K : ℕ := max K0 1
    have hK0K : K0 ≤ K := le_max_left _ _
    have hKpos : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
    have hfull : ∀ᶠ N : ℕ in atTop,
        dist ((harmonic N : ℝ) / Real.log N) 1 < 1 :=
      hratio.eventually (Metric.ball_mem_nhds 1 zero_lt_one)
    rw [eventually_atTop] at hfull
    obtain ⟨Nfull, hNfull⟩ := hfull
    have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hlarge : ∀ᶠ N : ℕ in atTop, 4 * B * (K : ℝ) / ε < Real.log N :=
      hlog.eventually_gt_atTop (4 * B * (K : ℝ) / ε)
    rw [eventually_atTop] at hlarge
    obtain ⟨Nlarge, hNlarge⟩ := hlarge
    refine ⟨max (max Nfull Nlarge) 2, ?_⟩
    intro N hN
    have hNfull' : Nfull ≤ N := (le_max_left Nfull Nlarge).trans
      ((le_max_left (max Nfull Nlarge) 2).trans hN)
    have hNlarge' : Nlarge ≤ N := (le_max_right Nfull Nlarge).trans
      ((le_max_left (max Nfull Nlarge) 2).trans hN)
    have hN2 : 2 ≤ N := (le_max_right (max Nfull Nlarge) 2).trans hN
    have hNpos : 0 < N := by omega
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
    have hratioTwo : (harmonic N : ℝ) / Real.log N < 2 := by
      have hfullN := hNfull N hNfull'
      rw [Real.dist_eq] at hfullN
      have hself : (harmonic N : ℝ) / Real.log N - 1 ≤
          |(harmonic N : ℝ) / Real.log N - 1| := le_abs_self _
      linarith
    have hglobal : ∀ n : ℕ, |a n - L| ≤ B := by
      intro n
      dsimp [B]
      exact (abs_sub _ _).trans (add_le_add (hbound n) le_rfl)
    have hterm : ∀ d ∈ Finset.Icc 1 N,
        |(a (N / d) - L) / (d : ℝ)| ≤
          δ * (1 / (d : ℝ)) + B * ((K : ℝ) / (N : ℝ)) := by
      intro d hd
      obtain ⟨hdpos, hdN⟩ := Finset.mem_Icc.mp hd
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
      rw [abs_div, abs_of_pos hdR]
      by_cases hquot : K ≤ N / d
      · have hsmall : |a (N / d) - L| < δ := by
          rw [← Real.dist_eq]
          exact hK0 (N / d) (hK0K.trans hquot)
        have hfirst : |a (N / d) - L| / (d : ℝ) ≤ δ * (1 / (d : ℝ)) := by
          have := mul_le_mul_of_nonneg_right hsmall.le (by positivity : 0 ≤ 1 / (d : ℝ))
          simpa [div_eq_mul_inv] using this
        exact hfirst.trans (le_add_of_nonneg_right (mul_nonneg hB (by positivity)))
      · have hquot' : N / d < K := by omega
        have hNd : N < K * d := by
          simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hdpos).mp hquot'
        have hfrac : 1 / (d : ℝ) ≤ (K : ℝ) / (N : ℝ) := by
          rw [div_le_div_iff₀ hdR hNR]
          norm_num
          exact_mod_cast (Nat.le_of_lt hNd)
        have htail : |a (N / d) - L| / (d : ℝ) ≤
            B * ((K : ℝ) / (N : ℝ)) := by
          calc
            |a (N / d) - L| / (d : ℝ) =
                |a (N / d) - L| * (1 / (d : ℝ)) := by ring
            _ ≤ B * ((K : ℝ) / (N : ℝ)) :=
              mul_le_mul (hglobal (N / d)) hfrac (by positivity) hB
        exact htail.trans (le_add_of_nonneg_left (mul_nonneg hδ.le (by positivity)))
    have habssum :
        |∑ d ∈ Finset.Icc 1 N, (a (N / d) - L) / (d : ℝ)| ≤
          δ * (harmonic N : ℝ) + B * (K : ℝ) := by
      calc
        |∑ d ∈ Finset.Icc 1 N, (a (N / d) - L) / (d : ℝ)| ≤
            ∑ d ∈ Finset.Icc 1 N, |(a (N / d) - L) / (d : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Finset.Icc 1 N,
            (δ * (1 / (d : ℝ)) + B * ((K : ℝ) / (N : ℝ))) :=
          Finset.sum_le_sum hterm
        _ = δ * (harmonic N : ℝ) + B * (K : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            RHTower.Sieve.sum_Icc_one_div_eq_harmonic]
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          simp only [Nat.add_sub_cancel]
          field_simp [hNR.ne']
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hlogpos]
    calc
      |∑ d ∈ Finset.Icc 1 N, (a (N / d) - L) / (d : ℝ)| / Real.log N ≤
          (δ * (harmonic N : ℝ) + B * (K : ℝ)) / Real.log N :=
        div_le_div_of_nonneg_right habssum hlogpos.le
      _ = δ * ((harmonic N : ℝ) / Real.log N) +
          B * (K : ℝ) / Real.log N := by ring
      _ < ε := by
        have htail : B * (K : ℝ) / Real.log N < ε / 4 := by
          have hlargeN := hNlarge N hNlarge'
          have hε0 : 0 < ε := hε
          have hBK : 0 ≤ B * (K : ℝ) := mul_nonneg hB (by positivity)
          apply (div_lt_iff₀ hlogpos).2
          have hscaled := (div_lt_iff₀ hε0).mp hlargeN
          nlinarith
        have hhead : δ * ((harmonic N : ℝ) / Real.log N) < ε / 4 := by
          dsimp [δ]
          nlinarith
        linarith
  have hmain : Tendsto (fun N : ℕ =>
      L * ((harmonic N : ℝ) / Real.log N)) atTop (𝓝 L) := by
    simpa only [mul_one] using hratio.const_mul L
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogne : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [harmonicQuotientMean, ← RHTower.Sieve.sum_Icc_one_div_eq_harmonic]
  field_simp [hlogne]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

end

end RHTower

