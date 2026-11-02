import GaloisForLFunctions.RenormalizedIntersectionTheory.ThePositiveDivisorMeanVariesRegularly

/-!
# Positive divisor means and Laplace comparison

Uniform power comparisons control every larger logarithmic horizon at once.
Positive exponential-step covers then compare the weighted Dirichlet series with
its truncated harmonic mean.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity

/-- The positive divisor mean has uniform power bounds over all scale factors at least
one, beyond a single sufficiently large logarithmic horizon. -/
theorem exists_positiveDivisorMean_uniform_power_comparison (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ u c : ℝ, U ≤ u → 1 ≤ c →
      (1 / 2) * c ^ (2 - ε) * realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u ≤
        realLogHarmonicSum (signDivisorCount (primeSetFlip P)) (c * u) ∧
      realLogHarmonicSum (signDivisorCount (primeSetFlip P)) (c * u) ≤
        2 * c ^ (2 + ε) * realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u := by
  let G := realLogHarmonicSum (signDivisorCount (primeSetFlip P))
  let J := realPolarMoment (signDivisorCount (primeSetFlip P))
  obtain ⟨U₁, hU₁1, hU₁⟩ := exists_positive_divisor_log_scaling_bounds P hP hε
  obtain ⟨U₂, hU₂⟩ := eventually_atTop.mp
    (eventually_positive_divisor_polarMoment_comparison P hP)
  refine ⟨max U₁ U₂, hU₁1.trans (le_max_left _ _), fun u c huU hc1 => ?_⟩
  have hu1 : 1 ≤ u := hU₁1.trans ((le_max_left _ _).trans huU)
  have hu : 0 < u := zero_lt_one.trans_le hu1
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hucu : u ≤ c * u := by nlinarith only [hc1, hu]
  have hcu := mul_pos hc hu
  have hJu : 0 < J u := hu.trans_le
    (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) hu.le)
  have hJcu : 0 < J (c * u) := hcu.trans_le
    (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) hcu.le)
  have hlogs := hU₁ u (c * u) ((le_max_left _ _).trans huU) hucu
  rw [mul_div_cancel_right₀ c hu.ne'] at hlogs
  have hpowlo : c ^ (3 - ε) ≤ J (c * u) / J u := by
    have h := Real.exp_le_exp.mpr hlogs.1
    change Real.exp ((3 - ε) * Real.log c) ≤ Real.exp (Real.log (J (c * u) / J u)) at h
    rw [Real.exp_log (div_pos hJcu hJu)] at h
    simpa only [Real.rpow_def_of_pos hc, mul_comm] using h
  have hpowhi : J (c * u) / J u ≤ c ^ (3 + ε) := by
    have h := Real.exp_le_exp.mpr hlogs.2
    change Real.exp (Real.log (J (c * u) / J u)) ≤ Real.exp ((3 + ε) * Real.log c) at h
    rw [Real.exp_log (div_pos hJcu hJu)] at h
    simpa only [Real.rpow_def_of_pos hc, mul_comm] using h
  have hlo := (le_div_iff₀ hJu).mp hpowlo
  have hhi := (div_le_iff₀ hJu).mp hpowhi
  have hbase := hU₂ u ((le_max_right _ _).trans huU)
  have hfar := hU₂ (c * u) (((le_max_right _ _).trans huU).trans hucu)
  change 2 * J u ≤ u * G u ∧ u * G u ≤ 4 * J u at hbase
  change 2 * J (c * u) ≤ c * u * G (c * u) ∧
    c * u * G (c * u) ≤ 4 * J (c * u) at hfar
  have hsplitlo : c ^ (3 - ε) = c * c ^ (2 - ε) := by
    rw [show 3 - ε = 1 + (2 - ε) by ring, Real.rpow_add hc, Real.rpow_one]
  have hsplithi : c ^ (3 + ε) = c * c ^ (2 + ε) := by
    rw [show 3 + ε = 1 + (2 + ε) by ring, Real.rpow_add hc, Real.rpow_one]
  change (1 / 2) * c ^ (2 - ε) * G u ≤ G (c * u) ∧
    G (c * u) ≤ 2 * c ^ (2 + ε) * G u
  constructor
  · have hweighted := mul_le_mul_of_nonneg_right hbase.2 (Real.rpow_nonneg hc.le (3 - ε))
    rw [hsplitlo] at hlo hweighted
    have hprod : (u * c) * (c ^ (2 - ε) * G u) ≤ (u * c) * (2 * G (c * u)) := by
      nlinarith only [hweighted, hlo, hfar.1]
    have h := le_of_mul_le_mul_left hprod (mul_pos hu hc)
    nlinarith only [h]
  · have hweighted := mul_le_mul_of_nonneg_right hbase.1 (Real.rpow_nonneg hc.le (3 + ε))
    rw [hsplithi] at hhi hweighted
    have hprod : (u * c) * G (c * u) ≤ (u * c) * (2 * c ^ (2 + ε) * G u) := by
      nlinarith only [hweighted, hhi, hfar.2]
    exact le_of_mul_le_mul_left hprod (mul_pos hu hc)

private theorem summable_cubic_exponential_steps :
    Summable (fun k : ℕ => Real.exp (-1) ^ k * ((k : ℝ) + 1) ^ 3) := by
  have hq : ‖Real.exp (-1)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hq
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hq
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hq
  have h3 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hq
  exact (((h3.add (h2.mul_left 3)).add (h1.mul_left 3)).add h0).congr fun k => by ring

/-- Exponential damping in the logarithmic variable, including the harmless zero term. -/
def logarithmicLaplaceTerm (g : ℕ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  g n / n * Real.exp (-(Real.log n / u))

private theorem sum_logarithmicLaplaceTerm_le {g : ℕ → ℝ}
    (hg : ∀ n, 0 ≤ g n) {u B : ℝ} (hu : 0 < u) (hB : 0 ≤ B)
    (hbound : ∀ k : ℕ, realLogHarmonicSum g (((k : ℝ) + 1) * u) ≤
      B * ((k : ℝ) + 1) ^ 3) (s : Finset ℕ) :
    ∑ n ∈ s, logarithmicLaplaceTerm g u n ≤
      B * ∑' k : ℕ, Real.exp (-1) ^ k * ((k : ℝ) + 1) ^ 3 := by
  let q := Real.exp (-1)
  let M := s.sup (fun n => ⌊Real.log n / u⌋₊) + 1
  let H (k : ℕ) := Icc 1 ⌊Real.exp (((k : ℝ) + 1) * u)⌋₊
  let f (k n : ℕ) := if n ∈ H k then q ^ k * (g n / n) else 0
  have hf (k n : ℕ) : 0 ≤ f k n := by
    dsimp only [f]
    split_ifs
    · exact mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (div_nonneg (hg n) (Nat.cast_nonneg n))
    · exact le_rfl
  have hcover (n : ℕ) (hn : n ∈ s) : logarithmicLaplaceTerm g u n ≤
      ∑ k ∈ range M, f k n := by
    by_cases hn0 : n = 0
    · subst n
      simp only [logarithmicLaplaceTerm, Nat.cast_zero, div_zero, zero_mul]
      exact sum_nonneg fun k _ => hf k 0
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    let k := ⌊Real.log n / u⌋₊
    have hkM : k ∈ range M := by
      apply mem_range.mpr
      change ⌊Real.log n / u⌋₊ < s.sup (fun m : ℕ => ⌊Real.log m / u⌋₊) + 1
      exact Nat.lt_succ_of_le (Finset.le_sup (f := fun m : ℕ => ⌊Real.log m / u⌋₊) hn)
    have hklo : (k : ℝ) ≤ Real.log n / u :=
      Nat.floor_le (div_nonneg (Real.log_natCast_nonneg n) hu.le)
    have hkhi : Real.log n / u < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hnH : n ∈ H k := by
      refine mem_Icc.mpr ⟨hn1, (Nat.le_floor_iff (Real.exp_pos _).le).mpr ?_⟩
      apply (Real.log_le_iff_le_exp hnr).mp
      exact (div_le_iff₀ hu).mp hkhi.le
    have hexp : Real.exp (-(Real.log n / u)) ≤ q ^ k := by
      have heq : q ^ k = Real.exp (-(k : ℝ)) := by
        rw [show -(k : ℝ) = (k : ℝ) * (-1) by ring, Real.exp_nat_mul]
      rw [heq]
      exact Real.exp_le_exp.mpr (neg_le_neg hklo)
    calc
      _ ≤ q ^ k * (g n / n) := by
        simpa only [logarithmicLaplaceTerm, mul_comm] using mul_le_mul_of_nonneg_left hexp
          (div_nonneg (hg n) (Nat.cast_nonneg n))
      _ = f k n := by simp only [f, if_pos hnH]
      _ ≤ _ := single_le_sum (fun j _ => hf j n) hkM
  have hsum (k : ℕ) : (∑ n ∈ s, f k n) ≤ q ^ k * realLogHarmonicSum g (((k : ℝ) + 1) * u) := by
    change (∑ n ∈ s, if n ∈ H k then q ^ k * (g n / n) else 0) ≤
      q ^ k * ∑ n ∈ H k, g n / n
    rw [← sum_filter, mul_sum]
    exact sum_le_sum_of_subset_of_nonneg (fun n hn => (mem_filter.mp hn).2)
      (fun n _ _ => mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (div_nonneg (hg n) (Nat.cast_nonneg n)))
  have hmajor := summable_cubic_exponential_steps.mul_left B
  calc
    _ ≤ ∑ n ∈ s, ∑ k ∈ range M, f k n := sum_le_sum hcover
    _ = ∑ k ∈ range M, ∑ n ∈ s, f k n := sum_comm
    _ ≤ ∑ k ∈ range M, B * (q ^ k * ((k : ℝ) + 1) ^ 3) := by
      apply sum_le_sum
      intro k _
      exact (hsum k).trans ((mul_le_mul_of_nonneg_left (hbound k)
        (pow_nonneg (Real.exp_pos _).le k)).trans_eq (by ring))
    _ ≤ ∑' k : ℕ, B * (q ^ k * ((k : ℝ) + 1) ^ 3) :=
      Summable.sum_le_tsum _ (fun k _ => by positivity) hmajor
    _ = _ := tsum_mul_left

/-- At zero prime density the positive divisor Dirichlet series is bounded by its
truncated harmonic mean, uniformly as the real argument tends to one from above. -/
theorem exists_positiveDivisorMean_laplace_comparison (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    ∃ C U : ℝ, 0 < C ∧ 1 ≤ U ∧ ∀ u : ℝ, U ≤ u →
      Summable (logarithmicLaplaceTerm (signDivisorCount (primeSetFlip P)) u) ∧
      (∑' n : ℕ, logarithmicLaplaceTerm (signDivisorCount (primeSetFlip P)) u n) ≤
        C * realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u := by
  let A := ∑' k : ℕ, Real.exp (-1) ^ k * ((k : ℝ) + 1) ^ 3
  have hA : 1 ≤ A := by
    have h := Summable.sum_le_tsum ({0} : Finset ℕ)
      (fun k _ => by positivity) summable_cubic_exponential_steps
    simpa only [sum_singleton, Nat.cast_zero, pow_zero, zero_add, one_pow, mul_one] using h
  obtain ⟨U, hU, hscale⟩ := exists_positiveDivisorMean_uniform_power_comparison P hP
    (show (0 : ℝ) < 1 by norm_num)
  refine ⟨2 * A, U, by linarith only [hA], hU, fun u huU => ?_⟩
  have hu1 : 1 ≤ u := hU.trans huU
  have hu : 0 < u := zero_lt_one.trans_le hu1
  let g := signDivisorCount (primeSetFlip P)
  have hg : ∀ n, 0 ≤ g n := signDivisorCount_nonneg (primeSetFlip_isSignGauge P)
  have hG : 0 ≤ realLogHarmonicSum g u := by
    exact zero_le_one.trans
      (one_le_realLogHarmonicSum_signDivisorCount (primeSetFlip_isSignGauge P) hu.le)
  have hbound (k : ℕ) : realLogHarmonicSum g (((k : ℝ) + 1) * u) ≤
      (2 * realLogHarmonicSum g u) * ((k : ℝ) + 1) ^ 3 := by
    have h := (hscale u ((k : ℝ) + 1) huU
      (le_add_of_nonneg_left (Nat.cast_nonneg k))).2
    rw [show (2 : ℝ) + 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    change realLogHarmonicSum g (((k : ℝ) + 1) * u) ≤
      2 * ((k : ℝ) + 1) ^ (3 : ℕ) * realLogHarmonicSum g u at h
    exact h.trans_eq (by ring)
  have hfinite (s : Finset ℕ) : (∑ n ∈ s, logarithmicLaplaceTerm g u n) ≤
      (2 * A) * realLogHarmonicSum g u :=
    (sum_logarithmicLaplaceTerm_le hg hu (by positivity) hbound s).trans_eq (by ring)
  have hnonneg (n : ℕ) : 0 ≤ logarithmicLaplaceTerm g u n :=
    mul_nonneg (div_nonneg (hg n) (Nat.cast_nonneg n)) (Real.exp_pos _).le
  exact ⟨summable_of_sum_le hnonneg hfinite, Real.tsum_le_of_sum_le hnonneg hfinite⟩

end GaloisForLFunctions.RenormalizedIntersectionTheory

