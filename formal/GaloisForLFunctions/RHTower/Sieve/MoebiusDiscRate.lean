import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusTwistRate
import GaloisForLFunctions.RHTower.Sieve.CofactorLowFreqBound

/-!
# The Möbius polynomial on the low-frequency disc

Near zero frequency every prime block of every ladder is essentially its own cardinality, so no
frequency partition helps there.  What does help is that the disc is **short**: the Route-T twisted
Möbius bound holds at every frequency below the length of the sum, so on a disc of bounded radius
the mean square is the pointwise bound squared times the length of the disc.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- A twisted Möbius initial sum is the same over `range (m+1)` and over `Icc 1 m`. -/
theorem sum_range_moebiusTwist_eq_Icc (τ : ℝ) (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), moebiusTwist τ n = ∑ n ∈ Finset.Icc 1 m, moebiusTwist τ n := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    omega
  · intro n hn hn2
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc] at hn2
    have hn0 : n = 0 := by omega
    subst hn0
    exact moebiusTwist_zero τ

/-- **The Möbius mean square over a disc of bounded radius.**  Route T at every frequency below the
length of the sum, integrated over a set of measure `2w₀`. -/
theorem exists_setIntegral_disc_normSq_logPoly_moebius_le_rate :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℝ in Filter.atTop, ∀ w₀ : ℝ, 0 ≤ w₀ → 2 * Real.pi * w₀ ≤ N →
      (∫ w in Set.Icc (-w₀) w₀, ‖logPoly moebiusCoeff (Finset.Icc 1 ⌊N⌋₊) w‖ ^ 2)
        ≤ 2 * w₀ * (K * N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 20)))) ^ 2 := by
  obtain ⟨K, hK, hmain⟩ := exists_norm_sum_moebiusTwist_le_rate
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmain] with N hN
  intro w₀ hw₀ hle
  set C : ℝ := K * N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 20))) with hC
  have hC0 : 0 ≤ C := by
    have hN0 : (0 : ℝ) ≤ N := le_trans (by positivity) hle
    rw [hC]; positivity
  have hpt : ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly moebiusCoeff (Finset.Icc 1 ⌊N⌋₊) w‖ ^ 2 ≤ C ^ 2 := by
    intro w hw
    rw [Set.mem_Icc] at hw
    have habs : |(-(2 * Real.pi * w))| ≤ N := by
      rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      have : |w| ≤ w₀ := abs_le.2 ⟨hw.1, hw.2⟩
      have h2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      calc 2 * Real.pi * |w| ≤ 2 * Real.pi * w₀ := by nlinarith
        _ ≤ N := hle
    have hval := hN (-(2 * Real.pi * w)) habs
    rw [sum_range_moebiusTwist_eq_Icc] at hval
    have heq : logPoly moebiusCoeff (Finset.Icc 1 ⌊N⌋₊) w
        = ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, moebiusTwist (-(2 * Real.pi * w)) n :=
      logPoly_moebiusCoeff_eq_sum_moebiusTwist _ w
    rw [heq]
    exact pow_le_pow_left₀ (norm_nonneg _) hval 2
  have hcont : Continuous fun w : ℝ => ‖logPoly moebiusCoeff (Finset.Icc 1 ⌊N⌋₊) w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  have hint : IntegrableOn (fun w : ℝ => ‖logPoly moebiusCoeff (Finset.Icc 1 ⌊N⌋₊) w‖ ^ 2)
      (Set.Icc (-w₀) w₀) volume := hcont.integrableOn_Icc
  have hintC : IntegrableOn (fun _ : ℝ => C ^ 2) (Set.Icc (-w₀) w₀) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hmono := setIntegral_mono_on hint hintC measurableSet_Icc hpt
  have hvol : (volume.real (Set.Icc (-w₀) w₀)) = 2 * w₀ := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ w₀ - -w₀)]
    ring
  rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul] at hmono
  exact hmono

/-- **The disc bound at the fibre index set.**  Specialising the length to `√x + h`, which is what
the fibre index set truncates. -/
theorem exists_eventually_setIntegral_disc_fibre_le {hh : ℝ → ℝ}
    (hh0 : ∀ᶠ x : ℝ in Filter.atTop, 0 ≤ hh x) {w₀ : ℝ} (hw₀ : 0 ≤ w₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
      (∫ w in Set.Icc (-w₀) w₀,
          ‖logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
            (Finset.Icc 1 ⌊Real.sqrt x + hh x⌋₊) w‖ ^ 2)
        ≤ 2 * w₀ * (K * (Real.sqrt x + hh x)
            * Real.exp (-((Real.log (Real.sqrt x + hh x)) ^ ((1 : ℝ) / 20)))) ^ 2 := by
  obtain ⟨K, hK, hmain⟩ := exists_setIntegral_disc_normSq_logPoly_moebius_le_rate
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hmain
  refine ⟨K, hK, ?_⟩
  set C : ℝ := max (max N₀ (2 * Real.pi * w₀)) 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  filter_upwards [hh0, Filter.eventually_ge_atTop (C ^ 2)] with x hx hxC
  have hsqrt : C ≤ Real.sqrt x := by
    rw [show C = Real.sqrt (C ^ 2) by rw [Real.sqrt_sq hC0]]
    exact Real.sqrt_le_sqrt hxC
  have hN : N₀ ≤ Real.sqrt x + hh x :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (by linarith)
  have hpi : 2 * Real.pi * w₀ ≤ Real.sqrt x + hh x :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (by linarith)
  have hbase := hN₀ (Real.sqrt x + hh x) hN w₀ hw₀ hpi
  exact hbase

/-- **The disc contributes nothing relative to `M²`.**  The Route-T rate beats the constant length
of the disc, and the floor loses at most a factor four. -/
theorem tendsto_discRelative {hh : ℝ → ℝ} (hh0 : ∀ᶠ x : ℝ in Filter.atTop, 0 ≤ hh x)
    {w₀ K : ℝ} (hw₀ : 0 ≤ w₀) :
    Filter.Tendsto (fun x : ℝ =>
        2 * w₀ * (K * (Real.sqrt x + hh x)
            * Real.exp (-((Real.log (Real.sqrt x + hh x)) ^ ((1 : ℝ) / 20)))) ^ 2
          / ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
  have hgto : Filter.Tendsto (fun x : ℝ => (Real.log x / 2) ^ ((1 : ℝ) / 20))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      (Real.tendsto_log_atTop.atTop_div_const (by norm_num))
  have hEto : Filter.Tendsto (fun x : ℝ => Real.exp (-((Real.log x / 2) ^ ((1 : ℝ) / 20))))
      Filter.atTop (nhds 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp hgto
  have hmaj : Filter.Tendsto (fun x : ℝ =>
      8 * w₀ * K ^ 2 * Real.exp (-((Real.log x / 2) ^ ((1 : ℝ) / 20))) ^ 2)
      Filter.atTop (nhds 0) := by
    have := (hEto.pow 2).const_mul (8 * w₀ * K ^ 2)
    simpa using this
  refine squeeze_zero' (g := fun x : ℝ =>
    8 * w₀ * K ^ 2 * Real.exp (-((Real.log x / 2) ^ ((1 : ℝ) / 20))) ^ 2) ?_ ?_ hmaj
  · filter_upwards [hh0, Filter.eventually_ge_atTop (4 : ℝ)] with x hx hx4
    positivity
  · filter_upwards [hh0, Filter.eventually_ge_atTop (4 : ℝ)] with x hx hx4
    set N : ℝ := Real.sqrt x + hh x with hN
    have hs2 : (2 : ℝ) ≤ Real.sqrt x := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hx4
    have hN2 : (2 : ℝ) ≤ N := by rw [hN]; linarith
    have hM : N - 1 ≤ ((⌊N⌋₊ : ℕ) : ℝ) := by
      have := Nat.sub_one_lt_floor N
      linarith
    have hMhalf : N / 2 ≤ ((⌊N⌋₊ : ℕ) : ℝ) := by linarith
    have hM0 : (0 : ℝ) < ((⌊N⌋₊ : ℕ) : ℝ) := by linarith
    have hlogN : Real.log x / 2 ≤ Real.log N := by
      have hsq : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt (by linarith)
      rw [← hsq]
      exact Real.log_le_log (by linarith) (by rw [hN]; linarith)
    have hlog0 : (0 : ℝ) ≤ Real.log x / 2 := by
      have : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
      linarith
    have hrpow : (Real.log x / 2) ^ ((1 : ℝ) / 20) ≤ (Real.log N) ^ ((1 : ℝ) / 20) :=
      Real.rpow_le_rpow hlog0 hlogN (by norm_num)
    have hEle : Real.exp (-((Real.log N) ^ ((1 : ℝ) / 20)))
        ≤ Real.exp (-((Real.log x / 2) ^ ((1 : ℝ) / 20))) := by
      exact Real.exp_le_exp.2 (by linarith)
    have hE0 : (0 : ℝ) ≤ Real.exp (-((Real.log N) ^ ((1 : ℝ) / 20))) := (Real.exp_pos _).le
    set E : ℝ := Real.exp (-((Real.log N) ^ ((1 : ℝ) / 20))) with hEdef
    set E₀ : ℝ := Real.exp (-((Real.log x / 2) ^ ((1 : ℝ) / 20))) with hE₀def
    have hratio : N ^ 2 / ((⌊N⌋₊ : ℕ) : ℝ) ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hMhalf, hM0, hN2]
    have hrw : 2 * w₀ * (K * N * E) ^ 2 / ((⌊N⌋₊ : ℕ) : ℝ) ^ 2
        = 2 * w₀ * K ^ 2 * E ^ 2 * (N ^ 2 / ((⌊N⌋₊ : ℕ) : ℝ) ^ 2) := by
      field_simp
    rw [hrw]
    have hEsq : E ^ 2 ≤ E₀ ^ 2 := by
      have := pow_le_pow_left₀ hE0 hEle 2
      exact this
    have hpos : (0 : ℝ) ≤ 2 * w₀ * K ^ 2 * E ^ 2 := by positivity
    have hstep1 : 2 * w₀ * K ^ 2 * E ^ 2 * (N ^ 2 / ((⌊N⌋₊ : ℕ) : ℝ) ^ 2)
        ≤ 2 * w₀ * K ^ 2 * E ^ 2 * 4 := mul_le_mul_of_nonneg_left hratio hpos
    have hstep2 : 2 * w₀ * K ^ 2 * E ^ 2 * 4 ≤ 8 * w₀ * K ^ 2 * E₀ ^ 2 := by
      have hc : (0 : ℝ) ≤ 8 * w₀ * K ^ 2 := by positivity
      nlinarith [hEsq, hc]
    linarith

end

end RHTower.Sieve
