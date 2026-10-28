import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRobinConstantOfAnAtom
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanCrossKernel
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheStabilityLawAtTheSpacingScale
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadCoherentQuantileGammaNoGo
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover

/-!
# The Markov form fails inside the separated regime

At width `≤ c₀ δ_N` the Markov form `M = archForm − primeSum` is nonnegative on every atomic test
(`TheStabilityLawAtTheSpacingScale`). This file shows that `M` alone fails at every fixed fraction
`c ∈ (e/(2π), 1)` of the spacing, so the rank-one pole correction of the stability law is needed
inside the separated regime, and locates the failure on the pole vector `x_n = n^{−1/2}`.

* **The prime form of the pole vector** (`atomicWeilForm_poleVector`):
  `P_N(n^{−1/2}) = 2 Σ_{n ≤ N} log n / n`, since `Σ_{d ∣ n} Λ(d) = log n`; so
  `P_N ≥ log² N − log² 3` (`atomicWeilForm_poleVector_ge`).
* **Nonnegative separated tests** (`levyEnergy_atomicTest_le`): for `x ≥ 0`, `g ≥ 0` and `w < δ_N`
  the Lévy energy is at most `‖x‖²` times the self-energy: the cross correlations only lower it.
* **The archimedean Robin constant** (`archRobinConstant_eq`): `2c_∞ = 2 log 2 + π/2`, from the
  closed antiderivative `½ log((1 + e^{−y/2})/(1 − e^{−y/2})) + arctan e^{−y/2}` of the Lévy density.
* **The threshold** (`markovQuad_poleVector_neg_of_threshold`): with `2θ′(0) + γ =
  −(3 log 2 + π/2 + log π)`, the finite part on the pole vector is at most
  `log(1/c) + β(φ)/‖φ‖² − log(2π)` per `log N`, Euler's constant cancelling between `H_N` and `θ′(0)`;
  so `M < 0` for all large `N` once `c > e^{β(φ)/‖φ‖²}/(2π)`.
* **Plateaus** (`exists_plateau_bumpRobin_le`): smooth plateau profiles have `β(φ)/‖φ‖² → 1`, so
  every `c ∈ (e/(2π), 1)` fails (`markov_poleVector_negative_inside_separated`).
-/

noncomputable section

open MeasureTheory Finset Filter Topology RHTower
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics ArithmeticEffectivityTheory
open RHTower.WeilLevyPoleGauss (archLevyAntideriv)

/-! ### The prime form of the pole vector -/

/-- The kernel splits into its two towers. -/
theorem weilPrimeKernel_eq_add (m n : ℕ) :
    weilPrimeKernel m n =
      (if m ∣ n ∧ m ≠ n then ArithmeticFunction.vonMangoldt (n / m) / Real.sqrt ((n / m : ℕ) : ℝ)
        else 0) +
      (if n ∣ m ∧ n ≠ m then ArithmeticFunction.vonMangoldt (m / n) / Real.sqrt ((m / n : ℕ) : ℝ)
        else 0) := by
  unfold weilPrimeKernel
  by_cases h1 : m ∣ n ∧ m ≠ n
  · have h2 : ¬ (n ∣ m ∧ n ≠ m) := fun h => h1.2 (Nat.dvd_antisymm h1.1 h.1)
    rw [if_pos h1, if_pos h1, if_neg h2, add_zero]
  · rw [if_neg h1, if_neg h1, zero_add]

/-- One entry of the pole vector against the up tower: `n^{−1/2} m^{−1/2} Λ(n/m)(n/m)^{−1/2} =
Λ(n/m)/n`. -/
theorem poleVector_upTower {m n : ℕ} (hm : 0 < m) (hmn : m ∣ n) :
    1 / Real.sqrt m * (1 / Real.sqrt n) *
        (ArithmeticFunction.vonMangoldt (n / m) / Real.sqrt ((n / m : ℕ) : ℝ)) =
      ArithmeticFunction.vonMangoldt (n / m) / n := by
  obtain ⟨t, rfl⟩ := hmn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht; simp
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  rw [Nat.mul_div_cancel_left t hm]
  push_cast
  rw [Real.sqrt_mul hm0.le]
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  field_simp
  rw [Real.sq_sqrt hm0.le, Real.sq_sqrt ht0.le]
  ring

/-- `Σ_{m ∣ n, m < n} Λ(n/m) = log n`. -/
theorem sum_properDivisors_vonMangoldt_div {n : ℕ} (hn : 0 < n) :
    ∑ m ∈ n.properDivisors, ArithmeticFunction.vonMangoldt (n / m) = Real.log n := by
  have h : ∑ m ∈ n.divisors, ArithmeticFunction.vonMangoldt (n / m) =
      ∑ m ∈ n.properDivisors, ArithmeticFunction.vonMangoldt (n / m) := by
    rw [← Nat.insert_self_properDivisors hn.ne', sum_insert Nat.self_notMem_properDivisors,
      Nat.div_self hn, ArithmeticFunction.vonMangoldt_apply_one, zero_add]
  rw [← h, Nat.sum_div_divisors n (fun d => ArithmeticFunction.vonMangoldt d),
    ArithmeticFunction.vonMangoldt_sum]

/-- **The prime form of the pole vector**: `P_N(n^{−1/2}) = 2 Σ_{n ≤ N} log n / n`. -/
theorem atomicWeilForm_poleVector (N : ℕ) :
    atomicWeilForm N (fun n => 1 / Real.sqrt n) = 2 * ∑ n ∈ Icc 1 N, Real.log n / n := by
  set A : ℕ → ℕ → ℝ := fun m n => if m ∣ n ∧ m ≠ n then
    ArithmeticFunction.vonMangoldt (n / m) / Real.sqrt ((n / m : ℕ) : ℝ) else 0
  set x : ℕ → ℝ := fun n => 1 / Real.sqrt n
  have hsplit : atomicWeilForm N x = 2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * A m n := by
    unfold atomicWeilForm
    simp_rw [weilPrimeKernel_eq_add, mul_add, sum_add_distrib]
    rw [sum_comm (f := fun m n => x m * x n * A n m)]
    simp only [A]
    rw [two_mul]
    congr 1
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    ring
  rw [hsplit, sum_comm]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  have hn1 := (mem_Icc.mp hn)
  have hn0 : 0 < n := by omega
  have hrow : ∀ m ∈ Icc 1 N, x m * x n * A m n =
      if m ∈ n.properDivisors then ArithmeticFunction.vonMangoldt (n / m) / n else 0 := by
    intro m hm
    have hm0 : 0 < m := by have := (mem_Icc.mp hm).1; omega
    simp only [A, x, Nat.mem_properDivisors]
    by_cases h : m ∣ n ∧ m ≠ n
    · have hlt : m < n := lt_of_le_of_ne (Nat.le_of_dvd hn0 h.1) h.2
      rw [if_pos h, if_pos ⟨h.1, hlt⟩]
      exact poleVector_upTower hm0 h.1
    · have h' : ¬ (m ∣ n ∧ m < n) := fun h' => h ⟨h'.1, h'.2.ne⟩
      rw [if_neg h, if_neg h', mul_zero]
  rw [sum_congr rfl hrow, ← sum_filter]
  have hfilt : (Icc 1 N).filter (fun m => m ∈ n.properDivisors) = n.properDivisors := by
    ext m
    simp only [mem_filter, mem_Icc, and_iff_right_iff_imp]
    intro hm
    have := Nat.mem_properDivisors.mp hm
    have hm0 : 0 < m := Nat.pos_of_dvd_of_pos this.1 hn0
    omega
  rw [hfilt, ← sum_div, sum_properDivisors_vonMangoldt_div hn0]

/-- `Σ_{n ≤ N} log n / n ≥ (log² N − log² 3)/2` for `N ≥ 3`, by comparison with `∫ log t / t`. -/
theorem sum_log_div_ge {N : ℕ} (hN : 3 ≤ N) :
    (Real.log N ^ 2 - Real.log 3 ^ 2) / 2 ≤ ∑ n ∈ Icc 1 N, Real.log n / n := by
  have hanti : AntitoneOn (fun t : ℝ => Real.log t / t) (Set.Icc 3 (3 + ((N - 3 : ℕ) : ℝ))) :=
    Real.log_div_self_antitoneOn.mono fun t ht => by
      have : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
      show Real.exp 1 ≤ t
      linarith [ht.1]
  have h := hanti.integral_le_sum
  have hN3 : (3 : ℝ) + ((N - 3 : ℕ) : ℝ) = N := by
    rw [Nat.cast_sub hN]; push_cast; ring
  rw [hN3] at h
  -- the integral of `log t / t`
  have hint : ∫ t in (3 : ℝ)..N, Real.log t / t = (Real.log N ^ 2 - Real.log 3 ^ 2) / 2 := by
    have hderiv : ∀ t ∈ Set.uIcc (3 : ℝ) N, HasDerivAt (fun t => Real.log t * Real.log t / 2)
        (Real.log t / t) t := by
      intro t ht
      have ht0 : 0 < t := by
        rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1, (show (3 : ℝ) ≤ N by exact_mod_cast hN)]
      refine (((Real.hasDerivAt_log ht0.ne').mul (Real.hasDerivAt_log ht0.ne')).div_const 2).congr_deriv
        ?_
      field_simp
      ring
    have hcont : ContinuousOn (fun t : ℝ => Real.log t / t) (Set.uIcc 3 N) := by
      refine ContinuousOn.div (Real.continuousOn_log.mono fun t ht => ?_) continuousOn_id
        fun t ht => ?_
      · rcases Set.mem_uIcc.mp ht with h | h <;>
          exact ne_of_gt (by linarith [h.1, (show (3 : ℝ) ≤ N by exact_mod_cast hN)])
      · rcases Set.mem_uIcc.mp ht with h | h <;>
          exact ne_of_gt (by linarith [h.1, (show (3 : ℝ) ≤ N by exact_mod_cast hN)])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
    ring
  rw [hint] at h
  refine h.trans ?_
  -- the left Riemann sum is part of the full sum
  have hsub : ∑ i ∈ range (N - 3), Real.log (3 + (i : ℝ)) / (3 + (i : ℝ)) =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => 3 ≤ n ∧ n < N), Real.log n / n := by
    refine sum_nbij' (fun i : ℕ => i + 3) (fun n : ℕ => n - 3) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      simp only [Finset.mem_range]
      omega
    · intro i _; simp
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      omega
    · intro i _; push_cast; ring_nf
  rw [hsub]
  refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n hn _ => ?_
  exact div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)

/-- `P_N(n^{−1/2}) ≥ log² N − log² 3`. -/
theorem atomicWeilForm_poleVector_ge {N : ℕ} (hN : 3 ≤ N) :
    Real.log N ^ 2 - Real.log 3 ^ 2 ≤ atomicWeilForm N (fun n => 1 / Real.sqrt n) := by
  rw [atomicWeilForm_poleVector]
  linarith [sum_log_div_ge hN]

/-- `Σ_{n ≤ N} (n^{−1/2})² = H_N`. -/
theorem sum_poleVector_sq (N : ℕ) :
    ∑ n ∈ Icc 1 N, (1 / Real.sqrt n) ^ 2 = ∑ n ∈ Icc 1 N, (1 : ℝ) / n := by
  refine sum_congr rfl fun n _ => ?_
  rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-! ### Nonnegative separated tests -/

variable {g : ℝ → ℝ} {w : ℝ}

theorem bumpCorr_nonneg (hg0 : ∀ u, 0 ≤ g u) (t : ℝ) : 0 ≤ bumpCorr g t :=
  integral_nonneg fun v => mul_nonneg (hg0 v) (hg0 (v + t))

/-- **The cross correlations lower the Lévy energy**: for `x ≥ 0`, `g ≥ 0` and `w < δ_N`,
`levyEnergy f_x ≤ ‖x‖² levyEnergy g`. -/
theorem levyEnergy_atomicTest_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hg0 : ∀ u, 0 ≤ g u) {N : ℕ}
    (hw : w < atomSpacing N) (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n) :
    levyEnergy (atomicTest N x g) ≤ (∑ n ∈ Icc 1 N, x n ^ 2) * levyEnergy g := by
  set X := ∑ n ∈ Icc 1 N, x n ^ 2
  have hf : ContDiff ℝ 2 (atomicTest N x g) := contDiff_atomicTest hg N x
  have hfc : HasCompactSupport (atomicTest N x g) := hasCompactSupport_atomicTest hgsupp N x
  -- the windowed bound, shift by shift
  have hQ : ∀ y, ∫ u, (atomicTest N x g u - atomicTest N x g (u + y)) ^ 2 ≤
      X * ∫ u, (g u - g (u + y)) ^ 2 := by
    intro y
    rw [integral_sub_shift_sq_eq hf.continuous hfc, integral_sub_shift_sq_eq hg.continuous hgc,
      integral_atomicTest_sq hg hgc hgsupp hw, integral_atomicTest_mul_shift hg.continuous hgc]
    have hdiag : X * bumpCorr g y ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        x m * x n * bumpCorr g (y - (Real.log n - Real.log m)) := by
      simp only [X, sum_mul]
      refine sum_le_sum fun m hm => ?_
      rw [← add_sum_erase _ _ hm, sub_self, sub_zero, ← sq]
      have : 0 ≤ ∑ n ∈ (Icc 1 N).erase m, x m * x n * bumpCorr g (y - (Real.log n - Real.log m)) :=
        sum_nonneg fun n _ => mul_nonneg (mul_nonneg (hx m) (hx n)) (bumpCorr_nonneg hg0 _)
      linarith
    have : bumpCorr g y = ∫ u, g u * g (u + y) := rfl
    rw [← this]
    nlinarith
  unfold levyEnergy
  rw [← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_levyIntegrand hf hfc)
    ((integrableOn_levyIntegrand hg hgc).const_mul X) measurableSet_Ioi fun y hy => ?_
  have hω : 0 ≤ archLevyDensity y := (archLevyDensity_pos hy).le
  calc archLevyDensity y * ∫ u, (atomicTest N x g u - atomicTest N x g (u + y)) ^ 2
      ≤ archLevyDensity y * (X * ∫ u, (g u - g (u + y)) ^ 2) := mul_le_mul_of_nonneg_left (hQ y) hω
    _ = X * (archLevyDensity y * ∫ u, (g u - g (u + y)) ^ 2) := by ring

/-! ### The archimedean Robin constant -/

/-- The finite part of the antiderivative at `0`: `A(ε) − ½ log(1/ε) → log 2 + π/4`. -/
theorem tendsto_archLevyAntideriv_sub_log :
    Tendsto (fun ε : ℝ => archLevyAntideriv ε - 1 / 2 * Real.log (1 / ε)) (𝓝[>] 0)
      (𝓝 (Real.log 2 + π / 4)) := by
  -- the slope of `1 − e^{−x/2}` at `0`
  have hd : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x / 2)) (1 / 2) 0 := by
    have := ((Real.hasDerivAt_exp (-(0 : ℝ) / 2)).comp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).neg.div_const 2)).const_sub 1
    refine this.congr_deriv ?_
    norm_num
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono _ fun x (hx : 0 < x) => ne_of_gt hx)
  have hq : Tendsto (fun ε : ℝ => (1 - Real.exp (-ε / 2)) / ε) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    refine hslope.congr' (Filter.Eventually.of_forall fun ε => ?_)
    simp [slope_def_field]
  have hexp : Tendsto (fun ε : ℝ => Real.exp (-ε / 2)) (𝓝[>] 0) (𝓝 1) := by
    have : Continuous fun ε : ℝ => Real.exp (-ε / 2) := by fun_prop
    simpa using this.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
  have hratio : Tendsto (fun ε : ℝ => (1 + Real.exp (-ε / 2)) / ((1 - Real.exp (-ε / 2)) / ε))
      (𝓝[>] 0) (𝓝 4) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add hexp).div hq (by norm_num)
    rw [show (4 : ℝ) = (1 + 1) / (1 / 2) by norm_num]
    exact this
  have hlog := (Real.continuousAt_log (by norm_num : (4 : ℝ) ≠ 0)).tendsto.comp hratio
  have hatan := (Real.continuous_arctan.tendsto 1).comp hexp
  have hlim := (hlog.const_mul (1 / 2)).add hatan
  rw [Real.arctan_one, show (1 : ℝ) / 2 * Real.log 4 = Real.log 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have he1 : Real.exp (-ε / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hp : 0 < 1 - Real.exp (-ε / 2) := by linarith
  have hq0 : 0 < 1 + Real.exp (-ε / 2) := by positivity
  simp only [Function.comp, archLevyAntideriv]
  have hl : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
  rw [hl, div_div_eq_mul_div, Real.log_div (by positivity) hp.ne', Real.log_mul hq0.ne' hε.ne']
  ring

/-- **The archimedean Robin constant**: `2c_∞ = 2 log 2 + π/2`. -/
theorem archRobinConstant_eq : archRobinConstant = 2 * Real.log 2 + π / 2 := by
  set r := levyRegularPart
  have hA1 : ∫ y in Set.Ioi (1 : ℝ), archLevyDensity y = archLevyAntideriv 1 :=
    WeilLevyCoshCrossover.integral_archLevyDensity_Ioi one_pos
  -- `∫_ε^1 r = A(ε) − A(1) − ½ log(1/ε)`
  have hpart : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∫ y in ε..1, r y =
      archLevyAntideriv ε - archLevyAntideriv 1 - 1 / 2 * Real.log (1 / ε) := by
    intro ε hε hε1
    have hωi : IntegrableOn archLevyDensity (Set.Ioc ε 1) :=
      (WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hε).mono_set Set.Ioc_subset_Ioi_self
    have hinv : IntervalIntegrable (fun y : ℝ => y⁻¹) volume ε 1 :=
      (continuousOn_inv₀.mono fun y hy => by
        rcases Set.mem_uIcc.mp hy with h | h <;> exact ne_of_gt (by linarith [h.1])).intervalIntegrable
    have hω : ∫ y in ε..1, archLevyDensity y = archLevyAntideriv ε - archLevyAntideriv 1 := by
      rw [intervalIntegral.integral_of_le hε1, ← WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hε,
        ← hA1, ← Set.Ioc_union_Ioi_eq_Ioi hε1, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
          measurableSet_Ioi hωi (WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi one_pos)]
      ring
    have hsplit : ∫ y in ε..1, r y = (∫ y in ε..1, archLevyDensity y) - ∫ y in ε..1, (1 / 2) * y⁻¹ := by
      rw [← intervalIntegral.integral_sub ((intervalIntegrable_iff_integrableOn_Ioc_of_le hε1).mpr hωi)
        (hinv.const_mul _)]
      refine intervalIntegral.integral_congr fun y hy => ?_
      simp only [r, levyRegularPart]
      field_simp
    rw [hsplit, hω, intervalIntegral.integral_const_mul, integral_inv_of_pos hε one_pos]
  -- `∫_0^1 r` is the limit of `∫_ε^1 r`
  have hrint : IntegrableOn r (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one, integrableOn_Icc_iff_integrableOn_Ioc]
    exact integrableOn_levyRegularPart le_rfl
  have hcont := intervalIntegral.continuousOn_primitive_interval_left hrint
  have hlim0 : Tendsto (fun ε => ∫ y in ε..1, r y) (𝓝[>] 0) (𝓝 (∫ y in (0 : ℝ)..1, r y)) := by
    have := (hcont 0 (by simp)).tendsto
    refine this.mono_left (nhdsWithin_le_of_mem ?_)
    rw [Set.uIcc_of_le zero_le_one]
    exact mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, by norm_num,
      fun x hx => ⟨le_of_lt hx.2, le_of_lt hx.1⟩⟩
  have hlim1 : Tendsto (fun ε => ∫ y in ε..1, r y) (𝓝[>] 0)
      (𝓝 (Real.log 2 + π / 4 - archLevyAntideriv 1)) := by
    have := tendsto_archLevyAntideriv_sub_log.sub_const (archLevyAntideriv 1)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds one_pos)] with ε
      (hε : 0 < ε) hε1
    rw [hpart ε hε hε1.le]
    ring
  have heq := tendsto_nhds_unique hlim0 hlim1
  unfold archRobinConstant
  rw [← intervalIntegral.integral_of_le zero_le_one, heq, hA1]
  ring

/-! ### Plateau profiles -/

/-- The smooth transition is Lipschitz: it agrees, after clamping to `[0, 1]`, with a compactly
supported `C²` function. -/
theorem exists_lipschitz_smoothTransition : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ,
    |Real.smoothTransition a - Real.smoothTransition b| ≤ C * |a - b| := by
  set h : ℝ → ℝ := fun x => Real.smoothTransition x * Real.smoothTransition (3 - x)
  have hh : ContDiff ℝ 2 h := Real.smoothTransition.contDiff.mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))
  have hhc : HasCompactSupport h :=
    HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 3)) fun x hx => by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · simp [h, Real.smoothTransition.zero_of_nonpos hx.le]
      · simp [h, Real.smoothTransition.zero_of_nonpos (by linarith : 3 - x ≤ 0)]
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hhc hh (by norm_num)
  refine ⟨C, C.2, fun a b => ?_⟩
  set cl : ℝ → ℝ := fun x => max (min x 1) 0
  have hcl : ∀ x, Real.smoothTransition x = h (cl x) := fun x => by
    have hle : max (min x 1) 0 ≤ 1 := max_le (min_le_right _ _) zero_le_one
    have h3 : Real.smoothTransition (3 - max (min x 1) 0) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith)
    simp only [h, cl]
    rw [h3, mul_one]
    rcases le_or_gt x 0 with hx | hx
    · rw [Real.smoothTransition.zero_of_nonpos hx, max_eq_right (min_le_of_left_le hx),
        Real.smoothTransition.zero_of_nonpos le_rfl]
    · rcases le_or_gt 1 x with hx1 | hx1
      · rw [Real.smoothTransition.one_of_one_le hx1, min_eq_right hx1, max_eq_left zero_le_one,
          Real.smoothTransition.one_of_one_le le_rfl]
      · rw [min_eq_left hx1.le, max_eq_left hx.le]
  have hclip : ∀ x y, |cl x - cl y| ≤ |x - y| := fun x y =>
    (abs_max_sub_max_le_abs _ _ _).trans ((abs_min_sub_min_le_max _ _ _ _).trans (by simp))
  rw [hcl a, hcl b]
  calc |h (cl a) - h (cl b)| ≤ C * |cl a - cl b| := by
        simpa [Real.dist_eq] using hC.dist_le_mul (cl a) (cl b)
    _ ≤ C * |a - b| := mul_le_mul_of_nonneg_left (hclip a b) C.2

/-- The **plateau profile**: `1` on `[η, 1 − η]`, `0` off `[0, 1]`, smooth. -/
def plateau (η u : ℝ) : ℝ := Real.smoothTransition (u / η) * Real.smoothTransition ((1 - u) / η)

section Plateau

variable {η : ℝ}

theorem contDiff_plateau (η : ℝ) : ContDiff ℝ 2 (plateau η) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.div_const η)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const η))

theorem plateau_nonneg (u : ℝ) : 0 ≤ plateau η u :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem plateau_le_one (u : ℝ) : plateau η u ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem plateau_eq_zero (hη : 0 < η) {u : ℝ} (hu : u ∉ Set.Icc 0 1) : plateau η u = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  unfold plateau
  rcases hu with hu | hu
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hu.le hη.le), zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (x := (1 - u) / η)
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le), mul_zero]

theorem plateau_eq_one (hη : 0 < η) {u : ℝ} (hu : u ∈ Set.Icc η (1 - η)) : plateau η u = 1 := by
  unfold plateau
  rw [Real.smoothTransition.one_of_one_le ((one_le_div hη).mpr hu.1),
    Real.smoothTransition.one_of_one_le ((one_le_div hη).mpr (by linarith [hu.2])), mul_one]

theorem hasCompactSupport_plateau (hη : 0 < η) : HasCompactSupport (plateau η) :=
  HasCompactSupport.intro isCompact_Icc fun _ hu => plateau_eq_zero hη hu

/-- The plateau is `2C/η`-Lipschitz. -/
theorem abs_plateau_sub_le {C : ℝ} (hC : ∀ a b : ℝ,
    |Real.smoothTransition a - Real.smoothTransition b| ≤ C * |a - b|) (hη : 0 < η) (u v : ℝ) :
    |plateau η u - plateau η v| ≤ 2 * C / η * |u - v| := by
  unfold plateau
  set a := Real.smoothTransition (u / η)
  set b := Real.smoothTransition ((1 - u) / η)
  set c := Real.smoothTransition (v / η)
  set d := Real.smoothTransition ((1 - v) / η)
  have h1 : |a - c| ≤ C * |u - v| / η := by
    have := hC (u / η) (v / η)
    rwa [← sub_div, abs_div, abs_of_pos hη, mul_div_assoc'] at this
  have h2 : |b - d| ≤ C * |u - v| / η := by
    have := hC ((1 - u) / η) ((1 - v) / η)
    rwa [← sub_div, abs_div, abs_of_pos hη, show 1 - u - (1 - v) = -(u - v) by ring, abs_neg,
      mul_div_assoc'] at this
  have hb : |b| ≤ 1 := by rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact
    Real.smoothTransition.le_one _
  have hc : |c| ≤ 1 := by rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact
    Real.smoothTransition.le_one _
  calc |a * b - c * d| = |(a - c) * b + c * (b - d)| := by ring_nf
    _ ≤ |a - c| * |b| + |c| * |b - d| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ C * |u - v| / η * 1 + 1 * (C * |u - v| / η) :=
        add_le_add (mul_le_mul h1 hb (abs_nonneg _) ((abs_nonneg _).trans h1))
          (mul_le_mul hc h2 (abs_nonneg _) zero_le_one)
    _ = 2 * C / η * |u - v| := by ring

theorem integral_plateau_eq_setIntegral (hη : 0 < η) (F : ℝ → ℝ) (hF : F 0 = 0) :
    ∫ u, F (plateau η u) = ∫ u in Set.Icc 0 1, F (plateau η u) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
    rw [plateau_eq_zero hη hu, hF]).symm

theorem setIntegral_Icc_zero_one_one : ∫ _ in Set.Icc (0 : ℝ) 1, (1 : ℝ) = 1 := by
  simp

theorem integral_plateau_sq_le (hη : 0 < η) : ∫ u, plateau η u ^ 2 ≤ 1 := by
  rw [integral_plateau_eq_setIntegral hη (fun z => z ^ 2) (by norm_num)]
  have hi1 : IntegrableOn (fun u => plateau η u ^ 2) (Set.Icc 0 1) :=
    ((contDiff_plateau η).continuous.pow 2).integrableOn_Icc
  have hi2 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 1) := continuous_const.integrableOn_Icc
  have := setIntegral_mono_on hi1 hi2 measurableSet_Icc fun u _ => by
    have := plateau_le_one (η := η) u
    have := plateau_nonneg (η := η) u
    nlinarith
  rwa [setIntegral_Icc_zero_one_one] at this

theorem integral_abs_plateau_le (hη : 0 < η) : ∫ u, |plateau η u| ≤ 1 := by
  rw [integral_plateau_eq_setIntegral hη (fun z => |z|) (by norm_num)]
  have hi1 : IntegrableOn (fun u => |plateau η u|) (Set.Icc 0 1) :=
    ((contDiff_plateau η).continuous.abs).integrableOn_Icc
  have hi2 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 1) := continuous_const.integrableOn_Icc
  have := setIntegral_mono_on hi1 hi2 measurableSet_Icc fun u _ => by
    rw [abs_of_nonneg (plateau_nonneg u)]; exact plateau_le_one u
  rwa [setIntegral_Icc_zero_one_one] at this

/-- On `[a, b]` where a nonnegative integrand is `1`, its integral is at least `b − a`. -/
theorem le_integral_of_eq_one_on {f : ℝ → ℝ} (hf : Integrable f) (hf0 : ∀ u, 0 ≤ f u)
    {a b : ℝ} (hab : a ≤ b) (h1 : ∀ u ∈ Set.Icc a b, f u = 1) : b - a ≤ ∫ u, f u := by
  have hset : ∫ u in Set.Icc a b, f u = b - a := by
    rw [setIntegral_congr_fun measurableSet_Icc h1]
    simp [hab]
  rw [← hset]
  exact setIntegral_le_integral hf (Filter.Eventually.of_forall hf0)

theorem integral_plateau_sq_ge (hη : 0 < η) (hη2 : η ≤ 1 / 2) : 1 - 2 * η ≤ ∫ u, plateau η u ^ 2 := by
  have := le_integral_of_eq_one_on (f := fun u => plateau η u ^ 2)
    (integrable_sq_of_continuous (contDiff_plateau η).continuous (hasCompactSupport_plateau hη))
    (fun u => sq_nonneg _) (a := η) (b := 1 - η) (by linarith) fun u hu => by
      rw [plateau_eq_one hη hu, one_pow]
  linarith

theorem integral_plateau_mul_shift_ge (hη : 0 < η) {y : ℝ} (hy : 0 ≤ y) :
    1 - 2 * η - y ≤ ∫ u, plateau η u * plateau η (u + y) := by
  have hint : Integrable fun u => plateau η u * plateau η (u + y) := by
    simpa using integrable_comp_sub_mul_comp_add (contDiff_plateau η).continuous
      (hasCompactSupport_plateau hη) 0 y
  have h0 : 0 ≤ ∫ u, plateau η u * plateau η (u + y) :=
    integral_nonneg fun u => mul_nonneg (plateau_nonneg u) (plateau_nonneg _)
  rcases le_or_gt (1 - η - y) η with h | h
  · linarith
  have := le_integral_of_eq_one_on hint (fun u => mul_nonneg (plateau_nonneg u) (plateau_nonneg _))
    (a := η) (b := 1 - η - y) h.le fun u hu => by
      rw [plateau_eq_one hη ⟨hu.1, by linarith [hu.2]⟩,
        plateau_eq_one hη ⟨by linarith [hu.1], by linarith [hu.2]⟩, one_mul]
  linarith

/-- `‖φ − φ(· + y)‖² ≤ 2y + 4η`. -/
theorem integral_plateau_sub_shift_sq_le (hη : 0 < η) {y : ℝ} (hy : 0 ≤ y) :
    ∫ u, (plateau η u - plateau η (u + y)) ^ 2 ≤ 2 * y + 4 * η := by
  rw [integral_sub_shift_sq_eq (contDiff_plateau η).continuous (hasCompactSupport_plateau hη)]
  linarith [integral_plateau_sq_le hη, integral_plateau_mul_shift_ge hη hy]

/-- **The shape term of a plateau**: `β(φ_η) ≤ 1 + 2Cη − 4η log η`. -/
theorem bumpRobin_plateau_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ a b : ℝ,
    |Real.smoothTransition a - Real.smoothTransition b| ≤ C * |a - b|) (hη : 0 < η) (hη1 : η < 1) :
    bumpRobin (plateau η) 1 ≤ 1 + 2 * C * η - 4 * η * Real.log η := by
  set Q : ℝ → ℝ := fun y => ∫ u, (plateau η u - plateau η (u + y)) ^ 2
  set K := 2 * C / η
  have hK0 : 0 ≤ K := by positivity
  have hQm : StronglyMeasurable Q := by
    have hc : Continuous fun p : ℝ × ℝ => (plateau η p.2 - plateau η (p.2 + p.1)) ^ 2 := by
      have := (contDiff_plateau η).continuous; fun_prop
    exact hc.stronglyMeasurable.integral_prod_right'
  have hQK : ∀ y, 0 < y → Q y / (2 * y) ≤ K := fun y hy => by
    have h1 : Q y ≤ 2 * K * |y| * ∫ u, |plateau η u| :=
      integral_sub_shift_sq_le_lipschitz (contDiff_plateau η).continuous
        (hasCompactSupport_plateau hη) (abs_plateau_sub_le hC hη) y
    have h2 := integral_abs_plateau_le hη
    rw [abs_of_pos hy] at h1
    rw [div_le_iff₀ (by linarith)]
    have h3 : 2 * K * y * (∫ u, |plateau η u|) ≤ 2 * K * y * 1 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hQ0 : ∀ y, 0 ≤ Q y := fun y => integral_nonneg fun u => sq_nonneg _
  have hint : IntegrableOn (fun y => Q y / (2 * y)) (Set.Ioc 0 1) := by
    refine Measure.integrableOn_of_bounded (M := K) (measure_Ioc_lt_top).ne
      ((hQm.measurable.div (measurable_const.mul measurable_id)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hQ0 y) (by linarith [hy.1]))]
    exact hQK y hy.1
  set a := η ^ 2
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by nlinarith
  have hsplit : Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 a ∪ Set.Ioc a 1 :=
    (Set.Ioc_union_Ioc_eq_Ioc ha0.le ha1).symm
  unfold bumpRobin
  rw [hsplit, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (hint.mono_set fun y hy => ⟨hy.1, hy.2.trans ha1⟩)
    (hint.mono_set fun y hy => ⟨lt_trans ha0 hy.1, hy.2⟩)]
  -- near zero: the Lipschitz bound
  have hnear : ∫ y in Set.Ioc 0 a, Q y / (2 * y) ≤ K * a := by
    have := setIntegral_mono_on (s := Set.Ioc 0 a)
      (hint.mono_set fun y hy => ⟨hy.1, hy.2.trans ha1⟩) (integrableOn_const (C := K) (by simp))
      measurableSet_Ioc fun y hy => hQK y hy.1
    simpa [Real.volume_Ioc, ha0.le, mul_comm] using this
  -- away from zero: `Q(y)/(2y) ≤ 1 + 2η/y`
  have hfarInt : IntegrableOn (fun y : ℝ => 1 + 2 * η * y⁻¹) (Set.Ioc a 1) := by
    have hc : ContinuousOn (fun y : ℝ => 1 + 2 * η * y⁻¹) (Set.Icc a 1) :=
      continuousOn_const.add (continuousOn_const.mul
        (continuousOn_inv₀.mono fun y hy => ne_of_gt (lt_of_lt_of_le ha0 hy.1)))
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hfar : ∫ y in Set.Ioc a 1, Q y / (2 * y) ≤ ∫ y in Set.Ioc a 1, (1 + 2 * η * y⁻¹) := by
    refine setIntegral_mono_on (hint.mono_set fun y hy => ⟨lt_trans ha0 hy.1, hy.2⟩) hfarInt
      measurableSet_Ioc fun y hy => ?_
    have hy0 : 0 < y := lt_trans ha0 hy.1
    have := integral_plateau_sub_shift_sq_le hη hy0.le
    rw [div_le_iff₀ (by linarith)]
    have : (1 + 2 * η * y⁻¹) * (2 * y) = 2 * y + 4 * η := by field_simp; ring
    linarith
  have hfarEq : ∫ y in Set.Ioc a 1, (1 + 2 * η * y⁻¹) = (1 - a) + 2 * η * Real.log (1 / a) := by
    have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume a 1 :=
      (continuousOn_inv₀.mono fun y hy => by
        rcases Set.mem_uIcc.mp hy with h | h <;> exact ne_of_gt (by linarith [h.1])).intervalIntegrable
    rw [← intervalIntegral.integral_of_le ha1, intervalIntegral.integral_add
      (f := fun _ => (1 : ℝ)) (g := fun x => 2 * η * x⁻¹) intervalIntegrable_const
      (hinv.const_mul _), intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 one_pos]
    simp
  have hlog : Real.log (1 / a) = -(2 * Real.log η) := by
    rw [one_div, Real.log_inv, Real.log_pow]; push_cast; ring
  have hKa : K * a = 2 * C * η := by simp only [K, a]; field_simp
  rw [hfarEq, hlog] at hfar
  nlinarith

end Plateau

/-- **Plateaus have shape term close to one**: for every `ε > 0` some plateau `φ_η`,
`0 < η ≤ 1/4`, has `β(φ_η)/‖φ_η‖² ≤ 1 + ε`. -/
theorem exists_plateau_bumpRobin_le {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧
      bumpRobin (plateau η) 1 / ∫ u, plateau η u ^ 2 ≤ 1 + ε := by
  obtain ⟨C, hC0, hC⟩ := exists_lipschitz_smoothTransition
  set F : ℝ → ℝ := fun η => (1 + 2 * C * η - 4 * (Real.log η * η)) / (1 - 2 * η)
  have hlim : Tendsto F (𝓝[>] 0) (𝓝 1) := by
    have hid : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have hlog : Tendsto (fun η : ℝ => Real.log η * η) (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
    have h2 := (((tendsto_const_nhds (x := (1 : ℝ))).add (hid.const_mul (2 * C))).sub
      (hlog.const_mul 4)).div ((tendsto_const_nhds (x := (1 : ℝ))).sub (hid.const_mul 2))
      (by norm_num)
    have hv : (1 + 2 * C * 0 - 4 * 0) / (1 - 2 * 0) = (1 : ℝ) := by norm_num
    rw [hv] at h2
    exact h2
  have h1 := hlim.eventually (gt_mem_nhds (show (1 : ℝ) < 1 + ε by linarith))
  have h4 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η < 1 / 4 := nhdsWithin_le_nhds (gt_mem_nhds (by norm_num))
  have h5 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η := self_mem_nhdsWithin
  obtain ⟨η, hF, hη4, hη0⟩ := (h1.and (h4.and h5)).exists
  refine ⟨η, hη0, hη4.le, ?_⟩
  have hB := bumpRobin_plateau_le hC0 hC hη0 (by linarith)
  have hM := integral_plateau_sq_ge hη0 (by linarith)
  have hden : 0 < 1 - 2 * η := by linarith
  have hlogη : Real.log η < 0 := Real.log_neg hη0 (by linarith)
  have hnum : 0 ≤ 1 + 2 * C * η - 4 * η * Real.log η := by nlinarith
  have hM0 : 0 < ∫ u, plateau η u ^ 2 := lt_of_lt_of_le hden hM
  calc bumpRobin (plateau η) 1 / ∫ u, plateau η u ^ 2
      ≤ (1 + 2 * C * η - 4 * η * Real.log η) / ∫ u, plateau η u ^ 2 :=
        div_le_div_of_nonneg_right hB hM0.le
    _ ≤ (1 + 2 * C * η - 4 * η * Real.log η) / (1 - 2 * η) :=
        div_le_div_of_nonneg_left hnum hden hM
    _ = F η := by simp only [F]; ring_nf
    _ ≤ 1 + ε := hF.le

/-! ### The Markov form on the pole vector -/

/-- **The pointwise bound on the pole vector**: for a nonnegative profile and `0 < w < δ_N`,
`M(f) ≤ ‖g‖² (H_N (2θ′(0) + log(1/w) + κ_L(φ) + e^{1/2}w/2) − (log² N − log² 3))`. -/
theorem markovQuad_poleVector_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : ∀ u, 0 ≤ φ u) (hφ2 : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) {N : ℕ} (hN : 3 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w < atomSpacing N) (hw1 : w ≤ 1) :
    markovQuad (atomicTest N (fun n => 1 / Real.sqrt n) (atomDilate φ w)) ≤
      (∫ u, atomDilate φ w u ^ 2) * ((∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n) *
        (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) + profileRobin φ + Real.exp (1 / 2) / 2 * w) -
          (Real.log N ^ 2 - Real.log 3 ^ 2)) := by
  set g := atomDilate φ w
  set x : ℕ → ℝ := fun n => 1 / Real.sqrt n
  set H := ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n
  have hg : ContDiff ℝ 2 g := hφ.comp (contDiff_id.div_const w)
  have hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0 := fun u hu => hφsupp (u / w) fun h => hu
    ⟨by have := h.1; rwa [le_div_iff₀ hw0, zero_mul] at this,
      by have := h.2; rwa [div_le_iff₀ hw0, one_mul] at this⟩
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro isCompact_Icc fun u hu => hgsupp u hu
  have hg0 : ∀ u, 0 ≤ g u := fun u => hφ0 _
  have hx : ∀ n, 0 ≤ x n := fun n => by positivity
  have hX : ∑ n ∈ Finset.Icc 1 N, x n ^ 2 = H := sum_poleVector_sq N
  have hH : 0 ≤ H := Finset.sum_nonneg fun n _ => by positivity
  have hf : ContDiff ℝ 2 (atomicTest N x g) := contDiff_atomicTest hg N x
  have hfc : HasCompactSupport (atomicTest N x g) := hasCompactSupport_atomicTest hgsupp N x
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  -- the three pieces
  have hM : markovQuad (atomicTest N x g) = 2 * gammaHardyPhaseRate 0 *
      (∫ u, atomicTest N x g u ^ 2) + levyEnergy (atomicTest N x g) - primeSum (atomicTest N x g) := by
    unfold markovQuad
    rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc]
  have hL2 : ∫ u, atomicTest N x g u ^ 2 = H * ∫ u, g u ^ 2 := by
    rw [integral_atomicTest_sq hg hgc hgsupp hw, hX]
  have hLevy := levyEnergy_atomicTest_le hg hgc hgsupp hg0 hw x hx
  rw [hX] at hLevy
  have hself := abs_levyEnergy_atomDilate_sub_le hφ hφsupp hφ2 hw0 hw1 hK
  have hself' : levyEnergy g ≤ (Real.log (1 / w) + profileRobin φ) * (∫ u, g u ^ 2) +
      Real.exp (1 / 2) / 2 * w * ∫ u, g u ^ 2 := by
    have := (abs_le.mp hself).2
    linarith
  have hP : primeSum (atomicTest N x g) = (∫ u, g u ^ 2) * atomicWeilForm N x :=
    primeSum_atomicTest hg hgc hgsupp hw x
  have hPN := atomicWeilForm_poleVector_ge hN
  have hPg : (∫ u, g u ^ 2) * (Real.log N ^ 2 - Real.log 3 ^ 2) ≤ primeSum (atomicTest N x g) := by
    rw [hP]; exact mul_le_mul_of_nonneg_left hPN hG
  have hLg : levyEnergy (atomicTest N x g) ≤
      H * ((Real.log (1 / w) + profileRobin φ) * (∫ u, g u ^ 2) +
        Real.exp (1 / 2) / 2 * w * ∫ u, g u ^ 2) :=
    hLevy.trans (mul_le_mul_of_nonneg_left hself' hH)
  rw [hM, hL2]
  nlinarith

/-- `1/(N+1) ≤ δ_N ≤ 1/N`. -/
theorem atomSpacing_bounds {N : ℕ} (hN : 1 ≤ N) :
    1 / ((N : ℝ) + 1) ≤ atomSpacing N ∧ atomSpacing N ≤ 1 / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : (0 : ℝ) < 1 + 1 / N := by positivity
  refine ⟨?_, ?_⟩
  · have := Real.one_sub_inv_le_log_of_pos hx
    unfold atomSpacing
    refine le_trans (le_of_eq ?_) this
    field_simp
    ring
  · have := Real.log_le_sub_one_of_pos hx
    unfold atomSpacing
    linarith

/-- **The asymptotics of the bound**: if `2θ′(0) + log(1/c) + κ + γ < 0`, then for all large `N`,
`H_N (2θ′(0) + log(1/(cδ_N)) + κ + e^{1/2}cδ_N/2) − (log² N − log² 3) < 0`. -/
theorem eventually_poleVector_bracket_neg {c κ : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hneg : 2 * gammaHardyPhaseRate 0 + Real.log (1 / c) + κ + Real.eulerMascheroniConstant < 0) :
    ∀ᶠ N : ℕ in atTop, (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n) *
        (2 * gammaHardyPhaseRate 0 + Real.log (1 / (c * atomSpacing N)) + κ +
          Real.exp (1 / 2) / 2 * (c * atomSpacing N)) - (Real.log N ^ 2 - Real.log 3 ^ 2) < 0 := by
  set a := 2 * gammaHardyPhaseRate 0 + Real.log (1 / c) + κ
  set γ := Real.eulerMascheroniConstant
  set ε := -(a + γ) / 4
  have hε : 0 < ε := by simp only [ε]; linarith
  set B := (γ + ε) * (a + ε) + Real.log 3 ^ 2
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hharm : ∀ᶠ N : ℕ in atTop, (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n) ≤ Real.log N + γ + ε := by
    have := Real.tendsto_harmonic_sub_log.eventually (gt_mem_nhds (show γ < γ + ε by linarith))
    filter_upwards [this] with N hN
    rw [RHTower.harmonic_eq_sum_Icc N] at hN
    linarith
  have hinv : ∀ᶠ N : ℕ in atTop, 2 / (N : ℝ) ≤ ε := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).eventually (ge_mem_nhds hε)
    exact this
  have hbig : ∀ᶠ N : ℕ in atTop, 0 ≤ Real.log N + a ∧ 0 ≤ Real.log N + γ + ε ∧
      ((a + γ) / 2) * Real.log N + B < 0 := by
    have h1 := hlogN.eventually_ge_atTop (-a)
    have h2 := hlogN.eventually_ge_atTop (-(γ + ε))
    have h3 := hlogN.eventually_gt_atTop (2 * B / (-(a + γ)))
    filter_upwards [h1, h2, h3] with N h1 h2 h3
    refine ⟨by linarith, by linarith, ?_⟩
    have hpos : 0 < -(a + γ) := by linarith
    rw [div_lt_iff₀ hpos] at h3
    nlinarith
  filter_upwards [hharm, hinv, hbig, eventually_ge_atTop 1] with N hH hI ⟨hb1, hb2, hb3⟩ hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hδl, hδu⟩ := atomSpacing_bounds hN
  have hδ0 : 0 < atomSpacing N := atomSpacing_pos hN
  set H := ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun n _ => by positivity
  -- the bracket
  have hlog1 : Real.log (1 / (c * atomSpacing N)) = Real.log (1 / c) + Real.log (1 / atomSpacing N) := by
    rw [show 1 / (c * atomSpacing N) = (1 / c) * (1 / atomSpacing N) by field_simp,
      Real.log_mul (by positivity) (by positivity)]
  have hlogδ_le : Real.log (1 / atomSpacing N) ≤ Real.log N + 1 / N := by
    have h1 : Real.log (1 / atomSpacing N) ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by
        rw [div_le_iff₀ hδ0]
        have := (div_le_iff₀ (by positivity : (0 : ℝ) < N + 1)).mp hδl
        linarith)
    have h2 : Real.log ((N : ℝ) + 1) ≤ Real.log N + 1 / N := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 1) / N by positivity)
      rw [Real.log_div (by positivity) hN0.ne'] at this
      have e : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
      linarith
    linarith
  have hlogδ_ge : Real.log N ≤ Real.log (1 / atomSpacing N) :=
    Real.log_le_log hN0 (by rw [le_div_iff₀ hδ0]; rw [le_div_iff₀ hN0] at hδu; linarith)
  have hexp : Real.exp (1 / 2) / 2 * (c * atomSpacing N) ≤ 1 / N := by
    have he : Real.exp (1 / 2) < 2 := by
      have := Real.exp_one_lt_d9
      have hs : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 / 2)]
    have hcδ : c * atomSpacing N ≤ atomSpacing N := by nlinarith
    have hcδ0 : 0 ≤ c * atomSpacing N := by positivity
    calc Real.exp (1 / 2) / 2 * (c * atomSpacing N) ≤ 1 * (c * atomSpacing N) :=
          mul_le_mul_of_nonneg_right (by linarith) hcδ0
      _ ≤ 1 / N := by linarith
  set Λ := 2 * gammaHardyPhaseRate 0 + Real.log (1 / (c * atomSpacing N)) + κ +
    Real.exp (1 / 2) / 2 * (c * atomSpacing N)
  have hΛ : Λ = a + Real.log (1 / atomSpacing N) + Real.exp (1 / 2) / 2 * (c * atomSpacing N) := by
    simp only [Λ, a, hlog1]; ring
  have hexp0 : 0 ≤ Real.exp (1 / 2) / 2 * (c * atomSpacing N) := by positivity
  have hI' : 1 / (N : ℝ) + 1 / N ≤ ε := by
    have : 2 / (N : ℝ) = 1 / N + 1 / N := by ring
    linarith
  have hΛu : Λ ≤ Real.log N + a + ε := by rw [hΛ]; linarith
  have hΛl : 0 ≤ Λ := by rw [hΛ]; linarith
  have hHΛ : H * Λ ≤ (Real.log N + γ + ε) * (Real.log N + a + ε) :=
    calc H * Λ ≤ (Real.log N + γ + ε) * Λ := mul_le_mul_of_nonneg_right hH hΛl
      _ ≤ (Real.log N + γ + ε) * (Real.log N + a + ε) := mul_le_mul_of_nonneg_left hΛu hb2
  have hexpand : (Real.log N + γ + ε) * (Real.log N + a + ε) - (Real.log N ^ 2 - Real.log 3 ^ 2) =
      ((a + γ) / 2) * Real.log N + B := by
    simp only [B, ε]; ring
  linarith

/-! ### The threshold -/

theorem two_gammaHardyPhaseRate_zero_add_euler :
    2 * gammaHardyPhaseRate 0 + Real.eulerMascheroniConstant =
      -(3 * Real.log 2 + π / 2 + Real.log π) := by
  rw [gammaHardyPhaseRate_zero_closed]
  ring

/-- The Markov form on the pole vector is eventually negative once its finite part
`2θ′(0) + log(1/c) + κ_L(φ) + γ` is negative. -/
theorem eventually_markovQuad_poleVector_neg {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : ∀ u, 0 ≤ φ u) (hφ2 : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hneg : 2 * gammaHardyPhaseRate 0 + Real.log (1 / c) + profileRobin φ +
      Real.eulerMascheroniConstant < 0) :
    ∀ᶠ N : ℕ in atTop,
      markovQuad (atomicTest N (fun n => 1 / Real.sqrt n) (atomDilate φ (c * atomSpacing N))) < 0 := by
  filter_upwards [eventually_poleVector_bracket_neg hc0 hc1.le hneg, eventually_ge_atTop 3]
    with N hN hN3
  have hN1 : 1 ≤ N := by omega
  have hδ := atomSpacing_pos hN1
  obtain ⟨-, hδu⟩ := atomSpacing_bounds hN1
  have hw0 : 0 < c * atomSpacing N := by positivity
  have hw : c * atomSpacing N < atomSpacing N := by nlinarith
  have hw1 : c * atomSpacing N ≤ 1 := by
    have : (1 : ℝ) / N ≤ 1 := by
      rw [div_le_one (by positivity)]; exact_mod_cast hN1
    nlinarith
  have hb := markovQuad_poleVector_le hφ hφsupp hφ0 hφ2 hK hN3 hw0 hw hw1
  have hg2 : 0 < ∫ u, atomDilate φ (c * atomSpacing N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; positivity
  exact hb.trans_lt (mul_neg_of_pos_of_neg hg2 hN)

/-- **The threshold on the pole vector**: for a nonnegative `C²` profile `φ` on `[0, 1]` and every
`c ∈ (e^{β(φ)/‖φ‖²}/(2π), 1)`, the Markov form is negative on the pole vector `x_n = n^{−1/2}` at
width `c δ_N` for all large `N`. -/
theorem markovQuad_poleVector_neg_of_threshold {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : ∀ u, 0 ≤ φ u) (hφ2 : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) {c : ℝ}
    (hc : Real.exp (bumpRobin φ 1 / ∫ u, φ u ^ 2) / (2 * π) < c) (hc1 : c < 1) :
    ∀ᶠ N : ℕ in atTop,
      markovQuad (atomicTest N (fun n => 1 / Real.sqrt n) (atomDilate φ (c * atomSpacing N))) < 0 := by
  have h2π : 0 < 2 * π := by positivity
  have hc0 : 0 < c := lt_trans (div_pos (Real.exp_pos _) h2π) hc
  refine eventually_markovQuad_poleVector_neg hφ hφsupp hφ0 hφ2 hK hc0 hc1 ?_
  set β := bumpRobin φ 1 / ∫ u, φ u ^ 2
  have h1 : Real.exp β < c * (2 * π) := (div_lt_iff₀ h2π).mp hc
  have h2 : β < Real.log (c * (2 * π)) := (Real.lt_log_iff_exp_lt (by positivity)).mpr h1
  rw [Real.log_mul hc0.ne' h2π.ne', Real.log_mul two_ne_zero Real.pi_pos.ne'] at h2
  have hθ := two_gammaHardyPhaseRate_zero_add_euler
  have hκ : profileRobin φ = 2 * Real.log 2 + π / 2 + β := by
    rw [profileRobin, archRobinConstant_eq]
  rw [hκ, one_div, Real.log_inv]
  linarith

/-- **The Markov form fails inside the separated regime**: for every `c ∈ (e/(2π), 1)` there is a
smooth nonnegative plateau profile `φ` on `[0, 1]` such that, for all large `N`, the Markov form is
negative on the pole vector at width `c δ_N`. The critical constant of the Markov form is at most
`e/(2π) ≈ 0.433`: below the spacing the stability law needs its rank-one pole correction. -/
theorem markov_poleVector_negative_inside_separated {c : ℝ} (hc : Real.exp 1 / (2 * π) < c)
    (hc1 : c < 1) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 2 φ ∧ (∀ u, u ∉ Set.Icc 0 1 → φ u = 0) ∧ (∀ u, 0 ≤ φ u) ∧
      ∀ᶠ N : ℕ in atTop,
        markovQuad (atomicTest N (fun n => 1 / Real.sqrt n) (atomDilate φ (c * atomSpacing N)))
          < 0 := by
  have h2π : 0 < 2 * π := by positivity
  have hc0 : 0 < c := lt_trans (div_pos (Real.exp_pos _) h2π) hc
  -- room above `1` in the exponent
  set ε := Real.log (c * (2 * π)) - 1
  have hε : 0 < ε := by
    have : Real.exp 1 < c * (2 * π) := (div_lt_iff₀ h2π).mp hc
    have := (Real.lt_log_iff_exp_lt (by positivity)).mpr this
    simp only [ε]; linarith
  obtain ⟨η, hη0, hη4, hβ⟩ := exists_plateau_bumpRobin_le (ε := ε / 2) (by linarith)
  obtain ⟨C, -, hC⟩ := exists_lipschitz_smoothTransition
  have hφ2 : 0 < ∫ u, plateau η u ^ 2 :=
    lt_of_lt_of_le (by linarith) (integral_plateau_sq_ge hη0 (by linarith))
  refine ⟨plateau η, contDiff_plateau η, fun u hu => plateau_eq_zero hη0 hu, plateau_nonneg,
    markovQuad_poleVector_neg_of_threshold (contDiff_plateau η) (fun u hu => plateau_eq_zero hη0 hu)
      plateau_nonneg hφ2 (abs_plateau_sub_le hC hη0) ?_ hc1⟩
  rw [div_lt_iff₀ h2π]
  calc Real.exp (bumpRobin (plateau η) 1 / ∫ u, plateau η u ^ 2) ≤ Real.exp (1 + ε / 2) :=
        Real.exp_le_exp.mpr hβ
    _ < Real.exp (1 + ε) := Real.exp_lt_exp.mpr (by linarith)
    _ = c * (2 * π) := by
        simp only [ε, add_sub_cancel]
        exact Real.exp_log (by positivity)

/-- `e/(2π) < 1`: the threshold lies inside the separated regime. -/
theorem exp_one_div_two_pi_lt_one : Real.exp 1 / (2 * π) < 1 := by
  rw [div_lt_one (by positivity)]
  have := Real.exp_one_lt_d9
  have := Real.pi_gt_three
  linarith

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
