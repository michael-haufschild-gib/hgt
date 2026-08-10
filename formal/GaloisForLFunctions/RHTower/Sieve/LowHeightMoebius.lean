import GaloisForLFunctions.RHTower.Sieve.LowHeightPoly
import GaloisForLFunctions.RHTower.Sieve.MoebiusMaximalWindow

/-!
# The Möbius Dirichlet polynomial at low heights

Abel summation transfers the cancellation of the Mertens function to the Dirichlet polynomial:

```text
‖ ∑_{n ≤ M} μ(n)·n^{2πiw} ‖  ≤  mertensSup(M)·( 1 + 2π|w|·log M ) ,
```

and `mertensSup M = o(M)` is the prime number theorem.  Integrating over `|w| ≤ T` gives

```text
∫_{|w| ≤ T} ‖ ∑_{n ≤ M} μ(n)·n^{2πiw} ‖² dw  ≤  2T·mertensSup(M)²·(1 + 2πT log M)² ,
```

which is `o(M²)` for every height `T ≪ 1/log M`.  Below that scale the mean square of the Möbius
polynomial is unconditionally smaller than the mean value theorem's `≍ M²`, with no zero-free
region and no distance estimate: the phase has too little total variation to undo the cancellation
already present in the coefficients.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset
open scoped ArithmeticFunction.Moebius

/-- The real Möbius coefficient sequence. -/
theorem sum_range_moebius_shift_eq_mertensM (k : ℕ) :
    ∑ j ∈ Finset.range k, ((μ (j + 1) : ℤ) : ℝ) = mertensM k := by
  rw [mertensM, Finset.sum_range_succ']
  have hzero : ((μ 0 : ℤ) : ℝ) = 0 := by
    simp
  rw [hzero, add_zero]

/-- **The Möbius Dirichlet polynomial at height `w`.** -/
theorem norm_logPoly_moebius_le (M : ℕ) (w : ℝ) :
    ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖
      ≤ mertensSup M * (1 + 2 * Real.pi * |w| * Real.log M) := by
  refine norm_logPoly_le_partial (fun n => ((μ n : ℤ) : ℝ)) M (fun k hk => ?_) w
  rw [sum_range_moebius_shift_eq_mertensM]
  exact abs_mertensM_le_mertensSup hk

/-- **The Möbius mean square at low heights.** -/
theorem integral_Icc_normSq_logPoly_moebius_le (M : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ w in Set.Icc (-T) T, ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ 2 * T * (mertensSup M * (1 + 2 * Real.pi * T * Real.log M)) ^ 2 := by
  classical
  set a : ℕ → ℂ := fun n => (((μ n : ℤ) : ℝ) : ℂ) with hadef
  set C : ℝ := mertensSup M * (1 + 2 * Real.pi * T * Real.log M) with hCdef
  have hlogM : 0 ≤ Real.log (M : ℝ) := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · refine Real.log_nonneg ?_
      exact_mod_cast hM
  have hB0 : 0 ≤ mertensSup M := mertensSup_nonneg M
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have : (0 : ℝ) ≤ 2 * Real.pi * T * Real.log (M : ℝ) := by
      have := Real.pi_pos
      positivity
    exact mul_nonneg hB0 (by linarith)
  have hcont : Continuous fun w : ℝ => ‖logPoly a (Finset.Icc 1 M) w‖ ^ 2 :=
    ((continuous_logPoly a _).norm).pow 2
  have hle : ∀ w ∈ Set.Icc (-T) T, ‖logPoly a (Finset.Icc 1 M) w‖ ^ 2 ≤ C ^ 2 := by
    intro w hw
    rw [Set.mem_Icc] at hw
    have hwT : |w| ≤ T := abs_le.2 ⟨hw.1, hw.2⟩
    have hstep : ‖logPoly a (Finset.Icc 1 M) w‖ ≤ C := by
      refine le_trans (norm_logPoly_moebius_le M w) ?_
      rw [hCdef]
      refine mul_le_mul_of_nonneg_left ?_ hB0
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      have : 2 * Real.pi * |w| * Real.log (M : ℝ) ≤ 2 * Real.pi * T * Real.log (M : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ hlogM
        exact mul_le_mul_of_nonneg_left hwT (by linarith)
      linarith
    exact pow_le_pow_left₀ (norm_nonneg _) hstep 2
  have hconstInt : IntegrableOn (fun _ : ℝ => C ^ 2) (Set.Icc (-T) T) volume :=
    (continuous_const).integrableOn_Icc
  have hmono := setIntegral_mono_on hcont.integrableOn_Icc hconstInt measurableSet_Icc hle
  refine le_trans hmono (le_of_eq ?_)
  rw [setIntegral_const, smul_eq_mul]
  have hval : volume.real (Set.Icc (-T) T) = 2 * T := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hval]

/-- The Abel weight of the Mertens function: the partial sums weighted by the phase increments. -/
def mertensAbelSum (M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range M, |mertensM (i + 1)| / ((i : ℝ) + 1)

theorem mertensAbelSum_nonneg (M : ℕ) : 0 ≤ mertensAbelSum M := by
  refine Finset.sum_nonneg fun i _ => ?_
  positivity

/-- **The Abel weight is `o(M)`.**  Cesàro means of the null sequence `|M(k)|/k`. -/
theorem tendsto_mertensAbelSum_div :
    Filter.Tendsto (fun M : ℕ => mertensAbelSum M / (M : ℝ)) Filter.atTop (nhds 0) := by
  have hu : Filter.Tendsto (fun i : ℕ => |mertensM (i + 1)| / ((i : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    have hbase := tendsto_abs_mertensM_div.comp (Filter.tendsto_add_atTop_nat 1)
    refine hbase.congr fun i => ?_
    simp only [Function.comp_apply]
    congr 1
    push_cast
    ring
  have hces := hu.cesaro
  refine hces.congr fun M => ?_
  rw [mertensAbelSum, div_eq_inv_mul]

/-- **The Möbius Dirichlet polynomial, Abel-weighted.**  The phase has total variation `2π|w|/n`
across one step, so the cancellation of the Mertens function transfers without a logarithmic loss. -/
theorem norm_logPoly_moebius_le_abel (M : ℕ) (w : ℝ) :
    ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖
      ≤ |mertensM M| + 2 * Real.pi * |w| * mertensAbelSum M := by
  refine le_trans (norm_logPoly_le_abel (fun n => ((μ n : ℤ) : ℝ)) M w) ?_
  rw [sum_range_moebius_shift_eq_mertensM]
  refine add_le_add le_rfl ?_
  have hnn : (0 : ℝ) ≤ 2 * Real.pi * |w| := by
    have := Real.pi_pos
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hnn
  have hcong : ∀ i ∈ Finset.range (M - 1),
      |∑ j ∈ Finset.range (i + 1), ((μ (j + 1) : ℤ) : ℝ)| / ((i : ℝ) + 1)
        = |mertensM (i + 1)| / ((i : ℝ) + 1) := by
    intro i _
    rw [sum_range_moebius_shift_eq_mertensM]
  rw [Finset.sum_congr rfl hcong, mertensAbelSum]
  have hsub : Finset.range (M - 1) ⊆ Finset.range M := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => ?_
  positivity

/-- **The Möbius mean square at any fixed height is `o(M²)`, unconditionally.** -/
theorem eventually_integral_Icc_normSq_logPoly_moebius_le {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in Filter.atTop,
      (∫ w in Set.Icc (-T) T,
        ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2) ≤ ε * (M : ℝ) ^ 2 := by
  classical
  set c : ℝ := Real.sqrt (ε / (2 * T + 1)) with hcdef
  have hden : (0 : ℝ) < 2 * T + 1 := by linarith
  have hc0 : 0 < c := by
    rw [hcdef]
    exact Real.sqrt_pos.2 (by positivity)
  have hcsq : c ^ 2 = ε / (2 * T + 1) := by
    rw [hcdef, Real.sq_sqrt (by positivity)]
  have hKdiv : Filter.Tendsto
      (fun M : ℕ => (|mertensM M| + 2 * Real.pi * T * mertensAbelSum M) / (M : ℝ))
      Filter.atTop (nhds 0) := by
    have h1 := tendsto_abs_mertensM_div
    have h2 := tendsto_mertensAbelSum_div.const_mul (2 * Real.pi * T)
    have hsum := h1.add h2
    rw [show (0 : ℝ) + 2 * Real.pi * T * 0 = 0 by ring] at hsum
    refine hsum.congr fun M => ?_
    field_simp
  have hev : ∀ᶠ M : ℕ in Filter.atTop,
      (|mertensM M| + 2 * Real.pi * T * mertensAbelSum M) / (M : ℝ) ≤ c := by
    have := hKdiv.eventually (eventually_lt_nhds hc0)
    filter_upwards [this] with M hM
    exact le_of_lt hM
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with M hM hM1
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  set K : ℝ := |mertensM M| + 2 * Real.pi * T * mertensAbelSum M with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have := Real.pi_pos
    have := mertensAbelSum_nonneg M
    have : (0 : ℝ) ≤ 2 * Real.pi * T * mertensAbelSum M := by positivity
    linarith [abs_nonneg (mertensM M)]
  have hKle : K ≤ c * (M : ℝ) := by
    rw [div_le_iff₀ hM0] at hM
    exact hM
  have hpt : ∀ w ∈ Set.Icc (-T) T,
      ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 ≤ K ^ 2 := by
    intro w hw
    rw [Set.mem_Icc] at hw
    have hwT : |w| ≤ T := abs_le.2 ⟨hw.1, hw.2⟩
    have hb : ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ≤ K := by
      refine le_trans (norm_logPoly_moebius_le_abel M w) (le_of_eq_of_le rfl ?_)
      rw [hKdef]
      refine add_le_add le_rfl ?_
      have hA : (0 : ℝ) ≤ mertensAbelSum M := mertensAbelSum_nonneg M
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      have : 2 * Real.pi * |w| ≤ 2 * Real.pi * T :=
        mul_le_mul_of_nonneg_left hwT (by linarith)
      exact mul_le_mul_of_nonneg_right this hA
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hcont : Continuous fun w : ℝ =>
      ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  have hconstInt : IntegrableOn (fun _ : ℝ => K ^ 2) (Set.Icc (-T) T) volume :=
    (continuous_const).integrableOn_Icc
  have hmono := setIntegral_mono_on hcont.integrableOn_Icc hconstInt measurableSet_Icc hpt
  have hval : (∫ _ in Set.Icc (-T) T, K ^ 2) = 2 * T * K ^ 2 := by
    rw [setIntegral_const, smul_eq_mul]
    have hv : volume.real (Set.Icc (-T) T) = 2 * T := by
      rw [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hv]
  rw [hval] at hmono
  refine le_trans hmono ?_
  have hKsq : K ^ 2 ≤ c ^ 2 * (M : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ hK0 hKle 2
    calc K ^ 2 ≤ (c * (M : ℝ)) ^ 2 := this
      _ = c ^ 2 * (M : ℝ) ^ 2 := by ring
  have hfin : 2 * T * K ^ 2 ≤ (2 * T + 1) * (c ^ 2 * (M : ℝ) ^ 2) := by
    have h1 : 2 * T * K ^ 2 ≤ 2 * T * (c ^ 2 * (M : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hKsq (by linarith)
    have h2 : (0 : ℝ) ≤ c ^ 2 * (M : ℝ) ^ 2 := by positivity
    linarith
  have hval2 : (2 * T + 1) * (c ^ 2 * (M : ℝ) ^ 2) = ε * (M : ℝ) ^ 2 := by
    rw [hcsq]
    field_simp
  linarith [hfin, hval2]

/-- The Abel scale of the Möbius coefficients: the head plus the phase-weighted partial sums. -/
def moebiusAbelScale (M : ℕ) : ℝ := |mertensM M| + mertensAbelSum M

theorem moebiusAbelScale_nonneg (M : ℕ) : 0 ≤ moebiusAbelScale M := by
  have := abs_nonneg (mertensM M)
  have := mertensAbelSum_nonneg M
  rw [moebiusAbelScale]
  linarith

/-- **The Abel scale is `o(M)`** — this is the prime number theorem. -/
theorem tendsto_moebiusAbelScale_div :
    Filter.Tendsto (fun M : ℕ => moebiusAbelScale M / (M : ℝ)) Filter.atTop (nhds 0) := by
  have hsum := tendsto_abs_mertensM_div.add tendsto_mertensAbelSum_div
  rw [add_zero] at hsum
  refine hsum.congr fun M => ?_
  rw [moebiusAbelScale, add_div]

/-- **The Möbius mean square grows at most cubically in the height.**  Only the Abel scale enters,
so the whole estimate is `o(M²)` for every height `T ≪ (M/moebiusAbelScale M)^{2/3}`. -/
theorem integral_Icc_normSq_logPoly_moebius_le_cube (M : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ w in Set.Icc (-T) T,
      ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ 200 * T ^ 3 * moebiusAbelScale M ^ 2 := by
  classical
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set s : ℝ := moebiusAbelScale M with hsdef
  have hs0 : 0 ≤ s := moebiusAbelScale_nonneg M
  have hA : |mertensM M| ≤ s := by
    rw [hsdef, moebiusAbelScale]
    linarith [mertensAbelSum_nonneg M]
  have hB : mertensAbelSum M ≤ s := by
    rw [hsdef, moebiusAbelScale]
    linarith [abs_nonneg (mertensM M)]
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hK : ∀ w ∈ Set.Icc (-T) T,
      ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 ≤ (10 * T * s) ^ 2 := by
    intro w hw
    rw [Set.mem_Icc] at hw
    have hwT : |w| ≤ T := abs_le.2 ⟨hw.1, hw.2⟩
    have hb := norm_logPoly_moebius_le_abel M w
    have hstep : |mertensM M| + 2 * Real.pi * |w| * mertensAbelSum M ≤ 10 * T * s := by
      have h1 : 2 * Real.pi * |w| * mertensAbelSum M ≤ 2 * Real.pi * T * s := by
        have hpos : (0 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_pos]
        have h1a : 2 * Real.pi * |w| ≤ 2 * Real.pi * T := mul_le_mul_of_nonneg_left hwT hpos
        have h1b : (0 : ℝ) ≤ 2 * Real.pi * |w| := by positivity
        calc 2 * Real.pi * |w| * mertensAbelSum M ≤ 2 * Real.pi * |w| * s :=
              mul_le_mul_of_nonneg_left hB h1b
          _ ≤ 2 * Real.pi * T * s := mul_le_mul_of_nonneg_right h1a hs0
      have h2 : 2 * Real.pi * T * s ≤ 8 * (T * s) := by
        have hTs : (0 : ℝ) ≤ T * s := by positivity
        nlinarith [hpi, hTs]
      have h3 : |mertensM M| ≤ T * s := by
        have : s ≤ T * s := by nlinarith [hs0, hT]
        linarith
      calc |mertensM M| + 2 * Real.pi * |w| * mertensAbelSum M
          ≤ T * s + 2 * Real.pi * T * s := add_le_add h3 h1
        _ ≤ T * s + 8 * (T * s) := by linarith [h2]
        _ ≤ 10 * T * s := by nlinarith [mul_nonneg hT0 hs0]
    have hfin : ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ≤ 10 * T * s :=
      le_trans hb hstep
    exact pow_le_pow_left₀ (norm_nonneg _) hfin 2
  have hcont : Continuous fun w : ℝ =>
      ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  have hconstInt : IntegrableOn (fun _ : ℝ => (10 * T * s) ^ 2) (Set.Icc (-T) T) volume :=
    (continuous_const).integrableOn_Icc
  have hmono := setIntegral_mono_on hcont.integrableOn_Icc hconstInt measurableSet_Icc hK
  have hval : (∫ _ in Set.Icc (-T) T, (10 * T * s) ^ 2) = 2 * T * (10 * T * s) ^ 2 := by
    rw [setIntegral_const, smul_eq_mul]
    have hv : volume.real (Set.Icc (-T) T) = 2 * T := by
      rw [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hv]
  rw [hval] at hmono
  refine le_trans hmono (le_of_eq ?_)
  ring

/-- **The unconditional good range is unbounded.**  For every height `T` the Möbius mean square is
below `ε·M²` at every height `S ≤ T`, once `M` is large.  No zero-free region and no multiplicative
distance enter: the input is `M(x) = o(x)` alone. -/
theorem eventually_forall_height_integral_moebius_le {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in Filter.atTop, ∀ S : ℝ, 0 ≤ S → S ≤ T →
      (∫ w in Set.Icc (-S) S,
        ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2) ≤ ε * (M : ℝ) ^ 2 := by
  filter_upwards [eventually_integral_Icc_normSq_logPoly_moebius_le hT hε] with M hM S hS0 hST
  have hcont : Continuous fun w : ℝ =>
      ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  have hsub : Set.Icc (-S) S ⊆ Set.Icc (-T) T := by
    refine Set.Icc_subset_Icc (by linarith) hST
  have hint : IntegrableOn (fun w : ℝ =>
      ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      (Set.Icc (-T) T) volume := hcont.integrableOn_Icc
  have hstep := setIntegral_mono_set hint
    (Filter.Eventually.of_forall fun w => by positivity) hsub.eventuallyLE
  linarith [hstep, hM]

end RHTower.Sieve

end
