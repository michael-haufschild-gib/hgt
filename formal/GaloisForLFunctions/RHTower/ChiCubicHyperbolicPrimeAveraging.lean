import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeKernel

/-!
# Dual averaging of the actual hyperbolic prime kernel

The literal Chebyshev increment becomes a finite sum of reciprocal-window
integrals. Sharp endpoints and every proper prime power are retained.
-/

noncomputable section
open Finset Filter Topology MeasureTheory
open GaloisForLFunctions.RHTower
namespace RHTower

private theorem psi_window_finite {N δ x : ℝ} (hN : 0 < N)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hx : x ∈ Set.Icc N (2 * N)) :
    Chebyshev.psi (x + δ * x) - Chebyshev.psi x =
      ∑ n ∈ Finset.Ioc 0 ⌊3 * N⌋₊,
        if x ∈ Set.Ico ((n : ℝ) / (1 + δ)) n then ArithmeticFunction.vonMangoldt n else 0 := by
  classical
  have hx0 : 0 ≤ x := hN.le.trans hx.1
  have hxd : x ≤ x + δ * x := by nlinarith
  have htop : x + δ * x ≤ 3 * N := by
    have := mul_le_mul_of_nonneg_right hδ1 hx0
    linarith [hx.2]
  have hd : 0 < 1 + δ := by linarith
  rw [psi_sub_psi_eq_sum hxd]
  have hs : Finset.Ioc ⌊x⌋₊ ⌊x + δ * x⌋₊ =
      (Finset.Ioc 0 ⌊3 * N⌋₊).filter (fun n : ℕ => x ∈ Set.Ico ((n : ℝ) / (1 + δ)) (n : ℝ)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Set.mem_Ico]
    constructor
    · intro hn
      have hxn := (Nat.floor_lt hx0).1 hn.1
      have hnx := (Nat.le_floor_iff (hx0.trans hxd)).1 hn.2
      refine ⟨⟨lt_of_le_of_lt (Nat.zero_le _) hn.1, Nat.le_floor (hnx.trans htop)⟩, ?_, hxn⟩
      apply (div_le_iff₀ hd).2
      nlinarith
    · rintro ⟨_, hn, hxn⟩
      refine ⟨(Nat.floor_lt hx0).2 hxn, Nat.le_floor ?_⟩
      have := (div_le_iff₀ hd).1 hn
      nlinarith
  rw [hs, Finset.sum_filter]

/-- The exact finite von Mangoldt dual average of the original ordered kernel. -/
def chiCubicHyperbolicVonMangoldtAverage (N : ℝ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊3 * N⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) *
    ∫ x in Set.Ico ((n : ℝ) / (1 + N ^ ((1 : ℝ) / 5 - 1))) n ∩ Set.Icc N (2 * N),
      chiCubicHyperbolicPrimeKernel N M x / ((N ^ ((1 : ℝ) / 5 - 1) * x : ℝ) : ℂ)

private theorem integrable_kernel_reciprocal {N : ℝ} (hN : 1 < N) (M : ℕ) :
    IntegrableOn (fun x => chiCubicHyperbolicPrimeKernel N M x /
      ((N ^ ((1 : ℝ) / 5 - 1) * x : ℝ) : ℂ)) (Set.Icc N (2 * N)) volume := by
  have hN0 : 0 < N := by linarith
  have hc : ContinuousOn (fun x : ℝ => (((N ^ ((1 : ℝ) / 5 - 1) * x : ℝ) : ℂ))⁻¹)
      (Set.Icc N (2 * N)) := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      exact_mod_cast (ne_of_gt (show 0 < N ^ ((1 : ℝ) / 5 - 1) * x by
        have : 0 < x := hN0.trans_le hx.1
        positivity))
  simpa only [div_eq_mul_inv] using
    (integrableOn_chiCubicHyperbolicPrimeKernel hN M).mul_continuousOn hc isCompact_Icc

/-- Exact dual averaging on the original band, with every term integrable. -/
theorem chiCubicHyperbolicVonMangoldtAverage_eq {N : ℝ} (hN : 1 < N)
    (hδ : N ^ ((1 : ℝ) / 5 - 1) ≤ 1 / 2) (M : ℕ) :
    IntegrableOn (fun x => (chiCubicPrimeWindowDensity N x : ℂ) *
      chiCubicHyperbolicPrimeKernel N M x) (Set.Icc N (2 * N)) volume ∧
    chiCubicHyperbolicVonMangoldtAverage N M =
      ∫ x in Set.Icc N (2 * N), (chiCubicPrimeWindowDensity N x : ℂ) *
        chiCubicHyperbolicPrimeKernel N M x := by
  classical
  let δ := N ^ ((1 : ℝ) / 5 - 1)
  let F := fun n : ℕ => (Set.Ico ((n : ℝ) / (1 + δ)) n).indicator
    (fun x => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (chiCubicHyperbolicPrimeKernel N M x / ((δ * x : ℝ) : ℂ)))
  have hN0 : 0 < N := by linarith
  have hδ0 : 0 ≤ δ := (Real.rpow_pos_of_pos hN0 _).le
  have hF (n : ℕ) : IntegrableOn (F n) (Set.Icc N (2 * N)) volume :=
    ((integrable_kernel_reciprocal hN M).const_mul _).indicator measurableSet_Ico
  have heq : Set.EqOn (fun x => (chiCubicPrimeWindowDensity N x : ℂ) *
      chiCubicHyperbolicPrimeKernel N M x)
      (fun x => ∑ n ∈ Finset.Ioc 0 ⌊3 * N⌋₊, F n x) (Set.Icc N (2 * N)) := by
    intro x hx
    have hpsi := psi_window_finite hN0 hδ0 hδ hx
    unfold chiCubicPrimeWindowDensity
    change (((Chebyshev.psi (x + δ * x) - Chebyshev.psi x) / (δ * x) : ℝ) : ℂ) *
      chiCubicHyperbolicPrimeKernel N M x = _
    rw [hpsi]
    push_cast
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : x ∈ Set.Ico ((n : ℝ) / (1 + δ)) n
    · simp only [F, if_pos hn, Set.indicator_of_mem hn]
      push_cast
      ring
    · simp [F, hn]
  have hi : IntegrableOn (fun x => ∑ n ∈ Finset.Ioc 0 ⌊3 * N⌋₊, F n x)
      (Set.Icc N (2 * N)) volume := integrable_finsetSum _ (fun n _ => hF n)
  refine ⟨hi.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (heq hx).symm), ?_⟩
  rw [setIntegral_congr_fun measurableSet_Icc heq, integral_finsetSum _ (fun n _ => hF n)]
  unfold chiCubicHyperbolicVonMangoldtAverage
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show F n = (Set.Ico ((n : ℝ) / (1 + δ)) n).indicator
    (fun x => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (chiCubicHyperbolicPrimeKernel N M x / ((δ * x : ℝ) : ℂ))) from rfl,
    setIntegral_indicator measurableSet_Ico, integral_const_mul]
  simp only [δ, Set.inter_comm]

/-- The exact finite dual average differs negligibly from the continuous signed
kernel integral, without deleting exceptional intervals. -/
theorem chiCubicHyperbolicVonMangoldtAverage_tendsto (M : ℕ) :
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N *
      ‖chiCubicHyperbolicVonMangoldtAverage N M -
        ∫ x in Set.Icc N (2 * N), chiCubicHyperbolicPrimeKernel N M x‖)
      atTop (𝓝 0) := by
  have hδ : ∀ᶠ N : ℝ in atTop, N ^ ((1 : ℝ) / 5 - 1) ≤ 1 / 2 := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 1 - (1 : ℝ) / 5 by norm_num)).eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 2)
    simpa only [neg_sub] using h
  apply (chiCubicHyperbolicPrimeDensityError_tendsto M).2.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ), hδ] with N hN hδN
  have hN1 : 1 < N := by linarith
  have h := chiCubicHyperbolicVonMangoldtAverage_eq hN1 hδN M
  have hi := integrableOn_chiCubicHyperbolicPrimeKernel hN1 M
  have heq : chiCubicHyperbolicVonMangoldtAverage N M -
      ∫ x in Set.Icc N (2 * N), chiCubicHyperbolicPrimeKernel N M x =
        chiCubicHyperbolicPrimeDensityError N M := by
    rw [h.2, ← integral_sub h.1 hi]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    push_cast
    ring
  rw [heq]

/-- The original sharp cubic on one ordered hyperbolic sector. -/
def chiCubicHyperbolicPrimePacket (N : ℝ) (M : ℕ) : ℂ :=
  ∑ q ∈ primeProfileBand N, ∑ p ∈ primeProfileBand N, ∑ r ∈ primeProfileBand N,
    if p ≠ r ∧ |(p : ℝ) - r| < |(q : ℝ) - r| ∧
      |(p : ℝ) - r| * |(q : ℝ) - r| ≤ (M : ℝ) * r
    then primeGaussianCubicMainEntry N p q r else 0

/-- The actual von Mangoldt sum before short-window averaging. -/
def chiCubicHyperbolicVonMangoldtSum (N : ℝ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
    (ArithmeticFunction.vonMangoldt n : ℂ) * chiCubicHyperbolicPrimeKernel N M n

private theorem vonMangoldt_sum_sub_primePacket {N : ℝ} (hN : 0 ≤ N) (M : ℕ) :
    chiCubicHyperbolicVonMangoldtSum N M - chiCubicHyperbolicPrimePacket N M =
      ∑ n ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => ¬n.Prime),
        (ArithmeticFunction.vonMangoldt n : ℂ) * chiCubicHyperbolicPrimeKernel N M n := by
  classical
  have hp : (∑ n ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter Nat.Prime,
      (ArithmeticFunction.vonMangoldt n : ℂ) * chiCubicHyperbolicPrimeKernel N M n) =
        chiCubicHyperbolicPrimePacket N M := by
    change (∑ q ∈ primeProfileBand N, _) = _
    unfold chiCubicHyperbolicPrimePacket
    refine Finset.sum_congr rfl fun q hq => ?_
    have hprime := (primeProfileBand_mem hN hq).1
    have hlog : (Real.log q : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.log_pos (by exact_mod_cast hprime.one_lt)))
    rw [ArithmeticFunction.vonMangoldt_apply_prime hprime,
      chiCubicHyperbolicPrimeKernel_nat hN M hq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs
    · field_simp
    · simp only [mul_zero]
  have hsum := Finset.sum_filter_add_sum_filter_not (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊) Nat.Prime
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * chiCubicHyperbolicPrimeKernel N M n)
  unfold chiCubicHyperbolicVonMangoldtSum
  rw [← hsum, hp, add_sub_cancel_left]

private theorem primePower_error_bound {N : ℝ} (hN : 4 ≤ N)
    (hlog : 1 ≤ Real.log N) (M : ℕ) :
    ‖chiCubicHyperbolicVonMangoldtSum N M - chiCubicHyperbolicPrimePacket N M‖ ≤
      (64 * Real.pi * ((M : ℝ) + 1)) * (8 * Real.sqrt N * Real.log N) := by
  classical
  have hN0 : 0 < N := by linarith
  let S := (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => ¬n.Prime)
  have hmass : (∑ n ∈ S, ArithmeticFunction.vonMangoldt n) ≤
      Chebyshev.psi (2 * N) - Chebyshev.theta (2 * N) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hn, hp⟩ := Finset.mem_filter.1 hn
      exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2
        ⟨lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.1 hn).1,
          (Finset.mem_Ioc.1 hn).2⟩, hp⟩
    · intro n _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
  have hleak : Chebyshev.psi (2 * N) - Chebyshev.theta (2 * N) ≤
      8 * Real.sqrt N * Real.log N := by
    have hpsi := Chebyshev.psi_sub_theta_le (show 1 ≤ 2 * N by linarith)
    have hs : Real.sqrt (2 * N) ≤ 2 * Real.sqrt N := by
      nlinarith [Real.sq_sqrt hN0.le, Real.sq_sqrt (show 0 ≤ 2 * N by positivity),
        Real.sqrt_nonneg N, Real.sqrt_nonneg (2 * N)]
    have hl : Real.log (2 * N) ≤ 2 * Real.log N := by
      rw [Real.log_mul (by norm_num) hN0.ne']
      have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    calc
      _ ≤ 2 * Real.sqrt (2 * N) * Real.log (2 * N) := hpsi
      _ ≤ 2 * (2 * Real.sqrt N) * (2 * Real.log N) := by
        gcongr
        exact Real.log_nonneg (by linarith)
      _ = _ := by ring
  rw [vonMangoldt_sum_sub_primePacket hN0.le M]
  calc
    ‖∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℂ) * chiCubicHyperbolicPrimeKernel N M n‖ ≤
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n * (64 * Real.pi * ((M : ℝ) + 1)) := by
      apply norm_sum_le_of_le
      intro n hn
      have hnI := Finset.mem_Ioc.1 (Finset.mem_filter.1 hn).1
      have hnN : (n : ℝ) ∈ Set.Icc N (2 * N) :=
        ⟨((Nat.floor_lt hN0.le).1 hnI.1).le,
          (Nat.le_floor_iff (show 0 ≤ 2 * N by positivity)).1 hnI.2⟩
      rw [norm_mul, Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_mul_of_nonneg_left (norm_chiCubicHyperbolicPrimeKernel_le hN hlog M hnN)
        ArithmeticFunction.vonMangoldt_nonneg
    _ = (64 * Real.pi * ((M : ℝ) + 1)) * ∑ n ∈ S, ArithmeticFunction.vonMangoldt n := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmass.trans hleak) (by positivity)

/-- All proper prime powers can be removed from the literal ordered hyperbolic
von Mangoldt sum with o(N/log² N) error. -/
theorem chiCubicHyperbolicPrimePowerError_tendsto (M : ℕ) :
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N *
      ‖chiCubicHyperbolicVonMangoldtSum N M - chiCubicHyperbolicPrimePacket N M‖)
      atTop (𝓝 0) := by
  have hbase : Tendsto (fun N : ℝ => Real.log N ^ 3 / Real.sqrt N) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ) / 2) (3 : ℕ)
      (by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast, Real.sqrt_eq_rpow] using h
  have hlim := hbase.const_mul (8 * (64 * Real.pi * ((M : ℝ) + 1)))
  simp only [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with N hN
    exact mul_nonneg (div_nonneg (sq_nonneg _) (by linarith)) (norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (4 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
      with N hN hlog
    have hN0 : 0 < N := by linarith
    have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN0).ne'
    calc
      _ ≤ Real.log N ^ 2 / N * ((64 * Real.pi * ((M : ℝ) + 1)) *
          (8 * Real.sqrt N * Real.log N)) :=
        mul_le_mul_of_nonneg_left (primePower_error_bound hN hlog M) (by positivity)
      _ = _ := by
        field_simp
        nlinarith [Real.sq_sqrt hN0.le]

end RHTower
end
