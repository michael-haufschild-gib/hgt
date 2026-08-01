import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointBoundaryGrowth
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

open scoped BigOperators InnerProductSpace

open Complex

namespace RHTower

noncomputable section

theorem summable_routeKPhysicalEndpointWeight_sq_mul_log_pow
    (k : ℕ) :
    Summable (fun p : Nat.Primes =>
      physicalPrimeEndpointWeight p ^ 2 * Real.log (p : ℝ) ^ k) := by
  have hnat :=
    summable_abs_log_natCast_pow_mul_rpow_neg (k + 2) 2 (by norm_num)
  have hnat' : Summable (fun n : ℕ =>
      Real.log n ^ (k + 2) / (n : ℝ) ^ 2) := by
    apply hnat.congr
    intro n
    rcases n with _ | n
    · simp
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hlog : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_natCast_nonneg _
    rw [abs_of_nonneg hlog, Real.rpow_neg hn.le]
    rw [show ((n + 1 : ℕ) : ℝ) ^ (2 : ℝ) =
        ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) by
      exact Real.rpow_natCast _ 2]
    rw [div_eq_mul_inv]
  have hprime : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ (k + 2) / (p : ℝ) ^ 2) :=
    hnat'.comp_injective Subtype.val_injective
  apply hprime.congr
  intro p
  rw [physicalPrimeEndpointWeight]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  field_simp [hp0]
  ring

theorem summable_routeKPhysicalEndpointWeight_sq_mul_one_add_log_pow
    (k : ℕ) :
    Summable (fun p : Nat.Primes =>
      physicalPrimeEndpointWeight p ^ 2 *
        (1 + Real.log (p : ℝ)) ^ k) := by
  let term : ℕ → Nat.Primes → ℝ := fun m p =>
    (Nat.choose k m : ℝ) *
      (physicalPrimeEndpointWeight p ^ 2 *
        Real.log (p : ℝ) ^ (k - m))
  have hterm : ∀ m ∈ Finset.range (k + 1), Summable (term m) := by
    intro m hm
    exact (summable_routeKPhysicalEndpointWeight_sq_mul_log_pow
      (k - m)).mul_left (Nat.choose k m : ℝ)
  have hsum : Summable (fun p : Nat.Primes =>
      ∑ m ∈ Finset.range (k + 1), term m p) := by
    have hsum' : Summable
        (∑ m ∈ Finset.range (k + 1), term m) := by
      refine Finset.sum_induction (s := Finset.range (k + 1))
        (f := fun m => term m)
        (p := fun f : Nat.Primes → ℝ => Summable f) ?_ ?_ ?_
      · intro f g hf hg
        exact hf.add hg
      · exact summable_zero
      · intro m hm
        exact hterm m hm
    refine hsum'.congr fun p => ?_
    simp only [Finset.sum_apply]
  apply hsum.congr
  intro p
  rw [add_pow]
  simp only [one_pow, one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [term]
  ring

theorem norm_digamma_two_add_I_div_two_le
    {t : ℝ} (ht : 9 ≤ |t|) :
    ‖Complex.digamma (((2 : ℂ) + (t : ℂ) * I) / 2)‖ ≤
      Real.log |t| + GaloisForLFunctions.digammaVerticalLogConstant := by
  let T : ℝ := |t| / 2
  have hT1 : 1 ≤ T := by dsimp [T]; linarith
  have hbase := GaloisForLFunctions.norm_digamma_vertical_le_log
    (σ := (1 : ℝ)) (t := T) (by norm_num) hT1 hT1
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have habspos : 0 < |t| := by linarith
  have hTle : T ≤ |t| := by dsimp [T]; linarith
  have hlog : Real.log T ≤ Real.log |t| := Real.log_le_log hTpos hTle
  have hnorm :
      ‖Complex.digamma (((2 : ℂ) + (t : ℂ) * I) / 2)‖ =
        ‖Complex.digamma (((1 : ℝ) : ℂ) + (T : ℂ) * I)‖ := by
    by_cases ht0 : 0 ≤ t
    · have harg : ((2 : ℂ) + (t : ℂ) * I) / 2 =
          (((1 : ℝ) : ℂ) + (T : ℂ) * I) := by
        apply Complex.ext <;>
          simp [T, abs_of_nonneg ht0, Complex.mul_re, Complex.mul_im]
      rw [harg]
    · have htneg : t < 0 := lt_of_not_ge ht0
      have harg : ((2 : ℂ) + (t : ℂ) * I) / 2 =
          (starRingEnd ℂ) (((1 : ℝ) : ℂ) + (T : ℂ) * I) := by
        apply Complex.ext
        · simp [T, abs_of_neg htneg, Complex.div_re, Complex.div_im,
            Complex.mul_re]
        · simp [T, abs_of_neg htneg, Complex.div_re, Complex.div_im,
            Complex.mul_im]
          ring
      rw [harg, ReflectedDigammaAnomaly.digamma_conj, norm_conj]
  rw [hnorm]
  linarith

def routeKArchLineTwoConstant : ℝ :=
  2 + |Real.log Real.pi| / 2 +
    GaloisForLFunctions.digammaVerticalLogConstant / 2

theorem norm_logDeriv_archFactor_lineTwo_le
    {t : ℝ} (ht : 9 ≤ |t|) :
    ‖logDeriv archFactor ((2 : ℂ) + (t : ℂ) * I)‖ ≤
      Real.log |t| / 2 + routeKArchLineTwoConstant := by
  let s : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s, Complex.mul_re] at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s, Complex.mul_re] at hre
  have hspos : 0 < s.re := by simp [s, Complex.mul_re]
  have hs_norm : 1 ≤ ‖s‖ := by
    calc
      1 ≤ |s.re| := by simp [s, Complex.mul_re]
      _ ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hsinv : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one, one_div]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hs_norm)).2 hs_norm
  have hsm1inv : ‖1 / (s - 1)‖ ≤ 1 := by
    have hre : (s - 1).re = 1 := by
      norm_num [s, Complex.sub_re, Complex.mul_re]
    have hnorm : 1 ≤ ‖s - 1‖ := by
      have h := Complex.abs_re_le_norm (s - 1)
      rw [hre, abs_one] at h
      exact h
    rw [norm_div, norm_one, one_div]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hnorm)).2 hnorm
  have hdig := norm_digamma_two_add_I_div_two_le ht
  have hgamma : ‖GaloisForLFunctions.gammaRealLogConnection s‖ ≤
      |Real.log Real.pi| / 2 +
        (Real.log |t| + GaloisForLFunctions.digammaVerticalLogConstant) / 2 := by
    rw [GaloisForLFunctions.gammaRealLogConnection]
    calc
      ‖-(((Real.log Real.pi : ℝ) : ℂ) / 2) + Complex.digamma (s / 2) / 2‖ ≤
          ‖-(((Real.log Real.pi : ℝ) : ℂ) / 2)‖ +
            ‖Complex.digamma (s / 2) / 2‖ := norm_add_le _ _
      _ = |Real.log Real.pi| / 2 + ‖Complex.digamma (s / 2)‖ / 2 := by
        simp [Real.norm_eq_abs]
      _ ≤ _ := by
        have hdig' : ‖Complex.digamma (s / 2)‖ ≤
            Real.log |t| + GaloisForLFunctions.digammaVerticalLogConstant := by
          simpa [s] using hdig
        linarith
  rw [logDeriv_archFactor_closed hspos hs0 hs1]
  calc
    ‖1 / s + 1 / (s - 1) + GaloisForLFunctions.gammaRealLogConnection s‖ ≤
        ‖1 / s‖ + ‖1 / (s - 1)‖ +
          ‖GaloisForLFunctions.gammaRealLogConnection s‖ := by
      calc
        _ ≤ ‖1 / s + 1 / (s - 1)‖ +
            ‖GaloisForLFunctions.gammaRealLogConnection s‖ := norm_add_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ 1 + 1 + (|Real.log Real.pi| / 2 +
        (Real.log |t| + GaloisForLFunctions.digammaVerticalLogConstant) / 2) := by
      gcongr
    _ = Real.log |t| / 2 + routeKArchLineTwoConstant := by
      rw [routeKArchLineTwoConstant]
      ring

def routeKLineTwoArithmeticMass : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2

def routeKLineTwoGrowthConstant : ℝ :=
  1 / 2 + routeKArchLineTwoConstant + routeKLineTwoArithmeticMass

theorem norm_seamFluxCochain_lineTwo_le
    {t : ℝ} (ht : 9 ≤ |t|) :
    ‖seamFluxCochain ((2 : ℂ) + (t : ℂ) * I)‖ ≤
      routeKLineTwoGrowthConstant * (1 + |t|) ^ 9 := by
  let s : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hsre : s.re = 2 := by simp [s, Complex.mul_re]
  have harith := logDeriv_xi_eq_arithmetic
    (s := s) (by rw [hsre]; norm_num)
  have harch := norm_logDeriv_archFactor_lineTwo_le ht
  have hL := norm_LSeries_vonMangoldt_le
    (s := s) (by rw [hsre]; norm_num)
  have hL' :
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖ ≤
        routeKLineTwoArithmeticMass := by
    simpa [routeKLineTwoArithmeticMass, hsre] using hL
  have hpow1 : 1 ≤ (1 + |t|) ^ 9 :=
    one_le_pow₀ (by linarith [abs_nonneg t] : 1 ≤ 1 + |t|)
  have habspos : 0 < |t| := by linarith
  have hlogbase : Real.log |t| ≤ 1 + |t| :=
    (Real.log_le_sub_one_of_pos habspos).trans (by linarith)
  have hlogpow : Real.log |t| ≤ (1 + |t|) ^ 9 :=
    hlogbase.trans (le_self_pow₀ (by linarith) (by norm_num))
  have harchC : 0 ≤ routeKArchLineTwoConstant := by
    rw [routeKArchLineTwoConstant,
      GaloisForLFunctions.digammaVerticalLogConstant]
    positivity
  have hmassC : 0 ≤ routeKLineTwoArithmeticMass := by
    rw [routeKLineTwoArithmeticMass]
    exact tsum_nonneg fun n =>
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hbound :
      Real.log |t| / 2 + routeKArchLineTwoConstant +
          routeKLineTwoArithmeticMass ≤
        routeKLineTwoGrowthConstant * (1 + |t|) ^ 9 := by
    rw [routeKLineTwoGrowthConstant]
    nlinarith
  have hsplit :
      logDeriv xi s =
        logDeriv archFactor s -
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    rw [harith, logDeriv_archFactor_closed
        (by rw [hsre]; norm_num)
        (by intro h; have := congrArg Complex.re h; simp [s, Complex.mul_re] at this)
        (by intro h; have := congrArg Complex.re h; simp [s, Complex.mul_re] at this),
      logDeriv_Gammaℝ_eq (by rw [hsre]; norm_num),
      GaloisForLFunctions.gammaRealLogConnection]
    ring
  rw [seamFluxCochain, norm_neg]
  change ‖logDeriv xi s‖ ≤ _
  rw [hsplit]
  calc
    ‖logDeriv archFactor s -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖ ≤
      ‖logDeriv archFactor s‖ +
        ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖ :=
      norm_sub_le _ _
    _ ≤ (Real.log |t| / 2 + routeKArchLineTwoConstant) +
        routeKLineTwoArithmeticMass := add_le_add harch hL'
    _ ≤ _ := hbound

theorem exists_norm_seamFluxCochain_lineTwo_global_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖seamFluxCochain ((2 : ℂ) + (t : ℂ) * I)‖ ≤
        C * (1 + |t|) ^ 9 := by
  have han : ∀ t : ℝ,
      AnalyticAt ℂ seamFluxCochain ((2 : ℂ) + (t : ℂ) * I) := by
    intro t
    have hxi : AnalyticAt ℂ xi ((2 : ℂ) + (t : ℂ) * I) :=
      xi_analyticOnNhd_univ _ (Set.mem_univ _)
    have hxi0 : xi ((2 : ℂ) + (t : ℂ) * I) ≠ 0 :=
      xi_ne_zero_of_one_le_re (by simp [Complex.mul_re])
    change AnalyticAt ℂ (fun z => -logDeriv xi z)
      ((2 : ℂ) + (t : ℂ) * I)
    exact (hxi.deriv.div hxi hxi0).neg
  have hcont : Continuous (fun t : ℝ =>
      seamFluxCochain ((2 : ℂ) + (t : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have harg : ContinuousAt
        (fun u : ℝ => (2 : ℂ) + (u : ℂ) * I) t := by fun_prop
    have houter : ContinuousAt seamFluxCochain
        ((2 : ℂ) + (t : ℂ) * I) := (han t).continuousAt
    have hcomp := ContinuousAt.comp
      (f := fun u : ℝ => (2 : ℂ) + (u : ℂ) * I)
      (g := seamFluxCochain) houter harg
    simpa [Function.comp_def] using hcomp
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  let C : ℝ := max (max C₀ routeKLineTwoGrowthConstant) 0
  have hC0 : 0 ≤ C := le_max_right _ _
  refine ⟨C, hC0, ?_⟩
  intro t
  have hpow : 1 ≤ (1 + |t|) ^ 9 :=
    one_le_pow₀ (by linarith [abs_nonneg t] : 1 ≤ 1 + |t|)
  by_cases ht : 9 ≤ |t|
  · have hhigh := norm_seamFluxCochain_lineTwo_le ht
    have hconst : routeKLineTwoGrowthConstant ≤ C :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have hgrowth0 : 0 ≤ (1 + |t|) ^ 9 := le_trans zero_le_one hpow
    exact hhigh.trans (mul_le_mul_of_nonneg_right hconst hgrowth0)
  · have htmem : t ∈ Set.Icc (-9 : ℝ) 9 := by
      rw [Set.mem_Icc, ← abs_le]
      linarith
    have hlow := hC₀ t htmem
    have hC₀C : C₀ ≤ C :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    calc
      ‖seamFluxCochain ((2 : ℂ) + (t : ℂ) * I)‖ ≤ C₀ := hlow
      _ ≤ C := hC₀C
      _ ≤ C * (1 + |t|) ^ 9 := by nlinarith

def routeKPhysicalEndpointCorrectionMass : ℝ :=
  ∑' pe : Nat.Primes × ℕ,
    |routeKPhysicalEndpointCorrectionCoefficient pe|

theorem routeKPhysicalEndpointCorrectionMass_nonneg :
    0 ≤ routeKPhysicalEndpointCorrectionMass :=
  tsum_nonneg fun _ => abs_nonneg _

theorem norm_xiPhysicalEndpointValuationCorrectionKernel_le
    (t : ℝ) :
    ‖xiPhysicalEndpointValuationCorrectionKernel t‖ ≤
      routeKPhysicalEndpointCorrectionMass := by
  rw [xiPhysicalEndpointValuationCorrectionKernel,
    routeKPhysicalEndpointCorrectionMass]
  calc
    ‖∑' pe, xiPhysicalEndpointValuationCorrectionKernelTerm t pe‖ ≤
        ∑' pe, ‖xiPhysicalEndpointValuationCorrectionKernelTerm t pe‖ :=
      norm_tsum_le_tsum_norm
        (summable_xiPhysicalEndpointValuationCorrectionKernelTerm t).norm
    _ = ∑' pe, |routeKPhysicalEndpointCorrectionCoefficient pe| := by
      apply tsum_congr
      intro pe
      rw [routeKPhysicalEndpointCorrectionKernelTerm_eq, norm_mul,
        Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp_ofReal_mul_I, mul_one]

theorem exists_norm_xiPhysicalEndpointCompletedKernel_global_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖xiPhysicalEndpointCompletedKernel t‖ ≤
        C * (1 + |t|) ^ 9 := by
  obtain ⟨C₁, hC₁, hlineOne⟩ :=
    exists_norm_seamFluxCochain_boundary_global_le
  obtain ⟨C₂, hC₂, hlineTwo⟩ :=
    exists_norm_seamFluxCochain_lineTwo_global_le
  let C := C₁ + 2 * C₂ + routeKPhysicalEndpointCorrectionMass
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg
      (add_nonneg hC₁ (mul_nonneg (by norm_num) hC₂))
      routeKPhysicalEndpointCorrectionMass_nonneg
  refine ⟨C, hC, ?_⟩
  intro t
  have hpow : 1 ≤ (1 + |t|) ^ 9 :=
    one_le_pow₀ (by linarith [abs_nonneg t] : 1 ≤ 1 + |t|)
  have hgrowth0 : 0 ≤ (1 + |t|) ^ 9 := le_trans zero_le_one hpow
  have hlineOne' :
      ‖xiCompletedApertureOffDiagonalKernel (1 / 2) t 0‖ ≤
        C₁ * (1 + |t|) ^ 9 := by
    convert hlineOne t using 1
    all_goals norm_num [xiCompletedApertureOffDiagonalKernel]
  have hlineTwo' :
      ‖xiCompletedApertureOffDiagonalKernel (3 / 2) t 0‖ ≤
        C₂ * (1 + |t|) ^ 9 := by
    convert hlineTwo t using 1
    all_goals norm_num [xiCompletedApertureOffDiagonalKernel]
  rw [xiPhysicalEndpointCompletedKernel]
  calc
    ‖xiCompletedApertureOffDiagonalKernel (1 / 2) t 0 -
        2 * xiCompletedApertureOffDiagonalKernel (3 / 2) t 0 +
          xiPhysicalEndpointValuationCorrectionKernel t‖ ≤
      ‖xiCompletedApertureOffDiagonalKernel (1 / 2) t 0‖ +
        2 * ‖xiCompletedApertureOffDiagonalKernel (3 / 2) t 0‖ +
          ‖xiPhysicalEndpointValuationCorrectionKernel t‖ := by
      calc
        _ ≤ ‖xiCompletedApertureOffDiagonalKernel (1 / 2) t 0 -
              2 * xiCompletedApertureOffDiagonalKernel (3 / 2) t 0‖ +
              ‖xiPhysicalEndpointValuationCorrectionKernel t‖ :=
          norm_add_le _ _
        _ ≤ (‖xiCompletedApertureOffDiagonalKernel (1 / 2) t 0‖ +
              ‖2 * xiCompletedApertureOffDiagonalKernel (3 / 2) t 0‖) +
              ‖xiPhysicalEndpointValuationCorrectionKernel t‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = _ := by norm_num
    _ ≤ C₁ * (1 + |t|) ^ 9 +
        2 * (C₂ * (1 + |t|) ^ 9) +
          routeKPhysicalEndpointCorrectionMass := by
      gcongr
      exact norm_xiPhysicalEndpointValuationCorrectionKernel_le t
    _ ≤ C₁ * (1 + |t|) ^ 9 +
        2 * (C₂ * (1 + |t|) ^ 9) +
          routeKPhysicalEndpointCorrectionMass * (1 + |t|) ^ 9 := by
      gcongr
      exact le_mul_of_one_le_right
        routeKPhysicalEndpointCorrectionMass_nonneg hpow
    _ = C * (1 + |t|) ^ 9 := by
      dsimp [C]
      ring

theorem exists_abs_xiPhysicalEndpointCompletedPrimeRatioRealKernel_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : Nat.Primes,
      |xiPhysicalEndpointCompletedPrimeRatioRealKernel p q| ≤
        C * (1 + |Real.log (p : ℝ) - Real.log (q : ℝ)|) ^ 9 := by
  obtain ⟨C, hC, hkernel⟩ :=
    exists_norm_xiPhysicalEndpointCompletedKernel_global_le
  refine ⟨C, hC, ?_⟩
  intro p q
  let t : ℝ := Real.log (p : ℝ) - Real.log (q : ℝ)
  have hpos : 0 ≤ (1 + |t|) ^ 9 := by positivity
  have hplus := hkernel t
  have hminus := hkernel (-t)
  have habsneg : |-t| = |t| := abs_neg t
  have hre :
      |((xiPhysicalEndpointCompletedKernel t +
          xiPhysicalEndpointCompletedKernel (-t)) / 2).re| ≤
        (‖xiPhysicalEndpointCompletedKernel t‖ +
          ‖xiPhysicalEndpointCompletedKernel (-t)‖) / 2 := by
    calc
      |((xiPhysicalEndpointCompletedKernel t +
          xiPhysicalEndpointCompletedKernel (-t)) / 2).re| ≤
        ‖(xiPhysicalEndpointCompletedKernel t +
          xiPhysicalEndpointCompletedKernel (-t)) / 2‖ :=
        Complex.abs_re_le_norm _
      _ ≤ (‖xiPhysicalEndpointCompletedKernel t‖ +
          ‖xiPhysicalEndpointCompletedKernel (-t)‖) / 2 := by
        rw [norm_div, norm_ofNat]
        gcongr
        exact norm_add_le _ _
  have hfinal :
      |((xiPhysicalEndpointCompletedKernel t +
          xiPhysicalEndpointCompletedKernel (-t)) / 2).re| ≤
        C * (1 + |t|) ^ 9 := calc
    |((xiPhysicalEndpointCompletedKernel t +
        xiPhysicalEndpointCompletedKernel (-t)) / 2).re| ≤
      (‖xiPhysicalEndpointCompletedKernel t‖ +
        ‖xiPhysicalEndpointCompletedKernel (-t)‖) / 2 := hre
    _ ≤ (C * (1 + |t|) ^ 9 + C * (1 + |-t|) ^ 9) / 2 := by
      gcongr
    _ = C * (1 + |t|) ^ 9 := by rw [habsneg]; ring
  simpa [xiPhysicalEndpointCompletedPrimeRatioRealKernel, t,
    sub_eq_add_neg] using hfinal

/-- Source matrix before Hilbert--Schmidt realization. -/
def routeKPhysicalEndpointCompletedPairKernel
    (pq : Nat.Primes × Nat.Primes) : ℂ :=
  (xiPhysicalEndpointCompletedPairResponse pq.1 pq.2 : ℂ)

theorem routeKPhysicalEndpointCompletedPairKernel_isHS :
    HilbertSchmidt.IsHS routeKPhysicalEndpointCompletedPairKernel := by
  obtain ⟨C, hC, hreal⟩ :=
    exists_abs_xiPhysicalEndpointCompletedPrimeRatioRealKernel_le
  let f : Nat.Primes → ℝ := fun p =>
    physicalPrimeEndpointWeight p ^ 2 *
      (1 + Real.log (p : ℝ)) ^ 18
  have hf : Summable f :=
    summable_routeKPhysicalEndpointWeight_sq_mul_one_add_log_pow 18
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    dsimp [f]
    positivity
  have hproduct : Summable (fun pq : Nat.Primes × Nat.Primes =>
      f pq.1 * f pq.2) := by
    apply (summable_prod_of_nonneg (fun pq =>
      mul_nonneg (hf0 pq.1) (hf0 pq.2))).2
    constructor
    · intro p
      exact hf.mul_left (f p)
    · have h : Summable (fun p : Nat.Primes =>
          f p * ∑' q : Nat.Primes, f q) :=
        hf.mul_right (∑' q : Nat.Primes, f q)
      apply h.congr
      intro p
      change f p * (∑' q : Nat.Primes, f q) =
        ∑' y : Nat.Primes, f p * f y
      rw [tsum_mul_left]
  have hmajor : Summable (fun pq : Nat.Primes × Nat.Primes =>
      C ^ 2 * (f pq.1 * f pq.2)) :=
    hproduct.mul_left (C ^ 2)
  apply Summable.of_nonneg_of_le
    (fun pq => sq_nonneg ‖routeKPhysicalEndpointCompletedPairKernel pq‖)
    (fun pq => ?_) hmajor
  rcases pq with ⟨p, q⟩
  have hpLog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_natCast_nonneg p
  have hqLog : 0 ≤ Real.log (q : ℝ) :=
    Real.log_natCast_nonneg q
  have hpWeight : 0 ≤ physicalPrimeEndpointWeight p := by
    rw [physicalPrimeEndpointWeight]
    positivity
  have hqWeight : 0 ≤ physicalPrimeEndpointWeight q := by
    rw [physicalPrimeEndpointWeight]
    positivity
  let t : ℝ := Real.log (p : ℝ) - Real.log (q : ℝ)
  have htBase0 : 0 ≤ 1 + |t| := by positivity
  have hreal' :
      |xiPhysicalEndpointCompletedPrimeRatioRealKernel p q| ≤
        C * (1 + |t|) ^ 9 := by
    simpa [t] using hreal p q
  have hgap :
      1 + |t| ≤
        (1 + Real.log (p : ℝ)) * (1 + Real.log (q : ℝ)) := by
    have habs :
        |Real.log (p : ℝ) - Real.log (q : ℝ)| ≤
          Real.log (p : ℝ) + Real.log (q : ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    dsimp [t]
    calc
      1 + |Real.log (p : ℝ) - Real.log (q : ℝ)| ≤
          1 + (Real.log (p : ℝ) + Real.log (q : ℝ)) := by linarith
      _ ≤ (1 + Real.log (p : ℝ)) *
          (1 + Real.log (q : ℝ)) := by
        nlinarith [mul_nonneg hpLog hqLog]
  have hgapPow :
      (1 + |t|) ^ 18 ≤
        ((1 + Real.log (p : ℝ)) *
          (1 + Real.log (q : ℝ))) ^ 18 :=
    pow_le_pow_left₀ htBase0 hgap 18
  have hentry :
      ‖routeKPhysicalEndpointCompletedPairKernel (p, q)‖ ≤
        physicalPrimeEndpointWeight p *
          physicalPrimeEndpointWeight q *
            (C * (1 + |t|) ^ 9) := by
    rw [routeKPhysicalEndpointCompletedPairKernel,
      Complex.norm_real, Real.norm_eq_abs,
      xiPhysicalEndpointCompletedPairResponse, abs_mul, abs_mul,
      abs_of_nonneg hpWeight, abs_of_nonneg hqWeight]
    gcongr
  have hentry0 :
      0 ≤ physicalPrimeEndpointWeight p *
          physicalPrimeEndpointWeight q *
            (C * (1 + |t|) ^ 9) := by positivity
  have hsq :
      ‖routeKPhysicalEndpointCompletedPairKernel (p, q)‖ ^ 2 ≤
        (physicalPrimeEndpointWeight p *
          physicalPrimeEndpointWeight q *
            (C * (1 + |t|) ^ 9)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hentry0).2 hentry
  calc
    ‖routeKPhysicalEndpointCompletedPairKernel (p, q)‖ ^ 2 ≤
        (physicalPrimeEndpointWeight p *
          physicalPrimeEndpointWeight q *
            (C * (1 + |t|) ^ 9)) ^ 2 := hsq
    _ = C ^ 2 *
        (physicalPrimeEndpointWeight p ^ 2 *
          physicalPrimeEndpointWeight q ^ 2 *
            (1 + |t|) ^ 18) := by ring
    _ ≤ C ^ 2 *
        (physicalPrimeEndpointWeight p ^ 2 *
          physicalPrimeEndpointWeight q ^ 2 *
            (((1 + Real.log (p : ℝ)) *
              (1 + Real.log (q : ℝ))) ^ 18)) := by
      gcongr
    _ = C ^ 2 * (f p * f q) := by
      dsimp [f]
      ring

/-- Completed physical-endpoint marked-prime boundary operator. -/
def routeKPhysicalEndpointCompletedPairOperator :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  HilbertSchmidt.toOperator
    routeKPhysicalEndpointCompletedPairKernel_isHS

theorem routeKPhysicalEndpointCompletedPairOperator_isHilbertSchmidt :
    routeKPhysicalEndpointCompletedPairOperator.IsHilbertSchmidt :=
  HilbertSchmidt.isHilbertSchmidt_toOperator
    routeKPhysicalEndpointCompletedPairKernel_isHS

theorem routeKPhysicalEndpointCompletedPairOperator_matrix
    (p q : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p)
      (routeKPhysicalEndpointCompletedPairOperator
          (routeKPrimeBasis q)) =
      (xiPhysicalEndpointCompletedPairResponse p q : ℂ) := by
  simp only [routeKPhysicalEndpointCompletedPairOperator,
    routeKPrimeBasis, lp.inner_single_left,
    RCLike.inner_apply, map_one,
    HilbertSchmidt.toOperator_single
      routeKPhysicalEndpointCompletedPairKernel_isHS]
  simp [routeKPhysicalEndpointCompletedPairKernel]

theorem routeKPhysicalEndpointCompletedPairKernel_hsAdjoint :
    HilbertSchmidt.hsAdjoint
        routeKPhysicalEndpointCompletedPairKernel =
      routeKPhysicalEndpointCompletedPairKernel := by
  funext pq
  rcases pq with ⟨p, q⟩
  rw [HilbertSchmidt.hsAdjoint,
    routeKPhysicalEndpointCompletedPairKernel,
    routeKPhysicalEndpointCompletedPairKernel,
    xiPhysicalEndpointCompletedPairResponse_symm]
  simp

theorem routeKPhysicalEndpointCompletedPairOperator_isSelfAdjoint :
    IsSelfAdjoint routeKPhysicalEndpointCompletedPairOperator := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff',
    routeKPhysicalEndpointCompletedPairOperator,
    HilbertSchmidt.adjoint_toOperator]
  simp only [routeKPhysicalEndpointCompletedPairKernel_hsAdjoint]

end

end RHTower
