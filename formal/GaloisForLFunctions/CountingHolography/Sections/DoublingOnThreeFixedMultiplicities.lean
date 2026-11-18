import GaloisForLFunctions.CountingHolography.Sections.BoundsFromSuccessiveDoublingDifferences
import GaloisForLFunctions.CountingHolography.Sections.TheJetRadiusOfPoleBalancedSections
import GaloisForLFunctions.CountingHolography.Sections.PrimeTraceWindows

/-!
# A doubling comparison on three squares

The divisor with coefficients 1, 2 and −1 on the squares of 1, n and
2n+1 kills the positive pole. Its degree is a doubling difference of
the spline trace, up to a bounded short lag. Iteration toward infinity
recovers the trace from a one-sided bound on the difference.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology SquareRootThreshold SurfaceOfSpecZ ArithmeticOrientationGeometry
open ArithmeticScatteringHolography RenormalizedIntersectionTheory Zeta23

open SquareDoubling

private def squareTrace (n : ℕ) : ℝ := realSplineTrace (2*Real.log n)

private theorem trace_bound {s : ℝ} (hs : 0 ≤ s) (hw : zetaZeroWidth ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → |squareTrace n| ≤ C*(scale n)^(2*s) := by
  obtain ⟨C,hC⟩ := (zeta_splineOrbit_rate_iff_zetaZeroWidth_le hs).mpr hw
  refine ⟨|C|,abs_nonneg _,fun n hn => ?_⟩
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h := hC (2*Real.log n) (mul_nonneg two_pos.le (Real.log_natCast_nonneg n))
  rw [orbitCorr_splineCycle_eq] at h
  have he : Real.exp (s*(2*Real.log n)) = (n : ℝ)^(2*s) := by
    rw [Real.rpow_def_of_pos hpos]
    congr 1
    ring
  rw [he] at h
  exact h.trans (mul_le_mul (le_abs_self _) (Real.rpow_le_rpow hpos.le
    (le_add_of_nonneg_right zero_le_one) (mul_nonneg two_pos.le hs)) (Real.rpow_nonneg hpos.le _) (abs_nonneg _))

private theorem trace_sublinear : Tendsto (fun n => squareTrace n/scale n) atTop (𝓝 0) := by
  have hp := tendsto_primePair_degree_div_sqrt.comp (tendsto_pow_atTop (α := ℕ) two_ne_zero)
  have hc : Tendsto (fun n : ℕ => 2*(splineSeries 0).re/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have htr : Tendsto (fun n : ℕ => squareTrace n/(n : ℝ)) atTop (𝓝 0) := by
    have h := (hp.sub hc).div_const 2
    rw [sub_zero,zero_div] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    change (integerProbe _ (primePair (n^2))/Real.sqrt ((n^2 : ℕ) : ℝ) -
      2*(splineSeries 0).re/(n : ℝ))/2 = _
    rw [integerProbe_primePair (pow_pos (by omega : 0<n) 2),Nat.cast_pow,
      Real.sqrt_sq (Nat.cast_nonneg (α := ℝ) n),Real.log_pow]
    unfold squareTrace realSplineTrace
    push_cast
    ring
  apply squeeze_zero_norm' (a := fun n : ℕ => |squareTrace n/(n : ℝ)|) _ (by simpa only [abs_zero] using htr.abs)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [Real.norm_eq_abs,abs_div,abs_div,abs_of_nonneg hn'.le,abs_of_nonneg (zero_le_one.trans (scale_ge_one n))]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hn' (le_add_of_nonneg_right zero_le_one)

private theorem short_lag (n : ℕ) (hn : 0 < n) :
    0 ≤ 2*(Real.log ((2*n+1 : ℕ) : ℝ)-Real.log n) ∧
      2*(Real.log ((2*n+1 : ℕ) : ℝ)-Real.log n) ≤ 2*Real.log 3 := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hx : 0 < ((2*n+1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos (2*n))
  rw [← Real.log_div hx.ne' hn'.ne']
  have hlo : (1:ℝ) ≤ ((2*n+1 : ℕ) : ℝ)/n := (le_div_iff₀ hn').mpr (by push_cast; linarith only [hn'])
  have hup : ((2*n+1 : ℕ) : ℝ)/n ≤ 3 := (div_le_iff₀ hn').mpr (by
    push_cast
    linarith only [show (1:ℝ) ≤ n by exact_mod_cast hn])
  exact ⟨mul_nonneg two_pos.le (Real.log_nonneg hlo),
    mul_le_mul_of_nonneg_left (Real.log_le_log (zero_lt_one.trans_le hlo) hup) two_pos.le⟩

private theorem doubling_remainder :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 0 < n →
      |integerProbe _ (successorSquareTriple n)-(4*squareTrace n-2*squareTrace (2*n+1))| ≤ D := by
  let J := Set.Icc (0:ℝ) (2*Real.log 3)
  have hc : Continuous (fun t => |realSplineTrace t|) := (Complex.continuous_re.comp continuous_splineSeries).abs
  have hcompact : IsCompact ((fun t => |realSplineTrace t|) '' J) := isCompact_Icc.image hc
  obtain ⟨K,hK⟩ := hcompact.bddAbove
  refine ⟨6*|realSplineTrace 0|+4*|K|,by positivity,fun n hn => ?_⟩
  let t := 2*(Real.log ((2*n+1 : ℕ) : ℝ)-Real.log n)
  have ht : |realSplineTrace t| ≤ |K| := (hK ⟨t,short_lag n hn,rfl⟩).trans (le_abs_self _)
  have he : integerProbe _ (successorSquareTriple n)-(4*squareTrace n-2*squareTrace (2*n+1)) =
      6*realSplineTrace 0-4*realSplineTrace t := by rw [integerProbe_successorSquareTriple hn]; unfold squareTrace t; ring
  rw [he]
  have h := abs_sub_le (6*realSplineTrace 0) 0 (4*realSplineTrace t)
  simp only [sub_zero,zero_sub,abs_neg,abs_mul] at h
  norm_num at h
  linarith only [h,ht]

/-- Removing the stationary and short interactions leaves the two long
traces with a bounded error independent of the conductor. -/
theorem successorSquare_degree_long_lags :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 0 < n →
      |integerProbe _ (successorSquareTriple n) -
        (4*realSplineTrace (2*Real.log n) -
         2*realSplineTrace (2*Real.log ((2*n+1:ℕ):ℝ)))| ≤ D := doubling_remainder

/-- The absolute signed degree on the three square conductors grows at
most with the actual zero width on each of its two long lags. -/
theorem successorSquare_degree_at_width : ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 0 < n →
    |integerProbe _ (successorSquareTriple n)| ≤ A*((n:ℝ)+1)^(2*zetaZeroWidth) := by
  let w := zetaZeroWidth
  obtain ⟨C,hC,h⟩ := trace_bound zetaZeroWidth_nonneg le_rfl
  obtain ⟨D,hD,hd⟩ := doubling_remainder
  refine ⟨4*C+2*C*(2:ℝ)^(2*w)+D,by positivity,fun n hn => ?_⟩
  have h₁ := abs_le.mp (h n hn)
  have h₂ := h (2*n+1) (Nat.succ_pos _)
  rw [scale_step,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (zero_le_one.trans (scale_ge_one n))] at h₂
  have hD' := le_mul_of_one_le_right hD (Real.one_le_rpow (scale_ge_one n)
    (mul_nonneg two_pos.le zetaZeroWidth_nonneg))
  have he := abs_le.mp (hd n hn)
  change |integerProbe _ (successorSquareTriple n)| ≤
    (4*C+2*C*(2:ℝ)^(2*w)+D)*(scale n)^(2*w)
  change |squareTrace (2*n+1)| ≤ C*((2:ℝ)^(2*w)*(scale n)^(2*w)) at h₂
  rw [abs_le]
  constructor <;> linarith only [h₁.1,h₁.2,(abs_le.mp h₂).1,(abs_le.mp h₂).2,he.1,he.2,hD']

/-- The signed degree divided by the square-root conductor tends to zero. -/
theorem successorSquare_degree_sublinear :
    Tendsto (fun n : ℕ => integerProbe _ (successorSquareTriple n)/((n:ℝ)+1)) atTop (𝓝 0) := by
  obtain ⟨A,_,hA⟩ := successorSquare_degree_at_width
  have he := (sublinear_power (show 2*zetaZeroWidth < 1 by
    linarith only [ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths])).const_mul A
  apply squeeze_zero_norm' _ (by simpa only [mul_zero] using he)
  filter_upwards [eventually_ge_atTop 1] with n hn
  change |integerProbe _ (successorSquareTriple n)/scale n| ≤ A*((scale n)^(2*zetaZeroWidth)/scale n)
  rw [abs_div,abs_of_nonneg (zero_le_one.trans (scale_ge_one n)),← mul_div_assoc]
  exact div_le_div_of_nonneg_right (hA n hn) (zero_le_one.trans (scale_ge_one n))

/-- The width is detected by three fixed coefficients, with a single
negative graph and a uniformly bounded positive pole-free coefficient mass. -/
theorem zetaZeroWidth_le_iff_successorSquareTriple {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1/2) :
    zetaZeroWidth ≤ s ↔ ∃ A : ℝ, ∀ n : ℕ, 0 < n →
      -(A*((n : ℝ)+1)^(2*s)) ≤ integerProbe _ (successorSquareTriple n) := by
  obtain ⟨D,hD,hd⟩ := doubling_remainder
  have hr : 0 ≤ 2*s := mul_nonneg two_pos.le hs
  constructor
  · intro hw
    obtain ⟨A,hA,h⟩ := successorSquare_degree_at_width
    refine ⟨A,fun n hn => (neg_le_neg ?_).trans (abs_le.mp (h n hn)).1⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (scale_ge_one n)
      (mul_le_mul_of_nonneg_left hw two_pos.le)) hA
  · rintro ⟨A,hA⟩
    have hstep (n : ℕ) (hn : 0 < n) : squareTrace (2*n+1) ≤ 2*squareTrace n+((A+D)/2)*(scale n)^(2*s) := by
      have hh := hA n hn
      change -(A*(scale n)^(2*s)) ≤ _ at hh
      have hD' := le_mul_of_one_le_right hD (Real.one_le_rpow (scale_ge_one n) hr)
      linarith only [hh,(abs_le.mp (hd n hn)).2,hD']
    obtain ⟨M,hM⟩ := lower_of_doubling_difference (by linarith : 2*s<1) trace_sublinear hstep
    apply (zetaZeroWidth_le_iff_bddBelow_of_powGaps hs hs' (by norm_num)
      (powGaps_kthPowers (k := 2) (by norm_num))).mpr
    refine ⟨2 * |M| * (2:ℝ)^(2*s),?_⟩
    rintro d ⟨n,hn,rfl⟩
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hp := Nat.cast_nonneg (α := ℝ) n
    have hb := Real.rpow_le_rpow (zero_le_one.trans (scale_ge_one n))
      (show scale n ≤ 2*(n : ℝ) by unfold scale; linarith only [hn']) hr
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hp] at hb
    have hmul := mul_le_mul (le_abs_self M) hb (Real.rpow_nonneg (zero_le_one.trans (scale_ge_one n)) _) (abs_nonneg _)
    rw [← orbitCorr_eq_re_lagStructure_spline,orbitCorr_splineCycle_eq,Nat.cast_pow,Real.log_pow]
    have he := (Real.rpow_natCast_mul hp 2 s).symm
    change ((n : ℝ)^2)^s = (n : ℝ)^(2*s) at he
    rw [he]
    change -(_*(n : ℝ)^(2*s)) ≤ 2*squareTrace n
    linarith only [hmul,hM n hn]

private theorem width_zero_of_upper_degree
    (h : ∃ A : ℝ, ∀ n : ℕ, 0 < n → integerProbe _ (successorSquareTriple n) ≤ A) :
    zetaZeroWidth ≤ 0 := by
  obtain ⟨A,hA⟩ := h
  obtain ⟨D,_,hD⟩ := doubling_remainder
  let F (n : ℕ) := -squareTrace n
  have hlim : Tendsto (fun n => F n / scale n) atTop (𝓝 0) := by
    simpa only [F,neg_div,neg_zero] using trace_sublinear.neg
  have hrec (n : ℕ) (hn : 0<n) :
      F (2*n+1) ≤ 2*F n+((A+D)/2)*(scale n)^(0:ℝ) := by
    rw [Real.rpow_zero,mul_one]
    unfold F
    linarith only [hA n hn,(abs_le.mp (hD n hn)).1]
  obtain ⟨M,hM⟩ := lower_of_doubling_difference (by norm_num : (0:ℝ)<1) hlim hrec
  apply (zetaZeroWidth_le_iff_bddAbove_of_powGaps (a := 0) le_rfl (by norm_num)
    (powGaps_kthPowers (k := 2) (by norm_num))).mpr
  refine ⟨2*M,?_⟩
  rintro d ⟨n,hn,rfl⟩
  rw [← orbitCorr_eq_re_lagStructure_spline,orbitCorr_splineCycle_eq,Nat.cast_pow,Real.log_pow,
    Real.rpow_zero,mul_one]
  have hbound := hM n hn
  simp only [Real.rpow_zero,mul_one,F,neg_le_neg_iff] at hbound
  change 2*squareTrace n ≤ 2*M
  exact mul_le_mul_of_nonneg_left hbound two_pos.le

private theorem unbounded_frequently {f : ℕ → ℝ}
    (h : ¬∃ K : ℝ, ∀ n : ℕ, 0 < n → f n ≤ K) (A : ℝ) :
    ∃ᶠ n : ℕ in atTop, A < f n := by
  by_contra hc
  obtain ⟨N,hN⟩ := eventually_atTop.mp (not_frequently.mp hc)
  apply h
  let S := ∑ k ∈ range N, |f k|
  have hS : 0 ≤ S := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨|A|+S,fun n _ => ?_⟩
  by_cases hn : N ≤ n
  · linarith only [le_of_not_gt (hN n hn),le_abs_self A,hS]
  have hh := single_le_sum (f := fun k => |f k|) (fun _ _ => abs_nonneg _) (mem_range.mpr (lt_of_not_ge hn))
  have : |f n| ≤ S := hh
  linarith only [this,le_abs_self (f n),abs_nonneg A]

/-- Off the critical line, both signs of the degrees of the same integral
divisors are unbounded on arbitrarily late conductors. -/
theorem successorSquare_degrees_of_not_rh (hRH : ¬RiemannHypothesis) (A : ℝ) :
    (∃ᶠ n : ℕ in atTop, A < integerProbe _ (successorSquareTriple n)) ∧
      (∃ᶠ n : ℕ in atTop, integerProbe _ (successorSquareTriple n) < -A) := by
  have hn : ¬zetaZeroWidth ≤ 0 := fun h =>
    hRH (riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr (le_antisymm h zetaZeroWidth_nonneg))
  refine ⟨unbounded_frequently (fun h => hn (width_zero_of_upper_degree h)) A,?_⟩
  have hh : ¬∃ K : ℝ, ∀ n : ℕ, 0<n → -integerProbe _ (successorSquareTriple n) ≤ K := by
    rintro ⟨K,hK⟩
    apply hn
    apply (zetaZeroWidth_le_iff_successorSquareTriple (s := 0) le_rfl (by norm_num)).mpr
    refine ⟨K,fun n h => ?_⟩
    simp only [mul_zero,Real.rpow_zero,mul_one]
    linarith only [hK n h]
  exact (unbounded_frequently hh A).mono fun n h => by linarith only [h]

/-- On the fixed coefficient family the ordinary-prime generator alone
detects every strip. Its allowance has no extra conductor-dependent mass. -/
theorem zetaZeroWidth_le_iff_successorSquare_generator {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1/2) :
    zetaZeroWidth ≤ s ↔ ∃ A : ℝ, ∀ n : ℕ, 0 < n → ∃ᶠ m : ℕ in atTop,
      Real.log (ordinaryPrimeGenerator (m • successorSquareTriple n) : ℝ) ≤
        A*((n : ℝ)+1)^(2*s)*(m : ℝ)^2 := by
  rw [zetaZeroWidth_le_iff_successorSquareTriple hs hs']
  obtain ⟨C,hC,h⟩ := poleBalanced_ordinary_error
  let D := 16*C+4
  have hD : 0 ≤ D := by unfold D; positivity
  have herr (n : ℕ) (hn : 0 < n) : ∀ᶠ m : ℕ in atTop,
      |Real.log (ordinaryPrimeGenerator (m • successorSquareTriple n) : ℝ) +
        integerProbe _ (successorSquareTriple n)*(m : ℝ)^2| ≤ D*(m : ℝ)^2 := by
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (sum_nonneg fun _ _ => abs_nonneg _) (successorSquareTriple_mass n) 2) hC
    apply (h _ _ (positivePoleDegree_successorSquareTriple hn)).mono
    intro m he
    exact he.trans (mul_le_mul_of_nonneg_right (by unfold D; linarith only [hm]) (sq_nonneg _))
  have hslack (n : ℕ) : D ≤ D*((n : ℝ)+1)^(2*s) :=
    le_mul_of_one_le_right hD (Real.one_le_rpow (scale_ge_one n) (mul_nonneg two_pos.le hs))
  constructor
  · rintro ⟨A,hA⟩
    refine ⟨A+D,fun n hn => ((herr n hn).mono fun m hm => ?_).frequently⟩
    have h₁ := mul_le_mul_of_nonneg_right (hA n hn) (sq_nonneg (m : ℝ))
    have h₂ := mul_le_mul_of_nonneg_right (hslack n) (sq_nonneg (m : ℝ))
    linarith only [(abs_le.mp hm).2,h₁,h₂]
  · rintro ⟨A,hA⟩
    refine ⟨A+D,fun n hn => ?_⟩
    obtain ⟨m,hm,he,hm1⟩ := ((hA n hn).and_eventually ((herr n hn).and (eventually_ge_atTop 1))).exists
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < (m : ℝ)^2)).mp
    have hh := mul_le_mul_of_nonneg_right (hslack n) (sq_nonneg (m : ℝ))
    linarith only [hm,(abs_le.mp he).1,hh]

/-- The numerator of each rational product must fit inside its denominator
times the same integer base raised to m², at unbounded multiplicities. -/
theorem riemannHypothesis_iff_successorSquare_power :
    RiemannHypothesis ↔ ∃ B : ℕ, 0 < B ∧ ∀ n : ℕ, 0 < n → ∃ᶠ m : ℕ in atTop,
      ordinaryPrimeGenerator (m • successorSquareTriple n) ≤ (B : ℚ)^(m^2) := by
  have hRH : RiemannHypothesis ↔ zetaZeroWidth ≤ 0 :=
    riemannHypothesis_iff_zetaZeroWidth_eq_zero.trans
      ⟨fun h => h.le,fun h => le_antisymm h zetaZeroWidth_nonneg⟩
  rw [hRH,zetaZeroWidth_le_iff_successorSquare_generator (s := 0) le_rfl (by norm_num)]
  simp only [mul_zero,Real.rpow_zero,mul_one]
  constructor
  · rintro ⟨A,hA⟩
    let B := ⌈Real.exp A⌉₊
    have hB : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos A)
    have hl : A ≤ Real.log B := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hB)).mpr (Nat.le_ceil _)
    refine ⟨B,hB,fun n hn => (hA n hn).mono fun m hm => ?_⟩
    have he := generator_le_power_iff (m • successorSquareTriple n) hB 1 m
    simp only [one_mul,Nat.cast_one,one_pow,mul_one] at he
    exact he.mpr (hm.trans (mul_le_mul_of_nonneg_right hl (sq_nonneg _)))
  · rintro ⟨B,hB,h⟩
    refine ⟨Real.log B,fun n hn => (h n hn).mono fun m hm => ?_⟩
    have he := generator_le_power_iff (m • successorSquareTriple n) hB 1 m
    simp only [one_mul,Nat.cast_one,one_pow,mul_one] at he
    exact he.mp hm

/-- Four units of total variation suffice on the integral pole hyperplane.
The base of the finite-place bound is shared by all horizons and divisors. -/
theorem riemannHypothesis_iff_poleBalanced_mass_four :
    RiemannHypothesis ↔ ∃ B : ℕ, 0 < B ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
      positivePoleDegree a = 0 → (∑ i, |(a i : ℝ)|) ≤ 4 → ∃ᶠ m : ℕ in atTop,
        ordinaryPrimeGenerator (m • a) ≤ (B : ℚ)^(m^2) := by
  constructor
  · intro hRH
    obtain ⟨C,hC,h⟩ := poleBalanced_ordinary_error
    let B := ⌈Real.exp (16*C+4)⌉₊
    have hB : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos _)
    have hl : 16*C+4 ≤ Real.log B := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hB)).mpr (Nat.le_ceil _)
    refine ⟨B,hB,fun N a ha hmass => ((h N a ha).mono fun m he => ?_).frequently⟩
    have hq := mul_nonneg (riemannHypothesis_iff_integerProbes.mp hRH N a) (sq_nonneg (m : ℝ))
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) hmass 2) hC
    have hh := mul_le_mul_of_nonneg_right (show C*(∑ i, |(a i : ℝ)|)^2+4 ≤ Real.log B by
      linarith only [hm,hl]) (sq_nonneg (m : ℝ))
    have hb := generator_le_power_iff (m • a) hB 1 m
    simp only [one_mul,Nat.cast_one,one_pow,mul_one] at hb
    exact hb.mpr (by linarith only [(abs_le.mp he).2,hq,hh])
  · rintro ⟨B,hB,h⟩
    exact riemannHypothesis_iff_successorSquare_power.mpr ⟨B,hB,fun n hn =>
      h _ _ (positivePoleDegree_successorSquareTriple hn) (successorSquareTriple_mass n)⟩

/-- At arbitrarily late conductors the signed lattice has ordinary small
sections realizing its full Weil degree, with no archimedean allowance. -/
theorem frequently_successorSquare_sections :
    ∃ᶠ n : ℕ in atTop, (∀ᶠ m : ℕ in atTop,
      Real.log (generator (m • successorSquareTriple n) : ℝ) < radius (m • successorSquareTriple n)) ∧
      Tendsto (fun m : ℕ => (splineCount (m • successorSquareTriple n) : ℝ)/(m : ℝ)^2)
        atTop (𝓝 (integerProbe _ (successorSquareTriple n))) := by
  have hgood : ∃ᶠ n : ℕ in atTop, 0 < integerProbe _ (successorSquareTriple n) := by
    by_cases hRH : RiemannHypothesis
    · apply Eventually.frequently
      apply Eventually.of_forall
      intro n
      apply integerProbe_pos_of_rh hRH
      intro hz
      have hsum : ∑ i, (1:ℝ)*(successorSquareTriple n i : ℝ) = 2 := by
        unfold successorSquareTriple
        rw [sum_threeGraphDivisor (fun _ => 1)]
        norm_num
      norm_num [hz] at hsum
    · exact (successorSquare_degrees_of_not_rh hRH 0).1
  apply hgood.mono
  intro n hn
  refine ⟨eventually_log_generator_lt_radius hn,?_⟩
  simpa only [max_eq_left hn.le] using splineCount_tateLimit (successorSquareTriple n)

#print axioms frequently_successorSquare_sections
#print axioms riemannHypothesis_iff_poleBalanced_mass_four
#print axioms riemannHypothesis_iff_successorSquare_power
#print axioms zetaZeroWidth_le_iff_successorSquareTriple

end GaloisForLFunctions.CountingHolography.Sections
