import GaloisForLFunctions.CountingHolography.Sections.ThePrimeExponentsOnTheSquareDiagonal
import GaloisForLFunctions.CountingHolography.Sections.CriticalZerosSeparateThePrimeProfileFromFactorialKernels
import Mathlib.NumberTheory.LSeries.Deriv
import GaloisForLFunctions.RHTower.BVPrimeWindowReciprocalReflection
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Mellin scaling and the holomorphic error of the square prices

The factor two in the prime valuation cancels the Jacobian of the square
scale. Rounding the prime coordinates gives a Dirichlet series holomorphic
on Re s > 3, including after taking either part of each prime valuation.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset ArithmeticFunction _root_.RHTower MeasureTheory Filter Topology
open BiScaleUncertainty.ChebyshevGauge ArithmeticWeightTheory _root_.RHTower.WeilDeletion
open scoped NNReal

/-- Mellin integral of one prime row in the conductor variable. The
parameter of the prime weight is s/2 − 1 in the conductor Dirichlet series. -/
theorem mellin_square_conductor_row {p : ℝ} (hp : 0 < p) (s : ℂ) :
    mellin (fun t : ℝ => (2:ℂ)*squarePrimeWeight (p/t^2)) (2-s) =
      (p:ℂ)^(1-s/2)*mellin squarePrimeWeight (s/2-1) := by
  have he : (fun t : ℝ => (2:ℂ)*squarePrimeWeight (p/t^2)) =
      fun t : ℝ => (2:ℂ) • (fun x : ℝ => squarePrimeWeight (p*x)) (t^(-2:ℝ)) := by
    funext t
    have ht : t^(-2:ℝ)=(t^2)⁻¹ := by
      simpa only [Nat.cast_ofNat,zpow_neg,zpow_ofNat] using Real.rpow_neg_natCast t 2
    simp only [ht,div_eq_mul_inv,smul_eq_mul]
  rw [he,mellin_const_smul,mellin_comp_rpow,mellin_comp_mul_left _ _ hp]
  norm_num only [abs_neg,abs_two,Complex.ofReal_neg,Complex.ofReal_ofNat]
  rw [show (2-s)/(-2:ℂ)=s/2-1 by ring,show -(s/2-1)=1-s/2 by ring]
  simp only [smul_eq_mul,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_ofNat]
  ring

/-- The right-endpoint quadrature error at an arbitrary real mesh density.
At prime p the conductor mesh has density exactly √p. -/
def realMeshMellinError (W : CompactBVPrimeWindow) (k : ℝ) (s : ℂ) :=
  (1/k) • (∑ i ∈ range ⌈W.upper*k⌉₊, W.mellinIntegrand s (((i+1:ℕ):ℝ)/k))-W.mellinTransform s

/-- Compact-uniform BV quadrature on the square-root meshes. -/
theorem realMeshMellinError_uniform (W : CompactBVPrimeWindow) {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ s ∈ K, ∀ k : ℝ, 1 ≤ k → ‖realMeshMellinError W k s‖ ≤ Q/k := by
  obtain ⟨B,C,hB,hbound,hLip⟩ := W.exists_mellinWeight_uniform_lipschitz_bound hK hne
  let V := (eVariationOn W.toFun Set.univ).toReal
  let Q := B*V+V*C*(W.upper+1)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have htop : 0 ≤ W.upper+1 := by linarith only [W.upper_pos]
  refine ⟨Q,add_nonneg (mul_nonneg hB hV) (mul_nonneg (mul_nonneg hV C.coe_nonneg) htop),?_⟩
  intro s hs k hk
  have hk' := zero_lt_one.trans_le hk
  let N := ⌈W.upper*k⌉₊
  let D := (N:ℝ)/k
  have hD : 0 ≤ D := div_nonneg (Nat.cast_nonneg _) hk'.le
  have hlo : W.upper ≤ D := (le_div_iff₀ hk').mpr (Nat.le_ceil _)
  have hhi : D ≤ W.upper+1 := by
    apply (div_le_iff₀ hk').mpr
    have he : (N:ℝ) < W.upper*k+1 := Nat.ceil_lt_add_one (mul_nonneg W.upper_pos.le hk'.le)
    linarith only [he,hk]
  have hvar := HTGeometry.eVariationOn_mul_le_of_norm_le_of_lipschitzOn
    (f := W.toFun) (h := W.mellinWeight s) (a := 0) (b := D) (Mf := V) (Mh := B)
    hD (W.boundedVariation.mono (Set.subset_univ _)) hV hB
    (fun x _ => W.norm_le_totalVariation x) (fun x _ => hbound s hs x) (hLip s hs).lipschitzOnWith
  have hv : (eVariationOn (W.mellinIntegrand s) (Set.Icc 0 D)).toReal ≤ Q := by
    have h := ENNReal.toReal_mono (by simp) hvar
    rw [ENNReal.toReal_ofReal] at h
    · have hm : (eVariationOn W.toFun (Set.Icc 0 D)).toReal ≤ V :=
        ENNReal.toReal_mono W.boundedVariation (eVariationOn.mono _ (Set.subset_univ _))
      calc _ ≤ B*(eVariationOn W.toFun (Set.Icc 0 D)).toReal+V*C*D := by
                simpa only [CompactBVPrimeWindow.mellinIntegrand,sub_zero] using h
        _ ≤ Q := add_le_add (mul_le_mul_of_nonneg_left hm hB) (mul_le_mul_of_nonneg_left hhi (mul_nonneg hV C.coe_nonneg))
    · positivity
  have hint : (∫ t in (0:ℝ)..D, W.mellinIntegrand s t)=W.mellinTransform s := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    have h := W.support_mellinIntegrand_subset s hx
    exact ⟨W.lower_pos.trans_le h.1,h.2.trans hlo⟩
  have hquad := HTGeometry.norm_rightEndpoint_riemannSum_sub_integral_le_eVariationOn
    (g := W.mellinIntegrand s) (k := k) hk' (n := N)
    (W.mellinIntegrand_integrable s).intervalIntegrable (W.mellinIntegrand_boundedVariationOn s hD)
  rw [realMeshMellinError,← hint]
  refine le_trans ?_ ((mul_le_mul_of_nonneg_left hv (show 0 ≤ 1/k by positivity)).trans_eq (by ring))
  simpa only [Nat.cast_add,Nat.cast_one] using hquad

private theorem differentiable_realMeshMellinError (W : CompactBVPrimeWindow) (k : ℝ) :
    Differentiable ℂ (realMeshMellinError W k) := by
  intro s
  apply DifferentiableAt.sub _ (W.differentiable_mellinTransform s)
  apply DifferentiableAt.const_smul
  apply DifferentiableAt.fun_sum
  intro i _
  let x := ((i+1:ℕ):ℝ)/k
  have hx : (W.mellinBase x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (W.mellinBase_pos x).ne'
  exact (((differentiableAt_id.neg).const_cpow (Or.inl hx)).const_mul (W x) :
    DifferentiableAt ℂ (fun z : ℂ => W x*(W.mellinBase x:ℂ)^(-z)) s)

/-- Quadrature error of a von Mangoldt row at the mesh √k, after extracting
the conductor Dirichlet scaling. -/
def sqrtMeshErrorTerm (W : CompactBVPrimeWindow) (k : ℕ) (s : ℂ) :=
  if k = 0 then 0 else (vonMangoldt k:ℂ)*(k:ℂ)^(1-s/2)*realMeshMellinError W (Real.sqrt k) s

private theorem differentiable_sqrtMeshErrorTerm (W : CompactBVPrimeWindow) (k : ℕ) :
    Differentiable ℂ (sqrtMeshErrorTerm W k) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simpa only [sqrtMeshErrorTerm,if_pos rfl] using (differentiable_const (c := (0:ℂ)) : Differentiable ℂ (fun _ : ℂ => (0:ℂ)))
  have h : Differentiable ℂ (fun z : ℂ => (k:ℂ)^(1-z/2)) :=
    ((differentiable_id.div_const (2:ℂ)).const_sub 1).const_cpow (Or.inl (Nat.cast_ne_zero.mpr hk))
  exact ((h.const_mul (vonMangoldt k:ℂ)).mul (differentiable_realMeshMellinError W _)).congr
    (fun s => by simp only [sqrtMeshErrorTerm,if_neg hk])

/-- Normal convergence of the real-mesh error in Re s > 3. The majorant is
the absolutely convergent von Mangoldt series at (σ−1)/2 for σ > 3. -/
theorem locallySummable_sqrtMeshErrorTerm (W : CompactBVPrimeWindow) :
    SummableLocallyUniformlyOn (sqrtMeshErrorTerm W) {s : ℂ | 3 < s.re} := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro s hs
  change 3 < s.re at hs
  let r := (s.re-3)/2
  let σ := s.re-r
  have hr : 0 < r := half_pos (sub_pos.mpr hs)
  have hσ : 3 < σ := by dsimp only [σ,r]; linarith only [hs]
  obtain ⟨Q,hQ,herr⟩ := realMeshMellinError_uniform W (isCompact_closedBall s r)
    ⟨s,Metric.mem_closedBall_self hr.le⟩
  let b := (σ-1)/2
  let z : ℂ := b
  have hz : 1 < z.re := by change 1 < (σ-1)/2; linarith only [hσ]
  have hvm := LSeriesSummable_vonMangoldt hz
  refine ⟨Metric.ball s r,mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)),?_⟩
  apply HasSumUniformlyOn.of_norm_le_summable (hvm.norm.mul_left Q)
  intro k x hx
  rcases eq_or_ne k 0 with rfl | hk
  · simp [sqrtMeshErrorTerm]
  have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hk₁ : (1:ℝ) ≤ k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hroot : 1 ≤ Real.sqrt k := Real.one_le_sqrt.mpr hk₁
  have he := herr x (Metric.ball_subset_closedBall hx) _ hroot
  have hxσ : σ ≤ x.re := by
    have h := (Complex.abs_re_le_norm (x-s)).trans_lt (by simpa only [← dist_eq_norm] using Metric.mem_ball.mp hx)
    rw [Complex.sub_re,abs_lt] at h
    dsimp only [σ]; linarith only [h.1]
  rw [sqrtMeshErrorTerm,if_neg hk,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg,Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hk),
    LSeries.term_of_ne_zero hk,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg,Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hk)]
  have hRe : (1-x/2).re=1-x.re/2 := by simp
  rw [hRe]
  refine (mul_le_mul_of_nonneg_left he (mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg hk'.le _))).trans ?_
  calc _ = (Q*vonMangoldt k)*(k:ℝ)^((1-x.re)/2) := by
             rw [Real.sqrt_eq_rpow,show (1-x.re)/2=(1-x.re/2)-(1/2) by ring,Real.rpow_sub hk']
             ring
    _ ≤ (Q*vonMangoldt k)*(k:ℝ)^(-b) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hk₁ (by dsimp only [b]; linarith only [hxσ]))
          (mul_nonneg hQ vonMangoldt_nonneg)
    _ = _ := by rw [Real.rpow_neg hk'.le]; change _ = Q*(vonMangoldt k/(k:ℝ)^b); ring

theorem analytic_sqrtMeshErrorSeries (W : CompactBVPrimeWindow) :
    AnalyticOnNhd ℂ (fun s => ∑' k, sqrtMeshErrorTerm W k s) {s : ℂ | 3 < s.re} := by
  let U := {s : ℂ | 3 < s.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  exact ((locallySummable_sqrtMeshErrorTerm W).differentiableOn hopen
    (fun k => (differentiable_sqrtMeshErrorTerm W k).differentiableOn)).analyticOnNhd hopen

private abbrev lo := Real.exp (-8)
private abbrev hi := Real.exp 8
private def rootWindowRaw (t : ℝ) : ℂ := (2*t^2*squareLogProfile (-2*Real.log t):ℝ)

private theorem rootWindow_regular : ContDiffOn ℝ 1 rootWindowRaw (Set.Icc lo hi) := by
  have hH : ContDiff ℝ 1 splineAutoCorr := by
    rw [show splineAutoCorr=upow 1 7 from funext splineAutoCorr_eq_eight_boxes]
    exact (contDiff_upow one_pos 6).of_le (by norm_num)
  have hF : ContDiff ℝ 1 squareLogProfile := (contDiff_const.mul hH).sub
    (hH.comp (contDiff_id.sub contDiff_const))
  intro x hx
  have hx' : 0 < x := (Real.exp_pos _).trans_le hx.1
  have hl := Real.contDiffAt_log (n := 1) hx'.ne'
  apply ContDiffAt.contDiffWithinAt
  dsimp only [rootWindowRaw]
  fun_prop

/-- The compact conductor window at the square root of each prime. -/
def squareConductorBVWindow : CompactBVPrimeWindow where
  lower := lo
  upper := hi
  lower_pos := Real.exp_pos _
  lower_lt_upper := Real.exp_lt_exp.mpr (by norm_num)
  toFun := (Set.Icc lo hi).indicator rootWindowRaw
  eq_zero_off_support _ h := Set.indicator_of_notMem h _
  integrable := (rootWindow_regular.continuousOn.integrableOn_Icc).integrable_indicator measurableSet_Icc
  boundedVariation := by
    have hl : lo ≤ hi := (Real.exp_le_exp.mpr (by norm_num : (-8:ℝ) ≤ 8))
    apply CompactBVPrimeWindow.boundedVariationOn_univ_of_eq_zero_off_Icc hl _
      (fun x h => Set.indicator_of_notMem h _)
    have hc : ContDiffOn ℝ 1 ((Set.Icc lo hi).indicator rootWindowRaw) (Set.Icc lo hi) :=
      rootWindow_regular.congr fun x hx => Set.indicator_of_mem hx _
    obtain ⟨C,hC⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc lo hi) isCompact_Icc
    simpa only [Set.inter_self] using hC.locallyBoundedVariationOn lo hi (Set.left_mem_Icc.mpr hl) (Set.right_mem_Icc.mpr hl)

private theorem squareConductorBVWindow_apply {t : ℝ} (ht : 0 < t) :
    squareConductorBVWindow t=(2:ℂ)*t*squarePrimeWeight (1/t^2) := by
  have hl : Real.log (1/t^2) = -2*Real.log t := by rw [one_div,Real.log_inv,Real.log_pow]; push_cast; ring
  have he : Real.exp (-Real.log (1/t^2)/2)=t := by rw [hl,show -(-2*Real.log t)/2=Real.log t by ring,Real.exp_log ht]
  have hraw : rootWindowRaw t=(2:ℂ)*t*squarePrimeWeight (1/t^2) := by
    rw [rootWindowRaw,squarePrimeWeight,he,hl]; push_cast; ring
  change (Set.Icc lo hi).indicator rootWindowRaw t=_
  rw [← hraw]
  by_cases h : t∈Set.Icc lo hi
  · exact Set.indicator_of_mem h _
  rw [Set.indicator_of_notMem h]
  have hb := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
  have hb₀ := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  have hzero (x : ℝ) (hx : 8 < |x|) := splineAutoCorr_zero_outside hx
  rcases lt_or_ge t lo with htlo|htlo
  · have hx := (Real.log_lt_iff_lt_exp ht).mpr htlo
    have h₁ : 8 < |-2*Real.log t| := by linarith only [hx,le_abs_self (-2*Real.log t)]
    have h₂ : 8 < |-2*Real.log t-Real.log 4| := by linarith only [hx,hb,le_abs_self (-2*Real.log t-Real.log 4)]
    simp [rootWindowRaw,squareLogProfile,hzero _ h₁,hzero _ h₂]
  · have hx := (Real.lt_log_iff_exp_lt ht).mpr (lt_of_not_ge fun hhi => h ⟨htlo,hhi⟩)
    have h₁ : 8 < |-2*Real.log t| := by linarith only [hx,neg_abs_le (-2*Real.log t)]
    have h₂ : 8 < |-2*Real.log t-Real.log 4| := by linarith only [hx,hb₀,neg_abs_le (-2*Real.log t-Real.log 4)]
    simp [rootWindowRaw,squareLogProfile,hzero _ h₁,hzero _ h₂]

/-- The real-mesh window carries precisely the dyadic Mellin multiplier. -/
theorem squareConductorBVWindow_transform (s : ℂ) :
    squareConductorBVWindow.mellinTransform s=mellin squarePrimeWeight (s/2-1) := by
  let W := squareConductorBVWindow
  have hs : (∫ t in Set.Ioi (0:ℝ), W.mellinIntegrand s t)=W.mellinTransform s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    by_contra hn
    exact ht (W.lower_pos.trans_le (W.support_mellinIntegrand_subset s hn).1)
  have hm := mellin_square_conductor_row (p := 1) one_pos s
  simp only [Complex.ofReal_one,Complex.one_cpow,one_mul] at hm
  rw [← hs,← hm,mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht' : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [CompactBVPrimeWindow.mellinIntegrand_eq_raw,squareConductorBVWindow_apply ht,
    show 2-s-1=1+(-s) by ring,Complex.cpow_add _ _ ht',Complex.cpow_one,smul_eq_mul]
  ring

private abbrev S (n : ℕ) := ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1))
private abbrev q (n : ℕ) := ordinaryPrimeGenerator (n • successorSquareTriple n)

/-- Coefficient of the error series when reading each exact valuation and
its prime profile through the same real function. -/
def squareValuationReadingError (g : ℝ → ℝ) (n : ℕ) : ℂ :=
  ((∑ p ∈ S n, (g (deningerRatExp (q n) p:ℝ)-g (diagonalPrimeProfile n p))*vonMangoldt p : ℝ):ℂ)

/-- Every Lipschitz reading has holomorphic Dirichlet error throughout
the half-plane to the right of three. This applies separately to the
logarithms of the reduced numerator, denominator and their ratio. -/
theorem analytic_squareValuationReadingError {g : ℝ → ℝ} {K : ℝ ≥ 0} (hg : LipschitzWith K g) :
    AnalyticOnNhd ℂ (LSeries (squareValuationReadingError g)) {s : ℂ | 3 < s.re} := by
  obtain ⟨C,hC,h⟩ := diagonal_prime_exponent_profile_error
  have hbound (n : ℕ) (hn : n≠0) : ‖squareValuationReadingError g n‖ ≤ ((K:ℝ)*C)*(n:ℝ)^2 := by
    rw [squareValuationReadingError,Complex.norm_real,Real.norm_eq_abs]
    have hrow (p : ℕ) : |(g (deningerRatExp (q n) p:ℝ)-g (diagonalPrimeProfile n p))*vonMangoldt p| ≤
        K*(|(deningerRatExp (q n) p:ℝ)-diagonalPrimeProfile n p|*vonMangoldt p) := by
      rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg,← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.dist_eq] using
        hg.dist_le_mul (deningerRatExp (q n) p:ℝ) (diagonalPrimeProfile n p)) vonMangoldt_nonneg
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (fun p _ => hrow p)).trans ?_)
    rw [← mul_sum,mul_assoc]
    exact mul_le_mul_of_nonneg_left (h (Nat.pos_of_ne_zero hn)) K.coe_nonneg
  have hab := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (f := squareValuationReadingError g)
    (x := 2) ⟨K*C,fun n hn => by simpa only [Real.rpow_two] using hbound n hn⟩
  have h₃ : LSeries.abscissaOfAbsConv (squareValuationReadingError g) ≤ (3:EReal) := by
    convert hab using 1 <;> norm_num
  exact fun s hs => LSeries_analyticOnNhd _ s (h₃.trans_lt (by exact_mod_cast hs : (3:EReal) < (s.re:EReal)))

end GaloisForLFunctions.CountingHolography.Sections
