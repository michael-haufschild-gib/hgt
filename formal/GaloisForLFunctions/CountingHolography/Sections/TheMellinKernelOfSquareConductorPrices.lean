import GaloisForLFunctions.CountingHolography.Sections.ThePrimeExponentsOnTheSquareDiagonal
import GaloisForLFunctions.CountingHolography.Sections.CriticalZerosSeparateThePrimeProfileFromFactorialKernels
import Mathlib.NumberTheory.LSeries.Deriv
import GaloisForLFunctions.RHTower.PrimeShiftResidueClosability
import GaloisForLFunctions.RHTower.BVPrimeWindowReciprocalReflection
import GaloisForLFunctions.CountingHolography.Sections.TheLogarithmicMomentOfTheSquarePrimeProfile
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

private def meshIndices (W : CompactBVPrimeWindow) (n : ℕ) := Ioc 0 ⌊((n:ℝ)/W.lower)^2⌋₊

private def rootMeshRow (W : CompactBVPrimeWindow) (n k : ℕ) : ℂ :=
  (vonMangoldt k:ℂ)*(Real.sqrt k:ℂ)*W ((n:ℝ)/Real.sqrt k)

private theorem mesh_support (W : CompactBVPrimeWindow) (n k : ℕ) (hne : rootMeshRow W n k ≠ 0) :
    k ∈ meshIndices W n := by
  have hk : k ≠ 0 := by rintro rfl; simp [rootMeshRow] at hne
  have hk' := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk) : 0 < (k:ℝ))
  have hband : (n:ℝ)/Real.sqrt k ∈ Set.Icc W.lower W.upper := by
    by_contra hu
    exact hne (by rw [rootMeshRow,W.eq_zero_off_support _ hu,mul_zero])
  have hs : Real.sqrt k ≤ (n:ℝ)/W.lower := (le_div_iff₀ W.lower_pos).mpr
    (by simpa only [mul_comm] using (le_div_iff₀ hk').mp hband.1)
  have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  rw [Real.sq_sqrt (Nat.cast_nonneg k)] at h
  exact mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hk,Nat.le_floor h⟩

private theorem rootMeshRow_bound (W : CompactBVPrimeWindow) (n : ℕ) {k : ℕ} (hk : k ∈ meshIndices W n) :
    ‖rootMeshRow W n k‖ ≤ ((n:ℝ)/W.lower)*(eVariationOn W.toFun Set.univ).toReal*vonMangoldt k := by
  let Y := (n:ℝ)/W.lower
  have hY : 0 ≤ Y := div_nonneg (Nat.cast_nonneg _) W.lower_pos.le
  have h₁ : (k:ℝ) ≤ Y^2 := (Nat.cast_le.mpr (mem_Ioc.mp hk).2).trans (Nat.floor_le (sq_nonneg Y))
  have h₂ := (Real.sqrt_le_sqrt h₁).trans_eq (Real.sqrt_sq hY)
  have h₃ := W.norm_le_totalVariation ((n:ℝ)/Real.sqrt k)
  rw [rootMeshRow,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left h₂ vonMangoldt_nonneg) h₃ (norm_nonneg _)
    (mul_nonneg vonMangoldt_nonneg hY)).trans_eq (by ring)

/-- The proper prime powers in a conductor row define an analytic Dirichlet
series on Re s > 3. Their log mass below x is bounded by a constant times √x. -/
def conductorPrimePowerError (W : CompactBVPrimeWindow) (n : ℕ) : ℂ :=
  ∑ k ∈ (meshIndices W n).filter (fun k => ¬k.Prime), rootMeshRow W n k

private theorem primePower_abscissa (W : CompactBVPrimeWindow) :
    LSeries.abscissaOfAbsConv (conductorPrimePowerError W) ≤ (3:EReal) := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let V := (eVariationOn W.toFun Set.univ).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hrow (n : ℕ) : ‖conductorPrimePowerError W n‖ ≤ (V*C/W.lower^2)*(n:ℝ)^2 := by
    let Y := (n:ℝ)/W.lower
    have hY : 0 ≤ Y := div_nonneg (Nat.cast_nonneg _) W.lower_pos.le
    have h := hC (Y^2)
    rw [Real.sqrt_sq hY,Chebyshev.psi_sub_theta_eq_sum_not_prime] at h
    refine (norm_sum_le _ _).trans ((sum_le_sum fun k hk => rootMeshRow_bound W _ (mem_filter.mp hk).1).trans ?_)
    rw [← mul_sum]
    exact (mul_le_mul_of_nonneg_left h (mul_nonneg hY hV)).trans_eq (by dsimp only [Y,V]; ring)
  have hab := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (f := conductorPrimePowerError W)
    (x := 2) ⟨V*C/W.lower^2,fun n _ => by simpa only [Real.rpow_two] using hrow n⟩
  convert hab using 1 <;> norm_num

theorem analytic_conductorPrimePowerError (W : CompactBVPrimeWindow) :
    AnalyticOnNhd ℂ (LSeries (conductorPrimePowerError W)) {s : ℂ | 3 < s.re} :=
  fun s hs => LSeries_analyticOnNhd _ s ((primePower_abscissa W).trans_lt (by exact_mod_cast hs : (3:EReal) < (s.re:EReal)))

/-- Moving square-root mesh with all von Mangoldt weights. -/
def squareMeshReading (W : CompactBVPrimeWindow) (n : ℕ) : ℂ :=
  ∑ k ∈ meshIndices W n, rootMeshRow W n k

private theorem squareMesh_norm_mass (W : CompactBVPrimeWindow) (n : ℕ) :
    (∑' k, ‖rootMeshRow W n k‖) ≤
      (7*(eVariationOn W.toFun Set.univ).toReal/W.lower^3)*(n:ℝ)^3 := by
  let Y := (n:ℝ)/W.lower
  have hY : 0 ≤ Y := div_nonneg (Nat.cast_nonneg _) W.lower_pos.le
  let V := (eVariationOn W.toFun Set.univ).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  rw [tsum_eq_sum (s := meshIndices W n) (fun k hk => norm_eq_zero.mpr
    (not_ne_iff.mp (fun h => hk (mesh_support W n k h))))]
  have hmass : (∑ k ∈ meshIndices W n, vonMangoldt k) ≤ 7*Y^2 := by
    have h := _root_.RHTower.sum_vonMangoldt_Icc_le_seven ⌊Y^2⌋₊
    have he : meshIndices W n=Icc 1 ⌊Y^2⌋₊ := by ext k; simp [meshIndices,Y,Nat.lt_iff_add_one_le]
    rw [he]
    exact h.trans (mul_le_mul_of_nonneg_left (Nat.floor_le (sq_nonneg Y)) (by norm_num))
  refine (sum_le_sum fun k hk => rootMeshRow_bound W _ hk).trans ?_
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left hmass (mul_nonneg hY hV)).trans_eq (by dsimp only [Y,V]; ring)

private def meshTerm (W : CompactBVPrimeWindow) (s : ℂ) (i : ℕ × ℕ) :=
  LSeries.term (fun n => rootMeshRow W n i.2) s i.1

private theorem summable_meshTerm (W : CompactBVPrimeWindow) {s : ℂ} (hs : 4 < s.re) :
    Summable (meshTerm W s) := by
  apply Summable.of_norm
  rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
  constructor
  · intro n
    apply summable_of_ne_finset_zero (s := meshIndices W n)
    intro k hk
    have hz : rootMeshRow W n k = 0 := not_ne_iff.mp fun h => hk (mesh_support W _ _ h)
    by_cases hn : n = 0
    · simp [meshTerm,hn]
    · simp [meshTerm,LSeries.term_of_ne_zero hn,hz]
  · let C := 7*(eVariationOn W.toFun Set.univ).toReal/W.lower^3
    have hC : 0 ≤ C := div_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (pow_nonneg W.lower_pos.le _)
    have hsum := (Real.summable_nat_rpow.mpr (by linarith only [hs] : 3-s.re < -1)).mul_left C
    apply Summable.of_nonneg_of_le (fun n => tsum_nonneg fun k => norm_nonneg _) _ hsum
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simpa [meshTerm] using mul_nonneg hC (Real.rpow_nonneg (by norm_num : (0:ℝ)≤0) (3-s.re))
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
    simp only [meshTerm,LSeries.term_of_ne_zero hn.ne',norm_div,Complex.norm_natCast_cpow_of_pos hn,div_eq_mul_inv,
      tsum_mul_right]
    refine (mul_le_mul_of_nonneg_right (squareMesh_norm_mass W n) (inv_nonneg.mpr (Real.rpow_nonneg hn'.le _))).trans_eq ?_
    rw [Real.rpow_sub hn',show (3:ℝ)=(3:ℕ) from rfl,Real.rpow_natCast]
    ring

private theorem sqrt_grid_factor {p n : ℕ} (hp : 0 < p) (hn : 0 < n) (s : ℂ) :
    let t := Real.sqrt p
    (p:ℂ)^(1-s/2)*((1/t:ℝ):ℂ)*(((n:ℝ)/t:ℝ):ℂ)^(-s) =
      (t:ℂ)/(n:ℂ)^s := by
  let t := Real.sqrt p
  have hp' : 0 < (p:ℝ) := Nat.cast_pos.mpr hp
  have ht : 0 < t := Real.sqrt_pos.mpr hp'
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have htC : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hnC : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hmul := Complex.mul_cpow_ofReal_nonneg (div_nonneg hn'.le ht.le) ht.le (-s)
  rw [show (((n:ℝ)/t:ℝ):ℂ)*(t:ℂ)=(n:ℂ) by push_cast; field_simp] at hmul
  have hpScale : (p:ℂ)^(1-s/2)=(t:ℂ)^2*(t:ℂ)^(-s) := by
    have hlog : Complex.log (p:ℂ)=2*Complex.log (t:ℂ) := by
      rw [← Complex.ofReal_natCast,← Complex.ofReal_log hp'.le,← Complex.ofReal_log ht.le]
      dsimp only [t]; rw [Real.log_sqrt hp'.le]; push_cast; ring
    rw [← Complex.cpow_ofNat (t:ℂ) 2,← Complex.cpow_add _ _ htC,
      Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp.ne'),Complex.cpow_def_of_ne_zero htC,hlog]
    congr 1; ring
  change (p:ℂ)^(1-s/2)*((1/t:ℝ):ℂ)*(((n:ℝ)/t:ℝ):ℂ)^(-s)=(t:ℂ)/(n:ℂ)^s
  rw [hpScale,Complex.ofReal_div,Complex.ofReal_one,div_eq_mul_inv,← Complex.cpow_neg,hmul]
  field_simp

private theorem mesh_column (W : CompactBVPrimeWindow) (s : ℂ) (k : ℕ) :
    (∑' n, meshTerm W s (n,k)) =
      W.mellinTransform s*LSeries.term (fun j => (vonMangoldt j:ℂ)) (s/2-1) k +
        sqrtMeshErrorTerm W k s := by
  rcases k.eq_zero_or_pos with rfl | hk
  · have hz (n : ℕ) : meshTerm W s (n,0)=0 := by
      rcases n.eq_zero_or_pos with rfl | hn <;> simp [meshTerm,LSeries.term,rootMeshRow]
    simp [hz,sqrtMeshErrorTerm]
  let t := Real.sqrt k
  let N := ⌈W.upper*t⌉₊
  have ht : 0 < t := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have hkC : (k:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hfin : (∑' n, meshTerm W s (n,k))=∑ i ∈ range N, meshTerm W s (i+1,k) := by
    rw [tsum_eq_sum (s := range (N+1)) (fun n hn => ?_),sum_range_succ']
    · simp [meshTerm]
    have hgt : N < n := by have h := mt mem_range.mpr hn; omega
    have hcast : W.upper*t < (n:ℝ) := (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr hgt)
    have hoff : (n:ℝ)/t ∉ Set.Icc W.lower W.upper :=
      fun h => (lt_div_iff₀ ht |>.mpr hcast).not_ge h.2
    rw [meshTerm,LSeries.term_of_ne_zero (by omega),rootMeshRow,W.eq_zero_off_support _ hoff,mul_zero,zero_div]
  let A := (vonMangoldt k:ℂ)*(k:ℂ)^(1-s/2)
  have hi (i : ℕ) : meshTerm W s (i+1,k)=A*((1/t:ℝ):ℂ)*W.mellinIntegrand s (((i+1:ℕ):ℝ)/t) := by
    have he := sqrt_grid_factor hk (Nat.succ_pos i) s
    rw [meshTerm,LSeries.term_of_ne_zero (Nat.succ_ne_zero _),rootMeshRow,W.mellinIntegrand_eq_raw]
    dsimp only [A]
    calc _ = (vonMangoldt k:ℂ)*W (((i+1:ℕ):ℝ)/t)*((t:ℂ)/((i+1:ℕ):ℂ)^s) := by ring
      _ = _ := by rw [← he]; ring
  rw [hfin]
  simp_rw [hi]
  rw [← mul_sum,sqrtMeshErrorTerm,if_neg hk.ne',LSeries.term_of_ne_zero hk.ne',
    realMeshMellinError,Complex.real_smul,div_eq_mul_inv,← Complex.cpow_neg,
    show -(s/2-1)=1-s/2 by ring]
  dsimp only [A,N,t]
  ring

/-- In the half-plane of absolute convergence, reversing the real meshes
identifies the Dirichlet series with the Mellin-weighted logarithmic derivative
plus an error analytic throughout Re s > 3. -/
theorem LSeries_squareMeshReading (W : CompactBVPrimeWindow) {s : ℂ} (hs : 4 < s.re) :
    LSeries (squareMeshReading W) s =
      W.mellinTransform s*(-deriv riemannZeta (s/2-1)/riemannZeta (s/2-1)) +
        ∑' k, sqrtMeshErrorTerm W k s := by
  have hd := summable_meshTerm W hs
  have hz : 1 < (s/2-1).re := by simp; linarith only [hs]
  have hmain := (LSeriesSummable_vonMangoldt hz).mul_left (W.mellinTransform s)
  have herr := (locallySummable_sqrtMeshErrorTerm W).summable
    (show s ∈ {z : ℂ | 3 < z.re} by exact lt_trans (by norm_num) hs)
  calc LSeries (squareMeshReading W) s = ∑' n : ℕ, ∑' k : ℕ, meshTerm W s (n,k) := by
         apply tsum_congr; intro n
         rcases n.eq_zero_or_pos with rfl | hn
         · simp [meshTerm]
         simp only [meshTerm,LSeries.term_of_ne_zero hn.ne',div_eq_mul_inv,tsum_mul_right]
         rw [tsum_eq_sum (s := meshIndices W n) (fun k hk => not_ne_iff.mp fun h => hk (mesh_support W _ _ h))]
         rfl
    _ = ∑' k : ℕ, ∑' n : ℕ, meshTerm W s (n,k) := hd.tsum_comm
    _ = _ := by
      simp_rw [mesh_column]
      rw [hmain.tsum_add herr,tsum_mul_left]
      change W.mellinTransform s*LSeries (fun k => (vonMangoldt k:ℂ)) (s/2-1)+_=_
      rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz]

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
  convert hab using 1 <;> norm_num

theorem analytic_squareValuationReadingError {g : ℝ → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    AnalyticOnNhd ℂ (LSeries (squareValuationReadingError g)) {s : ℂ | 3 < s.re} :=
  fun s hs => LSeries_analyticOnNhd _ s ((reading_abscissa hg).trans_lt (by exact_mod_cast hs : (3:EReal) < (s.re:EReal)))

private theorem squareMeshRow_profile {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    rootMeshRow squareConductorBVWindow n k =
      ((diagonalPrimeProfile n k*vonMangoldt k:ℝ):ℂ) := by
  let t := (n:ℝ)/Real.sqrt k
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  have ht : 0 < t := div_pos hn' (Real.sqrt_pos.mpr hk')
  have he : 1/t^2=(k:ℝ)/(n:ℝ)^2 := by
    rw [show t=(n:ℝ)/Real.sqrt k from rfl,div_pow,Real.sq_sqrt hk'.le]
    field_simp
  let y := (k:ℝ)/(n:ℝ)^2
  have hy : 0 < y := div_pos hk' (sq_pos_of_pos hn')
  have hexp : Real.exp (-Real.log y/2)=(Real.sqrt y)⁻¹ := by
    rw [neg_div,Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hy]
    congr 2; ring
  change (vonMangoldt k:ℂ)*(Real.sqrt k:ℂ)*squareConductorBVWindow t=_
  rw [squareConductorBVWindow_apply ht,he,diagonalPrimeProfile_eq_dilate hn hk]
  change _*((2:ℂ)*t*(Real.exp (-Real.log y/2)*squareLogProfile (Real.log y):ℝ))=
    ((2*(n:ℝ)*(squareLogProfile (Real.log y)/Real.sqrt y)*vonMangoldt k:ℝ):ℂ)
  rw [hexp]
  dsimp only [t]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hk').ne'] <;> ring

private theorem prime_mesh_profile_sum {n : ℕ} (hn : 0 < n) :
    squareMeshReading squareConductorBVWindow n - conductorPrimePowerError squareConductorBVWindow n =
      ∑ k ∈ S n, ((diagonalPrimeProfile n k*vonMangoldt k:ℝ):ℂ) := by
  classical
  let W := squareConductorBVWindow
  let f := rootMeshRow W n
  let I := meshIndices W n
  have hpart := sum_filter_add_sum_filter_not (s := I) (f := f) Nat.Prime
  have split : squareMeshReading W n - conductorPrimePowerError W n = ∑ k ∈ I.filter Nat.Prime, f k := by
    change (∑ k ∈ I, f k)-(∑ k ∈ I.filter (fun k => ¬k.Prime), f k)=_
    rw [← hpart,add_sub_cancel_right]
  have hsum : (∑' p : Nat.Primes, f p.val) = ∑ k ∈ I.filter Nat.Prime, f k := by
    let g := fun k => if k.Prime then f k else 0
    have h := tsum_subtype_eq_of_support_subset (f := g) (s := {k : ℕ | k.Prime})
      (fun k hk hp => hk (by simp [g,hp]))
    calc _ = ∑' p : Nat.Primes, g p.val := tsum_congr fun p => (if_pos p.property).symm
      _ = ∑' k, g k := h
      _ = _ := tsum_eq_sum fun k hk => by
        by_cases hp : k.Prime
        · have ho : k ∉ I := fun h => hk (mem_filter.mpr ⟨h,hp⟩)
          simp only [g,if_pos hp]
          exact not_ne_iff.mp fun h => ho (mesh_support W n k h)
        · simp [g,hp]
  let b := fun k : ℕ => Real.log k*
    (squareLogProfile (Real.log ((k:ℝ)/(n:ℝ)^2))/Real.sqrt ((k:ℝ)/(n:ℝ)^2))
  have hwindow : (∑' p : Nat.Primes, b p.val)=∑ k ∈ S n, b k := by
    simpa only [b,one_mul] using diagonal_prime_test_window hn (fun _ => 1)
  have hv (p : ℕ) (hp : p.Prime) : diagonalPrimeProfile n p*vonMangoldt p = (2*n)*b p := by
    rw [diagonalPrimeProfile_eq_dilate hn hp.pos,vonMangoldt_apply_prime hp]; dsimp only [b]; ring
  rw [split,← hsum]
  calc (∑' p : Nat.Primes, f p.val) = ∑' p : Nat.Primes, (2*(n:ℂ))*(b p.val:ℂ) := by
         apply tsum_congr; intro p; rw [show f p.val=_ from squareMeshRow_profile hn p.property.pos,hv p p.property]; push_cast; rfl
    _ = (2*(n:ℂ))*((∑ k ∈ S n, b k:ℝ):ℂ) := by rw [tsum_mul_left,← Complex.ofReal_tsum,hwindow]
    _ = _ := by
      rw [Complex.ofReal_sum,mul_sum]; refine sum_congr rfl fun k hk => ?_
      rw [hv k (mem_filter.mp hk).2]; push_cast; rfl

/-- Actual logarithm of the square-conductor price, as a complex Dirichlet coefficient. -/
def squareConductorPrice (n : ℕ) : ℂ := Real.log (q n:ℝ)

private def priceRounding (n : ℕ) := squareValuationReadingError id n

private theorem price_decomposition {n : ℕ} (hn : 0 < n) :
    squareConductorPrice n = squareMeshReading squareConductorBVWindow n -
      conductorPrimePowerError squareConductorBVWindow n + priceRounding n := by
  rw [prime_mesh_profile_sum hn]
  have hp : Real.log (q n:ℝ) = ∑ k ∈ S n, (deningerRatExp (q n) k:ℝ)*vonMangoldt k := by
    rw [log_ordinaryPrimeGenerator]; refine sum_congr rfl fun p h => ?_
    have he := ordinaryPrimeGenerator_exponent (n • successorSquareTriple n) p
    change deningerRatExp (q n) p = if p ∈ S n then _ else 0 at he
    rw [if_pos h] at he; rw [he]
  simp only [squareConductorPrice,hp,priceRounding,squareValuationReadingError,id_eq,Complex.ofReal_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  push_cast; ring

/-- Holomorphic remainder in the Dirichlet continuation of the actual prices. -/
def squareConductorAnalyticRemainder (s : ℂ) :=
  (∑' k, sqrtMeshErrorTerm squareConductorBVWindow k s) -
    LSeries (conductorPrimePowerError squareConductorBVWindow) s + LSeries priceRounding s

theorem analytic_squareConductorAnalyticRemainder :
    AnalyticOnNhd ℂ squareConductorAnalyticRemainder {s : ℂ | 3 < s.re} := by
  have hg : LipschitzWith 1 (id : ℝ → ℝ) := LipschitzWith.id
  exact ((analytic_sqrtMeshErrorSeries _).sub (analytic_conductorPrimePowerError _)).add
    (analytic_squareValuationReadingError hg)

/-- Meromorphic continuation from the absolutely convergent half-plane.
The only possible poles to the right of three arise from the shifted
logarithmic derivative of zeta. -/
theorem LSeries_squareConductorPrice {s : ℂ} (hs : 4 < s.re) :
    LSeries squareConductorPrice s =
      mellin squarePrimeWeight (s/2-1)*(-deriv riemannZeta (s/2-1)/riemannZeta (s/2-1)) +
        squareConductorAnalyticRemainder s := by
  let W := squareConductorBVWindow
  have ha := summable_meshTerm W hs
  have hW : LSeriesSummable (squareMeshReading W) s := ha.prod.congr fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [meshTerm]
    simp only [meshTerm,LSeries.term_of_ne_zero hn.ne',div_eq_mul_inv,tsum_mul_right]
    rw [tsum_eq_sum (s := meshIndices W n) (fun k hk => not_ne_iff.mp fun h => hk (mesh_support W _ _ h))]
    rfl
  have hp := primePower_abscissa W
  have hr := reading_abscissa (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ))
  have hs₃ : (3:EReal) < (s.re:EReal) := by exact_mod_cast lt_trans (by norm_num : (3:ℝ)<4) hs
  have hP := LSeriesSummable_of_abscissaOfAbsConv_lt_re (hp.trans_lt hs₃)
  have hR := LSeriesSummable_of_abscissaOfAbsConv_lt_re (hr.trans_lt hs₃)
  have he : LSeries squareConductorPrice s = LSeries (squareMeshReading W - conductorPrimePowerError W + priceRounding) s := by
    apply tsum_congr; intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · simp only [LSeries.term_of_ne_zero hn.ne',Pi.add_apply,Pi.sub_apply]; rw [price_decomposition hn]
  rw [he,LSeries_add (hW.sub hP) hR,LSeries_sub hW hP,LSeries_squareMeshReading W hs,
    squareConductorBVWindow_transform,squareConductorAnalyticRemainder]
  ring

/-- Value of the continued Dirichlet series away from the real polar point. -/
def squareConductorContinuation (s : ℂ) :=
  mellin squarePrimeWeight (s/2-1)*(-deriv riemannZeta (s/2-1)/riemannZeta (s/2-1)) +
    squareConductorAnalyticRemainder s

/-- Each zero to the right of the critical line gives a simple pole with
residue minus twice its multiplicity times the nonvanishing Mellin weight. -/
theorem squareConductorContinuation_zero_residue {ρ : ℂ} (hζ : riemannZeta ρ=0)
    (hhalf : 1/2 < ρ.re) (h₁ : ρ.re < 1) :
    let c := 2+2*ρ
    let A := -2*(zetaMultiplicity ρ:ℂ)*mellin squarePrimeWeight ρ
    A ≠ 0 ∧ Tendsto (fun s : ℂ => (s-c)*squareConductorContinuation s) (𝓝[≠] c) (𝓝 A) := by
  let c := 2+2*ρ
  let z := fun s : ℂ => s/2-1
  have hρ : ρ ≠ 1 := fun e => by rw [e,Complex.one_re] at h₁; exact lt_irrefl _ h₁
  have hz : z c=ρ := by dsimp only [z,c]; ring
  have hc : 3 < c.re := by dsimp only [c]; simp [Complex.add_re,Complex.mul_re]; linarith only [hhalf]
  have hzt : Tendsto z (𝓝[≠] c) (𝓝 ρ) := by
    rw [← hz]
    exact (show Continuous z by dsimp only [z]; fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzp : Tendsto z (𝓝[≠] c) (𝓝[≠] ρ) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hzt,?_⟩
    filter_upwards [self_mem_nhdsWithin (a := c) (s := {(c:ℂ)}ᶜ)] with x hx
    change z x ≠ ρ
    intro he
    apply hx
    change x=c
    dsimp only [z,c] at he ⊢
    linear_combination 2*he
  have hana := analyticAt_riemannZeta_primeShiftResidueClosability hρ
  obtain ⟨g,hg,hg₀,hfac⟩ := hana.analyticOrderAt_ne_top.mp (analyticOrderAt_riemannZeta_ne_top hρ)
  have hres := (logDeriv_residue_of_factorization (n := zetaMultiplicity ρ) hg hg₀ hfac).neg.comp hzp
  have hM := (differentiable_mellin_squarePrimeWeight ρ).continuousAt.tendsto.comp hzt
  have he := (analytic_squareConductorAnalyticRemainder c hc).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] c ≤ 𝓝 c)
  have hh := ((hM.const_mul (2:ℂ)).mul hres).add ((tendsto_sub_self_punctured_zero c).mul he)
  have hm : zetaMultiplicity ρ ≠ 0 := fun hm => (zetaMultiplicity_eq_zero_iff hρ).mp hm hζ
  refine ⟨mul_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hm))
    (mellin_squarePrimeWeight_off_line h₁ hhalf.ne'),?_⟩
  have heq : 2*mellin squarePrimeWeight ρ*(-(zetaMultiplicity ρ:ℂ))+0*squareConductorAnalyticRemainder c =
      -2*(zetaMultiplicity ρ:ℂ)*mellin squarePrimeWeight ρ := by ring
  rw [heq] at hh
  refine hh.congr fun s => ?_
  dsimp only [Function.comp_apply,z,c,squareConductorContinuation,logDeriv_apply]; ring

end GaloisForLFunctions.CountingHolography.Sections
