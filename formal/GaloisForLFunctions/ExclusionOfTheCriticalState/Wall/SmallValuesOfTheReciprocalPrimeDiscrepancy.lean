import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheReciprocalTermAboveTheTestAbscissa
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheLateTimeEndpointOfTheTestedIntegerRows
import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.LandauTailSignObstruction
import GaloisForLFunctions.RHTower.MertensProductLaplace
import GaloisForLFunctions.RHTower.MertensSquareRootOmega
import GaloisForLFunctions.RHTower.ZetaGaussianZeroSumContour
import GaloisForLFunctions.SurfaceOfSpecZ.ThePrimesSampleEveryTopLayer
import GaloisForLFunctions.LatticeSectionTheory.TheBoostTransformRestoresTheEulerProduct

/-!
# Small values of the reciprocal Mangoldt discrepancy

Removing the zeta pole gives a Laplace transform analytic at every real
argument above minus one. A permanent square-root lower bound would force
a fixed tail sign by the one-step jump estimate.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

private def reciprocalNumerator (s : ℂ) : ℂ :=
  -2*(Real.eulerMascheroniConstant:ℂ) + logDeriv zetaResidueUnit s + dslope zetaResidueUnit 1 s

private theorem reciprocalNumerator_one : reciprocalNumerator 1=0 := by
  rw [reciprocalNumerator,logDeriv_zetaResidueUnit_one,dslope_same,deriv_zetaResidueUnit_one]
  ring

private theorem analyticAt_reciprocalNumerator {s : ℂ} (hs : zetaResidueUnit s≠0) :
    AnalyticAt ℂ reciprocalNumerator s := by
  have h := analyticAt_zetaResidueUnit s
  exact (analyticAt_const.add (h.deriv.div h hs)).add
    (analyticAt_dslope_of_analyticAt_of_analyticAt (analyticAt_zetaResidueUnit 1) h)

private def reciprocalContinuation (z : ℂ) : ℂ := dslope reciprocalNumerator 1 (1+z)

private theorem analyticAt_reciprocalContinuation {x : ℝ} (hx : -1<x) :
    AnalyticAt ℂ reciprocalContinuation (x:ℂ) := by
  have hn : zetaResidueUnit (1+(x:ℂ))≠0 := by
    simpa only [Complex.ofReal_add,Complex.ofReal_one] using
      (zetaResidueUnit_ofReal_ne_zero (show 0<1+x by linarith))
  exact (analyticAt_dslope_of_analyticAt_of_analyticAt
    (analyticAt_reciprocalNumerator (by simp)) (analyticAt_reciprocalNumerator hn)).comp
      (analyticAt_const.add analyticAt_id)

private theorem reciprocalContinuation_of_pos {x : ℝ} (hx : 0 < x) :
    reciprocalContinuation x = (-2*(Real.eulerMascheroniConstant:ℂ) +
      logDeriv riemannZeta (1+x) + riemannZeta (1+x))/(x:ℂ) := by
  let s : ℂ := 1+x
  have hs : 1<s.re := by simp only [s,Complex.add_re,Complex.one_re,Complex.ofReal_re]; linarith
  have hs1 : s≠1 := fun h => by rw [h] at hs; simp at hs
  have hx' : (x:ℂ)≠0 := by exact_mod_cast hx.ne'
  change dslope reciprocalNumerator 1 s = _
  rw [dslope_of_ne _ hs1,slope_def_field,reciprocalNumerator_one,sub_zero,
    reciprocalNumerator,GaussZeroSum.logDeriv_zetaResidueUnit_eq hs1 (riemannZeta_ne_zero_of_one_lt_re hs),
    dslope_of_ne _ hs1,slope_def_field,(zetaResidueUnit_eventuallyEq hs1).eq_of_nhds,zetaResidueUnit_one]
  change (-2*(Real.eulerMascheroniConstant:ℂ)+(1/(s-1)+deriv riemannZeta s/riemannZeta s)+
    ((s-1)*riemannZeta s-1)/(s-1))/(s-1)=(-2*(Real.eulerMascheroniConstant:ℂ)+
    deriv riemannZeta s/riemannZeta s+riemannZeta s)/(x:ℂ)
  rw [show s-1=(x:ℂ) by dsimp only [s]; ring]
  field_simp [hx',riemannZeta_ne_zero_of_one_lt_re hs]; ring


private def countedReciprocal (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, c n

private theorem countedReciprocal_weight_integrable {c : ℕ → ℝ} (hn : ∀ n, 0 ≤ c n) (h0 : c 0=0)
    {σ : ℝ} (hσ : 0 < σ) (hs : Summable fun n : ℕ => c n*(n:ℝ)^(-σ)) {j : ℕ}
    (hj : 0 < c j*(j:ℝ)^(-σ)) :
    IntegrableOn (fun t => countedReciprocal c t*Real.exp (-σ*t)) (Ioi 0) := by
  have h := integral_sum_Icc_floor_exp_mul hn h0 hσ hs
  have hsum := hj.trans_le (hs.le_tsum j fun i _ => mul_nonneg (hn i) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  by_contra hi
  exact (div_pos hsum hσ).ne' (h.symm.trans (integral_undef hi))

private def reflectedReciprocal (u : ℝ) : ℝ :=
  (Iio 0).indicator (fun x : ℝ => reciprocalPrimeRemainder ⌊Real.exp (-x)⌋₊) u

private theorem measurable_reflectedReciprocal : Measurable reflectedReciprocal :=
  ((measurable_of_countable reciprocalPrimeRemainder).comp
    (Real.measurable_exp.comp measurable_neg).nat_floor).indicator measurableSet_Iio

private theorem reciprocal_at_exp {t : ℝ} (ht : 0 ≤ t) :
    (1:ℕ) ≤ ⌊Real.exp t⌋₊ ∧ Real.exp t/2 ≤ (⌊Real.exp t⌋₊:ℝ) := by
  have he := Real.one_le_exp ht
  have hk : (1:ℕ) ≤ ⌊Real.exp t⌋₊ := Nat.le_floor (by exact_mod_cast he)
  have h1 : (1:ℝ) ≤ (⌊Real.exp t⌋₊:ℝ) := by exact_mod_cast hk
  exact ⟨hk,by linarith only [h1,Nat.lt_floor_add_one (Real.exp t)]⟩

private theorem integrable_reflectedReciprocal :
    Integrable reflectedReciprocal := by
  obtain ⟨B,hB,hR⟩ := centered_reciprocal_prime_intervals (d := 1/8) (by norm_num) (by norm_num)
  have hb (k : ℕ) (hk : 1 ≤ k) : |reciprocalPrimeRemainder k| ≤ B*(k:ℝ)^(-(1/8:ℝ)) :=
    le_of_tendsto (tendsto_reciprocalPrimeBand k).abs
      ((eventually_ge_atTop k).mono fun L hL => hR k L hk hL)
  unfold reflectedReciprocal
  apply (integrable_indicator_iff measurableSet_Iio).mpr
  have hi := ((integrableOn_exp_mul_Iic (by norm_num : 0<(1/8:ℝ)) 0).mono_set Iio_subset_Iic_self).const_mul
    (B*(2:ℝ)^(1/8:ℝ))
  refine hi.mono' ((measurable_of_countable reciprocalPrimeRemainder).comp
    (Real.measurable_exp.comp measurable_neg).nat_floor).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Iio] with u hu
  obtain ⟨hk,hx⟩ := reciprocal_at_exp (neg_nonneg.mpr (le_of_lt hu))
  have h := Real.rpow_le_rpow_of_nonpos (div_pos (Real.exp_pos _) (by norm_num)) hx
    (by norm_num : -(1/8:ℝ) ≤ 0)
  rw [Real.norm_eq_abs]
  apply ((hb _ hk).trans (mul_le_mul_of_nonneg_left h hB)).trans_eq
  rw [Real.div_rpow (Real.exp_pos _).le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤2),
    div_inv_eq_mul,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,
    show -u * -(1/8:ℝ)=1/8*u by ring]
  ring

private theorem reflectedReciprocal_transform {σ : ℝ} (hσ : 0<σ) :
    negativeHalfLineLaplace (cx reflectedReciprocal) (σ:ℂ)=reciprocalContinuation σ := by
  let a := fun n : ℕ => (n:ℝ)⁻¹
  let b := fun n : ℕ => vonMangoldt n/(n:ℝ)
  let s := 1+σ
  have hs : 1<s := by dsimp only [s]; linarith
  let w := fun n : ℕ => (n:ℝ)^(-σ)
  have ha (n : ℕ) : a n*w n=(n:ℝ)^(-s) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hs0 : -s≠0 := by linarith only [hs]
      simp [a,w,Real.zero_rpow hs0]
    · rw [show -s= -1 + -σ by dsimp [s]; ring,
        Real.rpow_add (Nat.cast_pos.mpr hn),Real.rpow_neg_one]
  have hb (n : ℕ) : b n*w n=vonMangoldt n*(n:ℝ)^(-s) := by
    rw [← ha]; dsimp only [a,b]; ring
  have has : Summable fun n : ℕ => a n*w n := by
    simp only [ha]; exact Real.summable_nat_rpow.mpr (by linarith only [hs])
  have hbs : Summable fun n : ℕ => b n*w n := by
    rw [← summable_nat_add_iff 1]
    simpa only [hb,Nat.cast_add,Nat.cast_one] using SurfaceOfSpecZ.summable_vonMangoldt_rpow hs
  have hai := countedReciprocal_weight_integrable (c := a) (fun n => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by simp [a]) hσ has (j := 1) (by simp [a])
  have hbi := countedReciprocal_weight_integrable (c := b) (fun n => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
    (by simp [b]) hσ hbs (j := 2) (by dsimp only [b]; rw [vonMangoldt_apply_prime Nat.prime_two]; positivity)
  have hix := integrableOn_exp_mul_Ioi (by linarith only [hσ] : -σ < 0) 0
  have hia := integral_sum_Icc_floor_exp_mul (c := a) (fun n => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by simp [a]) hσ has
  have hib := integral_sum_Icc_floor_exp_mul (c := b) (fun n => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
    (by simp [b]) hσ hbs
  let g := Real.eulerMascheroniConstant
  have hR (t : ℝ) : reciprocalPrimeRemainder ⌊Real.exp t⌋₊ =
      -2*g+countedReciprocal a t-countedReciprocal b t := by
    have hsets : Finset.Icc 1 ⌊Real.exp t⌋₊=Finset.Ioc 0 ⌊Real.exp t⌋₊ := by ext n; simp; omega
    simp only [reciprocalPrimeRemainder,countedReciprocal,hsets,b,a,g,sub_div,one_div,Finset.sum_sub_distrib]
    ring
  have href : (∫ u, reflectedReciprocal u*Real.exp (σ*u)) =
      ∫ t in Ioi 0, reciprocalPrimeRemainder ⌊Real.exp t⌋₊*Real.exp (-σ*t) := by
    rw [← integral_neg_eq_self (fun u => reflectedReciprocal u*Real.exp (σ*u)) volume,
      ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : 0<t
    · simp only [reflectedReciprocal,indicator_of_mem (show -t∈Iio 0 from neg_lt_zero.mpr ht),
        indicator_of_mem (show t∈Ioi 0 from ht),neg_neg,neg_mul,mul_neg]
    · simp only [reflectedReciprocal,indicator_of_notMem (show -t∉Iio 0 from fun h => ht (neg_lt_zero.mp h)),
        indicator_of_notMem (show t∉Ioi 0 from ht),zero_mul]
  have htransform : (∫ u, reflectedReciprocal u*Real.exp (σ*u)) =
      (-2*g+(∑' n, a n*w n)-(∑' n, b n*w n))/σ := by
    rw [href]
    simp_rw [hR,sub_mul,add_mul]
    have hsum : IntegrableOn (fun t => -2*g*Real.exp (-σ*t)+countedReciprocal a t*Real.exp (-σ*t)) (Ioi 0) :=
      (hix.const_mul (-2*g)).add hai
    rw [integral_sub hsum hbi,
      integral_add (hix.const_mul (-2*g)) hai,integral_const_mul,integral_exp_mul_Ioi (by linarith only [hσ])]
    change -2*g*(-Real.exp (-σ*0)/(-σ))+
      (∫ t in Ioi 0, (∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, a n)*Real.exp (-σ*t))-
      (∫ t in Ioi 0, (∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, b n)*Real.exp (-σ*t)) = _
    rw [hia,hib,mul_zero,Real.exp_zero]
    dsimp only [w]; ring
  have hza : ((∑' n, a n*w n : ℝ):ℂ)=riemannZeta (s:ℂ) := by
    rw [has.tsum_eq_zero_add,show a 0*w 0=0 by simp [a],zero_add,
      LatticeSectionTheory.riemannZeta_ofReal_eq_tsum hs]
    congr 1
    apply tsum_congr fun n => ?_
    simp only [ha,Nat.cast_add,Nat.cast_one]
  have hzb : ((∑' n, b n*w n : ℝ):ℂ)= -logDeriv riemannZeta (s:ℂ) := by
    rw [hbs.tsum_eq_zero_add,show b 0*w 0=0 by simp [b],zero_add,← SurfaceOfSpecZ.ofReal_vmSum hs]
    congr 1
    apply tsum_congr fun n => ?_
    simp only [hb,Nat.cast_add,Nat.cast_one]
  rw [negativeHalfLineLaplace_ofReal,htransform,reciprocalContinuation_of_pos hσ]
  simp only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,
    Complex.ofReal_neg,Complex.ofReal_ofNat]
  rw [hza,hzb,show (s:ℂ)=1+σ by simp only [s,Complex.ofReal_add,Complex.ofReal_one]]
  dsimp only [g]; ring

private theorem reciprocalPrimeRemainder_jump (k : ℕ) :
    |reciprocalPrimeRemainder (k+1)-reciprocalPrimeRemainder k| ≤ 2/Real.sqrt (k+1:ℕ) := by
  let n := k+1
  have hn : 0<(n:ℝ) := by exact_mod_cast Nat.succ_pos k
  have hr := Real.sqrt_pos.mpr hn
  have h := Finset.sum_Ioc_succ_top (Nat.zero_le k) (fun i : ℕ => (vonMangoldt i-1)/(i:ℝ))
  have he : reciprocalPrimeRemainder (k+1)-reciprocalPrimeRemainder k =
      -((vonMangoldt n-1)/(n:ℝ)) := by rw [reciprocalPrimeRemainder,reciprocalPrimeRemainder,h]; dsimp [n]; ring
  rw [he,abs_neg,abs_div,abs_of_pos hn]
  have hlog := Real.log_le_sub_one_of_pos hr
  rw [Real.log_sqrt hn.le] at hlog
  have hcoeff : |vonMangoldt n-1| ≤ 2*Real.sqrt n := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg vonMangoldt_nonneg,abs_one]
    linarith only [vonMangoldt_le_log (n := n),hlog]
  change |vonMangoldt n-1| /(n:ℝ) ≤ 2/Real.sqrt n
  apply (div_le_div_of_nonneg_right hcoeff hn.le).trans_eq
  rw [div_eq_div_iff hn.ne' hr.ne']
  linear_combination 2*Real.sq_sqrt hn.le

private theorem sign_preserved_by_small_jump {s x y : ℝ} (hs : |s| = 1)
    (hx : 0 ≤ s*x) (hj : |y-x| < |y|) : 0 ≤ s*y := by
  by_contra! hneg
  have hy : |s*y| = |y| := by rw [abs_mul,hs,one_mul]
  have hdiff : |s*y-s*x| = |y-x| := by rw [← mul_sub,abs_mul,hs,one_mul]
  rw [abs_of_neg hneg] at hy
  rw [abs_of_nonpos (sub_nonpos.mpr (hneg.le.trans hx))] at hdiff
  linarith only [hx,hj,hy,hdiff]

/-- Arbitrarily large reciprocal Mangoldt tails are bounded by twice the
inverse square root of their integer endpoint. -/
theorem frequently_small_reciprocalPrimeRemainder :
    ∃ᶠ k : ℕ in atTop, |reciprocalPrimeRemainder k| ≤ 2/Real.sqrt k := by
  by_contra hn
  rw [Filter.not_frequently,Filter.eventually_atTop] at hn
  obtain ⟨n,hn⟩ := hn
  let N := max n 1
  have hN : 1 ≤ N := le_max_right _ _
  have hN0 : 0<(N:ℝ) := by exact_mod_cast hN
  have hlarge (k : ℕ) (hk : N≤k) : 2/Real.sqrt k < |reciprocalPrimeRemainder k| :=
    lt_of_not_ge (hn k ((le_max_left _ _).trans hk))
  let s : ℝ := if 0≤reciprocalPrimeRemainder N then 1 else -1
  have hs : s=1 ∨ s= -1 := by dsimp only [s]; split <;> simp
  have hsabs : |s| = 1 := hs.elim (fun h => by rw [h,abs_one]) (fun h => by rw [h,abs_neg,abs_one])
  have hsign (k : ℕ) (hk : N≤k) : 0 ≤ s*reciprocalPrimeRemainder k := by
    induction k, hk using Nat.le_induction with
    | base =>
      by_cases h : 0≤reciprocalPrimeRemainder N
      · simpa only [s,if_pos h,one_mul] using h
      · simpa only [s,if_neg h,neg_one_mul] using neg_nonneg.mpr (le_of_lt (lt_of_not_ge h))
    | succ k hk ih =>
      exact sign_preserved_by_small_jump hsabs ih
        ((reciprocalPrimeRemainder_jump k).trans_lt (hlarge (k+1) (Nat.le_succ_of_le hk)))
  let T := Real.log N
  have hT : 0 ≤ T := Real.log_natCast_nonneg _
  have hindex {u : ℝ} (hu : u ∈ Iio (-T)) : N ≤ ⌊Real.exp (-u)⌋₊ := by
    apply Nat.le_floor
    apply (Real.log_le_iff_le_exp hN0).mp
    change u< -Real.log N at hu
    linarith only [hu]
  have hue {u : ℝ} (hu : u ∈ Iio (-T)) : u < 0 := lt_of_lt_of_le hu (neg_nonpos.mpr hT)
  have hpos : ∀ᵐ u ∂volume.restrict (Iio (-T)), 0 ≤ s*reflectedReciprocal u := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Iio] with u hu
    rw [reflectedReciprocal,indicator_of_mem (show u∈Iio 0 from hue hu)]
    exact hsign _ (hindex hu)
  have hforce := integrable_exp_of_signed_tail_of_real_continuation measurable_reflectedReciprocal
    integrable_reflectedReciprocal (fun u hu => indicator_of_notMem (show u∉Iio 0 from not_lt.mpr hu) _)
    (κ := -1) (fun _ hx => analyticAt_reciprocalContinuation hx) (fun _ hx => reflectedReciprocal_transform hx)
    hs hT hpos (by norm_num : (-1:ℝ)< -1/2)
  have hcst : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Iio (-T)) := by
    refine hforce.integrableOn.mono' aestronglyMeasurable_const ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Iio] with u hu
    let k := ⌊Real.exp (-u)⌋₊
    have hk := hindex hu
    have hk0 : 0<(k:ℝ) := by exact_mod_cast hN.trans hk
    have hr := Real.sqrt_pos.mpr hk0
    have hroot : Real.sqrt k ≤ Real.exp ((-1/2)*u) := by
      rw [show (-1/2)*u= -u/2 by ring,Real.exp_half]
      exact Real.sqrt_le_sqrt (Nat.floor_le (Real.exp_pos _).le)
    change ‖(1:ℝ)‖ ≤ |reflectedReciprocal u| *Real.exp ((-1/2)*u)
    rw [norm_one,reflectedReciprocal,indicator_of_mem (show u∈Iio 0 from hue hu)]
    change 1≤ |reciprocalPrimeRemainder k| *Real.exp ((-1/2)*u)
    have hmul := mul_le_mul (hlarge k hk).le hroot (Real.sqrt_nonneg _) (abs_nonneg _)
    rw [div_mul_cancel₀ _ hr.ne'] at hmul
    linarith only [hmul]
  simp [integrableOn_const_iff,Real.volume_Iio] at hcst

/-- A single arithmetic sequence cancels the reciprocal term at the
seven-eighths logarithmic test centers for every state. -/
theorem exists_vanishing_scaled_reciprocalPrimeRemainder :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      Tendsto (fun j => (k j:ℝ)^(7/16:ℝ)*reciprocalPrimeRemainder (k j)) atTop (𝓝 0) := by
  obtain ⟨k,hk,hs⟩ := extraction_of_frequently_atTop frequently_small_reciprocalPrimeRemainder
  refine ⟨k,hk,?_⟩
  have hdec := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/16)).comp
    (tendsto_natCast_atTop_atTop.comp hk.tendsto_atTop)).const_mul (2:ℝ)
  simp only [mul_zero] at hdec
  apply squeeze_zero_norm' _ hdec
  filter_upwards [hk.tendsto_atTop.eventually_ge_atTop 1] with j hj
  have hpos : 0 < (k j:ℝ) := by exact_mod_cast hj
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
  apply (mul_le_mul_of_nonneg_left (hs j) (Real.rpow_nonneg hpos.le _)).trans_eq
  change (k j:ℝ)^(7/16:ℝ)*(2/Real.sqrt (k j)) = 2*(k j:ℝ)^(-(1/16:ℝ))
  rw [Real.sqrt_eq_rpow,div_eq_mul_inv (2:ℝ),← Real.rpow_neg hpos.le,
    show -(1/16:ℝ) = (7/16:ℝ) + -(1/2:ℝ) by norm_num,Real.rpow_add hpos]
  ring

#print axioms frequently_small_reciprocalPrimeRemainder
#print axioms exists_vanishing_scaled_reciprocalPrimeRemainder
end GaloisForLFunctions.ExclusionOfTheCriticalState
