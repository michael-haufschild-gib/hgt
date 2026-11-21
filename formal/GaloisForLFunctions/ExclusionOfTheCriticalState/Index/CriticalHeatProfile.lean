import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheConditionalOrdinateLawOnMultiplicativeBands
import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheHeatedZeroPairingOfTwoProfilesIsWeilsForm

/-!
# The heat profile of the critical-state ordinate tail

De Nitti–Ignat–Quirós (arXiv:2611.22679, Lemma 7.1) identify the
heat profile of data with inverse-linear tails. On the whole similarity
axis a bounded error compares the rescaled convolution to its local
mass times the kernel. The critical-state tail therefore has the
Gaussian profile with precisely the wall-cusp coefficient.
-/
noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri _root_.RHTower
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- The error from replacing a dilated kernel by its central value is
uniform in the observation point when |x|f(x) is bounded. -/
theorem inverse_tail_convolution_error {f K : ℝ → ℝ} {M B D L : ℝ}
    (hm : Measurable f) (hf : ∀ x, 0≤f x) (hM : ∀ x, f x≤M) (hB : ∀ x, |x| * f x≤B)
    (hK : Integrable K) (hK₀ : ∀ x, 0≤K x) (hD : 0≤D)
    (hLip : ∀ a b, |K a-K b| ≤ D*|a-b|) (hL : 0<L) (y : ℝ) :
    |(∫ x : ℝ, f x*K (y-x/L)) - (∫ x in Icc (-L) L, f x)*K y| ≤
      B*(2*D+∫ z : ℝ, K z) := by
  let S := Icc (-L) L
  let k := fun x : ℝ => K (y-x/L)
  have hk : Integrable k := (hK.comp_sub_left y).comp_div hL.ne'
  have hk₀ (x : ℝ) : 0≤k x := hK₀ _
  have hmass : (∫ x, k x)=L*∫ z, K z := by
    simp only [k]
    rw [Measure.integral_comp_div (fun u => K (y-u)) L,integral_sub_left_eq_self K volume,abs_of_pos hL,
      smul_eq_mul]
  have hfK : Integrable (fun x => f x*k x) := (hk.const_mul M).mono'
    (hm.aestronglyMeasurable.mul hk.aestronglyMeasurable) (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (hf _) (hk₀ _))]
      exact mul_le_mul_of_nonneg_right (hM _) (hk₀ _))
  have hfin : IntegrableOn f S := (continuousOn_const (c:=M)).integrableOn_Icc.mono'
    hm.aestronglyMeasurable.restrict (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (hf _)]; exact hM _)
  have hB₀ : 0≤B := by simpa only [abs_zero,zero_mul] using hB 0
  have hs : MeasurableSet S := measurableSet_Icc
  have hdiff : (∫ x in S, f x*(k x-K y))=(∫ x in S, f x*k x)-(∫ x in S, f x)*K y := by
    simp_rw [mul_sub]
    rw [integral_sub hfK.integrableOn (hfin.mul_const _),integral_mul_const]
  have hin : |∫ x in S, f x*(k x-K y)| ≤ 2*D*B := by
    have hb (x : ℝ) (_hx : x∈S) : ‖f x*(k x-K y)‖ ≤ D*B/L := by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hf x)]
      have hh := hLip (y-x/L) y
      rw [show y-x/L-y= -(x/L) by ring,abs_neg,abs_div,abs_of_pos hL] at hh
      calc f x*|k x-K y| ≤ f x*(D*(|x|/L)) := mul_le_mul_of_nonneg_left hh (hf x)
           _ = D*(|x| * f x)/L := by ring
           _ ≤ D*B/L := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hB x) hD) hL.le
    have ha := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=S) measure_Icc_lt_top hb
    rw [Real.norm_eq_abs,show volume.real S=L-(-L) from Real.volume_real_Icc_of_le (by linarith)] at ha
    exact ha.trans_eq (by field_simp; ring)
  have hout : (∫ x in Sᶜ, f x*k x)≤B*∫ z, K z := by
    have hp (x : ℝ) (hx : x∈Sᶜ) : L≤|x| := by
      by_contra! h
      exact hx ⟨(abs_lt.mp h).1.le,(abs_lt.mp h).2.le⟩
    have hbound := setIntegral_mono_on hfK.integrableOn ((hk.const_mul (B/L)).integrableOn)
      hs.compl (fun x hx => mul_le_mul_of_nonneg_right ((le_div_iff₀ hL).mpr (by
        calc f x*L ≤ |x| * f x := by simpa only [mul_comm (f x)] using mul_le_mul_of_nonneg_right (hp x hx) (hf x)
             _ ≤ B := hB x)) (hk₀ x))
    rw [integral_const_mul] at hbound
    refine hbound.trans ((mul_le_mul_of_nonneg_left (setIntegral_le_integral hk
      (Eventually.of_forall hk₀)) (div_nonneg hB₀ hL.le)).trans_eq ?_)
    rw [hmass]
    field_simp
  have hout₀ : 0≤∫ x in Sᶜ, f x*k x := integral_nonneg fun x => mul_nonneg (hf x) (hk₀ x)
  change |(∫ x, f x*k x)-(∫ x in S, f x)*K y|≤_
  rw [←integral_add_compl hs hfK]
  have ha := abs_add_le (∫ x in S, f x*(k x-K y)) (∫ x in Sᶜ, f x*k x)
  rw [hdiff,abs_of_nonneg hout₀] at ha
  rw [hdiff] at hin
  rw [show ∀ a b c : ℝ, a+b-c=(a-c)+b by intros; ring]
  exact ha.trans (by linarith only [hin,hout])

private theorem tail_data {F : ℝ → ℝ} (hs : Summable (fun q : onLineCopies => zeroValueMass F q)) :
    Antitone (ordinateTailMass F) ∧
    (∀ u, 0≤ordinateTailMass F u) ∧ (∀ u, ordinateTailMass F u≤∑' q : onLineCopies,zeroValueMass F q) := by
  have hn := zeroValueMass_nonneg F
  have hsum (u : ℝ) : Summable (fun q : onLineCopies =>
      if u < |(centredZero q).im| then zeroValueMass F q else 0) :=
    hs.of_nonneg_of_le (fun q => by split <;> first | exact le_rfl | exact hn q) (fun q => by split <;> first | exact le_rfl | exact hn q)
  refine ⟨fun a b hab => (hsum b).tsum_le_tsum (fun q => ?_) (hsum a),
    fun u => tsum_nonneg fun q => by split <;> first | exact le_rfl | exact hn q,
    fun u => (hsum u).tsum_le_tsum (fun q => by split <;> first | exact le_rfl | exact hn q) hs⟩
  split_ifs with hb ha
  · exact le_rfl
  · exact (ha (hab.trans_lt hb)).elim
  · exact hn q
  · exact le_rfl

/-- Symmetric truncated integral of the ordinate tail, a layer-cake
identity which also retains the mass above the cutoff. -/
theorem integrated_ordinate_tail {F : ℝ → ℝ} (hs : Summable (fun q : onLineCopies => zeroValueMass F q))
    {L : ℝ} (hL : 0≤L) :
    (∫ x in Icc (-L) L, ordinateTailMass F |x|)=
      2*((∑' q : onLineCopies, if |(centredZero q).im|≤L then
        |(centredZero q).im| * zeroValueMass F q else 0)+L*ordinateTailMass F L) := by
  let R := fun q : onLineCopies => |(centredZero q).im|
  let w := zeroValueMass F
  let S := Ioo (-L) L
  let g := fun q : onLineCopies => (Ioo (-(R q)) (R q)).indicator (fun _ => w q)
  have hw := zeroValueMass_nonneg F
  have hR (q) : 0≤R q := abs_nonneg _
  have hgi (q) : IntegrableOn (g q) S :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (C:=w q) measure_Ioo_lt_top.ne) |>.integrableOn
  have hp (q) (u : ℝ) : g q u = if |u|<R q then w q else 0 := by
    simp only [g,indicator,mem_Ioo,abs_lt]
  have hnorm (q) : (∫ x in S, ‖g q x‖)≤(2*L)*w q := by
    have HH := setIntegral_mono_on (hgi q).norm
      (integrableOn_const (hs:=measure_Ioo_lt_top.ne) (C:=w q)) measurableSet_Ioo (fun x _ => by
        rw [hp q x]; split_ifs
        · exact (Real.norm_of_nonneg (hw _)).le
        · rw [norm_zero]; exact hw _)
    rw [setIntegral_const,show volume.real S=L-(-L) from Real.volume_real_Ioo_of_le (by linarith),smul_eq_mul] at HH
    exact HH.trans_eq (by ring)
  have ht (q) : (∫ x in S,g q x) = 2*(min L (R q))*w q := by
    rw [show g q=(Ioo (-(R q)) (R q)).indicator (fun _ => w q) from rfl,setIntegral_indicator measurableSet_Ioo]
    simp only [S,Ioo_inter_Ioo,max_neg_neg,setIntegral_const,Real.volume_real_Ioo_of_le
      (show -(min L (R q))≤ min L (R q) by have := le_min hL (hR q); linarith),smul_eq_mul]
    ring
  have hg (u : ℝ) : ordinateTailMass F |u|=∑' q, g q u :=
    tsum_congr fun q => (hp q u).symm
  rw [integral_Icc_eq_integral_Ioo]
  simp_rw [hg]
  change (∫ x in S, ∑' q, g q x)=_
  rw [← integral_tsum_of_summable_integral_norm hgi ((hs.mul_left (2*L)).of_nonneg_of_le
    (fun q => integral_nonneg fun _ => norm_nonneg _) hnorm)]
  let a := fun q : onLineCopies => if R q≤L then R q*w q else 0
  let b := fun q : onLineCopies => if L<R q then w q else 0
  have ha : Summable a := (hs.mul_left L).of_nonneg_of_le
    (fun q => by
      dsimp only [a]; split_ifs
      · exact mul_nonneg (hR q) (hw q)
      · exact le_rfl)
    (fun q => by
      dsimp only [a]; split_ifs with h
      · exact mul_le_mul_of_nonneg_right h (hw q)
      · exact mul_nonneg hL (hw q))
  have hb : Summable b := hs.of_nonneg_of_le
    (fun q => by dsimp only [b]; split_ifs; exacts [hw q, le_rfl])
    (fun q => by dsimp only [b]; split_ifs; exacts [le_rfl, hw q])
  change _=2*((∑' q,a q)+L*∑' q,b q)
  rw [←tsum_mul_left,←ha.tsum_add (hb.mul_left L),←tsum_mul_left]
  apply tsum_congr
  intro q
  rw [ht]
  rcases le_or_gt (R q) L with h | h
  · simp only [a,b,if_pos h,if_neg (not_lt.mpr h),min_eq_right h,mul_zero,add_zero]; ring
  · simp only [a,b,if_neg h.not_ge,if_pos h,min_eq_left h.le,zero_add]; ring

private theorem gaussian_peak (x : ℝ) : stateHeatKernel 1 x≤ stateHeatKernel 1 0 := by
  let a := (2*Real.pi)⁻¹*Real.sqrt (Real.pi/1)
  change a*Real.exp (-(x^2/(4*1)))≤a*Real.exp (-(0^2/(4*1)))
  simp only [zero_pow (by decide : 2≠0),zero_div,neg_zero,Real.exp_zero,mul_one]
  exact mul_le_of_le_one_right (by dsimp [a]; positivity) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))

private theorem gaussian_lipschitz :
    ∀ x y : ℝ, |stateHeatKernel 1 x-stateHeatKernel 1 y|≤(stateHeatKernel 1 0/2)*|x-y| := by
  let K := stateHeatKernel 1
  have hK := stateHeatKernel_pos (by norm_num : 0<(1:ℝ))
  let D : NNReal := ⟨K 0/2,by dsimp [K]; positivity [hK 0]⟩
  have hLip : LipschitzWith D K := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_stateHeatKernel 1 x).differentiableAt)
    intro x
    change ‖deriv K x‖ ≤ K 0/2
    rw [(hasDerivAt_stateHeatKernel 1 x).deriv,Real.norm_eq_abs,abs_mul,abs_neg,abs_div,abs_of_pos (hK x)]
    norm_num
    have haux : |x|≤Real.exp (x^2/4) := by
      refine le_trans ?_ (Real.add_one_le_exp _)
      nlinarith only [sq_nonneg (|x|-2),sq_abs x]
    have hsmall' : |x| * Real.exp (-(x^2/4))≤1 := by
      rw [Real.exp_neg,←div_eq_mul_inv]
      exact (div_le_one (Real.exp_pos _)).mpr haux
    have he (s : ℝ) : K s=K 0*Real.exp (-(s^2/4)) := by simp [K,stateHeatKernel]
    rw [show stateHeatKernel 1 x = K 0*Real.exp (-(x^2/4)) from he x]
    have hh := mul_le_mul_of_nonneg_left hsmall' (hK 0).le
    nlinarith only [hh]
  intro x y
  have h := hLip.dist_le_mul x y
  rw [Real.dist_eq,Real.dist_eq] at h
  exact h

/-- Heat evolution of the even ordinate tail at similarity coordinate y. -/
def ordinateHeatReadout (F : ℝ → ℝ) (t y : ℝ) := ∫ x : ℝ,
  ordinateTailMass F |x| * stateHeatKernel t (Real.sqrt t*y-x)

private theorem scaled_gaussian {L : ℝ} (hL : 0<L) (x y : ℝ) :
    L*stateHeatKernel (L^2) (L*y-x)=stateHeatKernel 1 (y-x/L) := by
  have hp : (L*y-x)^2/(4*L^2)=(y-x/L)^2/(4*1) := by field_simp
  simp only [stateHeatKernel,hp,Real.sqrt_div Real.pi_pos.le,Real.sqrt_sq hL.le,Real.sqrt_one,div_one]
  field_simp

/-- Uniform similarity profile on the whole real axis. The coefficient at
the center is strictly positive for every first threshold ground state
on the finite-layer branch. -/
theorem critical_ordinate_heat_profile {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ t : ℝ in atTop, ∀ y : ℝ,
      |Real.sqrt t/Real.log t*ordinateHeatReadout F t y-ordinateCuspConstant W F*stateHeatKernel 1 y|<ε := by
  let C := ordinateCuspConstant W F
  let f := fun x : ℝ => ordinateTailMass F |x|
  let K := stateHeatKernel 1
  let M := ∑' q : onLineCopies,zeroValueMass F q
  let J := fun L => ∫ x in Icc (-L) L,f x
  have hs := (domain_zeroParseval_of_finiteOffLine (criticalHalfLineEnergyDomain_of_groundState hF) hf).1
  obtain ⟨hanti,hpos,hbound⟩ := tail_data hs
  have htlim : Tendsto (fun L : ℝ => L*ordinateTailMass F L) atTop (𝓝 C) :=
    criticalState_criticalLine_tail_asymptotic hW ht hF hf
  have hi : Tendsto (fun L : ℝ => (Real.log L)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hfirst := criticalState_criticalLine_firstMoment_asymptotic hW ht hF hf
  have hJ : Tendsto (fun L => J L/(2*Real.log L)) atTop (𝓝 C) := by
    have hj := hfirst.add (hi.mul htlim)
    simp only [zero_mul,add_zero] at hj
    refine hj.congr' ?_
    filter_upwards [eventually_gt_atTop (1:ℝ)] with L hL
    dsimp only [J,f]
    rw [integrated_ordinate_tail hs (zero_le_one.trans hL.le)]
    ring
  obtain ⟨U,hU⟩ := eventually_atTop.mp (htlim.eventually_lt_const (show C<C+1 by linarith))
  let B := max (C+1) (max U 0*M)
  have hM : 0≤M := tsum_nonneg (fun q => zeroValueMass_nonneg F q)
  have hB (x : ℝ) : |x| * f x≤B := by
    rcases le_or_gt U |x| with hu | hu
    · exact (hU _ hu).le.trans (le_max_left _ _)
    · exact (mul_le_mul (hu.le.trans (le_max_left _ _)) (hbound _) (hpos _) (le_max_right _ _)).trans (le_max_right _ _)
  have hK₀ (x : ℝ) : 0<K x := stateHeatKernel_pos (by norm_num) _
  have hhD : 0≤K 0/2 := by positivity [hK₀ 0]
  have hKi : Integrable K := by
    simpa only [zero_mul,Real.exp_zero,mul_one] using integrable_stateHeatKernel_mul_exp_abs (by norm_num : 0<(1:ℝ)) 0
  let A := B*(2*(K 0/2)+1)
  have he (L : ℝ) (hL : 0<L) (y : ℝ) :
      |(∫ x : ℝ, f x*K (y-x/L))-J L*K y|≤A := by
    have h := inverse_tail_convolution_error
      (hanti.measurable.comp continuous_abs.measurable) (fun x => hpos |x|) (fun x => hbound |x|)
      hB hKi (fun x => (hK₀ x).le) hhD gaussian_lipschitz hL y
    simp only [K,integral_stateHeatKernel_one] at h
    exact h
  have hnorm : Tendsto (fun L : ℝ => A/(2*Real.log L)+|J L/(2*Real.log L)-C| * K 0) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun L : ℝ => A/(2*Real.log L)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.const_mul_atTop (by norm_num))
    simpa using h₁.add ((hJ.sub_const C).abs.mul_const (K 0))
  intro ε hε
  have hscale : ∀ᶠ L : ℝ in atTop, ∀ y : ℝ,
      |(∫ x : ℝ, f x*K (y-x/L))/(2*Real.log L)-C*K y|<ε := by
    filter_upwards [hnorm.eventually_lt_const hε,eventually_gt_atTop (1:ℝ)] with L hb hL y
    let z := ∫ x : ℝ, f x*K (y-x/L)
    let ℓ := 2*Real.log L
    have hp : 0<ℓ := mul_pos (by norm_num) (Real.log_pos hL)
    have hd : |(z-J L*K y)/ℓ|≤A/ℓ := by
      rw [abs_div,abs_of_pos hp]
      exact div_le_div_of_nonneg_right (he L (zero_lt_one.trans hL) y) hp.le
    have hk : |(J L/ℓ-C)*K y|≤|J L/ℓ-C| * K 0 := by
      rw [abs_mul,abs_of_pos (hK₀ _)]
      exact mul_le_mul_of_nonneg_left (gaussian_peak y) (abs_nonneg _)
    change |z/ℓ-C*K y|<ε
    rw [show z/ℓ-C*K y=(z-J L*K y)/ℓ+(J L/ℓ-C)*K y by ring]
    exact (abs_add_le _ _).trans_lt ((add_le_add hd hk).trans_lt hb)
  filter_upwards [Real.tendsto_sqrt_atTop.eventually hscale,eventually_gt_atTop (0:ℝ)] with t hL ht₀ y
  let L := Real.sqrt t
  have hp : 0<L := Real.sqrt_pos.mpr ht₀
  have hsquare : L^2=t := Real.sq_sqrt ht₀.le
  have hlog : 2*Real.log L=Real.log t := by rw [←hsquare,Real.log_pow]; norm_num
  have hK (x : ℝ) : L*stateHeatKernel t (L*y-x)=K (y-x/L) := by
    rw [←hsquare]; exact scaled_gaussian hp x y
  have hsc : L*ordinateHeatReadout F t y=(∫ x : ℝ, f x*K (y-x/L)) := by
    rw [ordinateHeatReadout,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    change L*(f x*stateHeatKernel t (L*y-x))=f x*K (y-x/L)
    rw [←hK]
    ring
  change |L/Real.log t*ordinateHeatReadout F t y-C*K y|<ε
  rw [show L/Real.log t*ordinateHeatReadout F t y=(L*ordinateHeatReadout F t y)/Real.log t by ring,hsc,←hlog]
  exact hL y

private theorem gaussian_vanishes_iff {y : ℕ → ℝ} :
    Tendsto (fun n => stateHeatKernel 1 (y n)) atTop (𝓝 0) ↔ Tendsto (fun n => |y n|) atTop atTop := by
  let a := (2*Real.pi)⁻¹*Real.sqrt (Real.pi/1)
  have ha : 0<a := by dsimp [a]; positivity
  constructor
  · intro h
    refine tendsto_atTop.mpr fun b => ?_
    let R := max b 0
    have hp := stateHeatKernel_pos (by norm_num : 0<(1:ℝ)) R
    filter_upwards [h.eventually_lt_const hp] with n hn
    by_contra! hsmall
    have hsq : (y n)^2≤R^2 := by
      rw [←sq_abs (y n)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hsmall.le.trans (le_max_left _ _)) _
    have hle : stateHeatKernel 1 R ≤ stateHeatKernel 1 (y n) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ha.le
      linarith only [hsq]
    exact hn.not_ge hle
  · intro h
    have hs : Tendsto (fun n => |y n|^2/4) atTop atTop :=
      ((tendsto_pow_atTop (by decide : 2≠0)).comp h).atTop_div_const (by norm_num)
    have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hs).const_mul a
    simpa only [stateHeatKernel,a,sq_abs,mul_one,mul_zero,Function.comp_apply] using he

/-- For an actual finite-layer ground state the normalized heat reading
vanishes along moving centers exactly when the similarity coordinates
escape to infinity. Arbitrarily slow escape already suffices. -/
theorem critical_heat_vanishing_iff_escape {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {t y : ℕ → ℝ} (htime : Tendsto t atTop atTop) :
    Tendsto (fun n => Real.sqrt (t n)/Real.log (t n)*ordinateHeatReadout F (t n) (y n)) atTop (𝓝 0)
      ↔ Tendsto (fun n => |y n|) atTop atTop := by
  let C := ordinateCuspConstant W F
  let g := fun n => stateHeatKernel 1 (y n)
  let m := fun n => Real.sqrt (t n)/Real.log (t n)*ordinateHeatReadout F (t n) (y n)
  have hC : 0<C := by
    have hn := isConfinedNullVector_of_groundState hW ht hF
    have hm : (∫ u : ℝ, F u^2*Real.exp (-(8*u)))=criticalHalfLineExponentialPair F F := by
      unfold criticalHalfLineExponentialPair
      exact integral_congr_ae (Eventually.of_forall fun u => by ring)
    dsimp only [C,ordinateCuspConstant]
    rw [hm]
    exact div_pos (mul_pos (mul_pos (by norm_num) (criticalAliasCoefficient_positive hW))
      (exponentialPair_self_pos (criticalHalfLineEnergyDomain_of_groundState hF) hn.2.1)) Real.pi_pos
  have he : Tendsto (fun n => m n-C*g n) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [htime.eventually (critical_ordinate_heat_profile hW ht hF hf ε hε)] with n hn
    simpa only [Real.dist_eq,sub_zero] using hn (y n)
  constructor
  · intro hz
    change Tendsto m atTop (𝓝 0) at hz
    apply gaussian_vanishes_iff.mp
    have hg := (hz.sub he).div_const C
    simp only [sub_zero,zero_div] at hg
    exact hg.congr fun n => by change (m n-(m n-C*g n))/C=g n; field_simp; ring
  · intro hy
    have hg := (gaussian_vanishes_iff.mpr hy).const_mul C
    have hz := he.add hg
    rw [mul_zero,zero_add] at hz
    refine hz.congr (fun n => ?_)
    show m n-C*g n+C*stateHeatKernel 1 (y n) = m n
    simp only [g]; ring

/-- A vanishing heat reading along a sequence whose similarity centers
do not escape rules out every finite, nonempty off-line divisor. -/
theorem finite_layer_exclusion_iff_heat_reading :
    (BacklundConverse.FiniteOffLine → RiemannHypothesis) ↔
      (BacklundConverse.FiniteOffLine → ∀ (W : ℝ) (F : ℝ → ℝ), 0<W →
        (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal) →
        IsCriticalHalfLineGroundState W F → ∃ t y : ℕ → ℝ,
        Tendsto t atTop atTop ∧ ¬Tendsto (fun n => |y n|) atTop atTop ∧
        Tendsto (fun n => Real.sqrt (t n)/Real.log (t n)*ordinateHeatReadout F (t n) (y n)) atTop (𝓝 0)) := by
  have hno : (BacklundConverse.FiniteOffLine → RiemannHypothesis) ↔
    (BacklundConverse.FiniteOffLine → ¬∃ (W : ℝ) (F : ℝ → ℝ), 0<W ∧
      (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal) ∧ IsCriticalHalfLineGroundState W F) :=
    finiteLayer_ecs_b13_tfae.out 0 1
  rw [hno]
  constructor
  · intro h hf W F hW ht hF
    exact (h hf ⟨W,F,hW,ht,hF⟩).elim
  · rintro h hf ⟨W,F,hW,ht,hF⟩
    obtain ⟨t,y,htime,hstay,hvan⟩ := h hf W F hW ht hF
    exact hstay ((critical_heat_vanishing_iff_escape hW ht hF hf htime).mp hvan)


end GaloisForLFunctions.ExclusionOfTheCriticalState
