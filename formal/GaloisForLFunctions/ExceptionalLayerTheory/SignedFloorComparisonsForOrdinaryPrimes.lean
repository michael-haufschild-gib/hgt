import GaloisForLFunctions.ExceptionalLayerTheory.TheOrdinaryPrimesSeparateSignedQuotientProfiles
import GaloisForLFunctions.ExceptionalLayerTheory.RationalGridJumpsOfRealFloorSums
import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# Signed ordinary-prime comparisons of real floor sums

Summation over ordinary primes multiplies the Mellin transform by the
prime zeta function. Its logarithmic singularity at one detects every
nonzero floor-class difference, including balanced signed comparisons.
-/

noncomputable section
open MeasureTheory Finset Set Filter Topology Complex Asymptotics
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The sum of a profile over ordinary-prime quotients. For a profile
vanishing near zero only finitely many terms contribute at any positive cutoff. -/
def ordinaryPrimeRead (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' p : Nat.Primes, f (x/(p.1:ℝ))

/-- A positive lower endpoint for the support gives an explicit finite prime cutoff. -/
theorem ordinaryPrimeRead_eq_finite {f : ℝ → ℂ} {δ x : ℝ} (hδ : 0<δ) (hx : 0<x)
    (hz : ∀ t, 0<t → t<δ → f t=0) {N : ℕ} (hN : x/δ≤N) :
    ordinaryPrimeRead f x=∑ p ∈ Nat.primesLE N, f (x/(p:ℝ)) := by
  classical
  let S := (Nat.primesLE N).attach.map
    ⟨fun k => (⟨k.1,Nat.prime_of_mem_primesLE k.2⟩ : Nat.Primes),
      fun i j e => Subtype.ext (congrArg Subtype.val e)⟩
  have hmem (p : Nat.Primes) : p ∈ S ↔ p.1≤N := by
    constructor
    · intro hp
      obtain ⟨k,_,e⟩ := mem_map.mp hp
      exact (congrArg Subtype.val e) ▸ (Nat.mem_primesLE.mp k.2).1
    · intro hp
      let k : {n // n∈Nat.primesLE N} := ⟨p.1,Nat.mem_primesLE.mpr ⟨hp,p.2⟩⟩
      exact mem_map.mpr ⟨k,Finset.mem_attach _ _,Subtype.ext rfl⟩
  rw [ordinaryPrimeRead,tsum_eq_sum (s := S) (fun p hp => by
    have hlt : (N:ℝ)<p.1 := by exact_mod_cast lt_of_not_ge (fun hn => hp ((hmem p).mpr hn))
    have hpp : (0:ℝ)<p.1 := by exact_mod_cast p.2.pos
    exact hz _ (div_pos hx hpp) ((div_lt_iff₀ hpp).mpr
      (by linarith only [(div_lt_iff₀ hδ).mp (hN.trans_lt hlt)])))]
  simp only [S,sum_map,Function.Embedding.coeFn_mk]
  exact Finset.sum_attach _ _

private theorem local_of_bounded {f : ℝ → ℂ} (hm : Measurable f)
    (hb : ∀ T : ℝ, 0<T → ∃ B : ℝ, ∀ x : ℝ, 0<x → x<T → ‖f x‖≤B) :
    LocallyIntegrableOn f (Ioi 0) := by
  intro x hx
  have hx' : 0<x := hx
  obtain ⟨B,hB⟩ := hb (x+1) (by linarith only [hx'])
  refine ⟨Ioo 0 (x+1),mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hx' (lt_add_one x)),?_⟩
  exact Measure.integrableOn_of_bounded (measure_Ioo_lt_top.ne) hm.aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => hB t ht.1 ht.2)

private theorem read_local {f : ℝ → ℂ} (hm : Measurable f) {δ A : ℝ}
    (hδ : 0<δ) (hA : 0≤A) (hz : ∀ t, 0<t → t<δ → f t=0)
    (hb : ∀ t, 0<t → ‖f t‖≤A*t) : LocallyIntegrableOn (ordinaryPrimeRead f) (Ioi 0) := by
  apply local_of_bounded (Measurable.tsum (fun p : Nat.Primes => hm.comp (measurable_id.div_const _)))
  intro T hT
  obtain ⟨N,hN⟩ := exists_nat_ge (T/δ)
  refine ⟨(Nat.primesLE N).card*(A*T),fun x hx hxt => ?_⟩
  rw [ordinaryPrimeRead_eq_finite hδ hx hz ((div_le_div_of_nonneg_right hxt.le hδ.le).trans hN)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ ∈ Nat.primesLE N, A*T := by
      refine sum_le_sum fun p hp => ?_
      have h1 : (1:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
      exact (hb _ (div_pos hx (zero_lt_one.trans_le h1))).trans (mul_le_mul_of_nonneg_left
        ((div_le_self hx.le h1).trans hxt.le) hA)
    _ = _ := by simp

private theorem near_zero_bound {f : ℝ → ℂ} {δ : ℝ} (hδ : 0<δ)
    (h : ∀ t, 0<t → t<δ → f t=0) (a : ℝ) : f =O[𝓝[>] 0] (fun x : ℝ => x^a) := by
  apply IsBigO.of_bound 0
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hδ)] with t ht ht'
  simp only [h t ht ht',norm_zero,zero_mul,le_refl]

private theorem mellin_diff_of_power {f : ℝ → ℂ} {b δ : ℝ} (hl : LocallyIntegrableOn f (Ioi 0))
    (hδ : 0<δ) (hz : ∀ t, 0<t → t<δ → f t=0) (h : f =O[atTop] (fun x : ℝ => x^b)) :
    DifferentiableOn ℂ (fun z : ℂ => mellin f (-z)) {z | b<z.re} := by
  intro z hzb
  have ht := mellin_differentiableAt_of_isBigO_rpow (s := -z) (a := -b)
    (b := -z.re-1) hl (by simpa only [neg_neg] using h) (by simpa using hzb)
    (near_zero_bound hδ hz ( -(-z.re-1))) (by simp only [neg_re]; linarith)
  exact (ht.comp z differentiableAt_neg).differentiableWithinAt

/-- The multiplicative change of variable at each prime also scales its
absolute Mellin integral, giving absolute convergence before interchange. -/
private theorem prime_read_mellin_real {f : ℝ → ℂ} {s : ℝ} (hs : 1<s)
    (hf : MellinConvergent f (-(s:ℂ))) :
    mellin (ordinaryPrimeRead f) (-(s:ℂ)) = (_root_.RHTower.primeZeta s:ℂ)*mellin f (-(s:ℂ)) := by
  let F (p : Nat.Primes) (t : ℝ) := (t:ℂ)^(-(s:ℂ)-1)*f (t/p.1)
  let G (t : ℝ) := ‖(t:ℂ)^(-(s:ℂ)-1)*f t‖
  have hpp (p : Nat.Primes) : (0:ℝ)<p.1 := by exact_mod_cast p.2.pos
  have hI (p : Nat.Primes) : IntegrableOn (F p) (Ioi 0) := by
    have h := (MellinConvergent.comp_mul_left (inv_pos.mpr (hpp p))).mpr hf
    simpa only [MellinConvergent,F,smul_eq_mul,div_eq_inv_mul] using h
  have hnorm (p : Nat.Primes) :
      (∫ t in Ioi (0:ℝ), ‖F p t‖)=(p.1:ℝ)^(-s)*(∫ t in Ioi (0:ℝ), G t) := by
    let d := (p.1:ℝ)
    have hd : 0<d := hpp p
    have he (t : ℝ) (ht : 0<t) : ‖F p t‖=d^(-s-1)*G (d⁻¹*t) := by
      have h' : 0<d⁻¹*t := mul_pos (inv_pos.mpr hd) ht
      simp only [F,G,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht,
        Complex.norm_cpow_eq_rpow_re_of_pos h',sub_re,neg_re,ofReal_re,one_re,
        div_eq_inv_mul]
      rw [← mul_assoc,← Real.mul_rpow hd.le h'.le,mul_inv_cancel_left₀ hd.ne']
    rw [setIntegral_congr_fun measurableSet_Ioi he,integral_const_mul,
      integral_comp_mul_left_Ioi G _ (inv_pos.mpr hd),mul_zero,inv_inv,smul_eq_mul,← mul_assoc]
    congr 1
    rw [Real.rpow_sub_one hd.ne',div_mul_cancel₀ _ hd.ne']
  have hsum := (_root_.RHTower.summable_primeZetaTerm hs).mul_right (∫ t in Ioi (0:ℝ),G t)
  have hswap := integral_tsum_of_summable_integral_norm hI (hsum.congr fun p => (hnorm p).symm)
  have hrow (p : Nat.Primes) : (∫ t in Ioi (0:ℝ), F p t) =
      (((p.1:ℝ)^(-s):ℝ):ℂ)*mellin f (-(s:ℂ)) := by
    change mellin (fun t : ℝ => f (t / p.1)) (-(s:ℂ))=_
    simp only [div_eq_inv_mul]
    rw [mellin_comp_mul_left f _ (inv_pos.mpr (hpp p)),neg_neg,smul_eq_mul,
      ← Complex.ofReal_cpow (inv_pos.mpr (hpp p)).le,Real.inv_rpow (hpp p).le,
      Real.rpow_neg (hpp p).le]
  rw [mellin]
  calc
    _ = ∫ t in Ioi (0:ℝ), ∑' p, F p t := by
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by
        simp only [ordinaryPrimeRead,F,smul_eq_mul,tsum_mul_left]
    _ = _ := by
      rw [← hswap]
      simp_rw [hrow]
      rw [tsum_mul_right,← Complex.ofReal_tsum]
      rfl

private theorem mellin_conv_of_power {f : ℝ → ℂ} {b δ : ℝ} (hl : LocallyIntegrableOn f (Ioi 0))
    (hδ : 0<δ) (hz : ∀ t, 0<t → t<δ → f t=0) (h : f =O[atTop] (fun x : ℝ => x^b))
    {s : ℂ} (hs : b<s.re) : MellinConvergent f (-s) :=
  mellinConvergent_of_isBigO_rpow (a := -b) (b := -s.re-1) hl
    (by simpa only [neg_neg] using h) (by simpa using hs) (near_zero_bound hδ hz _)
    (by simp only [neg_re]; linarith)

private def linearCut (c : ℂ) (x : ℝ) : ℂ := if 1<x then c*x else 0

private theorem cut_measurable (c : ℂ) : Measurable (linearCut c) :=
  Measurable.ite measurableSet_Ioi (measurable_const.mul Complex.measurable_ofReal) measurable_const

private theorem cut_bound (c : ℂ) {x : ℝ} (hx : 0<x) : ‖linearCut c x‖≤‖c‖*x := by
  unfold linearCut
  split
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx]
  · simp [mul_nonneg (norm_nonneg c) hx.le]

private theorem of_linear_bound {f : ℝ → ℂ} {A : ℝ} (hb : ∀ x : ℝ, 0<x → ‖f x‖≤A*x) :
    f =O[atTop] (fun x : ℝ => x^(1:ℝ)) := by
  apply IsBigO.of_bound A
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos hx] using hb x hx

private theorem local_of_linear {f : ℝ → ℂ} (hm : Measurable f) {A : ℝ}
    (hA : 0≤A) (hb : ∀ t, 0<t → ‖f t‖≤A*t) : LocallyIntegrableOn f (Ioi 0) :=
  local_of_bounded hm (fun T _ => ⟨A*T,fun x hx ht => (hb x hx).trans
    (mul_le_mul_of_nonneg_left ht.le hA)⟩)

private theorem mellin_linearCut (c : ℂ) {s : ℂ} (hs : 1<s.re) :
    mellin (linearCut c) (-s) = c/(s-1) := by
  rw [mellin,setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (zero_le_one : (0:ℝ)≤1)) (fun x hx => by simp [linearCut,show ¬1<x from hx.2])]
  have he (x : ℝ) (hx : x∈Ioi (1:ℝ)) :
      (x:ℂ)^(-s-1) • linearCut c x = c*(x:ℂ)^(-s) := by
    simp only [linearCut,if_pos (show 1<x from hx),smul_eq_mul]
    have hpow : (x:ℂ)^(-s-1)*(x:ℂ)=(x:ℂ)^(-s) := calc
      _ = (x:ℂ)^(-s-1)*(x:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
      _ = _ := by rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'),
        sub_add_cancel]
    rw [mul_left_comm,hpow]
  rw [setIntegral_congr_fun measurableSet_Ioi he,integral_const_mul,
    integral_Ioi_cpow_of_lt (by simpa using hs) one_pos,Complex.ofReal_one,Complex.one_cpow]
  ring

private theorem log_line_nonzero {f : ℝ → ℂ} (hf : Measurable f) {δ A : ℝ}
    (hδ : 0<δ) (hz : ∀ x, 0<x → x<δ → f x=0)
    (hb : ∀ x, 0<x → ‖f x‖≤A*x) {l r : ℝ} (hl : 0<l) (hlr : l<r)
    (h : ∀ x, l<x → x<r → f x≠0) : ∃ s : ℂ, 1<s.re ∧ mellin f (-s)≠0 := by
  let G := _root_.RHTower.logMellinLineSource f (-3)
  let U := -Real.log δ
  let H (k : ℝ) := (Iic U).indicator (fun x : ℝ => Real.exp (k*x))
  have hI {k : ℝ} (hk : 0<k) : Integrable (H k) :=
    (integrableOn_exp_mul_Iic hk U).integrable_indicator measurableSet_Iic
  have hG : AEStronglyMeasurable G volume := by
    unfold G _root_.RHTower.logMellinLineSource
    exact (Measurable.smul (by fun_prop) (hf.comp (Real.measurable_exp.comp measurable_neg))).aestronglyMeasurable
  have hdom (x : ℝ) : ‖G x‖ ≤ A*H 2 x := by
    by_cases hx : x≤U
    · simp only [G,_root_.RHTower.logMellinLineSource,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
        neg_neg,H,indicator_of_mem (mem_Iic.mpr hx)]
      apply (mul_le_mul_of_nonneg_left (hb _ (Real.exp_pos _)) (Real.exp_pos _).le).trans_eq
      rw [mul_left_comm,← Real.exp_add,show 3*x+-x=2*x by ring]
    · have he : Real.exp (-x)<δ := (Real.exp_lt_exp.mpr (by
          change ¬x≤ -Real.log δ at hx; linarith only [lt_of_not_ge hx] : -x<Real.log δ)).trans_eq (Real.exp_log hδ)
      simp [G,_root_.RHTower.logMellinLineSource,hz _ (Real.exp_pos _) he,H,hx]
  have hL : Integrable G := ((hI (by norm_num : (0:ℝ)<2)).const_mul A).mono' hG (Eventually.of_forall hdom)
  have hsq : Integrable (fun x => ‖G x‖^2) := by
    apply ((hI (by norm_num : (0:ℝ)<4)).const_mul (A^2)).mono' (hG.norm.pow 2)
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    apply (pow_le_pow_left₀ (norm_nonneg _) (hdom x) 2).trans_eq
    rw [mul_pow]
    by_cases hx : x≤U
    · simp only [H,indicator_of_mem (mem_Iic.mpr hx),sq,← Real.exp_add,show 2*x+2*x=4*x by ring]
    · simp [H,hx]
  have hLp : MemLp G 2 volume := (memLp_two_iff_integrable_sq_norm hG).mpr hsq
  have he := _root_.RHTower.integral_norm_sq_mellin_line_eq_logMellinLineSource hL hLp
  change (∫ t : ℝ, ‖mellin f (((-3:ℝ):ℂ)+t*I)‖^2) = 2*Real.pi*∫ x, ‖G x‖^2 at he
  have hpos : 0<∫ x, ‖G x‖^2 := by
    apply (integral_pos_iff_support_of_nonneg (fun _ => sq_nonneg _) hsq).mpr
    have hlog : -Real.log r < -Real.log l := neg_lt_neg (Real.log_lt_log hl hlr)
    apply (isOpen_Ioo.measure_pos volume (Set.nonempty_Ioo.mpr hlog)).trans_le
    apply measure_mono
    intro x hx
    have hxl : l<Real.exp (-x) := (Real.log_lt_iff_lt_exp hl).mp (by linarith only [hx.2])
    have hxr : Real.exp (-x)<r := (Real.exp_lt_exp.mpr
      (by linarith only [hx.1] : -x<Real.log r)).trans_eq (Real.exp_log (hl.trans hlr))
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (smul_ne_zero (Real.exp_pos _).ne' (h _ hxl hxr)))
  by_contra! hvan
  have hzline (t : ℝ) : mellin f (((-3:ℝ):ℂ)+t*I)=0 := by
    rw [show (((-3:ℝ):ℂ)+(t:ℂ)*I)= -((3:ℂ)-(t:ℂ)*I) by push_cast; ring]
    exact hvan _ (by simp)
  simp only [hzline,norm_zero,zero_pow (by decide : 2≠0),integral_zero] at he
  exact (mul_pos (by positivity : 0<2*Real.pi) hpos).ne' he.symm

private theorem right_real_complex :
    Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(show Tendsto (fun t : ℝ => (t:ℂ)) (𝓝 1) (𝓝 1) by
    simpa using Complex.continuous_ofReal.tendsto (1:ℝ)).mono_left nhdsWithin_le_nhds,?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact fun he => (show (1:ℝ)<t from ht).ne' (by exact_mod_cast (show (t:ℂ)=1 from he))

private theorem no_small_prime_read {f : ℝ → ℂ} (hm : Measurable f) {δ A : ℝ}
    (hδ : 0<δ) (hA : 0≤A) (hz : ∀ t, 0<t → t<δ → f t=0) (hb : ∀ t, 0<t → ‖f t‖≤A*t)
    (c : ℂ) (hc : (fun x => f x-linearCut c x) =O[atTop] (fun x : ℝ => x^(0:ℝ)))
    {l r : ℝ} (hl : 0<l) (hlr : l<r) (hnz : ∀ t, l<t → t<r → f t≠0)
    {b : ℝ} (hb1 : b<1) : ¬ordinaryPrimeRead f =O[atTop] (fun x : ℝ => x^b) := by
  intro hsmall
  let g := fun x => f x-linearCut c x
  let H := fun s : ℂ => mellin (ordinaryPrimeRead f) (-s)
  let D := fun s : ℂ => mellin g (-s)+c/(s-1)
  let V := fun a : ℝ => {s : ℂ | a<s.re}
  have hopen (a : ℝ) : IsOpen (V a) := isOpen_lt continuous_const Complex.continuous_re
  have hfl := local_of_linear hm hA hb
  have hcut := local_of_linear (cut_measurable c) (norm_nonneg c) (fun _ => cut_bound c)
  have hgl : LocallyIntegrableOn g (Ioi 0) := hfl.sub hcut
  have hgz (t : ℝ) (ht : 0<t) (h : t<min δ 1) : g t=0 := by
    simp [g,hz t ht (h.trans_le (min_le_left ..)),linearCut,(h.trans_le (min_le_right ..)).not_gt]
  have hδ' := lt_min hδ zero_lt_one
  have hgd := mellin_diff_of_power hgl hδ' hgz hc
  have hDm : MeromorphicOn D (V 0) := fun z hz =>
    ((hgd.analyticOnNhd (hopen 0) z hz).meromorphicAt).add
      (meromorphicAt_const.div (meromorphicAt_id.sub meromorphicAt_const))
  have hread0 (t : ℝ) (ht : 0<t) (hh : t<δ) : ordinaryPrimeRead f t=0 := by
    apply tsum_eq_zero
    intro p
    have h1 : (1:ℝ)≤p.1 := by exact_mod_cast p.2.pos
    exact hz _ (div_pos ht (zero_lt_one.trans_le h1)) ((div_le_self ht.le h1).trans_lt hh)
  have hHd := mellin_diff_of_power (read_local hm hδ hA hz hb) hδ hread0 hsmall
  have hfs {s : ℂ} (hs : 1<s.re) := mellin_conv_of_power hfl hδ hz (of_linear_bound hb) hs
  have heuler {s : ℂ} (hs : 1<s.re) : D s=mellin f (-s) := by
    have hrc := mellin_conv_of_power hcut zero_lt_one (fun t _ ht => by simp [linearCut,ht.not_gt])
      (of_linear_bound (fun _ hx => cut_bound c hx)) hs
    rw [show D s=mellin g (-s)+mellin (linearCut c) (-s) by rw [mellin_linearCut c hs]; rfl]
    simp only [mellin,g,smul_sub,integral_sub (hfs hs) hrc,sub_add_cancel]
  have h1 : (1:ℂ)∈V 0 := by change (0:ℝ)<(1:ℂ).re; norm_num
  have hm1 := (hHd.analyticOnNhd (hopen b) 1 (by simpa [V] using hb1)).meromorphicAt
  have htop : meromorphicOrderAt D 1=⊤ := by
    by_contra hne
    apply primeZeta_no_meromorphic_right_germ (H/D) (hm1.div (hDm 1 h1))
    filter_upwards [self_mem_nhdsWithin,right_real_complex.eventually
      ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hDm 1 h1)).mp hne)] with t ht hd
    change H (t:ℂ)/D (t:ℂ)=_
    have he := prime_read_mellin_real ht (hfs (s := (t:ℂ)) ht)
    change H t=_ at he
    rw [he,← heuler (s := (t:ℂ)) ht,mul_div_cancel_right₀ _ hd]
  obtain ⟨s,hs,hn⟩ := log_line_nonzero hm hδ hz hb hl hlr hnz
  have hs0 : s∈V 0 := zero_lt_one.trans hs
  have hp : meromorphicOrderAt D s=⊤ := by
    by_contra hne
    exact (hDm.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt 0).isPreconnected hs0 h1 hne) htop
  have he : D =ᶠ[𝓝[≠] s] 0 := meromorphicOrderAt_eq_top_iff.mp hp
  have hu : D =ᶠ[𝓝 s] (fun z : ℂ => mellin f (-z)) := by
    filter_upwards [(hopen 1).mem_nhds hs] with z hz using heuler hz
  have hd := (mellin_diff_of_power hfl hδ hz (of_linear_bound hb)).differentiableAt ((hopen 1).mem_nhds hs)
  exact hn (tendsto_nhds_unique (hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' (he.symm.trans (hu.filter_mono nhdsWithin_le_nhds))))

/-- Every finite signed real-slope floor comparison to a last quotient
class of width at least three leaves an unweighted prime sum larger than
any fixed sublinear power along an unbounded sequence of real cutoffs. -/
theorem floorClassDifference_no_signed_prime_power {ι : Type*} (S : Finset ι)
    (w a : ι → ℝ) (ha : ∀ i ∈ S, 0<a i) {q : ℕ} (hq : 3≤q) {b : ℝ} (hb : b<1) :
    ¬ordinaryPrimeRead (fun t => (floorClassDifference S w a q t:ℂ)) =O[atTop] (fun x : ℝ => x^b) := by
  classical
  let f (t : ℝ) : ℂ := floorClassDifference S w a q t
  let χ (n : ℕ) : ℝ := if q∣n+1 then 1 else 0
  let D := 1+∑ i ∈ S, a i
  let B := 1+∑ i ∈ S, |w i| * a i
  let c := -(∑ i ∈ S, w i*a i)
  have hsum := sum_nonneg (s := S) (fun i hi => (ha i hi).le)
  have hD : 1≤D := le_add_of_nonneg_right hsum
  have hDp := zero_lt_one.trans_le hD
  have hB : 0≤B := add_nonneg zero_le_one (sum_nonneg fun i hi =>
    mul_nonneg (abs_nonneg _) (ha i hi).le)
  have hclass (n : ℕ) : |χ n|≤1 := by unfold χ; split <;> norm_num
  have hzero : χ 0=0 := by
    apply if_neg
    intro hd
    have ht := Nat.le_of_dvd (by decide : 0<0+1) hd
    omega
  have hf (x : ℝ) : f x=(χ ⌊x⌋₊-∑ i ∈ S, w i*(⌊a i*x⌋:ℝ):ℝ) := rfl
  have hmm : Measurable f := by
    have hχ : Measurable (fun x : ℝ => χ ⌊x⌋₊) := (measurable_of_countable χ).comp Nat.measurable_floor
    change Measurable (fun x : ℝ => ((χ ⌊x⌋₊-∑ i ∈ S,w i*(⌊a i*x⌋:ℝ):ℝ):ℂ))
    apply Complex.measurable_ofReal.comp
    apply hχ.sub
    fun_prop
  have hnear (x : ℝ) (hx : 0<x) (hxd : x<1/D) : f x=0 := by
    have hx1 : x<1 := hxd.trans_le ((div_le_one hDp).mpr hD)
    have hfl (i : ι) (hi : i∈S) : ⌊a i*x⌋=0 := by
      apply Int.floor_eq_zero_iff.mpr
      have hiD : a i≤D := (single_le_sum (fun i hi => (ha i hi).le) hi).trans
        (le_add_of_nonneg_left zero_le_one)
      exact ⟨mul_nonneg (ha i hi).le hx.le,(mul_le_mul_of_nonneg_right hiD hx.le).trans_lt
        (by linarith only [(lt_div_iff₀ hDp).mp hxd])⟩
    rw [hf,Nat.floor_eq_zero.mpr hx1,hzero,sum_eq_zero (fun i hi => by rw [hfl i hi]; simp)]
    simp
  have hg (x : ℝ) (hx : 0<x) : ‖f x‖≤B*x := by
    have hχ : |χ ⌊x⌋₊|≤x := by
      by_cases h : 1≤x
      · exact (hclass _).trans h
      · rw [Nat.floor_eq_zero.mpr (lt_of_not_ge h),hzero,abs_zero]; exact hx.le
    have hrow (i : ι) (hi : i∈S) : |w i*(⌊a i*x⌋:ℝ)|≤(|w i| * a i)*x := by
      rw [abs_mul,abs_of_nonneg (by exact_mod_cast (Int.floor_nonneg.mpr (mul_nonneg (ha i hi).le hx.le)) :
        (0:ℝ)≤(⌊a i*x⌋:ℝ)),mul_assoc]
      exact mul_le_mul_of_nonneg_left (Int.floor_le _) (abs_nonneg _)
    rw [hf,Complex.norm_real,Real.norm_eq_abs]
    apply (abs_sub _ _).trans
    have h := add_le_add hχ ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hrow))
    exact h.trans_eq (by rw [← sum_mul]; dsimp only [B]; ring)
  have hregular : (fun x => f x-linearCut (c:ℂ) x) =O[atTop] (fun x : ℝ => x^(0:ℝ)) := by
    apply IsBigO.of_bound (1+∑ i ∈ S, |w i|)
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    have he : f x-linearCut (c:ℂ) x = ((χ ⌊x⌋₊+∑ i ∈ S,w i*Int.fract (a i*x):ℝ):ℂ) := by
      rw [hf,linearCut,if_pos hx,← Complex.ofReal_mul,← Complex.ofReal_sub]
      congr 1
      dsimp only [c]
      rw [neg_mul,sub_neg_eq_add,sum_mul]
      simp only [Int.fract,mul_sub,sum_sub_distrib,mul_assoc]
      ring
    rw [he,Complex.norm_real,Real.rpow_zero,norm_one,mul_one,Real.norm_eq_abs]
    apply (abs_add_le _ _).trans (add_le_add (hclass _) _)
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => by
      rw [abs_mul,abs_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (Int.fract_lt_one _).le)
  obtain ⟨l,r,e,hl,hlr,he,hv⟩ := floorClassDifference_interval S w a ha hq
  exact no_small_prime_read hmm (one_div_pos.mpr hDp) hB hnear hg (c:ℂ) hregular hl hlr
    (fun x hx hu => fun hz => by
      have hz' := Complex.ofReal_eq_zero.mp (show ((floorClassDifference S w a q x:ℝ):ℂ)=0 from hz)
      have h := hv x hx.le hu
      rw [hz',abs_zero] at h
      exact he.ne h) hb

end GaloisForLFunctions.ExceptionalLayerTheory
