import GaloisForLFunctions.HTGeometry.MonotoneTranslationModulus
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheFractionalPartTestOfThePrimeWave
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheSignedPrimeExcessAtTheCriticalWidth

/-!
# Favorable signed readings on a set of positive relative measure

Freeze the width at the start of a short fixed-ratio interval. Translating
its Chebyshev integral leaves two endpoint averages, controlled by the prime
number theorem. The linear sieve bound gives a lower bound for the measure
of favorable centers and the wall law transports their sign to the state.
-/

noncomputable section
open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower

/-- A sublinear frozen width has mean Chebyshev slope one on every fixed-ratio
interval. Translation moves the interval integral to its two short ends. -/
theorem tendsto_frozen_chebyshev_window_mean {H : ℝ → ℝ} (hH : ∀ᶠ x in atTop, 0 < H x)
    (hsub : Tendsto (fun x => H x/x) atTop (𝓝 0)) {b : ℝ} (hb : 1 < b) :
    Tendsto (fun x => (∫ v in x..b*x, Chebyshev.psi (v+H x)-Chebyshev.psi v)/(H x*x))
      atTop (𝓝 (b-1)) := by
  have hψ := _root_.RHTower.FreeLagTrace.tendsto_psi_div
  have hpos := zero_lt_one.trans hb
  have hscale (a : ℝ) (ha : 0 < a) (h : ℝ → ℝ) (hh : ∀ᶠ x in atTop, 0 ≤ h x)
      (hs : Tendsto (fun x => h x/x) atTop (𝓝 0)) :
      Tendsto (fun x => Chebyshev.psi (a*x+h x)/x) atTop (𝓝 a) := by
    have hvar : Tendsto (fun x => a*x+h x) atTop atTop := by
      apply tendsto_atTop_mono' _ _ (tendsto_id.const_mul_atTop ha)
      exact hh.mono fun x hx => le_add_of_nonneg_right hx
    have hquot := (tendsto_const_nhds (x := a)).add hs
    rw [add_zero] at hquot
    have hratio : Tendsto (fun x => (a*x+h x)/x) atTop (𝓝 a) := hquot.congr' <|
      (eventually_gt_atTop (0:ℝ)).mono fun x hx => by field_simp [hx.ne'] <;> ring
    have hprod := (hψ.comp hvar).mul hratio
    rw [one_mul] at hprod
    exact hprod.congr' <| (hvar.eventually_gt_atTop 0).mono fun x hx => by
      change Chebyshev.psi (a*x+h x)/(a*x+h x)*((a*x+h x)/x)=_
      field_simp [hx.ne'] <;> ring
  have hzero : Tendsto (fun x : ℝ => (0:ℝ)/x) atTop (𝓝 0) := by
    simp only [zero_div]; exact tendsto_const_nhds
  have h0 (a : ℝ) (ha : 0 < a) : Tendsto (fun x => Chebyshev.psi (a*x)/x) atTop (𝓝 a) := by
    simpa only [add_zero] using hscale a ha (fun _ => 0) (Eventually.of_forall fun _ => le_rfl) hzero
  have hlo := (h0 b hpos).sub (hscale 1 zero_lt_one H (hH.mono fun _ h => h.le) hsub)
  have hup := (hscale b hpos H (hH.mono fun _ h => h.le) hsub).sub (h0 1 zero_lt_one)
  simp only [one_mul] at hlo hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [eventually_gt_atTop (0:ℝ),hH] with x hx hh
    rw [← sub_div,div_le_div_iff₀ hx (mul_pos hh hx)]
    have h := sub_le_sub (length_mul_left_le_integral Chebyshev.psi_mono (c := b*x) hh.le)
      (integral_le_length_mul_right Chebyshev.psi_mono (c := x) hh.le)
    rw [← mul_sub,← integral_translate_sub_eq_end_windows Chebyshev.psi_mono] at h
    calc _ = (H x*(Chebyshev.psi (b*x)-Chebyshev.psi (x+H x)))*x := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right h hx.le
  · filter_upwards [eventually_gt_atTop (0:ℝ),hH] with x hx hh
    rw [← sub_div,div_le_div_iff₀ (mul_pos hh hx) hx]
    have h := integral_translate_sub_le Chebyshev.psi_mono (a := x) (b := b*x) hh.le
    calc _ ≤ (H x*(Chebyshev.psi (b*x+H x)-Chebyshev.psi x))*x := mul_le_mul_of_nonneg_right h hx.le
         _ = _ := by ring


/-- A lower signed mean and a uniform upper bound force positive measure of
centers above the lower level. The witness set is measurable. -/
private theorem lower_mean_gives_good_centers {x y c d D : ℝ} (hxy : x ≤ y) (hc : 0 ≤ c)
    {q : ℝ → ℝ} (hm : Measurable q) (hi : IntervalIntegrable q volume x y)
    (havg : d*(y-x) ≤ ∫ u in x..y, q u) (hq : ∀ u ∈ Ioc x y, q u ≤ D) :
    ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ Ioc x y ∧ (∀ u ∈ A, c < q u) ∧
      (d-c)*(y-x) ≤ D*volume.real A := by
  let I := Ioc x y
  let A := I ∩ {u | c < q u}
  have hI : MeasurableSet I := measurableSet_Ioc
  have hA : MeasurableSet A := hI.inter (measurableSet_lt measurable_const hm)
  have hAI : A ⊆ I := inter_subset_left
  have hC : IntegrableOn (fun _ : ℝ => c) I := integrableOn_const (by dsimp only [I]; finiteness)
  have hD : IntegrableOn (fun _ : ℝ => D) I := integrableOn_const (by dsimp only [I]; finiteness)
  have hInd : IntegrableOn (A.indicator fun _ : ℝ => D) I := hD.indicator hA
  have hbig : (∫ u in I, q u) ≤ ∫ u in I, c+A.indicator (fun _ : ℝ => D) u := by
    apply setIntegral_mono_on (hi.integrableOn_Ioc) (hC.add hInd) hI
    intro u hu
    by_cases h : u ∈ A
    · rw [indicator_of_mem h]; exact (hq u hu).trans (le_add_of_nonneg_left hc)
    · rw [indicator_of_notMem h,add_zero]; exact le_of_not_gt fun hgt => h ⟨hu,hgt⟩
  have hIA : (volume.restrict I).real A = volume.real A := by
    rw [measureReal_restrict_apply hA,inter_eq_left.mpr hAI]
  rw [integral_add hC hInd,setIntegral_const,integral_indicator_const D hA,hIA,smul_eq_mul,smul_eq_mul] at hbig
  have hwidth : volume.real I=y-x := by
    exact Real.volume_real_Ioc.trans (max_eq_left (sub_nonneg.mpr hxy))
  rw [hwidth] at hbig
  rw [intervalIntegral.integral_of_le hxy] at havg
  refine ⟨A,hA,hAI,fun _ h => h.2,?_⟩
  linarith only [hbig,havg]

private def arithmeticWallWidth (x : ℝ) := criticalWallWidth (Real.log x)

private theorem arithmeticWallWidth_eq {x : ℝ} (hx : 0 < x) :
    arithmeticWallWidth x=Real.sqrt (x*Real.log x) := by
  rw [arithmeticWallWidth,criticalWallWidth,Real.exp_half,Real.exp_log hx,Real.sqrt_mul hx.le]

private theorem arithmeticWallWidth_sublinear :
    Tendsto (fun x => arithmeticWallWidth x/x) atTop (𝓝 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  rw [Real.sqrt_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  have hx0 := zero_lt_one.trans hx
  change Real.sqrt (Real.log x/x) = arithmeticWallWidth x/x
  rw [arithmeticWallWidth_eq hx0,Real.sqrt_div (Real.log_pos hx).le,Real.sqrt_mul hx0.le]
  apply (div_eq_div_iff (Real.sqrt_pos.2 hx0).ne' hx0.ne').mpr
  calc _ = Real.sqrt (Real.log x)*(Real.sqrt x)^2 := congrArg (Real.sqrt (Real.log x)*·) (Real.sq_sqrt hx0.le).symm
       _ = _ := by ring

/-- On a fixed-ratio interval the critical width grows by at most that same
ratio once log x ≥ 1. This keeps a frozen prime interval inside the true one. -/
private theorem arithmeticWallWidth_comparison {x u b : ℝ} (hx : Real.exp 1 ≤ x)
    (hb : 1 ≤ b) (hu : u ∈ Icc x (b*x)) :
    0 < arithmeticWallWidth x ∧ arithmeticWallWidth x ≤ arithmeticWallWidth u ∧
      arithmeticWallWidth u ≤ b*arithmeticWallWidth x := by
  have hx0 := (Real.exp_pos _).trans_le hx
  have hu0 := hx0.trans_le hu.1
  have hb0 := zero_lt_one.trans_le hb
  have hlx : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hlu := Real.log_le_log hx0 hu.1
  have hh : Real.log u ≤ b*Real.log x := by
    have h := Real.log_le_log hu0 hu.2
    rw [Real.log_mul hb0.ne' hx0.ne'] at h
    have hlog := Real.log_le_sub_one_of_pos hb0
    have hp := mul_le_mul_of_nonneg_left hlx (sub_nonneg.mpr hb)
    linarith only [hp,hlog,h]
  rw [arithmeticWallWidth_eq hx0,arithmeticWallWidth_eq hu0]
  have hl0 := zero_lt_one.trans_le hlx
  refine ⟨Real.sqrt_pos.2 (mul_pos hx0 hl0), Real.sqrt_le_sqrt
    (mul_le_mul hu.1 hlu hl0.le hu0.le),?_⟩
  calc _ ≤ Real.sqrt ((b*x)*(b*Real.log x)) := Real.sqrt_le_sqrt
            (mul_le_mul hu.2 hh (hl0.le.trans hlu) (mul_nonneg hb0.le hx0.le))
       _ = b*Real.sqrt (x*Real.log x) := by
            rw [show (b*x)*(b*Real.log x)=b^2*(x*Real.log x) by ring,
              Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hb0.le]

private theorem arithmeticWallWidth_sieve : ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ x in atTop,
    Chebyshev.psi (x+arithmeticWallWidth x)-Chebyshev.psi x ≤ C*arithmeticWallWidth x := by
  obtain ⟨C,hC,hbound⟩ := mangoldt_mass_on_power_width
  refine ⟨C+1,by linarith only [hC],?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ)] with x ht hx
  let t := Real.log x
  let H := arithmeticWallWidth x
  have hExp : Real.exp t=x := Real.exp_log hx
  have ht0 := zero_lt_one.trans_le ht
  have hR : 1 ≤ Real.sqrt t := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ht
  have hH : 0 < H := mul_pos (Real.exp_pos _) (Real.sqrt_pos.mpr ht0)
  have hlo : Real.exp (t/4) ≤ H := (Real.exp_le_exp.mpr (by linarith only [ht0])).trans
    (le_mul_of_one_le_right (Real.exp_pos (t/2)).le hR)
  have hup : H ≤ x := by
    change arithmeticWallWidth x ≤ x
    rw [arithmeticWallWidth_eq hx]
    apply (Real.sqrt_le_left hx.le).mpr
    rw [sq]; apply mul_le_mul_of_nonneg_left _ hx.le
    linarith only [Real.log_le_sub_one_of_pos hx]
  have hc := hbound t ht H hlo (hup.trans hExp.ge)
  rw [hExp] at hc
  have hψ : Chebyshev.psi (x+H)-Chebyshev.psi x =
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x+H⌋₊, ArithmeticFunction.vonMangoldt n := by
    unfold Chebyshev.psi
    rw [← Finset.sum_Ioc_consecutive (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))
      (Nat.zero_le ⌊x⌋₊) (Nat.floor_mono (le_add_of_nonneg_right hH.le))]
    ring
  change Chebyshev.psi (x+H)-Chebyshev.psi x ≤ (C+1)*H
  rw [hψ]; exact hc.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hH.le)

/-- A positive fraction of starting points have a favorable Chebyshev slope
already at the frozen width of the left endpoint. -/
private theorem frozen_criticalWidth_good_centers {b c : ℝ} (hb : 1 < b) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ x : ℝ in atTop, ∃ A : Set ℝ, MeasurableSet A ∧
      A ⊆ Ioc x (b*x) ∧ κ*x ≤ volume.real A ∧ ∀ u ∈ A,
        c*arithmeticWallWidth x < Chebyshev.psi (u+arithmeticWallWidth x)-Chebyshev.psi u := by
  let H := arithmeticWallWidth
  have hH : ∀ᶠ x : ℝ in atTop, 0 < H x :=
    (eventually_ge_atTop (Real.exp 1)).mono fun x hx =>
      (arithmeticWallWidth_comparison (b := 1) hx le_rfl ⟨le_rfl,by rw [one_mul]⟩).1
  have hf := tendsto_frozen_chebyshev_window_mean hH arithmeticWallWidth_sublinear hb
  let d := (1+c)/2
  have hcd : c < d := by dsimp only [d]; linarith only [hc1]
  have hd1 : d < 1 := by dsimp only [d]; linarith only [hc1]
  have hbl := sub_pos.mpr hb
  have hnear := hf.eventually_const_lt (show d*(b-1) < b-1 by
    exact mul_lt_of_lt_one_left hbl hd1)
  obtain ⟨C,hC,hbound⟩ := arithmeticWallWidth_sieve
  obtain ⟨U,hU⟩ := eventually_atTop.mp hbound
  let D := b*C
  have hD : 0 < D := mul_pos (zero_lt_one.trans hb) (zero_lt_one.trans_le hC)
  refine ⟨(d-c)*(b-1)/D,div_pos (mul_pos (sub_pos.mpr hcd) hbl) hD,?_⟩
  filter_upwards [hnear,eventually_ge_atTop U,eventually_ge_atTop (Real.exp 1),hH] with x hL hxU hxe hh
  have hx := (Real.exp_pos _).trans_le hxe
  have hxy : x ≤ b*x := le_mul_of_one_le_left hx.le hb.le
  let q := fun u : ℝ => (Chebyshev.psi (u+H x)-Chebyshev.psi u)/H x
  have hshift := monotone_comp_add_right Chebyshev.psi_mono (H x)
  have hm : Measurable q := (hshift.measurable.sub Chebyshev.psi_mono.measurable).div_const (H x)
  have hi : IntervalIntegrable q volume x (b*x) :=
    (hshift.intervalIntegrable.sub Chebyshev.psi_mono.intervalIntegrable).div_const _
  have hav : d*(b*x-x) ≤ ∫ u in x..b*x, q u := by
    dsimp only [q]; rw [intervalIntegral.integral_div,le_div_iff₀ hh]
    have h := (lt_div_iff₀ (mul_pos hh hx)).mp hL
    calc _ = (d*(b-1))*(H x*x) := by ring
         _ ≤ _ := h.le
  have hq (u : ℝ) (hu : u ∈ Ioc x (b*x)) : q u ≤ D := by
    obtain ⟨_,hlo,hhi⟩ := arithmeticWallWidth_comparison hxe hb.le ⟨hu.1.le,hu.2⟩
    apply (div_le_iff₀ hh).mpr
    calc _ ≤ Chebyshev.psi (u+H u)-Chebyshev.psi u :=
             sub_le_sub_right (Chebyshev.psi_mono (add_le_add le_rfl hlo)) _
         _ ≤ C*H u := hU _ (hxU.trans hu.1.le)
         _ ≤ C*(b*H x) := mul_le_mul_of_nonneg_left hhi (zero_le_one.trans hC)
         _ = _ := by dsimp only [D]; ring
  obtain ⟨A,hA,hAI,hgood,hmass⟩ := lower_mean_gives_good_centers hxy hc0 hm hi hav hq
  refine ⟨A,hA,hAI,?_,fun u hu => (lt_div_iff₀ hh).mp (hgood u hu)⟩
  rw [div_mul_eq_mul_div,div_le_iff₀ hD]
  calc _ = (d-c)*(b*x-x) := by ring
       _ ≤ _ := hmass.trans_eq (mul_comm ..)

/-- In every late fixed-ratio interval a set of positive relative measure has
signed reading above the specified negative level. -/
private theorem signed_criticalWidth_good_centers {Φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hw : Tendsto (fun t : ℝ => criticalWidthSignedReading Φ t -
      γ*((Chebyshev.psi (Real.exp t+criticalWallWidth t)-Chebyshev.psi (Real.exp t))/criticalWallWidth t-1))
      atTop (𝓝 0)) {R ε : ℝ} (hR : 1 < R) (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ x : ℝ in atTop, ∃ A : Set ℝ, MeasurableSet A ∧
      A ⊆ Ioc x (R*x) ∧ κ*x ≤ volume.real A ∧ ∀ u ∈ A, -ε < criticalWidthSignedReading Φ (Real.log u) := by
  let δ := min (1/4) (ε/(8*γ))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1/4 := min_le_left ..
  have hδε : 8*γ*δ ≤ ε := by
    have h := (le_div_iff₀ (by positivity : 0 < 8*γ)).1 (min_le_right (1/4:ℝ) (ε/(8*γ)))
    exact (mul_comm ..).le.trans h
  let b := min R (1+δ)
  have hb : 1 < b := lt_min hR (lt_add_of_pos_right _ hδ)
  have hbR : b ≤ R := min_le_left ..
  have hbd : b ≤ 1+δ := min_le_right ..
  obtain ⟨κ,hκ,hfreq⟩ := frozen_criticalWidth_good_centers hb
    (by linarith only [hδ1] : 0 ≤ 1-δ) (by linarith only [hδ] : 1-δ < 1)
  obtain ⟨V,hV⟩ := eventually_atTop.mp <| hw.eventually_const_lt (by linarith only [hε] : -ε/2 < 0)
  refine ⟨κ,hκ,?_⟩
  filter_upwards [hfreq,eventually_ge_atTop (Real.exp V),eventually_ge_atTop (Real.exp 1)] with x hA hxV hxe
  obtain ⟨A,hm,hAI,hmeasure,hgood⟩ := hA
  have hx := (Real.exp_pos _).trans_le hxe
  refine ⟨A,hm,hAI.trans (Ioc_subset_Ioc le_rfl (mul_le_mul_of_nonneg_right hbR hx.le)),hmeasure,?_⟩
  intro u hu
  obtain ⟨hxu,hub⟩ := hAI hu
  obtain ⟨hX,hHu,hHb⟩ := arithmeticWallWidth_comparison hxe hb.le ⟨hxu.le,hub⟩
  have hU := hX.trans_le hHu
  have hnon : 0 ≤ 1-2*δ := by linarith only [hδ1]
  have hrate : (1-2*δ)*arithmeticWallWidth u ≤ (1-δ)*arithmeticWallWidth x := by
    calc _ ≤ (1-2*δ)*((1+δ)*arithmeticWallWidth x) := mul_le_mul_of_nonneg_left
                (hHb.trans (mul_le_mul_of_nonneg_right hbd hX.le)) hnon
         _ = ((1-2*δ)*(1+δ))*arithmeticWallWidth x := (mul_assoc ..).symm
         _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith only [sq_nonneg δ]) hX.le
  have hs := (hrate.trans_lt (hgood u hu)).trans_le
    (sub_le_sub_right (Chebyshev.psi_mono (add_le_add le_rfl hHu)) (Chebyshev.psi u))
  have hq := (lt_div_iff₀ hU).2 hs
  have hu0 := hx.trans hxu
  have h := hV (Real.log u) ((Real.le_log_iff_exp_le hu0).2 (hxV.trans hxu.le))
  rw [Real.exp_log hu0] at h
  change -ε/2 < criticalWidthSignedReading Φ (Real.log u) -
    γ*((Chebyshev.psi (u+arithmeticWallWidth u)-Chebyshev.psi u)/arithmeticWallWidth u-1) at h
  have hg := mul_lt_mul_of_pos_left (sub_lt_sub_right hq 1) hγ
  linarith only [h,hg,hδε,hε]

private theorem fractional_mass_of_good_centers {A : Set ℝ} (hA : MeasurableSet A) {x R κ : ℝ}
    (hx : 0 < x) (hR : 0 < R) (hAI : A ⊆ Ioc x (R*x)) (hmass : κ*x ≤ volume.real A) :
    κ/R ≤ (∫ u in A, u⁻¹) ∧
    κ/R^2 ≤ ∫ u in A, fractionalPrimeTest (Real.log x-Real.log u)*u⁻¹ := by
  have hfin : volume A ≠ ⊤ := ((measure_mono hAI).trans_lt (by finiteness)).ne
  have hbound : IntegrableOn (fun _ : ℝ => x⁻¹) A := integrableOn_const hfin
  have hi : IntegrableOn (fun u : ℝ => u⁻¹) A := by
    apply hbound.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) hA] with u hu
    have hxu := (hAI hu).1
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (hx.trans hxu).le)]
    exact (inv_le_inv₀ (hx.trans hxu) hx).2 hxu.le
  have hh := setIntegral_ge_of_const_le_real (c := (R*x)⁻¹) hA hfin (fun u hu =>
    (inv_le_inv₀ (mul_pos hR hx) (hx.trans (hAI hu).1)).2 (hAI hu).2) hi
  have hlog : κ/R ≤ ∫ u in A, u⁻¹ := by
    apply le_trans _ hh
    calc _ = (R*x)⁻¹*(κ*x) := by field_simp [hx.ne',hR.ne'] <;> ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr (mul_pos hR hx).le)
  have htest : IntegrableOn (fun u => fractionalPrimeTest (Real.log x-Real.log u)*u⁻¹) A := by
    apply hi.norm.mono' ((measurable_fractionalPrimeTest.comp
      (measurable_const.sub Real.measurable_log)).mul measurable_inv).aestronglyMeasurable
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (fractionalPrimeTest_bounds _).1
  have hkernel (u : ℝ) (hu : u ∈ A) : R⁻¹ ≤ fractionalPrimeTest (Real.log x-Real.log u) := by
    have hxu := (hAI hu).1
    have hu0 := hx.trans hxu
    have hv := sub_neg.mpr (Real.log_lt_log hx hxu)
    rw [fractionalPrimeTest,Int.fract_eq_self.mpr ⟨(Real.exp_pos _).le,Real.exp_lt_one_iff.mpr hv⟩,← Real.exp_add]
    calc R⁻¹ ≤ x/u := by
           rw [← one_div,div_le_div_iff₀ hR hu0,one_mul,mul_comm x R]; exact (hAI hu).2
         _ = Real.exp (Real.log x-Real.log u) := by rw [Real.exp_sub,Real.exp_log hx,Real.exp_log hu0]
         _ ≤ _ := Real.exp_le_exp.2 (by linarith only [hv])
  have hcmp := setIntegral_mono_on (hi.const_mul R⁻¹) htest hA (fun u hu =>
    mul_le_mul_of_nonneg_right (hkernel u hu) (inv_nonneg.mpr (hx.trans (hAI hu).1).le))
  rw [integral_const_mul] at hcmp
  refine ⟨hlog,?_⟩
  calc κ/R^2 = R⁻¹*(κ/R) := by field_simp [hR.ne'] <;> ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hR.le)).trans hcmp

/-- Restoring the complete integer complement leaves exactly the signed first
window. Both rows retain the same square charge. -/
private theorem signed_window_complement {Φ : ℝ → ℝ} {C : ℝ} (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (t : ℝ) :
    let m := ∫ u, Φ u
    let v := fun n : ℕ => (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t
    let J := wallIntegerWindow t (criticalWallWidth t)
    m*((∑' n : ℕ, v n)-m/2) = criticalWidthSignedReading Φ t + m*((∑' n : {j : ℕ // j ∉ J}, v n)-m/2) := by
  let v := fun n : ℕ => (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t
  let J := wallIntegerWindow t (criticalWallWidth t)
  let m := ∫ u, Φ u
  have hs : Summable v := ((summable_mangoldt_integerAtom hb t).sub
    (summable_continuousIntegerAtom hb t)).congr fun n => by simp only [v,sub_mul,one_mul]
  change m*((∑' n : ℕ, v n)-m/2) = _
  rw [← hs.sum_add_tsum_compl (s := J)]
  have hr : criticalWidthSignedReading Φ t = m*∑ n ∈ J, v n := (Finset.mul_sum ..).symm
  rw [hr]; ring

/-- Every fixed-ratio interval at large height contains a set of positive
relative measure on which the actual signed critical-width reading beats any
prescribed negative level. All intervals concern the same critical state. -/
theorem riemannHypothesis_or_positive_measure_of_signed_criticalWidth_centers : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ (R ε : ℝ), 1 < R → 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ x : ℝ in atTop,
        ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ Ioc x (R*x) ∧ κ*x ≤ volume.real A ∧
          κ/R ≤ (∫ u in A, u⁻¹) ∧
          κ/R^2 ≤ (∫ u in A, fractionalPrimeTest (Real.log x-Real.log u)*u⁻¹) ∧
          ∀ u ∈ A,
            let t := Real.log u
            let J := wallIntegerWindow t (criticalWallWidth t)
            let m := ∫ v, Φ v
            let v := fun n : ℕ => (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t
            -ε < criticalWidthSignedReading Φ t ∧
              m*((∑' n : {j : ℕ // j ∉ J}, v n)-m/2)-ε < m*((∑' n : ℕ, v n)-m/2) := by
  rcases riemannHypothesis_or_signed_critical_width_chebyshev_excess with hr |
    ⟨W₀,F,Φ,γ,hW,ht,hF,hc,he,hγ,_,hw,_⟩
  · exact Or.inl hr
  obtain ⟨_,_,Ψ,hΨ,heΨ,_,⟨C,_,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq : Ψ=Φ := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,fun R ε hR hε => ?_⟩
  obtain ⟨κ,hκ,hgood⟩ := signed_criticalWidth_good_centers hγ hw hR hε
  refine ⟨κ,hκ,?_⟩
  filter_upwards [hgood,eventually_gt_atTop (0:ℝ)] with x hx hx0
  obtain ⟨A,hA,hAI,hmass,hread⟩ := hx
  obtain ⟨hl,hk⟩ := fractional_mass_of_good_centers hA hx0 (zero_lt_one.trans hR) hAI hmass
  refine ⟨A,hA,hAI,hmass,hl,hk,fun u hu => ⟨hread u hu,?_⟩⟩
  dsimp only
  rw [signed_window_complement hb (Real.log u)]
  linarith only [hread u hu]

#print axioms riemannHypothesis_or_positive_measure_of_signed_criticalWidth_centers
end GaloisForLFunctions.ExclusionOfTheCriticalState
