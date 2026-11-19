import GaloisForLFunctions.RHTower.BurnolFirstWallSourceMass

/-!
# Cancellation below the abscissa of the fractional test

On the reflected state ray the phase is y exp(z). The bounded primitive of
the centered sawtooth controls its weighted primitive uniformly by 1/y.
Averaging translates through that same length transfers this cancellation
to an integrable state with a small first absolute increment.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower

/-- The centered portion of the scaled kernel on the reflected state ray. -/
def centeredLogFraction (y : ℝ) : ℝ → ℝ :=
  (Ioi 0).indicator (fun z : ℝ => Real.exp (-z/2)*burnolCenteredSawtooth (y*Real.exp z))

theorem measurable_centeredLogFraction (y : ℝ) : Measurable (centeredLogFraction y) :=
  ((by fun_prop : Measurable fun z : ℝ => Real.exp (-z/2)).mul
    (measurable_burnolCenteredSawtooth.comp (measurable_const.mul Real.measurable_exp))).indicator measurableSet_Ioi

theorem abs_centeredLogFraction_le (y z : ℝ) : |centeredLogFraction y z| ≤ 1 := by
  by_cases hz : z ∈ Ioi (0:ℝ)
  · rw [centeredLogFraction,indicator_of_mem hz,abs_mul,abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-z/2) ≤ 1 := Real.exp_le_one_iff.mpr (by have hz0 : 0 < z := hz; linarith only [hz0])
    exact (mul_le_mul he (abs_burnolCenteredSawtooth_le _) (abs_nonneg _) zero_le_one).trans (by norm_num)
  · rw [centeredLogFraction,indicator_of_notMem hz,abs_zero]; exact zero_le_one

private theorem centeredLogFraction_interval (y a b : ℝ) :
    IntervalIntegrable (centeredLogFraction y) volume a b := by
  constructor <;> exact Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    (measurable_centeredLogFraction y).aestronglyMeasurable (Eventually.of_forall (abs_centeredLogFraction_le y))

/-- The bound includes the initial and terminal values of the periodic primitive. -/
theorem abs_primitive_centeredLogFraction {y : ℝ} (hy : 0 < y) (r : ℝ) :
    |∫ z in (0:ℝ)..r, centeredLogFraction y z| ≤ 1/y := by
  rcases le_or_gt r 0 with hr | hr
  · rw [intervalIntegral.integral_symm,intervalIntegral.integral_of_le hr]
    have hz : ∫ z in Ioc r 0, centeredLogFraction y z = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun z hz => indicator_of_notMem (s := Ioi (0:ℝ)) (not_lt.mpr hz.2) _
    rw [hz,neg_zero,abs_zero]; positivity
  let E := fun z : ℝ => Real.exp (-(3/2)*z)
  let Q := fun z : ℝ => burnolCenteredSawtoothPrimitive (y*Real.exp z)
  let B := fun z : ℝ => E z*Q z
  have hE : Continuous E := by dsimp only [E]; fun_prop
  have hQ : Continuous Q := continuous_burnolCenteredSawtoothPrimitive.comp (continuous_const.mul Real.continuous_exp)
  have hB : Continuous B := hE.mul hQ
  have hder (z : ℝ) (hz : z ∈ Ioo 0 r) : HasDerivWithinAt B
      (y*centeredLogFraction y z-(3/2)*B z) (Ioi z) z := by
    have hphase := (Real.hasDerivAt_exp z).const_mul y
    have hmaps : MapsTo (fun t : ℝ => y*Real.exp t) (Ioi z) (Ici (y*Real.exp z)) :=
      fun _ ht => mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht.le) hy.le
    have hq := (hasDerivWithinAt_burnolCenteredSawtoothPrimitive (y*Real.exp z)).comp z
      hphase.hasDerivWithinAt hmaps
    have he := (((hasDerivAt_id z).const_mul (-(3/2:ℝ))).exp).hasDerivWithinAt (s := Ioi z)
    have hp := he.mul hq
    apply hp.congr_deriv
    rw [centeredLogFraction,indicator_of_mem (show z ∈ Ioi (0:ℝ) from hz.1)]
    have hx : E z*Real.exp z = Real.exp (-z/2) := by
      rw [show E z = Real.exp (-(3/2)*z) from rfl,← Real.exp_add]; congr 1; ring
    change (E z*(-(3/2)*1))*Q z+E z*(burnolCenteredSawtooth (y*Real.exp z)*(y*Real.exp z)) = _
    dsimp only [B]
    linear_combination y*burnolCenteredSawtooth (y*Real.exp z)*hx
  have hK := centeredLogFraction_interval y 0 r
  have hBi := hB.intervalIntegrable (μ := volume) 0 r
  have hid := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hr.le hB.continuousOn hder
    ((hK.const_mul y).sub (hBi.const_mul (3/2)))
  rw [intervalIntegral.integral_sub (hK.const_mul y) (hBi.const_mul (3/2)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hid
  have hcoef (z : ℝ) : |B z| ≤ (1/8)*E z := by
    rw [show B z=E z*Q z from rfl,abs_mul,abs_of_pos (Real.exp_pos _),mul_comm (1/8:ℝ)]
    exact mul_le_mul_of_nonneg_left (abs_burnolCenteredSawtoothPrimitive_le _) (Real.exp_pos _).le
  have hbound (z : ℝ) (hz : 0 ≤ z) : |B z| ≤ 1/8 := (hcoef z).trans
    (mul_le_of_le_one_right (by norm_num) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hz)))
  have hIB : |∫ z in (0:ℝ)..r, B z| ≤ (1/8)*(2/3) := by
    have hEi : IntegrableOn E (Ioi 0) := integrableOn_exp_mul_Ioi (by norm_num : -(3/2:ℝ)<0) 0
    have hmajor : IntegrableOn (fun z => (1/8)*E z) (Ioi 0) := hEi.const_mul _
    rw [intervalIntegral.integral_of_le hr.le,← Real.norm_eq_abs]
    apply (norm_integral_le_of_norm_le (μ := volume.restrict (Ioc 0 r)) (f := B) (g := fun z => (1/8)*E z)
      (hmajor.mono_set Ioc_subset_Ioi_self) (Eventually.of_forall (fun z => hcoef z))).trans
    apply (setIntegral_mono_set hmajor (Eventually.of_forall fun z => by
      change 0 ≤ (1/8)*E z
      exact mul_nonneg (by norm_num) (Real.exp_pos _).le)
      (Eventually.of_forall fun _ hz => hz.1)).trans_eq
    rw [integral_const_mul,show (∫ z in Ioi (0:ℝ), E z) = 2/3 by
      dsimp only [E]; rw [integral_exp_mul_Ioi (by norm_num : -(3/2:ℝ)<0)]; norm_num]
  rw [abs_le] at hIB
  have hrB := abs_le.mp (hbound r hr.le)
  have h0B := abs_le.mp (hbound 0 le_rfl)
  rw [le_div_iff₀ hy,mul_comm,show y*|∫ z in (0:ℝ)..r, centeredLogFraction y z| =
    |y*(∫ z in (0:ℝ)..r, centeredLogFraction y z)| by rw [abs_mul,abs_of_pos hy],abs_le]
  constructor <;> linarith only [hid,hIB.1,hIB.2,hrB.1,hrB.2,h0B.1,h0B.2]

/-- Uniform cancellation at the scale of one reciprocal frequency. Averaging
over translates introduces one increment at each small shift and one at the
terminal shift; the latter is tested against the bounded primitive. -/
theorem centeredLogFraction_bound_of_increments {f : ℝ → ℝ} (hm : Measurable f) (hi : Integrable f)
    {y D : ℝ} (hy : 0 < y)
    (hinc : ∀ s ∈ Ioc 0 (1/y), (∫ x, |f (x-s)-f x|) ≤ D) :
    |∫ x, f x*centeredLogFraction y x| ≤ 2*D := by
  let b := 1/y
  have hb : 0 < b := one_div_pos.mpr hy
  let k := centeredLogFraction y
  let G := fun x => ∫ z in (0:ℝ)..x, k z
  let I := ∫ x, f x*k x
  let J := fun s : ℝ => ∫ x, f x*k (x+s)
  let μ := volume.restrict (Ioc 0 b)
  have hkm : Measurable k := measurable_centeredLogFraction y
  have hki (u v : ℝ) : IntervalIntegrable k volume u v := centeredLogFraction_interval y u v
  have hGm : Measurable G := (intervalIntegral.continuous_primitive hki 0).measurable
  have hG (x : ℝ) : |G x| ≤ b := abs_primitive_centeredLogFraction hy x
  have htranslate (s : ℝ) : J s = ∫ x, f (x-s)*k x := by
    rw [← integral_add_right_eq_self (fun x => f (x-s)*k x) s]
    simp only [J,add_sub_cancel_right]
  have hfk (s : ℝ) : Integrable fun x => f (x-s)*k x := by
    refine (hi.comp_sub_right s).abs.mono'
      (((hm.comp (measurable_id.sub_const s)).mul hkm).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_centeredLogFraction_le y x)
  have hf0 : Integrable fun x => f x*k x := by simpa only [sub_zero] using hfk 0
  have hdiff (s : ℝ) (hs : s ∈ Ioc 0 b) : |J s-I| ≤ D := by
    rw [htranslate,show I=∫ x, f x*k x from rfl,← integral_sub (hfk s) hf0,← Real.norm_eq_abs]
    let d := fun x : ℝ => f (x-s)*k x-f x*k x
    have hbnd (x : ℝ) : ‖d x‖ ≤ |f (x-s)-f x| := by
      rw [show d x=(f (x-s)-f x)*k x from (sub_mul ..).symm,Real.norm_eq_abs,abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_centeredLogFraction_le y x)
    exact (norm_integral_le_of_norm_le (μ := volume) (f := d) (g := fun x => |f (x-s)-f x|)
      (((hi.comp_sub_right s).sub hi).abs) (Eventually.of_forall hbnd)).trans (hinc s hs)
  let H := fun p : ℝ × ℝ => f p.2*k (p.2+p.1)
  have hHm : Measurable H := (hm.comp measurable_snd).mul (hkm.comp (measurable_snd.add measurable_fst))
  have hHi : Integrable H (μ.prod volume) := by
    refine (hi.abs.comp_snd μ).mono' hHm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    change |f p.2*k (p.2+p.1)| ≤ |f p.2|
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_centeredLogFraction_le y _)
  have hJ : Integrable J μ := hHi.integral_prod_left
  have hcell (x : ℝ) : (∫ s, k (x+s) ∂μ) = G (x+b)-G x := by
    change (∫ s in Ioc 0 b, k (x+s)) = _
    rw [← intervalIntegral.integral_of_le hb.le,intervalIntegral.integral_comp_add_left k,add_zero]
    exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals (hki 0 x) (hki x (x+b)))
  have hprod (s : ℝ) : Integrable fun x => f (x-s)*G x := by
    refine ((hi.comp_sub_right s).abs.mul_const b).mono'
      (((hm.comp (measurable_id.sub_const s)).mul hGm).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left (hG x) (abs_nonneg _)
  have hplus : Integrable fun x => f x*G (x+b) := by
    simpa only [add_sub_cancel_right] using (hprod b).comp_add_right b
  have hbase : Integrable fun x => f x*G x := by simpa only [sub_zero] using hprod 0
  have hmean : (∫ s, J s ∂μ) = ∫ x, (f (x-b)-f x)*G x := by
    have hs := integral_integral_swap (μ := μ) (ν := volume) (f := fun s x => f x*k (x+s)) hHi
    change (∫ s, (∫ x, f x*k (x+s)) ∂μ) = _
    rw [hs]; simp_rw [integral_const_mul,hcell,mul_sub]
    rw [integral_sub hplus hbase]
    simp_rw [sub_mul]
    rw [integral_sub (hprod b) hbase,← integral_add_right_eq_self (fun x => f (x-b)*G x) b]
    simp only [add_sub_cancel_right]
  have hmeanBound : |∫ s, J s ∂μ| ≤ D*b := by
    rw [hmean,← Real.norm_eq_abs]
    have hmaj := ((hi.comp_sub_right b).sub hi).abs.mul_const b
    have hp (x : ℝ) : ‖(f (x-b)-f x)*G x‖ ≤ |f (x-b)-f x| *b := by
      rw [Real.norm_eq_abs,abs_mul]; exact mul_le_mul_of_nonneg_left (hG x) (abs_nonneg _)
    refine (norm_integral_le_of_norm_le (μ := volume) (f := fun x => (f (x-b)-f x)*G x)
      (g := fun x => |f (x-b)-f x| *b) hmaj (Eventually.of_forall hp)).trans ?_
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right (hinc b ⟨hb,le_rfl⟩) hb.le
  have hvol : μ.real univ = b := by
    change (volume.restrict (Ioc 0 b)).real univ = b
    rw [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal hb.le]
  have hclose : |(∫ s, J s ∂μ)-b*I| ≤ b*D := by
    have hiI : Integrable (fun _ : ℝ => I) μ := integrable_const _
    rw [← hvol,← smul_eq_mul,← integral_const,← integral_sub hJ hiI,← Real.norm_eq_abs]
    have hp : ∀ᵐ s ∂μ, ‖J s-I‖ ≤ D := by
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := b))] with s hs
      exact hdiff s hs
    have h := norm_integral_le_of_norm_le (μ := μ) (f := fun s => J s-I)
      (g := fun _ => D) (integrable_const _) hp
    simpa only [integral_const,smul_eq_mul] using h
  change |I| ≤ 2*D
  apply le_of_mul_le_mul_left (a := b) _ hb
  rw [show b*|I|=|b*I| by rw [abs_mul,abs_of_pos hb]]
  have heq : b*I = (∫ s, J s ∂μ)-((∫ s, J s ∂μ)-b*I) := by ring
  calc |b*I| = |(∫ s, J s ∂μ)-((∫ s, J s ∂μ)-b*I)| := congrArg abs heq
       _ ≤ _ := (abs_sub _ _).trans ((add_le_add hmeanBound hclose).trans_eq (by ring))

#print axioms abs_primitive_centeredLogFraction
#print axioms centeredLogFraction_bound_of_increments
end GaloisForLFunctions.ExclusionOfTheCriticalState
