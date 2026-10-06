import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Complete lattice Poisson identities

Compact support makes the integer translates locally finite, allowing every
translate and overlap. Fundamental-domain unfolding identifies every torus
coefficient with its full real-space integral. Absolute summability of those
coefficients then yields the complete three-dimensional Poisson identity.
The normal-periodization theorem also retains every translate for integrable
inputs with a summable majorant on each bounded translation region. The
consuming physical Schwartz theorem constructs these majorants.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RHTower.BAGTrace
namespace FullPoisson
abbrev X := Fin 3 → ℝ
abbrev Z := Fin 3 → ℤ
abbrev T := UnitAddTorus (Fin 3)
def ip (n : Z) : X := fun i => (n i : ℝ)
def q (x : X) : T := fun i => (x i : UnitAddCircle)
private def per (f : X → ℂ) (x : X) : ℂ := ∑' n : Z, f (x+ip n)

private lemma finite_translates {f : X → ℂ} (hf : HasCompactSupport f) (R : ℝ) :
    ∃ S : Finset Z, ∀ x : X, ‖x‖ ≤ R → ∀ n ∉ S, f (x+ip n)=0 := by
  classical
  obtain ⟨B,hB⟩ := hf.isBounded.exists_norm_le
  obtain ⟨M,hM⟩ := exists_nat_gt (B+R)
  refine ⟨Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(M : ℤ)) M), ?_⟩
  intro x hx n hn
  by_contra ha
  apply hn
  rw [Fintype.mem_piFinset]
  intro i
  have hv := hB (x+ip n) (subset_tsupport f ha)
  have hi : |(n i : ℝ)| ≤ B+R := by
    calc
      |(n i : ℝ)| = ‖(x+ip n) i-x i‖ := by simp [ip]
      _ ≤ ‖(x+ip n) i‖+‖x i‖ := norm_sub_le _ _
      _ ≤ ‖x+ip n‖+‖x‖ := add_le_add (norm_le_pi_norm _ i) (norm_le_pi_norm _ i)
      _ ≤ B+R := add_le_add hv hx
  have hh := abs_le.mp (hi.trans hM.le)
  simpa only [Finset.mem_Icc, ← Int.cast_le (R := ℝ), Int.cast_neg, Int.cast_natCast] using hh

private lemma per_continuous {f : X → ℂ} (hc : Continuous f) (hf : HasCompactSupport f) :
    Continuous (per f) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨S,hS⟩ := finite_translates hf (‖x‖+1)
  have he : per f =ᶠ[𝓝 x] (fun y => ∑ n ∈ S, f (y+ip n)) := by
    filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
    apply tsum_eq_sum
    apply hS y
    have ht : ‖y‖ ≤ ‖y-x‖+‖x‖ := by
      calc ‖y‖ = ‖(y-x)+x‖ := by rw [sub_add_cancel]
           _ ≤ ‖y-x‖+‖x‖ := norm_add_le _ _
    have hd : ‖y-x‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
    linarith
  have hcon : Continuous (fun y => ∑ n ∈ S, f (y+ip n)) :=
    continuous_finsetSum S (fun n _ => hc.comp (continuous_id.add continuous_const))
  exact hcon.continuousAt.congr_of_eventuallyEq he

private lemma per_add (f : X → ℂ) (x : X) (m : Z) : per f (x+ip m)=per f x := by
  unfold per
  have h (n : Z) : (x+ip m)+ip n = x+ip (m+n) := by ext i; simp [ip,add_assoc]
  simp_rw [h]
  exact (Equiv.addLeft m).tsum_eq (fun n : Z => f (x+ip n))

private lemma q_open : IsOpenQuotientMap q :=
  IsOpenQuotientMap.piMap (fun _ : Fin 3 => QuotientAddGroup.isOpenQuotientMap_mk)

private lemma fiber {x y : X} (h : q x=q y) : ∃ n : Z, x=y+ip n := by
  have hi (i : Fin 3) : ∃ n : ℤ, (n : ℝ)=x i-y i := by
    have hh := QuotientAddGroup.eq_iff_sub_mem.mp (congrFun h i)
    simpa only [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul, mul_one] using hh
  choose n hn using hi
  refine ⟨n, ?_⟩
  ext i
  simp only [Pi.add_apply,ip]
  linarith [hn i]

private def torusPer (f : X → ℂ) : T → ℂ := per f ∘ Function.surjInv q_open.surjective
private lemma torusPer_q (f : X → ℂ) (x : X) : torusPer f (q x)=per f x := by
  obtain ⟨n,hn⟩ := fiber (Function.surjInv_eq q_open.surjective (q x))
  change per f (Function.surjInv q_open.surjective (q x))=per f x
  rw [hn,per_add]

private lemma torusPer_continuous {f : X → ℂ} (hc : Continuous f) (hf : HasCompactSupport f) :
    Continuous (torusPer f) := by
  apply q_open.continuous_comp_iff.mp
  simpa only [Function.comp_def,torusPer_q] using per_continuous hc hf

local instance : AddAction Z X where
  vadd n x := ip n+x
  zero_vadd x := by
    change ip 0+x=x
    ext i
    simp [ip]
  add_vadd m n x := by
    change ip (m+n)+x=ip m+(ip n+x)
    ext i
    simp [ip,add_assoc]

local instance : MeasurableConstVAdd Z X where
  measurable_const_vadd n :=
    show Measurable (fun x : X => ip n+x) from
      (continuous_const.add continuous_id).measurable

local instance : VAddInvariantMeasure Z X volume where
  measure_preimage_vadd n s _ := measure_preimage_add volume (ip n) s

private def cube : Set X := {x | ∀ i, x i ∈ Ioc 0 1}
private lemma cube_measurable : MeasurableSet cube := by
  simpa only [cube,Set.pi,Set.mem_univ,forall_true_left] using
    (MeasurableSet.pi Set.countable_univ (fun (_ : Fin 3) _ => measurableSet_Ioc (a := (0 : ℝ)) (b := 1)))

private lemma cube_fundamental : IsAddFundamentalDomain Z cube (volume : Measure X) := by
  apply IsAddFundamentalDomain.mk' cube_measurable.nullMeasurableSet
  intro x
  refine ⟨fun i => 1-Int.ceil (x i), ?_, ?_⟩
  · intro i
    change 0 < ((1-Int.ceil (x i) : ℤ) : ℝ)+x i ∧
      ((1-Int.ceil (x i) : ℤ) : ℝ)+x i ≤ 1
    push_cast
    constructor
    · linarith [Int.ceil_lt_add_one (x i)]
    · linarith [Int.le_ceil (x i)]
  · intro n hn
    ext i
    have hh := hn i
    change 0 < (n i : ℝ)+x i ∧ (n i : ℝ)+x i ≤ 1 at hh
    have hc : Int.ceil (x i) = 1-n i := Int.ceil_eq_iff.mpr (by
      push_cast
      constructor <;> linarith [hh.1,hh.2])
    omega

private lemma cube_norm {x : X} (hx : x ∈ cube) : ‖x‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [(hx i).1], (hx i).2⟩

private lemma integral_per {f : X → ℂ} (hc : Continuous f) (hf : HasCompactSupport f) :
    (∫ x in cube, per f x) = ∫ x, f x := by
  classical
  obtain ⟨S,hS⟩ := finite_translates hf 1
  have he (x : X) (hx : x ∈ cube) : per f x=∑ n ∈ S, f (x+ip n) :=
    tsum_eq_sum (hS x (cube_norm hx))
  rw [setIntegral_congr_fun cube_measurable he]
  rw [integral_finsetSum S]
  · rw [cube_fundamental.integral_eq_tsum'' f (hc.integrable_of_hasCompactSupport hf)]
    calc
      _ = ∑' n : Z, ∫ x in cube, f (x+ip n) := by
        symm
        apply tsum_eq_sum
        intro n hn
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro x hx
        exact hS x (cube_norm hx) n hn
      _ = _ := by
        apply tsum_congr
        intro n
        apply integral_congr_ae
        filter_upwards [] with x
        change f (x+ip n)=f (ip n+x)
        rw [add_comm]
  · intro n hn
    apply ((hc.comp (continuous_id.add continuous_const)).integrableOn_Icc
      (a := (0 : X)) (b := (1 : X))).mono_set
    intro x hx
    exact ⟨fun i => (hx i).1.le,fun i => (hx i).2⟩

private lemma q_add_ip (x : X) (n : Z) : q (x+ip n)=q x := by
  ext i
  change ((x i+(n i : ℝ) : ℝ) : UnitAddCircle)=(x i : UnitAddCircle)
  simp

private lemma per_character (f : X → ℂ) (k : Z) (x : X) :
    per (fun y => UnitAddTorus.mFourier (-k) (q y)*f y) x =
    UnitAddTorus.mFourier (-k) (q x)*per f x := by
  unfold per
  simp only [q_add_ip]
  exact tsum_mul_left

private lemma coefficient {f : X → ℂ} (hc : Continuous f) (hf : HasCompactSupport f) (k : Z) :
    UnitAddTorus.mFourierCoeff (torusPer f) k =
      ∫ x, UnitAddTorus.mFourier (-k) (q x)*f x := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral (torusPer f) k 0]
  have hh : Continuous (fun x => UnitAddTorus.mFourier (-k) (q x)*f x) :=
    ((UnitAddTorus.mFourier (-k)).continuous.comp q_open.continuous).mul hc
  have hs : HasCompactSupport (fun x => UnitAddTorus.mFourier (-k) (q x)*f x) :=
    hf.mul_left
  rw [← integral_per hh hs]
  simp only [Pi.zero_apply,zero_add]
  apply setIntegral_congr_fun cube_measurable
  intro x hx
  change UnitAddTorus.mFourier (-k) (q x)*torusPer f (q x) = _
  rw [torusPer_q,per_character]

/-- Every lattice point and Fourier coefficient is retained. -/
theorem poisson {f : X → ℂ} (hc : Continuous f) (hf : HasCompactSupport f)
    (hs : Summable (fun k : Z => ∫ x, UnitAddTorus.mFourier (-k) (q x)*f x)) :
    (∑' k : Z, ∫ x, UnitAddTorus.mFourier (-k) (q x)*f x) = ∑' n : Z, f (ip n) := by
  let F : C(T,ℂ) := ⟨torusPer f,torusPer_continuous hc hf⟩
  have hcoef : UnitAddTorus.mFourierCoeff F =
      (fun k : Z => ∫ x, UnitAddTorus.mFourier (-k) (q x)*f x) := by
    funext k
    exact coefficient hc hf k
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (f := F) (hcoef ▸ hs) (q 0)
  change HasSum (fun k => UnitAddTorus.mFourierCoeff (torusPer f) k •
    UnitAddTorus.mFourier k (q 0)) (torusPer f (q 0)) at h
  have hz (k : Z) : UnitAddTorus.mFourier k (q 0)=1 := by
    simp [UnitAddTorus.mFourier,q]
  simpa only [coefficient hc hf,hz,smul_eq_mul,mul_one,torusPer_q,per,zero_add]
    using h.tsum_eq


private def Normal (f : X → ℂ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∃ u : Z → ℝ, Summable u ∧
    ∀ x : X, ‖x‖ ≤ R → ∀ n : Z, ‖f (x+ip n)‖ ≤ u n

private lemma per_continuous_normal {f : X → ℂ} (hc : Continuous f) (hn : Normal f) :
    Continuous (per f) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨u,hu,hb⟩ := hn (‖x‖+1) (by positivity)
  have hs : ContinuousOn (per f) (Metric.ball (0 : X) (‖x‖+1)) :=
    continuousOn_tsum (fun n => (hc.comp (continuous_id.add continuous_const)).continuousOn)
      hu (fun n y hy => hb y
        (le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hy)) n)
  apply hs.continuousAt
  exact Metric.isOpen_ball.mem_nhds (by simp)

private lemma cube_finite : (volume : Measure X) cube < ⊤ := by
  apply (measure_mono (show cube ⊆ Metric.closedBall (0 : X) 1 from
    fun x hx => by simpa only [Metric.mem_closedBall,dist_zero_right] using cube_norm hx)).trans_lt
  exact (isCompact_closedBall (0 : X) 1).measure_lt_top

private lemma integral_per_normal {f : X → ℂ} (hc : Continuous f)
    (hf : Integrable f) (hn : Normal f) :
    (∫ x in cube, per f x) = ∫ x, f x := by
  letI : IsFiniteMeasure ((volume : Measure X).restrict cube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using cube_finite⟩
  have hi (n : Z) : IntegrableOn (fun x => f (x+ip n)) cube := by
    apply ((hc.comp (continuous_id.add continuous_const)).integrableOn_Icc
      (a := (0 : X)) (b := (1 : X))).mono_set
    intro x hx
    exact ⟨fun i => (hx i).1.le,fun i => (hx i).2⟩
  obtain ⟨u,hu,hb⟩ := hn 1 zero_le_one
  have hs : Summable (fun n : Z => ∫ x in cube, ‖f (x+ip n)‖) := by
    apply Summable.of_nonneg_of_le
      (g := fun n : Z => ∫ x in cube, ‖f (x+ip n)‖)
      (f := fun n => u n*((volume : Measure X).restrict cube).real univ)
      (fun n => integral_nonneg (fun x => norm_nonneg _)) _
      (hu.mul_right _)
    intro n
    have h := integral_mono_ae (hi n).norm (integrable_const (u n))
      (by filter_upwards [ae_restrict_mem cube_measurable] with x hx; exact hb x (cube_norm hx) n)
    simpa only [integral_const,smul_eq_mul,mul_comm] using h
  change (∫ x in cube, ∑' n : Z, f (x+ip n)) = _
  rw [← integral_tsum_of_summable_integral_norm hi hs,
    cube_fundamental.integral_eq_tsum'' f hf]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  filter_upwards [] with x
  change f (x+ip n)=f (ip n+x)
  rw [add_comm]

private lemma char_norm (k : Z) (x : X) : ‖UnitAddTorus.mFourier (-k) (q x)‖ ≤ 1 := by
  simpa only [UnitAddTorus.mFourier_norm] using (UnitAddTorus.mFourier (-k)).norm_coe_le_norm (q x)

private lemma coefficient_normal {f : X → ℂ} (hc : Continuous f)
    (hf : Integrable f) (hn : Normal f) (k : Z) :
    UnitAddTorus.mFourierCoeff (torusPer f) k =
      ∫ x, UnitAddTorus.mFourier (-k) (q x)*f x := by
  let g := fun x => UnitAddTorus.mFourier (-k) (q x)*f x
  have hg : Continuous g := ((UnitAddTorus.mFourier (-k)).continuous.comp q_open.continuous).mul hc
  have hb (x : X) : ‖g x‖ ≤ ‖f x‖ := by
    dsimp only [g]
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (char_norm k x) (norm_nonneg (f x))
  have hi : Integrable g := hf.mono hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hn' : Normal g := by
    intro R hR
    obtain ⟨u,hu,hb'⟩ := hn R hR
    exact ⟨u,hu,fun x hx n => (hb _).trans (hb' x hx n)⟩
  rw [UnitAddTorus.mFourierCoeff_eq_integral (torusPer f) k 0,
    ← integral_per_normal hg hi hn']
  simp only [Pi.zero_apply,zero_add]
  apply setIntegral_congr_fun cube_measurable
  intro x hx
  change UnitAddTorus.mFourier (-k) (q x)*torusPer f (q x) = per g x
  rw [torusPer_q,per_character]

/-- Full three-dimensional Poisson matching under absolute normal
periodization. The consuming Schwartz theorem proves all conditions;
no compact physical support is required here. -/
theorem poisson_of_summable_translates {f : X → ℂ} (hc : Continuous f) (hf : Integrable f)
    (hn : ∀ R : ℝ, 0 ≤ R → ∃ u : Z → ℝ, Summable u ∧
      ∀ x : X, ‖x‖ ≤ R → ∀ n : Z, ‖f (x+ip n)‖ ≤ u n)
    (hs : Summable (fun k : Z => ∫ x, UnitAddTorus.mFourier (-k) (q x)*f x)) :
    (∑' k : Z, ∫ x, UnitAddTorus.mFourier (-k) (q x)*f x) = ∑' n : Z, f (ip n) := by
  have ht : Continuous (torusPer f) := by
    apply q_open.continuous_comp_iff.mp
    simpa only [Function.comp_def,torusPer_q] using per_continuous_normal hc hn
  let F : C(T,ℂ) := ⟨torusPer f,ht⟩
  have hcoef : UnitAddTorus.mFourierCoeff F =
      (fun k : Z => ∫ x, UnitAddTorus.mFourier (-k) (q x)*f x) := by
    funext k
    exact coefficient_normal hc hf hn k
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (f := F) (hcoef ▸ hs) (q 0)
  change HasSum (fun k => UnitAddTorus.mFourierCoeff (torusPer f) k •
    UnitAddTorus.mFourier k (q 0)) (torusPer f (q 0)) at h
  have hz (k : Z) : UnitAddTorus.mFourier k (q 0)=1 := by
    simp [UnitAddTorus.mFourier,q]
  simpa only [coefficient_normal hc hf hn,hz,smul_eq_mul,mul_one,torusPer_q,per,zero_add]
    using h.tsum_eq

end FullPoisson
end RHTower.BAGTrace
