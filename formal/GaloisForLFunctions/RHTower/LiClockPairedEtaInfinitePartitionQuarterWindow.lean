import GaloisForLFunctions.RHTower.LiClockPairedEtaInfinitePartitionBorel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

noncomputable section
open MeasureTheory Filter Set Topology
namespace RHTower

def liClockPairedEtaInfinitePartitionQuarterDelta (c : ℝ) : ℝ := 1/2-Real.sqrt c

def liClockPairedEtaInfinitePartitionQuarterRate (c : ℝ) : ℝ := (1-2*Real.sqrt c)^2/2

def liClockPairedEtaInfinitePartitionQuarterWindowError (c : ℝ) (N : ℕ) : ℝ :=
  (2/(2-Real.sqrt 2)^2)*(Real.log (2*(N:ℝ))+1/liClockPairedEtaInfinitePartitionQuarterDelta c)*
    Real.exp (-liClockPairedEtaInfinitePartitionQuarterRate c*Real.log (2*(N:ℝ)))+
  (32/(2-Real.sqrt 2)^4)*Real.exp (-Real.log (2*(N:ℝ))/2)

theorem liClockPairedEtaInfinitePartitionQuarterDelta_pos {c : ℝ}
    (hc0 : 0≤c) (hc : c<1/4) : 0<liClockPairedEtaInfinitePartitionQuarterDelta c := by
  have hs := (Real.sqrt_lt hc0 (by norm_num : (0:ℝ)≤1/2)).mpr (by nlinarith : c<(1/2:ℝ)^2)
  unfold liClockPairedEtaInfinitePartitionQuarterDelta
  linarith

theorem liClockPairedEtaInfinitePartitionQuarterRate_pos {c : ℝ}
    (hc0 : 0≤c) (hc : c<1/4) : 0<liClockPairedEtaInfinitePartitionQuarterRate c := by
  have hd := liClockPairedEtaInfinitePartitionQuarterDelta_pos hc0 hc
  unfold liClockPairedEtaInfinitePartitionQuarterDelta at hd
  unfold liClockPairedEtaInfinitePartitionQuarterRate
  exact div_pos (sq_pos_of_pos (by linarith)) (by norm_num)

private theorem quarter_log_pos {N : ℕ} (hN : 0<N) : 0<Real.log (2*(N:ℝ)) := by
  apply Real.log_pos
  have hN1 : 1≤N := by omega
  have hNreal : (1:ℝ)≤N := by exact_mod_cast hN1
  linarith

theorem liClockPairedEtaInfinitePartitionQuarterWindowError_nonneg {c : ℝ}
    (hc0 : 0≤c) (hc : c<1/4) {N : ℕ} (hN : 0<N) :
    0≤liClockPairedEtaInfinitePartitionQuarterWindowError c N := by
  have hd := liClockPairedEtaInfinitePartitionQuarterDelta_pos hc0 hc
  have hL := quarter_log_pos hN
  unfold liClockPairedEtaInfinitePartitionQuarterWindowError
  positivity

private theorem quarter_log_tendsto :
    Tendsto (fun N:ℕ=>Real.log (2*(N:ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))

theorem tendsto_liClockPairedEtaInfinitePartitionQuarterWindowError_zero {c : ℝ}
    (hc0 : 0≤c) (hc : c<1/4) :
    Tendsto (liClockPairedEtaInfinitePartitionQuarterWindowError c) atTop (𝓝 0) := by
  have hd := liClockPairedEtaInfinitePartitionQuarterDelta_pos hc0 hc
  have hη := liClockPairedEtaInfinitePartitionQuarterRate_pos hc0 hc
  have ht : Tendsto (fun L:ℝ=>L*Real.exp (-liClockPairedEtaInfinitePartitionQuarterRate c*L)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 _ hη
  have he : Tendsto (fun L:ℝ=>Real.exp (-liClockPairedEtaInfinitePartitionQuarterRate c*L)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have ha : Tendsto (fun L:ℝ=>Real.exp (-L/2)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1/2:ℝ)<0))
    exact h.congr (fun L=>by dsimp only [Function.comp_def,id_eq];congr 1;ring)
  have h := ((ht.add (he.const_mul (1/liClockPairedEtaInfinitePartitionQuarterDelta c))).const_mul
    (2/(2-Real.sqrt 2)^2)).add (ha.const_mul (32/(2-Real.sqrt 2)^4))
  simp only [mul_zero,add_zero] at h
  exact (h.comp quarter_log_tendsto).congr (fun N=>by
    dsimp only [Function.comp_def]
    unfold liClockPairedEtaInfinitePartitionQuarterWindowError
    ring)

end RHTower

namespace RHTower

private theorem quarter_edge_exponent {c τ L : ℝ}
    (hc0 : 0 ≤ c) (hc : c < 1/4) (hτ0 : 0 ≤ τ) (hL : 0 < L)
    (hτ : τ ≤ c*L) :
    -L/2 + 2*Real.sqrt (τ*L) - 2*τ ≤ -((1-2*Real.sqrt c)^2/2)*L := by
  have ha : Real.sqrt c < 1/2 :=
    (Real.sqrt_lt hc0 (by norm_num : (0:ℝ) ≤ 1/2)).mpr (by nlinarith)
  have hp := Real.sqrt_le_sqrt hτ
  rw [Real.sqrt_mul hc0] at hp
  have hlow : 0 ≤ (1-2*Real.sqrt c)*Real.sqrt L :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg L)
  have horder : (1-2*Real.sqrt c)*Real.sqrt L ≤ Real.sqrt L-2*Real.sqrt τ := by
    nlinarith
  have hs : ((1-2*Real.sqrt c)*Real.sqrt L)^2 ≤ (Real.sqrt L-2*Real.sqrt τ)^2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr horder)
      (show 0 ≤ (Real.sqrt L-2*Real.sqrt τ)+(1-2*Real.sqrt c)*Real.sqrt L by linarith)
    nlinarith
  calc
    _ = -(Real.sqrt L-2*Real.sqrt τ)^2/2 := by
      rw [Real.sqrt_mul hτ0]
      nlinarith [Real.sq_sqrt hL.le,Real.sq_sqrt hτ0]
    _ ≤ -((1-2*Real.sqrt c)*Real.sqrt L)^2/2 := by linarith
    _ = _ := by rw [mul_pow,Real.sq_sqrt hL.le]; ring

private theorem quarter_inner_exponent {c τ L r : ℝ}
    (hc0 : 0 ≤ c) (hc : c < 1/4) (hτ0 : 0 ≤ τ) (hL : 0 < L)
    (hτ : τ ≤ c*L) (_hr0 : 0 ≤ r) (hr : r ≤ L) :
    r/2-L + 2*Real.sqrt (τ*r) - 2*τ ≤ -((1-2*Real.sqrt c)^2/2)*L := by
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hr hτ0)
  have he := quarter_edge_exponent hc0 hc hτ0 hL hτ
  linarith

private theorem quarter_outer_exponent {c τ L r : ℝ}
    (hc0 : 0 ≤ c) (hc : c < 1/4) (hτ0 : 0 ≤ τ) (hL : 0 < L)
    (hτ : τ ≤ c*L) (hr : L ≤ r) :
    -r/2 + 2*Real.sqrt (τ*r) - 2*τ ≤
      -((1-2*Real.sqrt c)^2/2)*L-(1/2-Real.sqrt c)*(r-L) := by
  have hr0 : 0 ≤ r := hL.le.trans hr
  have hq := Real.sqrt_le_sqrt hr
  have hp := Real.sqrt_le_sqrt hτ
  rw [Real.sqrt_mul hc0] at hp
  have hcoef : 2*Real.sqrt τ ≤ Real.sqrt c*(Real.sqrt r+Real.sqrt L) := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg c) (sub_nonneg.mpr hq)]
  have hm := mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hq)
  have hid : Real.sqrt c*(Real.sqrt r+Real.sqrt L)*(Real.sqrt r-Real.sqrt L)=
      Real.sqrt c*(r-L) := by
    calc
      _ = Real.sqrt c*((Real.sqrt r)^2-(Real.sqrt L)^2) := by ring
      _ = _ := by rw [Real.sq_sqrt hr0,Real.sq_sqrt hL.le]
  rw [hid] at hm
  have he := quarter_edge_exponent hc0 hc hτ0 hL hτ
  rw [Real.sqrt_mul hτ0] at he ⊢
  nlinarith

end RHTower

namespace RHTower

private theorem quarter_integrable_abs_exp {κ : ℝ} (hκ : 0<κ) :
    Integrable (fun x:ℝ=>Real.exp (-κ*|x|)) := by
  have hpos : IntegrableOn (fun x:ℝ=>Real.exp (-κ*|x|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (a:=-κ) (by linarith) 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [abs_of_pos hx]
  have hneg : IntegrableOn (fun x:ℝ=>Real.exp (-κ*|x|)) (Iic 0) := by
    rw [←Measure.map_neg_eq_self (volume:Measure ℝ)]
    let hM : MeasurableEmbedding (fun x:ℝ=>-x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [hM.integrableOn_map_iff]
    simp_rw [Function.comp_def,abs_neg,neg_preimage,neg_Iic,neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  simpa only [Iic_union_Ioi,integrableOn_univ] using hneg.union hpos

private theorem quarter_integrable_max_exp {κ : ℝ} (hκ : 0<κ) (L : ℝ) :
    Integrable (fun x:ℝ=>Real.exp (-κ*max L |x|)) := by
  have hm : Measurable (fun x:ℝ=>Real.exp (-κ*max L |x|)) := by fun_prop
  refine (quarter_integrable_abs_exp hκ).mono' hm.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (le_max_right L |x|) (by linarith)

private theorem quarter_integral_max_exp {κ L : ℝ} (hκ : 0<κ) (hL : 0≤L) :
    (∫x:ℝ,Real.exp (-κ*max L |x|))=2*(L+1/κ)*Real.exp (-κ*L) := by
  have habs : (∫x:ℝ,Real.exp (-κ*max L |x|))=
      2*(∫x:ℝ in Ioi 0,Real.exp (-κ*max L x)) :=
    integral_comp_abs (f:=fun x:ℝ=>Real.exp (-κ*max L x))
  rw [habs,←Ioc_union_Ioi_eq_Ioi hL]
  have hconst : IntegrableOn (fun x:ℝ=>Real.exp (-κ*L)) (Ioc 0 L) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have htail : IntegrableOn (fun x:ℝ=>Real.exp (-κ*x)) (Ioi L) := by
    simpa only [neg_mul] using integrableOn_exp_mul_Ioi (a:=-κ) (by linarith) L
  have ha : IntegrableOn (fun x:ℝ=>Real.exp (-κ*max L x)) (Ioc 0 L) := by
    apply hconst.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [max_eq_left hx.2]
  have hb : IntegrableOn (fun x:ℝ=>Real.exp (-κ*max L x)) (Ioi L) := by
    apply htail.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [max_eq_right hx.le]
  rw [setIntegral_union (by exact Set.disjoint_left.mpr (fun x hx hy=>not_lt_of_ge hx.2 hy)) measurableSet_Ioi ha hb]
  have hea : (∫x:ℝ in Ioc 0 L,Real.exp (-κ*max L x))=L*Real.exp (-κ*L) := by
    calc
      _ = ∫x:ℝ in Ioc 0 L,Real.exp (-κ*L) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx;dsimp only;rw [max_eq_left hx.2]
      _ = _ := by simp only [integral_const,measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le hL,sub_zero,smul_eq_mul]
  have heb : (∫x:ℝ in Ioi L,Real.exp (-κ*max L x))=Real.exp (-κ*L)/κ := by
    calc
      _ = ∫x:ℝ in Ioi L,Real.exp (-κ*x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx;dsimp only;rw [max_eq_right hx.le]
      _ = _ := by simpa only [neg_mul,neg_div_neg_eq] using integral_exp_mul_Ioi (a:=-κ) (by linarith) L
  rw [hea,heb]
  ring

private def quarter_scaledLoss (L τ x : ℝ) : ℝ :=
  (if |x|<L then Real.exp (|x|/2-L) else Real.exp (-|x|/2))*
    Real.exp (2*Real.sqrt (τ*|x|)-2*τ)

private theorem quarter_scaledLoss_nonneg (L τ x : ℝ) : 0≤quarter_scaledLoss L τ x := by
  unfold quarter_scaledLoss
  split_ifs <;> positivity

private theorem quarter_scaledLoss_le {c τ L : ℝ} (hc0 : 0≤c) (hc : c<1/4)
    (hτ0 : 0≤τ) (hL : 0<L) (hτ : τ≤c*L) (x : ℝ) :
    quarter_scaledLoss L τ x ≤
      Real.exp ((liClockPairedEtaInfinitePartitionQuarterDelta c-
        liClockPairedEtaInfinitePartitionQuarterRate c)*L)*
      Real.exp (-liClockPairedEtaInfinitePartitionQuarterDelta c*max L |x|) := by
  by_cases hx : |x|<L
  · calc
      _ = Real.exp (|x|/2-L+2*Real.sqrt (τ*|x|)-2*τ) := by
        rw [quarter_scaledLoss,if_pos hx,←Real.exp_add]
        congr 1;ring
      _ ≤ Real.exp (-liClockPairedEtaInfinitePartitionQuarterRate c*L) :=
        Real.exp_le_exp.mpr (quarter_inner_exponent hc0 hc hτ0 hL hτ (abs_nonneg x) hx.le)
      _ = _ := by
        rw [max_eq_left hx.le,←Real.exp_add]
        congr 1;ring
  · have hxL : L≤|x| := le_of_not_gt hx
    calc
      _ = Real.exp (-|x|/2+2*Real.sqrt (τ*|x|)-2*τ) := by
        rw [quarter_scaledLoss,if_neg hx,←Real.exp_add]
        congr 1;ring
      _ ≤ Real.exp (-liClockPairedEtaInfinitePartitionQuarterRate c*L-
          liClockPairedEtaInfinitePartitionQuarterDelta c*(|x|-L)) :=
        Real.exp_le_exp.mpr (quarter_outer_exponent hc0 hc hτ0 hL hτ hxL)
      _ = _ := by
        rw [max_eq_right hxL,←Real.exp_add]
        congr 1;ring

private theorem quarter_integrable_scaledLoss {c τ L : ℝ} (hc0 : 0≤c) (hc : c<1/4)
    (hτ0 : 0≤τ) (hL : 0<L) (hτ : τ≤c*L) :
    Integrable (quarter_scaledLoss L τ) := by
  have hd := liClockPairedEtaInfinitePartitionQuarterDelta_pos hc0 hc
  have hm : Measurable (quarter_scaledLoss L τ) := by
    unfold quarter_scaledLoss
    exact (Measurable.ite (isOpen_lt continuous_abs continuous_const).measurableSet
      (by fun_prop) (by fun_prop)).mul (by fun_prop)
  refine ((quarter_integrable_max_exp hd L).const_mul
    (Real.exp ((liClockPairedEtaInfinitePartitionQuarterDelta c-
      liClockPairedEtaInfinitePartitionQuarterRate c)*L))).mono' hm.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (quarter_scaledLoss_nonneg L τ x)]
  exact quarter_scaledLoss_le hc0 hc hτ0 hL hτ x

private theorem quarter_integral_scaledLoss_le {c τ L : ℝ} (hc0 : 0≤c) (hc : c<1/4)
    (hτ0 : 0≤τ) (hL : 0<L) (hτ : τ≤c*L) :
    (∫x:ℝ,quarter_scaledLoss L τ x) ≤
      2*(L+1/liClockPairedEtaInfinitePartitionQuarterDelta c)*
      Real.exp (-liClockPairedEtaInfinitePartitionQuarterRate c*L) := by
  have hd := liClockPairedEtaInfinitePartitionQuarterDelta_pos hc0 hc
  have hi := quarter_integrable_scaledLoss hc0 hc hτ0 hL hτ
  have hmaj := (quarter_integrable_max_exp hd L).const_mul
    (Real.exp ((liClockPairedEtaInfinitePartitionQuarterDelta c-
      liClockPairedEtaInfinitePartitionQuarterRate c)*L))
  calc
    _ ≤ ∫x:ℝ,Real.exp ((liClockPairedEtaInfinitePartitionQuarterDelta c-
        liClockPairedEtaInfinitePartitionQuarterRate c)*L)*
        Real.exp (-liClockPairedEtaInfinitePartitionQuarterDelta c*max L |x|) :=
      integral_mono_ae hi hmaj (Eventually.of_forall (quarter_scaledLoss_le hc0 hc hτ0 hL hτ))
    _ = _ := by
      rw [integral_const_mul,quarter_integral_max_exp hd hL.le]
      rw [show Real.exp ((liClockPairedEtaInfinitePartitionQuarterDelta c-
          liClockPairedEtaInfinitePartitionQuarterRate c)*L)*
          (2*(L+1/liClockPairedEtaInfinitePartitionQuarterDelta c)*
            Real.exp (-liClockPairedEtaInfinitePartitionQuarterDelta c*L))=
        2*(L+1/liClockPairedEtaInfinitePartitionQuarterDelta c)*
          (Real.exp ((liClockPairedEtaInfinitePartitionQuarterDelta c-
              liClockPairedEtaInfinitePartitionQuarterRate c)*L)*
            Real.exp (-liClockPairedEtaInfinitePartitionQuarterDelta c*L)) by ring,
        ←Real.exp_add]
      congr 1
      congr 1
      ring

end RHTower

namespace RHTower

private theorem quarter_weighted_cap {c τ L U V : ℝ}
    (hraw : Real.exp (-2*τ)*U ≤
      2*(L+1/liClockPairedEtaInfinitePartitionQuarterDelta c)*
        Real.exp (-liClockPairedEtaInfinitePartitionQuarterRate c*L))
    (hcap : V ≤ U/(2-Real.sqrt 2)^2+
      (32/(2-Real.sqrt 2)^4)*Real.exp (-L/2+2*τ)) :
    Real.exp (-2*τ)*V ≤
      (2/(2-Real.sqrt 2)^2)*(L+1/liClockPairedEtaInfinitePartitionQuarterDelta c)*
        Real.exp (-liClockPairedEtaInfinitePartitionQuarterRate c*L)+
      (32/(2-Real.sqrt 2)^4)*Real.exp (-L/2) := by
  have he : Real.exp (-2*τ)*Real.exp (-L/2+2*τ)=Real.exp (-L/2) := by
    rw [←Real.exp_add]
    congr 1;ring
  calc
    _ ≤ Real.exp (-2*τ)*(U/(2-Real.sqrt 2)^2+
        (32/(2-Real.sqrt 2)^4)*Real.exp (-L/2+2*τ)) :=
      mul_le_mul_of_nonneg_left hcap (Real.exp_pos _).le
    _ = (Real.exp (-2*τ)*U)/(2-Real.sqrt 2)^2+
        (32/(2-Real.sqrt 2)^4)*Real.exp (-L/2) := by
      rw [show Real.exp (-2*τ)*(U/(2-Real.sqrt 2)^2+
        (32/(2-Real.sqrt 2)^4)*Real.exp (-L/2+2*τ))=
        (Real.exp (-2*τ)*U)/(2-Real.sqrt 2)^2+
        (32/(2-Real.sqrt 2)^4)*(Real.exp (-2*τ)*Real.exp (-L/2+2*τ)) by ring,he]
    _ ≤ _ := by
      apply add_le_add
      · exact (div_le_div_of_nonneg_right hraw (sq_nonneg _)).trans_eq (by ring)
      · exact le_rfl


theorem liClockPairedEtaInfinitePartitionQuarterWindow_inner_exponent {c τ L r : ℝ}
    (hc0 : 0≤c) (hc : c<1/4) (hτ0 : 0≤τ) (hL : 0<L)
    (hτ : τ≤c*L) (hr0 : 0≤r) (hr : r≤L) :
    r/2-L+2*Real.sqrt (τ*r)-2*τ ≤ -liClockPairedEtaInfinitePartitionQuarterRate c*L :=
  quarter_inner_exponent hc0 hc hτ0 hL hτ hr0 hr

theorem liClockPairedEtaInfinitePartitionQuarterWindow_outer_exponent {c τ L r : ℝ}
    (hc0 : 0≤c) (hc : c<1/4) (hτ0 : 0≤τ) (hL : 0<L)
    (hτ : τ≤c*L) (hr : L≤r) :
    -r/2+2*Real.sqrt (τ*r)-2*τ ≤ -liClockPairedEtaInfinitePartitionQuarterRate c*L-
      liClockPairedEtaInfinitePartitionQuarterDelta c*(r-L) :=
  quarter_outer_exponent hc0 hc hτ0 hL hτ hr

end RHTower

open Filter Topology
namespace RHTower

private theorem quarter_weighted_perturbation
    {f g t : ℕ → ℝ} {a : ℝ}
    (herr : Tendsto (fun n => Real.exp (-2*t n)*|f n-g n|) atTop (𝓝 0))
    (hg : Tendsto (fun n => Real.exp (-2*t n)*g n) atTop (𝓝 a)) :
    Tendsto (fun n => Real.exp (-2*t n)*f n) atTop (𝓝 a) := by
  have hz : Tendsto (fun n => Real.exp (-2*t n)*(f n-g n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ herr
    filter_upwards with n
    simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact le_rfl
  have h := hz.add hg
  simp only [zero_add] at h
  exact h.congr (fun n => by ring)

private theorem quarter_scaled_ratio
    {A U t : ℕ → ℝ} {a b : ℝ}
    (ha : Tendsto (fun n => Real.exp (-2 * t n) * A n) atTop (𝓝 a))
    (hb : Tendsto (fun n => Real.exp (-2 * t n) * U n) atTop (𝓝 b))
    (hb0 : b ≠ 0) :
    Tendsto (fun n => A n / U n) atTop (𝓝 (a / b)) := by
  exact (ha.div hb hb0).congr (fun n =>
    mul_div_mul_left (A n) (U n) (Real.exp_ne_zero _))

private theorem quarter_negative_gap
    {A U t : ℕ → ℝ} {a b : ℝ}
    (ht : Tendsto t atTop atTop)
    (ha : Tendsto (fun n => Real.exp (-2 * t n) * A n) atTop (𝓝 a))
    (hb : Tendsto (fun n => Real.exp (-2 * t n) * U n) atTop (𝓝 b))
    (hab : a < b) :
    Tendsto (fun n => A n - U n) atTop atBot := by
  have hd : Tendsto (fun n => Real.exp (-2 * t n) * (A n - U n)) atTop
      (𝓝 (a - b)) := (ha.sub hb).congr (fun n => by ring)
  have he : Tendsto (fun n => Real.exp (2 * t n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (ht.const_mul_atTop (by norm_num))
  exact (he.atTop_mul_neg (sub_neg.mpr hab) hd).congr (fun n => by
    rw [← mul_assoc, ← Real.exp_add]
    have hx : 2 * t n + -2 * t n = 0 := by ring
    rw [hx]
    simp)

private theorem quarter_qualified_limits
    {A U Ainf Uinf t : ℕ → ℝ} {ell : ℝ}
    (ht : Tendsto t atTop atTop)
    (hAerr : Tendsto (fun n => Real.exp (-2*t n)*|A n-Ainf n|) atTop (𝓝 0))
    (hUerr : Tendsto (fun n => Real.exp (-2*t n)*|U n-Uinf n|) atTop (𝓝 0))
    (hAinf : Tendsto (fun n => Real.exp (-2*t n)*Ainf n) atTop (𝓝 (ell/2)))
    (hUinf : Tendsto (fun n => Real.exp (-2*t n)*Uinf n) atTop (𝓝 (1/2)))
    (hlimit : ell < 1) :
    Tendsto (fun n => Real.exp (-2*t n)*A n) atTop (𝓝 (ell/2)) ∧
    Tendsto (fun n => Real.exp (-2*t n)*U n) atTop (𝓝 (1/2)) ∧
    Tendsto (fun n => A n/U n) atTop (𝓝 ell) ∧
    Tendsto (fun n => A n-U n) atTop atBot := by
  have ha := quarter_weighted_perturbation hAerr hAinf
  have hu := quarter_weighted_perturbation hUerr hUinf
  have hr := quarter_scaled_ratio ha hu (by norm_num : (1/2:ℝ) ≠ 0)
  have hconst : (ell/2)/(1/2)=ell := by ring
  rw [hconst] at hr
  exact ⟨ha,hu,hr,quarter_negative_gap ht ha hu (by linarith)⟩

private theorem quarter_uniform_negative_gap
    {A U : ℕ → ℝ → ℝ} {Ainf Uinf : ℝ → ℝ} {E W : ℕ → ℝ} {a : ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hA : ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ W n →
      Real.exp (-2*t)*|A n t-Ainf t| ≤ E n)
    (hU : ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ W n →
      Real.exp (-2*t)*|U n t-Uinf t| ≤ E n)
    (hgap : Tendsto (fun t => Real.exp (-2*t)*(Ainf t-Uinf t)) atTop (𝓝 a))
    (ha : a < 0) :
    ∃ T : ℝ, 0 < T ∧
      ∀ᶠ n in atTop, ∀ t : ℝ, T ≤ t → t ≤ W n → A n t-U n t ≤ -(1/2) := by
  have hsource : ∀ᶠ t in atTop, Real.exp (-2*t)*(Ainf t-Uinf t) ≤ a/2 := by
    filter_upwards [hgap.eventually (gt_mem_nhds (by linarith : a < a/2))] with t ht
    exact ht.le
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp hsource
  have he : Tendsto (fun t:ℝ => Real.exp (2*t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
  obtain ⟨T₂,hT₂⟩ := eventually_atTop.mp (he.eventually (eventually_ge_atTop (-(2/a))))
  have hsmall := hE.eventually (gt_mem_nhds (by linarith : (0:ℝ) < -a/8))
  refine ⟨max (max T₁ T₂) 1, ?_, ?_⟩
  · have h := le_max_right (max T₁ T₂) (1:ℝ)
    linarith
  · filter_upwards [hsmall,hA,hU] with n hn hAn hUn
    intro t ht hw
    have hbase : max T₁ T₂ ≤ t := (le_max_left _ _).trans ht
    have ht0 : 0 ≤ t := by
      have h := (le_max_right (max T₁ T₂) (1:ℝ)).trans ht
      linarith
    have hfa := (mul_le_mul_of_nonneg_left (le_abs_self (A n t-Ainf t))
      (Real.exp_pos (-2*t)).le).trans (hAn t ht0 hw)
    have hfu := (mul_le_mul_of_nonneg_left (neg_le_abs (U n t-Uinf t))
      (Real.exp_pos (-2*t)).le).trans (hUn t ht0 hw)
    have hgt := hT₁ t ((le_max_left _ _).trans hbase)
    have hs : Real.exp (-2*t)*(A n t-U n t) ≤ a/4 := by
      nlinarith
    have hcancel : Real.exp (2*t)*(Real.exp (-2*t)*(A n t-U n t))=A n t-U n t := by
      rw [←mul_assoc,←Real.exp_add]
      have hzero : 2*t+ -2*t=0 := by ring
      rw [hzero]
      simp
    have hh := mul_le_mul_of_nonpos_right (hT₂ t ((le_max_right _ _).trans hbase))
      (by linarith : a/4 ≤ 0)
    have ha0 : a ≠ 0 := ha.ne
    have hconst : (-(2/a))*(a/4)=-(1/2:ℝ) := by field_simp; ring
    calc
      A n t-U n t = _ := hcancel.symm
      _ ≤ Real.exp (2*t)*(a/4) := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ ≤ -(1/2) := hh.trans_eq hconst

end RHTower

namespace RHTower

/-- Complete scaled raw truncation loss on the weighted quarter-window. -/
theorem liClockPairedEtaInfinitePartitionQuarterWindow_scaled_rawLossEnvelope_le
    {c : ℝ} (hc0 : 0≤c) (hc : c<1/4) {N : ℕ} (hN : 0<N) {z : ℂ}
    (hz : ‖z‖≤c*Real.log (2*(N:ℝ))) :
    Real.exp (-2*‖z‖)*liClockPairedEtaInfinitePartitionRawLossEnvelope N z ≤
      2*(Real.log (2*(N:ℝ))+1/liClockPairedEtaInfinitePartitionQuarterDelta c)*
        Real.exp (-liClockPairedEtaInfinitePartitionQuarterRate c*Real.log (2*(N:ℝ))) := by
  calc
    _ = ∫x:ℝ,quarter_scaledLoss (Real.log (2*(N:ℝ))) ‖z‖ x := by
      rw [liClockPairedEtaInfinitePartitionRawLossEnvelope,←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [liClockPairedEtaHalfLineRawDifferenceDensity_sub_contiguous]
      unfold quarter_scaledLoss
      rw [show Real.exp (2*Real.sqrt (‖z‖*|x|)-2*‖z‖)=
        Real.exp (2*Real.sqrt (‖z‖*|x|))*Real.exp (-2*‖z‖) by
          rw [←Real.exp_add];congr 1;ring]
      ring
    _ ≤ _ := quarter_integral_scaledLoss_le hc0 hc (norm_nonneg z) (quarter_log_pos hN) hz

/-- Full complex actual-source error, weighted by its literal clock magnitude. -/
theorem norm_liClockPairedEtaPartitionBorelKernelComplex_sub_infinite_quarterWindow_le
    {c : ℝ} (hc0 : 0≤c) (hc : c<1/4) {N : ℕ} (hN : 0<N) {z : ℂ}
    (hz : ‖z‖≤c*Real.log (2*(N:ℝ))) :
    Real.exp (-2*‖z‖)*‖liClockPairedEtaPartitionBorelKernelComplex N z-
      liClockPairedEtaInfinitePartitionBorelKernelComplex z‖ ≤
      liClockPairedEtaInfinitePartitionQuarterWindowError c N :=
  quarter_weighted_cap (liClockPairedEtaInfinitePartitionQuarterWindow_scaled_rawLossEnvelope_le hc0 hc hN hz)
    (norm_liClockPairedEtaPartitionBorelKernelComplex_sub_infinite_le_rawLossEnvelope hN z)

/-- Full complex reference error with its own finite and infinite normalizers. -/
theorem norm_liClockPairedEtaContiguousBorelKernelComplex_sub_halfLine_quarterWindow_le
    {c : ℝ} (hc0 : 0≤c) (hc : c<1/4) {N : ℕ} (hN : 0<N) {z : ℂ}
    (hz : ‖z‖≤c*Real.log (2*(N:ℝ))) :
    Real.exp (-2*‖z‖)*‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z-
      liClockPairedEtaHalfLineBorelKernelComplex z‖ ≤
      liClockPairedEtaInfinitePartitionQuarterWindowError c N :=
  quarter_weighted_cap (liClockPairedEtaInfinitePartitionQuarterWindow_scaled_rawLossEnvelope_le hc0 hc hN hz)
    (norm_liClockPairedEtaContiguousBorelKernelComplex_sub_halfLine_le_rawLossEnvelope hN z)

private theorem quarter_actual_real_error {c : ℝ} (hc0 : 0≤c) (hc : c<1/4)
    {N : ℕ} (hN : 0<N) {t : ℝ} (ht0 : 0≤t) (ht : t≤c*Real.log (2*(N:ℝ))) :
    Real.exp (-2*t)*|liClockPairedEtaPartitionBorelKernel N t-
      liClockPairedEtaInfinitePartitionBorelKernel t| ≤
      liClockPairedEtaInfinitePartitionQuarterWindowError c N := by
  have hz : ‖(t:ℂ)‖≤c*Real.log (2*(N:ℝ)) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0] using ht
  have h := norm_liClockPairedEtaPartitionBorelKernelComplex_sub_infinite_quarterWindow_le hc0 hc hN hz
  rw [liClockPairedEtaPartitionBorelKernelComplex_ofReal hN,
    liClockPairedEtaInfinitePartitionBorelKernelComplex_ofReal,←Complex.ofReal_sub] at h
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0] using h

private theorem quarter_reference_real_error {c : ℝ} (hc0 : 0≤c) (hc : c<1/4)
    {N : ℕ} (hN : 0<N) {t : ℝ} (ht0 : 0≤t) (ht : t≤c*Real.log (2*(N:ℝ))) :
    Real.exp (-2*t)*|liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t-
      liClockPairedEtaHalfLineBorelKernel t| ≤
      liClockPairedEtaInfinitePartitionQuarterWindowError c N := by
  have hz : ‖(t:ℂ)‖≤c*Real.log (2*(N:ℝ)) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0] using ht
  have h := norm_liClockPairedEtaContiguousBorelKernelComplex_sub_halfLine_quarterWindow_le hc0 hc hN hz
  rw [liClockPairedEtaContiguousBorelKernelComplex_ofReal (quarter_log_pos hN),
    liClockPairedEtaHalfLineBorelKernelComplex_ofReal,←Complex.ofReal_sub] at h
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0] using h

end RHTower

namespace RHTower

private theorem quarter_infinite_scaled_gap :
    Tendsto (fun t:ℝ=>Real.exp (-2*t)*(liClockPairedEtaInfinitePartitionBorelKernel t-
      liClockPairedEtaHalfLineBorelKernel t)) atTop
      (𝓝 ((liClockPairedEtaInfinitePartitionComparisonLimit-1)/2)) := by
  have h := tendsto_liClockPairedEtaHalfLineBorelKernel_sub_infinite_scaled.neg
  have he : -((1-liClockPairedEtaInfinitePartitionComparisonLimit)/2)=
      (liClockPairedEtaInfinitePartitionComparisonLimit-1)/2 := by ring
  rw [he] at h
  exact h.congr (fun t=>by ring)

private theorem quarter_reference_scaled_limit :
    Tendsto (fun t:ℝ=>Real.exp (-2*t)*liClockPairedEtaHalfLineBorelKernel t)
      atTop (𝓝 (1/2)) := by
  have h := tendsto_liClockPairedEtaHalfLineBorelKernel_sub_infinite_scaled.add
    tendsto_liClockPairedEtaInfinitePartitionBorelKernel_scaled
  have he : (1-liClockPairedEtaInfinitePartitionComparisonLimit)/2+
      liClockPairedEtaInfinitePartitionComparisonLimit/2=(1/2:ℝ) := by ring
  rw [he] at h
  exact h.congr (fun t=>by ring)

/-- All qualified real-clock limits on the weighted quarter-window. -/
theorem liClockPairedEtaInfinitePartitionQuarterWindow_joint
    {c : ℝ} (hc0 : 0<c) (hc : c<1/4) (ν : ℕ→ℕ) (τ : ℕ→ℝ)
    (hν : Tendsto ν atTop atTop) (hτ : Tendsto τ atTop atTop)
    (hwindow : ∀ᶠ m in atTop, 0≤τ m ∧ τ m≤c*Real.log (2*(ν m:ℝ))) :
    Tendsto (fun m=>Real.exp (-2*τ m)*liClockPairedEtaPartitionBorelKernel (ν m) (τ m))
      atTop (𝓝 (liClockPairedEtaInfinitePartitionComparisonLimit/2)) ∧
    Tendsto (fun m=>Real.exp (-2*τ m)*liClockPairedEtaContiguousBorelKernel
      (Real.log (2*(ν m:ℝ))) (τ m)) atTop (𝓝 (1/2)) ∧
    Tendsto (fun m=>liClockPairedEtaPartitionBorelKernel (ν m) (τ m)/
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(ν m:ℝ))) (τ m))
      atTop (𝓝 liClockPairedEtaInfinitePartitionComparisonLimit) ∧
    Tendsto (fun m=>liClockPairedEtaPartitionBorelKernel (ν m) (τ m)-
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(ν m:ℝ))) (τ m)) atTop atBot := by
  have hN : ∀ᶠ m in atTop, 0<ν m := by
    filter_upwards [hν.eventually (eventually_ge_atTop (1:ℕ))] with m hm
    omega
  have hE := (tendsto_liClockPairedEtaInfinitePartitionQuarterWindowError_zero hc0.le hc).comp hν
  have hAerr : Tendsto (fun m=>Real.exp (-2*τ m)*
      |liClockPairedEtaPartitionBorelKernel (ν m) (τ m)-
        liClockPairedEtaInfinitePartitionBorelKernel (τ m)|) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hE
    filter_upwards [hN,hwindow] with m hNm hwm
    simpa only [Function.comp_def,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_abs] using
      quarter_actual_real_error hc0.le hc hNm hwm.1 hwm.2
  have hUerr : Tendsto (fun m=>Real.exp (-2*τ m)*
      |liClockPairedEtaContiguousBorelKernel (Real.log (2*(ν m:ℝ))) (τ m)-
        liClockPairedEtaHalfLineBorelKernel (τ m)|) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hE
    filter_upwards [hN,hwindow] with m hNm hwm
    simpa only [Function.comp_def,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_abs] using
      quarter_reference_real_error hc0.le hc hNm hwm.1 hwm.2
  exact quarter_qualified_limits hτ hAerr hUerr
    (tendsto_liClockPairedEtaInfinitePartitionBorelKernel_scaled.comp hτ)
    (quarter_reference_scaled_limit.comp hτ) liClockPairedEtaInfinitePartitionComparisonLimit_lt_one

/-- One fixed real threshold gives a uniform negative finite-kernel gap. -/
theorem liClockPairedEtaInfinitePartitionQuarterWindow_eventually_uniform_negative_gap
    {c : ℝ} (hc0 : 0<c) (hc : c<1/4) :
    ∃T:ℝ, 0<T ∧ ∀ᶠ N:ℕ in atTop, ∀t:ℝ, T≤t → t≤c*Real.log (2*(N:ℝ)) →
      liClockPairedEtaPartitionBorelKernel N t-
        liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t ≤ -(1/2) := by
  have hA : ∀ᶠ N:ℕ in atTop, ∀t:ℝ, 0≤t → t≤c*Real.log (2*(N:ℝ)) →
      Real.exp (-2*t)*|liClockPairedEtaPartitionBorelKernel N t-
        liClockPairedEtaInfinitePartitionBorelKernel t| ≤
        liClockPairedEtaInfinitePartitionQuarterWindowError c N := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    intro t ht0 ht
    exact quarter_actual_real_error hc0.le hc (by omega) ht0 ht
  have hU : ∀ᶠ N:ℕ in atTop, ∀t:ℝ, 0≤t → t≤c*Real.log (2*(N:ℝ)) →
      Real.exp (-2*t)*|liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t-
        liClockPairedEtaHalfLineBorelKernel t| ≤
        liClockPairedEtaInfinitePartitionQuarterWindowError c N := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    intro t ht0 ht
    exact quarter_reference_real_error hc0.le hc (by omega) ht0 ht
  exact quarter_uniform_negative_gap
    (tendsto_liClockPairedEtaInfinitePartitionQuarterWindowError_zero hc0.le hc) hA hU
    quarter_infinite_scaled_gap (by linarith [liClockPairedEtaInfinitePartitionComparisonLimit_lt_one])

end RHTower
