import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheDisplacementIntegralOfAnOrdinaryPrimeBand
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The fixed denominator band in the middle test

Only a far negative tail and an exponentially short interval at the wall
can truncate the denominator band. Their signed cost is uniform over all
measurable deletions of the state.
-/
noncomputable section
open scoped Classical
open Set MeasureTheory Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- Displacements keeping every denominator inside the original time window and past the edge. -/
def middleBandInterior (r T : ℝ) : Set ℝ := Icc (-T/3) (-Real.exp ((-1/2+4*r)*T))

/-- Scale estimates uniform in all apertures at most r. -/
structure MiddleBandScale (r T : ℝ) (k L : ℕ) : Prop where
  pos : 0<T
  large : 1≤r*T
  lower : (1-r)*T≤Real.log k
  upper : Real.log L≤(1+2*r)*T
  count : (L:ℝ)≤Real.exp ((1+2*r)*T)
  poly : 1+2*T≤Real.exp (2*r*T)

theorem eventually_middleBandScale {r : ℝ} (hr : 0<r) :
    ∀ᶠ T : ℝ in atTop, ∀ {η : ℝ} {k : ℕ}, 0<η → η≤r → T/(1+η)≤Real.log k →
      MiddleBandScale r T k ⌈Real.exp ((1+η)*T)⌉₊ := by
  have hrt := (tendsto_id.const_mul_atTop hr : Tendsto (fun T : ℝ => r*T) atTop atTop)
  filter_upwards [eventually_gt_atTop (0:ℝ),hrt.eventually_ge_atTop 1,
    (Real.tendsto_exp_atTop.comp hrt).eventually_ge_atTop (2+2/r)] with T hT hlarge hcut
  intro η k hη hηr hk
  change 2+2/r≤Real.exp (r*T) at hcut
  have he := Real.add_one_le_exp (r*T)
  have h₂ : 2≤Real.exp (r*T) := by linarith only [he,hlarge]
  have hmul : (1-r)*(1+η)≤1 := by nlinarith only [hηr,mul_nonneg hr.le hη.le]
  have hlow : (1-r)*T≤T/(1+η) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith only [mul_le_mul_of_nonneg_right hmul hT.le]
  have hau : Real.exp ((1+η)*T)≤Real.exp ((1+r)*T) := by
    apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonneg_right (by linarith only [hηr]) hT.le
  have h₁ : 1≤Real.exp ((1+r)*T) := Real.one_le_exp (by positivity)
  have hc := Nat.ceil_lt_add_one (Real.exp_pos ((1+η)*T)).le
  have hcount : (⌈Real.exp ((1+η)*T)⌉₊:ℝ)≤Real.exp ((1+2*r)*T) := by
    rw [show (1+2*r)*T=(1+r)*T+r*T by ring,Real.exp_add]
    exact (show (⌈Real.exp ((1+η)*T)⌉₊:ℝ)≤Real.exp ((1+r)*T)*2 by
      linarith only [hc,hau,h₁]).trans (mul_le_mul_of_nonneg_left h₂ (Real.exp_pos _).le)
  have hLpos := (Real.exp_pos ((1+η)*T)).trans_le (Nat.le_ceil _)
  have ht : T≤Real.exp (r*T)/r := (le_div_iff₀ hr).mpr (by linarith only [he])
  refine ⟨hT,hlarge,hlow.trans hk,(Real.log_le_iff_le_exp hLpos).mpr hcount,hcount,?_⟩
  rw [show 2*r*T=r*T+r*T by ring,Real.exp_add]
  calc 1+2*T ≤ (2+2/r)*Real.exp (r*T) := by
          have h := mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤2)
          rw [← mul_div_assoc] at h
          rw [add_mul,div_mul_eq_mul_div]
          linarith only [h,h₂]
       _ ≤ _ := mul_le_mul_of_nonneg_right hcut (Real.exp_pos _).le

private theorem MiddleBandScale.start_pos {k L : ℕ} {r T : ℝ}
    (h : MiddleBandScale r T k L) (hsmall : r≤1/64) : 0<(k:ℝ) := by
  by_contra! hk
  have hk' : k=0 := by exact_mod_cast le_antisymm hk (Nat.cast_nonneg k)
  have hl := h.lower
  rw [hk',Nat.cast_zero,Real.log_zero] at hl
  linarith only [hl,mul_le_mul_of_nonneg_right hsmall h.pos.le,h.pos]

/-- Every physical abscissa is active throughout the interior. -/
theorem ordinaryIndicesAt_eq_full {k L : ℕ} {r T v : ℝ} (hr : 0<r) (hsmall : r≤1/64)
    (h : MiddleBandScale r T k L) (hv : v∈middleBandInterior r T) :
    ordinaryIndicesAt k L (Ioc (T/6) (6*T)) v=Finset.Ioc k L := by
  simp only [ordinaryIndicesAt,Finset.filter_eq_self]
  intro n hn
  obtain ⟨hkn,hnL⟩ := Finset.mem_Ioc.mp hn
  have hrT := mul_le_mul_of_nonneg_right hsmall h.pos.le
  have hkpos := h.start_pos hsmall
  have hnpos : 0<(n:ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hkn)
  have hlo := h.lower.trans (Real.log_le_log hkpos (Nat.cast_le.mpr hkn.le))
  have hup := (Real.log_le_log hnpos (Nat.cast_le.mpr hnL)).trans h.upper
  obtain ⟨hvlow,hvhi⟩ := hv
  have hvneg := hvhi.trans_lt (neg_lt_zero.mpr (Real.exp_pos _))
  let t := v+Real.log n
  have htlo : T/6<t := by dsimp only [t]; linarith only [hvlow,hlo,hrT,h.pos]
  have hthi : t≤2*T := by dsimp only [t]; linarith only [hvneg,hup,hrT,h.pos]
  refine ⟨⟨htlo,by change t≤_; linarith only [hthi,h.pos]⟩,
    (pastCriticalEdge_at_displacement (Nat.zero_lt_of_lt hkn) v).mpr ?_⟩
  change 1+Real.exp (-t/2)*Real.sqrt t<Real.exp (-v)
  by_cases hfar : v≤ -1
  · have hs := Real.sqrt_le_sqrt (show t≤Real.exp t by linarith only [Real.add_one_le_exp t])
    rw [← Real.exp_half] at hs
    have hw := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-t/2)).le
    rw [← Real.exp_add,show -t/2+t/2=0 by ring,Real.exp_zero] at hw
    have htwo := Real.add_one_lt_exp (by norm_num : (1:ℝ)≠0)
    exact (by linarith only [hw,htwo] : 1+Real.exp (-t/2)*Real.sqrt t<Real.exp 1).trans_le
      (Real.exp_le_exp.mpr (by linarith only [hfar]))
  · have ht : (1-2*r)*T≤t := by dsimp only [t]; linarith only [hfar,hlo,h.large]
    have hs := Real.sqrt_le_sqrt (show t≤Real.exp (2*r*T) by linarith only [hthi,h.poly])
    rw [← Real.exp_half,show 2*r*T/2=r*T by ring] at hs
    have hw := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-t/2)).le
    rw [← Real.exp_add] at hw
    have hstrict := hw.trans_lt (Real.exp_lt_exp.mpr
      (show -t/2+r*T<(-1/2+4*r)*T by linarith only [ht,mul_pos hr h.pos]))
    linarith only [hstrict,hvhi,Real.add_one_le_exp (-v)]

/-- The upper bound on numerator-block width puts its square root below the full band. -/
theorem sqrt_lt_middleBand_start {k L H : ℕ} {r T d : ℝ} (h : MiddleBandScale r T k L)
    (hr : 0<r) (hsmall : r≤1/64) (hd : 3*r≤d) (hX : Real.exp T≤H)
    (hpow : (H:ℝ)^(1/2+d)<L) : Real.sqrt H<k := by
  have hH := (Real.exp_pos T).trans_le hX
  have hlog := (Real.le_log_iff_exp_le hH).mpr hX
  have hroot : Real.sqrt H*Real.exp (d*T)<Real.exp ((1+2*r)*T) := by
    have hmon := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (by linarith only [hr,hd] : 0≤d))
    rw [Real.rpow_add hH,← Real.sqrt_eq_rpow,Real.rpow_def_of_pos hH d,mul_comm (Real.log H)] at hpow
    exact ((mul_le_mul_of_nonneg_left hmon (Real.sqrt_nonneg _)).trans_lt hpow).trans_le h.count
  have hcmp : Real.exp ((1+2*r)*T)≤Real.exp (Real.log k)*Real.exp (d*T) := by
    rw [← Real.exp_add,Real.exp_le_exp]
    linarith only [h.lower,mul_le_mul_of_nonneg_right hd h.pos.le]
  have hkpos := h.start_pos hsmall
  rw [Real.exp_log hkpos] at hcmp
  exact (lt_of_mul_lt_mul_right (hroot.trans_le hcmp) (Real.exp_pos _).le)

private theorem two_tail_cost {f : ℝ → ℝ} {D h T : ℝ} {A : Set ℝ} (hD : 0≤D) (hh : 0<h)
    (hA : MeasurableSet A) (hs : ∀ v ∈ A, v≤0 ∧ (v≤ -T/3 ∨ -h≤v))
    (hf : ∀ v ≤ 0, |f v| ≤ D*Real.exp (2*v)) :
    |∫ v in A, f v| ≤ D*(Real.exp (2*(-T/3))/2+h) := by
  let p := (Iic (-T/3)).indicator (fun v : ℝ => D*Real.exp (2*v))
  let q := (Icc (-h) 0).indicator (fun _ : ℝ => D)
  have hp' : IntegrableOn (fun v : ℝ => D*Real.exp (2*v)) (Iic (-T/3)) :=
    (integrableOn_exp_mul_Iic (by norm_num : 0<(2:ℝ)) (-T/3)).const_mul D
  have hp : Integrable p := hp'.integrable_indicator measurableSet_Iic
  have hq : Integrable q := (integrableOn_const (measure_Icc_lt_top.ne) :
    IntegrableOn (fun _ : ℝ => D) (Icc (-h) 0)).integrable_indicator measurableSet_Icc
  have hp₀ (v : ℝ) : 0≤p v := indicator_nonneg (fun _ _ => mul_nonneg hD (Real.exp_pos _).le) v
  have hq₀ (v : ℝ) : 0≤q v := indicator_nonneg (fun _ _ => hD) v
  have hmaj (v : ℝ) : ‖A.indicator f v‖≤(p+q) v := by
    rw [Pi.add_apply,Real.norm_eq_abs]
    by_cases hv : v∈A
    · rw [indicator_of_mem hv]
      obtain ⟨hv₀,hvleft|hvright⟩ := hs v hv
      · have hin : v∈Iic (-T/3) := hvleft
        have he : p v=D*Real.exp (2*v) := indicator_of_mem hin _
        linarith only [hf v hv₀,he,hq₀ v]
      · have hin : v∈Icc (-h) 0 := ⟨hvright,hv₀⟩
        have hbound := (hf v hv₀).trans (mul_le_of_le_one_right hD (Real.exp_le_one_iff.mpr (by linarith only [hv₀])))
        have he : q v=D := indicator_of_mem hin _
        linarith only [hbound,he,hp₀ v]
    · rw [indicator_of_notMem hv,abs_zero]
      exact add_nonneg (hp₀ v) (hq₀ v)
  have hi : ‖∫ v, A.indicator f v‖ ≤ ∫ v : ℝ, p v+q v :=
    norm_integral_le_of_norm_le (g := fun v => p v+q v) (hp.add hq) (Eventually.of_forall hmaj)
  rw [Real.norm_eq_abs,integral_indicator hA,integral_add hp hq] at hi
  dsimp only [p,q] at hi
  rw [integral_indicator measurableSet_Iic,integral_const_mul,integral_exp_mul_Iic (by norm_num),
    integral_indicator measurableSet_Icc,setIntegral_const,smul_eq_mul,Real.volume_real_Icc_of_le (neg_nonpos.mpr hh.le)] at hi
  linarith only [hi]

/-- Uniform exponential cost of all displacements outside the fixed band,
including every measurable part of the exceptional set. -/
theorem ordinaryDisplacementDensity_outside {Φ : ℝ → ℝ} {C r T m : ℝ} {k L : ℕ}
    (hC : 0≤C) (hb : ∀ v, |Φ v|≤C*Real.exp (2*v)) (hr : 0<r) (hsmall : r≤1/64)
    (h : MiddleBandScale r T k L) {A : Set ℝ} (hA : MeasurableSet A)
    (hs : ∀ v ∈ A, v≤0 ∧ v∉middleBandInterior r T) :
    |∫ v in A, ordinaryDisplacementDensity Φ m T k L v| ≤
      2*|m| *C*Real.exp (8*r*T) := by
  let w := Real.exp ((-1/2+4*r)*T)
  let D := |m| *C*((1+Real.log L)*L)*Real.exp (-T/2)
  have hlog := Real.log_natCast_nonneg L
  have hD : 0≤D := by dsimp only [D]; positivity
  have h₁ := two_tail_cost (T:=T) (h:=w) hD (Real.exp_pos _) hA (fun v hv => by
    obtain ⟨hv₀,hout⟩ := hs v hv
    refine ⟨hv₀,?_⟩
    by_cases hl : -T/3≤v
    · exact Or.inr (le_of_not_ge fun hh => hout ⟨hl,hh⟩)
    · exact Or.inl (le_of_not_ge hl)) (fun v hv => ordinaryDisplacementDensity_bound hC hb m T k L hv)
  have hleft : Real.exp (2*(-T/3))≤w := Real.exp_le_exp.mpr
    (by linarith only [mul_nonneg hr.le h.pos.le,h.pos])
  have hlogs : 1+Real.log L≤Real.exp (2*r*T) := by
    linarith only [h.upper,mul_le_mul_of_nonneg_right hsmall h.pos.le,h.poly,h.pos]
  have hprod := mul_le_mul hlogs h.count (Nat.cast_nonneg L) (Real.exp_pos _).le
  have hscale : Real.exp (2*r*T)*Real.exp ((1+2*r)*T)*Real.exp (-T/2)*w=Real.exp (8*r*T) := by
    dsimp only [w]; rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]; congr 1; ring
  calc _ ≤ D*(2*w) := h₁.trans (mul_le_mul_of_nonneg_left (by linarith only [hleft,(Real.exp_pos (2*(-T/3)))]) hD)
       _ = (2*|m| *C)*(((1+Real.log L)*L)*Real.exp (-T/2)*w) := by dsimp only [D]; ring
       _ ≤ (2*|m| *C)*(Real.exp (2*r*T)*Real.exp ((1+2*r)*T)*Real.exp (-T/2)*w) :=
         mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod
           (Real.exp_pos _).le) (Real.exp_pos _).le) (by positivity)
       _ = _ := by rw [hscale]

#print axioms ordinaryIndicesAt_eq_full
#print axioms ordinaryDisplacementDensity_outside
end GaloisForLFunctions.ExclusionOfTheCriticalState
