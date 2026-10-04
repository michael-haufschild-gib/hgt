import GaloisForLFunctions.RHTower.ThetaCuspRatioCubicNormalForm
import Mathlib.Topology.Algebra.MvPolynomial
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology

def normalPolyValue (P : Poly) (h r s : ℝ) : ℝ :=
  (eval (basePoint (h:ℂ) (r:ℂ) (s:ℂ)) P).re

theorem normalPolyValue_continuous (P : Poly) :
    Continuous (fun z : ℝ×(ℝ×ℝ) => normalPolyValue P z.1 z.2.1 z.2.2) := by
  apply Complex.continuous_re.comp
  apply P.continuous_eval.comp
  apply continuous_pi
  intro i
  cases i <;> simp only [basePoint] <;> fun_prop

theorem normalPolyValue_zero_continuous (P : Poly) :
    Continuous (fun z : ℝ×(ℝ×ℝ) => normalPolyValue P z.1 z.2.1 0) := by
  have hc : Continuous (fun z : ℝ×(ℝ×ℝ) => (z.1,(z.2.1,(0:ℝ)))) := by fun_prop
  simpa only [Function.comp_def] using (normalPolyValue_continuous P).comp hc

theorem normal_form_real (h r s : ℝ) :
    regularSlopeValue h r (s+cubicSheet h r)=
      s*normalPolyValue nonlinearTransverseCore h r s+
      h^3*normalPolyValue nonlinearCubicCore h r 0 := by
  have he := congrArg Complex.re (nonlinearSlope_normal_form (h:ℂ) (r:ℂ) (s:ℂ))
  rw [nonlinearShift_eval] at he
  have hb : (s:ℂ)+(r:ℂ)*(1/12-7*(h:ℂ)/72)+((r:ℂ)^2/144)*(h:ℂ)^2-
      (7*(r:ℂ)^2/432)*(h:ℂ)^3=((s+cubicSheet h r:ℝ):ℂ) := by
    dsimp [cubicSheet]
    push_cast
    ring
  rw [hb] at he
  simpa only [regularSlopeValue,normalPolyValue,←Complex.ofReal_pow,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.ofReal_zero,zero_mul,sub_zero,Complex.add_re] using he

theorem normalTransverseCore_real_zero (r s : ℝ) :
    normalPolyValue nonlinearTransverseCore 0 r s=
      7776*((6:ℝ)^24*1990656*1679616) := by
  change (eval (basePoint 0 (r:ℂ) (s:ℂ)) nonlinearTransverseCore).re=_
  rw [nonlinearTransverseCore_zero,principalMass_real]
  norm_cast

theorem normalCubicCore_real_zero (r : ℝ) :
    normalPolyValue nonlinearCubicCore 0 r 0=
      63*((6:ℝ)^24*1990656*1679616)*(122880/7-r^2) := by
  change (eval (basePoint 0 (r:ℂ) 0) nonlinearCubicCore).re=_
  rw [←affineLine_eval,nonlinearCubicCore_line,nonlinearSlopeCore_real_zero]

private theorem compact_pair_positive (A L : ℝ → ℝ → ℝ → ℝ)
    (ha : Continuous (fun z : ℝ×(ℝ×ℝ) => A z.1 z.2.1 z.2.2))
    (hl : Continuous (fun z : ℝ×(ℝ×ℝ) => L z.1 z.2.1 0))
    (hpos : ∀ r∈Set.Icc (0:ℝ) 15, ∀ s∈Set.Icc (0:ℝ) 4, 0<A 0 r s ∧ 0<L 0 r 0) :
    ∀ᶠ h in 𝓝 (0:ℝ), ∀ r∈Set.Icc (0:ℝ) 15, ∀ s∈Set.Icc (0:ℝ) 4,
      0<A h r s ∧ 0<L h r 0 := by
  have hcompact : IsCompact ((Set.Icc (0:ℝ) 15) ×ˢ (Set.Icc (0:ℝ) 4)) :=
    isCompact_Icc.prod isCompact_Icc
  have hp := hcompact.eventually_forall_of_forall_eventually
    (x₀ := (0:ℝ)) (P := fun (h : ℝ) (rs : ℝ×ℝ) => 0<A h rs.1 rs.2 ∧ 0<L h rs.1 0) (by
      intro rs hrs
      have hs := hpos rs.1 hrs.1 rs.2 hrs.2
      have hat : Tendsto (fun z : ℝ×(ℝ×ℝ) => A z.1 z.2.1 z.2.2)
          (𝓝 ((0:ℝ),rs)) (𝓝 (A 0 rs.1 rs.2)) := ha.continuousAt
      have hlt : Tendsto (fun z : ℝ×(ℝ×ℝ) => L z.1 z.2.1 0)
          (𝓝 ((0:ℝ),rs)) (𝓝 (L 0 rs.1 0)) := hl.continuousAt
      exact (hat.eventually_const_lt hs.1).and (hlt.eventually_const_lt hs.2))
  filter_upwards [hp] with h hh r hr s hs
  exact hh (r,s) ⟨hr,hs⟩

theorem nonlinear_cores_eventually_pos :
    ∀ᶠ h in 𝓝 (0:ℝ), ∀ r∈Set.Icc (0:ℝ) 15, ∀ s∈Set.Icc (0:ℝ) 4,
      0<normalPolyValue nonlinearTransverseCore h r s ∧
      0<normalPolyValue nonlinearCubicCore h r 0 := by
  apply compact_pair_positive (normalPolyValue nonlinearTransverseCore)
    (normalPolyValue nonlinearCubicCore) (normalPolyValue_continuous nonlinearTransverseCore)
    (normalPolyValue_zero_continuous nonlinearCubicCore)
  intro r hr s hs
  rw [normalTransverseCore_real_zero,normalCubicCore_real_zero]
  constructor
  · positivity
  · apply mul_pos (by positivity : (0:ℝ)<63*((6:ℝ)^24*1990656*1679616))
    have hr0 := hr.1
    have hr1 := hr.2
    nlinarith

def compactSpeed (h r t : ℝ) : ℝ :=
  r*(1-2*h/3-4*h^2/9)-(2/9)*(3+2*h)*(9-r*h^2)*t

theorem compactSpeed_bounds {h r t : ℝ} (hh0 : 0≤h) (hh1 : h≤1/4)
    (hr0 : 0≤r) (hr1 : r≤15) (ht : 0<t) (hf : 0<compactSpeed h r t) :
    0≤cubicSheet h r ∧ t<4 := by
  have hs : h^2≤1/16 := by nlinarith
  have hrv : r*h^2≤15/16 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hs)]
  have hv : 8≤9-r*h^2 := by linarith
  have hh : 0≤1-7*h/3 := by linarith
  have hb : 0≤r*(1/12-7*h/72) := mul_nonneg hr0 (by linarith)
  have hB : cubicSheet h r=r*(1/12-7*h/72)+(r^2*h^2/144)*(1-7*h/3) := by
    unfold cubicSheet
    ring
  constructor
  · rw [hB]
    exact add_nonneg hb (mul_nonneg (by positivity) hh)
  · have hc : 5≤(2/9)*(3+2*h)*(9-r*h^2) := by
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hh0) (sub_nonneg.mpr hv)]
    have hm := mul_le_mul_of_nonneg_right hc ht.le
    have hd : r*(1-2*h/3-4*h^2/9)≤r := by
      have he : 0≤2*h/3+4*h^2/9 := by positivity
      nlinarith [mul_nonneg hr0 he]
    unfold compactSpeed at hf
    linarith

theorem nonlinear_cone_tail_pos :
    ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ r t : ℝ,
      0≤r → r≤361/25 → 0<t → 0<compactSpeed h r t →
      r*(1/12-7*h/72)<t-h^2*t^2 → 0<regularSlopeValue h r t := by
  have hb : ∀ᶠ h in 𝓝[>] (0:ℝ), h≤1/4 :=
    (eventually_le_nhds (show (0:ℝ)<1/4 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [nonlinear_cores_eventually_pos.filter_mono nhdsWithin_le_nhds,hb,self_mem_nhdsWithin]
    with h hc hb hh
  intro r t hr0 hr1 ht hf he
  have hr15 : r≤15 := by linarith
  have hbounds := compactSpeed_bounds hh.le hb hr0 hr15 ht hf
  have hs0 : 0<t-cubicSheet h r := sub_pos.mpr (nonlinear_barrier_above_cubic hr0 (by linarith) he)
  have hs4 : t-cubicSheet h r≤4 := by linarith [hbounds.1,hbounds.2]
  have hp := hc r ⟨hr0,hr15⟩ (t-cubicSheet h r) ⟨hs0.le,hs4⟩
  have heq := normal_form_real h r (t-cubicSheet h r)
  simp only [sub_add_cancel] at heq
  rw [heq]
  exact add_pos (mul_pos hs0 hp.1) (mul_pos (pow_pos hh 3) hp.2)

end
end HTGeometry.ThetaRatioInfinity
