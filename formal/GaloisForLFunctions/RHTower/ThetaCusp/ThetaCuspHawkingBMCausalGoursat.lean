import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCausalRiemannKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The actual BM Riemann kernel satisfies its causal characteristic integral equation. -/
namespace RHTower.D4BMCausalKernel
open Complex Set Filter Topology MeasureTheory
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

/-- The original Riemann function in null coordinates based at the source point. -/
def characteristicKernel (nu : ℂ) (y u v : ℝ) : ℂ :=
  riemannKernel nu ((u+v)/2) (y+(u-v)/2) y

private theorem invariant_comp_derivative {h x : ℝ → ℝ} (y t dh dx : ℝ)
    (hh : HasDerivAt h dh t) (hx : HasDerivAt x dx t) :
    HasDerivAt (fun r => invariant (h r) (x r) y)
      (dh*invariantTimeFirst (h t) (x t) y+dx*invariantSpaceFirst (h t) (x t) y) t := by
  have hc := (Real.cosh_pos (x t)).ne'
  have hy := (Real.cosh_pos y).ne'
  apply ((((Real.hasDerivAt_cosh _).comp t hh).add
    (((Real.hasDerivAt_sinh _).comp t hx).mul_const (Real.sinh y))).div
    (((Real.hasDerivAt_cosh _).comp t hx).mul_const (Real.cosh y))
    (mul_ne_zero hc hy)).congr_deriv
  dsimp [invariantTimeFirst,invariantSpaceFirst,invariant,Real.tanh_eq_sinh_div_cosh]
  simp only [Real.tanh_eq_sinh_div_cosh]
  field_simp [hc,hy]
  ring

private theorem invariantTimeFirst_comp_derivative {h x : ℝ → ℝ} (y t dh dx : ℝ)
    (hh : HasDerivAt h dh t) (hx : HasDerivAt x dx t) :
    HasDerivAt (fun r => invariantTimeFirst (h r) (x r) y)
      (dh*invariantTimeSecond (h t) (x t) y-
        dx*Real.tanh (x t)*invariantTimeFirst (h t) (x t) y) t := by
  have hc := (Real.cosh_pos (x t)).ne'
  have hy := (Real.cosh_pos y).ne'
  apply (((Real.hasDerivAt_sinh _).comp t hh).div
    (((Real.hasDerivAt_cosh _).comp t hx).mul_const (Real.cosh y))
    (mul_ne_zero hc hy)).congr_deriv
  dsimp [invariantTimeFirst,invariantTimeSecond,Real.tanh_eq_sinh_div_cosh]
  simp only [Real.tanh_eq_sinh_div_cosh]
  field_simp [hc,hy]

private theorem tanh_derivative_local (x : ℝ) :
    HasDerivAt Real.tanh (1-Real.tanh x^(2 : ℕ)) x := by
  have hc := (Real.cosh_pos x).ne'
  have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  rw [show Real.tanh = Real.sinh / Real.cosh by
    funext r
    exact Real.tanh_eq_sinh_div_cosh r]
  apply hd.congr_deriv
  simp only [Pi.div_apply]
  field_simp [hc]

private def nullInvariantFirst (y u v : ℝ) : ℝ :=
  (invariantTimeFirst ((u+v)/2) (y+(u-v)/2) y+
    invariantSpaceFirst ((u+v)/2) (y+(u-v)/2) y)/2

private theorem nullInvariant_first (y u v : ℝ) :
    HasDerivAt (fun a => invariant ((a+v)/2) (y+(a-v)/2) y)
      (nullInvariantFirst y u v) u := by
  convert! invariant_comp_derivative y u (1/2) (1/2)
    (((hasDerivAt_id u).add_const v).div_const 2)
    ((((hasDerivAt_id u).sub_const v).div_const 2).const_add y) using 1
  simp only [nullInvariantFirst,id_eq]
  ring

private theorem nullInvariant_second (y u v : ℝ) :
    HasDerivAt (fun b => invariant ((u+b)/2) (y+(u-b)/2) y)
      ((invariantTimeFirst ((u+v)/2) (y+(u-v)/2) y-
        invariantSpaceFirst ((u+v)/2) (y+(u-v)/2) y)/2) v := by
  convert! invariant_comp_derivative y v (1/2) (-1/2)
    (((hasDerivAt_id v).const_add u).div_const 2)
    ((((hasDerivAt_id v).const_sub u).div_const 2).const_add y) using 1
  simp only [id_eq]
  ring

private theorem nullInvariant_mixed (y u v : ℝ) :
    HasDerivAt (nullInvariantFirst y u)
      ((invariantTimeSecond ((u+v)/2) (y+(u-v)/2) y-
        invariantSpaceSecond ((u+v)/2) (y+(u-v)/2) y)/4) v := by
  let h := (u+v)/2
  let x := y+(u-v)/2
  have ht : HasDerivAt (fun b : ℝ => (u+b)/2) (1/2) v := by
    convert! ((hasDerivAt_id v).const_add u).div_const 2 using 1
  have hx : HasDerivAt (fun b : ℝ => y+(u-b)/2) (-1/2) v := by
    convert! (((hasDerivAt_id v).const_sub u).div_const 2).const_add y using 1
  have hT := invariantTimeFirst_comp_derivative y v (1/2) (-1/2) ht hx
  have hX := (((tanh_derivative_local x).comp v hx).mul
    (nullInvariant_second y u v)).const_sub (Real.tanh y)
  apply ((hT.add hX).div_const 2).congr_deriv
  dsimp [h,x,invariantSpaceFirst,invariantSpaceSecond]
  ring

private theorem nullInvariant_positive (y : ℝ) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < invariant ((u+v)/2) (y+(u-v)/2) y := by
  have hi : |(y+(u-v)/2)-y| ≤ (u+v)/2 := by
    rw [abs_le]
    constructor <;> linarith
  exact lt_of_lt_of_le (by norm_num) (invariant_causal ⟨_,_,_,hi⟩)

private def characteristicFirst (nu : ℂ) (y u v : ℝ) : ℂ :=
  legendreKernelFirst nu (invariant ((u+v)/2) (y+(u-v)/2) y)*
    (nullInvariantFirst y u v : ℂ)

private theorem characteristic_first_derivative (nu : ℂ) (y u v : ℝ)
    (hz : 0 < invariant ((u+v)/2) (y+(u-v)/2) y) :
    HasDerivAt (fun a => characteristicKernel nu y a v) (characteristicFirst nu y u v) u := by
  simpa only [characteristicKernel,riemannKernel,characteristicFirst,Function.comp_def,
    Complex.real_smul,mul_comm] using
    (legendreKernel_derivatives nu hz).1.scomp u (nullInvariant_first y u v)

private theorem characteristic_mixed_derivative (nu : ℂ) (y u v : ℝ)
    (hz : 0 < invariant ((u+v)/2) (y+(u-v)/2) y) :
    HasDerivAt (characteristicFirst nu y u)
      (nu*(nu+1)/(4*(Real.cosh (y+(u-v)/2):ℂ)^(2 : ℕ))*characteristicKernel nu y u v) v := by
  let h := (u+v)/2
  let x := y+(u-v)/2
  have hc : (Real.cosh x : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos x).ne'
  have hg1 : (invariantTimeFirst h x y:ℂ)^(2 : ℕ)-(invariantSpaceFirst h x y:ℂ)^(2 : ℕ) =
      ((invariant h x y:ℂ)^(2 : ℕ)-1)/(Real.cosh x:ℂ)^(2 : ℕ) := by
    exact_mod_cast (invariant_wave_geometry h x y).1
  have hg2 : (invariantTimeSecond h x y:ℂ)-(invariantSpaceSecond h x y:ℂ) =
      2*(invariant h x y:ℂ)/(Real.cosh x:ℂ)^(2 : ℕ) := by
    exact_mod_cast (invariant_wave_geometry h x y).2
  have hraw := ((legendreKernel_derivatives nu hz).2.scomp v
    (nullInvariant_second y u v)).mul (nullInvariant_mixed y u v).ofReal_comp
  apply hraw.congr_deriv
  simp only [Complex.real_smul,Function.comp_apply]
  change _ = nu*(nu+1)/(4*(Real.cosh x:ℂ)^(2 : ℕ))*legendreKernel nu (invariant h x y)
  dsimp only [nullInvariantFirst]
  push_cast
  change ((invariantTimeFirst h x y-invariantSpaceFirst h x y:ℂ)/2*
      legendreKernelSecond nu (invariant h x y))*
      ((invariantTimeFirst h x y+invariantSpaceFirst h x y:ℂ)/2)+
    legendreKernelFirst nu (invariant h x y)*
      ((invariantTimeSecond h x y-invariantSpaceSecond h x y:ℂ)/4) = _
  have he := legendreKernel_equation nu hz
  change ((invariant h x y:ℂ)^(2 : ℕ)-1)*legendreKernelSecond nu (invariant h x y)+
    2*(invariant h x y:ℂ)*legendreKernelFirst nu (invariant h x y)-
    nu*(nu+1)*legendreKernel nu (invariant h x y) = 0 at he
  simp only [← Complex.ofReal_cosh]
  linear_combination
    legendreKernelSecond nu (invariant h x y)/4*hg1+
    legendreKernelFirst nu (invariant h x y)/4*hg2+
    1/(4*(Real.cosh x:ℂ)^(2 : ℕ))*he

private theorem characteristic_axis_right (nu : ℂ) (y u : ℝ) :
    characteristicKernel nu y u 0 = 1 := by
  unfold characteristicKernel
  have he : (u+0)/2 = (y+(u-0)/2)-y := by ring
  rw [he,riemannKernel_characteristic]

private theorem characteristic_axis_left (nu : ℂ) (y v : ℝ) :
    characteristicKernel nu y 0 v = 1 := by
  unfold characteristicKernel riemannKernel
  have he : (0+v)/2 = -((y+(0-v)/2)-y) := by ring
  rw [he]
  simp only [invariant,Real.cosh_neg]
  change legendreKernel nu (invariant ((y+(0-v)/2)-y) (y+(0-v)/2) y) = 1
  rw [invariant_characteristic,legendreKernel_one]

private theorem characteristicFirst_axis (nu : ℂ) (y : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    characteristicFirst nu y u 0 = 0 := by
  have hd := characteristic_first_derivative nu y u 0 (nullInvariant_positive y hu le_rfl)
  have he : (fun a => characteristicKernel nu y a 0) = fun _ => (1:ℂ) := by
    funext a
    exact characteristic_axis_right nu y a
  rw [he] at hd
  exact hd.unique (hasDerivAt_const u (1:ℂ))

private theorem nullInvariantFirst_continuous (y v : ℝ) :
    Continuous (fun u => nullInvariantFirst y u v) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have hh : HasDerivAt (fun a : ℝ => (a+v)/2) (1/2) u := by
    convert! ((hasDerivAt_id u).add_const v).div_const 2 using 1
  have hx : HasDerivAt (fun a : ℝ => y+(a-v)/2) (1/2) u := by
    convert! (((hasDerivAt_id u).sub_const v).div_const 2).const_add y using 1
  have ht := (invariantTimeFirst_comp_derivative y u (1/2) (1/2) hh hx).continuousAt
  have hz := (nullInvariant_first y u v).continuousAt
  have htan := ((tanh_derivative_local (y+(u-v)/2)).comp u hx).continuousAt
  exact (ht.add ((htan.mul hz).const_sub (Real.tanh y))).div_const 2

private theorem characteristicFirst_continuousAt (nu : ℂ) (y u v : ℝ)
    (hz : 0 < invariant ((u+v)/2) (y+(u-v)/2) y) :
    ContinuousAt (fun a => characteristicFirst nu y a v) u := by
  have hp := ((legendreKernel_derivatives nu hz).2.scomp u
    (nullInvariant_first y u v)).continuousAt
  have hf : ContinuousAt (fun a => (nullInvariantFirst y a v : ℂ)) u :=
    (Complex.continuous_ofReal.comp (nullInvariantFirst_continuous y v)).continuousAt
  convert! hp.mul hf using 1

private theorem characteristic_integrand_continuousOn (nu : ℂ) (y : ℝ)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ContinuousOn (fun b => nu*(nu+1)/(4*(Real.cosh (y+(u-b)/2):ℂ)^(2 : ℕ))*
      characteristicKernel nu y u b) (uIcc 0 v) := by
  intro b hb
  have hb0 : 0 ≤ b := (show b ∈ Icc 0 v by simpa only [uIcc_of_le hv] using hb).1
  have hz := nullInvariant_positive y hu hb0
  have hr := ((legendreKernel_derivatives nu hz).1.scomp b
    (nullInvariant_second y u b)).continuousAt
  have hx : HasDerivAt (fun a : ℝ => y+(u-a)/2) (-1/2) b := by
    convert! (((hasDerivAt_id b).const_sub u).div_const 2).const_add y using 1
  have hc := (((Real.hasDerivAt_cosh (y+(u-b)/2)).comp b hx).continuousAt.ofReal).pow 2
  have hn : (4:ℂ)*(Real.cosh (y+(u-b)/2):ℂ)^(2 : ℕ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (by exact_mod_cast (Real.cosh_pos _).ne'))
  exact ((continuousAt_const.div (continuousAt_const.mul hc) hn).mul hr).continuousWithinAt

private theorem characteristicFirst_integral (nu : ℂ) (y : ℝ)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (∫ b in (0:ℝ)..v, nu*(nu+1)/(4*(Real.cosh (y+(u-b)/2):ℂ)^(2 : ℕ))*
      characteristicKernel nu y u b) = characteristicFirst nu y u v := by
  have hd : ∀ b ∈ uIcc 0 v, HasDerivAt (characteristicFirst nu y u)
      (nu*(nu+1)/(4*(Real.cosh (y+(u-b)/2):ℂ)^(2 : ℕ))*characteristicKernel nu y u b) b := by
    intro b hb
    have hb0 : 0 ≤ b := (show b ∈ Icc 0 v by simpa only [uIcc_of_le hv] using hb).1
    exact characteristic_mixed_derivative nu y u b (nullInvariant_positive y hu hb0)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (characteristic_integrand_continuousOn nu y hu hv).intervalIntegrable
  simpa only [characteristicFirst_axis nu y hu,sub_zero] using he

private theorem characteristic_integral (nu : ℂ) (y : ℝ)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    characteristicKernel nu y u v = 1+
      ∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v,
        nu*(nu+1)/(4*(Real.cosh (y+(a-b)/2):ℂ)^(2 : ℕ))*characteristicKernel nu y a b := by
  have he : (∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v,
        nu*(nu+1)/(4*(Real.cosh (y+(a-b)/2):ℂ)^(2 : ℕ))*characteristicKernel nu y a b) =
      ∫ a in (0:ℝ)..u, characteristicFirst nu y a v := by
    apply intervalIntegral.integral_congr
    intro a ha
    have ha0 : 0 ≤ a := (show a ∈ Icc 0 u by simpa only [uIcc_of_le hu] using ha).1
    exact characteristicFirst_integral nu y ha0 hv
  have hd : ∀ a ∈ uIcc 0 u, HasDerivAt (fun r => characteristicKernel nu y r v)
      (characteristicFirst nu y a v) a := by
    intro a ha
    have ha0 : 0 ≤ a := (show a ∈ Icc 0 u by simpa only [uIcc_of_le hu] using ha).1
    exact characteristic_first_derivative nu y a v (nullInvariant_positive y ha0 hv)
  have hc : ContinuousOn (fun a => characteristicFirst nu y a v) (uIcc 0 u) := by
    intro a ha
    have ha0 : 0 ≤ a := (show a ∈ Icc 0 u by simpa only [uIcc_of_le hu] using ha).1
    exact (characteristicFirst_continuousAt nu y a v
      (nullInvariant_positive y ha0 hv)).continuousWithinAt
  rw [he,intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable,
    characteristic_axis_left]
  ring

/-- The actual causal Riemann function equals its unit vertex plus the integrated original
potential correction. This holds on the entire closed forward cone for every complex degree. -/
theorem riemannKernel_goursat (nu : ℂ) (p : CausalPoint) :
    riemannKernel nu p.time p.target p.source = 1+
      ∫ a in (0:ℝ)..(p.time+p.target-p.source),
        ∫ b in (0:ℝ)..(p.time-p.target+p.source),
          nu*(nu+1)/(4*(Real.cosh (p.source+(a-b)/2):ℂ)^(2 : ℕ))*
            characteristicKernel nu p.source a b := by
  obtain ⟨hl,hr⟩ := abs_le.mp p.inside
  have hu : 0 ≤ p.time+p.target-p.source := by linarith
  have hv : 0 ≤ p.time-p.target+p.source := by linarith
  have h := characteristic_integral nu p.source hu hv
  have ht : ((p.time+p.target-p.source)+(p.time-p.target+p.source))/2 = p.time := by ring
  have hx : p.source+((p.time+p.target-p.source)-(p.time-p.target+p.source))/2 = p.target := by ring
  simpa only [characteristicKernel,ht,hx] using h

/-- The potential part of the original causal kernel, with its entire characteristic rectangle. -/
def causalPotentialCorrection (nu : ℂ) (h x y : ℝ) : ℂ :=
  if |x-y| ≤ h then
    ∫ a in (0:ℝ)..(h+x-y), ∫ b in (0:ℝ)..(h-x+y),
      nu*(nu+1)/(4*(Real.cosh (y+(a-b)/2):ℂ)^(2 : ℕ))*characteristicKernel nu y a b
  else 0

private theorem causalKernel_split (nu : ℂ) (h x y : ℝ) :
    (if |x-y| ≤ h then riemannKernel nu h x y else 0) =
      (if |x-y| ≤ h then (1:ℂ) else 0)+causalPotentialCorrection nu h x y := by
  by_cases hi : |x-y| ≤ h
  · simpa only [causalPotentialCorrection,if_pos hi] using
      riemannKernel_goursat nu ⟨h,x,y,hi⟩
  · simp only [causalPotentialCorrection,if_neg hi,zero_add]

/-- The physical reflected kernel retains exactly the free causal impulse and the direct-minus-image
potential correction, including the original factor one half and both support conditions. -/
theorem dirichletCausalKernel_volterra (chi : ℂ) (h x y : ℝ) :
    dirichletCausalKernel chi h x y =
      ((if |x-y| ≤ h then (1:ℂ) else 0)-(if |x+y| ≤ h then (1:ℂ) else 0))/2+
      (causalPotentialCorrection (-1/2+Complex.I*chi) h x y-
        causalPotentialCorrection (-1/2+Complex.I*chi) h x (-y))/2 := by
  have hd := causalKernel_split (-1/2+Complex.I*chi) h x y
  have hi := causalKernel_split (-1/2+Complex.I*chi) h x (-y)
  simp only [sub_neg_eq_add] at hi
  unfold dirichletCausalKernel bmRiemannKernel
  rw [hd,hi]
  ring

end
end RHTower.D4BMCausalKernel
