import GaloisForLFunctions.HTGeometry.EvenEntireSquareFactor
import GaloisForLFunctions.HTGeometry.RealNonnegativeZeroEvenOrder
import GaloisForLFunctions.RHTower.Reflection

/-!
# Axis positivity removes the multiplicity obstruction

For an even entire function nonnegative on both axes, every axis zero has even
order and the origin order is divisible by four. Square descent exposes the
extra factor of two at the origin. These are consequences of positivity, not
additional divisor assumptions.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.HTGeometry.EvenHermitianFactor

def AxisNonnegative (f : ℂ → ℂ) : Prop :=
  ∀ z, z.re=0 ∨ z.im=0 → (f z).im=0 ∧ 0≤(f z).re

theorem even_order_real {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hr : ∀ x : ℝ,(f x).im=0) (hp : ∀ x : ℝ,0≤(f x).re)
    (x : ℝ) : Even (analyticOrderAt f x).toNat := by
  by_cases ht : analyticOrderAt f x=⊤
  · simp [ht]
  by_cases hz : f x=0
  · have hn : ∃ z,f z≠0 := by
      by_contra h
      push Not at h
      exact ht (analyticOrderAt_eq_top.mpr (Eventually.of_forall h))
    obtain ⟨z,hz'⟩ := hn
    obtain ⟨k,_,hk,_⟩ := exists_even_order_factor_of_real_nonneg hf hr hz
      (Eventually.of_forall hp) hz'
    rw [hk]
    simp
  · rw [(hf.analyticAt _).analyticOrderAt_eq_zero.mpr hz]
    simp

theorem even_order_axis {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (ha : AxisNonnegative f) (z : ℂ) (hz : z.re=0 ∨ z.im=0) :
    Even (analyticOrderAt f z).toNat := by
  rcases hz with hz | hz
  · let g := fun w : ℂ => f (Complex.I*w)
    have hg : Differentiable ℂ g := hf.comp (by fun_prop)
    have ho := even_order_real hg
      (fun x => (ha _ (Or.inl (by simp))).1)
      (fun x => (ha _ (Or.inl (by simp))).2) z.im
    have hord : analyticOrderAt g (z.im : ℂ)=analyticOrderAt f (Complex.I*(z.im : ℂ)) :=
      analyticOrderAt_comp_of_deriv_ne_zero (f := f) (g := fun w : ℂ => Complex.I*w)
        (by fun_prop) (by simp)
    have heq : Complex.I*(z.im : ℂ)=z := by apply Complex.ext <;> simp [hz]
    rwa [hord,heq] at ho
  · have heq : (z.re : ℂ)=z := by apply Complex.ext <;> simp [hz]
    simpa only [heq] using even_order_real hf
      (fun x => (ha _ (Or.inr (by simp))).1)
      (fun x => (ha _ (Or.inr (by simp))).2) z.re

theorem square_root_real_on_axis (x : ℝ) :
    (Complex.sqrt (x : ℂ)).re=0 ∨ (Complex.sqrt (x : ℂ)).im=0 := by
  have h := congrArg Complex.im (complex_sqrt_sq (x : ℂ))
  rw [pow_two,Complex.mul_im,Complex.ofReal_im] at h
  have hh : (Complex.sqrt (x : ℂ)).re*(Complex.sqrt (x : ℂ)).im=0 := by nlinarith
  exact mul_eq_zero.mp hh

theorem square_descent_nonnegative {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (he : Function.Even f) (ha : AxisNonnegative f) (x : ℝ) :
    (evenEntireSquareFactor f x).im=0 ∧ 0≤(evenEntireSquareFactor f x).re := by
  have h := ha (Complex.sqrt (x : ℂ)) (square_root_real_on_axis x)
  rwa [← evenEntireSquareFactor_sq hf he,complex_sqrt_sq] at h

theorem axis_four_pow (z : ℂ) (hz : z.re=0 ∨ z.im=0) (k : ℕ) :
    z^(4*k)=((‖z‖^(4*k) : ℝ) : ℂ) := by
  have h4 : z^4=((‖z‖^4 : ℝ) : ℂ) := by
    rcases hz with hz | hz
    · have heq : z=(z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
      rw [heq,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
        mul_pow,show Complex.I^4=1 by norm_num,mul_one]
      norm_cast
      rw [← abs_pow,abs_of_nonneg (by positivity)]
    · have heq : z=(z.re : ℂ) := by apply Complex.ext <;> simp [hz]
      rw [heq,Complex.norm_real,Real.norm_eq_abs]
      norm_cast
      rw [← abs_pow,abs_of_nonneg (by positivity)]
  rw [pow_mul,h4,← Complex.ofReal_pow,← pow_mul]

/-- Removing the origin zero leaves another even entire function positive on
both axes and strictly positive at the origin. The removed order is `4k`. -/
theorem exists_origin_four_power_factor {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (he : Function.Even f) (ha : AxisNonnegative f) (hn : ∃ z,f z≠0) :
    ∃ (k : ℕ) (g : ℂ → ℂ), Differentiable ℂ g ∧ Function.Even g ∧
      AxisNonnegative g ∧ (g 0).im=0 ∧ 0<(g 0).re ∧
      ∀ z,f z=z^(4*k)*g z := by
  by_cases h0 : f 0=0
  · let d := evenEntireSquareFactor f
    have hd := differentiable_evenEntireSquareFactor hf
    have hd0 : d 0=0 := by simpa [d] using (evenEntireSquareFactor_sq hf he 0).trans h0
    obtain ⟨z,hz⟩ := hn
    have hdn : d (z^2)≠0 := by simpa only [d,evenEntireSquareFactor_sq hf he] using hz
    obtain ⟨k,_,_,u,hu,huim,hupos,hdu⟩ := exists_even_order_factor_of_real_nonneg hd
      (fun x => (square_descent_nonnegative hf he ha x).1) hd0
      (Eventually.of_forall fun x => (square_descent_nonnegative hf he ha x).2) hdn
    let g := fun z : ℂ => u (z^2)
    have hg : Differentiable ℂ g := hu.comp (by fun_prop)
    have hfg (w : ℂ) : f w=w^(4*k)*g w := by
      rw [← evenEntireSquareFactor_sq hf he w]
      rw [hdu]
      simp only [Complex.ofReal_zero,sub_zero,g,← pow_mul]
      congr 1
      congr 1
      omega
    refine ⟨k,g,hg,fun w => by simp [g],?_,by simpa [g] using huim,
      by simpa [g] using hupos,hfg⟩
    intro w hw
    by_cases hw0 : w=0
    · subst w
      exact ⟨by simpa [g] using huim,by simpa [g] using hupos.le⟩
    have hp : 0<‖w‖^(4*k) := pow_pos (norm_pos_iff.mpr hw0) _
    have hq : g w=f w/((‖w‖^(4*k) : ℝ) : ℂ) := by
      rw [hfg w,axis_four_pow w hw]
      have hn : ((‖w‖^(4*k) : ℝ) : ℂ)≠0 := by exact_mod_cast hp.ne'
      rw [mul_div_cancel_left₀ _ hn]
    rw [hq,Complex.div_ofReal_im,Complex.div_ofReal_re]
    exact ⟨by rw [(ha w hw).1,zero_div],div_nonneg (ha w hw).2 hp.le⟩
  · have ha0 := ha 0 (Or.inl rfl)
    have hp : 0<(f 0).re := lt_of_le_of_ne ha0.2 (fun hh => h0 (Complex.ext hh.symm ha0.1))
    exact ⟨0,f,hf,he,ha,ha0.1,hp,by intro z; simp⟩

end GaloisForLFunctions.HTGeometry.EvenHermitianFactor
