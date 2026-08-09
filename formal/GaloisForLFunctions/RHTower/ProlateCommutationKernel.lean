import Mathlib
import GaloisForLFunctions.HTGeometry.SturmLagrangeIdentity

/-!
# The prolate operator commutes with the band kernel

The classical reason the eigenfunctions of the finite Fourier transform satisfy the prolate
differential equation is a single algebraic identity: the prolate operator applied to the kernel
`exp(i c x t)` in the variable `x` equals the same operator applied in the variable `t`.

```text
(1 - x²) ∂²ₓ k - 2x ∂ₓ k - c² x² k = (1 - t²) ∂²ₜ k - 2t ∂ₜ k - c² t² k.
```

Both sides equal `-(c² t² + c² x² - c² x² t² + 2 i c x t) k`.  The identity is exact and needs no
integration; the integrations by parts that turn it into the commutation of the operators are a
separate step, and their boundary terms vanish because `1 - t²` does at `t = ±1`.
-/

noncomputable section

open Complex

namespace RHTower

/-- The band kernel `exp(i c x t)`. -/
def bandKernel (c x t : ℝ) : ℂ := Complex.exp (Complex.I * ((c * x * t : ℝ) : ℂ))

theorem hasDerivAt_bandKernel_fst (c t x : ℝ) :
    HasDerivAt (fun y : ℝ => bandKernel c y t)
      (bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ))) x := by
  have hlin : HasDerivAt (fun y : ℝ => Complex.I * ((c * y * t : ℝ) : ℂ))
      (Complex.I * ((c * t : ℝ) : ℂ)) x := by
    have hid : HasDerivAt (fun y : ℝ => ((c * y * t : ℝ) : ℂ)) (((c * t : ℝ) : ℂ)) x := by
      have h : HasDerivAt (fun y : ℝ => c * y * t) (c * t) x := by
        simpa using ((hasDerivAt_id x).const_mul c).mul_const t
      exact h.ofReal_comp
    exact hid.const_mul Complex.I
  exact hlin.cexp

theorem hasDerivAt_bandKernel_snd (c x t : ℝ) :
    HasDerivAt (fun u : ℝ => bandKernel c x u)
      (bandKernel c x t * (Complex.I * ((c * x : ℝ) : ℂ))) t := by
  have hlin : HasDerivAt (fun u : ℝ => Complex.I * ((c * x * u : ℝ) : ℂ))
      (Complex.I * ((c * x : ℝ) : ℂ)) t := by
    have hid : HasDerivAt (fun u : ℝ => ((c * x * u : ℝ) : ℂ)) (((c * x : ℝ) : ℂ)) t := by
      have h : HasDerivAt (fun u : ℝ => c * x * u) (c * x) t := by
        simpa using (hasDerivAt_id t).const_mul (c * x)
      exact h.ofReal_comp
    exact hid.const_mul Complex.I
  exact hlin.cexp

/-- **The prolate operator acts identically on the two variables of the band kernel.**  This is the
commutation identity, before any integration by parts. -/
theorem prolate_bandKernel_symm (c x t : ℝ) :
    ((1 - ((x : ℝ) : ℂ) ^ 2) * (-(((c * t : ℝ) : ℂ)) ^ 2)
        - 2 * ((x : ℝ) : ℂ) * (Complex.I * ((c * t : ℝ) : ℂ))
        - ((c : ℝ) : ℂ) ^ 2 * ((x : ℝ) : ℂ) ^ 2) * bandKernel c x t
      = ((1 - ((t : ℝ) : ℂ) ^ 2) * (-(((c * x : ℝ) : ℂ)) ^ 2)
        - 2 * ((t : ℝ) : ℂ) * (Complex.I * ((c * x : ℝ) : ℂ))
        - ((c : ℝ) : ℂ) ^ 2 * ((t : ℝ) : ℂ) ^ 2) * bandKernel c x t := by
  have hcast : ((c * t : ℝ) : ℂ) = ((c : ℝ) : ℂ) * ((t : ℝ) : ℂ) := by push_cast; ring
  have hcast' : ((c * x : ℝ) : ℂ) = ((c : ℝ) : ℂ) * ((x : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, hcast']
  ring

theorem hasDerivAt_bandKernelDeriv_fst (c t x : ℝ) :
    HasDerivAt (fun y : ℝ => bandKernel c y t * (Complex.I * ((c * t : ℝ) : ℂ)))
      (bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ 2)) x := by
  have h := (hasDerivAt_bandKernel_fst c t x).mul_const (Complex.I * ((c * t : ℝ) : ℂ))
  refine h.congr_deriv ?_
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ)) * (Complex.I * ((c * t : ℝ) : ℂ))
      = bandKernel c x t * ((Complex.I * Complex.I) * ((c * t : ℝ) : ℂ) ^ 2) := by ring
    _ = bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ 2) := by rw [hI]; ring

theorem hasDerivAt_bandKernelDeriv_snd (c x t : ℝ) :
    HasDerivAt (fun u : ℝ => bandKernel c x u * (Complex.I * ((c * x : ℝ) : ℂ)))
      (bandKernel c x t * (-(((c * x : ℝ) : ℂ)) ^ 2)) t := by
  have h := (hasDerivAt_bandKernel_snd c x t).mul_const (Complex.I * ((c * x : ℝ) : ℂ))
  refine h.congr_deriv ?_
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc bandKernel c x t * (Complex.I * ((c * x : ℝ) : ℂ)) * (Complex.I * ((c * x : ℝ) : ℂ))
      = bandKernel c x t * ((Complex.I * Complex.I) * ((c * x : ℝ) : ℂ) ^ 2) := by ring
    _ = bandKernel c x t * (-(((c * x : ℝ) : ℂ)) ^ 2) := by rw [hI]; ring

/-- The prolate operator applied to a value, its first and its second derivative. -/
def prolateSymbol (c v dv ddv : ℂ) : ℂ := (1 - v ^ 2) * ddv - 2 * v * dv - (c : ℂ) ^ 2 * v ^ 2

/-- **The commutation identity, stated on the actual derivatives.**  Applying the prolate operator
to the band kernel in `x` and in `t` gives the same function. -/
theorem prolateSymbol_bandKernel_symm (c x t : ℝ) :
    prolateSymbol ((c : ℝ) : ℂ) ((x : ℝ) : ℂ)
        (Complex.I * ((c * t : ℝ) : ℂ)) (-(((c * t : ℝ) : ℂ)) ^ 2) * bandKernel c x t
      = prolateSymbol ((c : ℝ) : ℂ) ((t : ℝ) : ℂ)
        (Complex.I * ((c * x : ℝ) : ℂ)) (-(((c * x : ℝ) : ℂ)) ^ 2) * bandKernel c x t := by
  rw [prolateSymbol, prolateSymbol]
  exact prolate_bandKernel_symm c x t


/-- The prolate operator applied to a complex-valued function of a real variable, presented through
its value and its first two derivatives. -/
def prolateActionC (c : ℝ) (u Du DDu : ℝ → ℂ) (t : ℝ) : ℂ :=
  (1 - ((t : ℝ) : ℂ) ^ 2) * DDu t - 2 * ((t : ℝ) : ℂ) * Du t
    - ((c : ℝ) : ℂ) ^ 2 * ((t : ℝ) : ℂ) ^ 2 * u t

theorem hasDerivAt_prolateWeight (t : ℝ) :
    HasDerivAt (fun y : ℝ => ((1 - y ^ 2 : ℝ) : ℂ)) (((-2 * t : ℝ) : ℂ)) t := by
  have h : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * t) t := by
    simpa using ((hasDerivAt_pow 2 t).const_sub 1)
  exact h.ofReal_comp

/-- **The prolate operator is symmetric on the band.**  The weight `1 - t²` vanishes at both
endpoints, so the Lagrange boundary term vanishes and the two pairings agree.  The multiplication
part `-c² t² u` cancels between the two sides without any hypothesis. -/
theorem integral_prolate_pairing_eq_zero {c : ℝ} {u v Du Dv DDu DDv : ℝ → ℂ}
    (hu : ∀ x ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt u (Du x) x)
    (hv : ∀ x ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt v (Dv x) x)
    (hDu : ∀ x ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt Du (DDu x) x)
    (hDv : ∀ x ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt Dv (DDv x) x)
    (hint : IntervalIntegrable
      (fun t : ℝ => prolateActionC c u Du DDu t * v t - u t * prolateActionC c v Dv DDv t)
      MeasureTheory.volume (-1) 1) :
    (∫ t in (-1 : ℝ)..1,
        (prolateActionC c u Du DDu t * v t - u t * prolateActionC c v Dv DDv t)) = 0 := by
  have hcongr : ∀ t : ℝ,
      prolateActionC c u Du DDu t * v t - u t * prolateActionC c v Dv DDv t
        = (((-2 * t : ℝ) : ℂ) * Du t + ((1 - t ^ 2 : ℝ) : ℂ) * DDu t) * v t
          - u t * (((-2 * t : ℝ) : ℂ) * Dv t + ((1 - t ^ 2 : ℝ) : ℂ) * DDv t) := by
    intro t
    rw [prolateActionC, prolateActionC]
    push_cast
    ring
  have hint' : IntervalIntegrable
      (fun t : ℝ => (((-2 * t : ℝ) : ℂ) * Du t + ((1 - t ^ 2 : ℝ) : ℂ) * DDu t) * v t
        - u t * (((-2 * t : ℝ) : ℂ) * Dv t + ((1 - t ^ 2 : ℝ) : ℂ) * DDv t))
      MeasureTheory.volume (-1) 1 := by
    refine hint.congr ?_
    intro t _
    exact hcongr t
  have hmain := HTGeometry.integral_sturm_pairing_sub_complex_eq_zero
    (p := fun y : ℝ => ((1 - y ^ 2 : ℝ) : ℂ)) (Dp := fun y : ℝ => ((-2 * y : ℝ) : ℂ))
    (u := u) (v := v) (Du := Du) (Dv := Dv) (DDu := DDu) (DDv := DDv)
    (fun x _ => hasDerivAt_prolateWeight x) hu hv hDu hDv hint' (by norm_num) (by norm_num)
  rw [← hmain]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  exact hcongr t


theorem norm_bandKernel (c x t : ℝ) : ‖bandKernel c x t‖ = 1 := by
  rw [bandKernel, Complex.norm_exp]
  have hre : (Complex.I * ((c * x * t : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

theorem continuous_bandKernel_snd (c x : ℝ) : Continuous (fun t : ℝ => bandKernel c x t) :=
  Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))

/-- **Differentiation under the band integral.**  The kernel has modulus one and its `x`-derivative
modulus `|c t| ≤ |c|` on the band, so the dominated-convergence differentiation applies with the
integrable majorant `(|c| + 1) ‖f‖`. -/
theorem hasDerivAt_bandKernelTransform {c : ℝ} {f : ℝ → ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ t in (-1 : ℝ)..1, bandKernel c y t * f t)
      (∫ t in (-1 : ℝ)..1, bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t) x := by
  have huioc : Set.uIoc (-1 : ℝ) 1 = Set.Ioc (-1 : ℝ) 1 :=
    Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)
  have hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    rw [huioc]
    exact hf.1.aestronglyMeasurable
  have hKcont : ∀ y : ℝ, Continuous (fun t : ℝ =>
      bandKernel c y t * (Complex.I * ((c * t : ℝ) : ℂ))) := by
    intro y
    exact (continuous_bandKernel_snd c y).mul (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
  have hFm : ∀ y : ℝ, MeasureTheory.AEStronglyMeasurable (fun t : ℝ => bandKernel c y t * f t)
      (MeasureTheory.volume.restrict (Set.uIoc (-1 : ℝ) 1)) := fun y =>
    ((continuous_bandKernel_snd c y).aestronglyMeasurable).mul hfm
  have hF'm : ∀ y : ℝ, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => bandKernel c y t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t)
      (MeasureTheory.volume.restrict (Set.uIoc (-1 : ℝ) 1)) := fun y =>
    ((hKcont y).aestronglyMeasurable).mul hfm
  have hscale : IntervalIntegrable (fun t : ℝ => ((|c| + 1 : ℝ) : ℂ) * f t)
      MeasureTheory.volume (-1) 1 := hf.const_mul _
  have ht1 : ∀ t ∈ Set.uIoc (-1 : ℝ) 1, |t| ≤ 1 := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
    rw [abs_le]
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hFint : IntervalIntegrable (fun t : ℝ => bandKernel c x t * f t)
      MeasureTheory.volume (-1) 1 := by
    refine hscale.mono_fun (hFm x) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t _
    rw [norm_mul, norm_mul, norm_bandKernel, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |c| + 1)]
    nlinarith [norm_nonneg (f t), abs_nonneg c]
  have hbound : IntervalIntegrable (fun t : ℝ => (|c| + 1) * ‖f t‖)
      MeasureTheory.volume (-1) 1 := hf.norm.const_mul _
  have hdom : ∀ᵐ t : ℝ, t ∈ Set.uIoc (-1 : ℝ) 1 → ∀ y ∈ Set.univ,
      ‖bandKernel c y t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t‖ ≤ (|c| + 1) * ‖f t‖ := by
    filter_upwards with t ht _ _
    rw [norm_mul, norm_mul, norm_bandKernel, one_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have h := ht1 t ht
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg c) (norm_nonneg (f t)))
      (by linarith [h] : (0 : ℝ) ≤ 1 - |t|), norm_nonneg (f t), abs_nonneg c]
  have hderiv : ∀ᵐ t : ℝ, t ∈ Set.uIoc (-1 : ℝ) 1 → ∀ y ∈ Set.univ,
      HasDerivAt (fun z : ℝ => bandKernel c z t * f t)
        (bandKernel c y t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t) y := by
    filter_upwards with t _ y _
    exact (hasDerivAt_bandKernel_fst c t y).mul_const (f t)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun t =>
    (|c| + 1) * ‖f t‖) (F' := fun y t => bandKernel c y t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t)
    Filter.univ_mem (Filter.Eventually.of_forall fun y => hFm y) hFint (hF'm x) hdom hbound
    hderiv).2


theorem intervalIntegrable_kernelMul {f : ℝ → ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1) (g : ℝ → ℂ) (hg : Continuous g)
    (M : ℝ) (hM : ∀ t ∈ Set.uIoc (-1 : ℝ) 1, ‖g t‖ ≤ M) :
    IntervalIntegrable (fun t : ℝ => g t * f t) MeasureTheory.volume (-1) 1 := by
  have huioc : Set.uIoc (-1 : ℝ) 1 = Set.Ioc (-1 : ℝ) 1 :=
    Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)
  have hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    rw [huioc]; exact hf.1.aestronglyMeasurable
  have hM0 : (0 : ℝ) ≤ M := by
    have h0 : ((0 : ℝ)) ∈ Set.uIoc (-1 : ℝ) 1 := by
      rw [huioc]; constructor <;> norm_num
    exact le_trans (norm_nonneg _) (hM 0 h0)
  refine (hf.const_mul ((M : ℝ) : ℂ)).mono_fun
    ((hg.aestronglyMeasurable).mul hfm) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0]
  exact mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _)

theorem hasDerivAt_bandTransformDeriv {c : ℝ} {f : ℝ → ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1) (x : ℝ) :
    HasDerivAt (fun y : ℝ =>
        ∫ t in (-1 : ℝ)..1, bandKernel c y t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t)
      (∫ t in (-1 : ℝ)..1, bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ 2) * f t) x := by
  have hmul : IntervalIntegrable
      (fun t : ℝ => (Complex.I * ((c * t : ℝ) : ℂ)) * f t) MeasureTheory.volume (-1) 1 := by
    refine intervalIntegrable_kernelMul hf _ ?_ |c| ?_
    · exact continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.mul continuous_id))
    · intro t ht
      have hle : |t| ≤ 1 := by
        rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
        rw [abs_le]
        exact ⟨le_of_lt ht.1, ht.2⟩
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      nlinarith [abs_nonneg c, abs_nonneg t, hle]
  have h := hasDerivAt_bandKernelTransform (c := c) hmul x
  have hcongr1 : ∀ y : ℝ,
      (∫ t in (-1 : ℝ)..1, bandKernel c y t * ((Complex.I * ((c * t : ℝ) : ℂ)) * f t))
        = ∫ t in (-1 : ℝ)..1, bandKernel c y t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t := by
    intro y
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  have hcongr2 : (∫ t in (-1 : ℝ)..1, bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ))
        * ((Complex.I * ((c * t : ℝ) : ℂ)) * f t))
      = ∫ t in (-1 : ℝ)..1, bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ 2) * f t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    calc bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ))
          * ((Complex.I * ((c * t : ℝ) : ℂ)) * f t)
        = bandKernel c x t * ((Complex.I * Complex.I) * ((c * t : ℝ) : ℂ) ^ 2) * f t := by ring
      _ = bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ 2) * f t := by rw [hI]; ring
  rw [← hcongr2]
  simpa only [hcongr1] using h


theorem intervalIntegrable_bandKernel_mul {c : ℝ} {f : ℝ → ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1) (x : ℝ) (g : ℝ → ℂ)
    (hg : Continuous g) (M : ℝ) (hM : ∀ t ∈ Set.uIoc (-1 : ℝ) 1, ‖g t‖ ≤ M) :
    IntervalIntegrable (fun t : ℝ => bandKernel c x t * g t * f t)
      MeasureTheory.volume (-1) 1 := by
  refine intervalIntegrable_kernelMul hf (fun t => bandKernel c x t * g t)
    ((continuous_bandKernel_snd c x).mul hg) M (fun t ht => ?_)
  rw [norm_mul, norm_bandKernel, one_mul]
  exact hM t ht

/-- **The prolate operator, applied to the band transform, moves onto the kernel's second
variable.**  Combining the two differentiations with the pointwise kernel identity. -/
theorem prolateAction_bandTransform_eq {c : ℝ} {f : ℝ → ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1) (x : ℝ) :
    (1 - ((x : ℝ) : ℂ) ^ 2)
        * (∫ t in (-1 : ℝ)..1, bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ 2) * f t)
      - 2 * ((x : ℝ) : ℂ)
        * (∫ t in (-1 : ℝ)..1, bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t)
      - ((c : ℝ) : ℂ) ^ 2 * ((x : ℝ) : ℂ) ^ 2
        * (∫ t in (-1 : ℝ)..1, bandKernel c x t * f t)
      = ∫ t in (-1 : ℝ)..1,
          prolateSymbol ((c : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (Complex.I * ((c * x : ℝ) : ℂ)) (-(((c * x : ℝ) : ℂ)) ^ 2)
            * bandKernel c x t * f t := by
  have hle : ∀ t ∈ Set.uIoc (-1 : ℝ) 1, |t| ≤ 1 := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
    rw [abs_le]
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hi2 : IntervalIntegrable
      (fun t : ℝ => bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ 2) * f t)
      MeasureTheory.volume (-1) 1 := by
    refine intervalIntegrable_bandKernel_mul hf x _ ?_ (c ^ 2) (fun t ht => ?_)
    · exact (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).pow 2 |>.neg
    · rw [norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t, hle t ht]
      calc (|c| * |t|) ^ 2 = c ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs, sq_abs]
        _ ≤ c ^ 2 * 1 := by nlinarith [sq_nonneg c, ht2]
        _ = c ^ 2 := by ring
  have hi1 : IntervalIntegrable
      (fun t : ℝ => bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t)
      MeasureTheory.volume (-1) 1 := by
    refine intervalIntegrable_bandKernel_mul hf x _ ?_ |c| (fun t ht => ?_)
    · exact continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.mul continuous_id))
    · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      nlinarith [abs_nonneg c, abs_nonneg t, hle t ht]
  have hi0 : IntervalIntegrable (fun t : ℝ => bandKernel c x t * f t)
      MeasureTheory.volume (-1) 1 := by
    have := intervalIntegrable_bandKernel_mul (c := c) hf x (fun _ => 1) continuous_const 1
      (fun t _ => by norm_num)
    refine this.congr (fun t _ => ?_)
    ring
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hi2.const_mul _) (hi1.const_mul _),
    ← intervalIntegral.integral_sub ((hi2.const_mul _).sub (hi1.const_mul _))
      (hi0.const_mul _)]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  have hsym := prolate_bandKernel_symm c x t
  rw [prolateSymbol]
  have hexpand : (1 - ((x : ℝ) : ℂ) ^ 2) * (bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ 2) * f t)
      - 2 * ((x : ℝ) : ℂ) * (bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t)
      - ((c : ℝ) : ℂ) ^ 2 * ((x : ℝ) : ℂ) ^ 2 * (bandKernel c x t * f t)
      = (((1 - ((x : ℝ) : ℂ) ^ 2) * (-(((c * t : ℝ) : ℂ)) ^ 2)
          - 2 * ((x : ℝ) : ℂ) * (Complex.I * ((c * t : ℝ) : ℂ))
          - ((c : ℝ) : ℂ) ^ 2 * ((x : ℝ) : ℂ) ^ 2) * bandKernel c x t) * f t := by ring
  rw [hexpand, hsym]


/-- **The commutation of the prolate operator with the band transform.**  Applying the operator to
the transform of `f` is the transform of the operator applied to `f`. -/
theorem prolateAction_bandTransform_commutes {c : ℝ} {f Df DDf : ℝ → ℂ} (x : ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1)
    (hfd : ∀ y ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt f (Df y) y)
    (hfd2 : ∀ y ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt Df (DDf y) y)
    (hleft : IntervalIntegrable
      (fun t : ℝ => prolateActionC c (fun s => bandKernel c x s)
          (fun s => bandKernel c x s * (Complex.I * ((c * x : ℝ) : ℂ)))
          (fun s => bandKernel c x s * (-(((c * x : ℝ) : ℂ)) ^ 2)) t * f t)
      MeasureTheory.volume (-1) 1)
    (hright : IntervalIntegrable
      (fun t : ℝ => bandKernel c x t * prolateActionC c f Df DDf t)
      MeasureTheory.volume (-1) 1) :
    (1 - ((x : ℝ) : ℂ) ^ 2)
        * (∫ t in (-1 : ℝ)..1, bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ 2) * f t)
      - 2 * ((x : ℝ) : ℂ)
        * (∫ t in (-1 : ℝ)..1, bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t)
      - ((c : ℝ) : ℂ) ^ 2 * ((x : ℝ) : ℂ) ^ 2
        * (∫ t in (-1 : ℝ)..1, bandKernel c x t * f t)
      = ∫ t in (-1 : ℝ)..1, bandKernel c x t * prolateActionC c f Df DDf t := by
  have hpair := integral_prolate_pairing_eq_zero (c := c)
    (u := fun s : ℝ => bandKernel c x s)
    (Du := fun s : ℝ => bandKernel c x s * (Complex.I * ((c * x : ℝ) : ℂ)))
    (DDu := fun s : ℝ => bandKernel c x s * (-(((c * x : ℝ) : ℂ)) ^ 2))
    (v := f) (Dv := Df) (DDv := DDf)
    (fun y _ => hasDerivAt_bandKernel_snd c x y) hfd
    (fun y _ => hasDerivAt_bandKernelDeriv_snd c x y) hfd2 (hleft.sub hright)
  rw [intervalIntegral.integral_sub hleft hright] at hpair
  have hstep : (∫ t in (-1 : ℝ)..1, prolateActionC c (fun s => bandKernel c x s)
        (fun s => bandKernel c x s * (Complex.I * ((c * x : ℝ) : ℂ)))
        (fun s => bandKernel c x s * (-(((c * x : ℝ) : ℂ)) ^ 2)) t * f t)
      = ∫ t in (-1 : ℝ)..1, bandKernel c x t * prolateActionC c f Df DDf t :=
    sub_eq_zero.mp hpair
  rw [prolateAction_bandTransform_eq hf x, ← hstep]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [prolateSymbol, prolateActionC]
  ring


/-- The first derivative of a band-transform eigenfunction. -/
def bandEigenDeriv (c : ℝ) (χ : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  χ⁻¹ * ∫ t in (-1 : ℝ)..1, bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t

/-- Its second derivative. -/
def bandEigenSecondDeriv (c : ℝ) (χ : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  χ⁻¹ * ∫ t in (-1 : ℝ)..1, bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ 2) * f t

/-- **Regularity bootstrap.**  An eigenfunction of the band transform is differentiable, with the
derivative given by the transform against the differentiated kernel.  No smoothness of `f` is
assumed: it is inherited from the kernel. -/
theorem hasDerivAt_bandEigen {c : ℝ} {χ : ℂ} {f : ℝ → ℂ} (hχ : χ ≠ 0)
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1)
    (heig : ∀ y : ℝ, χ * f y = ∫ t in (-1 : ℝ)..1, bandKernel c y t * f t) (x : ℝ) :
    HasDerivAt f (bandEigenDeriv c χ f x) x := by
  have hbase : HasDerivAt (fun y : ℝ => χ⁻¹ * ∫ t in (-1 : ℝ)..1, bandKernel c y t * f t)
      (bandEigenDeriv c χ f x) x := by
    rw [bandEigenDeriv]
    exact (hasDerivAt_bandKernelTransform hf x).const_mul χ⁻¹
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards with y
  rw [← heig y, ← mul_assoc, inv_mul_cancel₀ hχ, one_mul]

/-- **The second derivative of a band eigenfunction.** -/
theorem hasDerivAt_bandEigenDeriv {c : ℝ} {χ : ℂ} {f : ℝ → ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1) (x : ℝ) :
    HasDerivAt (bandEigenDeriv c χ f) (bandEigenSecondDeriv c χ f x) x := by
  rw [bandEigenSecondDeriv]
  have hfun : bandEigenDeriv c χ f
      = fun y : ℝ => χ⁻¹ * ∫ t in (-1 : ℝ)..1,
          bandKernel c y t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t := by
    funext y
    rw [bandEigenDeriv]
  rw [hfun]
  exact (hasDerivAt_bandTransformDeriv hf x).const_mul χ⁻¹

/-- **A band eigenfunction is continuous**, hence interval-integrable on any interval. -/
theorem continuous_bandEigen {c : ℝ} {χ : ℂ} {f : ℝ → ℂ} (hχ : χ ≠ 0)
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1)
    (heig : ∀ y : ℝ, χ * f y = ∫ t in (-1 : ℝ)..1, bandKernel c y t * f t) :
    Continuous f :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_bandEigen hχ hf heig x).continuousAt


/-- **The prolate operator preserves the band eigenspace.**  If `f` is an eigenfunction of the band
transform with eigenvalue `χ`, so is `L f` with the same eigenvalue.  This is the classical
statement that the two operators share their eigenspaces; when `χ` is simple it forces `L f` to be
a multiple of `f`, i.e. the prolate eigen-equation. -/
theorem prolateAction_bandEigen_isEigen {c : ℝ} {χ : ℂ} {f : ℝ → ℂ} (hχ : χ ≠ 0)
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1)
    (heig : ∀ y : ℝ, χ * f y = ∫ t in (-1 : ℝ)..1, bandKernel c y t * f t) (x : ℝ)
    (hleft : IntervalIntegrable
      (fun t : ℝ => prolateActionC c (fun s => bandKernel c x s)
          (fun s => bandKernel c x s * (Complex.I * ((c * x : ℝ) : ℂ)))
          (fun s => bandKernel c x s * (-(((c * x : ℝ) : ℂ)) ^ 2)) t * f t)
      MeasureTheory.volume (-1) 1)
    (hright : IntervalIntegrable
      (fun t : ℝ => bandKernel c x t
        * prolateActionC c f (bandEigenDeriv c χ f) (bandEigenSecondDeriv c χ f) t)
      MeasureTheory.volume (-1) 1) :
    χ * prolateActionC c f (bandEigenDeriv c χ f) (bandEigenSecondDeriv c χ f) x
      = ∫ t in (-1 : ℝ)..1, bandKernel c x t
          * prolateActionC c f (bandEigenDeriv c χ f) (bandEigenSecondDeriv c χ f) t := by
  have hcomm := prolateAction_bandTransform_commutes (c := c) (f := f)
    (Df := bandEigenDeriv c χ f) (DDf := bandEigenSecondDeriv c χ f) x hf
    (fun y _ => hasDerivAt_bandEigen hχ hf heig y)
    (fun y _ => hasDerivAt_bandEigenDeriv hf y) hleft hright
  rw [← hcomm]
  have h0 : (∫ t in (-1 : ℝ)..1, bandKernel c x t * f t) = χ * f x := (heig x).symm
  have h1 : (∫ t in (-1 : ℝ)..1, bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t)
      = χ * bandEigenDeriv c χ f x := by
    rw [bandEigenDeriv, ← mul_assoc, mul_inv_cancel₀ hχ, one_mul]
  have h2 : (∫ t in (-1 : ℝ)..1, bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ 2) * f t)
      = χ * bandEigenSecondDeriv c χ f x := by
    rw [bandEigenSecondDeriv, ← mul_assoc, mul_inv_cancel₀ hχ, one_mul]
  rw [h0, h1, h2, prolateActionC]
  ring


/-- **Simplicity gives the prolate eigen-equation.**  If every band eigenfunction with eigenvalue
`χ` is a multiple of `f`, then `L f` is such a multiple, i.e. `f` solves the prolate differential
equation.  The simplicity hypothesis is a property of the operator's spectrum, not of the
differential equation; everything else here is unconditional. -/
theorem prolateAction_bandEigen_eq_smul {c : ℝ} {χ : ℂ} {f : ℝ → ℂ} (hχ : χ ≠ 0)
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1)
    (heig : ∀ y : ℝ, χ * f y = ∫ t in (-1 : ℝ)..1, bandKernel c y t * f t)
    (hleft : ∀ x : ℝ, IntervalIntegrable
      (fun t : ℝ => prolateActionC c (fun s => bandKernel c x s)
          (fun s => bandKernel c x s * (Complex.I * ((c * x : ℝ) : ℂ)))
          (fun s => bandKernel c x s * (-(((c * x : ℝ) : ℂ)) ^ 2)) t * f t)
      MeasureTheory.volume (-1) 1)
    (hright : ∀ x : ℝ, IntervalIntegrable
      (fun t : ℝ => bandKernel c x t
        * prolateActionC c f (bandEigenDeriv c χ f) (bandEigenSecondDeriv c χ f) t)
      MeasureTheory.volume (-1) 1)
    (hsimple : ∀ g : ℝ → ℂ,
      (∀ y : ℝ, χ * g y = ∫ t in (-1 : ℝ)..1, bandKernel c y t * g t) →
      ∃ α : ℂ, ∀ y : ℝ, g y = α * f y) :
    ∃ α : ℂ, ∀ x : ℝ,
      prolateActionC c f (bandEigenDeriv c χ f) (bandEigenSecondDeriv c χ f) x = α * f x :=
  hsimple _ (fun y => prolateAction_bandEigen_isEigen hχ hf heig y (hleft y) (hright y))


/-- The `n`-th transform of a band eigenfunction: the eigenfunction paired against the kernel
differentiated `n` times. -/
def bandTransformPow (c : ℝ) (χ : ℂ) (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  χ⁻¹ * ∫ t in (-1 : ℝ)..1, bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ)) ^ n * f t

theorem intervalIntegrable_kernelPow_mul {c : ℝ} {f : ℝ → ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1) (n : ℕ) :
    IntervalIntegrable
      (fun t : ℝ => (Complex.I * ((c * t : ℝ) : ℂ)) ^ n * f t) MeasureTheory.volume (-1) 1 := by
  refine intervalIntegrable_kernelMul hf _ ?_ (|c| ^ n) (fun t ht => ?_)
  · exact (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul continuous_id))).pow n
  · have hle : |t| ≤ 1 := by
      rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
      rw [abs_le]
      exact ⟨le_of_lt ht.1, ht.2⟩
    rw [norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    nlinarith [abs_nonneg c, abs_nonneg t, hle]

/-- **The tower of derivatives.**  Each transform in the tower differentiates to the next; the
argument is the same at every order because the kernel's derivative only raises the power of the
bounded factor `i c t`. -/
theorem hasDerivAt_bandTransformPow {c : ℝ} {χ : ℂ} {f : ℝ → ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1) (n : ℕ) (x : ℝ) :
    HasDerivAt (bandTransformPow c χ f n) (bandTransformPow c χ f (n + 1) x) x := by
  have hsrc := intervalIntegrable_kernelPow_mul (c := c) hf n
  have h := (hasDerivAt_bandKernelTransform (c := c) hsrc x).const_mul χ⁻¹
  have hfun : bandTransformPow c χ f n
      = fun y : ℝ => χ⁻¹ * ∫ t in (-1 : ℝ)..1,
          bandKernel c y t * ((Complex.I * ((c * t : ℝ) : ℂ)) ^ n * f t) := by
    funext y
    rw [bandTransformPow]
    congr 1
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  have hval : bandTransformPow c χ f (n + 1) x
      = χ⁻¹ * ∫ t in (-1 : ℝ)..1, bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ))
          * ((Complex.I * ((c * t : ℝ) : ℂ)) ^ n * f t) := by
    rw [bandTransformPow]
    congr 1
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  rw [hfun, hval]
  exact h

/-- The tower starts at the eigenfunction itself. -/
theorem bandTransformPow_zero {c : ℝ} {χ : ℂ} {f : ℝ → ℂ} (hχ : χ ≠ 0)
    (heig : ∀ y : ℝ, χ * f y = ∫ t in (-1 : ℝ)..1, bandKernel c y t * f t) :
    bandTransformPow c χ f 0 = f := by
  funext y
  rw [bandTransformPow]
  have hcongr : (∫ t in (-1 : ℝ)..1,
      bandKernel c y t * (Complex.I * ((c * t : ℝ) : ℂ)) ^ 0 * f t)
      = ∫ t in (-1 : ℝ)..1, bandKernel c y t * f t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  rw [hcongr, ← heig y, ← mul_assoc, inv_mul_cancel₀ hχ, one_mul]


/-- **The iterated derivatives of a band eigenfunction are the tower.** -/
theorem iteratedDeriv_bandEigen {c : ℝ} {χ : ℂ} {f : ℝ → ℂ} (hχ : χ ≠ 0)
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1)
    (heig : ∀ y : ℝ, χ * f y = ∫ t in (-1 : ℝ)..1, bandKernel c y t * f t) (n : ℕ) :
    iteratedDeriv n f = bandTransformPow c χ f n := by
  induction n with
  | zero =>
      rw [iteratedDeriv_zero, bandTransformPow_zero hχ heig]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hasDerivAt_bandTransformPow (χ := χ) hf n x).deriv

/-- **Every iterated derivative of a band eigenfunction is differentiable.**  The eigenfunction is
therefore smooth, with no regularity assumed anywhere. -/
theorem differentiable_iteratedDeriv_bandEigen {c : ℝ} {χ : ℂ} {f : ℝ → ℂ} (hχ : χ ≠ 0)
    (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1)
    (heig : ∀ y : ℝ, χ * f y = ∫ t in (-1 : ℝ)..1, bandKernel c y t * f t) (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n f) := by
  rw [iteratedDeriv_bandEigen hχ hf heig n]
  exact fun x => (hasDerivAt_bandTransformPow (χ := χ) hf n x).differentiableAt


end RHTower
