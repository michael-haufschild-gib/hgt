import GaloisForLFunctions.RHTower.Deninger.DeningerSuspensionNuclear

/-!
# Translation acts isometrically on the suspension

Translating a smooth periodic function multiplies each of its Fourier coefficients by a unit
complex number, because the kernel is a character and the integral over a period does not depend
on the interval chosen.  The coefficient seminorms only see the moduli of the coefficients, so
translation preserves every one of them.

By the functoriality of the projective tensor seminorm, translation in the suspension coordinate —
in particular a rational shift `t ↦ t − log q` — therefore acts continuously, indeed with norm at
most one, on the suspension tensor product.

* `deningerFourierKernel_add`, `_periodic'` : the kernel is a character of period `T`.
* `deningerFourierCoeff_translate` : **translating multiplies the coefficient by a phase.**
* `deningerTranslate` : translation on the smooth periodic test space.
* `deningerSmoothSeminorm_translate` : **translation is an isometry for every seminorm.**
* `deningerSuspensionTranslate_bounded`, `deningerSuspensionRationalShift_bounded` : **translations
  and rational shifts act continuously on the suspension.**
-/

namespace RHTower

open Complex intervalIntegral MeasureTheory

open scoped TensorProduct

section Kernel

/-- **The Fourier kernel is a character.** -/
theorem deningerFourierKernel_add (T : ℝ) (n : ℤ) (x y : ℝ) :
    deningerFourierKernel T n (x + y)
      = deningerFourierKernel T n x * deningerFourierKernel T n y := by
  simp only [deningerFourierKernel]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The kernel takes the value one at the period. -/
theorem deningerFourierKernel_period (T : ℝ) (hT : T ≠ 0) (n : ℤ) :
    deningerFourierKernel T n T = 1 := by
  rw [deningerFourierKernel]
  have hval : -(2 * Real.pi * Complex.I * n * (T : ℂ)) / T
      = (-n : ℤ) * (2 * Real.pi * Complex.I) := by
    have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT
    field_simp
    push_cast
    ring
  rw [hval, Complex.exp_int_mul_two_pi_mul_I]

/-- **The Fourier kernel has period `T`.** -/
theorem deningerFourierKernel_periodic' (T : ℝ) (hT : T ≠ 0) (n : ℤ) :
    Function.Periodic (deningerFourierKernel T n) T := by
  intro x
  rw [deningerFourierKernel_add, deningerFourierKernel_period T hT, mul_one]

end Kernel

section CoeffTranslate

/-- **Translating a periodic function multiplies its Fourier coefficients by a phase.**  The
kernel is a character, so the shift comes out of the integral, and the integral over one period
does not depend on the interval. -/
theorem deningerFourierCoeff_translate {T : ℝ} (hT : T ≠ 0) {f : ℝ → ℂ}
    (hper : Function.Periodic f T) (a : ℝ) (n : ℤ) :
    deningerFourierCoeff T (fun t => f (t - a)) n
      = deningerFourierKernel T n a * deningerFourierCoeff T f n := by
  set h : ℝ → ℂ := fun s => deningerFourierKernel T n (s + a) * f s with hh
  have hfun : (fun x => deningerFourierKernel T n x * f (x - a)) = fun x => h (x - a) := by
    funext x
    show deningerFourierKernel T n x * f (x - a)
      = deningerFourierKernel T n ((x - a) + a) * f (x - a)
    rw [sub_add_cancel]
  have hperh : Function.Periodic h T := by
    intro s
    show deningerFourierKernel T n ((s + T) + a) * f (s + T)
      = deningerFourierKernel T n (s + a) * f s
    rw [hper s]
    congr 1
    have hrw : (s + T) + a = (s + a) + T := by ring
    rw [hrw, deningerFourierKernel_periodic' T hT n (s + a)]
  have hshift : (∫ x in (0 : ℝ)..T, h (x - a)) = ∫ x in (0 : ℝ)..T, h x := by
    rw [intervalIntegral.integral_comp_sub_right h a]
    have hlow : (0 : ℝ) - a = -a := by ring
    have hhigh : T - a = -a + T := by ring
    rw [hlow, hhigh, hperh.intervalIntegral_add_eq (-a) 0, zero_add]
  have hconst : (∫ x in (0 : ℝ)..T, h x)
      = deningerFourierKernel T n a * ∫ x in (0 : ℝ)..T, deningerFourierKernel T n x * f x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    show deningerFourierKernel T n (x + a) * f x
      = deningerFourierKernel T n a * (deningerFourierKernel T n x * f x)
    rw [deningerFourierKernel_add]
    ring
  show (1 / T) * ∫ x in (0 : ℝ)..T, deningerFourierKernel T n x * f (x - a)
    = deningerFourierKernel T n a * ((1 / T) * ∫ x in (0 : ℝ)..T,
        deningerFourierKernel T n x * f x)
  rw [hfun, hshift, hconst]
  ring

/-- The modulus of a Fourier coefficient is unchanged by translation. -/
theorem deningerFourierCoeff_translate_norm {T : ℝ} (hT : T ≠ 0) {f : ℝ → ℂ}
    (hper : Function.Periodic f T) (a : ℝ) (n : ℤ) :
    ‖deningerFourierCoeff T (fun t => f (t - a)) n‖ = ‖deningerFourierCoeff T f n‖ := by
  rw [deningerFourierCoeff_translate hT hper a n, norm_mul, deningerFourierKernel_norm, one_mul]

end CoeffTranslate

section Translate

variable {T : ℝ}

/-- **Translation on the smooth periodic test space.** -/
noncomputable def deningerTranslate (T a : ℝ) :
    DeningerSmoothPeriodic T →ₗ[ℂ] DeningerSmoothPeriodic T where
  toFun f := ⟨fun t => (f : ℝ → ℂ) (t - a), by
    have hsub : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => t - a := by fun_prop
    refine ⟨(deningerSmoothPeriodic_contDiff f).comp hsub, fun t => ?_⟩
    show (f : ℝ → ℂ) ((t + T) - a) = (f : ℝ → ℂ) (t - a)
    have hrw : (t + T) - a = (t - a) + T := by ring
    rw [hrw, deningerSmoothPeriodic_periodic f (t - a)]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem deningerTranslate_apply (a : ℝ) (f : DeningerSmoothPeriodic T) :
    ((deningerTranslate T a f : DeningerSmoothPeriodic T) : ℝ → ℂ)
      = fun t => (f : ℝ → ℂ) (t - a) := rfl

/-- **Translation is an isometry for every coefficient seminorm**: it only multiplies the
coefficients by phases. -/
theorem deningerSmoothSeminorm_translate (hT : 0 < T) (k : ℕ) (a : ℝ)
    (f : DeningerSmoothPeriodic T) :
    deningerSmoothSeminorm hT k (deningerTranslate T a f) = deningerSmoothSeminorm hT k f := by
  rw [deningerSmoothSeminorm_apply, deningerSmoothSeminorm_apply, deningerKotheSeminorm_apply,
    deningerKotheSeminorm_apply]
  refine tsum_congr fun n => ?_
  congr 1
  exact deningerFourierCoeff_translate_norm hT.ne' (deningerSmoothPeriodic_periodic f) a n

end Translate

section Suspension

variable {Y : Type*} [TopologicalSpace Y] {T : ℝ}

local instance deningerSuspensionTranslateAddCommGroup
    (F : Submodule ℂ (DeningerTestSpaceC Y)) :
    AddCommGroup (TensorProduct ℂ ↥F ↥(DeningerSmoothPeriodic T)) :=
  @TensorProduct.addCommGroup ℂ _ ↥F ↥(DeningerSmoothPeriodic T) _ _ _ _

/-- **Translation in the suspension coordinate acts with norm at most one on the suspension**, for
every one of its seminorms. -/
theorem deningerSuspensionTranslate_bounded (hT : 0 < T)
    (F : Submodule ℂ (DeningerTestSpaceC Y)) (p : Seminorm ℂ (DeningerTestSpaceC Y)) (k : ℕ)
    (a : ℝ) (u : TensorProduct ℂ ↥F ↥(DeningerSmoothPeriodic T)) :
    deningerTensorSeminorm (deningerRestrictSeminorm F p) (deningerSmoothSeminorm hT k)
        (TensorProduct.map LinearMap.id (deningerTranslate T a) u)
      ≤ deningerTensorSeminorm (deningerRestrictSeminorm F p) (deningerSmoothSeminorm hT k) u := by
  have hbound := deningerTensorSeminorm_map_le (p := deningerRestrictSeminorm F p)
    (p' := deningerRestrictSeminorm F p) (q := deningerSmoothSeminorm hT k)
    (q' := deningerSmoothSeminorm hT k) (f := LinearMap.id)
    (g := deningerTranslate T a) zero_le_one zero_le_one
    (fun x => by rw [one_mul]; exact le_rfl)
    (fun y => by rw [one_mul, deningerSmoothSeminorm_translate hT k a y]) u
  rwa [one_mul, one_mul] at hbound

/-- **The rational shifts `t ↦ t − log q` act continuously on the suspension.** -/
theorem deningerSuspensionRationalShift_bounded (hT : 0 < T)
    (F : Submodule ℂ (DeningerTestSpaceC Y)) (p : Seminorm ℂ (DeningerTestSpaceC Y)) (k : ℕ)
    (q : ℚ) (u : TensorProduct ℂ ↥F ↥(DeningerSmoothPeriodic T)) :
    deningerTensorSeminorm (deningerRestrictSeminorm F p) (deningerSmoothSeminorm hT k)
        (TensorProduct.map LinearMap.id (deningerTranslate T (Real.log q)) u)
      ≤ deningerTensorSeminorm (deningerRestrictSeminorm F p) (deningerSmoothSeminorm hT k) u :=
  deningerSuspensionTranslate_bounded hT F p k (Real.log q) u

end Suspension

end RHTower
