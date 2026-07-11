import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Translation on Schwartz space

Mathlib supplies composition of a Schwartz function with a temperate antilipschitz map, but does
not package additive translation as a named continuous linear action.  This module builds that
action, proves its group law, inverse law, continuity for each fixed translation parameter, and
commutation with directional differentiation.  It is the reusable first layer needed to turn a
momentum-symmetry identity for a continuous Schwartz form into simultaneous-translation
invariance.
-/

open Function

namespace SchwartzMap

open LineDeriv

variable (𝕜 : Type*) {E F : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

/-- Right translation `f(x) ↦ f(x + a)` as a continuous linear map on Schwartz space. -/
def translateCLM (a : E) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) := by
  have hg : (fun x : E => x + a).HasTemperateGrowth :=
    Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const a)
  have hi : Isometry (fun x : E => x + a) := by
    apply Isometry.of_dist_eq
    intro x y
    simp [dist_eq_norm]
  exact SchwartzMap.compCLMOfAntilipschitz 𝕜 hg hi.antilipschitz

@[simp] theorem translateCLM_apply (a : E) (f : 𝓢(E, F)) (x : E) :
    translateCLM 𝕜 a f x = f (x + a) := rfl

@[simp] theorem translateCLM_zero (f : 𝓢(E, F)) :
    translateCLM 𝕜 (0 : E) f = f := by
  ext x
  simp

/-- The right-translation convention gives `T_a T_b = T_(a+b)`. -/
theorem translateCLM_add (a b : E) (f : 𝓢(E, F)) :
    translateCLM 𝕜 a (translateCLM 𝕜 b f) = translateCLM 𝕜 (a + b) f := by
  ext x
  simp [add_assoc]

@[simp] theorem translateCLM_neg_left (a : E) (f : 𝓢(E, F)) :
    translateCLM 𝕜 (-a) (translateCLM 𝕜 a f) = f := by
  rw [translateCLM_add, neg_add_cancel, translateCLM_zero]

@[simp] theorem translateCLM_neg_right (a : E) (f : 𝓢(E, F)) :
    translateCLM 𝕜 a (translateCLM 𝕜 (-a) f) = f := by
  rw [translateCLM_add, add_neg_cancel, translateCLM_zero]

/-- Translation commutes with every Schwartz directional derivative. -/
theorem lineDerivOp_translateCLM (a m : E) (f : 𝓢(E, F)) :
    ∂_{m} (translateCLM 𝕜 a f) = translateCLM 𝕜 a (∂_{m} f) := by
  ext x
  rw [lineDerivOp_apply_eq_fderiv]
  simp only [translateCLM_apply]
  rw [lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (fun y : E => f (y + a)) x m = fderiv ℝ f (x + a) m
  have hshift : HasFDerivAt (fun y : E => y + a) (ContinuousLinearMap.id ℝ E) x := by
    simpa only [id_eq] using (hasFDerivAt_id (𝕜 := ℝ) x).add_const a
  have hcomp := (f.hasFDerivAt (x + a)).comp x hshift
  have hfderiv := hcomp.fderiv
  change (fderiv ℝ (f ∘ fun y : E => y + a) x) m = fderiv ℝ f (x + a) m
  rw [hfderiv]
  rfl

/-! ## One-dimensional strong-orbit infrastructure -/

/-- Difference quotient for the real translation parameter on complex-valued Schwartz space. -/
noncomputable def translateDifferenceQuotient (a h : ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (h⁻¹ : ℝ) • (translateCLM ℂ (a + h) f - translateCLM ℂ a f)

/-- Difference between the translation difference quotient and its candidate Schwartz derivative. -/
noncomputable def translateDifferenceQuotientError (a h : ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  translateDifferenceQuotient a h f - translateCLM ℂ a (derivCLM ℂ ℂ f)

/-- Every derivative of the translation difference-quotient error is the corresponding ordinary
difference quotient of the iterated derivative.  This is the exact algebraic reduction required
before proving convergence in every Schwartz seminorm. -/
theorem iteratedDeriv_translateDifferenceQuotientError
    (a h x : ℝ) (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    iteratedDeriv n (translateDifferenceQuotientError a h f) x =
      (h⁻¹ : ℝ) •
        (iteratedDeriv n f (x + (a + h)) - iteratedDeriv n f (x + a)) -
          iteratedDeriv (n + 1) f (x + a) := by
  change iteratedDeriv n
      (fun y : ℝ => (h⁻¹ : ℝ) • (f (y + (a + h)) - f (y + a)) - deriv f (y + a)) x = _
  have h₁ : ContDiffAt ℝ n (fun y : ℝ => f (y + (a + h))) x :=
    ((f.smooth n).comp (contDiff_id.add contDiff_const)).contDiffAt
  have h₂ : ContDiffAt ℝ n (fun y : ℝ => f (y + a)) x :=
    ((f.smooth n).comp (contDiff_id.add contDiff_const)).contDiffAt
  have hd : ContDiffAt ℝ n (fun y : ℝ => deriv f (y + a)) x := by
    simpa only [derivCLM_apply] using
      (((derivCLM ℂ ℂ f).smooth n).comp (contDiff_id.add contDiff_const)).contDiffAt
  have hsub : iteratedDeriv n
      (fun y : ℝ => f (y + (a + h)) - f (y + a)) x =
      iteratedDeriv n f (x + (a + h)) - iteratedDeriv n f (x + a) := by
    change iteratedDeriv n
      ((fun y : ℝ => f (y + (a + h))) - (fun y : ℝ => f (y + a))) x = _
    rw [iteratedDeriv_sub h₁ h₂]
    exact congrArg₂ (· - ·)
      (congrFun (iteratedDeriv_comp_add_const n f (a + h)) x)
      (congrFun (iteratedDeriv_comp_add_const n f a) x)
  have hderivshift : iteratedDeriv n (fun y : ℝ => deriv f (y + a)) x =
      iteratedDeriv (n + 1) f (x + a) := by
    rw [congrFun (iteratedDeriv_comp_add_const n (deriv f) a) x]
    rw [congrFun iteratedDeriv_succ' (x + a)]
  change iteratedDeriv n
      (((h⁻¹ : ℝ) • (fun y : ℝ => f (y + (a + h)) - f (y + a))) -
        (fun y : ℝ => deriv f (y + a))) x = _
  calc
    _ = iteratedDeriv n ((h⁻¹ : ℝ) •
          (fun y : ℝ => f (y + (a + h)) - f (y + a))) x -
        iteratedDeriv n (fun y : ℝ => deriv f (y + a)) x :=
      iteratedDeriv_sub ((h₁.sub h₂).const_smul (h⁻¹ : ℝ)) hd
    _ = (h⁻¹ : ℝ) • iteratedDeriv n
          (fun y : ℝ => f (y + (a + h)) - f (y + a)) x -
        iteratedDeriv n (fun y : ℝ => deriv f (y + a)) x := by
      rw [iteratedDeriv_const_smul (h₁.sub h₂) (h⁻¹ : ℝ)]
    _ = _ := by
      rw [hsub, hderivshift]

/-- Uniform weighted derivative control under a bounded translation.  This supplies the precise
Schwartz-seminorm majorant needed for the Taylor remainder in the translation parameter. -/
theorem weighted_iteratedDeriv_translate_bound
    (f : 𝓢(ℝ, ℂ)) (a t x : ℝ) (k m : ℕ) (ht : |t| ≤ 1) :
    |x| ^ k * ‖iteratedDeriv m f (x + a + t)‖ ≤
      (2 + |a|) ^ k *
        (2 ^ k * ((Finset.Iic (k, m)).sup
          (fun p => SchwartzMap.seminorm ℂ p.1 p.2)) f) := by
  let z : ℝ := x + a + t
  have hxtriangle : |x| ≤ |z| + |a| + |t| := by
    have hident : z + -a + -t = x := by dsimp [z]; ring
    rw [← hident]
    calc
      |z + -a + -t| ≤ |z + -a| + |-t| := abs_add_le _ _
      _ ≤ |z| + |-a| + |-t| := by gcongr; exact abs_add_le z (-a)
      _ = |z| + |a| + |t| := by rw [abs_neg, abs_neg]
  have hx : |x| ≤ (2 + |a|) * (1 + |z|) := by
    have ha : 0 ≤ |a| := abs_nonneg a
    have hz : 0 ≤ |z| := abs_nonneg z
    calc
      |x| ≤ |z| + |a| + |t| := hxtriangle
      _ ≤ |z| + |a| + 1 := by linarith
      _ ≤ (2 + |a|) * (1 + |z|) := by nlinarith
  have hbase := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (k, m)) (k := k) (n := m) le_rfl le_rfl f z
  rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hbase
  calc
    |x| ^ k * ‖iteratedDeriv m f z‖ ≤
        ((2 + |a|) * (1 + |z|)) ^ k * ‖iteratedDeriv m f z‖ := by
      gcongr
    _ = (2 + |a|) ^ k *
        ((1 + |z|) ^ k * ‖iteratedDeriv m f z‖) := by rw [mul_pow]; ring
    _ ≤ (2 + |a|) ^ k *
        (2 ^ k * ((Finset.Iic (k, m)).sup
          (fun p => SchwartzMap.seminorm ℂ p.1 p.2)) f) := by
      gcongr

end SchwartzMap
