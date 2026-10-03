import GaloisForLFunctions.RHTower.ThetaTailConfluentCenterLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Joint calculus of the actual theta tail kernel

The moving-tail identity gives joint continuity without a parameter-dependent
infinite-tail majorant. Differentiation then stays inside Schwartz correlations.
These are the literal integrals used by the center Schur kernel.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.ThetaJoint

open ThetaConfluent

def shifted (f : SchwartzMap ℝ ℝ) (x : ℝ) : SchwartzMap ℝ ℝ :=
  f.compSubConstCLM ℝ (-x)

theorem shifted_apply (f : SchwartzMap ℝ ℝ) (x t : ℝ) :
    shifted f x t = f (x+t) := by
  simp [shifted, SchwartzMap.compSubConstCLM_apply, add_comm]

def weighted (f : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => t) f

theorem weighted_apply (f : SchwartzMap ℝ ℝ) (t : ℝ) : weighted f t = t*f t := by
  have hg : (fun t : ℝ => t).HasTemperateGrowth := by fun_prop
  simp only [weighted, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]

def correlation (f g : SchwartzMap ℝ ℝ) (x y : ℝ) : ℝ :=
  ∫ t in Ioi 0, f (x+t)*g (y+t)

theorem correlation_integrable (f g : SchwartzMap ℝ ℝ) (x y : ℝ) :
    Integrable (fun t => f (x+t)*g (y+t)) := by
  simpa only [shifted_apply] using schwartzCorrelation_integrable (shifted f x) g y

theorem correlation_symm (f g : SchwartzMap ℝ ℝ) (x y : ℝ) :
    correlation f g x y = correlation g f y x := by
  simp only [correlation, mul_comm]

theorem correlation_movingTail (f g : SchwartzMap ℝ ℝ) (x y : ℝ) :
    correlation f g x y = correlation f g 0 (y-x) -
      ∫ t in (0 : ℝ)..x, f t*g ((y-x)+t) := by
  have hi := schwartzCorrelation_integrable f g (y-x)
  have ht : correlation f g x y = ∫ t in Ioi x, f t*g ((y-x)+t) := by
    rw [← setIntegral_Ioi_zero_comp_add_right (fun t => f t*g ((y-x)+t)) x]
    unfold correlation
    congr 1
    funext t
    congr 1 <;> congr 1 <;> ring
  have hs := intervalIntegral.integral_Ioi_sub_Ioi'
    (hi.integrableOn (s := Ioi 0)) (hi.integrableOn (s := Ioi x))
  rw [ht]
  simp only [correlation, zero_add]
  linarith only [hs]

theorem correlation_continuous (f g : SchwartzMap ℝ ℝ) :
    Continuous fun p : ℝ × ℝ => correlation f g p.1 p.2 := by
  have hc : Continuous (fun y => correlation f g 0 y) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    simpa only [correlation, zero_add] using
      (schwartzCorrelation_hasDerivAt f g y).continuousAt
  have hi : Continuous fun p : ℝ × ℝ =>
      ∫ t in (0 : ℝ)..p.1, f t*g ((p.2-p.1)+t) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun p : ℝ × ℝ => fun t : ℝ => f t*g ((p.2-p.1)+t))
    · exact (f.continuous.comp continuous_snd).mul
        (g.continuous.comp ((continuous_fst.snd.sub continuous_fst.fst).add continuous_snd))
    · exact continuous_fst
  have he : (fun p : ℝ × ℝ => correlation f g p.1 p.2) =
      (fun p : ℝ × ℝ => correlation f g 0 (p.2-p.1) -
        ∫ t in (0 : ℝ)..p.1, f t*g ((p.2-p.1)+t)) :=
    funext fun p => correlation_movingTail f g p.1 p.2
  rw [he]
  exact (hc.comp (continuous_snd.sub continuous_fst)).sub hi

theorem correlation_hasDerivAt_right (f g : SchwartzMap ℝ ℝ) (x y : ℝ) :
    HasDerivAt (correlation f g x)
      (correlation f (SchwartzMap.derivCLM ℝ ℝ g) x y) y := by
  unfold correlation
  simpa only [shifted_apply, SchwartzMap.derivCLM_apply] using
    schwartzCorrelation_hasDerivAt (shifted f x) g y

theorem correlation_hasDerivAt_left (f g : SchwartzMap ℝ ℝ) (x y : ℝ) :
    HasDerivAt (fun x => correlation f g x y)
      (correlation (SchwartzMap.derivCLM ℝ ℝ f) g x y) x := by
  rw [show (fun x => correlation f g x y) = correlation g f y from
    funext fun x => correlation_symm f g x y]
  simpa only [correlation_symm g] using correlation_hasDerivAt_right g f y x

def kernel (f g : SchwartzMap ℝ ℝ) (x y : ℝ) : ℝ :=
  (y-x)*correlation f g x y + 2*correlation (weighted f) g x y

theorem kernel_eq_integral (f g : SchwartzMap ℝ ℝ) (x y : ℝ) :
    kernel f g x y = ∫ t in Ioi 0, (x+y+2*t)*f (x+t)*g (y+t) := by
  have h₁ := ((correlation_integrable f g x y).const_mul (y-x)).integrableOn (s := Ioi 0)
  have h₂ := ((correlation_integrable (weighted f) g x y).const_mul 2).integrableOn (s := Ioi 0)
  unfold kernel correlation
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add h₁ h₂]
  apply integral_congr_ae
  filter_upwards with t
  rw [weighted_apply]
  ring

theorem kernel_symm (f g : SchwartzMap ℝ ℝ) (x y : ℝ) :
    kernel f g x y = kernel g f y x := by
  rw [kernel_eq_integral, kernel_eq_integral]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem kernel_continuous (f g : SchwartzMap ℝ ℝ) :
    Continuous fun p : ℝ × ℝ => kernel f g p.1 p.2 :=
  ((continuous_snd.sub continuous_fst).mul (correlation_continuous f g)).add
    (continuous_const.mul (correlation_continuous (weighted f) g))

theorem kernel_hasDerivAt_right (f g : SchwartzMap ℝ ℝ) (x y : ℝ) :
    HasDerivAt (kernel f g x)
      (correlation f g x y + kernel f (SchwartzMap.derivCLM ℝ ℝ g) x y) y := by
  convert! (((hasDerivAt_id y).sub_const x).mul
    (correlation_hasDerivAt_right f g x y)).add
      ((correlation_hasDerivAt_right (weighted f) g x y).const_mul 2) using 1
  simp only [kernel, id_eq]
  ring

theorem kernel_hasDerivAt_left (f g : SchwartzMap ℝ ℝ) (x y : ℝ) :
    HasDerivAt (fun x => kernel f g x y)
      (correlation f g x y + kernel (SchwartzMap.derivCLM ℝ ℝ f) g x y) x := by
  rw [show (fun x => kernel f g x y) = kernel g f y from
    funext fun x => kernel_symm f g x y]
  simpa only [kernel_symm g, correlation_symm g] using kernel_hasDerivAt_right g f y x

private theorem product_integrable (f g : SchwartzMap ℝ ℝ) :
    Integrable (fun t : ℝ => f t*g t) :=
  (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) f g).integrable

theorem correlation_origin_parts (f g : SchwartzMap ℝ ℝ) :
    correlation f (SchwartzMap.derivCLM ℝ ℝ g) 0 0 =
      -f 0*g 0-correlation (SchwartzMap.derivCLM ℝ ℝ f) g 0 0 := by
  let df := SchwartzMap.derivCLM ℝ ℝ f
  let dg := SchwartzMap.derivCLM ℝ ℝ g
  have hi : Integrable (fun t => df t*g t+f t*dg t) :=
    (product_integrable df g).add (product_integrable f dg)
  have hd (t : ℝ) : HasDerivAt (fun t => f t*g t) (df t*g t+f t*dg t) t :=
    (f.hasDerivAt t).mul (g.hasDerivAt t)
  have hl : Tendsto (fun t : ℝ => f t*g t) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (f.tendsto_cocompact.mono_left atTop_le_cocompact).mul
        (g.tendsto_cocompact.mono_left atTop_le_cocompact)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun t _ => hd t) hi.integrableOn hl
  rw [integral_add (product_integrable df g).integrableOn
    (product_integrable f dg).integrableOn] at h
  unfold correlation
  simp only [zero_add]
  dsimp only [df, dg] at h
  linarith only [h]

theorem kernel_origin_parts (f g : SchwartzMap ℝ ℝ) :
    kernel (SchwartzMap.derivCLM ℝ ℝ f) g 0 0 +
      kernel f (SchwartzMap.derivCLM ℝ ℝ g) 0 0 = -2*correlation f g 0 0 := by
  let df := SchwartzMap.derivCLM ℝ ℝ f
  let dg := SchwartzMap.derivCLM ℝ ℝ g
  have hi0 := product_integrable f g
  have hi1 : Integrable (fun t => t*df t*g t) := by
    simpa only [weighted_apply] using product_integrable (weighted df) g
  have hi2 : Integrable (fun t => t*f t*dg t) := by
    simpa only [weighted_apply] using product_integrable (weighted f) dg
  have hi : Integrable (fun t => f t*g t+t*df t*g t+t*f t*dg t) :=
    (hi0.add hi1).add hi2
  have hd (t : ℝ) : HasDerivAt (fun t => t*f t*g t)
      (f t*g t+t*df t*g t+t*f t*dg t) t := by
    convert! ((hasDerivAt_id t).mul (f.hasDerivAt t)).mul (g.hasDerivAt t) using 1
    dsimp [df, dg]
    ring
  have hl : Tendsto (fun t : ℝ => t*f t*g t) atTop (𝓝 0) := by
    simpa only [weighted_apply, mul_zero] using
      ((weighted f).tendsto_cocompact.mono_left atTop_le_cocompact).mul
        (g.tendsto_cocompact.mono_left atTop_le_cocompact)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun t _ => hd t) hi.integrableOn hl
  have hi01 : IntegrableOn (fun t => f t*g t+t*df t*g t) (Ioi 0) :=
    (hi0.add hi1).integrableOn
  rw [integral_add hi01 hi2.integrableOn,
    integral_add hi0.integrableOn hi1.integrableOn] at h
  simp only [kernel, correlation, sub_self, zero_mul, zero_add, weighted_apply]
  dsimp only [df, dg] at h
  simp only [zero_mul, sub_zero] at h
  linarith only [h]

theorem kernel_origin_diagonal (f : SchwartzMap ℝ ℝ) :
    kernel f (SchwartzMap.derivCLM ℝ ℝ f) 0 0 = -correlation f f 0 0 := by
  have h := kernel_origin_parts f f
  rw [kernel_symm (SchwartzMap.derivCLM ℝ ℝ f)] at h
  linarith only [h]

theorem source_kernel_eq (x y : ℝ) :
    kernel thetaCuspSchwartzReal thetaCuspSchwartzReal x y =
      thetaTailFirstMomentKernel x y := by
  rw [kernel_eq_integral, thetaTailFirstMomentKernel_eq_shiftTail]
  simp only [thetaCuspSchwartzReal_apply]

theorem source_kernel_continuous :
    Continuous fun p : ℝ × ℝ => thetaTailFirstMomentKernel p.1 p.2 := by
  simpa only [source_kernel_eq] using
    kernel_continuous thetaCuspSchwartzReal thetaCuspSchwartzReal

end RHTower.ThetaJoint
