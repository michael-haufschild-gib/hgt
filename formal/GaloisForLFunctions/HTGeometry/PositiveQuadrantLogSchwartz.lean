import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Schwartz logarithmic profiles and full two-variable Mellin inversion

For every Schwartz function on the plane, the reflected logarithmic pullback
weighted by exp(-2u-2v) is Schwartz. Its Fréchet derivative has the same
form with a Schwartz-valued gradient. Induction therefore reduces every
mixed derivative estimate to a single bound valid in all four quadrants.

Fourier inversion of this full logarithmic profile gives absolutely
integrable two-variable Mellin inversion on the line with real parts two.
No vanishing at either coordinate boundary is required.
-/

noncomputable section
open scoped BigOperators ContDiff SchwartzMap Topology
open MeasureTheory Set Filter
namespace HTGeometry

abbrev QuadrantLogSpace := EuclideanSpace ℝ (Fin 2)
private abbrev E := QuadrantLogSpace
private def coord (i : Fin 2) : E →L[ℝ] ℝ := EuclideanSpace.proj i

def quadrantLogBasis (i : Fin 2) : E := WithLp.toLp 2 (Pi.single i 1)

def quadrantLogNode (u : E) : E :=
  Real.exp (-u 0) • quadrantLogBasis 0 + Real.exp (-u 1) • quadrantLogBasis 1

theorem quadrantLogNode_apply (u : E) (i : Fin 2) :
    quadrantLogNode u i=Real.exp (-u i) := by
  fin_cases i <;> simp [quadrantLogNode,quadrantLogBasis]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def quadrantLogWeight (f : SchwartzMap E F) (u : E) : F :=
  Real.exp (-2*u 0-2*u 1) • f (quadrantLogNode u)

private lemma coordinate_growth (i : Fin 2) : (fun u : E => u i).HasTemperateGrowth :=
  (coord i).hasTemperateGrowth

def quadrantLogEuler (i : Fin 2) (f : SchwartzMap E F) : SchwartzMap E F :=
  (-2 : ℝ) • f - SchwartzMap.smulLeftCLM F (fun u : E => u i)
    (SchwartzMap.evalCLM ℝ E F (quadrantLogBasis i) (SchwartzMap.fderivCLM ℝ E F f))

def quadrantLogGradient (f : SchwartzMap E F) : SchwartzMap E (E →L[ℝ] F) :=
  (quadrantLogEuler 0 f).postcompCLM
    ((ContinuousLinearMap.smulRightL ℝ E F) (coord 0)) +
  (quadrantLogEuler 1 f).postcompCLM
    ((ContinuousLinearMap.smulRightL ℝ E F) (coord 1))


private lemma gradient_apply (f : SchwartzMap E F) (x v : E) :
    quadrantLogGradient f x v =
      v 0 • ((-2 : ℝ) • f x - x 0 • (fderiv ℝ f x (quadrantLogBasis 0))) +
      v 1 • ((-2 : ℝ) • f x - x 1 • (fderiv ℝ f x (quadrantLogBasis 1))) := by
  simp [quadrantLogGradient,quadrantLogEuler,SchwartzMap.smulLeftCLM_apply_apply
    (coordinate_growth _),SchwartzMap.fderivCLM_apply,coord]
  module

private lemma logNode_hasFDeriv (u : E) :
    HasFDerivAt quadrantLogNode
      (((-Real.exp (-u 0)) • (coord 0)).smulRight (quadrantLogBasis 0) +
       ((-Real.exp (-u 1)) • (coord 1)).smulRight (quadrantLogBasis 1)) u := by
  have h (i : Fin 2) := (((coord i).hasFDerivAt (x := u)).neg.exp).smul_const
    (quadrantLogBasis i)
  apply ((h 0).add (h 1)).congr_fderiv
  ext v
  simp [coord]

private lemma logWeight_hasFDeriv (f : SchwartzMap E F) (u : E) :
    HasFDerivAt (quadrantLogWeight f) (quadrantLogWeight (quadrantLogGradient f) u) u := by
  have he := logNode_hasFDeriv u
  have hw : HasFDerivAt (fun v : E => Real.exp (-2*v 0-2*v 1))
      (Real.exp (-2*u 0-2*u 1) •
        ((-2 : ℝ) • coord 0 - (2 : ℝ) • coord 1)) u :=
    (((coord 0).hasFDerivAt.const_mul (-2)).sub
      ((coord 1).hasFDerivAt.const_mul 2)).exp
  have hf := (f.differentiableAt.hasFDerivAt.comp u he)
  apply (hw.smul hf).congr_fderiv
  ext v
  simp only [quadrantLogWeight,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    sub_apply,gradient_apply,quadrantLogNode_apply]
  dsimp [coord]
  simp only [map_add,map_smul,smul_add,smul_sub,smul_smul]
  module

private lemma logWeight_fderiv (f : SchwartzMap E F) :
    fderiv ℝ (quadrantLogWeight f)=quadrantLogWeight (quadrantLogGradient f) := by
  funext u
  exact (logWeight_hasFDeriv f u).fderiv

private lemma logWeight_smooth (f : SchwartzMap E F) : ContDiff ℝ ∞ (quadrantLogWeight f) := by
  have hn : ContDiff ℝ ∞ quadrantLogNode := by
    unfold quadrantLogNode
    fun_prop
  exact (by fun_prop : ContDiff ℝ ∞ (fun v : E => Real.exp (-2*v 0-2*v 1))).smul
    ((f.smooth ⊤).comp hn)

private lemma logWeight_decay (f : SchwartzMap E F) (k : ℕ) :
    ∃ C : ℝ, ∀ u : E, ‖u‖^k*‖quadrantLogWeight f u‖ ≤ C := by
  let C : ℝ := 2^6*(Finset.Iic (6,0)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) f
  have hC : 0 ≤ C := by positivity
  refine ⟨(k.factorial : ℝ)*C,?_⟩
  intro u
  let S : ℝ := |u 0|+|u 1|
  let B : ℝ := 1+‖quadrantLogNode u‖
  have hB : 1 ≤ B := by dsimp [B]; exact le_add_of_nonneg_right (norm_nonneg _)
  have hu : ‖u‖ ≤ S := by
    have h := EuclideanSpace.norm_sq_eq u
    simp only [Fin.sum_univ_two,Real.norm_eq_abs] at h
    dsimp [S]
    nlinarith [norm_nonneg u,abs_nonneg (u 0),abs_nonneg (u 1)]
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hc (i : Fin 2) : Real.exp (-2*u i+|u i|) ≤ B^3 := by
    by_cases hi : 0 ≤ u i
    · rw [abs_of_nonneg hi]
      calc
        _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        _ ≤ B^3 := one_le_pow₀ hB
    · rw [abs_of_nonpos (le_of_not_ge hi)]
      have hp : Real.exp (-u i) ≤ B := by
        have h := PiLp.norm_apply_le (quadrantLogNode u) i
        rw [quadrantLogNode_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at h
        dsimp [B]
        linarith
      calc
        _ = (Real.exp (-u i))^3 := by rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
        _ ≤ B^3 := pow_le_pow_left₀ (Real.exp_nonneg _) hp 3
  have hexp : Real.exp (-2*u 0-2*u 1)*Real.exp S ≤ B^6 := by
    calc
      _ = Real.exp (-2*u 0+|u 0|)*Real.exp (-2*u 1+|u 1|) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        dsimp [S]
        ring
      _ ≤ B^3*B^3 := mul_le_mul (hc 0) (hc 1) (Real.exp_nonneg _) (by positivity)
      _ = B^6 := by ring
  have hbound : B^6*‖f (quadrantLogNode u)‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (6,0))
        (k := 6) (n := 0) le_rfl le_rfl f (quadrantLogNode u))
  have hp : ‖u‖^k ≤ (k.factorial : ℝ)*Real.exp S := by
    apply (pow_le_pow_left₀ (norm_nonneg _) hu k).trans
    have h := Real.pow_div_factorial_le_exp S hS k
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mp h |>.trans_eq (mul_comm _ _)
  rw [quadrantLogWeight,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ ((k.factorial : ℝ)*Real.exp S)*
        (Real.exp (-2*u 0-2*u 1)*‖f (quadrantLogNode u)‖) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = (k.factorial : ℝ)*(Real.exp (-2*u 0-2*u 1)*Real.exp S*‖f (quadrantLogNode u)‖) := by ring
    _ ≤ (k.factorial : ℝ)*(B^6*‖f (quadrantLogNode u)‖) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

private lemma logWeight_derivative_decay (n k : ℕ) :
    ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F),
      ∃ C : ℝ, ∀ u : E, ‖u‖^k*‖iteratedFDeriv ℝ n (quadrantLogWeight f) u‖ ≤ C := by
  induction n with
  | zero =>
    intro F _ _ f
    simpa only [norm_iteratedFDeriv_zero] using logWeight_decay f k
  | succ n ih =>
    intro F _ _ f
    obtain ⟨C,hC⟩ := ih (quadrantLogGradient f)
    refine ⟨C,fun u => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv,logWeight_fderiv]
    exact hC u

def quadrantLogSchwartz (f : SchwartzMap E F) : SchwartzMap E F where
  toFun := quadrantLogWeight f
  smooth' := logWeight_smooth f
  decay' k n := logWeight_derivative_decay n k f

theorem quadrantLogSchwartz_apply (f : SchwartzMap E F) (u : E) :
    quadrantLogSchwartz f u=Real.exp (-2*u 0-2*u 1) • f (quadrantLogNode u) := rfl

open scoped FourierTransform

def quadrantMellinLine (t : ℝ) : ℂ := 2+(2*Real.pi*t : ℝ)*Complex.I

def quadrantMellinProfile (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  𝓕 (quadrantLogSchwartz f)

def quadrantMellinKernel (x y : ℝ) (v : E) : ℂ :=
  (x : ℂ)^(-quadrantMellinLine (v 0))*(y : ℂ)^(-quadrantMellinLine (v 1))

theorem norm_quadrantMellinKernel {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (v : E) :
    ‖quadrantMellinKernel x y v‖=x^(-2 : ℝ)*y^(-2 : ℝ) := by
  rw [quadrantMellinKernel,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp [quadrantMellinLine]

private lemma kernel_phase {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (v : E) :
    (Real.exp (2*Real.log x+2*Real.log y) : ℂ)*quadrantMellinKernel x y v=
      Complex.exp ((2*Real.pi*inner ℝ v
        (WithLp.toLp 2 ![-Real.log x,-Real.log y] : E) : ℝ)*Complex.I) := by
  rw [quadrantMellinKernel,Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'),
    ← Complex.ofReal_log hx.le,← Complex.ofReal_log hy.le,Complex.ofReal_exp,
    ← Complex.exp_add,← Complex.exp_add]
  congr 1
  simp only [quadrantMellinLine,PiLp.inner_apply,Fin.sum_univ_two,Real.inner_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring

/-- Full two-variable Mellin inversion on the line with real parts two.
The profile contains both variables and is integrable without extra premises. -/
theorem quadrantMellin_inversion (f : SchwartzMap E ℂ)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ v : E, quadrantMellinKernel x y v*quadrantMellinProfile f v)=
      f (WithLp.toLp 2 ![x,y]) := by
  let u : E := WithLp.toLp 2 ![-Real.log x,-Real.log y]
  have he : quadrantLogNode u=WithLp.toLp 2 ![x,y] := by
    ext i
    fin_cases i <;> simp [quadrantLogNode_apply,u,Real.exp_log hx,Real.exp_log hy]
  have h := congrArg (fun g : SchwartzMap E ℂ => g u)
    (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap E ℂ) (quadrantLogSchwartz f))
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq'] at h
  change (∫ v : E, Complex.exp ((2*Real.pi*inner ℝ v u : ℝ)*Complex.I)*
    quadrantMellinProfile f v)=quadrantLogSchwartz f u at h
  rw [quadrantLogSchwartz_apply,he] at h
  have hw : Real.exp (-2*u 0-2*u 1)=Real.exp (2*Real.log x+2*Real.log y) := by
    dsimp [u]
    congr 1
    ring
  rw [hw,Complex.real_smul] at h
  apply mul_left_cancel₀ (show (Real.exp (2*Real.log x+2*Real.log y) : ℂ) ≠ 0 by
    exact_mod_cast (Real.exp_pos _).ne')
  rw [← integral_const_mul]
  calc
    _ = ∫ v : E, Complex.exp ((2*Real.pi*inner ℝ v u : ℝ)*Complex.I)*
        quadrantMellinProfile f v := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [← mul_assoc,kernel_phase hx hy]
    _ = _ := h

theorem continuous_quadrantMellinKernel {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Continuous (quadrantMellinKernel x y) := by
  have h (i : Fin 2) : Continuous (fun v : E => -quadrantMellinLine (v i)) := by
    unfold quadrantMellinLine
    fun_prop
  exact ((h 0).const_cpow (Or.inl (by exact_mod_cast hx.ne'))).mul
    ((h 1).const_cpow (Or.inl (by exact_mod_cast hy.ne')))

theorem integrable_quadrantMellin_inversion (f : SchwartzMap E ℂ)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Integrable (fun v : E => quadrantMellinKernel x y v*quadrantMellinProfile f v) := by
  have hc := continuous_quadrantMellinKernel hx hy
  apply ((quadrantMellinProfile f).integrable.norm.const_mul
    (x^(-2 : ℝ)*y^(-2 : ℝ))).mono' (hc.mul (quadrantMellinProfile f).continuous).aestronglyMeasurable
  filter_upwards [] with v
  change ‖quadrantMellinKernel x y v*quadrantMellinProfile f v‖ ≤ _
  rw [norm_mul,norm_quadrantMellinKernel hx hy]


end HTGeometry
