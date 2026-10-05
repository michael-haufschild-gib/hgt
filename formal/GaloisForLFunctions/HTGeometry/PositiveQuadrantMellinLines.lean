import GaloisForLFunctions.HTGeometry.PositiveQuadrantLogSchwartz
/-!
# Full two-variable Mellin inversion on arbitrary positive lines

For every positive pair of real parts, the weighted logarithmic pullback
of every planar Schwartz function is Schwartz. A positive exponential margin
absorbs all logarithmic powers, and the exact Schwartz-valued gradient closes
all mixed derivatives. Fourier inversion supplies the full integrable profile
on these lines. No coordinate-boundary vanishing condition is imposed.
-/

noncomputable section
open scoped BigOperators ContDiff SchwartzMap Topology
open MeasureTheory Set Filter
namespace HTGeometry.PositiveLine
private abbrev E := QuadrantLogSpace
private def coord (i : Fin 2) : E →L[ℝ] ℝ := EuclideanSpace.proj i
variable (σ : Fin 2 → {r : ℝ // 0 < r})
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def quadrantLogWeight (f : SchwartzMap E F) (u : E) : F :=
  Real.exp (-(σ 0 : ℝ)*u 0-(σ 1 : ℝ)*u 1) • f (quadrantLogNode u)

private lemma coordinate_growth (i : Fin 2) : (fun u : E => u i).HasTemperateGrowth :=
  (coord i).hasTemperateGrowth

def quadrantLogEuler (i : Fin 2) (f : SchwartzMap E F) : SchwartzMap E F :=
  (-(σ i : ℝ)) • f - SchwartzMap.smulLeftCLM F (fun u : E => u i)
    (SchwartzMap.evalCLM ℝ E F (quadrantLogBasis i) (SchwartzMap.fderivCLM ℝ E F f))

def quadrantLogGradient (f : SchwartzMap E F) : SchwartzMap E (E →L[ℝ] F) :=
  (quadrantLogEuler σ 0 f).postcompCLM
    ((ContinuousLinearMap.smulRightL ℝ E F) (coord 0)) +
  (quadrantLogEuler σ 1 f).postcompCLM
    ((ContinuousLinearMap.smulRightL ℝ E F) (coord 1))


private lemma gradient_apply (f : SchwartzMap E F) (x v : E) :
    quadrantLogGradient σ f x v =
      v 0 • ((-(σ 0 : ℝ)) • f x - x 0 • (fderiv ℝ f x (quadrantLogBasis 0))) +
      v 1 • ((-(σ 1 : ℝ)) • f x - x 1 • (fderiv ℝ f x (quadrantLogBasis 1))) := by
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
    HasFDerivAt (quadrantLogWeight σ f) (quadrantLogWeight σ (quadrantLogGradient σ f) u) u := by
  have he := logNode_hasFDeriv u
  have hw : HasFDerivAt (fun v : E => Real.exp (-(σ 0 : ℝ)*v 0-(σ 1 : ℝ)*v 1))
      (Real.exp (-(σ 0 : ℝ)*u 0-(σ 1 : ℝ)*u 1) •
        ((-(σ 0 : ℝ)) • coord 0 - (σ 1 : ℝ) • coord 1)) u :=
    (((coord 0).hasFDerivAt.const_mul (-(σ 0 : ℝ))).sub
      ((coord 1).hasFDerivAt.const_mul (σ 1 : ℝ))).exp
  have hf := (f.differentiableAt.hasFDerivAt.comp u he)
  apply (hw.smul hf).congr_fderiv
  ext v
  simp only [quadrantLogWeight,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    sub_apply,gradient_apply σ,quadrantLogNode_apply]
  dsimp [coord]
  simp only [map_add,map_smul,smul_add,smul_sub,smul_smul]
  module

private lemma logWeight_fderiv (f : SchwartzMap E F) :
    fderiv ℝ (quadrantLogWeight σ f)=quadrantLogWeight σ (quadrantLogGradient σ f) := by
  funext u
  exact (logWeight_hasFDeriv σ f u).fderiv

private lemma logWeight_smooth (f : SchwartzMap E F) : ContDiff ℝ ∞ (quadrantLogWeight σ f) := by
  have hn : ContDiff ℝ ∞ quadrantLogNode := by
    unfold quadrantLogNode
    fun_prop
  exact (by fun_prop : ContDiff ℝ ∞ (fun v : E => Real.exp (-(σ 0 : ℝ)*v 0-(σ 1 : ℝ)*v 1))).smul
    ((f.smooth ⊤).comp hn)

private lemma logWeight_decay (f : SchwartzMap E F) (k : ℕ) :
    ∃ C : ℝ, ∀ u : E, ‖u‖^k*‖quadrantLogWeight σ f u‖ ≤ C := by
  let δ : ℝ := min (σ 0 : ℝ) (σ 1 : ℝ)
  have hδ : 0 < δ := lt_min (σ 0).property (σ 1).property
  obtain ⟨m,hm⟩ := exists_nat_gt (max (σ 0 : ℝ) (σ 1 : ℝ)+δ)
  have hlow (i : Fin 2) : δ ≤ (σ i : ℝ) := by
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hupp (i : Fin 2) : (σ i : ℝ)+δ ≤ (m : ℝ) := by
    fin_cases i
    · change (σ 0 : ℝ)+δ ≤ (m : ℝ)
      have h := le_max_left (σ 0 : ℝ) (σ 1 : ℝ)
      linarith
    · change (σ 1 : ℝ)+δ ≤ (m : ℝ)
      have h := le_max_right (σ 0 : ℝ) (σ 1 : ℝ)
      linarith
  let C : ℝ := 2^(2*m)*(Finset.Iic (2*m,0)).sup
    (fun j : ℕ × ℕ => SchwartzMap.seminorm ℝ j.1 j.2) f
  let D : ℝ := (k.factorial : ℝ)/δ^k
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D*C,?_⟩
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
  have hc (i : Fin 2) : Real.exp (-(σ i : ℝ)*u i+δ*|u i|) ≤ B^m := by
    by_cases hi : 0 ≤ u i
    · rw [abs_of_nonneg hi]
      calc
        _ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hlow i])
        _ ≤ B^m := one_le_pow₀ hB
    · have hin : u i ≤ 0 := le_of_not_ge hi
      rw [abs_of_nonpos hin]
      have hp : Real.exp (-u i) ≤ B := by
        have h := PiLp.norm_apply_le (quadrantLogNode u) i
        rw [quadrantLogNode_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at h
        dsimp [B]
        linarith
      calc
        _ ≤ Real.exp ((m : ℝ)*(-u i)) := Real.exp_le_exp.mpr (by nlinarith [hupp i])
        _ = (Real.exp (-u i))^m := Real.exp_nat_mul _ _
        _ ≤ B^m := pow_le_pow_left₀ (Real.exp_nonneg _) hp m
  have hexp : Real.exp (-(σ 0 : ℝ)*u 0-(σ 1 : ℝ)*u 1)*Real.exp (δ*S) ≤ B^(2*m) := by
    calc
      _ = Real.exp (-(σ 0 : ℝ)*u 0+δ*|u 0|)*Real.exp (-(σ 1 : ℝ)*u 1+δ*|u 1|) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        dsimp [S]
        ring
      _ ≤ B^m*B^m := mul_le_mul (hc 0) (hc 1) (Real.exp_nonneg _) (by positivity)
      _ = B^(2*m) := by rw [← pow_add]; congr 1; omega
  have hbound : B^(2*m)*‖f (quadrantLogNode u)‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (2*m,0))
        (k := 2*m) (n := 0) le_rfl le_rfl f (quadrantLogNode u))
  have hp : ‖u‖^k ≤ D*Real.exp (δ*S) := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mp
      (Real.pow_div_factorial_le_exp (δ*S) (mul_nonneg hδ.le hS) k)
    calc
      _ ≤ S^k := pow_le_pow_left₀ (norm_nonneg _) hu k
      _ = (δ*S)^k/δ^k := by rw [mul_pow]; field_simp
      _ ≤ (Real.exp (δ*S)*(k.factorial : ℝ))/δ^k :=
        div_le_div_of_nonneg_right h (by positivity)
      _ = _ := by dsimp [D]; ring
  rw [quadrantLogWeight,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (D*Real.exp (δ*S))*
        (Real.exp (-(σ 0 : ℝ)*u 0-(σ 1 : ℝ)*u 1)*‖f (quadrantLogNode u)‖) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = D*(Real.exp (-(σ 0 : ℝ)*u 0-(σ 1 : ℝ)*u 1)*Real.exp (δ*S)*‖f (quadrantLogNode u)‖) := by ring
    _ ≤ D*(B^(2*m)*‖f (quadrantLogNode u)‖) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hD

private lemma logWeight_derivative_decay (n k : ℕ) :
    ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F),
      ∃ C : ℝ, ∀ u : E, ‖u‖^k*‖iteratedFDeriv ℝ n (quadrantLogWeight σ f) u‖ ≤ C := by
  induction n with
  | zero =>
    intro F _ _ f
    simpa only [norm_iteratedFDeriv_zero] using logWeight_decay σ f k
  | succ n ih =>
    intro F _ _ f
    obtain ⟨C,hC⟩ := ih (quadrantLogGradient σ f)
    refine ⟨C,fun u => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv,logWeight_fderiv σ]
    exact hC u

def quadrantLogSchwartz (f : SchwartzMap E F) : SchwartzMap E F where
  toFun := quadrantLogWeight σ f
  smooth' := logWeight_smooth σ f
  decay' k n := logWeight_derivative_decay σ n k f

theorem quadrantLogSchwartz_apply (f : SchwartzMap E F) (u : E) :
    quadrantLogSchwartz σ f u=Real.exp (-(σ 0 : ℝ)*u 0-(σ 1 : ℝ)*u 1) • f (quadrantLogNode u) := rfl

open scoped FourierTransform

def quadrantMellinLine (c t : ℝ) : ℂ := (c : ℂ)+(2*Real.pi*t : ℝ)*Complex.I

def quadrantMellinProfile (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  𝓕 (quadrantLogSchwartz σ f)

def quadrantMellinKernel (x y : ℝ) (v : E) : ℂ :=
  (x : ℂ)^(-quadrantMellinLine (σ 0) (v 0))*(y : ℂ)^(-quadrantMellinLine (σ 1) (v 1))

theorem norm_quadrantMellinKernel {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (v : E) :
    ‖quadrantMellinKernel σ x y v‖=x^(-(σ 0 : ℝ))*y^(-(σ 1 : ℝ)) := by
  rw [quadrantMellinKernel,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp [quadrantMellinLine]

private lemma kernel_phase {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (v : E) :
    (Real.exp ((σ 0 : ℝ)*Real.log x+(σ 1 : ℝ)*Real.log y) : ℂ)*quadrantMellinKernel σ x y v=
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

/-- Full two-variable Mellin inversion on the line with arbitrary positive real parts.
The profile contains both variables and is integrable without extra premises. -/
theorem quadrantMellin_inversion (f : SchwartzMap E ℂ)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ v : E, quadrantMellinKernel σ x y v*quadrantMellinProfile σ f v)=
      f (WithLp.toLp 2 ![x,y]) := by
  let u : E := WithLp.toLp 2 ![-Real.log x,-Real.log y]
  have he : quadrantLogNode u=WithLp.toLp 2 ![x,y] := by
    ext i
    fin_cases i <;> simp [quadrantLogNode_apply,u,Real.exp_log hx,Real.exp_log hy]
  have h := congrArg (fun g : SchwartzMap E ℂ => g u)
    (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap E ℂ) (quadrantLogSchwartz σ f))
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq'] at h
  change (∫ v : E, Complex.exp ((2*Real.pi*inner ℝ v u : ℝ)*Complex.I)*
    quadrantMellinProfile σ f v)=quadrantLogSchwartz σ f u at h
  rw [quadrantLogSchwartz_apply σ,he] at h
  have hw : Real.exp (-(σ 0 : ℝ)*u 0-(σ 1 : ℝ)*u 1)=Real.exp ((σ 0 : ℝ)*Real.log x+(σ 1 : ℝ)*Real.log y) := by
    dsimp [u]
    congr 1
    ring
  rw [hw,Complex.real_smul] at h
  apply mul_left_cancel₀ (show (Real.exp ((σ 0 : ℝ)*Real.log x+(σ 1 : ℝ)*Real.log y) : ℂ) ≠ 0 by
    exact_mod_cast (Real.exp_pos _).ne')
  rw [← integral_const_mul]
  calc
    _ = ∫ v : E, Complex.exp ((2*Real.pi*inner ℝ v u : ℝ)*Complex.I)*
        quadrantMellinProfile σ f v := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [← mul_assoc,kernel_phase σ hx hy]
    _ = _ := h

theorem continuous_quadrantMellinKernel {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Continuous (quadrantMellinKernel σ x y) := by
  have h (i : Fin 2) : Continuous (fun v : E => -quadrantMellinLine (σ i) (v i)) := by
    unfold quadrantMellinLine
    fun_prop
  exact ((h 0).const_cpow (Or.inl (by exact_mod_cast hx.ne'))).mul
    ((h 1).const_cpow (Or.inl (by exact_mod_cast hy.ne')))

theorem integrable_quadrantMellin_inversion (f : SchwartzMap E ℂ)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Integrable (fun v : E => quadrantMellinKernel σ x y v*quadrantMellinProfile σ f v) := by
  have hc := continuous_quadrantMellinKernel σ hx hy
  apply ((quadrantMellinProfile σ f).integrable.norm.const_mul
    (x^(-(σ 0 : ℝ))*y^(-(σ 1 : ℝ)))).mono' (hc.mul (quadrantMellinProfile σ f).continuous).aestronglyMeasurable
  filter_upwards [] with v
  change ‖quadrantMellinKernel σ x y v*quadrantMellinProfile σ f v‖ ≤ _
  rw [norm_mul,norm_quadrantMellinKernel σ hx hy]


end HTGeometry.PositiveLine
