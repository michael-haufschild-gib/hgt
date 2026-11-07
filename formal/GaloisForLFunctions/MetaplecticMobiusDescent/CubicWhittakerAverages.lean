/-
Compact cusp Whittaker averages adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicHyperbolicFourierKernel
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Holomorphy of compact cusp Whittaker averages

Write the height average and horizontal Fourier kernel as one product
integral. A slightly smaller real exponent absorbs the logarithm from
parameter differentiation, giving an integrable bound for `Re s > 1`.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein

def whittakerHeight (v : ℝ) : ℝ := max 5 v
def whittakerBase (p : ℝ × ℂ) : ℝ := whittakerHeight p.1*(1+‖p.2‖^2)
def whittakerIntegrand (freq s : ℂ) (p : ℝ × ℂ) : ℂ :=
  (whittakerHeight p.1:ℂ)⁻¹*(whittakerBase p:ℂ)^(-s)*
    tracePhase (-(freq*whittakerHeight p.1)*p.2)
def whittakerIntegrandDeriv (freq s : ℂ) (p : ℝ × ℂ) : ℂ :=
  -(Real.log (whittakerBase p):ℂ)*whittakerIntegrand freq s p
def whittakerProductVolume : Measure (ℝ × ℂ) :=
  (volume.restrict (Set.Icc (5:ℝ) 6)).prod volume

lemma whittakerHeight_ge_one (v : ℝ) : 1≤whittakerHeight v := by
  exact (by norm_num : (1:ℝ)≤5).trans (le_max_left _ _)

lemma whittakerBase_ge (p : ℝ × ℂ) : 1+‖p.2‖^2≤whittakerBase p := by
  exact le_mul_of_one_le_left (by positivity) (whittakerHeight_ge_one p.1)

lemma whittakerBase_ge_one (p : ℝ × ℂ) : 1≤whittakerBase p :=
  (by nlinarith [sq_nonneg ‖p.2‖] : 1≤1+‖p.2‖^2).trans (whittakerBase_ge p)

lemma whittakerBase_pos (p : ℝ × ℂ) : 0<whittakerBase p :=
  zero_lt_one.trans_le (whittakerBase_ge_one p)

lemma whittakerIntegrand_continuous (freq s : ℂ) : Continuous (whittakerIntegrand freq s) := by
  have hv : Continuous (fun p : ℝ × ℂ => whittakerHeight p.1) := by
    unfold whittakerHeight
    fun_prop
  have hb : Continuous whittakerBase := by unfold whittakerBase; fun_prop
  have hp : Continuous (fun p : ℝ × ℂ => (whittakerBase p:ℂ)^(-s)) :=
    (Complex.continuous_ofReal.comp hb).cpow continuous_const
      (fun p => Complex.ofReal_mem_slitPlane.mpr (whittakerBase_pos p))
  have hi : Continuous (fun p : ℝ × ℂ => (whittakerHeight p.1:ℂ)⁻¹) :=
    (Complex.continuous_ofReal.comp hv).inv₀ (fun p => by
      change (whittakerHeight p.1:ℂ)≠0
      exact_mod_cast (zero_lt_one.trans_le (whittakerHeight_ge_one p.1)).ne')
  have hc : Continuous (fun p : ℝ × ℂ =>
      tracePhase (-(freq*whittakerHeight p.1)*p.2)) := by
    change Continuous (fun p : ℝ × ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-(freq*whittakerHeight p.1)*p.2)+starRingEnd ℂ (-(freq*whittakerHeight p.1)*p.2))))
    fun_prop
  exact (hi.mul hp).mul hc

lemma whittakerIntegrandDeriv_continuous (freq s : ℂ) : Continuous (whittakerIntegrandDeriv freq s) := by
  have hb : Continuous whittakerBase := by unfold whittakerBase whittakerHeight; fun_prop
  have hl : Continuous (fun p => Real.log (whittakerBase p)) :=
    hb.log (fun p => (whittakerBase_pos p).ne')
  exact (Complex.continuous_ofReal.comp hl).neg.mul (whittakerIntegrand_continuous freq s)

lemma whittakerIntegrand_hasDerivAt (freq s : ℂ) (p : ℝ × ℂ) :
    HasDerivAt (fun w => whittakerIntegrand freq w p) (whittakerIntegrandDeriv freq s p) s := by
  have hn : (whittakerBase p:ℂ)≠0 := by exact_mod_cast (whittakerBase_pos p).ne'
  have hh := (((hasDerivAt_id s).neg.const_cpow (Or.inl hn)).const_mul
    ((whittakerHeight p.1:ℂ)⁻¹)).mul_const
      (tracePhase (-(freq*whittakerHeight p.1)*p.2))
  convert hh using 1 <;> try rfl
  rw [←Complex.ofReal_log (whittakerBase_pos p).le]
  unfold whittakerIntegrandDeriv whittakerIntegrand
  simp only [Pi.neg_apply,id_eq]
  ring

lemma whittakerIntegrand_norm (freq s : ℂ) (p : ℝ × ℂ) :
    ‖whittakerIntegrand freq s p‖=(whittakerHeight p.1)⁻¹*(whittakerBase p)^(-s.re) := by
  unfold whittakerIntegrand
  rw [norm_mul,norm_mul,tracePhase_norm,mul_one,norm_inv,
    Complex.norm_of_nonneg (zero_lt_one.trans_le (whittakerHeight_ge_one p.1)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos (whittakerBase_pos p)]
  rfl

lemma whittakerIntegrand_norm_bound (freq s : ℂ) (p : ℝ × ℂ)
    (b : ℝ) (hb : 0≤b) (hs : b≤ s.re) :
    ‖whittakerIntegrand freq s p‖≤(1+‖p.2‖^2)^(-b) := by
  rw [whittakerIntegrand_norm]
  calc
    _ ≤ (whittakerBase p)^(-s.re) := by
      exact mul_le_of_le_one_left (Real.rpow_nonneg (whittakerBase_pos p).le _)
        (inv_le_one_of_one_le₀ (whittakerHeight_ge_one p.1))
    _ ≤ (whittakerBase p)^(-b) :=
      Real.rpow_le_rpow_of_exponent_le (whittakerBase_ge_one p) (by linarith)
    _ ≤ (1+‖p.2‖^2)^(-b) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (whittakerBase_ge p) (by linarith)

lemma whittakerIntegrandDeriv_norm_bound (freq s : ℂ) (p : ℝ × ℂ)
    (b ε : ℝ) (hb : 0≤b) (hε : 0<ε) (hs : b+ε≤ s.re) :
    ‖whittakerIntegrandDeriv freq s p‖≤ε⁻¹*(1+‖p.2‖^2)^(-b) := by
  have hlog := Real.log_nonneg (whittakerBase_ge_one p)
  unfold whittakerIntegrandDeriv
  rw [norm_mul,norm_neg,Complex.norm_of_nonneg hlog,whittakerIntegrand_norm]
  calc
    _ ≤ Real.log (whittakerBase p)*(whittakerBase p)^(-s.re) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (Real.rpow_nonneg (whittakerBase_pos p).le _)
          (inv_le_one_of_one_le₀ (whittakerHeight_ge_one p.1))) hlog
    _ ≤ ((whittakerBase p)^ε/ε)*(whittakerBase p)^(-s.re) := by
      exact mul_le_mul_of_nonneg_right (Real.log_le_rpow_div (whittakerBase_pos p).le hε)
        (Real.rpow_nonneg (whittakerBase_pos p).le _)
    _ = ε⁻¹*(whittakerBase p)^(ε-s.re) := by
      rw [Real.rpow_sub (whittakerBase_pos p),Real.rpow_neg (whittakerBase_pos p).le]
      ring
    _ ≤ ε⁻¹*(whittakerBase p)^(-b) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (whittakerBase_ge_one p) (by linarith)) (by positivity)
    _ ≤ ε⁻¹*(1+‖p.2‖^2)^(-b) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) (whittakerBase_ge p) (by linarith)) (by positivity)

lemma whittaker_bound_integrable (b : ℝ) (hb : 1<b) :
    Integrable (fun p : ℝ × ℂ => (1+‖p.2‖^2)^(-b)) whittakerProductVolume := by
  have hk : Integrable (fun z : ℂ => (1+‖z‖^2)^(-b)) := by
    convert (hyperbolicKernel_integrable (b:ℂ) hb).norm using 1
    funext z
    simp only [hyperbolicKernel,Complex.norm_cpow_eq_rpow_re_of_pos
      (by positivity : 0<1+‖z‖^2),Complex.neg_re,Complex.ofReal_re]
  have hv : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Set.Icc (5:ℝ) 6)) := integrable_const _
  unfold whittakerProductVolume
  simpa only [one_mul] using hv.mul_prod hk

lemma whittakerIntegrand_integrable (freq s : ℂ) (hs : 1<s.re) :
    Integrable (whittakerIntegrand freq s) whittakerProductVolume := by
  exact (whittaker_bound_integrable s.re hs).mono'
    (whittakerIntegrand_continuous freq s).aestronglyMeasurable
    (Eventually.of_forall (fun p => whittakerIntegrand_norm_bound freq s p s.re (by linarith) le_rfl))

lemma whittakerProduct_differentiableAt (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ (fun w => ∫p,whittakerIntegrand freq w p∂whittakerProductVolume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := whittakerProductVolume) (F := whittakerIntegrand freq)
    (F' := whittakerIntegrandDeriv freq)
    (bound := fun p => ε⁻¹*(1+‖p.2‖^2)^(-b)) hU
    (Eventually.of_forall (fun w => (whittakerIntegrand_continuous freq w).aestronglyMeasurable))
    (whittakerIntegrand_integrable freq s hs)
    (whittakerIntegrandDeriv_continuous freq s).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => whittakerIntegrandDeriv_norm_bound freq w p b ε (by linarith) hε hw.le))
    ((whittaker_bound_integrable b hb).const_mul ε⁻¹)
    (Eventually.of_forall (fun p w _ => whittakerIntegrand_hasDerivAt freq w p))
  exact h.2.differentiableAt

lemma whittakerIntegrand_eq (freq s : ℂ) (v : ℝ) (hv : 5≤v) (z : ℂ) :
    whittakerIntegrand freq s (v,z)=
      (v:ℂ)^(-s-1)*(hyperbolicKernel s z*tracePhase (-(freq*v)*z)) := by
  have hvp : 0<v := by linarith
  have hvn : (v:ℂ)≠0 := by exact_mod_cast hvp.ne'
  have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(-s)*(v:ℂ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hvn,Complex.cpow_one,div_eq_mul_inv]
  unfold whittakerIntegrand whittakerBase whittakerHeight hyperbolicKernel
  simp only [max_eq_right hv,Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hvp.le (by positivity),hp]
  ring

lemma whittakerProduct_eq_average (freq s : ℂ) (hs : 1<s.re) :
    (∫p,whittakerIntegrand freq s p∂whittakerProductVolume)=
      ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := whittakerIntegrand_integrable freq s hs
  unfold whittakerProductVolume at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  calc
    _ = ∫z : ℂ,(v:ℂ)^(-s-1)*(hyperbolicKernel s z*tracePhase (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => whittakerIntegrand_eq freq s v hv.1 z)
    _ = _ := integral_const_mul _ _

theorem cuspWhittakerAverage_differentiableAt (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have he : (fun w => ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v))
      =ᶠ[𝓝 s](fun w => ∫p,whittakerIntegrand freq w p∂whittakerProductVolume) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact (whittakerProduct_eq_average freq w hw).symm
  exact (whittakerProduct_differentiableAt freq s hs).congr_of_eventuallyEq he


#print axioms cuspWhittakerAverage_differentiableAt
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
