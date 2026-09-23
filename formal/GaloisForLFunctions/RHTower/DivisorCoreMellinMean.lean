import GaloisForLFunctions.RHTower.DivisorCoreMellinStrip
import GaloisForLFunctions.HTGeometry.CauchyKernelFourier
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Large-dilation limit of the literal paired divisor Mellin contour

The entire remainder moves from Re(s)=1 to Re(s)=0 by the proved strip
bounds. The rational two-pole contribution is evaluated by the existing
Cauchy Fourier transform. Its normalized contribution is exactly the
source residue for nonnegative logarithmic dilation. The boundary
remainder tends to zero by Riemann–Lebesgue. This closes the literal
analytic contour limit, without asserting its still-open identification
with the physical signed head average or a sign for the residue.
-/

noncomputable section
open Complex Filter Set Topology MeasureTheory Finset
open GaloisForLFunctions.HTGeometry
namespace RHTower

/-- The literal paired source's normalized inverse Mellin contour at logarithmic dilation a. -/
def divisorCoreMellinContourMean (P : Finset ℕ) (a : ℝ) : ℂ :=
  (1/(2*(Real.pi:ℂ)))*(∫ t : ℝ,
    Complex.exp ((a:ℂ)*(1+(t:ℂ)*I))*divisorCoreMellinPair P (1+(t:ℂ)*I))

private def corePoleLine (P : Finset ℕ) (a t : ℝ) : ℂ :=
  (2*divisorCoreMellinPairResidue P*Complex.exp (a:ℂ))*
    (Complex.exp (((t*a:ℝ):ℂ)*I)*((1+t^(2 : ℕ):ℝ):ℂ)⁻¹)

private lemma corePoleLine_integrable (P : Finset ℕ) (a : ℝ) :
    Integrable (corePoleLine P a) := by
  have hc : Continuous (fun t : ℝ => Complex.exp (((t*a:ℝ):ℂ)*I)*((1+t^(2 : ℕ):ℝ):ℂ)⁻¹) := by
    apply Continuous.mul (by fun_prop)
    apply Continuous.inv₀ (by fun_prop)
    intro t
    exact Complex.ofReal_ne_zero.mpr (by positivity : (1+t^(2 : ℕ):ℝ) ≠ 0)
  have hi : Integrable (fun t : ℝ =>
      Complex.exp (((t*a:ℝ):ℂ)*I)*((1+t^(2 : ℕ):ℝ):ℂ)⁻¹) := by
    apply integrable_inv_one_add_sq.mono' hc.aestronglyMeasurable
    filter_upwards with t
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs]
    have hp : ‖Complex.exp (((t*a:ℝ):ℂ)*I)‖=1 := by simp [norm_exp]
    rw [hp,one_mul,abs_of_pos (show 0 < (1+t^(2 : ℕ):ℝ) by positivity)]
  exact hi.const_mul _

private lemma paired_one_split (P : Finset ℕ) (a t : ℝ) :
    Complex.exp ((a:ℂ)*(1+(t:ℂ)*I))*divisorCoreMellinPair P (1+(t:ℂ)*I) =
    Complex.exp ((a:ℂ)*(1+(t:ℂ)*I))*divisorCoreMellinPairEntire P (1+(t:ℂ)*I)+
      corePoleLine P a t := by
  have hs0 : (1:ℂ)+(t:ℂ)*I ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  have hs2 : (1:ℂ)+(t:ℂ)*I ≠ 2 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  have hd : ((1:ℂ)+(t:ℂ)*I)*(2-((1:ℂ)+(t:ℂ)*I))=((1+t^(2 : ℕ):ℝ):ℂ) := by
    push_cast
    ring_nf
    simp
  rw [divisorCoreMellinPairEntire_eq P hs0 hs2,hd,corePoleLine]
  have he : Complex.exp ((a:ℂ)*(1+(t:ℂ)*I)) =
      Complex.exp (a:ℂ)*Complex.exp (((t*a:ℝ):ℂ)*I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- The full source contour, including both endpoint poles, is absolutely
integrable on the central line for every fixed logarithmic dilation. -/
theorem integrable_exp_mul_divisorCoreMellinPair_one
    (P : Finset ℕ) (hP : P.Nonempty) (a : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp ((a:ℂ)*(1+(t:ℂ)*I))*divisorCoreMellinPair P (1+(t:ℂ)*I)) := by
  have hi := (integrable_exp_mul_divisorCoreMellinPairEntire_line P hP a
    (σ := 1) (by norm_num) (by norm_num)).add (corePoleLine_integrable P a)
  apply hi.congr
  filter_upwards with t
  exact (paired_one_split P a t).symm

private lemma corePoleLine_integral (P : Finset ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (∫ t : ℝ, corePoleLine P a t)=2*(Real.pi:ℂ)*divisorCoreMellinPairResidue P := by
  have h := integral_cexp_mul_inv_sq_add_sq (a := 1) (by norm_num) a
  norm_num [abs_of_nonneg ha] at h
  simp only [corePoleLine]
  rw [integral_const_mul]
  push_cast
  rw [h]
  have hc : Complex.exp (a:ℂ)*Complex.exp (-(a:ℂ))=1 := by
    rw [← Complex.exp_add,add_neg_cancel,Complex.exp_zero]
  calc
    _ = 2*(Real.pi:ℂ)*divisorCoreMellinPairResidue P*
        (Complex.exp (a:ℂ)*Complex.exp (-(a:ℂ))) := by ring
    _ = _ := by rw [hc,mul_one]

/-- Exact contour residue plus an integrable oscillating boundary. This is
an identity for the literal source continuation, before the physical Mellin identification. -/
theorem divisorCoreMellinContourMean_eq_residue_add_boundary
    (P : Finset ℕ) (hP : P.Nonempty) {a : ℝ} (ha : 0 ≤ a) :
    divisorCoreMellinContourMean P a=divisorCoreMellinPairResidue P+
      (1/(2*(Real.pi:ℂ)))*(∫ t : ℝ,
        Complex.exp ((a:ℂ)*(t:ℂ)*I)*divisorCoreMellinPairEntire P ((t:ℂ)*I)) := by
  rw [divisorCoreMellinContourMean]
  simp_rw [paired_one_split]
  have hi : Integrable (fun t : ℝ => Complex.exp ((a:ℂ)*(1+(t:ℂ)*I))*
      divisorCoreMellinPairEntire P (1+(t:ℂ)*I)) := by
    simpa only [Complex.ofReal_one] using
      integrable_exp_mul_divisorCoreMellinPairEntire_line P hP a
        (σ := 1) (by norm_num) (by norm_num)
  have hshift : (∫ t : ℝ, Complex.exp ((a:ℂ)*(1+(t:ℂ)*I))*
      divisorCoreMellinPairEntire P (1+(t:ℂ)*I)) =
      ∫ t : ℝ, Complex.exp ((a:ℂ)*(t:ℂ)*I)*divisorCoreMellinPairEntire P ((t:ℂ)*I) := by
    simpa only [Complex.ofReal_one] using
      integral_exp_mul_divisorCoreMellinPairEntire_shift P hP a
        (σ := 1) (by norm_num) (by norm_num)
  rw [integral_add hi (corePoleLine_integrable P a),corePoleLine_integral P ha,hshift]
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp only [mul_comm,mul_left_comm,mul_assoc,add_comm]

/-- The actual boundary remainder vanishes at large logarithmic dilation by
Riemann–Lebesgue; its integrability was proved from source bounds. -/
theorem tendsto_divisorCoreMellinPairEntire_boundary_zero (P : Finset ℕ) :
    Tendsto (fun a : ℝ => ∫ t : ℝ,
      Complex.exp ((a:ℂ)*(t:ℂ)*I)*divisorCoreMellinPairEntire P ((t:ℂ)*I))
      atTop (𝓝 0) := by
  have hpi : 0 < 2*Real.pi := by positivity
  have hRL := Real.tendsto_integral_exp_smul_cocompact
    (fun t : ℝ => divisorCoreMellinPairEntire P ((t:ℂ)*I))
  have hw : Tendsto (fun a : ℝ => -a/(2*Real.pi)) atTop atBot :=
    tendsto_neg_atTop_atBot.atBot_div_const hpi
  have hc := hRL.comp (hw.mono_right atBot_le_cocompact)
  apply hc.congr
  intro a
  apply integral_congr_ae
  filter_upwards with t
  simp only [Circle.smul_def,Real.fourierChar_apply,smul_eq_mul]
  congr 2
  push_cast
  field_simp

/-- Unconditional large-dilation limit of the literal paired Mellin contour.
No physical signed-mean identification or sign of the residue is assumed. -/
theorem tendsto_divisorCoreMellinContourMean (P : Finset ℕ) (hP : P.Nonempty) :
    Tendsto (divisorCoreMellinContourMean P) atTop (𝓝 (divisorCoreMellinPairResidue P)) := by
  have h := ((tendsto_divisorCoreMellinPairEntire_boundary_zero P).const_mul
    (1/(2*(Real.pi:ℂ)))).const_add (divisorCoreMellinPairResidue P)
  simp only [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with a ha
  exact (divisorCoreMellinContourMean_eq_residue_add_boundary P hP ha).symm

end RHTower
