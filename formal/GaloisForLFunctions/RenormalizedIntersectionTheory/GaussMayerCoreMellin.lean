import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerThetaCore
import GaloisForLFunctions.RHTower.Suzuki.SuzukiMellinConvolution

/-! Exact arithmetic Mellin spectrum of the actual scattering-subtracted Mayer
core. Multiplicative convolution of the renormalized Gaussian rays proves
absolute convergence and the two-zeta Gamma product. -/

open Complex Set Filter MeasureTheory
open GaloisForLFunctions.ArithmeticOrientationGeometry
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoreMellin
open MayerThetaRay MayerThetaProduct MayerThetaCore MayerScatteringCore

private def inverseRay (w : ℂ) (t : ℝ) : ℂ :=
  ((t⁻¹ : ℝ) : ℂ)^(w/2)*thetaRay t⁻¹

private theorem inverseRay_hasMellin {w u : ℂ}
    (hu : 0 < (w/2-u).re) (hu1 : (w/2-u).re < 1/2) :
    HasMellin (inverseRay w) u
      (Gammaℝ (w-2*u)*riemannZeta (w-2*u)) := by
  have h : MellinConvergent (fun t : ℝ => (t : ℂ)^(w/2) • thetaRay t) (-u) := by
    rw [MellinConvergent.cpow_smul,show -u+w/2=w/2-u by ring]
    exact (thetaRay_hasMellin hu hu1).1
  have hi := (MellinConvergent.comp_rpow
    (f := fun t : ℝ => (t : ℂ)^(w/2) • thetaRay t) (s := u) (a := -1) (by norm_num)).mpr
    (by simpa only [Complex.ofReal_neg,Complex.ofReal_one,div_neg,div_one] using h)
  constructor
  · unfold inverseRay
    simpa only [Real.rpow_neg_one,smul_eq_mul] using! hi
  · have he := mellin_comp_inv (fun t : ℝ => (t : ℂ)^(w/2) • thetaRay t) u
    rw [mellin_cpow_smul,show -u+w/2=w/2-u by ring,
      (thetaRay_hasMellin hu hu1).2,show 2*(w/2-u)=w-2*u by ring] at he
    exact he

private theorem thetaRay_measurable : Measurable thetaRay := by
  have htheta : Measurable thetaSum := by
    unfold thetaSum
    apply Measurable.tsum
    intro n
    fun_prop
  unfold thetaRay
  fun_prop

private theorem inverseRay_measurable (w : ℂ) : Measurable (inverseRay w) := by
  have htheta := thetaRay_measurable.comp measurable_inv
  unfold inverseRay
  fun_prop

private theorem convolution_eq_theta (w : ℂ) (b : ℝ) :
    _root_.RHTower.positiveMellinConvolution (inverseRay w) thetaRay b=
      mellin (fun t => thetaRay t*thetaRay (b*t)) (w/2) := by
  let k : ℝ → ℂ := fun t => (t : ℂ)^(w/2) • (thetaRay t*thetaRay (b*t))
  calc
    _ = mellin (fun t => k t⁻¹) 0 := by
      unfold _root_.RHTower.positiveMellinConvolution mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [inverseRay,k,smul_eq_mul,zero_sub,Complex.cpow_neg_one,
        div_eq_mul_inv,Complex.ofReal_inv]
      ring
    _ = mellin k 0 := by rw [mellin_comp_inv,neg_zero]
    _ = _ := by rw [mellin_cpow_smul,zero_add]

private theorem convolution_square_eq_core {w : ℂ} (hw : 0 < w.re) (hw2 : w.re < 2)
    (him : 0 < w.im) {a : ℝ} (ha : 0 < a) :
    _root_.RHTower.positiveMellinConvolution (inverseRay w) thetaRay (a^2)=
      Gammaℝ w*fieldCore w a/2 := by
  rw [convolution_eq_theta w (a^2)]
  exact (core_theta_hasMellin hw hw2 him ha).2

/-- The actual finite-energy core has a two-zeta Mellin transform throughout the common
absolute-convergence strip of the two renormalized theta rays. -/
theorem core_hasMellin_gammaR {w u : ℂ} (hu : 0 < u.re) (hu1 : u.re < 1)
    (hwu : 0 < (w-u).re) (hwu1 : (w-u).re < 1) (him : 0 < w.im) :
    HasMellin (fieldCore w) u
      (Gammaℝ u*Gammaℝ (w-u)/Gammaℝ w*riemannZeta u*riemannZeta (w-u)) := by
  have hr0 : 0 < w.re-u.re := by simpa only [Complex.sub_re] using hwu
  have hr1 : w.re-u.re < 1 := by simpa only [Complex.sub_re] using hwu1
  have hw : 0 < w.re := by linarith only [hu,hr0]
  have hw2 : w.re < 2 := by linarith only [hu1,hr1]
  have hv : w/2-u/2=(w-u)/2 := by ring
  have hI := inverseRay_hasMellin (w := w) (u := u/2)
    (by rw [hv]; simp; linarith only [hr0])
    (by rw [hv]; simp; linarith only [hr1])
  have hT := thetaRay_hasMellin (u := u/2)
    (by simp; linarith only [hu]) (by simp; linarith only [hu1])
  rw [show w-2*(u/2)=w-u by ring] at hI
  rw [show 2*(u/2)=u by ring] at hT
  let C := _root_.RHTower.positiveMellinConvolution (inverseRay w) thetaRay
  have hC0 := _root_.RHTower.hasMellin_positiveMellinConvolution
    (inverseRay_measurable w) thetaRay_measurable hI.1 hT.1
  rw [hI.2,hT.2] at hC0
  have hC : HasMellin C (u/2)
      ((Gammaℝ (w-u)*riemannZeta (w-u))*(Gammaℝ u*riemannZeta u)) := hC0
  have hAc : MellinConvergent (fun a : ℝ => C (a^2)) u := by
    have h := (MellinConvergent.comp_rpow (f := C) (s := u) (a := 2) (by norm_num)).mpr hC.1
    simpa only [Real.rpow_two] using! h
  have hAv : mellin (fun a : ℝ => C (a^2)) u=
      (1/2 : ℂ)*((Gammaℝ (w-u)*riemannZeta (w-u))*(Gammaℝ u*riemannZeta u)) := by
    have h := mellin_comp_rpow C u 2
    norm_num only [Real.rpow_two,Complex.real_smul] at h
    push_cast at h
    rw [hC.2] at h
    simpa only [one_div] using h
  have hm := hasMellin_const_smul hAc (2/Gammaℝ w)
  rw [hAv] at hm
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos hw
  have hp : ∀ a ∈ Ioi (0 : ℝ),(2/Gammaℝ w) • C (a^2)=fieldCore w a := by
    intro a ha
    change (2/Gammaℝ w)*( _root_.RHTower.positiveMellinConvolution
      (inverseRay w) thetaRay (a^2))=fieldCore w a
    rw [convolution_square_eq_core hw hw2 him ha]
    field_simp
  constructor
  · exact MeasureTheory.IntegrableOn.congr_fun hm.1
      (fun a ha => congrArg (fun z : ℂ => (a : ℂ)^(u-1) • z) (hp a ha)) measurableSet_Ioi
  · calc
      mellin (fieldCore w) u=mellin (fun a : ℝ => (2/Gammaℝ w) • C (a^2)) u := by
        unfold mellin
        exact setIntegral_congr_fun measurableSet_Ioi
          (fun a ha => congrArg (fun z : ℂ => (a : ℂ)^(u-1) • z) (hp a ha).symm)
      _ = _ := by rw [hm.2]; simp only [smul_eq_mul]; ring

#print axioms core_hasMellin_gammaR

private theorem gammaR_product_quotient {w : ℂ} (hw : 0 < w.re) (u : ℂ) :
    Gammaℝ u*Gammaℝ (w-u)/Gammaℝ w=
      Gamma (u/2)*Gamma ((w-u)/2)/Gamma (w/2) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hA : (Real.pi : ℂ)^(-u/2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hB : (Real.pi : ℂ)^(-(w-u)/2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hG : Gamma (w/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith only [hw])
  have hp : (Real.pi : ℂ)^(-u/2)*(Real.pi : ℂ)^(-(w-u)/2)=
      (Real.pi : ℂ)^(-w/2) := by
    rw [← Complex.cpow_add _ _ hpi]
    congr 1
    ring
  simp only [Gammaℝ_def]
  rw [← hp]
  field_simp

/-- Exact arithmetic spectrum of the actual scattering-subtracted Epstein–Mayer core,
with absolute convergence in `0 < Re u < 1` and `0 < Re (w-u) < 1`. -/
theorem core_hasMellin {w u : ℂ} (hu : 0 < u.re) (hu1 : u.re < 1)
    (hwu : 0 < (w-u).re) (hwu1 : (w-u).re < 1) (him : 0 < w.im) :
    HasMellin (fieldCore w) u
      (Gamma (u/2)*Gamma ((w-u)/2)/Gamma (w/2)*riemannZeta u*riemannZeta (w-u)) := by
  have hw : 0 < w.re := by simp only [Complex.sub_re] at hwu; linarith only [hu,hwu]
  simpa only [gammaR_product_quotient hw u] using core_hasMellin_gammaR hu hu1 hwu hwu1 him

#print axioms core_hasMellin

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoreMellin
