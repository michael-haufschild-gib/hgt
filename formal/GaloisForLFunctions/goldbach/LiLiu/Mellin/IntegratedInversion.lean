import GaloisForLFunctions.goldbach.LiLiu.MellinWeight
import Mathlib.MeasureTheory.Integral.Prod

/-! # Mellin inversion inside the continuous Goldbach convolutions

Inverting the weight at a product of two positive arguments separates the
two integrations. Absolute convergence follows from the real-part powers
of the same arguments and integrability of the vertical Mellin transform.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Set Filter MetaplecticMobiusDescent.CubicEisenstein
noncomputable section

private def line (σ t : ℝ) : ℂ := (σ:ℂ)+t*I

private theorem weight_inversion (φ : TestWeight) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    (φ x : ℂ) = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ)^(-(1/2 + line σ t)) * mellin (companion φ) (line σ t) := by
  have h0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hh : (Real.sqrt x : ℂ) = (x:ℂ)^(1/2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le]
    push_cast
    rfl
  calc
    _ = (x:ℂ)^(-(1/2:ℂ)) * companion φ x := by
      rw [companion, Vstar, hh, ← mul_assoc, ← cpow_add _ _ h0, neg_add_cancel, cpow_zero, one_mul]
    _ = _ := by
      rw [companion_inversion φ σ x hx, mul_left_comm, ← integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [← mul_assoc, ← cpow_add _ _ h0, neg_add]
      rfl

/-- Continuous-index Mellin inversion. The real-part majorant is the only
absolute convergence requirement on the measure against which we invert. -/
theorem integrated_weight_inversion {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (φ : TestWeight) (σ : ℝ) {q : X → ℝ} {W : X → ℂ}
    (hq : Measurable q) (hW : Measurable W) (hp : ∀ᵐ x ∂μ, 0 < q x)
    (hi : Integrable (fun x => ‖W x‖ * q x ^ (-(1/2+σ))) μ) :
    (∫ x, W x * (φ (q x) : ℂ) ∂μ) = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      (∫ x, W x * (q x : ℂ)^(-(1/2+((σ:ℂ)+t*I))) ∂μ) *
        mellin (companion φ) ((σ:ℂ)+t*I) := by
  let M (t : ℝ) := mellin (companion φ) (line σ t)
  let F (x : X) (t : ℝ) := W x * (q x : ℂ)^(-(1/2+line σ t)) * M t
  have hM : Integrable M := compactMellin_vertical_integrable _ _ _ (by norm_num)
    (companion_support φ) (companion_smooth φ) σ
  have hc : Continuous (line σ) := by unfold line; fun_prop
  have hm : Measurable M := ((mellin_companion_differentiable φ).continuous.comp hc).measurable
  have hF : Measurable (Function.uncurry F) :=
    ((hW.comp measurable_fst).mul
      ((continuous_ofReal.measurable.comp (hq.comp measurable_fst)).pow
        ((measurable_const.add (hc.measurable.comp measurable_snd)).neg))).mul (hm.comp measurable_snd)
  have hpos : ∀ᵐ p ∂μ.prod (volume : Measure ℝ), 0 < q p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hp
  have hFi : Integrable (Function.uncurry F) (μ.prod volume) := by
    apply (hi.mul_prod hM.norm).mono' hF.aestronglyMeasurable
    filter_upwards [hpos] with p hp
    simp only [Function.uncurry, F, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp]
    have hre : (-(1/2+line σ p.2)).re = -(1/2+σ) := by norm_num [line]
    rw [hre]
  calc
    _ = (1/(2*Real.pi) : ℂ) * ∫ x, ∫ t : ℝ, F x t ∂volume ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hp] with x hx
      simp only [F, M, mul_assoc, integral_const_mul, weight_inversion φ σ hx]
      ring
    _ = _ := by
      rw [integral_integral_swap hFi]
      simp only [F, integral_mul_const, M, line]

/-- With two independent positive scales the height integral factors into
the two Mellin moments. In the model one moment is an Euler Beta integral. -/
theorem product_weight_inversion (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (φ : TestWeight) (σ : ℝ) {A B : ℝ → ℂ} (hA : Measurable A) (hB : Measurable B)
    (hμ : ∀ᵐ x ∂μ, 0 < x) (hν : ∀ᵐ x ∂ν, 0 < x)
    (hI : Integrable (fun x => ‖A x‖ * x ^ (-(1/2+σ))) μ)
    (hJ : Integrable (fun x => ‖B x‖ * x ^ (-(1/2+σ))) ν) :
    (∫ p : ℝ × ℝ, A p.1 * B p.2 * (φ (p.1*p.2) : ℂ) ∂μ.prod ν) =
      (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
        (∫ x, A x * (x:ℂ)^(-(1/2+((σ:ℂ)+t*I))) ∂μ) *
        (∫ y, B y * (y:ℂ)^(-(1/2+((σ:ℂ)+t*I))) ∂ν) *
        mellin (companion φ) ((σ:ℂ)+t*I) := by
  have hx : ∀ᵐ p ∂μ.prod ν, 0 < p.1 := Measure.quasiMeasurePreserving_fst.ae hμ
  have hy : ∀ᵐ p ∂μ.prod ν, 0 < p.2 := Measure.quasiMeasurePreserving_snd.ae hν
  rw [integrated_weight_inversion (μ.prod ν) φ σ (measurable_fst.mul measurable_snd)
    ((hA.comp measurable_fst).mul (hB.comp measurable_snd))
    (hx.and hy |>.mono fun _ h => mul_pos h.1 h.2) (by
      apply (hI.mul_prod hJ).congr
      filter_upwards [hx,hy] with p hx hy
      simp only [norm_mul, Real.mul_rpow hx.le hy.le]
      ring)]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [hx,hy] with p hx hy
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le hy.le]
  ring

#print axioms product_weight_inversion
end
end GaloisForLFunctions.Goldbach.LiLiu
