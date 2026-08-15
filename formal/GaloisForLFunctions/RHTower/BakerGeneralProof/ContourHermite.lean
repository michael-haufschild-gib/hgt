import Mathlib.Analysis.Complex.CauchyIntegral
import GaloisForLFunctions.HTGeometry.PolynomialGrowthBound
import GaloisForLFunctions.HTGeometry.WeightedArgumentPrincipleDisc
import GaloisForLFunctions.HTGeometry.CircleIntegralParamOpen
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Algebra.Polynomial

/-!
# Gap-free contour Hermite interpolation

This module constructs the Hermite interpolation polynomial for an exponential by a contour
integral. Its coefficient bound depends only on a containing circle and the modulus polynomial,
never on separation between interpolation nodes. A local analytic factorization proves agreement
of every jet forced by a power of a linear factor of the modulus.
-/

open scoped Classical
open Complex Metric
open Filter
open GaloisForLFunctions.HTGeometry
open HTGeometry

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

noncomputable def contourQuotient (Q : Polynomial ℂ) (ζ : ℂ) : Polynomial ℂ :=
  Q /ₘ (Polynomial.X - Polynomial.C ζ)

theorem eval_contourQuotient (Q : Polynomial ℂ) (ζ w : ℂ) :
    Q.eval ζ - Q.eval w = (ζ - w) * (contourQuotient Q ζ).eval w := by
  have h := congrArg (Polynomial.eval w)
    (Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic Q ζ)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.modByMonic_X_sub_C_eq_C_eval] at h
  rw [contourQuotient]
  calc
    Q.eval ζ - Q.eval w = -(Q.eval w - Q.eval ζ) := by ring
    _ = -((w - ζ) * (Q /ₘ (Polynomial.X - Polynomial.C ζ)).eval w) := by rw [h]
    _ = (ζ - w) * (Q /ₘ (Polynomial.X - Polynomial.C ζ)).eval w := by ring

theorem norm_coeff_contourQuotient_le (Q : Polynomial ℂ) (ζ : ℂ) (m : ℕ)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (hζ : ‖ζ‖ ≤ ρ) :
    ‖(contourQuotient Q ζ).coeff m‖ ≤ ρ ^ Q.natDegree * coeffNormSum Q := by
  rw [contourQuotient, Polynomial.coeff_divByMonic_X_sub_C]
  calc
    ‖∑ i ∈ Finset.Icc (m + 1) Q.natDegree,
        ζ ^ (i - (m + 1)) * Q.coeff i‖
        ≤ ∑ i ∈ Finset.Icc (m + 1) Q.natDegree,
            ‖ζ ^ (i - (m + 1)) * Q.coeff i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.Icc (m + 1) Q.natDegree,
          ρ ^ Q.natDegree * ‖Q.coeff i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hexp : i - (m + 1) ≤ Q.natDegree := by
        exact le_trans (Nat.sub_le i (m + 1)) (Finset.mem_Icc.mp hi).2
      exact (pow_le_pow_left₀ (norm_nonneg ζ) hζ _).trans
        (pow_le_pow_right₀ hρ hexp)
    _ ≤ ∑ i ∈ Finset.range (Q.natDegree + 1),
          ρ ^ Q.natDegree * ‖Q.coeff i‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_Icc.mp hi).2)
      · intro i hi hnot
        positivity
    _ = ρ ^ Q.natDegree * coeffNormSum Q := by
      rw [coeffNormSum, Finset.mul_sum]

noncomputable def contourHermiteCoeff (Q : Polynomial ℂ) (ρ : ℝ) (z : ℂ) (m : ℕ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    ∮ ζ in C(0, ρ), Complex.exp (z * ζ) * (contourQuotient Q ζ).coeff m / Q.eval ζ

theorem norm_contourHermiteCoeff_le (Q : Polynomial ℂ) {ρ C δ : ℝ}
    (hρ : 1 ≤ ρ) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hcoeff : coeffNormSum Q ≤ C)
    (hden : ∀ ζ ∈ sphere (0 : ℂ) ρ, δ ≤ ‖Q.eval ζ‖)
    (z : ℂ) (m : ℕ) :
    ‖contourHermiteCoeff Q ρ z m‖ ≤
      ρ * (Real.exp (‖z‖ * ρ) * (ρ ^ Q.natDegree * C) / δ) := by
  unfold contourHermiteCoeff
  have hρ0 : 0 ≤ ρ := le_trans zero_le_one hρ
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ0
  intro ζ hζ
  have hζnorm : ‖ζ‖ = ρ := by simpa [mem_sphere_iff_norm] using hζ
  have hquot := norm_coeff_contourQuotient_le Q ζ m hρ hζnorm.le
  have hq : ‖(contourQuotient Q ζ).coeff m‖ ≤ ρ ^ Q.natDegree * C :=
    hquot.trans (mul_le_mul_of_nonneg_left hcoeff (by positivity))
  have hexp : ‖Complex.exp (z * ζ)‖ ≤ Real.exp (‖z‖ * ρ) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      (z * ζ).re ≤ ‖z * ζ‖ := Complex.re_le_norm _
      _ = ‖z‖ * ρ := by rw [norm_mul, hζnorm]
  rw [norm_div, norm_mul]
  have hnum : ‖Complex.exp (z * ζ)‖ * ‖(contourQuotient Q ζ).coeff m‖ ≤
      Real.exp (‖z‖ * ρ) * (ρ ^ Q.natDegree * C) :=
    mul_le_mul hexp hq (norm_nonneg _) (Real.exp_pos _).le
  calc
    ‖Complex.exp (z * ζ)‖ * ‖(contourQuotient Q ζ).coeff m‖ / ‖Q.eval ζ‖ ≤
        (Real.exp (‖z‖ * ρ) * (ρ ^ Q.natDegree * C)) / ‖Q.eval ζ‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (Real.exp (‖z‖ * ρ) * (ρ ^ Q.natDegree * C)) / δ :=
      div_le_div_of_nonneg_left
        (mul_nonneg (Real.exp_pos _).le (mul_nonneg (pow_nonneg hρ0 _) hC))
        hδ (hden ζ hζ)

noncomputable def contourHermitePolynomial (Q : Polynomial ℂ) (ρ : ℝ) (z : ℂ) :
    Polynomial ℂ :=
  ∑ m ∈ Finset.range (Q.natDegree + 1),
    Polynomial.C (contourHermiteCoeff Q ρ z m) * Polynomial.X ^ m

theorem continuous_contourQuotient_coeff (Q : Polynomial ℂ) (m : ℕ) :
    Continuous fun ζ : ℂ => (contourQuotient Q ζ).coeff m := by
  simp only [contourQuotient, Polynomial.coeff_divByMonic_X_sub_C]
  fun_prop

theorem contourHermitePolynomial_eval_eq_integral (Q : Polynomial ℂ) {ρ δ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ)
    (hden : ∀ ζ ∈ sphere (0 : ℂ) ρ, δ ≤ ‖Q.eval ζ‖)
    (z w : ℂ) :
    (contourHermitePolynomial Q ρ z).eval w =
      (2 * Real.pi * Complex.I)⁻¹ *
        ∮ ζ in C(0, ρ),
          Complex.exp (z * ζ) * (contourQuotient Q ζ).eval w / Q.eval ζ := by
  have hQne : ∀ ζ ∈ sphere (0 : ℂ) ρ, Q.eval ζ ≠ 0 := by
    intro ζ hζ hzero
    have := hden ζ hζ
    rw [hzero, norm_zero] at this
    linarith
  have hint : ∀ m ∈ Finset.range (Q.natDegree + 1),
      CircleIntegrable
        (fun ζ : ℂ => Complex.exp (z * ζ) * (contourQuotient Q ζ).coeff m /
          Q.eval ζ * w ^ m) 0 ρ := by
    intro m hm
    refine ContinuousOn.circleIntegrable hρ.le ?_
    refine ((((Complex.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_contourQuotient_coeff Q m)).continuousOn).div
        Q.continuous.continuousOn ?_).mul continuousOn_const
    exact hQne
  unfold contourHermitePolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, contourHermiteCoeff]
  have hmove : ∀ m ∈ Finset.range (Q.natDegree + 1),
      ((2 * Real.pi * Complex.I)⁻¹ *
          ∮ ζ in C(0, ρ),
            Complex.exp (z * ζ) * (contourQuotient Q ζ).coeff m / Q.eval ζ) * w ^ m =
        (2 * Real.pi * Complex.I)⁻¹ *
          ∮ ζ in C(0, ρ),
            (Complex.exp (z * ζ) * (contourQuotient Q ζ).coeff m / Q.eval ζ) *
              w ^ m := by
    intro m hm
    have hi := circleIntegral.integral_smul_const
      (fun ζ : ℂ => Complex.exp (z * ζ) * (contourQuotient Q ζ).coeff m /
        Q.eval ζ) (w ^ m) 0 ρ
    simp only [smul_eq_mul] at hi
    rw [hi]
    ring
  rw [Finset.sum_congr rfl hmove, ← Finset.mul_sum,
    ← HTGeometry.circleIntegral_finset_sum
      (fun (m : ℕ) (ζ : ℂ) =>
        (Complex.exp (z * ζ) * (contourQuotient Q ζ).coeff m / Q.eval ζ) * w ^ m)
      0 ρ (Finset.range (Q.natDegree + 1)) hint]
  congr 1
  refine circleIntegral.integral_congr hρ.le fun ζ hζ => ?_
  have hdeg : (contourQuotient Q ζ).natDegree < Q.natDegree + 1 := by
    exact lt_of_le_of_lt (Polynomial.natDegree_le_natDegree
      (Polynomial.degree_divByMonic_le Q (Polynomial.X - Polynomial.C ζ)))
      (Nat.lt_succ_self _)
  rw [Polynomial.eval_eq_sum_range' hdeg]
  simp only [div_eq_mul_inv]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  ring

noncomputable def contourHermiteQuotient (Q : Polynomial ℂ) (ρ : ℝ) (z w : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    ∮ ζ in C(0, ρ), Complex.exp (z * ζ) / ((ζ - w) * Q.eval ζ)

theorem contourHermitePolynomial_eval_eq_exp_sub (Q : Polynomial ℂ) {ρ δ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ)
    (hden : ∀ ζ ∈ sphere (0 : ℂ) ρ, δ ≤ ‖Q.eval ζ‖)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ) (z : ℂ) :
    (contourHermitePolynomial Q ρ z).eval w =
      Complex.exp (z * w) - Q.eval w * contourHermiteQuotient Q ρ z w := by
  have hQne : ∀ ζ ∈ sphere (0 : ℂ) ρ, Q.eval ζ ≠ 0 := by
    intro ζ hζ hzero
    have := hden ζ hζ
    rw [hzero, norm_zero] at this
    linarith
  have hzw : ∀ ζ ∈ sphere (0 : ℂ) ρ, ζ - w ≠ 0 := by
    intro ζ hζ hzero
    have hEq : ζ = w := sub_eq_zero.mp hzero
    have hnorm : ‖ζ‖ = ρ := by simpa [mem_sphere_iff_norm] using hζ
    have hw' : ‖w‖ < ρ := by simpa [mem_ball, dist_zero_right] using hw
    rw [hEq] at hnorm
    linarith
  have hcauchyInt : CircleIntegrable
      (fun ζ : ℂ => (ζ - w)⁻¹ * Complex.exp (z * ζ)) 0 ρ := by
    refine ContinuousOn.circleIntegrable hρ.le ?_
    exact ((continuousOn_id.sub continuousOn_const).inv₀ hzw).mul
      (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hquotInt : CircleIntegrable
      (fun ζ : ℂ => Complex.exp (z * ζ) / ((ζ - w) * Q.eval ζ)) 0 ρ := by
    refine ContinuousOn.circleIntegrable hρ.le ?_
    refine (Complex.continuous_exp.comp
      (continuous_const.mul continuous_id)).continuousOn.div
        (((continuousOn_id.sub continuousOn_const).mul Q.continuous.continuousOn)) ?_
    intro ζ hζ
    exact mul_ne_zero (hzw ζ hζ) (hQne ζ hζ)
  have hcauchy :
      (2 * Real.pi * Complex.I)⁻¹ *
          (∮ ζ in C(0, ρ), (ζ - w)⁻¹ * Complex.exp (z * ζ)) =
        Complex.exp (z * w) := by
    simpa only [Function.comp_apply, Pi.mul_apply, id_eq, smul_eq_mul] using
      (two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        (E := ℂ) (s := (∅ : Set ℂ)) Set.countable_empty hw
        (Complex.continuous_exp.comp
          (continuous_const.mul continuous_id)).continuousOn
        (fun _ _ => by fun_prop))
  rw [contourHermitePolynomial_eval_eq_integral Q hρ hδ hden z w]
  have hcongr :
      (∮ ζ in C(0, ρ),
          Complex.exp (z * ζ) * (contourQuotient Q ζ).eval w / Q.eval ζ) =
        ∮ ζ in C(0, ρ),
          (ζ - w)⁻¹ * Complex.exp (z * ζ) -
            Q.eval w * (Complex.exp (z * ζ) / ((ζ - w) * Q.eval ζ)) := by
    refine circleIntegral.integral_congr hρ.le fun ζ hζ => ?_
    have hQ := hQne ζ hζ
    have hsub := hzw ζ hζ
    have hid := eval_contourQuotient Q ζ w
    have hD : (contourQuotient Q ζ).eval w =
        (Q.eval ζ - Q.eval w) / (ζ - w) := by
      apply (eq_div_iff hsub).2
      simpa [mul_comm] using hid.symm
    rw [hD]
    field_simp [hQ, hsub]
  have hscaledInt : CircleIntegrable
      (fun ζ : ℂ => Q.eval w * (Complex.exp (z * ζ) / ((ζ - w) * Q.eval ζ))) 0 ρ := by
    refine ContinuousOn.circleIntegrable hρ.le ?_
    exact continuousOn_const.mul
      ((Complex.continuous_exp.comp
        (continuous_const.mul continuous_id)).continuousOn.div
          (((continuousOn_id.sub continuousOn_const).mul Q.continuous.continuousOn))
          (fun ζ hζ => mul_ne_zero (hzw ζ hζ) (hQne ζ hζ)))
  rw [hcongr, circleIntegral.integral_sub hcauchyInt hscaledInt]
  have hsmul := circleIntegral.integral_smul (Q.eval w)
    (fun ζ : ℂ => Complex.exp (z * ζ) / ((ζ - w) * Q.eval ζ)) 0 ρ
  simp only [smul_eq_mul] at hsmul
  rw [hsmul]
  unfold contourHermiteQuotient
  rw [mul_sub, hcauchy]
  ring

theorem analyticAt_contourHermiteQuotient (Q : Polynomial ℂ) {ρ δ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ)
    (hden : ∀ ζ ∈ sphere (0 : ℂ) ρ, δ ≤ ‖Q.eval ζ‖)
    (z : ℂ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ) :
    AnalyticAt ℂ (contourHermiteQuotient Q ρ z) w := by
  let F : (Fin 2 → ℂ) → ℂ :=
    (fun x => Complex.exp (z * x 0)) *
      (fun x => (x 0 - x 1) * Q.eval (x 0))⁻¹
  let U : Set (Fin 2 → ℂ) := {x | (x 0 - x 1) * Q.eval (x 0) ≠ 0}
  let V : Set (Fin 1 → ℂ) := {y | y 0 ∈ ball (0 : ℂ) ρ}
  have hUopen : IsOpen U := by
    exact isOpen_ne.preimage (by fun_prop)
  have hVopen : IsOpen V := by
    exact isOpen_ball.preimage (continuous_apply 0)
  have hFdiff : DifferentiableOn ℂ F U := by
    intro x hx
    change (x 0 - x 1) * Q.eval (x 0) ≠ 0 at hx
    change DifferentiableWithinAt ℂ
      ((fun x : Fin 2 → ℂ => Complex.exp (z * x 0)) *
        (fun x : Fin 2 → ℂ => (x 0 - x 1) * Q.eval (x 0))⁻¹) U x
    have hnum : DifferentiableAt ℂ
        (fun x : Fin 2 → ℂ => Complex.exp (z * x 0)) x := by fun_prop
    have hdenom : DifferentiableAt ℂ
        (fun x : Fin 2 → ℂ => (x 0 - x 1) * Q.eval (x 0)) x := by fun_prop
    exact (hnum.mul (hdenom.inv hx)).differentiableWithinAt
  have hQne : ∀ ζ ∈ sphere (0 : ℂ) ρ, Q.eval ζ ≠ 0 := by
    intro ζ hζ hzero
    have := hden ζ hζ
    rw [hzero, norm_zero] at this
    linarith
  have hmemU : ∀ (θ : ℝ) (y : Fin 1 → ℂ), y ∈ V →
      (Fin.cons (circleMap 0 ρ θ) y : Fin 2 → ℂ) ∈ U := by
    intro θ y hy
    have hcircle : circleMap 0 ρ θ ∈ sphere (0 : ℂ) ρ := by
      rw [mem_sphere_iff_norm]
      simpa using abs_of_pos hρ
    have hsep : circleMap 0 ρ θ - y 0 ≠ 0 := by
      intro hzero
      have heq : circleMap 0 ρ θ = y 0 := sub_eq_zero.mp hzero
      have hynorm : ‖y 0‖ < ρ := by
        simpa [V, mem_ball, dist_zero_right] using hy
      have hcnorm : ‖circleMap 0 ρ θ‖ = ρ := by
        simpa [mem_sphere_iff_norm] using hcircle
      rw [heq] at hcnorm
      linarith
    change (circleMap 0 ρ θ - y 0) * Q.eval (circleMap 0 ρ θ) ≠ 0
    exact mul_ne_zero hsep (hQne _ hcircle)
  have hdiffOn : DifferentiableOn ℂ (contourHermiteQuotient Q ρ z) (ball 0 ρ) := by
    intro u hu
    let y : Fin 1 → ℂ := fun _ => u
    have hy : y ∈ V := by simpa [y, V] using hu
    have hvec := differentiableAt_circleIntegral_slice_open
      (n := 1) hUopen hVopen hFdiff hρ (fun _ => (1 : ℂ)) (by fun_prop)
      hmemU hy
    have hscalar : DifferentiableAt ℂ
        (fun v : ℂ => ∮ ζ in C(0, ρ), (1 : ℂ) • F (Fin.cons ζ (fun _ : Fin 1 => v))) u := by
      have hemb : DifferentiableAt ℂ (fun v : ℂ => fun _ : Fin 1 => v) u := by
        fun_prop
      change DifferentiableAt ℂ
        ((fun y : Fin 1 → ℂ => ∮ ζ in C(0, ρ), (1 : ℂ) • F (Fin.cons ζ y)) ∘
          (fun v : ℂ => fun _ : Fin 1 => v)) u
      simpa [y] using hvec.comp u hemb
    have heq : (fun v : ℂ => contourHermiteQuotient Q ρ z v) =
        fun v : ℂ => (2 * Real.pi * Complex.I)⁻¹ *
          ∮ ζ in C(0, ρ), (1 : ℂ) • F (Fin.cons ζ (fun _ : Fin 1 => v)) := by
      funext v
      simp [contourHermiteQuotient, F, div_eq_mul_inv, mul_inv_rev, mul_comm]
    have hr := hscalar.const_mul (2 * Real.pi * Complex.I)⁻¹
    rw [← heq] at hr
    exact hr.differentiableWithinAt
  exact (hdiffOn.analyticOnNhd isOpen_ball) w hw

theorem iteratedDeriv_contourHermitePolynomial_eq_exp
    (Q : Polynomial ℂ) {ρ δ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ)
    (hden : ∀ ζ ∈ sphere (0 : ℂ) ρ, δ ≤ ‖Q.eval ζ‖)
    (z η : ℂ) {K k : ℕ}
    (hdvd : (Polynomial.X - Polynomial.C η) ^ K ∣ Q)
    (hη : η ∈ ball (0 : ℂ) ρ) (hk : k < K) :
    iteratedDeriv k (fun w : ℂ => (contourHermitePolynomial Q ρ z).eval w) η =
      iteratedDeriv k (fun w : ℂ => Complex.exp (z * w)) η := by
  let H : ℂ → ℂ := fun w => (contourHermitePolynomial Q ρ z).eval w
  let E : ℂ → ℂ := fun w => Complex.exp (z * w)
  let J : ℂ → ℂ := contourHermiteQuotient Q ρ z
  have hH : AnalyticAt ℂ H η := by
    dsimp [H]
    simpa using (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) η).aeval_polynomial
      (contourHermitePolynomial Q ρ z)
  have hE : AnalyticAt ℂ E η := by
    dsimp [E]
    fun_prop
  have hJ : AnalyticAt ℂ J η := by
    exact analyticAt_contourHermiteQuotient Q hρ hδ hden z hη
  have hevent : (H - E) =ᶠ[nhds η] -(fun w => Q.eval w * J w) := by
    filter_upwards [isOpen_ball.eventually_mem hη] with w hw
    rw [Pi.sub_apply, Pi.neg_apply]
    dsimp [H, E, J]
    rw [contourHermitePolynomial_eval_eq_exp_sub Q hρ hδ hden hw z]
    ring
  have hleft : AnalyticAt ℂ (H - E) η := hH.sub hE
  have hQ : AnalyticAt ℂ (fun w : ℂ => Q.eval w) η := by
    simpa using (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) η).aeval_polynomial Q
  have hright : AnalyticAt ℂ (-(fun w => Q.eval w * J w)) η := by
    exact (hQ.mul hJ).neg
  obtain ⟨S, hS⟩ := hdvd
  have hQfun : (fun w : ℂ => Q.eval w) =
      (fun w : ℂ => (w - η) ^ K) * (fun w : ℂ => S.eval w) := by
    funext w
    rw [hS]
    simp
  have hcenter : AnalyticAt ℂ (fun w : ℂ => (w - η) ^ K) η := by fun_prop
  have hS : AnalyticAt ℂ (fun w : ℂ => S.eval w) η := by
    simpa using (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) η).aeval_polynomial S
  have hcenterOrder : analyticOrderAt (fun w : ℂ => (w - η) ^ K) η = (K : ℕ∞) := by
    change analyticOrderAt ((fun w : ℂ => w - η) ^ K) η = (K : ℕ∞)
    exact analyticOrderAt_centeredMonomial
  have hordQ : (K : ℕ∞) ≤ analyticOrderAt (fun w : ℂ => Q.eval w) η := by
    rw [hQfun, analyticOrderAt_mul hcenter hS, hcenterOrder]
    simp
  have hordRight : (K : ℕ∞) ≤
      analyticOrderAt (-(fun w => Q.eval w * J w)) η := by
    change (K : ℕ∞) ≤ analyticOrderAt (-((fun w : ℂ => Q.eval w) * J)) η
    rw [analyticOrderAt_neg, analyticOrderAt_mul hQ hJ]
    exact hordQ.trans (by simp)
  have hordLeft : (K : ℕ∞) ≤ analyticOrderAt (H - E) η := by
    rw [analyticOrderAt_congr hevent]
    exact hordRight
  have hzero : iteratedDeriv k (H - E) η = 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hleft).mp hordLeft k hk
  rw [iteratedDeriv_sub hH.contDiffAt hE.contDiffAt] at hzero
  exact sub_eq_zero.mp hzero

end GaloisForLFunctions.RHTower.BakerGeneralProof

