import GaloisForLFunctions.HTGeometry.ConformalMetricDalembertian
import GaloisForLFunctions.HTGeometry.ConformalClockDiffusion

/-!
# Realization of the exponential clock calculus by a smooth metric d'Alembertian

The abstract `ExponentialSecondOrderClockCalculus` is realized on the algebra of smooth real
functions of `d` coordinates: `laplacian` is the divergence-form d'Alembertian of a smooth metric
chart, `gamma` is its carré du champ, and `expSmul c σ = e^{cσ}`.

Every structural axiom is proved from the coordinate product rule; the symmetry of the
inverse-metric field is what makes the carré du champ symmetric and hence makes the second-order
Leibniz rule hold with the factor `2`.

Consequently the general-dimensional conformal conjugation law at `a = (d-2)/2` holds for a
literal smooth nondegenerate metric field.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ContDiff

section Algebra

variable {d : ℕ}

/-- The `ℝ`-algebra of smooth real functions of `d` coordinates. -/
def smoothScalarAlgebra (d : ℕ) : Subalgebra ℝ ((Fin d → ℝ) → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  mul_mem' := by
    intro a b ha hb
    show ContDiff ℝ ∞ fun x => a x * b x
    exact ContDiff.mul ha hb
  one_mem' := by
    show ContDiff ℝ ∞ fun _ : Fin d → ℝ => (1 : ℝ)
    exact contDiff_const
  add_mem' := by
    intro a b ha hb
    show ContDiff ℝ ∞ fun x => a x + b x
    exact ContDiff.add ha hb
  zero_mem' := by
    show ContDiff ℝ ∞ fun _ : Fin d → ℝ => (0 : ℝ)
    exact contDiff_const
  algebraMap_mem' := by
    intro r
    show ContDiff ℝ ∞ fun _ : Fin d → ℝ => r
    exact contDiff_const

theorem contDiff_smoothScalar (f : ↥(smoothScalarAlgebra d)) :
    ContDiff ℝ ∞ (f : (Fin d → ℝ) → ℝ) := f.2

@[simp] theorem smoothScalarAlgebra_coe_mul (f g : ↥(smoothScalarAlgebra d)) :
    ((f * g : ↥(smoothScalarAlgebra d)) : (Fin d → ℝ) → ℝ) =
      (f : (Fin d → ℝ) → ℝ) * (g : (Fin d → ℝ) → ℝ) := rfl

@[simp] theorem smoothScalarAlgebra_coe_add (f g : ↥(smoothScalarAlgebra d)) :
    ((f + g : ↥(smoothScalarAlgebra d)) : (Fin d → ℝ) → ℝ) =
      (f : (Fin d → ℝ) → ℝ) + (g : (Fin d → ℝ) → ℝ) := rfl

@[simp] theorem smoothScalarAlgebra_coe_sub (f g : ↥(smoothScalarAlgebra d)) :
    ((f - g : ↥(smoothScalarAlgebra d)) : (Fin d → ℝ) → ℝ) =
      (f : (Fin d → ℝ) → ℝ) - (g : (Fin d → ℝ) → ℝ) := rfl

@[simp] theorem smoothScalarAlgebra_coe_one :
    ((1 : ↥(smoothScalarAlgebra d)) : (Fin d → ℝ) → ℝ) = 1 := rfl

@[simp] theorem smoothScalarAlgebra_coe_smul (c : ℝ) (f : ↥(smoothScalarAlgebra d)) :
    ((c • f : ↥(smoothScalarAlgebra d)) : (Fin d → ℝ) → ℝ) =
      c • (f : (Fin d → ℝ) → ℝ) := rfl

@[simp] theorem smoothScalarAlgebra_coe_two_apply (x : Fin d → ℝ) :
    ((2 : ↥(smoothScalarAlgebra d)) : (Fin d → ℝ) → ℝ) x = 2 := rfl

/-- The conformal weight `e^{cσ}` as a smooth scalar. -/
noncomputable def smoothExpSmul (c : ℝ) (sigma : ↥(smoothScalarAlgebra d)) :
    ↥(smoothScalarAlgebra d) :=
  ⟨fun x => Real.exp (c * (sigma : (Fin d → ℝ) → ℝ) x),
    ContDiff.exp (contDiff_const.mul (contDiff_smoothScalar sigma))⟩

@[simp] theorem smoothExpSmul_coe (c : ℝ) (sigma : ↥(smoothScalarAlgebra d)) :
    ((smoothExpSmul c sigma : ↥(smoothScalarAlgebra d)) : (Fin d → ℝ) → ℝ) =
      fun x => Real.exp (c * (sigma : (Fin d → ℝ) → ℝ) x) := rfl

end Algebra

namespace SmoothMetricChart

variable {d : ℕ} (M : SmoothMetricChart d)

/-! ### Product and exponential rules for the metric d'Alembertian -/

theorem flux_const (c : ℝ) (i : Fin d) : M.flux (fun _ => c) i = fun _ => 0 := by
  funext x
  simp [flux, coordPartial_const]

theorem dalembert_const (c : ℝ) (x : Fin d → ℝ) : M.dalembert (fun _ => c) x = 0 := by
  simp only [dalembert, M.flux_const c]
  simp [coordPartial_const]

theorem gradPair_const_left (c : ℝ) (h : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    M.gradPair (fun _ => c) h x = 0 := by
  simp [gradPair, coordPartial_const]

theorem gradPair_const_right (c : ℝ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    M.gradPair f (fun _ => c) x = 0 := by
  simp [gradPair, coordPartial_const]

/-- Symmetry of the inverse metric makes the carré du champ symmetric. -/
theorem gradPair_comm (f h : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    M.gradPair f h x = M.gradPair h f x := by
  simp only [gradPair]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [M.inverseMetric_symm x b a]
  ring

theorem flux_mul {f h : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (i : Fin d) :
    M.flux (fun y => f y * h y) i =
      fun x => f x * M.flux h i x + h x * M.flux f i x := by
  funext x
  have hpd : ∀ j : Fin d, coordPartial j (fun y => f y * h y) x =
      f x * coordPartial j h x + h x * coordPartial j f x := fun j =>
    coordPartial_mul (differentiableAt_of_contDiff_infty hf x)
      (differentiableAt_of_contDiff_infty hh x) j
  simp only [flux]
  have hstep : ∑ j, M.inverseMetric x i j * coordPartial j (fun y => f y * h y) x =
      f x * (∑ j, M.inverseMetric x i j * coordPartial j h x) +
        h x * (∑ j, M.inverseMetric x i j * coordPartial j f x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hpd j]; ring
  rw [hstep]
  ring

theorem gradPair_mul_left {f h : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hh : ContDiff ℝ ∞ h) (k : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    M.gradPair (fun y => f y * h y) k x =
      f x * M.gradPair h k x + h x * M.gradPair f k x := by
  have hpd : ∀ i : Fin d, coordPartial i (fun y => f y * h y) x =
      f x * coordPartial i h x + h x * coordPartial i f x := fun i =>
    coordPartial_mul (differentiableAt_of_contDiff_infty hf x)
      (differentiableAt_of_contDiff_infty hh x) i
  simp only [gradPair]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hpd i, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem gradPair_mul_right (f : (Fin d → ℝ) → ℝ) {h k : (Fin d → ℝ) → ℝ}
    (hh : ContDiff ℝ ∞ h) (hk : ContDiff ℝ ∞ k) (x : Fin d → ℝ) :
    M.gradPair f (fun y => h y * k y) x =
      h x * M.gradPair f k x + k x * M.gradPair f h x := by
  rw [M.gradPair_comm f (fun y => h y * k y) x, M.gradPair_mul_left hh hk f x,
    M.gradPair_comm k f x, M.gradPair_comm h f x]

/-- Second-order Leibniz rule of the metric d'Alembertian. -/
theorem dalembert_mul {f h : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (x : Fin d → ℝ) :
    M.dalembert (fun y => f y * h y) x =
      f x * M.dalembert h x + h x * M.dalembert f x + 2 * M.gradPair f h x := by
  have hfluxf := M.contDiff_flux hf
  have hfluxh := M.contDiff_flux hh
  have hd : ∀ i : Fin d,
      coordPartial i (M.flux (fun y => f y * h y) i) x =
        f x * coordPartial i (M.flux h i) x + M.flux h i x * coordPartial i f x +
          (h x * coordPartial i (M.flux f i) x + M.flux f i x * coordPartial i h x) := by
    intro i
    rw [M.flux_mul hf hh i]
    rw [coordPartial_add
      (differentiableAt_of_contDiff_infty (hf.mul (hfluxh i)) x)
      (differentiableAt_of_contDiff_infty (hh.mul (hfluxf i)) x) i]
    rw [coordPartial_mul (differentiableAt_of_contDiff_infty hf x)
        (differentiableAt_of_contDiff_infty (hfluxh i) x) i,
      coordPartial_mul (differentiableAt_of_contDiff_infty hh x)
        (differentiableAt_of_contDiff_infty (hfluxf i) x) i]
  have hsplit : ∑ i, coordPartial i (M.flux (fun y => f y * h y) i) x =
      f x * (∑ i, coordPartial i (M.flux h i) x) +
        h x * (∑ i, coordPartial i (M.flux f i) x) +
        (∑ i, coordPartial i f x * M.flux h i x) +
        (∑ i, coordPartial i h x * M.flux f i x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hd i]; ring
  have h1 := M.inv_density_mul_sum_flux f h x
  have h2 := M.inv_density_mul_sum_flux h f x
  have h3 := M.gradPair_comm h f x
  simp only [dalembert]
  rw [hsplit]
  have hring : (M.density x)⁻¹ *
      (f x * (∑ i, coordPartial i (M.flux h i) x) +
        h x * (∑ i, coordPartial i (M.flux f i) x) +
        (∑ i, coordPartial i f x * M.flux h i x) +
        (∑ i, coordPartial i h x * M.flux f i x)) =
      f x * ((M.density x)⁻¹ * ∑ i, coordPartial i (M.flux h i) x) +
        h x * ((M.density x)⁻¹ * ∑ i, coordPartial i (M.flux f i) x) +
        ((M.density x)⁻¹ * ∑ i, coordPartial i f x * M.flux h i x) +
        ((M.density x)⁻¹ * ∑ i, coordPartial i h x * M.flux f i x) := by ring
  rw [hring, h1, h2, h3]
  ring

theorem flux_expSmul (c : ℝ) {sigma : (Fin d → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    (i : Fin d) :
    M.flux (fun y => Real.exp (c * sigma y)) i =
      fun x => c * Real.exp (c * sigma x) * M.flux sigma i x := by
  funext x
  have hcsigma : DifferentiableAt ℝ (fun y => c * sigma y) x :=
    (differentiableAt_of_contDiff_infty hsigma x).const_mul c
  have hpd : ∀ j : Fin d, coordPartial j (fun y => Real.exp (c * sigma y)) x =
      Real.exp (c * sigma x) * (c * coordPartial j sigma x) := by
    intro j
    rw [coordPartial_exp hcsigma j,
      coordPartial_const_mul (differentiableAt_of_contDiff_infty hsigma x) c j]
  simp only [flux]
  have hstep : ∑ j, M.inverseMetric x i j * coordPartial j (fun y => Real.exp (c * sigma y)) x =
      c * Real.exp (c * sigma x) * ∑ j, M.inverseMetric x i j * coordPartial j sigma x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hpd j]; ring
  rw [hstep]
  ring

theorem gradPair_expSmul_left (c : ℝ) {sigma : (Fin d → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    (u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    M.gradPair (fun y => Real.exp (c * sigma y)) u x =
      Real.exp (c * sigma x) * (c * M.gradPair sigma u x) := by
  have hcsigma : DifferentiableAt ℝ (fun y => c * sigma y) x :=
    (differentiableAt_of_contDiff_infty hsigma x).const_mul c
  have hpd : ∀ i : Fin d, coordPartial i (fun y => Real.exp (c * sigma y)) x =
      Real.exp (c * sigma x) * (c * coordPartial i sigma x) := by
    intro i
    rw [coordPartial_exp hcsigma i,
      coordPartial_const_mul (differentiableAt_of_contDiff_infty hsigma x) c i]
  simp only [gradPair]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [hpd i]; ring

theorem gradPair_expSmul_right (c : ℝ) {sigma : (Fin d → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    (u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    M.gradPair u (fun y => Real.exp (c * sigma y)) x =
      Real.exp (c * sigma x) * (c * M.gradPair u sigma x) := by
  rw [M.gradPair_comm u (fun y => Real.exp (c * sigma y)) x,
    M.gradPair_expSmul_left c hsigma u x, M.gradPair_comm sigma u x]

/-- Exponential chain rule of the metric d'Alembertian. -/
theorem dalembert_expSmul (c : ℝ) {sigma : (Fin d → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    (x : Fin d → ℝ) :
    M.dalembert (fun y => Real.exp (c * sigma y)) x =
      Real.exp (c * sigma x) *
        (c * M.dalembert sigma x + c ^ 2 * M.gradPair sigma sigma x) := by
  have hcsigma : DifferentiableAt ℝ (fun y => c * sigma y) x :=
    (differentiableAt_of_contDiff_infty hsigma x).const_mul c
  have hexpd : DifferentiableAt ℝ (fun y => Real.exp (c * sigma y)) x := hcsigma.exp
  have hweightd : DifferentiableAt ℝ (fun y => c * Real.exp (c * sigma y)) x :=
    hexpd.const_mul c
  have hfluxsigma := M.contDiff_flux hsigma
  have hd : ∀ i : Fin d,
      coordPartial i (M.flux (fun y => Real.exp (c * sigma y)) i) x =
        c * Real.exp (c * sigma x) * coordPartial i (M.flux sigma i) x +
          M.flux sigma i x * (c * (Real.exp (c * sigma x) * (c * coordPartial i sigma x))) := by
    intro i
    rw [M.flux_expSmul c hsigma i]
    rw [coordPartial_mul hweightd (differentiableAt_of_contDiff_infty (hfluxsigma i) x) i]
    rw [coordPartial_const_mul hexpd c i, coordPartial_exp hcsigma i,
      coordPartial_const_mul (differentiableAt_of_contDiff_infty hsigma x) c i]
  have hsplit : ∑ i, coordPartial i (M.flux (fun y => Real.exp (c * sigma y)) i) x =
      c * Real.exp (c * sigma x) * (∑ i, coordPartial i (M.flux sigma i) x) +
        c ^ 2 * Real.exp (c * sigma x) * (∑ i, coordPartial i sigma x * M.flux sigma i x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hd i]; ring
  have h1 := M.inv_density_mul_sum_flux sigma sigma x
  simp only [dalembert]
  rw [hsplit]
  have hring : (M.density x)⁻¹ *
      (c * Real.exp (c * sigma x) * (∑ i, coordPartial i (M.flux sigma i) x) +
        c ^ 2 * Real.exp (c * sigma x) * (∑ i, coordPartial i sigma x * M.flux sigma i x)) =
      c * Real.exp (c * sigma x) *
          ((M.density x)⁻¹ * ∑ i, coordPartial i (M.flux sigma i) x) +
        c ^ 2 * Real.exp (c * sigma x) *
          ((M.density x)⁻¹ * ∑ i, coordPartial i sigma x * M.flux sigma i x) := by ring
  rw [hring, h1]
  ring

/-! ### The realized clock calculus -/

/-- The d'Alembertian as an operator on the algebra of smooth scalars. -/
noncomputable def clockLaplacian (f : ↥(smoothScalarAlgebra d)) : ↥(smoothScalarAlgebra d) :=
  ⟨M.dalembert (f : (Fin d → ℝ) → ℝ), M.contDiff_dalembert (contDiff_smoothScalar f)⟩

/-- The carré du champ as a bilinear operation on the algebra of smooth scalars. -/
noncomputable def clockGamma (f h : ↥(smoothScalarAlgebra d)) : ↥(smoothScalarAlgebra d) :=
  ⟨M.gradPair (f : (Fin d → ℝ) → ℝ) (h : (Fin d → ℝ) → ℝ),
    M.contDiff_gradPair (contDiff_smoothScalar f) (contDiff_smoothScalar h)⟩

@[simp] theorem clockLaplacian_coe (f : ↥(smoothScalarAlgebra d)) :
    ((M.clockLaplacian f : ↥(smoothScalarAlgebra d)) : (Fin d → ℝ) → ℝ) =
      M.dalembert (f : (Fin d → ℝ) → ℝ) := rfl

@[simp] theorem clockGamma_coe (f h : ↥(smoothScalarAlgebra d)) :
    ((M.clockGamma f h : ↥(smoothScalarAlgebra d)) : (Fin d → ℝ) → ℝ) =
      M.gradPair (f : (Fin d → ℝ) → ℝ) (h : (Fin d → ℝ) → ℝ) := rfl

/-- The metric d'Alembertian and its carré du champ form a second-order clock calculus. -/
noncomputable def secondOrderCalculus :
    SecondOrderClockCalculus ↥(smoothScalarAlgebra d) where
  laplacian := M.clockLaplacian
  gamma := M.clockGamma
  laplacian_one := by
    apply Subtype.ext
    funext x
    simp only [clockLaplacian_coe, smoothScalarAlgebra_coe_one, ZeroMemClass.coe_zero,
      Pi.zero_apply]
    exact M.dalembert_const 1 x
  laplacian_mul := by
    intro f h
    apply Subtype.ext
    funext x
    simp only [clockLaplacian_coe, clockGamma_coe, smoothScalarAlgebra_coe_mul,
      smoothScalarAlgebra_coe_add, Pi.mul_apply, Pi.add_apply,
      smoothScalarAlgebra_coe_two_apply]
    exact M.dalembert_mul (contDiff_smoothScalar f) (contDiff_smoothScalar h) x
  gamma_one_left := by
    intro h
    apply Subtype.ext
    funext x
    simp only [clockGamma_coe, smoothScalarAlgebra_coe_one, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact M.gradPair_const_left 1 (h : (Fin d → ℝ) → ℝ) x
  gamma_one_right := by
    intro f
    apply Subtype.ext
    funext x
    simp only [clockGamma_coe, smoothScalarAlgebra_coe_one, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact M.gradPair_const_right 1 (f : (Fin d → ℝ) → ℝ) x
  gamma_mul_left := by
    intro f h k
    apply Subtype.ext
    funext x
    simp only [clockGamma_coe, smoothScalarAlgebra_coe_mul, smoothScalarAlgebra_coe_add,
      Pi.mul_apply, Pi.add_apply]
    exact M.gradPair_mul_left (contDiff_smoothScalar f) (contDiff_smoothScalar h)
      (k : (Fin d → ℝ) → ℝ) x
  gamma_mul_right := by
    intro f h k
    apply Subtype.ext
    funext x
    simp only [clockGamma_coe, smoothScalarAlgebra_coe_mul, smoothScalarAlgebra_coe_add,
      Pi.mul_apply, Pi.add_apply]
    exact M.gradPair_mul_right (f : (Fin d → ℝ) → ℝ) (contDiff_smoothScalar h)
      (contDiff_smoothScalar k) x

@[simp] theorem secondOrderCalculus_laplacian (f : ↥(smoothScalarAlgebra d)) :
    M.secondOrderCalculus.laplacian f = M.clockLaplacian f := rfl

@[simp] theorem secondOrderCalculus_gamma (f h : ↥(smoothScalarAlgebra d)) :
    M.secondOrderCalculus.gamma f h = M.clockGamma f h := rfl

/-- The realized exponential clock calculus of a smooth metric chart. -/
noncomputable def expClockCalculus :
    ExponentialSecondOrderClockCalculus ↥(smoothScalarAlgebra d) where
  toSecondOrder := M.secondOrderCalculus
  expSmul := smoothExpSmul
  expSmul_zero := by
    intro sigma
    apply Subtype.ext
    funext x
    simp [smoothExpSmul]
  expSmul_add := by
    intro c e sigma
    apply Subtype.ext
    funext x
    simp only [smoothExpSmul_coe, smoothScalarAlgebra_coe_mul, Pi.mul_apply]
    rw [← Real.exp_add]
    congr 1
    ring
  laplacian_expSmul := by
    intro c sigma
    apply Subtype.ext
    funext x
    simp only [secondOrderCalculus_laplacian, secondOrderCalculus_gamma, clockLaplacian_coe,
      clockGamma_coe, smoothExpSmul_coe, smoothScalarAlgebra_coe_mul,
      smoothScalarAlgebra_coe_add, smoothScalarAlgebra_coe_smul, Pi.mul_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    exact M.dalembert_expSmul c (contDiff_smoothScalar sigma) x
  gamma_expSmul_left := by
    intro c sigma u
    apply Subtype.ext
    funext x
    simp only [secondOrderCalculus_gamma, clockGamma_coe, smoothExpSmul_coe,
      smoothScalarAlgebra_coe_mul, smoothScalarAlgebra_coe_smul, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul]
    exact M.gradPair_expSmul_left c (contDiff_smoothScalar sigma) (u : (Fin d → ℝ) → ℝ) x
  gamma_expSmul_right := by
    intro c sigma u
    apply Subtype.ext
    funext x
    simp only [secondOrderCalculus_gamma, clockGamma_coe, smoothExpSmul_coe,
      smoothScalarAlgebra_coe_mul, smoothScalarAlgebra_coe_smul, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul]
    exact M.gradPair_expSmul_right c (contDiff_smoothScalar sigma) (u : (Fin d → ℝ) → ℝ) x

/-- The abstract conformal wave operator of the realized calculus at `a = (d-2)/2` is exactly the
d'Alembertian of the conformally rescaled chart. -/
theorem conformalWaveSigma_eq_dalembert_conformalRescale
    (sigma f : ↥(smoothScalarAlgebra d)) :
    ((M.expClockCalculus.conformalWaveSigma
        (ExponentialSecondOrderClockCalculus.conformalDimensionWeight d) sigma f :
          ↥(smoothScalarAlgebra d)) : (Fin d → ℝ) → ℝ) =
      (M.conformalRescale (sigma : (Fin d → ℝ) → ℝ) (contDiff_smoothScalar sigma)).dalembert
        (f : (Fin d → ℝ) → ℝ) := by
  funext x
  rw [M.dalembert_conformalRescale (sigma : (Fin d → ℝ) → ℝ) (contDiff_smoothScalar sigma)
    (contDiff_smoothScalar f) x]
  simp only [ExponentialSecondOrderClockCalculus.conformalWaveSigma, expClockCalculus,
    secondOrderCalculus_laplacian, secondOrderCalculus_gamma, clockLaplacian_coe,
    clockGamma_coe, smoothExpSmul_coe, smoothScalarAlgebra_coe_mul,
    smoothScalarAlgebra_coe_add, smoothScalarAlgebra_coe_smul, Pi.mul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, smoothScalarAlgebra_coe_two_apply,
    ExponentialSecondOrderClockCalculus.conformalDimensionWeight]
  ring

end SmoothMetricChart

end GaloisForLFunctions.HTGeometry
