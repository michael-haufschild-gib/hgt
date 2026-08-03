import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import GaloisForLFunctions.HTGeometry.SmoothMatrixDeterminantCalculus

/-!
# The scalar d'Alembertian of a smooth metric chart and its conformal transformation law

A *smooth metric chart* in dimension `d` is a smooth symmetric inverse-metric field together with
a smooth positive volume density.  Its scalar d'Alembertian is the divergence-form operator

`□ f = ρ⁻¹ ∑ᵢ ∂ᵢ (ρ ∑ⱼ Gⁱʲ ∂ⱼ f)`,

and its carré du champ is `Γ(f,h) = ∑ᵢⱼ Gⁱʲ ∂ᵢ f ∂ⱼ h`.

The main theorem is the exact conformal transformation law: replacing `(G, ρ)` by
`(e^{-2σ} G, e^{dσ} ρ)` — the chart of the conformally rescaled metric `e^{2σ} g` — gives

`□̃ f = e^{-2σ} (□ f + (d - 2) Γ(σ, f))`.

The final section realizes a chart from a genuine nondegenerate smooth symmetric metric field `g`
by `G = g⁻¹` and `ρ = √|det g|`, and shows that literal conformal rescaling of `g` induces exactly
the above rescaling of the chart.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ContDiff

section Partial

variable {d : ℕ}

/-- Coordinate partial derivative in direction `i`. -/
noncomputable def coordPartial (i : Fin d) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i (1 : ℝ))

theorem coordPartial_const (i : Fin d) (c : ℝ) (x : Fin d → ℝ) :
    coordPartial i (fun _ => c) x = 0 := by
  simp [coordPartial]

theorem coordPartial_add {f g : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin d) :
    coordPartial i (fun y => f y + g y) x = coordPartial i f x + coordPartial i g x := by
  have h : (fun y => f y + g y) = f + g := rfl
  simp [coordPartial, h, fderiv_add hf hg]

theorem coordPartial_mul {f g : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin d) :
    coordPartial i (fun y => f y * g y) x =
      f x * coordPartial i g x + g x * coordPartial i f x := by
  have h : (fun y => f y * g y) = f * g := rfl
  simp [coordPartial, h, fderiv_mul hf hg]

theorem coordPartial_const_mul {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : Fin d) :
    coordPartial i (fun y => c * f y) x = c * coordPartial i f x := by
  simp [coordPartial, fderiv_const_mul hf c]

theorem coordPartial_sum {ι : Type*} {s : Finset ι} {F : ι → (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) x) (k : Fin d) :
    coordPartial k (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, coordPartial k (F i) x := by
  simp [coordPartial, fderiv_fun_sum hF]

theorem coordPartial_exp {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (i : Fin d) :
    coordPartial i (fun y => Real.exp (f y)) x = Real.exp (f x) * coordPartial i f x := by
  have h : fderiv ℝ (fun y => Real.exp (f y)) x = Real.exp (f x) • fderiv ℝ f x :=
    (hf.hasFDerivAt.exp).fderiv
  simp [coordPartial, h]

/-- Coordinate partial derivatives preserve smoothness. -/
theorem contDiff_coordPartial {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d) :
    ContDiff ℝ ∞ (coordPartial i f) :=
  ContDiff.clm_apply (contDiff_infty_iff_fderiv.mp hf).2 contDiff_const

theorem differentiableAt_of_contDiff_infty {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : Fin d → ℝ) : DifferentiableAt ℝ f x :=
  (contDiff_infty_iff_fderiv.mp hf).1 x

end Partial

/-- Smooth chart data of a nondegenerate metric: a smooth symmetric inverse-metric field and a
smooth positive volume density. -/
structure SmoothMetricChart (d : ℕ) where
  /-- Contravariant metric coefficients `Gⁱʲ`. -/
  inverseMetric : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ
  /-- Volume density `ρ`. -/
  density : (Fin d → ℝ) → ℝ
  contDiff_inverseMetric : ∀ i j, ContDiff ℝ ∞ fun x => inverseMetric x i j
  contDiff_density : ContDiff ℝ ∞ density
  density_pos : ∀ x, 0 < density x
  inverseMetric_symm : ∀ x i j, inverseMetric x i j = inverseMetric x j i

namespace SmoothMetricChart

variable {d : ℕ} (M : SmoothMetricChart d)

theorem density_ne_zero (x : Fin d → ℝ) : M.density x ≠ 0 :=
  ne_of_gt (M.density_pos x)

/-- A smooth metric chart is determined by its inverse-metric field and its density. -/
theorem ext' {M N : SmoothMetricChart d} (h1 : M.inverseMetric = N.inverseMetric)
    (h2 : M.density = N.density) : M = N := by
  obtain ⟨G, rho, _, _, _, _⟩ := M
  obtain ⟨G', rho', _, _, _, _⟩ := N
  have hG : G = G' := h1
  have hrho : rho = rho' := h2
  subst hG
  subst hrho
  rfl

/-- Carré du champ `Γ(f,h) = ∑ᵢⱼ Gⁱʲ ∂ᵢ f ∂ⱼ h`. -/
noncomputable def gradPair (f h : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, M.inverseMetric x i j * coordPartial i f x * coordPartial j h x

/-- The `i`-th component of the metric flux `ρ Gⁱʲ ∂ⱼ f`. -/
noncomputable def flux (f : (Fin d → ℝ) → ℝ) (i : Fin d) (x : Fin d → ℝ) : ℝ :=
  M.density x * ∑ j, M.inverseMetric x i j * coordPartial j f x

/-- Scalar d'Alembertian in divergence form. -/
noncomputable def dalembert (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  (M.density x)⁻¹ * ∑ i, coordPartial i (M.flux f i) x

theorem contDiff_flux {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d) :
    ContDiff ℝ ∞ (M.flux f i) := by
  refine M.contDiff_density.mul (ContDiff.sum ?_)
  intro j _
  exact (M.contDiff_inverseMetric i j).mul (contDiff_coordPartial hf j)

theorem contDiff_dalembert {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (M.dalembert f) := by
  refine (ContDiff.inv M.contDiff_density M.density_ne_zero).mul (ContDiff.sum ?_)
  intro i _
  exact contDiff_coordPartial (M.contDiff_flux hf i) i

theorem contDiff_gradPair {f h : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (M.gradPair f h) := by
  refine ContDiff.sum ?_
  intro i _
  refine ContDiff.sum ?_
  intro j _
  exact ((M.contDiff_inverseMetric i j).mul (contDiff_coordPartial hf i)).mul
    (contDiff_coordPartial hh j)

/-- The density-weighted flux pairing recovers the carré du champ. -/
theorem inv_density_mul_sum_flux (sigma f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    (M.density x)⁻¹ * ∑ i, coordPartial i sigma x * M.flux f i x = M.gradPair sigma f x := by
  have hstep : ∀ i : Fin d,
      coordPartial i sigma x * M.flux f i x =
        M.density x * ∑ j, M.inverseMetric x i j * coordPartial i sigma x *
          coordPartial j f x := by
    intro i
    simp only [flux, Finset.mul_sum]
    ring_nf
  calc
    (M.density x)⁻¹ * ∑ i, coordPartial i sigma x * M.flux f i x
        = (M.density x)⁻¹ * ∑ i, M.density x *
            ∑ j, M.inverseMetric x i j * coordPartial i sigma x * coordPartial j f x := by
          exact congrArg _ (Finset.sum_congr rfl fun i _ => hstep i)
    _ = (M.density x)⁻¹ * (M.density x *
          ∑ i, ∑ j, M.inverseMetric x i j * coordPartial i sigma x * coordPartial j f x) := by
          rw [← Finset.mul_sum]
    _ = M.gradPair sigma f x := by
          rw [← mul_assoc, inv_mul_cancel₀ (M.density_ne_zero x), one_mul]
          rfl

/-- Chart of the conformally rescaled metric `e^{2σ} g`: the inverse metric picks up `e^{-2σ}`
and the volume density picks up `e^{dσ}`. -/
noncomputable def conformalRescale (sigma : (Fin d → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma) :
    SmoothMetricChart d where
  inverseMetric := fun x => Real.exp (-2 * sigma x) • M.inverseMetric x
  density := fun x => Real.exp ((d : ℝ) * sigma x) * M.density x
  contDiff_inverseMetric := by
    intro i j
    have h : (fun x => (Real.exp (-2 * sigma x) • M.inverseMetric x) i j) =
        fun x => Real.exp (-2 * sigma x) * M.inverseMetric x i j := by
      funext x; simp [Matrix.smul_apply]
    rw [h]
    exact (Real.contDiff_exp.comp (contDiff_const.mul hsigma)).mul (M.contDiff_inverseMetric i j)
  contDiff_density :=
    (Real.contDiff_exp.comp (contDiff_const.mul hsigma)).mul M.contDiff_density
  density_pos := fun x => mul_pos (Real.exp_pos _) (M.density_pos x)
  inverseMetric_symm := by
    intro x i j
    simp [Matrix.smul_apply, M.inverseMetric_symm x i j]

@[simp] theorem conformalRescale_inverseMetric (sigma : (Fin d → ℝ) → ℝ)
    (hsigma : ContDiff ℝ ∞ sigma) (x : Fin d → ℝ) (i j : Fin d) :
    (M.conformalRescale sigma hsigma).inverseMetric x i j =
      Real.exp (-2 * sigma x) * M.inverseMetric x i j := by
  simp [conformalRescale, Matrix.smul_apply]

@[simp] theorem conformalRescale_density (sigma : (Fin d → ℝ) → ℝ)
    (hsigma : ContDiff ℝ ∞ sigma) (x : Fin d → ℝ) :
    (M.conformalRescale sigma hsigma).density x =
      Real.exp ((d : ℝ) * sigma x) * M.density x := rfl

/-- The conformally rescaled flux is the original flux weighted by `e^{(d-2)σ}`. -/
theorem flux_conformalRescale (sigma : (Fin d → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma)
    (f : (Fin d → ℝ) → ℝ) (i : Fin d) :
    (M.conformalRescale sigma hsigma).flux f i =
      fun x => Real.exp (((d : ℝ) - 2) * sigma x) * M.flux f i x := by
  funext x
  have hsum : ∑ j, (M.conformalRescale sigma hsigma).inverseMetric x i j * coordPartial j f x =
      Real.exp (-2 * sigma x) * ∑ j, M.inverseMetric x i j * coordPartial j f x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [M.conformalRescale_inverseMetric sigma hsigma x i j]
    ring
  have hexp : Real.exp ((d : ℝ) * sigma x) * Real.exp (-2 * sigma x) =
      Real.exp (((d : ℝ) - 2) * sigma x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [flux, conformalRescale_density]
  rw [hsum, ← hexp]
  ring

/-- **Exact conformal transformation law of the scalar d'Alembertian.**

For the chart of `e^{2σ} g`, `□̃ f = e^{-2σ} (□ f + (d-2) Γ(σ,f))`. -/
theorem dalembert_conformalRescale (sigma : (Fin d → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (x : Fin d → ℝ) :
    (M.conformalRescale sigma hsigma).dalembert f x =
      Real.exp (-2 * sigma x) *
        (M.dalembert f x + ((d : ℝ) - 2) * M.gradPair sigma f x) := by
  have hweight : ContDiff ℝ ∞ fun y => Real.exp (((d : ℝ) - 2) * sigma y) :=
    Real.contDiff_exp.comp (contDiff_const.mul hsigma)
  have hderiv : ∀ i : Fin d,
      coordPartial i ((M.conformalRescale sigma hsigma).flux f i) x =
        Real.exp (((d : ℝ) - 2) * sigma x) *
          (((d : ℝ) - 2) * coordPartial i sigma x * M.flux f i x +
            coordPartial i (M.flux f i) x) := by
    intro i
    rw [M.flux_conformalRescale sigma hsigma f i]
    rw [coordPartial_mul (differentiableAt_of_contDiff_infty hweight x)
      (differentiableAt_of_contDiff_infty (M.contDiff_flux hf i) x) i]
    rw [coordPartial_exp
        (differentiableAt_of_contDiff_infty (contDiff_const.mul hsigma) x) i,
      coordPartial_const_mul (differentiableAt_of_contDiff_infty hsigma x) _ i]
    ring
  have hsum :
      ∑ i, coordPartial i ((M.conformalRescale sigma hsigma).flux f i) x =
        Real.exp (((d : ℝ) - 2) * sigma x) *
          (((d : ℝ) - 2) * ∑ i, coordPartial i sigma x * M.flux f i x +
            ∑ i, coordPartial i (M.flux f i) x) := by
    have h1 : ∑ i, coordPartial i ((M.conformalRescale sigma hsigma).flux f i) x =
        ∑ i, (Real.exp (((d : ℝ) - 2) * sigma x) *
              (((d : ℝ) - 2) * (coordPartial i sigma x * M.flux f i x)) +
            Real.exp (((d : ℝ) - 2) * sigma x) * coordPartial i (M.flux f i) x) :=
      Finset.sum_congr rfl fun i _ => by rw [hderiv i]; ring
    rw [h1, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
  have hinv : (Real.exp ((d : ℝ) * sigma x))⁻¹ * Real.exp (((d : ℝ) - 2) * sigma x) =
      Real.exp (-2 * sigma x) := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have hdensity : ((M.conformalRescale sigma hsigma).density x)⁻¹ =
      (Real.exp ((d : ℝ) * sigma x))⁻¹ * (M.density x)⁻¹ := by
    rw [conformalRescale_density, mul_inv]
  calc
    (M.conformalRescale sigma hsigma).dalembert f x
        = ((M.conformalRescale sigma hsigma).density x)⁻¹ *
            ∑ i, coordPartial i ((M.conformalRescale sigma hsigma).flux f i) x := rfl
    _ = ((Real.exp ((d : ℝ) * sigma x))⁻¹ * Real.exp (((d : ℝ) - 2) * sigma x)) *
          ((M.density x)⁻¹ *
            (((d : ℝ) - 2) * ∑ i, coordPartial i sigma x * M.flux f i x +
              ∑ i, coordPartial i (M.flux f i) x)) := by
          rw [hdensity, hsum]; ring
    _ = Real.exp (-2 * sigma x) *
          (((d : ℝ) - 2) *
              ((M.density x)⁻¹ * ∑ i, coordPartial i sigma x * M.flux f i x) +
            (M.density x)⁻¹ * ∑ i, coordPartial i (M.flux f i) x) := by
          rw [hinv]; ring
    _ = Real.exp (-2 * sigma x) *
          (M.dalembert f x + ((d : ℝ) - 2) * M.gradPair sigma f x) := by
          rw [M.inv_density_mul_sum_flux sigma f x]
          simp only [dalembert]
          ring

end SmoothMetricChart

/-- A smooth nondegenerate symmetric metric field in a coordinate chart. -/
structure SmoothPseudoMetric (d : ℕ) where
  /-- Covariant metric coefficients `g_{ij}`. -/
  metric : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ
  contDiff_metric : ∀ i j, ContDiff ℝ ∞ fun x => metric x i j
  metric_symm : ∀ x, (metric x).IsSymm
  det_ne_zero : ∀ x, (metric x).det ≠ 0

namespace SmoothPseudoMetric

variable {d : ℕ} (g : SmoothPseudoMetric d)

theorem isUnit_det (x : Fin d → ℝ) : IsUnit (g.metric x).det :=
  isUnit_iff_ne_zero.mpr (g.det_ne_zero x)

/-- The chart `(g⁻¹, √|det g|)` of a smooth nondegenerate metric field. -/
noncomputable def chart : SmoothMetricChart d where
  inverseMetric := fun x => (g.metric x)⁻¹
  density := fun x => Real.sqrt |(g.metric x).det|
  contDiff_inverseMetric := fun i j =>
    contDiff_matrix_inv_apply g.contDiff_metric g.det_ne_zero i j
  contDiff_density :=
    contDiff_sqrt_abs (contDiff_matrix_det g.contDiff_metric) g.det_ne_zero
  density_pos := fun x => Real.sqrt_pos.mpr (abs_pos.mpr (g.det_ne_zero x))
  inverseMetric_symm := by
    intro x i j
    have h : ((g.metric x)⁻¹).transpose = (g.metric x)⁻¹ :=
      Matrix.IsSymm.inv (g.metric_symm x)
    calc (g.metric x)⁻¹ i j = ((g.metric x)⁻¹).transpose j i := rfl
      _ = (g.metric x)⁻¹ j i := by rw [h]

@[simp] theorem chart_inverseMetric (x : Fin d → ℝ) :
    g.chart.inverseMetric x = (g.metric x)⁻¹ := rfl

@[simp] theorem chart_density (x : Fin d → ℝ) :
    g.chart.density x = Real.sqrt |(g.metric x).det| := rfl

/-- Literal conformal rescaling `g ↦ e^{2σ} g` of a smooth metric field. -/
noncomputable def conformal (sigma : (Fin d → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma) :
    SmoothPseudoMetric d where
  metric := fun x => Real.exp (2 * sigma x) • g.metric x
  contDiff_metric := by
    intro i j
    have h : (fun x => (Real.exp (2 * sigma x) • g.metric x) i j) =
        fun x => Real.exp (2 * sigma x) * g.metric x i j := by
      funext x; simp [Matrix.smul_apply]
    rw [h]
    exact (Real.contDiff_exp.comp (contDiff_const.mul hsigma)).mul (g.contDiff_metric i j)
  metric_symm := by
    intro x
    have h : (g.metric x).transpose = g.metric x := g.metric_symm x
    show (Real.exp (2 * sigma x) • g.metric x).transpose =
      Real.exp (2 * sigma x) • g.metric x
    rw [Matrix.transpose_smul, h]
  det_ne_zero := by
    intro x
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Real.exp_ne_zero _)) (g.det_ne_zero x)

@[simp] theorem conformal_metric (sigma : (Fin d → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma)
    (x : Fin d → ℝ) :
    (g.conformal sigma hsigma).metric x = Real.exp (2 * sigma x) • g.metric x := rfl

/-- **The chart of a conformally rescaled metric is the conformally rescaled chart.**

`(e^{2σ}g)⁻¹ = e^{-2σ} g⁻¹` and `√|det (e^{2σ}g)| = e^{dσ} √|det g|`. -/
theorem chart_conformal (sigma : (Fin d → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma) :
    (g.conformal sigma hsigma).chart = g.chart.conformalRescale sigma hsigma := by
  have hinv : ∀ x : Fin d → ℝ,
      ((g.conformal sigma hsigma).metric x)⁻¹ =
        Real.exp (-2 * sigma x) • (g.metric x)⁻¹ := by
    intro x
    have hne : Real.exp (2 * sigma x) ≠ 0 := Real.exp_ne_zero _
    have hinvertible : Invertible (Real.exp (2 * sigma x)) := invertibleOfNonzero hne
    have hprod : Real.exp (2 * sigma x) * Real.exp (-2 * sigma x) = 1 := by
      rw [← Real.exp_add]
      have h : 2 * sigma x + -2 * sigma x = 0 := by ring
      rw [h, Real.exp_zero]
    have hinvOf : (⅟(Real.exp (2 * sigma x)) : ℝ) = Real.exp (-2 * sigma x) :=
      invOf_eq_right_inv hprod
    rw [conformal_metric, Matrix.inv_smul _ _ (g.isUnit_det x), hinvOf]
  have hdet : ∀ x : Fin d → ℝ,
      Real.sqrt |((g.conformal sigma hsigma).metric x).det| =
        Real.exp ((d : ℝ) * sigma x) * Real.sqrt |(g.metric x).det| := by
    intro x
    have hcard : (Fintype.card (Fin d)) = d := Fintype.card_fin d
    have hpow : (Real.exp (2 * sigma x)) ^ d = (Real.exp ((d : ℝ) * sigma x)) ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [conformal_metric, Matrix.det_smul, hcard, hpow, abs_mul,
      abs_of_nonneg (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt (Real.exp_pos _))]
  refine SmoothMetricChart.ext' ?_ ?_
  · funext x
    exact hinv x
  · funext x
    exact hdet x

/-- **Conformal transformation law for a literally rescaled smooth metric.**

The d'Alembertian of `e^{2σ} g` differs from that of `g` by the exact carré-du-champ shift. -/
theorem dalembert_conformal (sigma : (Fin d → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (x : Fin d → ℝ) :
    (g.conformal sigma hsigma).chart.dalembert f x =
      Real.exp (-2 * sigma x) *
        (g.chart.dalembert f x + ((d : ℝ) - 2) * g.chart.gradPair sigma f x) := by
  rw [g.chart_conformal sigma hsigma]
  exact g.chart.dalembert_conformalRescale sigma hsigma hf x

end SmoothPseudoMetric

end GaloisForLFunctions.HTGeometry
