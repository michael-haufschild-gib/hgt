import GaloisForLFunctions.HilbertMetric.Geometry.BonnetSupport
import GaloisForLFunctions.Bottcher.ChordalMetric

/-!
# The stereographic normal and its moving tangent frame

The existing sphere embedding supplies the normal. Its actual first and
second derivatives give the conformal tangent frame and connection terms
needed for the support-function parametrization.
-/

open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.StereographicFrame
open BonnetSupport Bottcher
noncomputable section
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The existing stereographic sphere embedding, in real plane coordinates. -/
def normal (p : ℝ × ℝ) : Space := Bottcher.stereo ⟨p.1, p.2⟩

theorem normal_formula (p : ℝ × ℝ) : normal p =
    !₂[2 * p.1 / denominator p, 2 * p.2 / denominator p,
      (p.1 ^ 2 + p.2 ^ 2 - 1) / denominator p] := by
  have hn : ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  ext i
  fin_cases i <;> simp [normal, Bottcher.stereo, hn, denominator, add_assoc]

/-- The first stereographic tangent vector. -/
def tangentX (p : ℝ × ℝ) : Space :=
  !₂[2 * (1 - p.1 ^ 2 + p.2 ^ 2) / denominator p ^ 2,
    -4 * p.1 * p.2 / denominator p ^ 2, 4 * p.1 / denominator p ^ 2]

/-- The second stereographic tangent vector. -/
def tangentY (p : ℝ × ℝ) : Space :=
  !₂[-4 * p.1 * p.2 / denominator p ^ 2,
    2 * (1 + p.1 ^ 2 - p.2 ^ 2) / denominator p ^ 2, 4 * p.2 / denominator p ^ 2]

private theorem contDiff_three {f₀ f₁ f₂ : ℝ × ℝ → ℝ}
    (h₀ : ContDiff ℝ ∞ f₀) (h₁ : ContDiff ℝ ∞ f₁) (h₂ : ContDiff ℝ ∞ f₂) :
    ContDiff ℝ ∞ (fun p => (!₂[f₀ p, f₁ p, f₂ p] : Space)) := by
  have h : ContDiff ℝ ∞ (fun p => (![f₀ p, f₁ p, f₂ p] : Fin 3 → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contDiff.comp h

private theorem denominator_smooth : ContDiff ℝ ∞ denominator := by
  unfold denominator
  fun_prop

private theorem denominator_sq_ne (p : ℝ × ℝ) : denominator p ^ 2 ≠ 0 :=
  pow_ne_zero 2 (denominator_pos p).ne'

theorem normal_smooth : ContDiff ℝ ∞ normal := by
  rw [show normal = (fun p => !₂[2 * p.1 / denominator p, 2 * p.2 / denominator p,
    (p.1 ^ 2 + p.2 ^ 2 - 1) / denominator p]) from funext normal_formula]
  apply contDiff_three <;>
    exact ContDiff.div (by fun_prop) denominator_smooth (fun p => (denominator_pos p).ne')

theorem tangentX_smooth : ContDiff ℝ ∞ tangentX := by
  unfold tangentX
  apply contDiff_three <;>
    exact ContDiff.div (by fun_prop) (denominator_smooth.pow 2) denominator_sq_ne

theorem tangentY_smooth : ContDiff ℝ ∞ tangentY := by
  unfold tangentY
  apply contDiff_three <;>
    exact ContDiff.div (by fun_prop) (denominator_smooth.pow 2) denominator_sq_ne

theorem denominator_path {u v : ℝ → ℝ} {u' v' t : ℝ}
    (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => denominator (u s, v s)) (2 * u t * u' + 2 * v t * v') t := by
  have h := ((hu.pow 2).const_add 1).add (hv.pow 2)
  change HasDerivAt (fun s => denominator (u s, v s))
    (2 * u t ^ 1 * u' + 2 * v t ^ 1 * v') t at h
  simpa only [pow_one] using h

/-- Actual differential of the sphere embedding along any differentiable plane curve. -/
theorem normal_path {u v : ℝ → ℝ} {u' v' t : ℝ}
    (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => normal (u s, v s))
      (u' • tangentX (u t, v t) + v' • tangentY (u t, v t)) t := by
  have hd := denominator_path hu hv
  have hn := (denominator_pos (u t, v t)).ne'
  have h0 := (hu.const_mul 2).div hd hn
  have h1 := (hv.const_mul 2).div hd hn
  have h2 := (((hu.pow 2).add (hv.pow 2)).sub_const 1).div hd hn
  have h := hasDerivAt_euclidean3 h0 h1 h2
  rw [show (fun s => normal (u s, v s)) =
    (fun s => !₂[2 * u s / denominator (u s, v s),
      2 * v s / denominator (u s, v s),
      (u s ^ 2 + v s ^ 2 - 1) / denominator (u s, v s)]) from
      funext (fun s => normal_formula (u s, v s))]
  apply h.congr_deriv
  ext i
  fin_cases i <;>
    simp [tangentX, tangentY, PiLp.add_apply, PiLp.smul_apply] <;>
    field_simp [hn] <;> unfold denominator <;> ring

theorem normal_partials (p : ℝ × ℝ) :
    deriv (fun t => normal (t, p.2)) p.1 = tangentX p ∧
    deriv (fun t => normal (p.1, t)) p.2 = tangentY p := by
  constructor
  · simpa only [one_smul, zero_smul, add_zero, id_eq, Prod.mk.eta] using
      (normal_path (hasDerivAt_id p.1) (hasDerivAt_const p.1 p.2)).deriv
  · simpa only [one_smul, zero_smul, zero_add, id_eq, Prod.mk.eta] using
      (normal_path (hasDerivAt_const p.2 p.1) (hasDerivAt_id p.2)).deriv

/-- Actual derivative of the first tangent vector; coefficients are the round connection. -/
theorem tangentX_path {u v : ℝ → ℝ} {u' v' t : ℝ}
    (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => tangentX (u s, v s))
      ((-4 * u' / denominator (u t, v t) ^ 2) • normal (u t, v t) +
        (-2 * (u t * u' + v t * v') / denominator (u t, v t)) • tangentX (u t, v t) +
        (2 * (v t * u' - u t * v') / denominator (u t, v t)) • tangentY (u t, v t)) t := by
  have hd := (denominator_path hu hv).pow 2
  have hn := pow_ne_zero 2 (denominator_pos (u t, v t)).ne'
  have h0 := (((hu.pow 2).const_sub 1).add (hv.pow 2)).const_mul 2
  have h1 := (hu.const_mul (-4)).mul hv
  have h2 := hu.const_mul 4
  have h := hasDerivAt_euclidean3 (h0.div hd hn) (h1.div hd hn) (h2.div hd hn)
  apply h.congr_deriv
  ext i
  fin_cases i <;>
    simp [normal_formula, tangentX, tangentY, PiLp.add_apply, PiLp.smul_apply] <;>
    field_simp [(denominator_pos (u t, v t)).ne'] <;> unfold denominator <;> ring

/-- Actual derivative of the second tangent vector, including mixed partials. -/
theorem tangentY_path {u v : ℝ → ℝ} {u' v' t : ℝ}
    (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => tangentY (u s, v s))
      ((-4 * v' / denominator (u t, v t) ^ 2) • normal (u t, v t) +
        (2 * (u t * v' - v t * u') / denominator (u t, v t)) • tangentX (u t, v t) +
        (-2 * (u t * u' + v t * v') / denominator (u t, v t)) • tangentY (u t, v t)) t := by
  have hd := (denominator_path hu hv).pow 2
  have hn := pow_ne_zero 2 (denominator_pos (u t, v t)).ne'
  have h0 := (hu.const_mul (-4)).mul hv
  have h1 := (((hu.pow 2).const_add 1).sub (hv.pow 2)).const_mul 2
  have h2 := hv.const_mul 4
  have h := hasDerivAt_euclidean3 (h0.div hd hn) (h1.div hd hn) (h2.div hd hn)
  apply h.congr_deriv
  ext i
  fin_cases i <;>
    simp [normal_formula, tangentX, tangentY, PiLp.add_apply, PiLp.smul_apply] <;>
    field_simp [(denominator_pos (u t, v t)).ne'] <;> unfold denominator <;> ring

private theorem inner_three (a b c d e f : ℝ) :
    inner ℝ (!₂[a,b,c] : Space) (!₂[d,e,f] : Space) = a*d + b*e + c*f := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

/-- The tangent frame is orthogonal, with the exact round conformal factor. -/
theorem tangent_metric (p : ℝ × ℝ) :
    inner ℝ (tangentX p) (tangentX p) = (2 / denominator p) ^ 2 ∧
    inner ℝ (tangentY p) (tangentY p) = (2 / denominator p) ^ 2 ∧
    inner ℝ (tangentX p) (tangentY p) = 0 := by
  simpa only [tangentX, tangentY, inner_three, ← pow_two, denominator] using
    stereo_conformal_identities p.1 p.2

/-- The normal has unit length and is perpendicular to both tangent vectors. -/
theorem normal_metric (p : ℝ × ℝ) :
    inner ℝ (normal p) (normal p) = 1 ∧
    inner ℝ (normal p) (tangentX p) = 0 ∧ inner ℝ (normal p) (tangentY p) = 0 := by
  rw [normal_formula]
  simp only [tangentX, tangentY, inner_three]
  have hn := (denominator_pos p).ne'
  constructor
  · field_simp [hn]
    unfold denominator
    ring
  constructor <;> field_simp [hn] <;> unfold denominator <;> ring

#print axioms normal_path
#print axioms tangentX_path
#print axioms tangentY_path
#print axioms tangent_metric
#print axioms normal_metric
end
end GaloisForLFunctions.HilbertMetric.Geometry.StereographicFrame
