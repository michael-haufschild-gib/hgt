import GaloisForLFunctions.SchwartzTranslation
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Continuous sesquilinear forms on complex Schwartz space

Mathlib has algebraic sesquilinear maps but does not currently package jointly continuous
sesquilinear forms on a locally convex space.  This file supplies the exact object needed by the
Hedenmalm theta-pair metric classification.  The strong translation-orbit derivative from
`SchwartzTranslation` then proves, without an analytic hypothesis, that symmetry of the momentum
generator forces simultaneous-translation invariance.
-/

open Complex Function Filter
open scoped Topology

namespace SchwartzMap

noncomputable section

/-- A jointly continuous form on complex Schwartz space, complex-linear in the first argument and
conjugate-linear in the second. -/
structure ContinuousSchwartzSesquilinearForm where
  toFun : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ) → ℂ
  map_add_left : ∀ u v w, toFun (u + v) w = toFun u w + toFun v w
  map_smul_left : ∀ (c : ℂ) u v, toFun (c • u) v = c * toFun u v
  map_add_right : ∀ u v w, toFun u (v + w) = toFun u v + toFun u w
  map_smul_right : ∀ (c : ℂ) u v,
    toFun u (c • v) = (starRingEnd ℂ) c * toFun u v
  continuous : Continuous (fun p : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ) => toFun p.1 p.2)

instance : CoeFun ContinuousSchwartzSesquilinearForm
    (fun _ => 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ) → ℂ) :=
  ⟨ContinuousSchwartzSesquilinearForm.toFun⟩

namespace ContinuousSchwartzSesquilinearForm

variable (Q : ContinuousSchwartzSesquilinearForm)

@[simp] theorem apply_add_left (u v w : 𝓢(ℝ, ℂ)) :
    Q (u + v) w = Q u w + Q v w := Q.map_add_left u v w

@[simp] theorem apply_smul_left (c : ℂ) (u v : 𝓢(ℝ, ℂ)) :
    Q (c • u) v = c * Q u v := Q.map_smul_left c u v

@[simp] theorem apply_add_right (u v w : 𝓢(ℝ, ℂ)) :
    Q u (v + w) = Q u v + Q u w := Q.map_add_right u v w

@[simp] theorem apply_smul_right (c : ℂ) (u v : 𝓢(ℝ, ℂ)) :
    Q u (c • v) = (starRingEnd ℂ) c * Q u v := Q.map_smul_right c u v

@[simp] theorem apply_neg_left (u v : 𝓢(ℝ, ℂ)) : Q (-u) v = -Q u v := by
  simpa using Q.apply_smul_left (-1) u v

@[simp] theorem apply_neg_right (u v : 𝓢(ℝ, ℂ)) : Q u (-v) = -Q u v := by
  simpa using Q.apply_smul_right (-1) u v

@[simp] theorem apply_sub_left (u v w : 𝓢(ℝ, ℂ)) :
    Q (u - v) w = Q u w - Q v w := by
  rw [sub_eq_add_neg, Q.apply_add_left, Q.apply_neg_left, sub_eq_add_neg]

@[simp] theorem apply_sub_right (u v w : 𝓢(ℝ, ℂ)) :
    Q u (v - w) = Q u v - Q u w := by
  rw [sub_eq_add_neg, Q.apply_add_right, Q.apply_neg_right, sub_eq_add_neg]

@[simp] theorem apply_real_smul_left (r : ℝ) (u v : 𝓢(ℝ, ℂ)) :
    Q (r • u) v = r • Q u v := by
  change Q ((r : ℂ) • u) v = (r : ℂ) * Q u v
  rw [Q.apply_smul_left]

@[simp] theorem apply_real_smul_right (r : ℝ) (u v : 𝓢(ℝ, ℂ)) :
    Q u (r • v) = r • Q u v := by
  change Q u ((r : ℂ) • v) = (r : ℂ) * Q u v
  rw [Q.apply_smul_right, Complex.conj_ofReal]

/-- Joint continuity transports simultaneous convergence in the two arguments. -/
theorem tendsto_apply {α : Type*} {l : Filter α}
    {u v : α → 𝓢(ℝ, ℂ)} {u₀ v₀ : 𝓢(ℝ, ℂ)}
    (hu : Tendsto u l (𝓝 u₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun x => Q (u x) (v x)) l (𝓝 (Q u₀ v₀)) := by
  exact (Q.continuous.tendsto (u₀, v₀)).comp (hu.prodMk_nhds hv)

/-- Positivity of a complex sesquilinear form: every diagonal value is real and nonnegative. -/
def IsNonnegative : Prop :=
  ∀ u : 𝓢(ℝ, ℂ), 0 ≤ (Q u u).re ∧ (Q u u).im = 0

/-- Hermitian symmetry, in the convention that the first argument is complex-linear. -/
def IsHermitian : Prop :=
  ∀ u v : 𝓢(ℝ, ℂ), Q v u = (starRingEnd ℂ) (Q u v)

/-- A nonnegative sesquilinear form is automatically Hermitian. -/
theorem isHermitian_of_isNonnegative (hQ : Q.IsNonnegative) : Q.IsHermitian := by
  intro u v
  have huu := (hQ u).2
  have hvv := (hQ v).2
  have hplus := (hQ (u + v)).2
  have hI := (hQ (u + I • v)).2
  simp only [Q.apply_add_left, Q.apply_add_right, Q.apply_smul_left,
    Q.apply_smul_right] at hplus hI
  simp only [Complex.add_im] at hplus
  rw [huu, hvv] at hplus
  have him : (Q v u).im = -(Q u v).im := by linarith
  norm_num [Complex.add_im, Complex.mul_im, huu, hvv] at hI
  have hre : (Q v u).re = (Q u v).re := by linarith
  apply Complex.ext
  · simpa using hre
  · simpa using him

/-- Derivative of the simultaneous-translation orbit of a continuous sesquilinear form. -/
theorem hasDerivAt_translate_pair (u v : 𝓢(ℝ, ℂ)) (a : ℝ) :
    HasDerivAt (fun t : ℝ => Q (translateCLM ℂ t u) (translateCLM ℂ t v))
      (Q (translateCLM ℂ a (derivCLM ℂ ℂ u)) (translateCLM ℂ a v) +
        Q (translateCLM ℂ a u) (translateCLM ℂ a (derivCLM ℂ ℂ v))) a := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hDQu := tendsto_translateDifferenceQuotient u a
  have hDQv := tendsto_translateDifferenceQuotient v a
  have hVv : Tendsto (fun h : ℝ => translateCLM ℂ (a + h) v)
      (𝓝[≠] 0) (𝓝 (translateCLM ℂ a v)) :=
    (tendsto_translateCLM_add_zero v a).mono_left
      (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hterm₁ := Q.tendsto_apply hDQu hVv
  have hconstu : Tendsto (fun _h : ℝ => translateCLM ℂ a u)
      (𝓝[≠] 0) (𝓝 (translateCLM ℂ a u)) := tendsto_const_nhds
  have hterm₂ := Q.tendsto_apply hconstu hDQv
  have hsum := hterm₁.add hterm₂
  apply Tendsto.congr' _ hsum
  filter_upwards with h
  symm
  change (h⁻¹ : ℝ) •
      (Q (translateCLM ℂ (a + h) u) (translateCLM ℂ (a + h) v) -
        Q (translateCLM ℂ a u) (translateCLM ℂ a v)) = _
  rw [translateDifferenceQuotient, translateDifferenceQuotient,
    Q.apply_real_smul_left, Q.apply_real_smul_right,
    Q.apply_sub_left, Q.apply_sub_right]
  module

/-- Skewness of the ordinary derivative, the real-generator form of momentum symmetry. -/
def DerivativeSkew : Prop :=
  ∀ u v : 𝓢(ℝ, ℂ),
    Q (derivCLM ℂ ℂ u) v + Q u (derivCLM ℂ ℂ v) = 0

/-- Symmetry of `D = -i d/dx`, in the convention linear in the first argument. -/
def MomentumSymmetric : Prop :=
  ∀ u v : 𝓢(ℝ, ℂ),
    Q ((-I) • derivCLM ℂ ℂ u) v = Q u ((-I) • derivCLM ℂ ℂ v)

theorem momentumSymmetric_iff_derivativeSkew :
    Q.MomentumSymmetric ↔ Q.DerivativeSkew := by
  constructor
  · intro h u v
    have huv := h u v
    rw [Q.apply_smul_left, Q.apply_smul_right] at huv
    have hmul : (-I) * (Q (derivCLM ℂ ℂ u) v + Q u (derivCLM ℂ ℂ v)) = 0 := by
      calc
        (-I) * (Q (derivCLM ℂ ℂ u) v + Q u (derivCLM ℂ ℂ v)) =
            (-I) * Q (derivCLM ℂ ℂ u) v - I * Q u (derivCLM ℂ ℂ v) := by ring
        _ = 0 := sub_eq_zero.mpr (by simpa using huv)
    exact (mul_eq_zero.mp hmul).resolve_left (neg_ne_zero.mpr I_ne_zero)
  · intro h u v
    have huv := h u v
    rw [Q.apply_smul_left, Q.apply_smul_right]
    have hneg : Q (derivCLM ℂ ℂ u) v = -Q u (derivCLM ℂ ℂ v) :=
      eq_neg_of_add_eq_zero_left huv
    rw [hneg]
    simp

/-- Momentum symmetry forces invariance under simultaneous translation. -/
theorem translate_pair_invariant (hQ : Q.MomentumSymmetric)
    (u v : 𝓢(ℝ, ℂ)) (a : ℝ) :
    Q (translateCLM ℂ a u) (translateCLM ℂ a v) = Q u v := by
  have hskew : Q.DerivativeSkew := Q.momentumSymmetric_iff_derivativeSkew.mp hQ
  let H : ℝ → ℂ := fun t => Q (translateCLM ℂ t u) (translateCLM ℂ t v)
  have hderiv (t : ℝ) : HasDerivAt H 0 t := by
    have ht := Q.hasDerivAt_translate_pair u v t
    have hs := hskew (translateCLM ℂ t u) (translateCLM ℂ t v)
    rw [derivCLM_translateCLM, derivCLM_translateCLM] at hs
    simpa only [H, hs] using ht
  have hdiff : Differentiable ℝ H := fun t => (hderiv t).differentiableAt
  have hconst : Differentiable ℝ (fun _t : ℝ => H 0) := differentiable_const _
  have hfderiv : ∀ t : ℝ,
      fderiv ℝ H t = fderiv ℝ (fun _s : ℝ => H 0) t := by
    intro t
    have ht := (hderiv t).hasFDerivAt.fderiv
    simpa using ht
  have heq : H = fun _t : ℝ => H 0 :=
    eq_of_fderiv_eq hdiff hconst hfderiv 0 rfl
  have ha := congrFun heq a
  simpa [H] using ha

end ContinuousSchwartzSesquilinearForm

end

end SchwartzMap
