import GaloisForLFunctions.HTGeometry.DistributionalLinearODE
import GaloisForLFunctions.HTGeometry.PointSupportGammaForm

/-!
# Scalar conjugation of a distributional transport equation

A distributional solution of `u' = A u + m u`, with `A` a bounded operator and `m` a scalar
multiplier, is conjugated to the constant-coefficient equation by any integrating factor `g` with
`g' = -m g` on the interval.  The conjugated distribution is therefore the propagator applied to a
single vector, and undoing the conjugation represents the original distribution as the locally
integrable function `g(t)^{-1} exp(t A) c`.
-/

open Set SchwartzMap MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Multiplication by a temperate multiplier preserves the carrier of a test function. -/
theorem mulTemperateCLM_eq_zero_of_notMem {g : ℝ → ℂ} (hg : Function.HasTemperateGrowth g)
    {φ : SchwartzMap ℝ ℂ} {a b : ℝ} (hsupp : ∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) :
    ∀ x, x ∉ Ioo a b → ((mulTemperateCLM hg φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = 0 := by
  intro x hx
  rw [mulTemperateCLM_apply, hsupp x hx, zero_mul]

/-- The Leibniz rule for a temperate multiplier, in the form used by the integrating factor. -/
theorem derivCLM_mulTemperateCLM {g m : ℝ → ℂ} (hg : Function.HasTemperateGrowth g)
    (hm : Function.HasTemperateGrowth m) {a b : ℝ}
    (hgd : ∀ x ∈ Ioo a b, deriv g x = -(m x * g x))
    {φ : SchwartzMap ℝ ℂ} (hsupp : ∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) :
    SchwartzMap.derivCLM ℂ ℂ (mulTemperateCLM hg φ)
      = mulTemperateCLM hg (SchwartzMap.derivCLM ℂ ℂ φ)
        - mulTemperateCLM hm (mulTemperateCLM hg φ) := by
  have hgc : ContDiff ℝ (⊤ : ℕ∞) g := hg.1
  refine SchwartzMap.ext fun x => ?_
  have hdφ : HasDerivAt (φ : ℝ → ℂ) (deriv (φ : ℝ → ℂ) x) x :=
    (φ.smooth'.differentiable (by simp) x).hasDerivAt
  have hdg : HasDerivAt g (deriv g x) x := (hgc.differentiable (by simp) x).hasDerivAt
  have hval : ((SchwartzMap.derivCLM ℂ ℂ (mulTemperateCLM hg φ) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      = deriv (φ : ℝ → ℂ) x * g x + (φ : ℝ → ℂ) x * deriv g x := by
    show deriv ((mulTemperateCLM hg φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = _
    have hfun : ((mulTemperateCLM hg φ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        = fun y : ℝ => (φ : ℝ → ℂ) y * g y := rfl
    rw [hfun]
    exact (hdφ.mul hdg).deriv
  have hrhs : ((mulTemperateCLM hg (SchwartzMap.derivCLM ℂ ℂ φ)
        - mulTemperateCLM hm (mulTemperateCLM hg φ) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      = deriv (φ : ℝ → ℂ) x * g x - (φ : ℝ → ℂ) x * g x * m x := rfl
  rw [hval, hrhs]
  by_cases hx : x ∈ Ioo a b
  · rw [hgd x hx]
    ring
  · rw [hsupp x hx]
    ring

/-- **A scalar-conjugated distributional transport equation has a propagator representation.** -/
theorem exists_conjugate_representation (A : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X) {a b : ℝ}
    (hab : a < b) {m g ginv : ℝ → ℂ}
    (hm : Function.HasTemperateGrowth m) (hg : Function.HasTemperateGrowth g)
    (hginv : Function.HasTemperateGrowth ginv)
    (hgd : ∀ x ∈ Ioo a b, deriv g x = -(m x * g x))
    (hgi : ∀ x ∈ Ioo a b, g x * ginv x = 1)
    (hEq : ∀ ψ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (ψ : ℝ → ℂ) x = 0) →
      u (SchwartzMap.derivCLM ℂ ℂ ψ) = -(A (u ψ)) - u (mulTemperateCLM hm ψ)) :
    ∃ c : X, ∀ φ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
      u φ = ∫ t in a..b, (ginv t * (φ : ℝ → ℂ) t) • (NormedSpace.exp ((t : ℂ) • A) c) := by
  set h : SchwartzMap ℝ ℂ →L[ℂ] X := u.comp (mulTemperateCLM hg) with hh
  have hhapply : ∀ φ : SchwartzMap ℝ ℂ, h φ = u (mulTemperateCLM hg φ) := fun _ => rfl
  have hode : ∀ φ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
      h (SchwartzMap.derivCLM ℂ ℂ φ) = -(A (h φ)) := by
    intro φ hφ
    have hsuppg := mulTemperateCLM_eq_zero_of_notMem hg hφ
    have hleib := derivCLM_mulTemperateCLM hg hm hgd hφ
    have hEqg := hEq (mulTemperateCLM hg φ) hsuppg
    rw [hleib, map_sub] at hEqg
    have : u (mulTemperateCLM hg (SchwartzMap.derivCLM ℂ ℂ φ))
        = -(A (u (mulTemperateCLM hg φ))) := by
      have hcancel := hEqg
      rw [sub_eq_iff_eq_add] at hcancel
      rw [hcancel]
      abel
    rw [hhapply, hhapply, this]
  obtain ⟨c, hc⟩ := exists_exp_representation A h hab hode
  refine ⟨c, fun φ hsupp => ?_⟩
  have hsuppinv := mulTemperateCLM_eq_zero_of_notMem hginv hsupp
  have hback : mulTemperateCLM hg (mulTemperateCLM hginv φ) = φ := by
    refine SchwartzMap.ext fun x => ?_
    rw [mulTemperateCLM_apply, mulTemperateCLM_apply]
    by_cases hx : x ∈ Ioo a b
    · have := hgi x hx
      calc (φ : ℝ → ℂ) x * ginv x * g x = (φ : ℝ → ℂ) x * (g x * ginv x) := by ring
        _ = (φ : ℝ → ℂ) x := by rw [this, mul_one]
    · rw [hsupp x hx, zero_mul, zero_mul]
  have huφ : u φ = h (mulTemperateCLM hginv φ) := by
    rw [hhapply, hback]
  rw [huφ, hc (mulTemperateCLM hginv φ) hsuppinv]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [mulTemperateCLM_apply]
  congr 1
  ring

end

end GaloisForLFunctions.HTGeometry
