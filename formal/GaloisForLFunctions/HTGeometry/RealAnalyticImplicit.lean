import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-!
# The real-analytic scalar implicit function theorem

The corpus's implicit-function engine is holomorphic.  A matching problem posed in a real parameter
— a scalar shift selected by a real anchor — needs the same statement over `ℝ`, and the proof is
the same: analytic smoothness is `ContDiffAt ℝ ω`, and a scalar continuous linear map is invertible
as soon as its value at one is nonzero.

The consequence used downstream is a *matching branch*: if two real-analytic families agree at a
base point and the first is transverse in its second variable there, the equation between them has
a unique real-analytic solution branch through that point.  Transversality at one point therefore
propagates the match to a whole interval, rather than requiring a fresh selection at each
parameter.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology ContinuousLinearMap
open scoped ContDiff

/-- A scalar continuous linear map is invertible once its value at one is nonzero. -/
theorem clm_invertible_of_apply_one_ne_real {g : ℝ →L[ℝ] ℝ} (hg : g 1 ≠ 0) : g.IsInvertible := by
  rw [show g = smulRight (1 : ℝ →L[ℝ] ℝ) (g 1) from by ext; simp]
  exact ⟨(Units.mk0 (g 1) hg) • ContinuousLinearEquiv.refl ℝ ℝ, by ext; simp⟩

/-- **The real-analytic implicit function theorem**, scalar parameter and scalar root. -/
theorem real_analytic_implicit {f : ℝ × ℝ → ℝ} {t₀ w₀ : ℝ}
    (hf : AnalyticAt ℝ f (t₀, w₀)) (h0 : f (t₀, w₀) = 0)
    (hfw : (fderiv ℝ f (t₀, w₀)) (0, 1) ≠ 0) :
    ∃ r : ℝ → ℝ, AnalyticAt ℝ r t₀ ∧ r t₀ = w₀ ∧ (∀ᶠ t in 𝓝 t₀, f (t, r t) = 0) := by
  have cdf : ContDiffAt ℝ ω f (t₀, w₀) := hf.contDiffAt
  have if₂ : (fderiv ℝ f (t₀, w₀) ∘L (.inr ℝ ℝ ℝ)).IsInvertible :=
    clm_invertible_of_apply_one_ne_real (by simpa using hfw)
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by decide
  refine ⟨cdf.implicitFunction hω if₂,
    (cdf.contDiffAt_implicitFunction hω if₂).analyticAt, ?_, ?_⟩
  · exact cdf.implicitFunction_apply_self hω if₂
  · filter_upwards [cdf.eventually_apply_implicitFunction hω if₂] with t ht
    rw [ht, h0]

/-- **The matching branch.**  Two real-analytic families that agree at a base point, the first
transverse in its second variable there, are matched along a unique real-analytic branch. -/
theorem exists_matching_branch_of_transverse {Φ : ℝ × ℝ → ℝ} {Ψ : ℝ → ℝ} {t₀ lam : ℝ}
    (hΦ : AnalyticAt ℝ Φ (t₀, lam)) (hΨ : AnalyticAt ℝ Ψ t₀)
    (hmatch : Φ (t₀, lam) = Ψ t₀)
    (htrans : (fderiv ℝ Φ (t₀, lam)) (0, 1) ≠ 0) :
    ∃ r : ℝ → ℝ, AnalyticAt ℝ r t₀ ∧ r t₀ = lam ∧
      (∀ᶠ t in 𝓝 t₀, Φ (t, r t) = Ψ t) := by
  have hfst : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1) (t₀, lam) := analyticAt_fst
  have hcomp : AnalyticAt ℝ (fun p : ℝ × ℝ => Ψ p.1) (t₀, lam) := hΨ.comp hfst
  have hf : AnalyticAt ℝ (fun p : ℝ × ℝ => Φ p - Ψ p.1) (t₀, lam) := hΦ.sub hcomp
  have hzero : (fun p : ℝ × ℝ => Φ p - Ψ p.1) (t₀, lam) = 0 := by
    simp [hmatch]
  have hderiv : (fderiv ℝ (fun p : ℝ × ℝ => Φ p - Ψ p.1) (t₀, lam)) (0, 1)
      = (fderiv ℝ Φ (t₀, lam)) (0, 1) := by
    have hd1 : DifferentiableAt ℝ Φ (t₀, lam) := hΦ.differentiableAt
    have hd2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => Ψ p.1) (t₀, lam) := hcomp.differentiableAt
    rw [fderiv_fun_sub hd1 hd2]
    have hchain : (fderiv ℝ (fun p : ℝ × ℝ => Ψ p.1) (t₀, lam)) (0, 1) = 0 := by
      have hΨd : DifferentiableAt ℝ Ψ t₀ := hΨ.differentiableAt
      rw [show (fun p : ℝ × ℝ => Ψ p.1) = Ψ ∘ (fun p : ℝ × ℝ => p.1) from rfl,
        fderiv_comp _ hΨd (differentiableAt_fst)]
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
      rw [show (fun p : ℝ × ℝ => p.1) = (Prod.fst : ℝ × ℝ → ℝ) from rfl, fderiv_fst]
      simp
    simp [hchain]
  obtain ⟨r, hr1, hr2, hr3⟩ := real_analytic_implicit hf hzero (by rw [hderiv]; exact htrans)
  refine ⟨r, hr1, hr2, ?_⟩
  filter_upwards [hr3] with t ht
  exact sub_eq_zero.mp ht

end GaloisForLFunctions.HTGeometry
