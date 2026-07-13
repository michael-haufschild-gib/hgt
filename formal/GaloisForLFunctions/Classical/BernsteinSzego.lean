import Mathlib
import GaloisForLFunctions.Classical.CircleMoments

/-!
# The Bernstein–Szegő orthogonality relations

Let `h : ℂ → ℂ` be analytic on the open unit disk, continuous on the closed disk, and
**nonvanishing on the closed disk**.  Consider the measure `dμ = |h(e^{iθ})|⁻² dθ` on the unit
circle.  The **Bernstein–Szegő** theorem describes the orthogonal polynomials for `dμ`
explicitly: for a polynomial `h` of degree `n`, the monic orthogonal polynomial of degree
`m ≥ n` is `z^{m-n} h*(z) / \overline{h(0)}`, where `h*(z) = z^n \overline{h(1/\bar z)}` is the
reversed polynomial.

On the unit circle the reversed-polynomial factor collapses:
`(z^{m-n} h*)(e^{iθ}) = e^{imθ} \overline{h(e^{iθ})}`.  This is the function `bsTest h m`.
Everything then reduces to the circle moments of the analytic function `1/h`
(`GaloisForLFunctions.Classical.CircleMoments`):

* `bernsteinSzego_orthogonality` — `⟨ψ_m, z^k⟩_μ = 0` for `k < m`  (orthogonality);
* `bernsteinSzego_top` — `⟨ψ_m, z^m⟩_μ = 2π / h(0)`  (leading Szegő coefficient);
* `bernsteinSzego_normSq` — `⟨ψ_m, ψ_m⟩_μ = 2π`  (exact Szegő norm).

The last is the Szegő asymptotics *made exact* for this dense class of weights: the norm of the
`m`-th orthogonal function is independent of `m`, so the reciprocal leading coefficients converge
to `(2π)^{1/2}` with no error term.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real
open ValueDistribution.CircleMoments

namespace ValueDistribution.BernsteinSzego

/-- On the unit circle, complex conjugation is inversion: `conj(e^{iθ}) = e^{-iθ}`. -/
lemma conj_circleMap_unit (θ : ℝ) :
    (starRingEnd ℂ) (circleMap 0 1 θ) = (circleMap 0 1 θ)⁻¹ := by
  have hns : Complex.normSq (circleMap 0 1 θ) = 1 := by
    have h1 : ‖circleMap 0 1 θ‖ = 1 := by simp [norm_circleMap_zero]
    rw [Complex.normSq_eq_norm_sq, h1]; norm_num
  rw [Complex.inv_def, hns]; simp

/-- The weighted circle inner product `⟨f₁, f₂⟩ = ∫₀^{2π} f₁ · conj(f₂) · |h|⁻²`. -/
noncomputable def bsInner (h f₁ f₂ : ℂ → ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    f₁ (circleMap 0 1 θ) * (starRingEnd ℂ) (f₂ (circleMap 0 1 θ))
      * (h (circleMap 0 1 θ) * (starRingEnd ℂ) (h (circleMap 0 1 θ)))⁻¹

/-- The Bernstein–Szegő test function `ψ_m(z) = z^m · conj(h z)`; on the unit circle these are
the boundary values of the degree-`m` polynomial `z^{m-n} h*(z)`. -/
noncomputable def bsTest (h : ℂ → ℂ) (m : ℤ) : ℂ → ℂ :=
  fun z => z ^ m * (starRingEnd ℂ) (h z)

/-- Pointwise reduction: the `⟨ψ_m, z^k⟩` integrand equals `z^{m-k} · (h z)⁻¹`. -/
lemma test_monomial_integrand (h : ℂ → ℂ) (z : ℂ) (m k : ℤ) (hzne : z ≠ 0) (hhne : h z ≠ 0)
    (hconj : (starRingEnd ℂ) z = z⁻¹) :
    z ^ m * (starRingEnd ℂ) (h z) * (starRingEnd ℂ) (z ^ k) * (h z * (starRingEnd ℂ) (h z))⁻¹
      = z ^ (m - k) * (h z)⁻¹ := by
  have hchne : (starRingEnd ℂ) (h z) ≠ 0 := by simpa using hhne
  rw [map_zpow₀, hconj, inv_zpow, zpow_sub₀ hzne, div_eq_mul_inv, mul_inv]
  field_simp

/-- If `h` is nonvanishing on the closed disk, `1/h` is analytic on the disk and continuous
up to the boundary. -/
lemma diffContOnCl_inv (h : ℂ → ℂ) (hh : DiffContOnCl ℂ h (Metric.ball 0 1))
    (hnz : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, h z ≠ 0) :
    DiffContOnCl ℂ (fun z => (h z)⁻¹) (Metric.ball 0 1) := by
  have hcl : closure (Metric.ball (0 : ℂ) 1) = Metric.closedBall 0 1 :=
    closure_ball 0 (by norm_num)
  refine ⟨hh.differentiableOn.inv (fun x hx => hnz x (Metric.ball_subset_closedBall hx)), ?_⟩
  rw [hcl]
  have hcont : ContinuousOn h (Metric.closedBall (0 : ℂ) 1) := by
    have := hh.continuousOn; rwa [hcl] at this
  exact hcont.inv₀ hnz

/-- Nonvanishing on the closed disk gives nonvanishing on the unit circle. -/
lemma circle_ne_zero_of_closedBall (h : ℂ → ℂ)
    (hnz : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, h z ≠ 0) (θ : ℝ) :
    h (circleMap 0 1 θ) ≠ 0 :=
  hnz _ (by simp [Metric.mem_closedBall, dist_eq_norm])

/-- The inner product of the test function with a monomial reduces to a circle moment of `1/h`. -/
lemma bsInner_bsTest_monomial (h : ℂ → ℂ) (m k : ℤ)
    (hhc : ∀ θ : ℝ, h (circleMap 0 1 θ) ≠ 0) :
    bsInner h (bsTest h m) (fun z => z ^ k) = circleMoment (fun z => (h z)⁻¹) (m - k) := by
  rw [bsInner, circleMoment]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [bsTest]
  exact test_monomial_integrand h (circleMap 0 1 θ) m k (circleMap_unit_ne_zero θ) (hhc θ)
    (conj_circleMap_unit θ)

/-- **Bernstein–Szegő orthogonality.**  For `h` analytic and nonvanishing on the closed unit
disk, the test function `ψ_m(z) = z^m · conj(h z)` (the boundary values of `z^{m-n}h*`) is
orthogonal in `L²(|h|⁻² dθ)` to every monomial `z^k` with `k < m`. -/
theorem bernsteinSzego_orthogonality (h : ℂ → ℂ) (hh : DiffContOnCl ℂ h (Metric.ball 0 1))
    (hnz : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, h z ≠ 0) (m k : ℕ) (hk : k < m) :
    bsInner h (bsTest h m) (fun z => z ^ (k : ℤ)) = 0 := by
  have hhc := circle_ne_zero_of_closedBall h hnz
  rw [bsInner_bsTest_monomial h m k hhc]
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (m : ℤ) - k = (p : ℤ) + 1 := ⟨m - k - 1, by omega⟩
  rw [hp]
  exact circleMoment_succ_eq_zero _ (diffContOnCl_inv h hh hnz) p

/-- **Bernstein–Szegő leading coefficient.**  The inner product of `ψ_m` with the top monomial
`z^m` equals `2π / h(0)`.  This pins the Szegő leading coefficient of the orthogonal
polynomials. -/
theorem bernsteinSzego_top (h : ℂ → ℂ) (hh : DiffContOnCl ℂ h (Metric.ball 0 1))
    (hnz : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, h z ≠ 0) (m : ℕ) :
    bsInner h (bsTest h m) (fun z => z ^ (m : ℤ)) = 2 * Real.pi * (h 0)⁻¹ := by
  have hhc := circle_ne_zero_of_closedBall h hnz
  rw [bsInner_bsTest_monomial h m m hhc, sub_self,
    circleMoment_zero _ (diffContOnCl_inv h hh hnz)]

/-- **Exact Szegő norm.**  The squared `L²(|h|⁻² dθ)` norm of the test function is `2π`,
independently of `m`.  The integrand collapses to the constant `1` because `|ψ_m|² = |h|²`
on the circle.  This is Szegő's asymptotic law made exact for Bernstein–Szegő weights. -/
theorem bernsteinSzego_normSq (h : ℂ → ℂ)
    (hnz : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, h z ≠ 0) (m : ℕ) :
    bsInner h (bsTest h m) (bsTest h m) = 2 * Real.pi := by
  have hhc := circle_ne_zero_of_closedBall h hnz
  have hone : bsInner h (bsTest h m) (bsTest h m)
      = ∫ _θ in (0 : ℝ)..(2 * Real.pi), (1 : ℂ) := by
    rw [bsInner]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [bsTest]
    have hzne : circleMap 0 1 θ ≠ 0 := circleMap_unit_ne_zero θ
    have hhne : h (circleMap 0 1 θ) ≠ 0 := hhc θ
    have hchne : (starRingEnd ℂ) (h (circleMap 0 1 θ)) ≠ 0 := by simpa using hhne
    rw [map_mul, map_zpow₀, conj_circleMap_unit θ, Complex.conj_conj, inv_zpow]
    field_simp
  rw [hone]
  simp [mul_comm]

end ValueDistribution.BernsteinSzego
