import GaloisForLFunctions.HTGeometry.StripHullSeparation
import GaloisForLFunctions.HTGeometry.JetSampleSeparation
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Sampling jets by a contour integral

Cauchy's formula writes the `k`-th derivative of a holomorphic function at a point as an integral of
its values on a circle around that point.  On the carrier of the strip translate curve the values are
what a carrier point *is*, so the formula turns the jet sample into a bounded linear functional of the
carrier point — in particular a Lipschitz, hence continuous, map to `ℂ`.
-/

open Filter Topology Metric Set Complex

open scoped BoundedContinuousFunction Real

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- The `k`-th jet of a carrier point, sampled by Cauchy's integral around a circle inside the
substrip. -/
noncomputable def circleJetSample {σ r : ℝ} (z₀ : ℂ) (ρ : ℝ)
    (hball : ∀ θ : ℝ, circleMap z₀ ρ θ ∈ closedStrip σ r) (k : ℕ)
    (u : (closedStrip σ r) →ᵇ ℂ) : ℂ :=
  ((k.factorial : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      deriv (circleMap z₀ ρ) θ * ((1 / (circleMap z₀ ρ θ - z₀) ^ (k + 1)) *
        u ⟨circleMap z₀ ρ θ, hball θ⟩)

/-- **The jet sample is Lipschitz in the carrier point.** -/
theorem lipschitzWith_circleJetSample {σ r : ℝ} (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ∀ θ : ℝ, circleMap z₀ ρ θ ∈ closedStrip σ r) (k : ℕ) :
    ∃ C : NNReal, LipschitzWith C (circleJetSample z₀ ρ hball k) := by
  classical
  set A : ℝ := (k.factorial : ℝ) / (2 * Real.pi) * (ρ ^ k)⁻¹ * (2 * Real.pi) with hA
  have hA0 : 0 ≤ A := by
    have h1 : (0 : ℝ) ≤ (k.factorial : ℝ) / (2 * Real.pi) := by positivity
    have h2 : (0 : ℝ) ≤ (ρ ^ k)⁻¹ := by positivity
    have h3 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    positivity
  refine ⟨⟨A, hA0⟩, ?_⟩
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  have hnormfac : ‖((k.factorial : ℂ) / (2 * (Real.pi : ℂ) * Complex.I))‖
      = (k.factorial : ℝ) / (2 * Real.pi) := by
    rw [norm_div]
    simp [abs_of_pos Real.pi_pos]
  have hkernel : ∀ θ : ℝ, ‖deriv (circleMap z₀ ρ) θ
      * ((1 / (circleMap z₀ ρ θ - z₀) ^ (k + 1)) * (u ⟨circleMap z₀ ρ θ, hball θ⟩
        - v ⟨circleMap z₀ ρ θ, hball θ⟩))‖ ≤ (ρ ^ k)⁻¹ * dist u v := by
    intro θ
    have hderiv : ‖deriv (circleMap z₀ ρ) θ‖ = ρ := by
      rw [deriv_circleMap]
      simp [abs_of_pos hρ]
    have hsub : ‖(circleMap z₀ ρ θ - z₀) ^ (k + 1)‖ = ρ ^ (k + 1) := by
      rw [circleMap_sub_center, norm_pow]
      simp [abs_of_pos hρ]
    have hval : ‖u ⟨circleMap z₀ ρ θ, hball θ⟩ - v ⟨circleMap z₀ ρ θ, hball θ⟩‖ ≤ dist u v := by
      rw [← dist_eq_norm]
      exact BoundedContinuousFunction.dist_coe_le_dist _
    rw [norm_mul, norm_mul, hderiv, norm_div, hsub]
    have hρk : (0 : ℝ) < ρ ^ (k + 1) := by positivity
    calc ρ * (‖(1 : ℂ)‖ / ρ ^ (k + 1)
        * ‖u ⟨circleMap z₀ ρ θ, hball θ⟩ - v ⟨circleMap z₀ ρ θ, hball θ⟩‖)
        ≤ ρ * (1 / ρ ^ (k + 1) * dist u v) := by
          have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
          rw [h1]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hval (by positivity)) hρ.le
      _ = (ρ ^ k)⁻¹ * dist u v := by
          field_simp
          ring
  have hint : ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
      (deriv (circleMap z₀ ρ) θ * ((1 / (circleMap z₀ ρ θ - z₀) ^ (k + 1)) *
        u ⟨circleMap z₀ ρ θ, hball θ⟩)
      - deriv (circleMap z₀ ρ) θ * ((1 / (circleMap z₀ ρ θ - z₀) ^ (k + 1)) *
        v ⟨circleMap z₀ ρ θ, hball θ⟩))‖ ≤ ((ρ ^ k)⁻¹ * dist u v) * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    have hrw : deriv (circleMap z₀ ρ) θ * ((1 / (circleMap z₀ ρ θ - z₀) ^ (k + 1)) *
        u ⟨circleMap z₀ ρ θ, hball θ⟩)
      - deriv (circleMap z₀ ρ) θ * ((1 / (circleMap z₀ ρ θ - z₀) ^ (k + 1)) *
        v ⟨circleMap z₀ ρ θ, hball θ⟩)
      = deriv (circleMap z₀ ρ) θ * ((1 / (circleMap z₀ ρ θ - z₀) ^ (k + 1)) *
        (u ⟨circleMap z₀ ρ θ, hball θ⟩ - v ⟨circleMap z₀ ρ θ, hball θ⟩)) := by
      ring
    rw [hrw]
    exact hkernel θ
  have hcont : ∀ w : (closedStrip σ r) →ᵇ ℂ, Continuous (fun θ : ℝ =>
      deriv (circleMap z₀ ρ) θ * ((1 / (circleMap z₀ ρ θ - z₀) ^ (k + 1)) *
        w ⟨circleMap z₀ ρ θ, hball θ⟩)) := by
    intro w
    have hcm : Continuous (fun θ : ℝ => circleMap z₀ ρ θ) := continuous_circleMap _ _
    have hsubc : Continuous (fun θ : ℝ => (⟨circleMap z₀ ρ θ, hball θ⟩ : closedStrip σ r)) :=
      hcm.subtype_mk _
    have hw : Continuous (fun θ : ℝ => w ⟨circleMap z₀ ρ θ, hball θ⟩) := w.continuous.comp hsubc
    have hker : Continuous (fun θ : ℝ => (1 : ℂ) / (circleMap z₀ ρ θ - z₀) ^ (k + 1)) := by
      refine continuous_const.div ((hcm.sub continuous_const).pow _) fun θ => ?_
      have hne : circleMap z₀ ρ θ - z₀ ≠ 0 := sub_ne_zero.mpr (circleMap_ne_center hρ.ne')
      exact pow_ne_zero _ hne
    have hd : Continuous (fun θ : ℝ => deriv (circleMap z₀ ρ) θ) := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 ρ).mul continuous_const
    exact hd.mul (hker.mul hw)
  rw [dist_eq_norm, circleJetSample, circleJetSample, ← mul_sub,
    ← intervalIntegral.integral_sub ((hcont u).intervalIntegrable _ _)
      ((hcont v).intervalIntegrable _ _), norm_mul, hnormfac]
  have habs : |2 * Real.pi - 0| = 2 * Real.pi := by
    rw [sub_zero, abs_of_pos (by positivity)]
  rw [habs] at hint
  have hfacnn : (0 : ℝ) ≤ (k.factorial : ℝ) / (2 * Real.pi) := by positivity
  calc (k.factorial : ℝ) / (2 * Real.pi) * ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
        (deriv (circleMap z₀ ρ) θ * ((1 / (circleMap z₀ ρ θ - z₀) ^ (k + 1)) *
          u ⟨circleMap z₀ ρ θ, hball θ⟩)
        - deriv (circleMap z₀ ρ) θ * ((1 / (circleMap z₀ ρ θ - z₀) ^ (k + 1)) *
          v ⟨circleMap z₀ ρ θ, hball θ⟩))‖
      ≤ (k.factorial : ℝ) / (2 * Real.pi) * (((ρ ^ k)⁻¹ * dist u v) * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hint hfacnn
    _ = A * dist u v := by
        rw [hA]
        ring

/-- **The sample is the jet.**  For a carrier point represented by a holomorphic function on a disc
inside the substrip, the contour sample returns its `k`-th derivative at the centre. -/
theorem circleJetSample_eq_iteratedDeriv {σ r : ℝ} {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ∀ θ : ℝ, circleMap z₀ ρ θ ∈ closedStrip σ r) (k : ℕ)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.closedBall z₀ ρ))
    {u : (closedStrip σ r) →ᵇ ℂ} (hu : ∀ z : closedStrip σ r, u z = g (z : ℂ)) :
    circleJetSample z₀ ρ hball k u = iteratedDeriv k g z₀ := by
  have hcauchy := hg.circleIntegral_one_div_sub_center_pow_smul hρ k
  have hval : (∮ z in C(z₀, ρ), (1 / (z - z₀) ^ (k + 1)) • g z)
      = ∫ θ in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap z₀ ρ) θ * ((1 / (circleMap z₀ ρ θ - z₀) ^ (k + 1)) *
          u ⟨circleMap z₀ ρ θ, hball θ⟩) := by
    rw [circleIntegral]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [hu ⟨circleMap z₀ ρ θ, hball θ⟩]
    simp [smul_eq_mul]
  rw [hval] at hcauchy
  have hfac : (2 * (Real.pi : ℂ) * Complex.I / (k.factorial : ℂ)) ≠ 0 := by
    refine div_ne_zero ?_ ?_
    · exact Complex.two_pi_I_ne_zero
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [circleJetSample, hcauchy, smul_eq_mul]
  field_simp
  rw [mul_comm, mul_div_assoc, div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)),
    mul_one]

/-- **The contour jet sample separates carrier points.**  Where the separant does not vanish, two
carrier points with the same sampled jets are equal. -/
theorem hull_injective_of_circleJetSample {σ R r : ℝ} (hr0 : 0 < r) (hr : r < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    {n : ℕ} (hn : 0 < n) (P : MvPolynomial (Fin (n + 1)) ℂ)
    (hrel : ∀ z ∈ verticalStrip σ R,
      MvPolynomial.eval (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F z) P = 0)
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ ℂ)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I))
    (t₀ : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ∀ θ : ℝ, circleMap ((σ : ℂ) + (t₀ : ℂ) * Complex.I) ρ θ ∈ closedStrip σ r)
    (hdisc : Metric.closedBall ((σ : ℂ) + (t₀ : ℂ) * Complex.I) ρ ⊆ verticalStrip σ r)
    (hsep : ∀ (x : BohrHull Gb) (g : ℂ → ℂ), DifferentiableOn ℂ g (verticalStrip σ r) →
      (∀ z : closedStrip σ r, g (z : ℂ) = bohrEval Gb x z) →
      deriv (fun u : ℂ => MvPolynomial.eval
          (Fin.snoc (jetVec (n := n) (lineFun σ g) t₀) u)
          (scaleVars (fun k : Fin (n + 1) => (Complex.I ^ (k : ℕ))⁻¹) P))
        (iteratedDeriv n (lineFun σ g) t₀) ≠ 0) :
    Function.Injective (fun x : BohrHull Gb => fun k : Fin (n + 1) =>
      circleJetSample ((σ : ℂ) + (t₀ : ℂ) * Complex.I) ρ hball (k : ℕ) (bohrEval Gb x)) := by
  intro x y hxy
  obtain ⟨gx, hgxd, hgxv⟩ := exists_holomorphic_of_hull hr hF hGb x
  obtain ⟨gy, hgyd, hgyv⟩ := exists_holomorphic_of_hull hr hF hGb y
  have hgxball : DifferentiableOn ℂ gx (Metric.closedBall ((σ : ℂ) + (t₀ : ℂ) * Complex.I) ρ) :=
    hgxd.mono hdisc
  have hgyball : DifferentiableOn ℂ gy (Metric.closedBall ((σ : ℂ) + (t₀ : ℂ) * Complex.I) ρ) :=
    hgyd.mono hdisc
  have hjetx : ∀ k : ℕ, circleJetSample ((σ : ℂ) + (t₀ : ℂ) * Complex.I) ρ hball k
      (bohrEval Gb x) = iteratedDeriv k gx ((σ : ℂ) + (t₀ : ℂ) * Complex.I) :=
    fun k => circleJetSample_eq_iteratedDeriv hρ hball k hgxball (fun z => (hgxv z).symm)
  have hjety : ∀ k : ℕ, circleJetSample ((σ : ℂ) + (t₀ : ℂ) * Complex.I) ρ hball k
      (bohrEval Gb y) = iteratedDeriv k gy ((σ : ℂ) + (t₀ : ℂ) * Complex.I) :=
    fun k => circleJetSample_eq_iteratedDeriv hρ hball k hgyball (fun z => (hgyv z).symm)
  have hcplx : ∀ k : Fin (n + 1), iteratedDeriv (k : ℕ) gx ((σ : ℂ) + (t₀ : ℂ) * Complex.I)
      = iteratedDeriv (k : ℕ) gy ((σ : ℂ) + (t₀ : ℂ) * Complex.I) := by
    intro k
    have h : circleJetSample ((σ : ℂ) + (t₀ : ℂ) * Complex.I) ρ hball (k : ℕ) (bohrEval Gb x)
        = circleJetSample ((σ : ℂ) + (t₀ : ℂ) * Complex.I) ρ hball (k : ℕ) (bohrEval Gb y) :=
      congrFun hxy k
    rw [hjetx (k : ℕ), hjety (k : ℕ)] at h
    exact h
  have hline : ∀ k : Fin (n + 1),
      iteratedDeriv (k : ℕ) (lineFun σ gx) t₀ = iteratedDeriv (k : ℕ) (lineFun σ gy) t₀ := by
    intro k
    show iteratedDeriv (k : ℕ) (fun s : ℝ => gx ((σ : ℂ) + (s : ℂ) * Complex.I)) t₀
      = iteratedDeriv (k : ℕ) (fun s : ℝ => gy ((σ : ℂ) + (s : ℂ) * Complex.I)) t₀
    rw [iteratedDeriv_line_restriction hr0 hgxd (k : ℕ) t₀,
      iteratedDeriv_line_restriction hr0 hgyd (k : ℕ) t₀, hcplx k]
  exact hull_eq_of_jet_sample_eq hr0 hr hF hn P hrel hGb t₀ hgxd hgxv hgyd hgyv hline
    (hsep x gx hgxd hgxv)

end GaloisForLFunctions
