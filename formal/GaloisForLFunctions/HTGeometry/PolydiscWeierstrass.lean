import GaloisForLFunctions.HTGeometry.PolydiscApproximation

/-!
# Weierstrass' theorem in several complex variables

A limit, uniform on every closed ball strictly inside, of functions holomorphic on a ball is
holomorphic there.  The proof passes to the limit in the Cauchy integral formula over a small torus
around each point: the kernel is bounded there because the point is strictly inside, the convergence
is uniform on the compact torus, and the resulting formula produces the Cauchy power series of the
limit, hence its analyticity at that point.

* `GaloisForLFunctions.HTGeometry.polydiscSet_const` : a polydisc with equal radii is a ball of the
  supremum norm.
* `GaloisForLFunctions.HTGeometry.tendsto_torusIntegral_smul` : uniform convergence passes through a
  torus integral against a bounded kernel.
* `GaloisForLFunctions.HTGeometry.differentiableOn_of_tendstoUniformlyOn` : Weierstrass' theorem.
-/

open MeasureTheory Complex Set
open scoped Real

namespace GaloisForLFunctions.HTGeometry

section BallPolydisc

variable {n : ℕ}

/-- A polydisc with equal radii is the ball of the supremum norm. -/
theorem polydiscSet_const (c : Fin n → ℂ) {R : ℝ} (hR : 0 < R) :
    polydiscSet c (fun _ => R) = Metric.ball c R := by
  ext z
  rw [mem_polydiscSet, Metric.mem_ball, dist_pi_lt_iff hR]
  rfl

end BallPolydisc

section IntegralLimit

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Uniform convergence passes through a torus integral against a bounded kernel.** -/
theorem tendsto_torusIntegral_smul
    {F : ℕ → (Fin n → ℂ) → E} {g : (Fin n → ℂ) → E} {K : (Fin n → ℂ) → ℂ}
    {c : Fin n → ℂ} {R : Fin n → ℝ} {S : Set (Fin n → ℂ)} {CK : ℝ}
    (hKcomp : Continuous fun θ : Fin n → ℝ => K (torusMap c R θ))
    (hFcont : ∀ k, Continuous fun θ : Fin n → ℝ => F k (torusMap c R θ))
    (hgcont : Continuous fun θ : Fin n → ℝ => g (torusMap c R θ))
    (hKb : ∀ θ, ‖K (torusMap c R θ)‖ ≤ CK) (hCK : 0 ≤ CK)
    (hmem : ∀ θ, torusMap c R θ ∈ S)
    (huni : TendstoUniformlyOn F g Filter.atTop S) :
    Filter.Tendsto (fun k => ∯ ζ in T(c, R), K ζ • F k ζ) Filter.atTop
      (nhds (∯ ζ in T(c, R), K ζ • g ζ)) := by
  have hmap : Continuous fun θ : Fin n → ℝ => torusMap c R θ := continuous_torusMap c R
  have hintF : ∀ k, TorusIntegrable (fun ζ => K ζ • F k ζ) c R := fun k =>
    torusIntegrable_of_continuous (hKcomp.smul (hFcont k))
  have hintg : TorusIntegrable (fun ζ => K ζ • g ζ) c R :=
    torusIntegrable_of_continuous (hKcomp.smul hgcont)
  set B : ℝ := (2 * Real.pi) ^ n * ∏ i, |R i| with hB
  have hBnn : (0 : ℝ) ≤ B := by
    rw [hB]
    positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hden : (0 : ℝ) < B * CK + 1 := by positivity
  set δ : ℝ := ε / (B * CK + 1) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 huni δ hδpos)
  refine ⟨N, fun k hk => ?_⟩
  have hsub : (∯ ζ in T(c, R), K ζ • F k ζ) - (∯ ζ in T(c, R), K ζ • g ζ)
      = ∯ ζ in T(c, R), (K ζ • F k ζ - K ζ • g ζ) := (torusIntegral_sub (hintF k) hintg).symm
  rw [dist_eq_norm, hsub]
  have hpt : ∀ θ : Fin n → ℝ,
      ‖K (torusMap c R θ) • F k (torusMap c R θ) - K (torusMap c R θ) • g (torusMap c R θ)‖
        ≤ CK * δ := by
    intro θ
    rw [← smul_sub, norm_smul]
    refine mul_le_mul (hKb θ) ?_ (norm_nonneg _) hCK
    have hd := hN k hk (torusMap c R θ) (hmem θ)
    rw [dist_eq_norm] at hd
    rw [← norm_neg, neg_sub]
    exact le_of_lt hd
  refine lt_of_le_of_lt (norm_torusIntegral_le_of_norm_le_const hpt) ?_
  rw [hδ, show B * (CK * (ε / (B * CK + 1))) = B * CK * ε / (B * CK + 1) by ring,
    div_lt_iff₀ hden]
  nlinarith [hε, hBnn, hCK]

end IntegralLimit

section Weierstrass

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Weierstrass' theorem in several complex variables.**  A limit, uniform on every closed ball
strictly inside, of functions holomorphic on a ball is holomorphic on that ball. -/
theorem differentiableOn_of_tendstoUniformlyOn
    {F : ℕ → (Fin n → ℂ) → E} {g : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : ℝ} (hR : 0 < R)
    (hFcont : ∀ k, ContinuousOn (F k) (Metric.ball c R))
    (hFdiff : ∀ k, DifferentiableOn ℂ (F k) (Metric.ball c R))
    (hgcont : ContinuousOn g (Metric.ball c R))
    (huni : ∀ ρ : ℝ, 0 ≤ ρ → ρ < R →
      TendstoUniformlyOn F g Filter.atTop (Metric.closedBall c ρ)) :
    DifferentiableOn ℂ g (Metric.ball c R) := by
  intro z₀ hz₀
  rw [Metric.mem_ball] at hz₀
  set d : ℝ := dist z₀ c with hd
  have hdnn : 0 ≤ d := dist_nonneg
  set r : ℝ := (R - d) / 4 with hr
  have hrpos : 0 < r := by
    rw [hr]; linarith
  set ρ : ℝ := d + 2 * r with hρ
  have hρnn : 0 ≤ ρ := by rw [hρ]; linarith
  have hρR : ρ < R := by rw [hρ, hr]; linarith
  have hsubc : Metric.closedBall z₀ (2 * r) ⊆ Metric.closedBall c ρ := by
    intro w hw
    rw [Metric.mem_closedBall] at hw ⊢
    calc dist w c ≤ dist w z₀ + dist z₀ c := dist_triangle w z₀ c
      _ ≤ 2 * r + d := by rw [← hd]; linarith
      _ = ρ := by rw [hρ]; ring
  have hsubball : Metric.closedBall z₀ (2 * r) ⊆ Metric.ball c R := fun w hw =>
    Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp (hsubc hw)) hρR)
  have hFdisc : ∀ k, DifferentiableOn ℂ (F k) (polydiscSet z₀ fun _ => 2 * r) := by
    intro k
    refine (hFdiff k).mono ?_
    rw [polydiscSet_const z₀ (by linarith)]
    exact Metric.ball_subset_closedBall.trans hsubball
  have hunifρ : TendstoUniformlyOn F g Filter.atTop (Metric.closedBall c ρ) := huni ρ hρnn hρR
  have hcauchy : ∀ z : Fin n → ℂ, (∀ i, z i ∈ Metric.ball (z₀ i) r) →
      (∯ ζ in T(z₀, fun _ => r), (∏ i, (ζ i - z i)⁻¹) • g ζ) =
        ((2 * Real.pi * Complex.I) ^ n : ℂ) • g z := by
    intro z hz
    have hFcauchy : ∀ k,
        (∯ ζ in T(z₀, fun _ => r), (∏ i, (ζ i - z i)⁻¹) • F k ζ) =
          ((2 * Real.pi * Complex.I) ^ n : ℂ) • F k z := fun k =>
      polydiscCauchyFormula_of_differentiableOn n (F k) z₀ (fun _ => 2 * r) (fun _ => r)
        (hFdisc k) (fun _ => hrpos.le) (fun _ => by linarith) z hz
    have hmap : Continuous fun θ : Fin n → ℝ => torusMap z₀ (fun _ => r) θ :=
      continuous_torusMap z₀ (fun _ => r)
    have hne : ∀ (θ : Fin n → ℝ) (i : Fin n), torusMap z₀ (fun _ => r) θ i - z i ≠ 0 :=
      torusMap_sub_ne_zero hz
    have hKcomp : Continuous fun θ : Fin n → ℝ =>
        ∏ i, (torusMap z₀ (fun _ => r) θ i - z i)⁻¹ := by
      refine continuous_finsetProd _ fun i _ => ?_
      exact (((continuous_apply i).comp hmap).sub continuous_const).inv₀ fun θ => hne θ i
    -- the point is strictly inside, so the kernel is bounded on the torus
    set s : ℝ := dist z z₀ with hs
    have hsr : s < r := by
      rw [hs, dist_pi_lt_iff hrpos]
      intro i
      exact Metric.mem_ball.mp (hz i)
    have hsnn : 0 ≤ s := dist_nonneg
    have hKb : ∀ θ : Fin n → ℝ,
        ‖∏ i, (torusMap z₀ (fun _ => r) θ i - z i)⁻¹‖ ≤ ((r - s)⁻¹) ^ n := by
      intro θ
      rw [norm_prod]
      have hterm : ∀ i : Fin n, ‖(torusMap z₀ (fun _ => r) θ i - z i)⁻¹‖ ≤ (r - s)⁻¹ := by
        intro i
        rw [norm_inv]
        refine inv_anti₀ (by linarith) ?_
        have h1 : ‖torusMap z₀ (fun _ => r) θ i - z₀ i‖ = r := by
          rw [norm_torusMap_sub_center, abs_of_pos hrpos]
        have h2 : ‖z i - z₀ i‖ ≤ s := by
          rw [hs, ← Complex.dist_eq]
          exact dist_le_pi_dist z z₀ i
        have h3 : ‖torusMap z₀ (fun _ => r) θ i - z₀ i‖ - ‖z i - z₀ i‖ ≤
            ‖torusMap z₀ (fun _ => r) θ i - z i‖ := by
          have := norm_sub_norm_le (torusMap z₀ (fun _ => r) θ i - z₀ i) (z i - z₀ i)
          simpa using this
        linarith
      refine le_trans (Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hterm i) ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hmemS : ∀ θ : Fin n → ℝ, torusMap z₀ (fun _ => r) θ ∈ Metric.closedBall c ρ := by
      intro θ
      refine hsubc ?_
      rw [Metric.mem_closedBall, dist_pi_le_iff (by linarith)]
      intro i
      rw [Complex.dist_eq, norm_torusMap_sub_center, abs_of_pos hrpos]
      linarith
    have hballsub : ∀ θ : Fin n → ℝ, torusMap z₀ (fun _ => r) θ ∈ Metric.ball c R := by
      intro θ
      refine hsubball ?_
      rw [Metric.mem_closedBall, dist_pi_le_iff (by linarith)]
      intro i
      rw [Complex.dist_eq, norm_torusMap_sub_center, abs_of_pos hrpos]
      linarith
    have hFcont' : ∀ k, Continuous fun θ : Fin n → ℝ => F k (torusMap z₀ (fun _ => r) θ) :=
      fun k => (hFcont k).comp_continuous hmap hballsub
    have hgcont' : Continuous fun θ : Fin n → ℝ => g (torusMap z₀ (fun _ => r) θ) :=
      hgcont.comp_continuous hmap hballsub
    have h1 := tendsto_torusIntegral_smul (K := fun ζ => ∏ i, (ζ i - z i)⁻¹) hKcomp hFcont' hgcont'
      hKb (by positivity) hmemS hunifρ
    have hzmem : z ∈ Metric.closedBall c ρ := by
      refine hsubc ?_
      rw [Metric.mem_closedBall, ← hs]
      linarith
    have h2 : Filter.Tendsto (fun k => ((2 * Real.pi * Complex.I) ^ n : ℂ) • F k z)
        Filter.atTop (nhds (((2 * Real.pi * Complex.I) ^ n : ℂ) • g z)) :=
      (hunifρ.tendsto_at hzmem).const_smul _
    have h1' : Filter.Tendsto (fun k => ((2 * Real.pi * Complex.I) ^ n : ℂ) • F k z)
        Filter.atTop (nhds (∯ ζ in T(z₀, fun _ => r), (∏ i, (ζ i - z i)⁻¹) • g ζ)) := by
      refine h1.congr fun k => hFcauchy k
    exact tendsto_nhds_unique h1' h2
  have hball := polydiscHasFPowerSeriesOnBall_of_cauchy hrpos
    (hgcont.mono (fun x hx => hsubball (by
      rw [Metric.mem_closedBall, dist_pi_le_iff (by linarith)]
      intro i
      rw [Complex.dist_eq, hx i]
      linarith))) hcauchy
  exact (hball.analyticAt.differentiableAt).differentiableWithinAt

end Weierstrass

section LocalAnalytic

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Holomorphy on an open set implies analyticity there.**  mathlib has this only in one
variable; in several variables it comes from the local Cauchy power series. -/
theorem analyticAt_of_differentiableOn {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z : Fin n → ℂ} (hz : z ∈ U) : AnalyticAt ℂ f z := by
  obtain ⟨R₁, hR₁pos, hR₁sub⟩ := Metric.isOpen_iff.1 hU z hz
  have hdiff : DifferentiableOn ℂ f (polydiscSet z fun _ => R₁) := by
    rw [polydiscSet_const z hR₁pos]
    exact hf.mono hR₁sub
  exact (polydiscHasFPowerSeriesOnBall_of_differentiableOn z (R := R₁ / 2) (R₁ := R₁)
    (by positivity) (by linarith) hdiff).analyticAt

/-- **Holomorphy on an open set implies smoothness there, over `ℂ`.** -/
theorem contDiffAt_complex_of_differentiableOn {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {z : Fin n → ℂ} (hz : z ∈ U) :
    ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) f z :=
  (analyticAt_of_differentiableOn hU hf hz).contDiffAt

/-- **The differential of a holomorphic function is continuous on the domain.** -/
theorem continuousOn_fderiv_of_differentiableOn {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fderiv ℂ f) U := by
  intro z hz
  have hC := contDiffAt_complex_of_differentiableOn hU hf hz
  have h1 : ContDiffAt ℂ (1 : WithTop ℕ∞) f z := hC.of_le (by exact_mod_cast le_top)
  exact ((h1.continuousAt_fderiv one_ne_zero).continuousWithinAt)

end LocalAnalytic

end GaloisForLFunctions.HTGeometry
