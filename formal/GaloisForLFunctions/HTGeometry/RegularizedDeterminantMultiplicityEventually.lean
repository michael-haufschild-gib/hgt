import GaloisForLFunctions.HTGeometry.RegularizedDeterminantMultiplicity

/-!
# Eventual boundary form of determinant multiplicity

Uniform convergence to a function nonvanishing on a compact circle makes the approximants
nonvanishing there eventually.  Consequently the finite-section argument-principle identity is
needed only eventually, not for every early truncation.
-/

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt Metric Filter Matrix

/-- Uniform convergence on a containing closed ball preserves nonvanishing on an interior sphere
eventually. -/
theorem eventually_forall_ne_zero_on_sphere_of_tendstoUniformlyOn
    {α : Type*} {p : Filter α} {F : α → ℂ → ℂ} {f : ℂ → ℂ}
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : ContinuousOn f (sphere c r)) (hfne : ∀ z ∈ sphere c r, f z ≠ 0)
    (huniform : TendstoUniformlyOn F f p (closedBall c R)) :
    ∀ᶠ a in p, ∀ z ∈ sphere c r, F a z ≠ 0 := by
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_norm_on_sphere hr hf hfne
  rw [Metric.tendstoUniformlyOn_iff] at huniform
  filter_upwards [huniform (m / 2) (half_pos hm)] with a ha
  intro z hz hzero
  have hzR : z ∈ closedBall c R := by
    rw [mem_closedBall, mem_sphere.mp hz]
    exact hrR.le
  have hdist : ‖f z‖ < m / 2 := by
    simpa [Complex.dist_eq, hzero] using ha z hzR
  linarith [hmle z hz]

/-- Counting Hurwitz when the integral formula for the integer count holds eventually. -/
theorem eventually_zeroCount_eq_analyticOrder_of_eventually {α : Type*} {p : Filter α}
    {F : α → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ a, Differentiable ℂ (F a))
    (hf : Differentiable ℂ f) {c : ℂ} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (huniform : TendstoUniformlyOn F f p (closedBall c R))
    {d : ℕ} {R' : ℝ} (hrR' : r < R') (hord : analyticOrderAt f c = (d : ℕ∞))
    (hne : ∀ z ∈ closedBall c R', z ≠ c → f z ≠ 0) {n : α → ℕ}
    (hn : ∀ᶠ a in p, (∮ z in C(c, r), logDeriv (F a) z)
      = 2 * Real.pi * Complex.I * (n a : ℂ)) :
    ∀ᶠ a in p, n a = d := by
  have hfne : ∀ z ∈ sphere c r, f z ≠ 0 := by
    intro z hz
    have hd : dist z c = r := mem_sphere.mp hz
    refine hne z (by rw [mem_closedBall, hd]; linarith) fun hzc => ?_
    rw [hzc, dist_self] at hd
    exact hr.ne hd
  have hlim := tendsto_circleIntegral_logDeriv hF hf hr hrR huniform hfne
  have hf' : (∮ z in C(c, r), logDeriv f z) =
      2 * Real.pi * Complex.I * (d : ℂ) := by
    have h := circleIntegral_logDeriv_eq_analyticOrder_local (R := R') hf hord
      (fun z hz hzc => hne z (ball_subset_closedBall hz) hzc) hr hrR'
    simpa [logDeriv_apply] using h
  have hscaled : Tendsto (fun a => 2 * Real.pi * Complex.I * (n a : ℂ)) p
      (nhds (2 * Real.pi * Complex.I * (d : ℂ))) := by
    have h := hlim.congr' hn
    rw [hf'] at h
    exact h
  have hconst : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have htend := hscaled.const_mul ((2 * Real.pi * Complex.I : ℂ)⁻¹)
  simp only [← mul_assoc, inv_mul_cancel₀ hconst, one_mul] at htend
  exact eventually_eq_of_tendsto_natCast htend

open scoped Classical in
/-- **The analytic order is eventually the Schur reciprocal-eigenvalue count, with boundary
nonvanishing derived from uniform convergence rather than assumed for every truncation.** -/
theorem eventually_schurCount_eq_analyticOrder' {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K) {z₀ : ℂ} {d : ℕ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hord : analyticOrderAt (entireDet2 K) z₀ = (d : ℕ∞))
    (hne : ∀ z ∈ closedBall z₀ R, z ≠ z₀ → entireDet2 K z ≠ 0)
    (U T : ∀ s : Finset ι,
      Matrix (Fin (Fintype.card ↥s)) (Fin (Fintype.card ↥s)) ℂ)
    (hU1 : ∀ s, (U s)ᴴ * U s = 1) (hU2 : ∀ s, U s * (U s)ᴴ = 1)
    (hT : ∀ s, (T s).BlockTriangular id)
    (hMT : ∀ s, (U s)ᴴ * (-(blockFin K s)) * U s = T s) :
    ∀ᶠ s : Finset ι in atTop,
      (Finset.univ.filter fun i => T s i i ≠ 0 ∧ -(T s i i)⁻¹ ∈ ball z₀ r).card = d := by
  have hρ : 0 < ‖z₀‖ + R := by
    have := norm_nonneg z₀
    linarith
  have hsub : closedBall z₀ R ⊆ closedBall (0 : ℂ) (‖z₀‖ + R) := by
    refine closedBall_subset_closedBall' ?_
    rw [Complex.dist_eq, sub_zero]
    linarith
  have huniform := (tendstoUniformlyOn_finiteDet2_entireDet2 hK hρ).mono hsub
  have hlimitSphere : ∀ z ∈ sphere z₀ r, entireDet2 K z ≠ 0 := by
    intro z hz
    have hd := mem_sphere.mp hz
    refine hne z (by rw [mem_closedBall, hd]; exact hrR.le) fun heq => ?_
    rw [heq, dist_self] at hd
    exact hr.ne hd
  have hfiniteSphere : ∀ᶠ s : Finset ι in atTop,
      ∀ z ∈ sphere z₀ r, finiteDet2 (-(blockMatrix K s)) z ≠ 0 :=
    eventually_forall_ne_zero_on_sphere_of_tendstoUniformlyOn hr hrR
      (differentiable_entireDet2 hK).continuous.continuousOn hlimitSphere huniform
  have hsph : ∀ᶠ s : Finset ι in atTop,
      ∀ z ∈ sphere z₀ r, ∀ i, 1 + z * T s i i ≠ 0 := by
    filter_upwards [hfiniteSphere] with s hs z hz i hfactor
    have hdet : finiteDet2 (-(blockFin K s)) z ≠ 0 := by
      rw [finiteDet2_neg_blockFin]
      exact hs z hz
    apply hdet
    rw [finiteDet2_eq_prod (hU1 s) (hU2 s) (hT s) (hMT s)]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hfactor, zero_mul]
  let n : Finset ι → ℕ := fun s =>
    (Finset.univ.filter fun i => T s i i ≠ 0 ∧ -(T s i i)⁻¹ ∈ ball z₀ r).card
  have hn : ∀ᶠ s : Finset ι in atTop,
      (∮ z in C(z₀, r), logDeriv (finiteDet2 (-(blockMatrix K s))) z)
        = 2 * Real.pi * Complex.I * (n s : ℂ) := by
    filter_upwards [hsph] with s hs
    have h := circleIntegral_logDeriv_finiteDet2
      (hU1 s) (hU2 s) (hT s) (hMT s) hr hs
    have hfun : finiteDet2 (-(blockFin K s)) = finiteDet2 (-(blockMatrix K s)) :=
      funext (finiteDet2_neg_blockFin K s)
    rw [hfun] at h
    exact h
  exact eventually_zeroCount_eq_analyticOrder_of_eventually
    (fun s => differentiable_finiteDet2 (-(blockMatrix K s)))
    (differentiable_entireDet2 hK) hr hrR huniform hrR hord hne hn

end GaloisForLFunctions.HTGeometry
