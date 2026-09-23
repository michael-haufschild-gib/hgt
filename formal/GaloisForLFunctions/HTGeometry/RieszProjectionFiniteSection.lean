/-
# Stability of the Riesz projection under finite-section approximation

A circle in the resolvent set of `a` stays in the resolvent set of every nearby element, the
projections stay close, and two idempotents at distance less than one have the same rank.  So the
rank of the Riesz projection is locally constant in the element, and finite-dimensionality of its
range transfers.

When the contour avoids the origin the projection factors through the element itself, so an element
of finite rank has a projection of finite rank.

Main results:
* `exists_norm_resolvent_le_on_compact` — a uniform resolvent bound on a compact set.
* `forall_mem_resolventSet_of_norm_sub_le` — the compact set stays in the resolvent set.
* `rieszProjection_eq_mul`, `range_rieszProjection_le_range` — the projection factors through the
  element when the contour avoids the origin.
* `finiteDimensional_range_of_norm_sub_lt_one` — finite-dimensionality transfers between nearby
  idempotents.
* `exists_eps_finrank_range_rieszProjection_eq` — **the rank of the Riesz projection is locally
  constant in the element**.
-/
import GaloisForLFunctions.HTGeometry.ResolventPerturbation
import GaloisForLFunctions.HTGeometry.IdempotentSimilarity

namespace GaloisForLFunctions.HTGeometry

open Metric

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] {a b : A}

/-- **A uniform resolvent bound on a compact subset of the resolvent set.** -/
theorem exists_norm_resolvent_le_on_compact (a : A) {s : Set ℂ} (hs : IsCompact s)
    (h : ∀ lam ∈ s, lam ∈ resolventSet ℂ a) :
    ∃ M : ℝ, 0 < M ∧ ∀ lam ∈ s, ‖resolvent a lam‖ ≤ M := by
  have hcont : ContinuousOn (resolvent a) s := fun lam hlam =>
    ((spectrum.hasDerivAt_resolvent_const_left (h lam hlam)).continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hcont
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun lam hlam => le_trans (hC lam hlam) (le_max_left _ _)⟩

/-- A compact subset of the resolvent set stays in the resolvent set of every nearby element. -/
theorem forall_mem_resolventSet_of_norm_sub_le {s : Set ℂ} {M : ℝ}
    (h : ∀ lam ∈ s, lam ∈ resolventSet ℂ a) (hM : ∀ lam ∈ s, ‖resolvent a lam‖ ≤ M)
    (hab : 2 * ‖b - a‖ * M ≤ 1) : ∀ lam ∈ s, lam ∈ resolventSet ℂ b :=
  fun lam hlam => (norm_resolvent_sub_le_of_norm_sub_le (h lam hlam) (hM lam hlam) hab).1

/-- **The Riesz projection factors through the element when the contour avoids the origin.** -/
theorem rieszProjection_eq_mul (a : A) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ a) (h0 : (0 : ℂ) ∉ closedBall c r) :
    rieszProjection a c r
      = a * ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ lam in C(c, r), lam⁻¹ • resolvent a lam) := by
  have hne : ∀ lam ∈ sphere c r, lam ≠ 0 := fun lam hlam hcon =>
    h0 (hcon ▸ sphere_subset_closedBall hlam)
  have hcont : ContinuousOn (resolvent a) (sphere c r) := fun lam hlam =>
    ((spectrum.hasDerivAt_resolvent_const_left (h lam hlam)).continuousAt).continuousWithinAt
  have hkern : ContinuousOn (fun lam : ℂ => lam⁻¹) (sphere c r) :=
    ContinuousOn.inv₀ continuous_id.continuousOn hne
  have hci1 : CircleIntegrable (fun lam : ℂ => lam⁻¹ • (1 : A)) c r :=
    ContinuousOn.circleIntegrable hr (hkern.smul continuousOn_const)
  have hci2 : CircleIntegrable (fun lam => a * (lam⁻¹ • resolvent a lam)) c r :=
    ContinuousOn.circleIntegrable hr (continuousOn_const.mul (hkern.smul hcont))
  have hci3 : CircleIntegrable (fun lam => lam⁻¹ • resolvent a lam) c r :=
    ContinuousOn.circleIntegrable hr (hkern.smul hcont)
  have hpt : ∀ lam ∈ sphere c r,
      resolvent a lam = lam⁻¹ • (1 : A) + a * (lam⁻¹ • resolvent a lam) := by
    intro lam hlam
    have hlne : lam ≠ 0 := hne lam hlam
    have hkey : algebraMap ℂ A lam * resolvent a lam = 1 + a * resolvent a lam := by
      have := sub_mul_resolvent (h lam hlam)
      rw [sub_mul] at this
      linear_combination (norm := noncomm_ring) this
    have hsm : lam • resolvent a lam = 1 + a * resolvent a lam := by
      rw [← hkey, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    calc resolvent a lam = lam⁻¹ • (lam • resolvent a lam) := by
          rw [smul_smul, inv_mul_cancel₀ hlne, one_smul]
      _ = lam⁻¹ • ((1 : A) + a * resolvent a lam) := by rw [hsm]
      _ = lam⁻¹ • (1 : A) + a * (lam⁻¹ • resolvent a lam) := by
          rw [smul_add, mul_smul_comm]
  have hzero : (∮ lam in C(c, r), lam⁻¹ • (1 : A)) = 0 := by
    have hsc : (∮ lam in C(c, r), (lam⁻¹ : ℂ)) = 0 := by
      refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr
        Set.countable_empty ?_ (fun lam hlam => ?_)
      · exact ContinuousOn.inv₀ continuous_id.continuousOn
          (fun lam hlam hcon => h0 (hcon ▸ hlam))
      · exact DifferentiableAt.inv differentiableAt_id
          (fun hcon => h0 (hcon ▸ ball_subset_closedBall hlam.1))
    rw [circleIntegral.integral_smul_const, hsc, zero_smul]
  rw [rieszProjection, circleIntegral.integral_congr hr hpt,
    circleIntegral.integral_add hci1 hci2, hzero, zero_add,
    Algebra.mul_smul_comm, circleIntegral_mul_left hci3]

/-- The range of the Riesz projection lies in the range of the element when the contour avoids the
origin. -/
theorem range_rieszProjection_le_range {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ T) (h0 : (0 : ℂ) ∉ closedBall c r) :
    LinearMap.range ((rieszProjection T c r : H →L[ℂ] H) : H →ₗ[ℂ] H)
      ≤ LinearMap.range (T : H →ₗ[ℂ] H) := by
  rintro x ⟨w, rfl⟩
  rw [rieszProjection_eq_mul T hr h h0]
  exact ⟨_, rfl⟩

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- Finite-dimensionality of the range transfers between nearby idempotents. -/
theorem finiteDimensional_range_of_norm_sub_lt_one {p q : H →L[ℂ] H}
    (hp : p * p = p) (hq : q * q = q) (h : ‖p - q‖ < 1)
    (hfin : FiniteDimensional ℂ (LinearMap.range (p : H →ₗ[ℂ] H))) :
    FiniteDimensional ℂ (LinearMap.range (q : H →ₗ[ℂ] H)) := by
  haveI := hfin
  obtain ⟨u, hu⟩ := exists_unit_conj_of_norm_sub_lt_one hp hq h
  have hinv : ∀ x : H, (↑u⁻¹ : H →L[ℂ] H) ((u : H →L[ℂ] H) x) = x := fun x => by
    have h1 := congrArg (fun f : H →L[ℂ] H => f x) u.inv_mul
    simp only [mul_apply_eq_comp, one_apply_eq_self] at h1
    exact h1
  have hinj : Function.Injective ((u : H →L[ℂ] H) : H →ₗ[ℂ] H) :=
    Function.LeftInverse.injective hinv
  rw [range_eq_map_of_conj hu]
  exact (Submodule.equivMapOfInjective _ hinj _).finiteDimensional

/-- **The rank of the Riesz projection is locally constant in the element.** -/
theorem exists_eps_finrank_range_rieszProjection_eq (T : H →L[ℂ] H) {c : ℂ} {r R : ℝ}
    (h0 : 0 < r) (hrR : r < R)
    (hT : ∀ lam ∈ closedBall c R \ ball c r, lam ∈ resolventSet ℂ T) :
    ∃ eps > 0, ∀ S : H →L[ℂ] H, ‖S - T‖ < eps →
      (∀ lam ∈ closedBall c R \ ball c r, lam ∈ resolventSet ℂ S) ∧
      Module.finrank ℂ (LinearMap.range ((rieszProjection T c r : H →L[ℂ] H) : H →ₗ[ℂ] H))
        = Module.finrank ℂ (LinearMap.range ((rieszProjection S c r : H →L[ℂ] H) : H →ₗ[ℂ] H)) ∧
      (FiniteDimensional ℂ (LinearMap.range ((rieszProjection S c r : H →L[ℂ] H) : H →ₗ[ℂ] H)) →
        FiniteDimensional ℂ (LinearMap.range ((rieszProjection T c r : H →L[ℂ] H) : H →ₗ[ℂ] H))) := by
  have hcpt : IsCompact (closedBall c R \ ball c r) :=
    (isCompact_closedBall c R).diff isOpen_ball
  obtain ⟨M, hM0, hM⟩ := exists_norm_resolvent_le_on_compact T hcpt hT
  have hsph : sphere c r ⊆ closedBall c R \ ball c r := by
    intro lam hlam
    have hd : dist lam c = r := hlam
    exact ⟨by rw [mem_closedBall, hd]; linarith, by intro hb; rw [mem_ball, hd] at hb; linarith⟩
  refine ⟨min (1 / (2 * M)) (1 / (r * (2 * M ^ (2 : ℕ)) + 1)), by positivity, fun S hS => ?_⟩
  have hSlt1 : ‖S - T‖ < 1 / (2 * M) := lt_of_lt_of_le hS (min_le_left _ _)
  have hSlt2 : ‖S - T‖ < 1 / (r * (2 * M ^ (2 : ℕ)) + 1) := lt_of_lt_of_le hS (min_le_right _ _)
  have hpos : (0 : ℝ) < r * (2 * M ^ (2 : ℕ)) + 1 := by positivity
  have hab : 2 * ‖S - T‖ * M ≤ 1 := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * M)] at hSlt1
    nlinarith
  have hres : ∀ lam ∈ closedBall c R \ ball c r, lam ∈ resolventSet ℂ S :=
    forall_mem_resolventSet_of_norm_sub_le hT hM hab
  have hlt : ‖rieszProjection S c r - rieszProjection T c r‖ < 1 := by
    have hbd := norm_rieszProjection_sub_le T S h0.le (fun lam hlam => hT lam (hsph hlam))
      (fun lam hlam => hM lam (hsph hlam)) hab
    have hkey : r * (2 * M ^ (2 : ℕ) * ‖S - T‖) < 1 := by
      rw [lt_div_iff₀ hpos] at hSlt2
      nlinarith [norm_nonneg (S - T), h0.le, sq_nonneg M]
    linarith
  have hPT : rieszProjection T c r * rieszProjection T c r = rieszProjection T c r :=
    rieszProjection_mul_self T h0 hrR hT
  have hPS : rieszProjection S c r * rieszProjection S c r = rieszProjection S c r :=
    rieszProjection_mul_self S h0 hrR hres
  exact ⟨hres, finrank_range_eq_of_norm_sub_lt_one hPS hPT hlt,
    fun hfin => finiteDimensional_range_of_norm_sub_lt_one hPS hPT hlt hfin⟩

end GaloisForLFunctions.HTGeometry
