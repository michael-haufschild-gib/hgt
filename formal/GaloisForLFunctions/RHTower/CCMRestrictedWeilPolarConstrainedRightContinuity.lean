import GaloisForLFunctions.RHTower.SuzukiGroundEnergyContinuity

/-!
# Right continuity of the polar-constrained Rayleigh floor of the restricted Weil form

The literature's positivity of the Weil form at the aperture `√2` (Connes–Consani, Yoshida) holds
on the subspace of test functions whose two pole coefficients vanish, where the indefinite polar
term of the exact CCM source form drops out.  This file carries the corpus's right-aperture
continuity argument for the ground energy (Suzuki 2026, Theorem 1.3, `SuzukiGroundEnergyContinuity`)
through those two constraints.

* `IsPolarConstrained a u`: both pole coefficients of the form-domain vector `u` vanish.
* Constraints are invariant under aperture extension and scaling.
* A Rayleigh floor on constrained vectors is antitone in the aperture.
* **Right continuity of the constrained floor.**  If `m ‖u‖² ≤ Q(u)` for every constrained `u` at
  the aperture `a`, then for every `ε > 0` the floor `m − ε` holds on constrained vectors at every
  aperture in `[a, a + δ]` for some `δ > 0`.  The proof normalizes a sequence of constrained
  counterexamples at apertures decreasing to `a`, extends them to one fixed aperture, uses
  compactness of the form embedding to extract a physical limit, the no-boundary-escape theorem to
  place it in the aperture `a`, continuity of the pole coefficients to keep it constrained, and the
  closed sublevel sets of the form to bound its energy, contradicting the floor at `a`.
* **Consequence.**  A strictly positive constrained floor at `a` persists on `[a, a + δ]`; in
  particular strict positivity of the constrained form at a prime threshold propagates past it,
  the new prime term included.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct

namespace RHTower

/-- Both pole coefficients of the form-domain vector vanish. -/
def IsPolarConstrained (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : Prop :=
  inner ℂ (ccmPolarApertureVector a (1 / 2)) (ccmArchimedeanFormToAperture a u) = 0 ∧
  inner ℂ (ccmPolarApertureVector a (-1 / 2)) (ccmArchimedeanFormToAperture a u) = 0

/-- The constraints are invariant under aperture extension. -/
theorem isPolarConstrained_iff_of_val_eq {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b} (hvu : v.1 = u.1) :
    IsPolarConstrained b v ↔ IsPolarConstrained a u := by
  unfold IsPolarConstrained
  rw [inner_ccmPolarApertureVector_eq_of_val_eq hab (1 / 2) hvu,
    inner_ccmPolarApertureVector_eq_of_val_eq hab (-1 / 2) hvu]

/-- The constraints are invariant under scaling. -/
theorem IsPolarConstrained.smul {a : SuzukiPositiveAperture} {u : CCMArchimedeanFormDomain a}
    (h : IsPolarConstrained a u) (c : ℂ) : IsPolarConstrained a (c • u) := by
  unfold IsPolarConstrained at h ⊢
  rw [map_smul]
  have key : ∀ p : suzukiApertureHilbert a, ∀ x : suzukiApertureHilbert a,
      inner ℂ p (c • x) = c * inner ℂ p x := by
    intro p x
    rw [Submodule.coe_inner, Submodule.coe_inner, Submodule.coe_smul, inner_smul_right]
  rw [key, key, h.1, h.2, mul_zero]
  exact ⟨rfl, rfl⟩

/-- **A constrained Rayleigh floor is antitone in the aperture.** -/
theorem polarConstrained_floor_of_le {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) {m : ℝ}
    (hb : ∀ v : CCMArchimedeanFormDomain b, IsPolarConstrained b v →
      m * ‖ccmArchimedeanFormToAperture b v‖ ^ (2 : ℕ) ≤ ccmRestrictedWeilSourceQuadratic b v)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u) :
    m * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) ≤ ccmRestrictedWeilSourceQuadratic a u := by
  obtain ⟨v, hvu⟩ := exists_ccmArchimedeanFormDomain_extension hab u
  have hv : IsPolarConstrained b v := (isPolarConstrained_iff_of_val_eq hab hvu).mpr hu
  have h := hb v hv
  rw [norm_ccmArchimedeanFormToAperture_eq_of_val_eq hvu,
    ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab hvu] at h
  exact h

theorem ccmRestrictedWeilSourceQuadratic_zero (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a (0 : CCMArchimedeanFormDomain a) = 0 := by
  have h := ccmRestrictedWeilSourceQuadratic_smul a 0 (0 : CCMArchimedeanFormDomain a)
  rw [zero_smul] at h
  simpa using h

/-- **Right continuity of the constrained floor along the canonical right apertures.** -/
theorem exists_polarConstrained_floor_suzukiRightAperture (a : SuzukiPositiveAperture) {m : ℝ}
    (hm : ∀ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u →
      m * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) ≤ ccmRestrictedWeilSourceQuadratic a u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∀ v : CCMArchimedeanFormDomain (suzukiRightAperture a k),
      IsPolarConstrained (suzukiRightAperture a k) v →
        (m - ε) * ‖ccmArchimedeanFormToAperture (suzukiRightAperture a k) v‖ ^ (2 : ℕ) ≤
          ccmRestrictedWeilSourceQuadratic (suzukiRightAperture a k) v := by
  by_contra hnone
  push Not at hnone
  choose v hvc hvQ using hnone
  let b := suzukiRightAperture a 0
  have hab : a.1 ≤ b.1 := (suzukiRightAperture_gt a 0).le
  have hkb : ∀ k, (suzukiRightAperture a k).1 ≤ b.1 := fun k =>
    Subtype.coe_le_coe.mpr (antitone_suzukiRightAperture a (Nat.zero_le k))
  -- the counterexamples are nonzero
  have hr : ∀ k, 0 < ‖ccmArchimedeanFormToAperture (suzukiRightAperture a k) (v k)‖ := by
    intro k
    rcases (norm_nonneg (ccmArchimedeanFormToAperture (suzukiRightAperture a k) (v k))).lt_or_eq
      with h | h
    · exact h
    · exfalso
      have h0 : ccmArchimedeanFormToAperture (suzukiRightAperture a k) (v k) = 0 :=
        norm_eq_zero.mp h.symm
      have hv0 : v k = 0 :=
        ccmArchimedeanFormToAperture_injective _ (by rw [h0, map_zero])
      have := hvQ k
      rw [hv0, ccmRestrictedWeilSourceQuadratic_zero, map_zero, norm_zero] at this
      simp at this
  -- normalized counterexamples
  let w : ∀ k, CCMArchimedeanFormDomain (suzukiRightAperture a k) := fun k =>
    ((‖ccmArchimedeanFormToAperture (suzukiRightAperture a k) (v k)‖ : ℂ)⁻¹) • v k
  have hwnorm : ∀ k, ‖ccmArchimedeanFormToAperture (suzukiRightAperture a k) (w k)‖ = 1 := by
    intro k
    show ‖ccmArchimedeanFormToAperture (suzukiRightAperture a k)
      (((‖ccmArchimedeanFormToAperture (suzukiRightAperture a k) (v k)‖ : ℂ)⁻¹) • v k)‖ = 1
    rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr k)]
    exact inv_mul_cancel₀ (hr k).ne'
  have hwQ : ∀ k, ccmRestrictedWeilSourceQuadratic (suzukiRightAperture a k) (w k) < m - ε := by
    intro k
    show ccmRestrictedWeilSourceQuadratic (suzukiRightAperture a k)
      (((‖ccmArchimedeanFormToAperture (suzukiRightAperture a k) (v k)‖ : ℂ)⁻¹) • v k) < m - ε
    rw [ccmRestrictedWeilSourceQuadratic_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hr k), inv_pow]
    have hk := hvQ k
    have hrpos : 0 < ‖ccmArchimedeanFormToAperture (suzukiRightAperture a k) (v k)‖ ^ (2 : ℕ) :=
      pow_pos (hr k) 2
    rw [inv_mul_lt_iff₀ hrpos]
    linarith
  have hwc : ∀ k, IsPolarConstrained (suzukiRightAperture a k) (w k) := fun k =>
    (hvc k).smul _
  -- extension to the fixed aperture `b`
  have hext : ∀ k, ∃ e : CCMArchimedeanFormDomain b, e.1 = (w k).1 := fun k =>
    exists_ccmArchimedeanFormDomain_extension (hkb k) (w k)
  choose e he using hext
  have heQ : ∀ k, ccmRestrictedWeilSourceQuadratic b (e k) < m - ε := by
    intro k
    rw [ccmRestrictedWeilSourceQuadratic_eq_of_val_eq (hkb k) (he k)]
    exact hwQ k
  have henorm : ∀ k, ‖ccmArchimedeanFormToAperture b (e k)‖ = 1 := by
    intro k
    rw [norm_ccmArchimedeanFormToAperture_eq_of_val_eq (he k)]
    exact hwnorm k
  have hec : ∀ k, IsPolarConstrained b (e k) := fun k =>
    (isPolarConstrained_iff_of_val_eq (hkb k) (he k)).mpr (hwc k)
  -- bounded form norm
  let radius := Real.sqrt (max 0 (m - ε + ‖ccmRestrictedWeilBoundedRemainder b‖))
  have hebound : ∀ k, ‖e k‖ ≤ radius := by
    intro k
    have hb := ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass b (e k)
    rw [henorm k] at hb
    simp only [one_pow, mul_one] at hb
    have hsq : ‖(e k).1‖ ^ (2 : ℕ) ≤ max 0 (m - ε + ‖ccmRestrictedWeilBoundedRemainder b‖) :=
      hb.trans (le_max_of_le_right (by linarith [heQ k]))
    have hnonneg : 0 ≤ max 0 (m - ε + ‖ccmRestrictedWeilBoundedRemainder b‖) := le_max_left _ _
    have hsqrt : 0 ≤ radius := Real.sqrt_nonneg _
    change ‖(e k).1‖ ≤ radius
    nlinarith [Real.sq_sqrt hnonneg, norm_nonneg (e k).1, hsqrt]
  -- compactness
  have hmem : ∀ k, ccmArchimedeanFormToAperture b (e k) ∈
      closure (ccmArchimedeanFormToAperture b '' Metric.closedBall
        (0 : CCMArchimedeanFormDomain b) radius) := by
    intro k
    apply subset_closure
    refine ⟨e k, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hebound k
  obtain ⟨fstar, -, phi, hphi, hconv⟩ :=
    (isCompactOperator_ccmArchimedeanFormToAperture b
      |>.isCompact_closure_image_closedBall radius).tendsto_subseq hmem
  -- no boundary escape
  have hconvGlobal : Tendsto
      (fun n => (ccmArchimedeanFormToAperture b (e (phi n)) : SoninL2)) atTop
      (nhds (fstar : SoninL2)) :=
    (continuous_subtype_val.tendsto fstar).comp hconv
  have hsupport : indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
      (fstar : SoninL2) = (fstar : SoninL2) := by
    apply indicatorCutoff_limit_suzukiRightAperture a phi hphi.tendsto_atTop _ _ _ hconvGlobal
    intro n
    rw [ccmArchimedeanFormToAperture_coe_eq_of_val_eq (he (phi n))]
    exact indicatorCutoff_suzukiApertureHilbert (suzukiRightAperture a (phi n))
      (ccmArchimedeanFormToAperture (suzukiRightAperture a (phi n)) (w (phi n)))
  -- unit norm of the limit
  have hnorm : ‖fstar‖ = 1 := by
    have h1 : Tendsto (fun n => ‖ccmArchimedeanFormToAperture b (e (phi n))‖) atTop
        (nhds ‖fstar‖) := (continuous_norm.tendsto fstar).comp hconv
    have h2 : Tendsto (fun n => ‖ccmArchimedeanFormToAperture b (e (phi n))‖) atTop
        (nhds 1) := by
      simp only [henorm]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- the limit lies in the closed sublevel set
  have hsub : ∀ n, ccmArchimedeanFormToAperture b (e (phi n)) ∈
      {f : suzukiApertureHilbert b | ∃ u : CCMArchimedeanFormDomain b,
        ccmArchimedeanFormToAperture b u = f ∧
          ccmRestrictedWeilSourceQuadratic b u ≤ m - ε} := fun n =>
    ⟨e (phi n), rfl, (heQ (phi n)).le⟩
  obtain ⟨w', hw'J, hw'Q⟩ :=
    (isClosed_ccmRestrictedWeilSource_sublevel b (m - ε)).mem_of_tendsto hconv
      (Eventually.of_forall hsub)
  -- the limit is constrained
  have hlimc : ∀ s : ℝ, (∀ k, inner ℂ (ccmPolarApertureVector b s)
      (ccmArchimedeanFormToAperture b (e k)) = 0) →
      inner ℂ (ccmPolarApertureVector b s) fstar = 0 := by
    intro s hs
    have h1 : Tendsto (fun n => inner ℂ (ccmPolarApertureVector b s)
        (ccmArchimedeanFormToAperture b (e (phi n)))) atTop
        (nhds (inner ℂ (ccmPolarApertureVector b s) fstar)) :=
      (continuous_const.inner continuous_id).tendsto fstar |>.comp hconv
    have h2 : Tendsto (fun n => inner ℂ (ccmPolarApertureVector b s)
        (ccmArchimedeanFormToAperture b (e (phi n)))) atTop (nhds 0) := by
      simp only [hs]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hfc1 : inner ℂ (ccmPolarApertureVector b (1 / 2)) fstar = 0 :=
    hlimc _ fun k => (hec k).1
  have hfc2 : inner ℂ (ccmPolarApertureVector b (-1 / 2)) fstar = 0 :=
    hlimc _ fun k => (hec k).2
  -- transfer to the aperture `a`
  obtain ⟨u, huw, huJ⟩ :=
    exists_ccmArchimedeanFormDomain_of_limit_support a b w' fstar hw'J hsupport
  have hnormu : ‖ccmArchimedeanFormToAperture a u‖ = 1 := by
    have hnormeq := norm_ccmArchimedeanFormToAperture_eq_of_val_eq huw.symm
    rw [hw'J, hnorm] at hnormeq
    exact hnormeq.symm
  have hsource : ccmRestrictedWeilSourceQuadratic a u =
      ccmRestrictedWeilSourceQuadratic b w' :=
    (ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab huw.symm).symm
  have huc : IsPolarConstrained a u := by
    have h := (isPolarConstrained_iff_of_val_eq hab huw.symm).mp
    apply h
    unfold IsPolarConstrained
    rw [hw'J]
    exact ⟨hfc1, hfc2⟩
  have hfloor := hm u huc
  rw [hnormu, one_pow, mul_one, hsource] at hfloor
  linarith

/-- **Right continuity of the constrained floor on an aperture interval.** -/
theorem exists_polarConstrained_floor_right (a : SuzukiPositiveAperture) {m : ℝ}
    (hm : ∀ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u →
      m * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) ≤ ccmRestrictedWeilSourceQuadratic a u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : SuzukiPositiveAperture, c.1 ≤ a.1 + δ →
      ∀ v : CCMArchimedeanFormDomain c, IsPolarConstrained c v →
        (m - ε) * ‖ccmArchimedeanFormToAperture c v‖ ^ (2 : ℕ) ≤
          ccmRestrictedWeilSourceQuadratic c v := by
  obtain ⟨k, hk⟩ := exists_polarConstrained_floor_suzukiRightAperture a hm hε
  refine ⟨1 / (k + 1 : ℝ), by positivity, fun c hc v hv => ?_⟩
  have hck : c.1 ≤ (suzukiRightAperture a k).1 := by
    rw [suzukiRightAperture_coe]
    exact hc
  exact polarConstrained_floor_of_le hck hk v hv

/-- **Strict constrained positivity propagates past the aperture.**  If the constrained form is
coercive at `a`, it stays coercive on every aperture up to `a + δ`, the terms of newly entering
prime powers included. -/
theorem exists_polarConstrained_pos_floor_right (a : SuzukiPositiveAperture) {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u →
      m * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) ≤ ccmRestrictedWeilSourceQuadratic a u) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : SuzukiPositiveAperture, c.1 ≤ a.1 + δ →
      ∀ v : CCMArchimedeanFormDomain c, IsPolarConstrained c v →
        (m / 2) * ‖ccmArchimedeanFormToAperture c v‖ ^ (2 : ℕ) ≤
          ccmRestrictedWeilSourceQuadratic c v := by
  obtain ⟨δ, hδ, h⟩ := exists_polarConstrained_floor_right a hm (half_pos hm0)
  refine ⟨δ, hδ, fun c hc v hv => ?_⟩
  have := h c hc v hv
  rwa [show m - m / 2 = m / 2 by ring] at this

end RHTower
