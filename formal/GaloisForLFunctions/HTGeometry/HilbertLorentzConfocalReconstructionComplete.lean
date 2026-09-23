import GaloisForLFunctions.HTGeometry.HilbertLorentzConfocalReconstruction

/-!
# Complete Hilbert--Lorentz confocal reconstruction endpoints

This module finishes the clauses of the dimension-free master theorem that are implicit in the
scalar axial projection but were not exposed for general Lorentz sources: the literal causal
contact equation, complete null-radical classification, global field/support/hull faithfulness,
and the sharp stable exterior chart.
-/

namespace HTGeometry

noncomputable section

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The scalar support operator of a Lorentz source along an axis. -/
def lorentzAxialSupportOperator (e : E) (S : Set (E × ℝ)) (R d : ℝ) : ℝ :=
  confocalNullSupportOperator (lorentzAxialProjection e '' S) R d

/-- The radical height of a Lorentz source along an axis.  On a radical axis this is the supremal
height of the source. -/
def lorentzAxialRadicalHeight (e : E) (S : Set (E × ℝ)) : ℝ :=
  confocalRadicalHeight (lorentzAxialProjection e '' S)

/-- The Lorentz axial radical height is literally the supremal source height.  It is independent
of the axis; the axis becomes relevant when the incoming null support vanishes. -/
theorem lorentzAxialRadicalHeight_eq_sSup_height
    (e : E) {S : Set (E × ℝ)} (hne : S.Nonempty) {M : ℝ}
    (hbound : ∀ q ∈ S, q.2 ≤ M) :
    lorentzAxialRadicalHeight e S = sSup ((fun q : E × ℝ => q.2) '' S) := by
  have hbdd : BddAbove ((fun q : E × ℝ => q.2) '' S) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact hbound q hq
  have himage :
      confocalNullFunctional (lambda := 1) '' (lorentzAxialProjection e '' S) =
        (fun x : ℝ => 2 * x) '' ((fun q : E × ℝ => q.2) '' S) := by
    ext x
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨q.2, ⟨q, hq, rfl⟩, ?_⟩
      simp [confocalNullFunctional, confocalNullMinus, confocalNullPlus,
        lorentzAxialProjection]
      ring
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨lorentzAxialProjection e q, ⟨q, hq, rfl⟩, ?_⟩
      simp [confocalNullFunctional, confocalNullMinus, confocalNullPlus,
        lorentzAxialProjection]
      ring
  have hscaled : IsLUB
      ((fun x : ℝ => 2 * x) '' ((fun q : E × ℝ => q.2) '' S))
      (2 * sSup ((fun q : E × ℝ => q.2) '' S)) :=
    IsLUB.mul_left (by norm_num : (0 : ℝ) ≤ 2)
      (isLUB_csSup (hne.image _) hbdd)
  have hsupport : confocalNullSupport (lorentzAxialProjection e '' S) 1 =
      2 * sSup ((fun q : E × ℝ => q.2) '' S) := by
    rw [confocalNullSupport, himage]
    exact hscaled.csSup_eq ((hne.image _).image _)
  rw [lorentzAxialRadicalHeight, confocalRadicalHeight, hsupport]
  ring

/-- Envelope and defect differ by exactly the observation radius. -/
theorem lorentzAxialEnvelope_eq_radius_add_defect
    (e : E) (S : Set (E × ℝ)) (R : ℝ) :
    lorentzAxialEnvelope e S R = R + lorentzAxialDefect e S R := by
  rw [lorentzAxialEnvelope, lorentzAxialDefect, confocalGlobalDefect]
  ring

private theorem lorentz_projection_data
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} {M : ℝ}
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    lorentzAxialProjection e '' S ⊆ confocalLorentzCone ∧
      ∀ p ∈ lorentzAxialProjection e '' S, p.2 ≤ M := by
  constructor
  · rintro _ ⟨q, hq, rfl⟩
    exact lorentzAxialProjection_mem_confocalLorentzCone he (hScone q hq)
  · rintro _ ⟨q, hq, rfl⟩
    exact hbound q hq

/-- A causal contact level above the observation radius is exactly a fixed point of the axial
support operator. -/
theorem causalContact_eq_iff_lorentzAxialSupportOperator_fixedPoint
    {e : E} {S : Set (E × ℝ)} (hne : S.Nonempty) {M R g : ℝ}
    (hR : 0 < R) (hgR : R ≤ g)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    causalSupport S ((-R) • e) g = (g ^ (2 : ℕ) - R ^ (2 : ℕ)) / 2 ↔
      g - R = lorentzAxialSupportOperator e S R (g - R) := by
  have hd0 : 0 ≤ g - R := sub_nonneg.mpr hgR
  have hden : 0 < 2 * R + (g - R) := by linarith
  have hc : 0 < (g + R) / 2 := by linarith
  have hlambda0 : 0 ≤ confocalProjectiveParameter R (g - R) :=
    confocalProjectiveParameter_nonneg hR hd0
  have hzscale :
      ((g + R) / 2) •
          (-(1 - confocalProjectiveParameter R (g - R)) • e) =
        (-R) • e := by
    rw [smul_smul]
    congr 1
    rw [confocalProjectiveParameter]
    field_simp [hden.ne']
    ring
  have htscale :
      ((g + R) / 2) * (1 + confocalProjectiveParameter R (g - R)) = g := by
    rw [confocalProjectiveParameter]
    field_simp [hden.ne']
    ring
  have hscale := causalSupport_smul_of_pos hne hScone hbound
    (z := -(1 - confocalProjectiveParameter R (g - R)) • e)
    (t := 1 + confocalProjectiveParameter R (g - R))
    (by linarith) hc
  rw [hzscale, htscale,
    ← lorentzAxialSupport_eq_causalSupport e S
      (confocalProjectiveParameter R (g - R))] at hscale
  have hquadratic : (g ^ (2 : ℕ) - R ^ (2 : ℕ)) / 2 = ((g + R) / 2) * (g - R) := by
    ring
  rw [hscale, hquadratic, lorentzAxialSupportOperator,
    confocalNullSupportOperator, lorentzAxialSupport]
  constructor <;> intro h <;> nlinarith

/-- Exact causal-contact selection: the confocal envelope is the greatest contact level above the
observation radius. -/
theorem lorentzAxialEnvelope_isGreatest_causalContact
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    R ≤ lorentzAxialEnvelope e S R ∧
      causalSupport S ((-R) • e) (lorentzAxialEnvelope e S R) =
        (lorentzAxialEnvelope e S R ^ (2 : ℕ) - R ^ (2 : ℕ)) / 2 ∧
      ∀ g : ℝ, R ≤ g →
        causalSupport S ((-R) • e) g = (g ^ (2 : ℕ) - R ^ (2 : ℕ)) / 2 →
          g ≤ lorentzAxialEnvelope e S R := by
  have hgreat := lorentzAxialDefect_isGreatest_fixedPoint
    he hne hM hR hScone hbound
  have henv := lorentzAxialEnvelope_eq_radius_add_defect e S R
  have henvR : R ≤ lorentzAxialEnvelope e S R := by
    rw [henv]
    linarith [hgreat.1]
  have hdiff : lorentzAxialEnvelope e S R - R = lorentzAxialDefect e S R := by
    rw [henv]
    ring
  refine ⟨henvR, ?_, ?_⟩
  · apply (causalContact_eq_iff_lorentzAxialSupportOperator_fixedPoint
      hne hR henvR hScone hbound).2
    rw [hdiff, lorentzAxialSupportOperator]
    exact hgreat.2.1
  · intro g hgR hcontact
    have hfixed :=
      (causalContact_eq_iff_lorentzAxialSupportOperator_fixedPoint
        hne hR hgR hScone hbound).1 hcontact
    have hle := hgreat.2.2 (g - R) (sub_nonneg.mpr hgR) (by
      rw [lorentzAxialSupportOperator] at hfixed
      exact hfixed)
    rw [henv]
    linarith

/-- There is at most one causal-contact solution strictly above the radius. -/
theorem causalContact_above_radius_unique
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M R g k : ℝ}
    (hR : 0 < R)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hg : R < g) (hk : R < k)
    (hgcontact : causalSupport S ((-R) • e) g = (g ^ (2 : ℕ) - R ^ (2 : ℕ)) / 2)
    (hkcontact : causalSupport S ((-R) • e) k = (k ^ (2 : ℕ) - R ^ (2 : ℕ)) / 2) :
    g = k := by
  obtain ⟨hcone, hbnd⟩ := lorentz_projection_data he hScone hbound
  have hfixedG :=
    (causalContact_eq_iff_lorentzAxialSupportOperator_fixedPoint
      hne hR hg.le hScone hbound).1 hgcontact
  have hfixedK :=
    (causalContact_eq_iff_lorentzAxialSupportOperator_fixedPoint
      hne hR hk.le hScone hbound).1 hkcontact
  have heq := confocalNullSupport_positive_fixedPoint_unique_global
    (hne.image _) hR hcone hbnd (sub_pos.mpr hg) (sub_pos.mpr hk)
    (by simpa [lorentzAxialSupportOperator] using hfixedG)
    (by simpa [lorentzAxialSupportOperator] using hfixedK)
  linarith

/-- The general Lorentz support operator has the sharp scalar contraction modulus `M / R`. -/
theorem lorentzAxialSupportOperator_contraction
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty)
    {M R d f : ℝ} (hM : 0 ≤ M) (hR : 0 < R)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hd : 0 ≤ d) (hf : 0 ≤ f) :
    |lorentzAxialSupportOperator e S R d - lorentzAxialSupportOperator e S R f| ≤
      (M / R) * |d - f| := by
  obtain ⟨hcone, hbnd⟩ := lorentz_projection_data he hScone hbound
  exact confocalNullSupportOperator_contraction (hne.image _) hM hR hcone hbnd hd hf

/-- Every proposed nonnegative contraction modulus below `M / R` fails already on the singleton
null source `{(M e,M)}`. -/
theorem lorentzAxialSupportOperator_contraction_modulus_optimal
    {e : E} (he : ‖e‖ = 1) {M R c : ℝ} (hM : 0 < M) (hRM : M < R)
    (hc0 : 0 ≤ c) (hc : c < M / R) :
    ∃ d f : ℝ, 0 ≤ d ∧ 0 ≤ f ∧
      c * |d - f| <
        |lorentzAxialSupportOperator e ({(M • e, M)} : Set (E × ℝ)) R d -
          lorentzAxialSupportOperator e ({(M • e, M)} : Set (E × ℝ)) R f| := by
  have himage : lorentzAxialProjection e '' ({(M • e, M)} : Set (E × ℝ)) =
      ({(M, M)} : Set (ℝ × ℝ)) := by
    ext p
    simp only [Set.image_singleton, Set.mem_singleton_iff]
    rw [lorentzAxialProjection]
    simp [real_inner_smul_right, he]
  simpa [lorentzAxialSupportOperator, himage] using
    (confocalNullSupportOperator_contraction_modulus_optimal hM hRM hc0 hc)

/-- Exterior Lorentz defects depend Lipschitz-continuously on their complete axial support fields,
with the exact factor `(1-M/R)⁻¹`. -/
theorem lorentzAxialDefect_stability
    {e : E} (he : ‖e‖ = 1) {S T : Set (E × ℝ)}
    (hSne : S.Nonempty) (hTne : T.Nonempty) {M R epsilon : ℝ}
    (hM : 0 ≤ M) (hRM : M < R)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hTcone : ∀ q ∈ T, ‖q.1‖ ≤ q.2)
    (hSbound : ∀ q ∈ S, q.2 ≤ M) (hTbound : ∀ q ∈ T, q.2 ≤ M)
    (hsupport : ∀ lambda, 0 ≤ lambda → lambda ≤ 1 →
      |lorentzAxialSupport e S lambda - lorentzAxialSupport e T lambda| ≤ epsilon) :
    |lorentzAxialDefect e S R - lorentzAxialDefect e T R| ≤
      epsilon / (1 - M / R) := by
  obtain ⟨hScone', hSbound'⟩ := lorentz_projection_data he hScone hSbound
  obtain ⟨hTcone', hTbound'⟩ := lorentz_projection_data he hTcone hTbound
  have hG := isLUB_confocalGlobalEnvelope (hSne.image _) hM (hM.trans_lt hRM)
    hScone' hSbound'
  have hH := isLUB_confocalGlobalEnvelope (hTne.image _) hM (hM.trans_lt hRM)
    hTcone' hTbound'
  simpa [lorentzAxialDefect, lorentzAxialEnvelope, confocalGlobalDefect,
    lorentzAxialSupport] using
    (confocalEnvelopeDefect_stability (hSne.image _) (hTne.image _) hM hRM
      hScone' hTcone' hSbound' hTbound' hG hH hsupport)

/-- Vanishing axial support is exactly concentration of the source on the corresponding positive
Lorentz null ray. -/
theorem lorentzAxialSupport_zero_iff_positiveNullRay
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M : ℝ}
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    lorentzAxialSupport e S 0 = 0 ↔
      ∀ q ∈ S, q.1 = q.2 • e := by
  obtain ⟨hcone, hbnd⟩ := lorentz_projection_data he hScone hbound
  rw [lorentzAxialSupport,
    confocalNullSupport_zero_iff_positiveNullRay_global (hne.image _) hcone hbnd]
  constructor
  · intro h q hq
    have hinner : inner ℝ e q.1 = q.2 := (h _ ⟨q, hq, rfl⟩).symm
    have hq2 : 0 ≤ q.2 := le_trans (norm_nonneg _) (hScone q hq)
    have hnorm : ‖q.1‖ = q.2 := by
      apply le_antisymm (hScone q hq)
      calc
        q.2 = inner ℝ e q.1 := hinner.symm
        _ ≤ ‖e‖ * ‖q.1‖ := real_inner_le_norm e q.1
        _ = ‖q.1‖ := by rw [he, one_mul]
    have hsquare : ‖q.1 - q.2 • e‖ ^ (2 : ℕ) = 0 := by
      rw [norm_sub_sq_real, hnorm, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hq2, he, mul_one, real_inner_smul_right,
        real_inner_comm e q.1, hinner]
      ring
    have hnormzero : ‖q.1 - q.2 • e‖ = 0 := by
      nlinarith [norm_nonneg (q.1 - q.2 • e)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
  · intro h p hp
    rcases hp with ⟨q, hq, rfl⟩
    rw [lorentzAxialProjection, h q hq, real_inner_smul_right]
    simp [he]

/-- Literal causal-support version of the radical classification. -/
theorem causalSupport_neg_axis_eq_zero_iff_positiveNullRay
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M : ℝ}
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    causalSupport S (-e) 1 = 0 ↔ ∀ q ∈ S, q.1 = q.2 • e := by
  have haxis : lorentzAxialSupport e S 0 = causalSupport S (-e) 1 := by
    simpa using lorentzAxialSupport_eq_causalSupport e S 0
  rw [← haxis]
  exact lorentzAxialSupport_zero_iff_positiveNullRay he hne hScone hbound

/-- Complete three-way null-radical equivalence in the literal global causal-support notation. -/
theorem lorentzAxial_nullRadical_equiv
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M : ℝ}
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    (causalSupport S (-e) 1 = 0 ↔ lorentzAxialSupport e S 0 = 0) ∧
      (lorentzAxialSupport e S 0 = 0 ↔ ∀ q ∈ S, q.1 = q.2 • e) := by
  constructor
  · have haxis : lorentzAxialSupport e S 0 = causalSupport S (-e) 1 := by
      simpa using lorentzAxialSupport_eq_causalSupport e S 0
    rw [haxis]
  · exact lorentzAxialSupport_zero_iff_positiveNullRay he hne hScone hbound

/-- On a radical axis the entire normalized support slice is exactly linear. -/
theorem lorentzAxialSupport_eq_two_mul_radicalHeight_mul
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M lambda : ℝ}
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hradical : lorentzAxialSupport e S 0 = 0)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    lorentzAxialSupport e S lambda =
      2 * lorentzAxialRadicalHeight e S * lambda := by
  obtain ⟨hcone, hbnd⟩ := lorentz_projection_data he hScone hbound
  exact confocalNullSupport_eq_two_mul_radicalHeight_mul
    (hne.image _) hcone hbnd hradical hlambda0 hlambda1

/-- Every positive fixed point on a radical axis is the explicit second fold branch. -/
theorem lorentzPositiveFixedPoint_eq_two_mul_radicalHeight_sub
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M R d : ℝ}
    (hR : 0 < R)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hradical : lorentzAxialSupport e S 0 = 0)
    (hd0 : 0 < d) (hd : d = lorentzAxialSupportOperator e S R d) :
    d = 2 * (lorentzAxialRadicalHeight e S - R) := by
  obtain ⟨hcone, hbnd⟩ := lorentz_projection_data he hScone hbound
  simpa [lorentzAxialSupportOperator, lorentzAxialRadicalHeight,
    lorentzAxialSupport] using
    (confocalPositiveFixedPoint_eq_two_mul_radicalHeight_sub
      (hne.image _) hR hcone hbnd hradical hd0 hd)

/-- Exact finite-radius fold law on a radical axis. -/
theorem lorentzAxialDefect_eq_two_mul_max_radicalHeight_sub
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hradical : lorentzAxialSupport e S 0 = 0) :
    lorentzAxialDefect e S R =
      2 * max (lorentzAxialRadicalHeight e S - R) 0 := by
  obtain ⟨hcone, hbnd⟩ := lorentz_projection_data he hScone hbound
  exact confocalGlobalDefect_eq_two_mul_max_radicalHeight_sub
    (hne.image _) hM hR hcone hbnd hradical

/-- Exact envelope fold law on a radical axis. -/
theorem lorentzAxialEnvelope_eq_radius_add_two_mul_max_radicalHeight_sub
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hradical : lorentzAxialSupport e S 0 = 0) :
    lorentzAxialEnvelope e S R =
      R + 2 * max (lorentzAxialRadicalHeight e S - R) 0 := by
  rw [lorentzAxialEnvelope_eq_radius_add_defect,
    lorentzAxialDefect_eq_two_mul_max_radicalHeight_sub
      he hne hM hR hScone hbound hradical]

/-- Complete causal-contact root classification on a radical axis: the diagonal root is always
present, while the second branch exists exactly below the radical height. -/
theorem causalContact_radical_iff
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M R g : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R) (hgR : R ≤ g)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hradical : lorentzAxialSupport e S 0 = 0) :
    causalSupport S ((-R) • e) g = (g ^ (2 : ℕ) - R ^ (2 : ℕ)) / 2 ↔
      g = R ∨
        (R < lorentzAxialRadicalHeight e S ∧
          g = 2 * lorentzAxialRadicalHeight e S - R) := by
  constructor
  · intro hcontact
    have hfixed :=
      (causalContact_eq_iff_lorentzAxialSupportOperator_fixedPoint
        hne hR hgR hScone hbound).1 hcontact
    rcases (sub_nonneg.mpr hgR).eq_or_lt with hzero | hpos
    · exact Or.inl (by linarith)
    · have hfold := lorentzPositiveFixedPoint_eq_two_mul_radicalHeight_sub
        he hne hR hScone hbound hradical hpos hfixed
      exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (rfl | ⟨hRheight, rfl⟩)
    · apply (causalContact_eq_iff_lorentzAxialSupportOperator_fixedPoint
        hne hR le_rfl hScone hbound).2
      simpa [lorentzAxialSupportOperator, confocalNullSupportOperator,
        confocalProjectiveParameter, lorentzAxialSupport] using hradical.symm
    · have henv :=
        lorentzAxialEnvelope_eq_radius_add_two_mul_max_radicalHeight_sub
          he hne hM hR hScone hbound hradical
      rw [max_eq_left (by linarith : 0 ≤ lorentzAxialRadicalHeight e S - R)] at henv
      have hcontact :=
        (lorentzAxialEnvelope_isGreatest_causalContact
          he hne hM hR hScone hbound).2.1
      rw [henv] at hcontact
      have hlevel : R + 2 * (lorentzAxialRadicalHeight e S - R) =
          2 * lorentzAxialRadicalHeight e S - R := by ring
      rw [hlevel] at hcontact
      exact hcontact

/-- Off the radical, every positive radius has strictly positive defect. -/
theorem lorentzAxialDefect_pos_of_nonradical
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hnonradical : 0 < lorentzAxialSupport e S 0) :
    0 < lorentzAxialDefect e S R := by
  obtain ⟨hcone, hbnd⟩ := lorentz_projection_data he hScone hbound
  exact confocalGlobalDefect_pos_of_nullSupport_zero_pos
    (hne.image _) hM hR hcone hbnd hnonradical

/-- On every nonradical axis the contact equation has exactly one solution above the diagonal. -/
theorem causalContact_nonradical_existsUnique
    {e : E} (he : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hnonradical : 0 < lorentzAxialSupport e S 0) :
    ∃! g : ℝ, R ≤ g ∧
      causalSupport S ((-R) • e) g = (g ^ (2 : ℕ) - R ^ (2 : ℕ)) / 2 := by
  have hgreat := lorentzAxialEnvelope_isGreatest_causalContact
    he hne hM hR hScone hbound
  have hdefectPos := lorentzAxialDefect_pos_of_nonradical
    he hne hM hR hScone hbound hnonradical
  have henv := lorentzAxialEnvelope_eq_radius_add_defect e S R
  have henvPos : R < lorentzAxialEnvelope e S R := by
    rw [henv]
    linarith
  refine ⟨lorentzAxialEnvelope e S R, ⟨henvPos.le, hgreat.2.1⟩, ?_⟩
  intro g hg
  have hfixed :=
    (causalContact_eq_iff_lorentzAxialSupportOperator_fixedPoint
      hne hR hg.1 hScone hbound).1 hg.2
  have hgPos : R < g := by
    rcases hg.1.eq_or_lt with hEq | hlt
    · have hzero : g - R = 0 := by linarith
      have hsupportZero : lorentzAxialSupport e S 0 = 0 := by
        simpa [hzero, lorentzAxialSupportOperator, confocalNullSupportOperator,
          confocalProjectiveParameter, lorentzAxialSupport] using hfixed.symm
      linarith
    · exact hlt
  exact causalContact_above_radius_unique he hne hR hScone hbound
    hgPos henvPos hg.2 hgreat.2.1

/-- A source containing a nonzero point has at most one radical unit direction. -/
theorem radical_axis_unique_of_contains_nonzero
    {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    {S : Set (E × ℝ)} (hne : S.Nonempty) {M : ℝ}
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hradicalE : lorentzAxialSupport e S 0 = 0)
    (hradicalF : lorentzAxialSupport f S 0 = 0)
    {q : E × ℝ} (hq : q ∈ S) (hq0 : q ≠ (0, 0)) : e = f := by
  have hrayE := (lorentzAxialSupport_zero_iff_positiveNullRay he hne hScone hbound).mp
    hradicalE q hq
  have hrayF := (lorentzAxialSupport_zero_iff_positiveNullRay hf hne hScone hbound).mp
    hradicalF q hq
  have hq2 : 0 < q.2 := by
    have hq2nonneg : 0 ≤ q.2 := le_trans (norm_nonneg _) (hScone q hq)
    refine lt_of_le_of_ne hq2nonneg ?_
    intro hzero
    have hq1zero : q.1 = 0 := norm_eq_zero.mp (le_antisymm
      (by simpa [hzero] using hScone q hq) (norm_nonneg _))
    exact hq0 (Prod.ext hq1zero hzero.symm)
  have hscaled : q.2 • e = q.2 • f := hrayE.symm.trans hrayF
  have := congrArg (fun x : E => q.2⁻¹ • x) hscaled
  simpa [smul_smul, hq2.ne'] using this

/-- The causal support of a source is the support function of its own maximal dual-support hull. -/
theorem causalSupport_eq_sSup_dualSupportHull
    [Nontrivial E] {S : Set (E × ℝ)} (hne : S.Nonempty) {M : ℝ}
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    {z : E} {t : ℝ} (hzt : ‖z‖ ≤ t) :
    causalSupport S z t =
      sSup ((fun q : E × ℝ => inner ℝ z q.1 + t * q.2) ''
        lorentzDualSupportHull S) := by
  have ht : 0 ≤ t := le_trans (norm_nonneg z) hzt
  have hsourceSubset : S ⊆ lorentzDualSupportHull S := by
    intro q hq
    refine ⟨hScone q hq, fun w u hwu => ?_⟩
    exact (isLUB_csSup (hne.image _)
      (bddAbove_causalSupport_image hScone hbound
        (le_trans (norm_nonneg w) hwu))).1 ⟨q, hq, rfl⟩
  have hbdd : BddAbove ((fun q : E × ℝ => inner ℝ z q.1 + t * q.2) ''
      lorentzDualSupportHull S) := by
    refine ⟨causalSupport S z t, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact hq.2 z t hzt
  have hneHull : ((fun q : E × ℝ => inner ℝ z q.1 + t * q.2) ''
      lorentzDualSupportHull S).Nonempty := by
    obtain ⟨q, hq⟩ := hne
    exact ⟨_, ⟨q, hsourceSubset hq, rfl⟩⟩
  apply le_antisymm
  · rw [causalSupport]
    exact csSup_le_csSup hbdd (hne.image _) (Set.image_mono hsourceSubset)
  · apply csSup_le hneHull
    rintro _ ⟨q, hq, rfl⟩
    exact hq.2 z t hzt

/-- Equality of maximal dual-support hulls is equivalent to equality of causal support functions on
the complete dual Lorentz cone. -/
theorem lorentzDualSupportHull_eq_iff_causalSupport_eqOn
    [Nontrivial E] {S T : Set (E × ℝ)} (hSne : S.Nonempty) (hTne : T.Nonempty)
    {MS MT : ℝ}
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hTcone : ∀ q ∈ T, ‖q.1‖ ≤ q.2)
    (hSbound : ∀ q ∈ S, q.2 ≤ MS) (hTbound : ∀ q ∈ T, q.2 ≤ MT) :
    lorentzDualSupportHull S = lorentzDualSupportHull T ↔
      ∀ z : E, ∀ t : ℝ, ‖z‖ ≤ t → causalSupport S z t = causalSupport T z t := by
  constructor
  · intro hhull z t hzt
    rw [causalSupport_eq_sSup_dualSupportHull hSne hScone hSbound hzt,
      causalSupport_eq_sSup_dualSupportHull hTne hTcone hTbound hzt, hhull]
  · intro hsupport
    ext q
    simp only [lorentzDualSupportHull, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hqcone, hqS⟩
      exact ⟨hqcone, fun z t hzt => by rw [← hsupport z t hzt]; exact hqS z t hzt⟩
    · rintro ⟨hqcone, hqT⟩
      exact ⟨hqcone, fun z t hzt => by rw [hsupport z t hzt]; exact hqT z t hzt⟩

/-- Global all-direction confocal fields and causal support functions determine one another. -/
theorem lorentzAxialDefect_eqOn_iff_causalSupport_eqOn
    [Nontrivial E] {S T : Set (E × ℝ)} (hSne : S.Nonempty) (hTne : T.Nonempty)
    {MS MT : ℝ} (hMS : 0 ≤ MS) (hMT : 0 ≤ MT)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hTcone : ∀ q ∈ T, ‖q.1‖ ≤ q.2)
    (hSbound : ∀ q ∈ S, q.2 ≤ MS) (hTbound : ∀ q ∈ T, q.2 ≤ MT) :
    (∀ e : E, ‖e‖ = 1 →
      Set.EqOn (lorentzAxialDefect e S) (lorentzAxialDefect e T) (Set.Ioi 0)) ↔
      ∀ z : E, ∀ t : ℝ, ‖z‖ ≤ t → causalSupport S z t = causalSupport T z t := by
  constructor
  · intro hfield z t hzt
    rcases eq_or_lt_of_le (le_trans (norm_nonneg z) hzt) with ht0 | ht0
    · have htzero : t = 0 := ht0.symm
      subst t
      have hzzero : z = 0 := norm_le_zero_iff.mp hzt
      subst z
      simp [causalSupport, hSne, hTne]
    · obtain ⟨e, lambda, c, he, hl0, hl1, hc, hz, ht⟩ :=
        exists_axial_of_mem_dualCone hzt ht0
      have hsupportAxial :=
        (lorentzAxialDefect_eqOn_iff_axialSupport_eqOn he hSne hTne hMS hMT
          hScone hTcone hSbound hTbound).mp (hfield e he)
      have hSscale : causalSupport S z t =
          c * causalSupport S (-(1 - lambda) • e) (1 + lambda) := by
        rw [hz, ht]
        exact causalSupport_smul_of_pos hSne hScone hSbound (by linarith) hc
      have hTscale : causalSupport T z t =
          c * causalSupport T (-(1 - lambda) • e) (1 + lambda) := by
        rw [hz, ht]
        exact causalSupport_smul_of_pos hTne hTcone hTbound (by linarith) hc
      rw [hSscale, hTscale]
      exact congrArg (fun x : ℝ => c * x)
        (by simpa [lorentzAxialSupport_eq_causalSupport] using
          hsupportAxial ⟨hl0, hl1⟩)
  · intro hsupport e he
    apply (lorentzAxialDefect_eqOn_iff_axialSupport_eqOn he hSne hTne hMS hMT
      hScone hTcone hSbound hTbound).2
    intro lambda hlambda
    rw [lorentzAxialSupport_eq_causalSupport,
      lorentzAxialSupport_eq_causalSupport]
    apply hsupport
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (sub_nonneg.mpr hlambda.2)]
    linarith [hlambda.1, hlambda.2]

/-- Complete three-way inverse theorem: global confocal field equality, causal-support equality,
and maximal Lorentz-hull equality are equivalent. -/
theorem lorentzConfocal_field_support_hull_equiv
    [Nontrivial E] {S T : Set (E × ℝ)} (hSne : S.Nonempty) (hTne : T.Nonempty)
    {MS MT : ℝ} (hMS : 0 ≤ MS) (hMT : 0 ≤ MT)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hTcone : ∀ q ∈ T, ‖q.1‖ ≤ q.2)
    (hSbound : ∀ q ∈ S, q.2 ≤ MS) (hTbound : ∀ q ∈ T, q.2 ≤ MT) :
    ((∀ e : E, ‖e‖ = 1 →
        Set.EqOn (lorentzAxialDefect e S) (lorentzAxialDefect e T) (Set.Ioi 0)) ↔
      (∀ z : E, ∀ t : ℝ, ‖z‖ ≤ t → causalSupport S z t = causalSupport T z t)) ∧
    ((∀ z : E, ∀ t : ℝ, ‖z‖ ≤ t → causalSupport S z t = causalSupport T z t) ↔
      lorentzDualSupportHull S = lorentzDualSupportHull T) := by
  exact ⟨lorentzAxialDefect_eqOn_iff_causalSupport_eqOn hSne hTne hMS hMT
      hScone hTcone hSbound hTbound,
    (lorentzDualSupportHull_eq_iff_causalSupport_eqOn hSne hTne
      hScone hTcone hSbound hTbound).symm⟩

end

end HTGeometry
