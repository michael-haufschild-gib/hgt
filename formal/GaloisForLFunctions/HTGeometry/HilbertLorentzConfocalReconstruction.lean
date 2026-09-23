import GaloisForLFunctions.HTGeometry.ConfocalGlobalSupportFaithfulness

/-!
# Hilbert-Lorentz confocal reconstruction: the dimension-free master theorem

The scalar all-radius confocal support transform (`ConfocalGlobalSupportTransform`,
`ConfocalGlobalSupportFaithfulness`) lifts, direction by direction, to an arbitrary real
inner-product space through the canonical axial Lorentz lift `z ↦ (⟪z, axis⟫, ‖z‖)`.  Along any unit
axis, the realized all-radius confocal defect is the greatest nonnegative causal-contact fixed point
of the one-dimensional null-support operator (`axialGlobalDefect_eq_nullSupport_fixedPoint`,
`axialGlobalDefect_isGreatest_fixedPoint`).  The transfer is exact because the axial distance-sum
branch coincides with the lifted Lorentz branch (`liftedConfocalBranch_axialLorentzLift`), so the
entire scalar theory applies to the lifted source with no dimensional hypothesis.
-/

namespace HTGeometry
noncomputable section
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- All-positive-radius axial confocal envelope of a source in a real inner-product space, along a
unit direction `axis`. -/
def axialGlobalEnvelope (axis : E) (S : Set E) (R : ℝ) : ℝ :=
  sSup ((fun z => axialDistanceSumBranch axis z R) '' S)

/-- The axial confocal defect: envelope minus radius. -/
def axialGlobalDefect (axis : E) (S : Set E) (R : ℝ) : ℝ :=
  axialGlobalEnvelope axis S R - R

private theorem axial_liftedImage
    {axis : E} {S : Set E} {R : ℝ} (haxis : ‖axis‖ = 1) (hR : 0 < R) :
    liftedConfocalBranch (R := R) '' (axialLorentzLift axis '' S) =
      (fun z => axialDistanceSumBranch axis z R) '' S := by
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (liftedConfocalBranch_axialLorentzLift haxis hR).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨axialLorentzLift axis z, ⟨z, hz, rfl⟩,
      liftedConfocalBranch_axialLorentzLift haxis hR⟩

theorem axialGlobalEnvelope_eq_confocalGlobalEnvelope
    {axis : E} {S : Set E} {R : ℝ} (haxis : ‖axis‖ = 1) (hR : 0 < R) :
    axialGlobalEnvelope axis S R = confocalGlobalEnvelope (axialLorentzLift axis '' S) R := by
  rw [axialGlobalEnvelope, confocalGlobalEnvelope, axial_liftedImage haxis hR]

theorem axialGlobalDefect_eq_confocalGlobalDefect
    {axis : E} {S : Set E} {R : ℝ} (haxis : ‖axis‖ = 1) (hR : 0 < R) :
    axialGlobalDefect axis S R = confocalGlobalDefect (axialLorentzLift axis '' S) R := by
  rw [axialGlobalDefect, confocalGlobalDefect, axialGlobalEnvelope_eq_confocalGlobalEnvelope haxis hR]

private theorem axial_cone_bound
    {axis : E} {S : Set E} {M : ℝ} (haxis : ‖axis‖ = 1) (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    axialLorentzLift axis '' S ⊆ confocalLorentzCone ∧
      ∀ q ∈ axialLorentzLift axis '' S, q.2 ≤ M := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩; exact axialLorentzLift_mem_confocalLorentzCone haxis
  · rintro _ ⟨z, hz, rfl⟩; exact hbound z hz

/-- **Dimension-free causal-contact master equation.**  In any real inner-product space, along any
unit axis, the realized axial confocal defect is a nonnegative fixed point of the one-dimensional
null-support operator of the axial Lorentz lift, at every positive radius. -/
theorem axialGlobalDefect_eq_nullSupport_fixedPoint
    {axis : E} (haxis : ‖axis‖ = 1) {S : Set E} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R) (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    0 ≤ axialGlobalDefect axis S R ∧
      axialGlobalDefect axis S R =
        confocalNullSupportOperator (axialLorentzLift axis '' S) R
          (axialGlobalDefect axis S R) := by
  obtain ⟨hcone, hbnd⟩ := axial_cone_bound haxis hbound
  rw [axialGlobalDefect_eq_confocalGlobalDefect haxis hR]
  exact confocalGlobalDefect_eq_nullSupport_fixedPoint (hne.image _) hM hR hcone hbnd

/-- **Dimension-free greatest-root selection.**  The realized axial confocal defect is the greatest
nonnegative fixed point of the null-support operator, in any real inner-product space. -/
theorem axialGlobalDefect_isGreatest_fixedPoint
    {axis : E} (haxis : ‖axis‖ = 1) {S : Set E} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R) (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    0 ≤ axialGlobalDefect axis S R ∧
      axialGlobalDefect axis S R =
        confocalNullSupportOperator (axialLorentzLift axis '' S) R
          (axialGlobalDefect axis S R) ∧
      ∀ d : ℝ, 0 ≤ d →
        d = confocalNullSupportOperator (axialLorentzLift axis '' S) R d →
          d ≤ axialGlobalDefect axis S R := by
  obtain ⟨hcone, hbnd⟩ := axial_cone_bound haxis hbound
  rw [axialGlobalDefect_eq_confocalGlobalDefect haxis hR]
  exact confocalGlobalDefect_isGreatest_fixedPoint (hne.image _) hM hR hcone hbnd


/-- Scalar axial projection of a general Lorentz source point `(y,a) ∈ L(V)` along a unit direction:
`(y,a) ↦ (⟪e,y⟫, a)`. -/
def lorentzAxialProjection (e : E) (q : E × ℝ) : ℝ × ℝ :=
  (inner ℝ e q.1, q.2)

theorem lorentzAxialProjection_mem_confocalLorentzCone
    {e : E} (haxis : ‖e‖ = 1) {q : E × ℝ} (hq : ‖q.1‖ ≤ q.2) :
    lorentzAxialProjection e q ∈ confocalLorentzCone := by
  rw [lorentzAxialProjection, confocalLorentzCone, Set.mem_setOf_eq]
  calc |inner ℝ e q.1| ≤ ‖e‖ * ‖q.1‖ := abs_real_inner_le_norm e q.1
    _ = ‖q.1‖ := by rw [haxis, one_mul]
    _ ≤ q.2 := hq

/-- The scalar lifted branch of the axial projection is the general Lorentz distance-sum branch
`a + sqrt(R² - 2R⟪e,y⟫ + a²)`. -/
theorem liftedConfocalBranch_lorentzAxialProjection (e : E) (q : E × ℝ) (R : ℝ) :
    liftedConfocalBranch (lorentzAxialProjection e q) R =
      q.2 + Real.sqrt (R ^ (2 : ℕ) - 2 * R * inner ℝ e q.1 + q.2 ^ (2 : ℕ)) := by
  rw [liftedConfocalBranch, lorentzAxialProjection]
  congr 2
  ring

/-- All-radius confocal envelope of a general Lorentz source along a unit direction. -/
def lorentzAxialEnvelope (e : E) (S : Set (E × ℝ)) (R : ℝ) : ℝ :=
  confocalGlobalEnvelope (lorentzAxialProjection e '' S) R

/-- All-radius confocal defect of a general Lorentz source along a unit direction. -/
def lorentzAxialDefect (e : E) (S : Set (E × ℝ)) (R : ℝ) : ℝ :=
  confocalGlobalDefect (lorentzAxialProjection e '' S) R

private theorem lorentz_cone_bound
    {e : E} {S : Set (E × ℝ)} {M : ℝ} (haxis : ‖e‖ = 1)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    lorentzAxialProjection e '' S ⊆ confocalLorentzCone ∧
      ∀ p ∈ lorentzAxialProjection e '' S, p.2 ≤ M := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact lorentzAxialProjection_mem_confocalLorentzCone haxis (hScone q hq)
  · rintro _ ⟨q, hq, rfl⟩
    exact hbound q hq

/-- **Dimension-free causal-contact master equation (general Lorentz source).**  In any real
inner-product space, along any unit direction, the realized all-radius confocal defect of a general
bounded Lorentz source is a nonnegative fixed point of the one-dimensional null-support operator of
its axial projection, at every positive radius (master theorem part A). -/
theorem lorentzAxialDefect_eq_nullSupport_fixedPoint
    {e : E} (haxis : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R) (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    0 ≤ lorentzAxialDefect e S R ∧
      lorentzAxialDefect e S R =
        confocalNullSupportOperator (lorentzAxialProjection e '' S) R (lorentzAxialDefect e S R) := by
  obtain ⟨hcone, hbnd⟩ := lorentz_cone_bound haxis hScone hbound
  exact confocalGlobalDefect_eq_nullSupport_fixedPoint (hne.image _) hM hR hcone hbnd

/-- **Greatest-root selection (general Lorentz source).**  The realized axial confocal defect is the
greatest nonnegative fixed point of the null-support operator, in any dimension. -/
theorem lorentzAxialDefect_isGreatest_fixedPoint
    {e : E} (haxis : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R) (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    0 ≤ lorentzAxialDefect e S R ∧
      lorentzAxialDefect e S R =
        confocalNullSupportOperator (lorentzAxialProjection e '' S) R (lorentzAxialDefect e S R) ∧
      ∀ d : ℝ, 0 ≤ d →
        d = confocalNullSupportOperator (lorentzAxialProjection e '' S) R d →
          d ≤ lorentzAxialDefect e S R := by
  obtain ⟨hcone, hbnd⟩ := lorentz_cone_bound haxis hScone hbound
  exact confocalGlobalDefect_isGreatest_fixedPoint (hne.image _) hM hR hcone hbnd


/-- Causal support function `h_{S,e}` of a general Lorentz source along a unit direction: the scalar
null support of the axial projection. -/
def lorentzAxialSupport (e : E) (S : Set (E × ℝ)) (lambda : ℝ) : ℝ :=
  confocalNullSupport (lorentzAxialProjection e '' S) lambda

/-- The axial null functional is the causal linear functional `(a - ⟪e,y⟫) + λ(a + ⟪e,y⟫)`. -/
theorem confocalNullFunctional_lorentzAxialProjection (e : E) (q : E × ℝ) (lambda : ℝ) :
    confocalNullFunctional (lorentzAxialProjection e q) lambda =
      (q.2 - inner ℝ e q.1) + lambda * (q.2 + inner ℝ e q.1) := by
  rw [confocalNullFunctional, lorentzAxialProjection, confocalNullMinus, confocalNullPlus]

/-- **Per-direction field/support faithfulness (master theorem representation (0), one axis).**  Two
general bounded Lorentz sources have the same all-radius confocal defect field along a unit direction
iff they have the same causal support function `h_{·,e}` on `[0,1]`. -/
theorem lorentzAxialDefect_eqOn_iff_axialSupport_eqOn
    {e : E} (haxis : ‖e‖ = 1) {S T : Set (E × ℝ)} (hSne : S.Nonempty) (hTne : T.Nonempty)
    {MS MT : ℝ} (hMS : 0 ≤ MS) (hMT : 0 ≤ MT)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hTcone : ∀ q ∈ T, ‖q.1‖ ≤ q.2)
    (hSbound : ∀ q ∈ S, q.2 ≤ MS) (hTbound : ∀ q ∈ T, q.2 ≤ MT) :
    Set.EqOn (lorentzAxialDefect e S) (lorentzAxialDefect e T) (Set.Ioi 0) ↔
      Set.EqOn (lorentzAxialSupport e S) (lorentzAxialSupport e T) (Set.Icc 0 1) := by
  obtain ⟨hSc, hSb⟩ := lorentz_cone_bound haxis hScone hSbound
  obtain ⟨hTc, hTb⟩ := lorentz_cone_bound haxis hTcone hTbound
  exact globalDefect_eqOn_iff_nullSupport_eqOn (hSne.image _) (hTne.image _) hMS hMT hSc hTc hSb hTb

/-- **Per-direction field/support/hull equivalence (master theorem representation (0), one axis).**
Along a unit direction, the all-radius confocal hull of a general Lorentz source equals its causal
null-support hull. -/
theorem lorentzAxial_confocalHull_eq_nullSupportHull
    {e : E} (haxis : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    confocalHullOfField (Set.Ioi 0) (confocalGlobalEnvelope (lorentzAxialProjection e '' S)) =
      confocalNullSupportHull (lorentzAxialProjection e '' S) := by
  obtain ⟨hSc, hSb⟩ := lorentz_cone_bound haxis hScone hbound
  exact confocalHullOfField_eq_confocalNullSupportHull (hne.image _) hM hSc hSb


/-- The causal support function `H_S(z,t) = sup_{(y,a)∈S} (⟪z,y⟫ + t·a)` on the dual Lorentz cone. -/
def causalSupport (S : Set (E × ℝ)) (z : E) (t : ℝ) : ℝ :=
  sSup ((fun q => inner ℝ z q.1 + t * q.2) '' S)

/-- **Causal support / axial support identity (equation (4)).**  The per-direction causal support
`h_{S,e}(λ)` is the value of the global causal support at the dual point `(-(1-λ)e, 1+λ)`. -/
theorem lorentzAxialSupport_eq_causalSupport (e : E) (S : Set (E × ℝ)) (lambda : ℝ) :
    lorentzAxialSupport e S lambda = causalSupport S (-(1 - lambda) • e) (1 + lambda) := by
  have hfun : (fun q : E × ℝ => confocalNullFunctional (lorentzAxialProjection e q) lambda) =
      (fun q : E × ℝ => inner ℝ (-(1 - lambda) • e) q.1 + (1 + lambda) * q.2) := by
    funext q
    rw [confocalNullFunctional_lorentzAxialProjection, real_inner_smul_left]
    ring
  rw [lorentzAxialSupport, confocalNullSupport, causalSupport, Set.image_image, hfun]

/-- **Coverage of the dual Lorentz cone by axial directions.**  Every dual-cone point `(z,t)` with
`‖z‖ ≤ t` and `t > 0` is a positive multiple of an axial dual point `(-(1-λ)e, 1+λ)` for a unit
direction `e` and `λ ∈ [0,1]`. -/
theorem exists_axial_of_mem_dualCone [Nontrivial E] {z : E} {t : ℝ} (hzt : ‖z‖ ≤ t) (ht : 0 < t) :
    ∃ (e : E) (lambda c : ℝ), ‖e‖ = 1 ∧ 0 ≤ lambda ∧ lambda ≤ 1 ∧ 0 < c ∧
      z = c • (-(1 - lambda) • e) ∧ t = c * (1 + lambda) := by
  rcases eq_or_ne z 0 with hz | hz
  · obtain ⟨e, he⟩ := exists_ne (0 : E)
    refine ⟨‖e‖⁻¹ • e, 1, t / 2, ?_, zero_le_one, le_refl 1, by positivity, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr he)
    · rw [hz]; simp
    · ring
  · have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    refine ⟨-‖z‖⁻¹ • z, (t - ‖z‖) / (t + ‖z‖), (‖z‖ + t) / 2, ?_, ?_, ?_, by positivity, ?_, ?_⟩
    · rw [norm_smul, norm_neg, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (ne_of_gt hznorm)
    · apply div_nonneg (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]; linarith
    · rw [smul_smul, smul_smul]
      have hne : (t + ‖z‖) ≠ 0 := by positivity
      rw [show (‖z‖ + t) / 2 * -(1 - (t - ‖z‖) / (t + ‖z‖)) * -‖z‖⁻¹ = 1 by
        field_simp; ring]
      rw [one_smul]
    · field_simp; ring


/-- The causal-support image of a bounded Lorentz source is bounded above. -/
theorem bddAbove_causalSupport_image
    {S : Set (E × ℝ)} {M : ℝ} (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    {z : E} {t : ℝ} (ht : 0 ≤ t) :
    BddAbove ((fun q => inner ℝ z q.1 + t * q.2) '' S) := by
  refine ⟨(‖z‖ + t) * M, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  have hq2 : 0 ≤ q.2 := le_trans (norm_nonneg _) (hScone q hq)
  have hinner : inner ℝ z q.1 ≤ ‖z‖ * q.2 :=
    calc inner ℝ z q.1 ≤ ‖(inner ℝ z q.1 : ℝ)‖ := Real.le_norm_self _
      _ ≤ ‖z‖ * ‖q.1‖ := norm_inner_le_norm z q.1
      _ ≤ ‖z‖ * q.2 := mul_le_mul_of_nonneg_left (hScone q hq) (norm_nonneg _)
  nlinarith [hinner, mul_le_mul_of_nonneg_left (hbound q hq) ht,
    mul_le_mul_of_nonneg_left (hbound q hq) (norm_nonneg z)]

/-- **Positive homogeneity of the causal support function.**  `H_S(c·z, c·t) = c·H_S(z,t)` for
`c > 0`, on a bounded Lorentz source. -/
theorem causalSupport_smul_of_pos
    {S : Set (E × ℝ)} (hne : S.Nonempty) {M : ℝ}
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    {z : E} {t : ℝ} (ht : 0 ≤ t) {c : ℝ} (hc : 0 < c) :
    causalSupport S (c • z) (c * t) = c * causalSupport S z t := by
  have hbdd := bddAbove_causalSupport_image (z := z) (t := t) hScone hbound ht
  have himg : (fun q : E × ℝ => inner ℝ (c • z) q.1 + (c * t) * q.2) '' S =
      (fun x => c * x) '' ((fun q : E × ℝ => inner ℝ z q.1 + t * q.2) '' S) := by
    rw [Set.image_image]
    congr 1
    funext q
    rw [real_inner_smul_left]; ring
  rw [causalSupport, causalSupport, himg]
  exact (IsLUB.mul_left hc.le (isLUB_csSup (hne.image _) hbdd)).csSup_eq ((hne.image _).image _)

/-- The axial null functional equals the causal linear functional at the dual point `(-(1-λ)e, 1+λ)`. -/
theorem confocalNullFunctional_proj_eq_causal (e : E) (q : E × ℝ) (lambda : ℝ) :
    confocalNullFunctional (lorentzAxialProjection e q) lambda =
      inner ℝ (-(1 - lambda) • e) q.1 + (1 + lambda) * q.2 := by
  rw [confocalNullFunctional_lorentzAxialProjection, real_inner_smul_left]; ring

/-- **Per-direction field ↔ causal-support constraint.**  For a bounded Lorentz source and a fixed
unit direction, a cone point satisfies all confocal branch bounds along that direction iff its causal
functional stays below the causal support at every axial dual point `(-(1-λ)e, 1+λ)`. -/
theorem lorentzField_iff_dual_perDirection
    {S : Set (E × ℝ)} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M)
    {q : E × ℝ} (hqcone : ‖q.1‖ ≤ q.2) {e : E} (he : ‖e‖ = 1) :
    (∀ R : ℝ, 0 < R →
        liftedConfocalBranch (lorentzAxialProjection e q) R ≤
          confocalGlobalEnvelope (lorentzAxialProjection e '' S) R) ↔
      (∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ 1 →
        inner ℝ (-(1 - lambda) • e) q.1 + (1 + lambda) * q.2 ≤
          causalSupport S (-(1 - lambda) • e) (1 + lambda)) := by
  have hproj : lorentzAxialProjection e q ∈ confocalLorentzCone :=
    lorentzAxialProjection_mem_confocalLorentzCone he hqcone
  have hhull := lorentzAxial_confocalHull_eq_nullSupportHull he hne hM hScone hbound
  have hsupp : ∀ lambda : ℝ, confocalNullSupport (lorentzAxialProjection e '' S) lambda
      = causalSupport S (-(1 - lambda) • e) (1 + lambda) :=
    fun lambda => lorentzAxialSupport_eq_causalSupport e S lambda
  constructor
  · intro hfield lambda hl0 hl1
    have hmem : lorentzAxialProjection e q ∈
        confocalHullOfField (Set.Ioi 0) (confocalGlobalEnvelope (lorentzAxialProjection e '' S)) :=
      ⟨hproj, fun R hR => hfield R hR⟩
    rw [hhull] at hmem
    have hc := hmem.2 lambda ⟨hl0, hl1⟩
    rw [confocalNullFunctional_proj_eq_causal, hsupp] at hc
    exact hc
  · intro hdual R hR
    have hmem : lorentzAxialProjection e q ∈ confocalNullSupportHull (lorentzAxialProjection e '' S) := by
      refine ⟨hproj, fun lambda hlam => ?_⟩
      rw [confocalNullFunctional_proj_eq_causal, hsupp]
      exact hdual lambda hlam.1 hlam.2
    rw [← hhull] at hmem
    exact hmem.2 R hR

/-- The all-directions confocal field hull `K_G(S)`: cone points whose confocal branch stays below
the envelope along every unit direction and radius. -/
def lorentzConfocalFieldHull (S : Set (E × ℝ)) : Set (E × ℝ) :=
  {q | ‖q.1‖ ≤ q.2 ∧ ∀ e : E, ‖e‖ = 1 → ∀ R : ℝ, 0 < R →
    liftedConfocalBranch (lorentzAxialProjection e q) R ≤
      confocalGlobalEnvelope (lorentzAxialProjection e '' S) R}

/-- The dual causal-support hull `K_H(S)`: cone points dominated by the causal support over the whole
dual Lorentz cone. -/
def lorentzDualSupportHull (S : Set (E × ℝ)) : Set (E × ℝ) :=
  {q | ‖q.1‖ ≤ q.2 ∧ ∀ z : E, ∀ t : ℝ, ‖z‖ ≤ t →
    inner ℝ z q.1 + t * q.2 ≤ causalSupport S z t}

/-- **Master theorem, field/hull equivalence (representation (0), all directions).**  For a nonempty
bounded Lorentz source in any nonzero real inner-product space, the all-directions confocal field hull
equals the dual causal-support hull: `K_G(S) = K_H(S)`. -/
theorem lorentzConfocalFieldHull_eq_dualSupportHull [Nontrivial E]
    {S : Set (E × ℝ)} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    lorentzConfocalFieldHull S = lorentzDualSupportHull S := by
  ext q
  constructor
  · rintro ⟨hqcone, hqfield⟩
    refine ⟨hqcone, fun z t hzt => ?_⟩
    rcases eq_or_lt_of_le (le_trans (norm_nonneg z) hzt) with ht0 | ht0
    · have htz : t = 0 := ht0.symm
      subst htz
      have hz : z = 0 := norm_le_zero_iff.mp hzt
      subst hz
      obtain ⟨q0, hq0⟩ := hne
      have hbdd := bddAbove_causalSupport_image (z := (0:E)) (t := (0:ℝ)) hScone hbound (le_refl 0)
      have h0mem : (0:ℝ) ∈ (fun q : E × ℝ => inner ℝ (0:E) q.1 + (0:ℝ) * q.2) '' S :=
        ⟨q0, hq0, by simp⟩
      have h00 : (0:ℝ) ≤ causalSupport S 0 0 := le_csSup hbdd h0mem
      simp only [inner_zero_left, zero_mul, add_zero]
      exact h00
    · obtain ⟨e, lambda, c, he, hl0, hl1, hc, hzeq, hteq⟩ := exists_axial_of_mem_dualCone hzt ht0
      have hfunc : inner ℝ z q.1 + t * q.2 =
          c * (inner ℝ (-(1 - lambda) • e) q.1 + (1 + lambda) * q.2) := by
        rw [hzeq, hteq, real_inner_smul_left]; ring
      have hHS : causalSupport S z t = c * causalSupport S (-(1 - lambda) • e) (1 + lambda) := by
        rw [hzeq, hteq]
        exact causalSupport_smul_of_pos hne hScone hbound (by linarith) hc
      have hax := (lorentzField_iff_dual_perDirection hne hM hScone hbound hqcone he).mp
        (hqfield e he) lambda hl0 hl1
      rw [hfunc, hHS]
      exact mul_le_mul_of_nonneg_left hax hc.le
  · rintro ⟨hqcone, hqdual⟩
    refine ⟨hqcone, fun e he R hR => ?_⟩
    refine (lorentzField_iff_dual_perDirection hne hM hScone hbound hqcone he).mpr
      (fun lambda hl0 hl1 => ?_) R hR
    refine hqdual (-(1 - lambda) • e) (1 + lambda) ?_
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lambda)]
    linarith

/-- **Master theorem part B (projective graph, per direction).**  Along any unit direction, the
positive all-radius confocal defect graph of a general Lorentz source equals the rational projective
image of its causal null-support graph. -/
theorem lorentzAxial_positiveDefectGraph_eq
    {e : E} (haxis : ‖e‖ = 1) {S : Set (E × ℝ)} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hScone : ∀ q ∈ S, ‖q.1‖ ≤ q.2) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    confocalGlobalPositiveDefectGraph (lorentzAxialProjection e '' S) =
      confocalFullProjectiveSupportGraph (lorentzAxialProjection e '' S) := by
  obtain ⟨hcone, hbnd⟩ := lorentz_cone_bound haxis hScone hbound
  exact confocalGlobalPositiveDefectGraph_eq_fullProjectiveSupportGraph (hne.image _) hM hcone hbnd

end
end HTGeometry
