import GaloisForLFunctions.HTGeometry.ConfocalEnvelopeHull
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Projective null-support law for confocal envelopes

In Lorentz null coordinates, an exterior confocal distance-sum envelope is the unique fixed point
of an ordinary linear support field.  The fixed-point operator is a contraction with the universal
modulus `M / R`, where `M` bounds the source radius and `R > M` is the moving focus.
-/

namespace HTGeometry

noncomputable section

open scoped Real

/-- Incoming Lorentz null coordinate `a - x`. -/
def confocalNullMinus (q : ℝ × ℝ) : ℝ :=
  q.2 - q.1

/-- Outgoing Lorentz null coordinate `a + x`. -/
def confocalNullPlus (q : ℝ × ℝ) : ℝ :=
  q.2 + q.1

/-- Linear null-coordinate observable at projective parameter `lambda`. -/
def confocalNullFunctional (q : ℝ × ℝ) (lambda : ℝ) : ℝ :=
  confocalNullMinus q + lambda * confocalNullPlus q

/-- The projective parameter associated with radius `R` and envelope defect `d`. -/
def confocalProjectiveParameter (R d : ℝ) : ℝ :=
  d / (2 * R + d)

/-- Ordinary support field of a Lorentz source in the null direction `(1, lambda)`. -/
def confocalNullSupport (S : Set (ℝ × ℝ)) (lambda : ℝ) : ℝ :=
  sSup (confocalNullFunctional (lambda := lambda) '' S)

/-- The scalar self-consistency operator for the exterior confocal defect. -/
def confocalNullSupportOperator (S : Set (ℝ × ℝ)) (R d : ℝ) : ℝ :=
  confocalNullSupport S (confocalProjectiveParameter R d)

theorem confocalNullMinus_nonneg
    {q : ℝ × ℝ} (hq : q ∈ confocalLorentzCone) :
    0 ≤ confocalNullMinus q := by
  rw [confocalNullMinus]
  exact sub_nonneg.mpr ((le_abs_self q.1).trans hq)

theorem confocalNullPlus_nonneg
    {q : ℝ × ℝ} (hq : q ∈ confocalLorentzCone) :
    0 ≤ confocalNullPlus q := by
  rw [confocalNullPlus]
  exact neg_le_iff_add_nonneg.mp ((neg_le_abs q.1).trans hq)

theorem confocalNullPlus_le_two_mul_snd
    {q : ℝ × ℝ} (hq : q ∈ confocalLorentzCone) :
    confocalNullPlus q ≤ 2 * q.2 := by
  rw [confocalNullPlus]
  have hx : q.1 ≤ q.2 := (le_abs_self q.1).trans hq
  linarith

theorem confocalProjectiveParameter_nonneg
    {R d : ℝ} (hR : 0 < R) (hd : 0 ≤ d) :
    0 ≤ confocalProjectiveParameter R d := by
  rw [confocalProjectiveParameter]
  positivity

theorem confocalProjectiveParameter_le_one
    {R d : ℝ} (hR : 0 < R) (hd : 0 ≤ d) :
    confocalProjectiveParameter R d ≤ 1 := by
  rw [confocalProjectiveParameter]
  apply (div_le_one (by positivity)).2
  linarith

theorem confocalProjectiveParameter_mono
    {R d e : ℝ} (hR : 0 < R) (hd : 0 ≤ d) (hde : d ≤ e) :
    confocalProjectiveParameter R d ≤ confocalProjectiveParameter R e := by
  have he : 0 ≤ e := hd.trans hde
  rw [confocalProjectiveParameter, confocalProjectiveParameter]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * R + d)
    (by positivity : 0 < 2 * R + e)).2
  nlinarith

/-- The projective coordinate has a degree-free Lipschitz constant `1/(2R)`. -/
theorem confocalProjectiveParameter_lipschitz
    {R d e : ℝ} (hR : 0 < R) (hd : 0 ≤ d) (he : 0 ≤ e) :
    |confocalProjectiveParameter R d - confocalProjectiveParameter R e| ≤
      |d - e| / (2 * R) := by
  have hdenD : 0 < 2 * R + d := by positivity
  have hdenE : 0 < 2 * R + e := by positivity
  have hid :
      confocalProjectiveParameter R d - confocalProjectiveParameter R e =
        (2 * R * (d - e)) / ((2 * R + d) * (2 * R + e)) := by
    rw [confocalProjectiveParameter, confocalProjectiveParameter]
    field_simp [hdenD.ne', hdenE.ne']
    ring
  rw [hid]
  norm_num [abs_div, abs_mul, abs_of_pos hR, abs_of_pos hdenD,
    abs_of_pos hdenE]
  have hbase : (2 * R) ^ (2 : ℕ) ≤ (2 * R + d) * (2 * R + e) := by
    nlinarith [mul_nonneg hd he]
  have hnum : 0 ≤ 2 * R * |d - e| := mul_nonneg (by positivity) (abs_nonneg _)
  calc
    2 * R * |d - e| / ((2 * R + d) * (2 * R + e)) ≤
        2 * R * |d - e| / ((2 * R) ^ (2 : ℕ)) := by
      exact div_le_div_of_nonneg_left hnum (by positivity) hbase
    _ = |d - e| / (2 * R) := by field_simp [hR.ne']

/-- Every exterior lifted branch lies above the focal separation `R`. -/
theorem le_liftedConfocalBranch_of_snd_lt_radius
    {q : ℝ × ℝ} (hq : q ∈ confocalLorentzCone) {R : ℝ} (hqR : q.2 < R) :
    R ≤ liftedConfocalBranch q R := by
  have ha0 : 0 ≤ q.2 := (abs_nonneg q.1).trans hq
  have hxle : q.1 ≤ q.2 := (le_abs_self q.1).trans hq
  have hRx : 0 ≤ R - q.1 := by linarith
  have hsq : q.1 ^ (2 : ℕ) ≤ q.2 ^ (2 : ℕ) := by
    rw [sq_le_sq]
    simpa only [abs_of_nonneg ha0] using! hq
  have hrad := liftedConfocalRadicand_nonneg hq R
  have hsqrt2 := Real.sq_sqrt hrad
  have hsqrt0 := Real.sqrt_nonneg ((R - q.1) ^ (2 : ℕ) + (q.2 ^ (2 : ℕ) - q.1 ^ (2 : ℕ)))
  rw [liftedConfocalBranch]
  nlinarith

/-- A branch is self-supported by its Lorentz half-space with equality. -/
theorem liftedConfocalBranch_halfspace_self
    {q : ℝ × ℝ} (hq : q ∈ confocalLorentzCone) (R : ℝ) :
    R * q.1 - liftedConfocalBranch q R * q.2 =
      (R ^ (2 : ℕ) - liftedConfocalBranch q R ^ (2 : ℕ)) / 2 := by
  have hrad := liftedConfocalRadicand_nonneg hq R
  have hsqrt2 := Real.sq_sqrt hrad
  rw [liftedConfocalBranch]
  nlinarith

/-- **Pointwise projective linearization.**  An exterior confocal sublevel is exactly one
ordinary null-coordinate half-space. -/
theorem liftedConfocalBranch_le_add_iff_nullFunctional_le
    {q : ℝ × ℝ} (hq : q ∈ confocalLorentzCone)
    {R d : ℝ} (hR : 0 < R) (hqR : q.2 < R) (hd : 0 ≤ d) :
    liftedConfocalBranch q R ≤ R + d ↔
      confocalNullFunctional q (confocalProjectiveParameter R d) ≤ d := by
  have hden : 0 < 2 * R + d := by positivity
  have haL : q.2 ≤ R + d := by linarith
  have hre :
      confocalNullFunctional q (confocalProjectiveParameter R d) =
        ((confocalNullMinus q) * (2 * R + d) + d * confocalNullPlus q) /
          (2 * R + d) := by
    rw [confocalNullFunctional, confocalProjectiveParameter]
    field_simp [hden.ne']
  rw [liftedConfocalBranch_le_iff_halfspace hq R (R + d), hre]
  constructor
  · rintro ⟨_, hhalf⟩
    rw [div_le_iff₀ hden]
    rw [confocalNullMinus, confocalNullPlus]
    nlinarith
  · intro hnull
    refine ⟨haL, ?_⟩
    rw [div_le_iff₀ hden] at hnull
    rw [confocalNullMinus, confocalNullPlus] at hnull
    nlinarith

/-- A branch defect is exactly its own projectively selected null functional. -/
theorem liftedConfocalBranch_sub_eq_nullFunctional_projective
    {q : ℝ × ℝ} (hq : q ∈ confocalLorentzCone)
    {R : ℝ} (hR : 0 < R) (hqR : q.2 < R) :
    liftedConfocalBranch q R - R =
      confocalNullFunctional q
        (confocalProjectiveParameter R (liftedConfocalBranch q R - R)) := by
  have hd : 0 ≤ liftedConfocalBranch q R - R :=
    sub_nonneg.mpr (le_liftedConfocalBranch_of_snd_lt_radius hq hqR)
  have hden : 0 < 2 * R + (liftedConfocalBranch q R - R) := by positivity
  have hself := liftedConfocalBranch_halfspace_self hq R
  rw [confocalNullFunctional, confocalProjectiveParameter,
    confocalNullMinus, confocalNullPlus]
  field_simp [hden.ne']
  nlinarith

private theorem bddAbove_confocalNullFunctional_image
    {S : Set (ℝ × ℝ)} {M lambda : ℝ}
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hlambda1 : lambda ≤ 1) :
    BddAbove (confocalNullFunctional (lambda := lambda) '' S) := by
  refine ⟨2 * max M 0, ?_⟩
  rintro _ ⟨q, hqS, rfl⟩
  have hq := hcone hqS
  have hu0 := confocalNullMinus_nonneg hq
  have hv0 := confocalNullPlus_nonneg hq
  have hvle := confocalNullPlus_le_two_mul_snd hq
  have hqM : q.2 ≤ max M 0 := (hbound q hqS).trans (le_max_left _ _)
  change confocalNullMinus q + lambda * confocalNullPlus q ≤ 2 * max M 0
  have hmul : lambda * confocalNullPlus q ≤ confocalNullPlus q := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hlambda1 hv0
  have huv : confocalNullMinus q + confocalNullPlus q = 2 * q.2 := by
    rw [confocalNullMinus, confocalNullPlus]
    ring
  nlinarith

theorem isLUB_confocalNullSupport
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M lambda : ℝ}
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hlambda1 : lambda ≤ 1) :
    IsLUB (confocalNullFunctional (lambda := lambda) '' S)
      (confocalNullSupport S lambda) := by
  exact isLUB_csSup (hne.image _) <|
    bddAbove_confocalNullFunctional_image hcone hbound hlambda1

/-- Ordinary null support is Lipschitz, with constant twice the source radius, throughout the
entire upper parameter half-line `lambda ≤ 1`. -/
theorem confocalNullSupport_lipschitz
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M lambda mu : ℝ}
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hlambda1 : lambda ≤ 1) (hmu1 : mu ≤ 1) :
    |confocalNullSupport S lambda - confocalNullSupport S mu| ≤
      2 * M * |lambda - mu| := by
  have hLlambda := isLUB_confocalNullSupport hne hcone hbound hlambda1
  have hLmu := isLUB_confocalNullSupport hne hcone hbound hmu1
  have hforward : confocalNullSupport S lambda ≤
      confocalNullSupport S mu + 2 * M * |lambda - mu| := by
    apply hLlambda.2
    rintro _ ⟨q, hqS, rfl⟩
    have hq := hcone hqS
    have hv0 := confocalNullPlus_nonneg hq
    have hvM : confocalNullPlus q ≤ 2 * M :=
      (confocalNullPlus_le_two_mul_snd hq).trans
        (mul_le_mul_of_nonneg_left (hbound q hqS) (by norm_num))
    have hqmu : confocalNullFunctional q mu ≤ confocalNullSupport S mu :=
      hLmu.1 ⟨q, hqS, rfl⟩
    have hrewrite : confocalNullFunctional q lambda =
        confocalNullFunctional q mu + (lambda - mu) * confocalNullPlus q := by
      rw [confocalNullFunctional, confocalNullFunctional]
      ring
    have hdiff : (lambda - mu) * confocalNullPlus q ≤
        |lambda - mu| * (2 * M) := by
      calc
        (lambda - mu) * confocalNullPlus q ≤
            |lambda - mu| * confocalNullPlus q :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hv0
        _ ≤ |lambda - mu| * (2 * M) :=
          mul_le_mul_of_nonneg_left hvM (abs_nonneg _)
    change confocalNullFunctional q lambda ≤
      confocalNullSupport S mu + 2 * M * |lambda - mu|
    rw [hrewrite]
    nlinarith
  have hbackward : confocalNullSupport S mu ≤
      confocalNullSupport S lambda + 2 * M * |lambda - mu| := by
    apply hLmu.2
    rintro _ ⟨q, hqS, rfl⟩
    have hq := hcone hqS
    have hv0 := confocalNullPlus_nonneg hq
    have hvM : confocalNullPlus q ≤ 2 * M :=
      (confocalNullPlus_le_two_mul_snd hq).trans
        (mul_le_mul_of_nonneg_left (hbound q hqS) (by norm_num))
    have hqlambda : confocalNullFunctional q lambda ≤ confocalNullSupport S lambda :=
      hLlambda.1 ⟨q, hqS, rfl⟩
    have hrewrite : confocalNullFunctional q mu =
        confocalNullFunctional q lambda + (mu - lambda) * confocalNullPlus q := by
      rw [confocalNullFunctional, confocalNullFunctional]
      ring
    have hdiff : (mu - lambda) * confocalNullPlus q ≤
        |lambda - mu| * (2 * M) := by
      have habs : |mu - lambda| = |lambda - mu| := by rw [abs_sub_comm]
      calc
        (mu - lambda) * confocalNullPlus q ≤
            |mu - lambda| * confocalNullPlus q :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hv0
        _ ≤ |mu - lambda| * (2 * M) :=
          mul_le_mul_of_nonneg_left hvM (abs_nonneg _)
        _ = |lambda - mu| * (2 * M) := by rw [habs]
    change confocalNullFunctional q mu ≤
      confocalNullSupport S lambda + 2 * M * |lambda - mu|
    rw [hrewrite]
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- The projective support operator is a contraction with universal modulus `M / R`. -/
theorem confocalNullSupportOperator_contraction
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R d e : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hd : 0 ≤ d) (he : 0 ≤ e) :
    |confocalNullSupportOperator S R d - confocalNullSupportOperator S R e| ≤
      (M / R) * |d - e| := by
  have hlambda1 := confocalProjectiveParameter_le_one hR hd
  have hmu1 := confocalProjectiveParameter_le_one hR he
  have hsupp := confocalNullSupport_lipschitz hne hcone hbound
    hlambda1 hmu1
  have hparam := confocalProjectiveParameter_lipschitz hR hd he
  rw [confocalNullSupportOperator]
  calc
    |confocalNullSupport S (confocalProjectiveParameter R d) -
        confocalNullSupport S (confocalProjectiveParameter R e)| ≤
        2 * M * |confocalProjectiveParameter R d -
          confocalProjectiveParameter R e| := hsupp
    _ ≤ 2 * M * (|d - e| / (2 * R)) :=
      mul_le_mul_of_nonneg_left hparam (by positivity)
    _ = (M / R) * |d - e| := by field_simp [hR.ne']

/-- The realized exterior envelope defect is exactly the fixed point of the ordinary null
support field. -/
theorem confocalEnvelopeDefect_eq_nullSupport_fixedPoint
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R G : ℝ}
    (hM : 0 ≤ M) (hRM : M < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hG : IsLUB (liftedConfocalBranch (R := R) '' S) G) :
    0 ≤ G - R ∧
      G - R = confocalNullSupportOperator S R (G - R) := by
  have hR : 0 < R := hM.trans_lt hRM
  have hqR : ∀ q ∈ S, q.2 < R := fun q hq => (hbound q hq).trans_lt hRM
  rcases hne with ⟨q0, hq0⟩
  have hGR : R ≤ G :=
    (le_liftedConfocalBranch_of_snd_lt_radius (hcone hq0) (hqR q0 hq0)).trans
      (hG.1 ⟨q0, hq0, rfl⟩)
  have hD0 : 0 ≤ G - R := sub_nonneg.mpr hGR
  have hlambda1 := confocalProjectiveParameter_le_one hR hD0
  have hnullLUB : IsLUB
      (confocalNullFunctional
        (lambda := confocalProjectiveParameter R (G - R)) '' S) (G - R) := by
    constructor
    · rintro _ ⟨q, hqS, rfl⟩
      apply (liftedConfocalBranch_le_add_iff_nullFunctional_le
        (hcone hqS) hR (hqR q hqS) hD0).mp
      simpa only [show R + (G - R) = G by ring] using hG.1 ⟨q, hqS, rfl⟩
    · intro b hb
      have hbranchUpper : ∀ y ∈ liftedConfocalBranch (R := R) '' S, y ≤ R + b := by
        rintro _ ⟨q, hqS, rfl⟩
        let dq := liftedConfocalBranch q R - R
        have hdq0 : 0 ≤ dq :=
          sub_nonneg.mpr (le_liftedConfocalBranch_of_snd_lt_radius
            (hcone hqS) (hqR q hqS))
        have hdqD : dq ≤ G - R := by
          dsimp only [dq]
          have := hG.1 ⟨q, hqS, rfl⟩
          linarith
        have hparam : confocalProjectiveParameter R dq ≤
            confocalProjectiveParameter R (G - R) :=
          confocalProjectiveParameter_mono hR hdq0 hdqD
        have hv0 := confocalNullPlus_nonneg (hcone hqS)
        have hself := liftedConfocalBranch_sub_eq_nullFunctional_projective
          (hcone hqS) hR (hqR q hqS)
        have hle : dq ≤ confocalNullFunctional q
            (confocalProjectiveParameter R (G - R)) := by
          change confocalProjectiveParameter R (liftedConfocalBranch q R - R) ≤
            confocalProjectiveParameter R (G - R) at hparam
          change liftedConfocalBranch q R - R ≤
            confocalNullFunctional q (confocalProjectiveParameter R (G - R))
          rw [hself, confocalNullFunctional, confocalNullFunctional]
          have hmul := mul_le_mul_of_nonneg_right hparam hv0
          linarith
        have hqb := hb ⟨q, hqS, rfl⟩
        dsimp only [dq] at hle
        linarith
      have hleast := hG.2 hbranchUpper
      linarith
  refine ⟨hD0, ?_⟩
  rw [confocalNullSupportOperator]
  exact hnullLUB.unique
    (isLUB_confocalNullSupport (Set.nonempty_def.mpr ⟨q0, hq0⟩)
      hcone hbound hlambda1)

/-- The projective null-support equation has at most one nonnegative solution outside the source
radius. -/
theorem confocalNullSupport_fixedPoint_unique
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R d e : ℝ}
    (hM : 0 ≤ M) (hRM : M < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hd0 : 0 ≤ d) (he0 : 0 ≤ e)
    (hd : d = confocalNullSupportOperator S R d)
    (he : e = confocalNullSupportOperator S R e) :
    d = e := by
  have hR : 0 < R := hM.trans_lt hRM
  have hcontract := confocalNullSupportOperator_contraction hne hM hR
    hcone hbound hd0 he0
  rw [← hd, ← he] at hcontract
  have hratio : M / R < 1 := (div_lt_one hR).2 hRM
  have habs : 0 ≤ |d - e| := abs_nonneg _
  have hz : |d - e| = 0 := by nlinarith
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

/-- **Universal fixed-point characterization.**  A scalar is the realized exterior confocal
defect exactly when it is a nonnegative fixed point of the ordinary null support field. -/
theorem confocalEnvelopeDefect_eq_iff_nullSupport_fixedPoint
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R G d : ℝ}
    (hM : 0 ≤ M) (hRM : M < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hG : IsLUB (liftedConfocalBranch (R := R) '' S) G) :
    d = G - R ↔
      0 ≤ d ∧ d = confocalNullSupportOperator S R d := by
  have hactual := confocalEnvelopeDefect_eq_nullSupport_fixedPoint
    hne hM hRM hcone hbound hG
  constructor
  · rintro rfl
    exact hactual
  · rintro ⟨hd0, hd⟩
    exact confocalNullSupport_fixedPoint_unique hne hM hRM hcone hbound
      hd0 hactual.1 hd hactual.2

/-- Uniform stability of exterior confocal fields under perturbation of the complete null support
field. -/
theorem confocalEnvelopeDefect_stability
    {S T : Set (ℝ × ℝ)} (hneS : S.Nonempty) (hneT : T.Nonempty)
    {M R G H epsilon : ℝ}
    (hM : 0 ≤ M) (hRM : M < R)
    (hconeS : S ⊆ confocalLorentzCone)
    (hconeT : T ⊆ confocalLorentzCone)
    (hboundS : ∀ q ∈ S, q.2 ≤ M)
    (hboundT : ∀ q ∈ T, q.2 ≤ M)
    (hG : IsLUB (liftedConfocalBranch (R := R) '' S) G)
    (hH : IsLUB (liftedConfocalBranch (R := R) '' T) H)
    (hsupport : ∀ lambda, 0 ≤ lambda → lambda ≤ 1 →
      |confocalNullSupport S lambda - confocalNullSupport T lambda| ≤ epsilon) :
    |(G - R) - (H - R)| ≤ epsilon / (1 - M / R) := by
  have hR : 0 < R := hM.trans_lt hRM
  have hactualS := confocalEnvelopeDefect_eq_nullSupport_fixedPoint
    hneS hM hRM hconeS hboundS hG
  have hactualT := confocalEnvelopeDefect_eq_nullSupport_fixedPoint
    hneT hM hRM hconeT hboundT hH
  let d := G - R
  let e := H - R
  have hd0 : 0 ≤ d := hactualS.1
  have he0 : 0 ≤ e := hactualT.1
  have hd : d = confocalNullSupportOperator S R d := hactualS.2
  have he : e = confocalNullSupportOperator T R e := hactualT.2
  have hcontract := confocalNullSupportOperator_contraction hneS hM hR
    hconeS hboundS hd0 he0
  have hlambda0 := confocalProjectiveParameter_nonneg hR he0
  have hlambda1 := confocalProjectiveParameter_le_one hR he0
  have hcross := hsupport (confocalProjectiveParameter R e) hlambda0 hlambda1
  have hsum : |d - e| ≤ (M / R) * |d - e| + epsilon := by
    calc
      |d - e| =
          |confocalNullSupportOperator S R d -
            confocalNullSupportOperator T R e| := by rw [← hd, ← he]
      _ ≤ |confocalNullSupportOperator S R d -
              confocalNullSupportOperator S R e| +
            |confocalNullSupportOperator S R e -
              confocalNullSupportOperator T R e| := by
          rw [show confocalNullSupportOperator S R d -
                confocalNullSupportOperator T R e =
              (confocalNullSupportOperator S R d -
                confocalNullSupportOperator S R e) +
              (confocalNullSupportOperator S R e -
                confocalNullSupportOperator T R e) by ring]
          exact abs_add_le _ _
      _ ≤ (M / R) * |d - e| + epsilon := by
          apply add_le_add hcontract
          simpa only [confocalNullSupportOperator] using hcross
  have hden : 0 < 1 - M / R := by
    have : M / R < 1 := (div_lt_one hR).2 hRM
    linarith
  change |d - e| ≤ epsilon / (1 - M / R)
  rw [le_div_iff₀ hden]
  nlinarith

/-- The zero fixed point is exactly the positive Lorentz null ray. -/
theorem confocalEnvelopeDefect_eq_zero_iff_positiveNullRay
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R G : ℝ}
    (hM : 0 ≤ M) (hRM : M < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hG : IsLUB (liftedConfocalBranch (R := R) '' S) G) :
    G - R = 0 ↔ ∀ q ∈ S, q.2 = q.1 := by
  have hR : 0 < R := hM.trans_lt hRM
  have hactual := confocalEnvelopeDefect_eq_nullSupport_fixedPoint
    hne hM hRM hcone hbound hG
  constructor
  · intro hzero q hqS
    have hsupport0 : confocalNullSupport S 0 = 0 := by
      have hfix := hactual.2
      rw [hzero, confocalNullSupportOperator, confocalProjectiveParameter] at hfix
      simpa using hfix.symm
    have hLUB := isLUB_confocalNullSupport hne hcone hbound (lambda := 0)
      (by norm_num)
    have hle : confocalNullFunctional q 0 ≤ 0 := by
      have hqle : confocalNullFunctional q 0 ≤ confocalNullSupport S 0 :=
        hLUB.1 ⟨q, hqS, rfl⟩
      rwa [hsupport0] at hqle
    have hnonneg := confocalNullMinus_nonneg (hcone hqS)
    rw [confocalNullFunctional, zero_mul, add_zero] at hle
    change 0 ≤ q.2 - q.1 at hnonneg
    exact sub_eq_zero.mp (le_antisymm hle hnonneg)
  · intro hnull
    have hconst : IsLUB (liftedConfocalBranch (R := R) '' S) R := by
      constructor
      · rintro _ ⟨q, hqS, rfl⟩
        have hqa : q.2 = q.1 := hnull q hqS
        have hqR : q.2 < R := (hbound q hqS).trans_lt hRM
        have hRqa : 0 ≤ R - q.2 := hqR.le |> sub_nonneg.mpr
        have hbranch : liftedConfocalBranch q R = R := by
          rw [liftedConfocalBranch, ← hqa]
          simp only [sub_self, add_zero]
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hRqa]
          ring
        exact hbranch.le
      · intro b hb
        rcases hne with ⟨q, hqS⟩
        have hqa : q.2 = q.1 := hnull q hqS
        have hqR : q.2 < R := (hbound q hqS).trans_lt hRM
        have hRqa : 0 ≤ R - q.2 := hqR.le |> sub_nonneg.mpr
        have hbranch : liftedConfocalBranch q R = R := by
          rw [liftedConfocalBranch, ← hqa]
          simp only [sub_self, add_zero]
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hRqa]
          ring
        exact hbranch ▸ hb ⟨q, hqS, rfl⟩
    have hGR : G = R := hG.unique hconst
    linarith

@[simp] theorem confocalNullSupport_singleton_positiveNullPoint
    (M lambda : ℝ) :
    confocalNullSupport ({(M, M)} : Set (ℝ × ℝ)) lambda = 2 * M * lambda := by
  simp [confocalNullSupport, confocalNullFunctional, confocalNullMinus, confocalNullPlus]
  ring

@[simp] theorem confocalNullSupportOperator_singleton_positiveNullPoint
    (M R d : ℝ) :
    confocalNullSupportOperator ({(M, M)} : Set (ℝ × ℝ)) R d =
      2 * M * (d / (2 * R + d)) := by
  rw [confocalNullSupportOperator,
    confocalNullSupport_singleton_positiveNullPoint, confocalProjectiveParameter]

/-- The universal modulus `M / R` is optimal: every smaller proposed nonnegative modulus fails
already on a one-point source on the positive null ray. -/
theorem confocalNullSupportOperator_contraction_modulus_optimal
    {M R c : ℝ} (hM : 0 < M) (hRM : M < R)
    (hc0 : 0 ≤ c) (hc : c < M / R) :
    ∃ d e : ℝ, 0 ≤ d ∧ 0 ≤ e ∧
      c * |d - e| <
        |confocalNullSupportOperator ({(M, M)} : Set (ℝ × ℝ)) R d -
          confocalNullSupportOperator ({(M, M)} : Set (ℝ × ℝ)) R e| := by
  have hR : 0 < R := hM.trans hRM
  have hgap : 0 < M - c * R := by
    have hcR : c * R < M := (lt_div_iff₀ hR).mp hc
    linarith
  let e : ℝ := (M - c * R) / (c + 1)
  have hc1 : 0 < c + 1 := by linarith
  have he : 0 < e := by
    dsimp only [e]
    positivity
  have hce : c * e < M - c * R := by
    have hratio : c / (c + 1) < 1 := (div_lt_one hc1).2 (by linarith)
    calc
      c * e = (c / (c + 1)) * (M - c * R) := by
        dsimp only [e]
        field_simp [hc1.ne']
      _ < 1 * (M - c * R) := mul_lt_mul_of_pos_right hratio hgap
      _ = M - c * R := one_mul _
  have hcore : c * (2 * R + e) < 2 * M := by nlinarith
  have hden : 0 < 2 * R + e := by positivity
  have hquot : c * e < 2 * M * (e / (2 * R + e)) := by
    rw [show 2 * M * (e / (2 * R + e)) = (2 * M * e) / (2 * R + e) by ring]
    rw [lt_div_iff₀ hden]
    have hmul := mul_lt_mul_of_pos_right hcore he
    nlinarith
  refine ⟨e, 0, he.le, le_rfl, ?_⟩
  rw [confocalNullSupportOperator_singleton_positiveNullPoint,
    confocalNullSupportOperator_singleton_positiveNullPoint]
  simp only [zero_div, mul_zero, sub_zero]
  rw [abs_of_pos he]
  have hpositive : 0 < 2 * M * (e / (2 * R + e)) := by positivity
  rw [abs_of_pos hpositive]
  exact hquot

/-- On a radius domain lying strictly outside a fixed source bound, membership in the confocal
hull is exactly membership in the projectively selected null half-spaces.  This is the
bound-aware projective form of the maximal confocal completion. -/
theorem mem_confocalHullOfField_add_defect_iff_nullFunctional_le
    {D : Set ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hD : ∀ R ∈ D, M < R) {d : ℝ → ℝ}
    (hd : ∀ R ∈ D, 0 ≤ d R) {q : ℝ × ℝ} (hqM : q.2 ≤ M) :
    q ∈ confocalHullOfField D (fun R => R + d R) ↔
      q ∈ confocalLorentzCone ∧
        ∀ R ∈ D,
          confocalNullFunctional q (confocalProjectiveParameter R (d R)) ≤ d R := by
  constructor
  · rintro ⟨hqCone, hqField⟩
    refine ⟨hqCone, ?_⟩
    intro R hRD
    have hR : 0 < R := hM.trans_lt (hD R hRD)
    have hqR : q.2 < R := hqM.trans_lt (hD R hRD)
    exact (liftedConfocalBranch_le_add_iff_nullFunctional_le
      hqCone hR hqR (hd R hRD)).mp (hqField R hRD)
  · rintro ⟨hqCone, hqNull⟩
    refine ⟨hqCone, ?_⟩
    intro R hRD
    have hR : 0 < R := hM.trans_lt (hD R hRD)
    have hqR : q.2 < R := hqM.trans_lt (hD R hRD)
    exact (liftedConfocalBranch_le_add_iff_nullFunctional_le
      hqCone hR hqR (hd R hRD)).mpr (hqNull R hRD)

/-- The bounded part of a confocal hull is the intersection of its projectively selected null
half-spaces. -/
theorem confocalHullOfField_inter_snd_le_eq_projectiveNullHalfspaces
    {D : Set ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hD : ∀ R ∈ D, M < R) {d : ℝ → ℝ}
    (hd : ∀ R ∈ D, 0 ≤ d R) :
    confocalHullOfField D (fun R => R + d R) ∩ {q | q.2 ≤ M} =
      {q | q ∈ confocalLorentzCone ∧ q.2 ≤ M ∧
        ∀ R ∈ D,
          confocalNullFunctional q (confocalProjectiveParameter R (d R)) ≤ d R} := by
  ext q
  constructor
  · rintro ⟨hqHull, hqM⟩
    have hprojective :=
      (mem_confocalHullOfField_add_defect_iff_nullFunctional_le
        hM hD hd hqM).mp hqHull
    exact ⟨hprojective.1, hqM, hprojective.2⟩
  · rintro ⟨hqCone, hqM, hqNull⟩
    refine ⟨?_, hqM⟩
    exact (mem_confocalHullOfField_add_defect_iff_nullFunctional_le
      hM hD hd hqM).mpr ⟨hqCone, hqNull⟩

/-- Radius reconstructed from a positive projective direction and its support value. -/
def confocalRadiusFromProjective (lambda d : ℝ) : ℝ :=
  d * (1 - lambda) / (2 * lambda)

/-- The projective radius reconstruction is inverse to the defect parameter. -/
theorem confocalProjectiveParameter_radiusFromProjective
    {lambda d : ℝ} (hlambda0 : 0 < lambda) (hd : 0 < d) :
    confocalProjectiveParameter (confocalRadiusFromProjective lambda d) d = lambda := by
  rw [confocalProjectiveParameter, confocalRadiusFromProjective]
  field_simp [hlambda0.ne', hd.ne']
  ring

/-- Conversely, a positive radius and positive defect are recovered from their projective
parameter. -/
theorem confocalRadiusFromProjective_projectiveParameter
    {R d : ℝ} (hR : 0 < R) (hd : 0 < d) :
    confocalRadiusFromProjective (confocalProjectiveParameter R d) d = R := by
  rw [confocalRadiusFromProjective, confocalProjectiveParameter]
  have hden : 0 < 2 * R + d := by positivity
  field_simp [hden.ne', hd.ne']
  ring

/-- The null support field is monotone in its projective direction whenever the larger parameter is
at most one; no lower bound on either parameter is needed. -/
theorem confocalNullSupport_mono
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M lambda mu : ℝ}
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hlambdaMu : lambda ≤ mu) (hmu1 : mu ≤ 1) :
    confocalNullSupport S lambda ≤ confocalNullSupport S mu := by
  have hlambda1 : lambda ≤ 1 := hlambdaMu.trans hmu1
  have hLlambda := isLUB_confocalNullSupport hne hcone hbound hlambda1
  have hLmu := isLUB_confocalNullSupport hne hcone hbound hmu1
  apply hLlambda.2
  rintro _ ⟨q, hqS, rfl⟩
  have hv0 := confocalNullPlus_nonneg (hcone hqS)
  have hmul : lambda * confocalNullPlus q ≤ mu * confocalNullPlus q :=
    mul_le_mul_of_nonneg_right hlambdaMu hv0
  have hqmu : confocalNullFunctional q mu ≤ confocalNullSupport S mu :=
    hLmu.1 ⟨q, hqS, rfl⟩
  change confocalNullMinus q + mu * confocalNullPlus q ≤
    confocalNullSupport S mu at hqmu
  change confocalNullMinus q + lambda * confocalNullPlus q ≤
    confocalNullSupport S mu
  linarith

/-- The radius chart obtained by feeding a null-support value into the inverse projective map. -/
def confocalNullSupportRadius (S : Set (ℝ × ℝ)) (lambda : ℝ) : ℝ :=
  confocalRadiusFromProjective lambda (confocalNullSupport S lambda)

/-- The exterior defect graph of a field above a source-radius bound. -/
def confocalExteriorDefectGraph (M : ℝ) (G : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | M < p.1 ∧ p.2 = G p.1 - p.1}

/-- The admissible projective support graph above a source-radius bound. -/
def confocalProjectiveSupportGraph (S : Set (ℝ × ℝ)) (M : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ lambda : ℝ,
    0 < lambda ∧ lambda < 1 ∧
    0 < confocalNullSupport S lambda ∧
    M < confocalNullSupportRadius S lambda ∧
    p.1 = confocalNullSupportRadius S lambda ∧
    p.2 = confocalNullSupport S lambda}

/-- **Global projective support--envelope duality.**  Away from the exact positive-null radical,
the complete exterior confocal defect graph is exactly the rational projective image of the
ordinary null-support graph.  This is a global classification, not merely a pointwise fixed-point
identity. -/
theorem confocalExteriorDefectGraph_eq_projectiveSupportGraph
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    {G : ℝ → ℝ}
    (hG : IsConfocalEnvelopeOn {R | M < R} S G)
    (hnonradical : 0 < confocalNullSupport S 0) :
    confocalExteriorDefectGraph M G = confocalProjectiveSupportGraph S M := by
  ext p
  constructor
  · rintro ⟨hMR, hpDefect⟩
    let R := p.1
    let d := G R - R
    let lambda := confocalProjectiveParameter R d
    have hR : 0 < R := hM.trans_lt hMR
    have hLUB : IsLUB (liftedConfocalBranch (R := R) '' S) (G R) :=
      hG R hMR
    have hfixed := confocalEnvelopeDefect_eq_nullSupport_fixedPoint
      hne hM hMR hcone hbound hLUB
    have hd0 : 0 ≤ d := hfixed.1
    have hlambda0 : 0 ≤ lambda := confocalProjectiveParameter_nonneg hR hd0
    have hlambda1le : lambda ≤ 1 := confocalProjectiveParameter_le_one hR hd0
    have hsupport : d = confocalNullSupport S lambda := by
      simpa only [d, lambda, confocalNullSupportOperator] using hfixed.2
    have hsupport0le : confocalNullSupport S 0 ≤ confocalNullSupport S lambda :=
      confocalNullSupport_mono hne hcone hbound hlambda0 hlambda1le
    have hd : 0 < d := by
      rw [hsupport]
      exact hnonradical.trans_le hsupport0le
    have hlambdaPos : 0 < lambda := by
      dsimp only [lambda]
      rw [confocalProjectiveParameter]
      positivity
    have hlambdaLt : lambda < 1 := by
      dsimp only [lambda]
      rw [confocalProjectiveParameter]
      apply (div_lt_one (by positivity)).2
      linarith
    have hRadius : confocalNullSupportRadius S lambda = R := by
      rw [confocalNullSupportRadius, ← hsupport]
      exact confocalRadiusFromProjective_projectiveParameter hR hd
    refine ⟨lambda, hlambdaPos, hlambdaLt, ?_, ?_, ?_, ?_⟩
    · rwa [← hsupport]
    · rwa [hRadius]
    · exact hRadius.symm
    · calc
        p.2 = d := hpDefect
        _ = confocalNullSupport S lambda := hsupport
  · rintro ⟨lambda, hlambda0, hlambda1, hsupport0, hMRadius, hpRadius, hpSupport⟩
    let R := confocalNullSupportRadius S lambda
    let d := confocalNullSupport S lambda
    have hR : 0 < R := hM.trans_lt hMRadius
    have hprojective : confocalProjectiveParameter R d = lambda := by
      dsimp only [R, d, confocalNullSupportRadius]
      exact confocalProjectiveParameter_radiusFromProjective
        hlambda0 hsupport0
    have hfix : d = confocalNullSupportOperator S R d := by
      rw [confocalNullSupportOperator, hprojective]
    have hLUB : IsLUB (liftedConfocalBranch (R := R) '' S) (G R) :=
      hG R hMRadius
    have hactual : d = G R - R :=
      (confocalEnvelopeDefect_eq_iff_nullSupport_fixedPoint
        hne hM hMRadius hcone hbound hLUB).2 ⟨hsupport0.le, hfix⟩
    constructor
    · rwa [hpRadius]
    · calc
        p.2 = d := hpSupport
        _ = G R - R := hactual
        _ = G p.1 - p.1 := by rw [hpRadius]

/-- The projective support radius is one-to-one on the complete exterior chart.  Hence the field
radius and the selected projective direction recover one another without a presentation choice. -/
theorem confocalNullSupportRadius_injective_on_exterior
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    {G : ℝ → ℝ}
    (hG : IsConfocalEnvelopeOn {R | M < R} S G)
    (hnonradical : 0 < confocalNullSupport S 0)
    {lambda mu : ℝ}
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (hmu0 : 0 < mu) (hmu1 : mu < 1)
    (hMlambda : M < confocalNullSupportRadius S lambda)
    (hMmu : M < confocalNullSupportRadius S mu)
    (hRadius : confocalNullSupportRadius S lambda = confocalNullSupportRadius S mu) :
    lambda = mu := by
  have hsupportLambda : 0 < confocalNullSupport S lambda := by
    have hmono := confocalNullSupport_mono hne hcone hbound
      hlambda0.le hlambda1.le
    exact hnonradical.trans_le hmono
  have hsupportMu : 0 < confocalNullSupport S mu := by
    have hmono := confocalNullSupport_mono hne hcone hbound
      hmu0.le hmu1.le
    exact hnonradical.trans_le hmono
  have hGraph := confocalExteriorDefectGraph_eq_projectiveSupportGraph
    hne hM hcone hbound hG hnonradical
  have hLambda :
      (confocalNullSupportRadius S lambda, confocalNullSupport S lambda) ∈
        confocalExteriorDefectGraph M G := by
    rw [hGraph]
    exact ⟨lambda, hlambda0, hlambda1, hsupportLambda, hMlambda, rfl, rfl⟩
  have hMu :
      (confocalNullSupportRadius S mu, confocalNullSupport S mu) ∈
        confocalExteriorDefectGraph M G := by
    rw [hGraph]
    exact ⟨mu, hmu0, hmu1, hsupportMu, hMmu, rfl, rfl⟩
  have hsupportEq : confocalNullSupport S lambda = confocalNullSupport S mu := by
    have hLambdaDefect := hLambda.2
    have hMuDefect := hMu.2
    rw [hRadius] at hLambdaDefect
    exact hLambdaDefect.trans hMuDefect.symm
  have hprojectiveLambda :
      confocalProjectiveParameter (confocalNullSupportRadius S lambda)
        (confocalNullSupport S lambda) = lambda := by
    rw [confocalNullSupportRadius]
    exact confocalProjectiveParameter_radiusFromProjective
      hlambda0 hsupportLambda
  have hprojectiveMu :
      confocalProjectiveParameter (confocalNullSupportRadius S mu)
        (confocalNullSupport S mu) = mu := by
    rw [confocalNullSupportRadius]
    exact confocalProjectiveParameter_radiusFromProjective hmu0 hsupportMu
  rw [hRadius, hsupportEq] at hprojectiveLambda
  exact hprojectiveLambda.symm.trans hprojectiveMu

/-- Two bounded sources realizing the same exterior value have the same support value at the
projective direction selected by that value.  This is the presentation-independent support
trace carried by the common field. -/
theorem confocalNullSupport_eq_on_common_exterior_trace
    {S T : Set (ℝ × ℝ)} (hneS : S.Nonempty) (hneT : T.Nonempty)
    {M R G : ℝ} (hM : 0 ≤ M) (hRM : M < R)
    (hconeS : S ⊆ confocalLorentzCone)
    (hconeT : T ⊆ confocalLorentzCone)
    (hboundS : ∀ q ∈ S, q.2 ≤ M)
    (hboundT : ∀ q ∈ T, q.2 ≤ M)
    (hGS : IsLUB (liftedConfocalBranch (R := R) '' S) G)
    (hGT : IsLUB (liftedConfocalBranch (R := R) '' T) G) :
    confocalNullSupport S (confocalProjectiveParameter R (G - R)) = G - R ∧
      confocalNullSupport T (confocalProjectiveParameter R (G - R)) = G - R := by
  have hS := confocalEnvelopeDefect_eq_nullSupport_fixedPoint
    hneS hM hRM hconeS hboundS hGS
  have hT := confocalEnvelopeDefect_eq_nullSupport_fixedPoint
    hneT hM hRM hconeT hboundT hGT
  constructor
  · simpa only [confocalNullSupportOperator] using hS.2.symm
  · simpa only [confocalNullSupportOperator] using hT.2.symm

/-- At projective parameter zero, the null support of a complex Lorentz lift is exactly the
transverse-defect envelope. -/
theorem confocalNullSupport_lorentzLift_zero_eq_transverseDefectEnvelope
    (S : Set ℂ) :
    confocalNullSupport (confocalLorentzLift '' S) 0 = transverseDefectEnvelope S := by
  rw [confocalNullSupport, transverseDefectEnvelope]
  congr 1
  ext y
  constructor
  · rintro ⟨q, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by
      simp [confocalNullFunctional, confocalNullMinus, confocalLorentzLift,
        transverseDefect]⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨confocalLorentzLift z, ⟨z, hz, rfl⟩, by
      simp [confocalNullFunctional, confocalNullMinus, confocalLorentzLift,
        transverseDefect]⟩

/-- For a bounded complex source, its ordinary confocal defect envelope is exactly the unique
nonnegative fixed point of the null-support operator of its Lorentz lift. -/
theorem complexConfocalDefectEnvelope_eq_iff_nullSupport_fixedPoint
    {S : Set ℂ} (hne : S.Nonempty) {M R d : ℝ}
    (hM : 0 ≤ M) (hRM : M < R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    d = confocalDefectEnvelope S R ↔
      0 ≤ d ∧ d =
        confocalNullSupportOperator (confocalLorentzLift '' S) R d := by
  have hR : 0 < R := hM.trans_lt hRM
  have hneLift : (confocalLorentzLift '' S).Nonempty := hne.image _
  have hcone : confocalLorentzLift '' S ⊆ confocalLorentzCone := by
    rintro _ ⟨z, hz, rfl⟩
    exact confocalLorentzLift_mem z
  have hboundLift : ∀ q ∈ confocalLorentzLift '' S, q.2 ≤ M := by
    rintro _ ⟨z, hz, rfl⟩
    exact hbound z hz
  have hfield := isConfocalEnvelopeOn_confocalLorentzLift_image
    hne hbound (D := {R}) (by
      intro r hr
      rw [Set.mem_singleton_iff] at hr
      subst r
      exact hR)
  have hG : IsLUB
      (liftedConfocalBranch (R := R) '' (confocalLorentzLift '' S))
      (R + confocalDefectEnvelope S R) := by
    have hAtR := hfield R (by simp)
    have hupper : confocalUpperField S R = R + confocalDefectEnvelope S R := by
      rw [confocalUpperField, confocalAmplitudeEnvelope]
      field_simp [hR.ne']
    rwa [hupper] at hAtR
  simpa using confocalEnvelopeDefect_eq_iff_nullSupport_fixedPoint
    hneLift hM hRM hcone hboundLift hG

section AxialInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every point of a real inner-product space has a canonical two-dimensional axial Lorentz
lift relative to a unit direction. -/
def axialLorentzLift (axis z : E) : ℝ × ℝ :=
  (inner ℝ z axis, ‖z‖)

/-- Distance-sum branch with foci `0` and `R * axis` in an arbitrary real inner-product space. -/
def axialDistanceSumBranch (axis z : E) (R : ℝ) : ℝ :=
  ‖z‖ + ‖R • axis - z‖

theorem axialLorentzLift_mem_confocalLorentzCone
    {axis z : E} (haxis : ‖axis‖ = 1) :
    axialLorentzLift axis z ∈ confocalLorentzCone := by
  rw [axialLorentzLift, confocalLorentzCone, Set.mem_setOf_eq]
  simpa only [haxis, mul_one] using abs_real_inner_le_norm z axis

/-- The axial distance-sum branch in every real inner-product space is exactly the same lifted
Lorentz branch. -/
theorem liftedConfocalBranch_axialLorentzLift
    {axis z : E} (haxis : ‖axis‖ = 1) {R : ℝ} (hR : 0 < R) :
    liftedConfocalBranch (axialLorentzLift axis z) R =
      axialDistanceSumBranch axis z R := by
  have hnormsq : ‖R • axis - z‖ ^ (2 : ℕ) =
      R ^ (2 : ℕ) - 2 * R * inner ℝ z axis + ‖z‖ ^ (2 : ℕ) := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hR, haxis,
      mul_one, real_inner_smul_left, real_inner_comm axis z]
    ring
  rw [liftedConfocalBranch, axialLorentzLift, axialDistanceSumBranch]
  have hrad :
      (R - inner ℝ z axis) ^ (2 : ℕ) + (‖z‖ ^ (2 : ℕ) - (inner ℝ z axis) ^ (2 : ℕ)) =
        ‖R • axis - z‖ ^ (2 : ℕ) := by
    rw [hnormsq]
    ring
  rw [hrad, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- **Dimension-free projective null-support law.**  Any bounded source in any real
inner-product space is classified by the same one-dimensional fixed-point equation after its
canonical axial Lorentz lift. -/
theorem axialEnvelopeDefect_eq_iff_nullSupport_fixedPoint
    {axis : E} (haxis : ‖axis‖ = 1)
    {S : Set E} (hne : S.Nonempty) {M R G d : ℝ}
    (hM : 0 ≤ M) (hRM : M < R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M)
    (hG : IsLUB ((fun z => axialDistanceSumBranch axis z R) '' S) G) :
    d = G - R ↔
      0 ≤ d ∧ d =
        confocalNullSupportOperator (axialLorentzLift axis '' S) R d := by
  have hR : 0 < R := hM.trans_lt hRM
  have hneLift : (axialLorentzLift axis '' S).Nonempty := hne.image _
  have hcone : axialLorentzLift axis '' S ⊆ confocalLorentzCone := by
    rintro _ ⟨z, hz, rfl⟩
    exact axialLorentzLift_mem_confocalLorentzCone haxis
  have hboundLift : ∀ q ∈ axialLorentzLift axis '' S, q.2 ≤ M := by
    rintro _ ⟨z, hz, rfl⟩
    exact hbound z hz
  have himage :
      liftedConfocalBranch (R := R) '' (axialLorentzLift axis '' S) =
        (fun z => axialDistanceSumBranch axis z R) '' S := by
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, (liftedConfocalBranch_axialLorentzLift haxis hR).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨axialLorentzLift axis z, ⟨z, hz, rfl⟩,
        liftedConfocalBranch_axialLorentzLift haxis hR⟩
  apply confocalEnvelopeDefect_eq_iff_nullSupport_fixedPoint
    hneLift hM hRM hcone hboundLift
  rwa [himage]

end AxialInnerProductSpace

end

end HTGeometry
