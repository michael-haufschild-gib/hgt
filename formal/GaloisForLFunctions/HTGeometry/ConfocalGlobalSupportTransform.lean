import GaloisForLFunctions.HTGeometry.ConfocalNullSupportFixedPoint

/-!
# Global confocal support transform

The exterior contraction chart of `ConfocalNullSupportFixedPoint` is not the domain of the
projective support law.  This file proves the all-positive-radius theorem.  The realized confocal
defect is the greatest nonnegative fixed point of the null support operator; positive fixed points
are unique; and the complete positive defect graph is the rational projective image of the null
support graph.
-/

namespace HTGeometry

noncomputable section

open scoped Real

/-- The canonical all-radius upper envelope of a scalar Lorentz source. -/
def confocalGlobalEnvelope (S : Set (ℝ × ℝ)) (R : ℝ) : ℝ :=
  sSup (liftedConfocalBranch (R := R) '' S)

/-- The canonical all-radius confocal defect. -/
def confocalGlobalDefect (S : Set (ℝ × ℝ)) (R : ℝ) : ℝ :=
  confocalGlobalEnvelope S R - R

/-- Every Lorentz branch lies above the observation radius, with no exterior assumption. -/
theorem le_liftedConfocalBranch
    {q : ℝ × ℝ} (hq : q ∈ confocalLorentzCone) (R : ℝ) :
    R ≤ liftedConfocalBranch q R := by
  by_cases hqR : q.2 < R
  · exact le_liftedConfocalBranch_of_snd_lt_radius hq hqR
  · have hRq : R ≤ q.2 := le_of_not_gt hqR
    rw [liftedConfocalBranch]
    nlinarith [Real.sqrt_nonneg ((R - q.1) ^ 2 + (q.2 ^ 2 - q.1 ^ 2))]

/-- The exact general-radius hypothesis behind projective linearization is only that the proposed
sublevel lies above the source height. -/
theorem liftedConfocalBranch_le_add_iff_nullFunctional_le_of_snd_le_add
    {q : ℝ × ℝ} (hq : q ∈ confocalLorentzCone)
    {R d : ℝ} (hR : 0 < R) (hd : 0 ≤ d) (haL : q.2 ≤ R + d) :
    liftedConfocalBranch q R ≤ R + d ↔
      confocalNullFunctional q (confocalProjectiveParameter R d) ≤ d := by
  have hden : 0 < 2 * R + d := by positivity
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

/-- A branch defect is its own projectively selected null functional at every positive radius. -/
theorem liftedConfocalBranch_sub_eq_nullFunctional_projective_global
    {q : ℝ × ℝ} (hq : q ∈ confocalLorentzCone)
    {R : ℝ} (hR : 0 < R) :
    liftedConfocalBranch q R - R =
      confocalNullFunctional q
        (confocalProjectiveParameter R (liftedConfocalBranch q R - R)) := by
  have hd : 0 ≤ liftedConfocalBranch q R - R :=
    sub_nonneg.mpr (le_liftedConfocalBranch hq R)
  have hden : 0 < 2 * R + (liftedConfocalBranch q R - R) := by positivity
  have hself := liftedConfocalBranch_halfspace_self hq R
  rw [confocalNullFunctional, confocalProjectiveParameter,
    confocalNullMinus, confocalNullPlus]
  field_simp [hden.ne']
  nlinarith

private theorem liftedConfocalBranch_le_radius_add_two_mul_bound
    {q : ℝ × ℝ} (hq : q ∈ confocalLorentzCone)
    {M R : ℝ} (hM : 0 ≤ M) (hR : 0 < R) (hqM : q.2 ≤ M) :
    liftedConfocalBranch q R ≤ R + 2 * M := by
  have ha0 : 0 ≤ q.2 := (abs_nonneg q.1).trans hq
  have hxneg : -q.1 ≤ q.2 := (neg_le_abs q.1).trans hq
  have hrad := liftedConfocalRadicand_nonneg hq R
  have hrad_le :
      (R - q.1) ^ 2 + (q.2 ^ 2 - q.1 ^ 2) ≤ (R + M) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ R by positivity) (sub_nonneg.mpr hxneg),
      mul_nonneg (show 0 ≤ R by positivity) (sub_nonneg.mpr hqM),
      sq_nonneg (M - q.2)]
  have hsqrt2 := Real.sq_sqrt hrad
  have hsqrt0 := Real.sqrt_nonneg
    ((R - q.1) ^ 2 + (q.2 ^ 2 - q.1 ^ 2))
  have hRM0 : 0 ≤ R + M := by positivity
  have hsqrt_le :
      Real.sqrt ((R - q.1) ^ 2 + (q.2 ^ 2 - q.1 ^ 2)) ≤ R + M := by
    nlinarith [sq_nonneg
      (Real.sqrt ((R - q.1) ^ 2 + (q.2 ^ 2 - q.1 ^ 2)) - (R + M))]
  rw [liftedConfocalBranch]
  linarith

private theorem bddAbove_liftedConfocalBranch_image
    {S : Set (ℝ × ℝ)} {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M) :
    BddAbove (liftedConfocalBranch (R := R) '' S) := by
  refine ⟨R + 2 * M, ?_⟩
  rintro _ ⟨q, hqS, rfl⟩
  exact liftedConfocalBranch_le_radius_add_two_mul_bound
    (hcone hqS) hM hR (hbound q hqS)

/-- The canonical global envelope is the least upper bound of the branch family. -/
theorem isLUB_confocalGlobalEnvelope
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M) :
    IsLUB (liftedConfocalBranch (R := R) '' S)
      (confocalGlobalEnvelope S R) := by
  exact isLUB_csSup (hne.image _) <|
    bddAbove_liftedConfocalBranch_image hM hR hcone hbound

/-- The realized defect is a null-support fixed point at every positive radius. -/
theorem confocalEnvelopeDefect_eq_nullSupport_fixedPoint_global
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R G : ℝ}
    (hR : 0 < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hG : IsLUB (liftedConfocalBranch (R := R) '' S) G) :
    0 ≤ G - R ∧
      G - R = confocalNullSupportOperator S R (G - R) := by
  rcases hne with ⟨q0, hq0⟩
  have hRG : R ≤ G :=
    (le_liftedConfocalBranch (hcone hq0) R).trans
      (hG.1 ⟨q0, hq0, rfl⟩)
  have hD0 : 0 ≤ G - R := sub_nonneg.mpr hRG
  have hlambda1 := confocalProjectiveParameter_le_one hR hD0
  have hnullLUB := isLUB_confocalNullSupport
    (Set.nonempty_def.mpr ⟨q0, hq0⟩) hcone hbound hlambda1
  have hsupport_le :
      confocalNullSupport S (confocalProjectiveParameter R (G - R)) ≤ G - R := by
    apply hnullLUB.2
    rintro _ ⟨q, hqS, rfl⟩
    have hqBranch : liftedConfocalBranch q R ≤ G :=
      hG.1 ⟨q, hqS, rfl⟩
    have hqa : q.2 ≤ G := by
      rw [liftedConfocalBranch] at hqBranch
      nlinarith [Real.sqrt_nonneg
        ((R - q.1) ^ 2 + (q.2 ^ 2 - q.1 ^ 2))]
    have hqa' : q.2 ≤ R + (G - R) := by linarith
    apply (liftedConfocalBranch_le_add_iff_nullFunctional_le_of_snd_le_add
      (hcone hqS) hR hD0 hqa').mp
    linarith
  have hdefect_le :
      G - R ≤ confocalNullSupport S (confocalProjectiveParameter R (G - R)) := by
    have hbranchUpper :
        ∀ y ∈ liftedConfocalBranch (R := R) '' S,
          y ≤ R + confocalNullSupport S (confocalProjectiveParameter R (G - R)) := by
      rintro _ ⟨q, hqS, rfl⟩
      let dq := liftedConfocalBranch q R - R
      have hdq0 : 0 ≤ dq :=
        sub_nonneg.mpr (le_liftedConfocalBranch (hcone hqS) R)
      have hdqD : dq ≤ G - R := by
        dsimp only [dq]
        have := hG.1 ⟨q, hqS, rfl⟩
        linarith
      have hparam : confocalProjectiveParameter R dq ≤
          confocalProjectiveParameter R (G - R) :=
        confocalProjectiveParameter_mono hR hdq0 hdqD
      have hself := liftedConfocalBranch_sub_eq_nullFunctional_projective_global
        (hcone hqS) hR
      have hv0 := confocalNullPlus_nonneg (hcone hqS)
      have hqSupport :
          confocalNullFunctional q (confocalProjectiveParameter R (G - R)) ≤
            confocalNullSupport S (confocalProjectiveParameter R (G - R)) :=
        hnullLUB.1 ⟨q, hqS, rfl⟩
      have hdqSupport : dq ≤
          confocalNullSupport S (confocalProjectiveParameter R (G - R)) := by
        have hmul := mul_le_mul_of_nonneg_right hparam hv0
        have hfunctional :
            confocalNullFunctional q (confocalProjectiveParameter R dq) ≤
              confocalNullFunctional q (confocalProjectiveParameter R (G - R)) := by
          rw [confocalNullFunctional, confocalNullFunctional]
          linarith
        calc
          dq = confocalNullFunctional q (confocalProjectiveParameter R dq) := by
            simpa only [dq] using hself
          _ ≤ confocalNullFunctional q (confocalProjectiveParameter R (G - R)) :=
            hfunctional
          _ ≤ confocalNullSupport S (confocalProjectiveParameter R (G - R)) :=
            hqSupport
      dsimp only [dq] at hdqSupport
      linarith
    have hGle := hG.2 hbranchUpper
    linarith
  refine ⟨hD0, ?_⟩
  rw [confocalNullSupportOperator]
  exact le_antisymm hdefect_le hsupport_le

/-- Canonical all-radius fixed-point identity. -/
theorem confocalGlobalDefect_eq_nullSupport_fixedPoint
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M) :
    0 ≤ confocalGlobalDefect S R ∧
      confocalGlobalDefect S R =
        confocalNullSupportOperator S R (confocalGlobalDefect S R) := by
  exact confocalEnvelopeDefect_eq_nullSupport_fixedPoint_global
    hne hR hcone hbound
      (isLUB_confocalGlobalEnvelope hne hM hR hcone hbound)

/-- The projective parameter is strictly increasing on nonnegative defects. -/
theorem confocalProjectiveParameter_strictMono
    {R d e : ℝ} (hR : 0 < R) (hd : 0 ≤ d) (hde : d < e) :
    confocalProjectiveParameter R d < confocalProjectiveParameter R e := by
  have he : 0 < e := hd.trans_lt hde
  rw [confocalProjectiveParameter, confocalProjectiveParameter]
  apply (div_lt_div_iff₀ (by positivity : 0 < 2 * R + d)
    (by positivity : 0 < 2 * R + e)).2
  nlinarith

private theorem scaled_nullFunctional_gap
    {q : ℝ × ℝ} (hq : q ∈ confocalLorentzCone)
    {lambda mu : ℝ} (hlambda0 : 0 < lambda) (hlambdaMu : lambda < mu)
    (hmu1 : mu < 1) :
    ((1 - mu) / (2 * mu) + (mu - lambda) / 2) *
        confocalNullFunctional q mu ≤
      ((1 - lambda) / (2 * lambda)) * confocalNullFunctional q lambda := by
  have hu0 := confocalNullMinus_nonneg hq
  have hv0 := confocalNullPlus_nonneg hq
  have hmu0 : 0 < mu := hlambda0.trans hlambdaMu
  have hlamu : 0 < lambda * mu := mul_pos hlambda0 hmu0
  have hlamu1 : lambda * mu < 1 := by
    have hlambda1 : lambda < 1 := hlambdaMu.trans hmu1
    nlinarith [mul_lt_mul_of_pos_left hmu1 hlambda0,
      mul_lt_mul_of_pos_right hlambda1 hmu0]
  have hgapU :
      0 ≤ ((mu - lambda) * (1 - lambda * mu) / (2 * lambda * mu)) *
        confocalNullMinus q := by positivity
  have hgapV :
      0 ≤ (((mu - lambda) * (1 - mu)) / 2) * confocalNullPlus q := by positivity
  have hid :
      ((1 - lambda) / (2 * lambda)) * confocalNullFunctional q lambda -
          ((1 - mu) / (2 * mu) + (mu - lambda) / 2) *
            confocalNullFunctional q mu =
        ((mu - lambda) * (1 - lambda * mu) / (2 * lambda * mu)) *
            confocalNullMinus q +
          (((mu - lambda) * (1 - mu)) / 2) * confocalNullPlus q := by
    rw [confocalNullFunctional, confocalNullFunctional]
    field_simp [hlambda0.ne', hmu0.ne']
    ring
  rw [← sub_nonneg]
  rw [hid]
  exact add_nonneg hgapU hgapV

/-- The support-radius chart is strictly decreasing wherever the later support value is positive. -/
theorem confocalNullSupportRadius_strictAnti_of_support_pos
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M lambda mu : ℝ}
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hlambda0 : 0 < lambda) (hlambdaMu : lambda < mu) (hmu1 : mu < 1)
    (hsupportMu : 0 < confocalNullSupport S mu) :
    confocalNullSupportRadius S mu < confocalNullSupportRadius S lambda := by
  have hmu0 : 0 < mu := hlambda0.trans hlambdaMu
  have hlambda1 : lambda < 1 := hlambdaMu.trans hmu1
  have hLlambda := isLUB_confocalNullSupport hne hcone hbound
    hlambda1.le
  have hLmu := isLUB_confocalNullSupport hne hcone hbound hmu1.le
  let cMu := (1 - mu) / (2 * mu)
  let delta := (mu - lambda) / 2
  let cLambda := (1 - lambda) / (2 * lambda)
  have hcMu : 0 < cMu := by dsimp only [cMu]; positivity
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hcLambda : 0 < cLambda := by dsimp only [cLambda]; positivity
  have hden : 0 < cMu + delta := add_pos hcMu hdelta
  have hscaled :
      (cMu + delta) * confocalNullSupport S mu ≤
        cLambda * confocalNullSupport S lambda := by
    have hupper : ∀ x ∈ confocalNullFunctional (lambda := mu) '' S,
        x ≤ (cLambda * confocalNullSupport S lambda) / (cMu + delta) := by
      rintro _ ⟨q, hqS, rfl⟩
      have hgap := scaled_nullFunctional_gap (hcone hqS)
        hlambda0 hlambdaMu hmu1
      have hgap' :
          (cMu + delta) * confocalNullFunctional q mu ≤
            cLambda * confocalNullFunctional q lambda := by
        simpa only [cMu, delta, cLambda] using hgap
      have hqLambda : confocalNullFunctional q lambda ≤
          confocalNullSupport S lambda := hLlambda.1 ⟨q, hqS, rfl⟩
      have hmul := mul_le_mul_of_nonneg_left hqLambda hcLambda.le
      have hcore := hgap'.trans hmul
      exact (le_div_iff₀ hden).2 (by simpa only [mul_comm] using hcore)
    have hleast := hLmu.2 hupper
    simpa only [mul_comm] using (le_div_iff₀ hden).1 hleast
  have hstrict :
      cMu * confocalNullSupport S mu <
        (cMu + delta) * confocalNullSupport S mu := by
    nlinarith
  have hfinal := hstrict.trans_le hscaled
  calc
    confocalNullSupportRadius S mu =
        cMu * confocalNullSupport S mu := by
      rw [confocalNullSupportRadius, confocalRadiusFromProjective]
      dsimp only [cMu]
      ring
    _ < cLambda * confocalNullSupport S lambda := hfinal
    _ = confocalNullSupportRadius S lambda := by
      rw [confocalNullSupportRadius, confocalRadiusFromProjective]
      dsimp only [cLambda]
      ring

/-- Positive fixed points of the all-radius support equation are unique. -/
theorem confocalNullSupport_positive_fixedPoint_unique_global
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R d e : ℝ}
    (hR : 0 < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hd0 : 0 < d) (he0 : 0 < e)
    (hd : d = confocalNullSupportOperator S R d)
    (he : e = confocalNullSupportOperator S R e) :
    d = e := by
  have parameter_data : ∀ {x : ℝ}, 0 < x →
      0 < confocalProjectiveParameter R x ∧
      confocalProjectiveParameter R x < 1 := by
    intro x hx
    constructor
    · rw [confocalProjectiveParameter]
      positivity
    · rw [confocalProjectiveParameter]
      exact (div_lt_one (by positivity)).2 (by linarith)
  rcases parameter_data hd0 with ⟨hld0, hld1⟩
  rcases parameter_data he0 with ⟨hle0, hle1⟩
  have hsupportD :
      confocalNullSupport S (confocalProjectiveParameter R d) = d := by
    simpa only [confocalNullSupportOperator] using hd.symm
  have hsupportE :
      confocalNullSupport S (confocalProjectiveParameter R e) = e := by
    simpa only [confocalNullSupportOperator] using he.symm
  have hradiusD :
      confocalNullSupportRadius S (confocalProjectiveParameter R d) = R := by
    rw [confocalNullSupportRadius, hsupportD]
    exact confocalRadiusFromProjective_projectiveParameter hR hd0
  have hradiusE :
      confocalNullSupportRadius S (confocalProjectiveParameter R e) = R := by
    rw [confocalNullSupportRadius, hsupportE]
    exact confocalRadiusFromProjective_projectiveParameter hR he0
  rcases lt_trichotomy d e with hde | hde | hde
  · have hparam := confocalProjectiveParameter_strictMono hR hd0.le hde
    have hstrict := confocalNullSupportRadius_strictAnti_of_support_pos
      hne hcone hbound hld0 hparam hle1 (by rwa [hsupportE])
    rw [hradiusD, hradiusE] at hstrict
    exact (lt_irrefl R hstrict).elim
  · exact hde
  · have hparam := confocalProjectiveParameter_strictMono hR he0.le hde
    have hstrict := confocalNullSupportRadius_strictAnti_of_support_pos
      hne hcone hbound hle0 hparam hld1 (by rwa [hsupportD])
    rw [hradiusD, hradiusE] at hstrict
    exact (lt_irrefl R hstrict).elim

/-- Every positive fixed point is the realized all-radius defect. -/
theorem confocalPositiveFixedPoint_eq_envelopeDefect_global
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R G d : ℝ}
    (hR : 0 < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hG : IsLUB (liftedConfocalBranch (R := R) '' S) G)
    (hd0 : 0 < d)
    (hd : d = confocalNullSupportOperator S R d) :
    d = G - R := by
  have hactual := confocalEnvelopeDefect_eq_nullSupport_fixedPoint_global
    hne hR hcone hbound hG
  let D := G - R
  have hD0 : 0 ≤ D := hactual.1
  have hsupportD : D = confocalNullSupportOperator S R D := hactual.2
  have hd_le_D : d ≤ D := by
    by_contra hnot
    have hDd : D < d := lt_of_not_ge hnot
    let e := (D + d) / 2
    have hDe : D < e := by dsimp only [e]; linarith
    have hed : e < d := by dsimp only [e]; linarith
    have he0 : 0 < e := hD0.trans_lt hDe
    have hparamEd : confocalProjectiveParameter R e <
        confocalProjectiveParameter R d :=
      confocalProjectiveParameter_strictMono hR he0.le hed
    have hparamE0 : 0 < confocalProjectiveParameter R e := by
      rw [confocalProjectiveParameter]
      positivity
    have hparamD1 : confocalProjectiveParameter R d < 1 := by
      rw [confocalProjectiveParameter]
      exact (div_lt_one (by positivity)).2 (by linarith)
    have hsupportd :
        confocalNullSupport S (confocalProjectiveParameter R d) = d := by
      simpa only [confocalNullSupportOperator] using hd.symm
    have hsupportE :
        confocalNullSupport S (confocalProjectiveParameter R e) ≤ e := by
      have hL := isLUB_confocalNullSupport hne hcone hbound
        (confocalProjectiveParameter_le_one hR he0.le)
      apply hL.2
      rintro _ ⟨q, hqS, rfl⟩
      have hqBranch : liftedConfocalBranch q R ≤ G :=
        hG.1 ⟨q, hqS, rfl⟩
      have hqHeight : q.2 ≤ R + e := by
        have hqHeightG : q.2 ≤ G := by
          rw [liftedConfocalBranch] at hqBranch
          nlinarith [Real.sqrt_nonneg
            ((R - q.1) ^ 2 + (q.2 ^ 2 - q.1 ^ 2))]
        dsimp only [D] at hDe
        linarith
      apply (liftedConfocalBranch_le_add_iff_nullFunctional_le_of_snd_le_add
        (hcone hqS) hR he0.le hqHeight).mp
      dsimp only [D] at hDe
      linarith
    have hradiusDUpper :
        confocalNullSupportRadius S (confocalProjectiveParameter R e) ≤ R := by
      rw [confocalNullSupportRadius]
      calc
        confocalRadiusFromProjective (confocalProjectiveParameter R e)
            (confocalNullSupport S (confocalProjectiveParameter R e)) ≤
            confocalRadiusFromProjective (confocalProjectiveParameter R e) e := by
          rw [confocalRadiusFromProjective, confocalRadiusFromProjective]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hsupportE
              (sub_nonneg.mpr (confocalProjectiveParameter_le_one hR he0.le)))
            (by positivity)
        _ = R := confocalRadiusFromProjective_projectiveParameter hR he0
    have hstrict := confocalNullSupportRadius_strictAnti_of_support_pos
      hne hcone hbound
      hparamE0
      hparamEd
      hparamD1
      (by rwa [hsupportd])
    have hradiusd :
        confocalNullSupportRadius S (confocalProjectiveParameter R d) = R := by
      rw [confocalNullSupportRadius, hsupportd]
      exact confocalRadiusFromProjective_projectiveParameter hR hd0
    rw [hradiusd] at hstrict
    exact (not_lt_of_ge hradiusDUpper hstrict)
  have hDpos : 0 < D := hd0.trans_le hd_le_D
  have hEq := confocalNullSupport_positive_fixedPoint_unique_global
    hne hR hcone hbound hd0 hDpos hd hsupportD
  simpa only [D] using hEq

/-- The canonical defect is the greatest nonnegative null-support fixed point. -/
theorem confocalGlobalDefect_isGreatest_fixedPoint
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M) :
    0 ≤ confocalGlobalDefect S R ∧
      confocalGlobalDefect S R =
        confocalNullSupportOperator S R (confocalGlobalDefect S R) ∧
      ∀ d : ℝ, 0 ≤ d → d = confocalNullSupportOperator S R d →
        d ≤ confocalGlobalDefect S R := by
  have hactual := confocalGlobalDefect_eq_nullSupport_fixedPoint
    hne hM hR hcone hbound
  refine ⟨hactual.1, hactual.2, ?_⟩
  intro d hd0 hd
  rcases hd0.eq_or_lt with rfl | hdpos
  · exact hactual.1
  · have hEq := confocalPositiveFixedPoint_eq_envelopeDefect_global
      hne hR hcone hbound
      (isLUB_confocalGlobalEnvelope hne hM hR hcone hbound) hdpos hd
    simpa only [confocalGlobalDefect] using hEq.le

/-- Complete positive all-radius defect graph. -/
def confocalGlobalPositiveDefectGraph
    (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ p.2 = confocalGlobalDefect S p.1}

/-- Complete positive projective support graph. -/
def confocalFullProjectiveSupportGraph
    (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | ∃ lambda : ℝ,
    0 < lambda ∧ lambda < 1 ∧
    0 < confocalNullSupport S lambda ∧
    p.1 = confocalNullSupportRadius S lambda ∧
    p.2 = confocalNullSupport S lambda}

/-- **All-radius projective support--envelope duality.**  The full positive defect graph is
exactly the rational projective image of the complete null-support graph. -/
theorem confocalGlobalPositiveDefectGraph_eq_fullProjectiveSupportGraph
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M : ℝ}
    (hM : 0 ≤ M)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M) :
    confocalGlobalPositiveDefectGraph S =
      confocalFullProjectiveSupportGraph S := by
  ext p
  constructor
  · rintro ⟨hR, hd, hpDefect⟩
    let d := confocalGlobalDefect S p.1
    let lambda := confocalProjectiveParameter p.1 d
    have hactual := confocalGlobalDefect_eq_nullSupport_fixedPoint
      hne hM hR hcone hbound
    have hsupport : confocalNullSupport S lambda = d := by
      simpa only [lambda, d, confocalNullSupportOperator] using hactual.2.symm
    have hd' : 0 < d := by simpa only [d, ← hpDefect] using hd
    have hlambda0 : 0 < lambda := by
      dsimp only [lambda]
      rw [confocalProjectiveParameter]
      positivity
    have hlambda1 : lambda < 1 := by
      dsimp only [lambda]
      rw [confocalProjectiveParameter]
      exact (div_lt_one (by positivity)).2 (by linarith)
    have hradius : confocalNullSupportRadius S lambda = p.1 := by
      rw [confocalNullSupportRadius, hsupport]
      exact confocalRadiusFromProjective_projectiveParameter hR hd'
    exact ⟨lambda, hlambda0, hlambda1, by rwa [hsupport],
      hradius.symm, by
        calc
          p.2 = d := by simpa only [d] using hpDefect
          _ = confocalNullSupport S lambda := hsupport.symm⟩
  · rintro ⟨lambda, hlambda0, hlambda1, hsupport0, hpRadius, hpSupport⟩
    let R := confocalNullSupportRadius S lambda
    let d := confocalNullSupport S lambda
    have hR : 0 < R := by
      dsimp only [R, confocalNullSupportRadius, confocalRadiusFromProjective]
      positivity
    have hprojective : confocalProjectiveParameter R d = lambda := by
      dsimp only [R, d, confocalNullSupportRadius]
      exact confocalProjectiveParameter_radiusFromProjective hlambda0 hsupport0
    have hfix : d = confocalNullSupportOperator S R d := by
      rw [confocalNullSupportOperator, hprojective]
    have hEq : d = confocalGlobalDefect S R := by
      apply confocalPositiveFixedPoint_eq_envelopeDefect_global
        hne hR hcone hbound
        (isLUB_confocalGlobalEnvelope hne hM hR hcone hbound)
        hsupport0 hfix
    refine ⟨?_, ?_, ?_⟩
    · rwa [hpRadius]
    · rwa [hpSupport]
    · calc
        p.2 = d := hpSupport
        _ = confocalGlobalDefect S R := hEq
        _ = confocalGlobalDefect S p.1 := by rw [hpRadius]

/-- Vanishing incoming null support is exactly pointwise vanishing of the incoming null
coordinate. -/
theorem confocalNullSupport_zero_iff_forall_nullMinus_zero
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M : ℝ}
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M) :
    confocalNullSupport S 0 = 0 ↔
      ∀ q ∈ S, confocalNullMinus q = 0 := by
  have hL0 := isLUB_confocalNullSupport hne hcone hbound
    (lambda := 0) (by norm_num)
  constructor
  · intro hsupport q hqS
    have hle : confocalNullMinus q ≤ 0 := by
      have hqle := hL0.1 ⟨q, hqS, rfl⟩
      change confocalNullFunctional q 0 ≤ confocalNullSupport S 0 at hqle
      rw [confocalNullFunctional, zero_mul, add_zero, hsupport] at hqle
      exact hqle
    exact le_antisymm hle (confocalNullMinus_nonneg (hcone hqS))
  · intro hminus
    have hzeroLUB :
        IsLUB (confocalNullFunctional (lambda := 0) '' S) 0 := by
      constructor
      · rintro _ ⟨q, hqS, rfl⟩
        change confocalNullFunctional q 0 ≤ 0
        rw [confocalNullFunctional, zero_mul, add_zero, hminus q hqS]
      · intro b hb
        rcases hne with ⟨q, hqS⟩
        have hqb := hb ⟨q, hqS, rfl⟩
        change confocalNullFunctional q 0 ≤ b at hqb
        rwa [confocalNullFunctional, zero_mul, add_zero, hminus q hqS] at hqb
    exact hL0.unique hzeroLUB

/-- Vanishing incoming null support is exactly concentration on the positive scalar null ray. -/
theorem confocalNullSupport_zero_iff_positiveNullRay_global
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M : ℝ}
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M) :
    confocalNullSupport S 0 = 0 ↔ ∀ q ∈ S, q.2 = q.1 := by
  rw [confocalNullSupport_zero_iff_forall_nullMinus_zero hne hcone hbound]
  constructor
  · intro h q hqS
    exact sub_eq_zero.mp (h q hqS)
  · intro h q hqS
    exact sub_eq_zero.mpr (h q hqS)

/-- On the null radical, the entire support slice is the linear interpolation from zero to its
outgoing endpoint. -/
theorem confocalNullSupport_eq_mul_one_of_zero
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M lambda : ℝ}
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hsupport0 : confocalNullSupport S 0 = 0)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    confocalNullSupport S lambda =
      lambda * confocalNullSupport S 1 := by
  have hminus :=
    (confocalNullSupport_zero_iff_forall_nullMinus_zero hne hcone hbound).mp hsupport0
  rcases hlambda0.eq_or_lt with rfl | hlambdaPos
  · simpa only [zero_mul] using hsupport0
  · have hLlambda := isLUB_confocalNullSupport hne hcone hbound
      hlambda1
    have hLone := isLUB_confocalNullSupport hne hcone hbound
      (lambda := 1) (by norm_num)
    have hcandidate :
        IsLUB (confocalNullFunctional (lambda := lambda) '' S)
          (lambda * confocalNullSupport S 1) := by
      constructor
      · rintro _ ⟨q, hqS, rfl⟩
        have hqOne : confocalNullFunctional q 1 ≤ confocalNullSupport S 1 :=
          hLone.1 ⟨q, hqS, rfl⟩
        have hpoint : confocalNullFunctional q lambda =
            lambda * confocalNullFunctional q 1 := by
          rw [confocalNullFunctional, confocalNullFunctional, hminus q hqS]
          ring
        change confocalNullFunctional q lambda ≤ lambda * confocalNullSupport S 1
        rw [hpoint]
        exact mul_le_mul_of_nonneg_left hqOne hlambdaPos.le
      · intro b hb
        have honeUpper :
            ∀ x ∈ confocalNullFunctional (lambda := 1) '' S,
              x ≤ b / lambda := by
          rintro _ ⟨q, hqS, rfl⟩
          have hqb := hb ⟨q, hqS, rfl⟩
          change confocalNullFunctional q lambda ≤ b at hqb
          have hpoint : confocalNullFunctional q lambda =
              lambda * confocalNullFunctional q 1 := by
            rw [confocalNullFunctional, confocalNullFunctional, hminus q hqS]
            ring
          rw [hpoint] at hqb
          change confocalNullFunctional q 1 ≤ b / lambda
          exact (le_div_iff₀ hlambdaPos).2 (by simpa only [mul_comm] using hqb)
        have honeLeast := hLone.2 honeUpper
        simpa only [mul_comm] using (le_div_iff₀ hlambdaPos).1 honeLeast
    exact hLlambda.unique hcandidate

/-- Axial height of a scalar null-radical source. -/
def confocalRadicalHeight (S : Set (ℝ × ℝ)) : ℝ :=
  confocalNullSupport S 1 / 2

/-- The null-radical support is exactly `2 A lambda`. -/
theorem confocalNullSupport_eq_two_mul_radicalHeight_mul
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M lambda : ℝ}
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hsupport0 : confocalNullSupport S 0 = 0)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    confocalNullSupport S lambda =
      2 * confocalRadicalHeight S * lambda := by
  rw [confocalNullSupport_eq_mul_one_of_zero hne hcone hbound
    hsupport0 hlambda0 hlambda1, confocalRadicalHeight]
  ring

/-- A positive fixed point on the null radical is forced to be the explicit second branch. -/
theorem confocalPositiveFixedPoint_eq_two_mul_radicalHeight_sub
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R d : ℝ}
    (hR : 0 < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hsupport0 : confocalNullSupport S 0 = 0)
    (hd0 : 0 < d)
    (hd : d = confocalNullSupportOperator S R d) :
    d = 2 * (confocalRadicalHeight S - R) := by
  have hlambda0 : 0 ≤ confocalProjectiveParameter R d :=
    confocalProjectiveParameter_nonneg hR hd0.le
  have hlambda1 : confocalProjectiveParameter R d ≤ 1 :=
    confocalProjectiveParameter_le_one hR hd0.le
  have hsupport := confocalNullSupport_eq_two_mul_radicalHeight_mul
    hne hcone hbound hsupport0 hlambda0 hlambda1
  have hEq :
      d = 2 * confocalRadicalHeight S * (d / (2 * R + d)) := by
    rw [confocalNullSupportOperator] at hd
    rw [hsupport] at hd
    rw [confocalProjectiveParameter] at hd
    exact hd
  have hden : 0 < 2 * R + d := by positivity
  field_simp [hden.ne'] at hEq
  nlinarith [hEq]

/-- **Exact null-radical extinction law.**  The global defect follows the positive second root up
to the axial height and then vanishes. -/
theorem confocalGlobalDefect_eq_two_mul_max_radicalHeight_sub
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hsupport0 : confocalNullSupport S 0 = 0) :
    confocalGlobalDefect S R =
      2 * max (confocalRadicalHeight S - R) 0 := by
  have hactual := confocalGlobalDefect_eq_nullSupport_fixedPoint
    hne hM hR hcone hbound
  rcases hactual.1.eq_or_lt with hDzero | hDpos
  · have hheightR : confocalRadicalHeight S ≤ R := by
      by_contra hnot
      have hRheight : R < confocalRadicalHeight S := lt_of_not_ge hnot
      have hheightPos : 0 < confocalRadicalHeight S := hR.trans hRheight
      let d := 2 * (confocalRadicalHeight S - R)
      have hd0 : 0 < d := by dsimp only [d]; linarith
      have hparam0 := confocalProjectiveParameter_nonneg hR hd0.le
      have hparam1 := confocalProjectiveParameter_le_one hR hd0.le
      have hsupport := confocalNullSupport_eq_two_mul_radicalHeight_mul
        hne hcone hbound hsupport0 hparam0 hparam1
      have hfix : d = confocalNullSupportOperator S R d := by
        rw [confocalNullSupportOperator, hsupport, confocalProjectiveParameter]
        dsimp only [d]
        field_simp [hheightPos.ne']
        ring
      have hEq := confocalPositiveFixedPoint_eq_envelopeDefect_global
        hne hR hcone hbound
        (isLUB_confocalGlobalEnvelope hne hM hR hcone hbound)
        hd0 hfix
      change d = confocalGlobalDefect S R at hEq
      exact hd0.ne' (hEq.trans hDzero.symm)
    rw [hDzero.symm]
    simp only [max_eq_right (sub_nonpos.mpr hheightR), mul_zero]
  · have hpositive := confocalPositiveFixedPoint_eq_two_mul_radicalHeight_sub
      hne hR hcone hbound hsupport0 hDpos hactual.2
    have hRheight : R < confocalRadicalHeight S := by linarith
    rw [hpositive]
    simp only [max_eq_left (sub_nonneg.mpr hRheight.le)]

/-- Off the incoming null radical, every positive radius has strictly positive defect. -/
theorem confocalGlobalDefect_pos_of_nullSupport_zero_pos
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R)
    (hcone : S ⊆ confocalLorentzCone)
    (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hsupport0 : 0 < confocalNullSupport S 0) :
    0 < confocalGlobalDefect S R := by
  have hactual := confocalGlobalDefect_eq_nullSupport_fixedPoint
    hne hM hR hcone hbound
  have hmono := confocalNullSupport_mono hne hcone hbound
    (lambda := 0)
    (mu := confocalProjectiveParameter R (confocalGlobalDefect S R))
    (confocalProjectiveParameter_nonneg hR hactual.1)
    (confocalProjectiveParameter_le_one hR hactual.1)
  have hsupportEq :
      confocalNullSupport S
          (confocalProjectiveParameter R (confocalGlobalDefect S R)) =
        confocalGlobalDefect S R := by
    simpa only [confocalNullSupportOperator] using hactual.2.symm
  rw [hsupportEq] at hmono
  exact hsupport0.trans_le hmono

end

end HTGeometry
