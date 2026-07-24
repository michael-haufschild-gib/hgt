import GaloisForLFunctions.HTGeometry.ConfocalGlobalSupportTransform

/-!
# Faithfulness of the confocal support transform

Two bounded Lorentz sources with the same null support field on `[0,1]` have the same all-radius
confocal defect on `(0,∞)`.  This is the support-to-defect (`h ↦ D`) half of the global transform
faithfulness: the defect at each radius is the greatest nonnegative fixed point of the
support-driven self-consistency operator (`confocalGlobalDefect_isGreatest_fixedPoint`), and that
operator depends on the source only through its null support field, so equal support fields force
equal defects.
-/

namespace HTGeometry

noncomputable section

/-- **Support-to-defect faithfulness.**  If two nonempty bounded Lorentz sources have the same null
support field on `[0,1]`, their all-radius confocal defects agree on `(0,∞)`.  The defect is the
greatest nonnegative fixed point of `confocalNullSupportOperator`, which factors through the null
support field, so equal support fields yield equal greatest fixed points. -/
theorem confocalGlobalDefect_eqOn_of_nullSupport_eqOn
    {S T : Set (ℝ × ℝ)} (hSne : S.Nonempty) (hTne : T.Nonempty)
    {MS MT : ℝ} (hMS : 0 ≤ MS) (hMT : 0 ≤ MT)
    (hScone : S ⊆ confocalLorentzCone) (hTcone : T ⊆ confocalLorentzCone)
    (hSbound : ∀ q ∈ S, q.2 ≤ MS) (hTbound : ∀ q ∈ T, q.2 ≤ MT)
    (hsupp : Set.EqOn (confocalNullSupport S) (confocalNullSupport T) (Set.Icc 0 1)) :
    Set.EqOn (confocalGlobalDefect S) (confocalGlobalDefect T) (Set.Ioi 0) := by
  intro R hRmem
  have hR : (0:ℝ) < R := hRmem
  obtain ⟨hDS0, hDSfp, hDSgreatest⟩ :=
    confocalGlobalDefect_isGreatest_fixedPoint hSne hMS hR hScone hSbound
  obtain ⟨hDT0, hDTfp, hDTgreatest⟩ :=
    confocalGlobalDefect_isGreatest_fixedPoint hTne hMT hR hTcone hTbound
  have hop : ∀ d : ℝ, 0 ≤ d →
      confocalNullSupportOperator S R d = confocalNullSupportOperator T R d := by
    intro d hd
    rw [confocalNullSupportOperator, confocalNullSupportOperator]
    apply hsupp
    rw [Set.mem_Icc, confocalProjectiveParameter]
    have hden : (0:ℝ) < 2 * R + d := by linarith
    exact ⟨div_nonneg hd hden.le, by rw [div_le_one hden]; linarith⟩
  have hDS_fpT : confocalGlobalDefect S R
      = confocalNullSupportOperator T R (confocalGlobalDefect S R) := by
    rw [← hop _ hDS0]; exact hDSfp
  have hDT_fpS : confocalGlobalDefect T R
      = confocalNullSupportOperator S R (confocalGlobalDefect T R) := by
    rw [hop _ hDT0]; exact hDTfp
  exact le_antisymm (hDTgreatest _ hDS0 hDS_fpT) (hDSgreatest _ hDT0 hDT_fpS)

/-- The null-support hull `K_h(S)`: points of the Lorentz cone whose null functionals are dominated
by the source null support field on `[0,1]`. -/
def confocalNullSupportHull (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {q | q ∈ confocalLorentzCone ∧
    ∀ lambda ∈ Set.Icc (0:ℝ) 1, confocalNullFunctional q lambda ≤ confocalNullSupport S lambda}

/-- **The null-support hull is contained in the all-radius confocal hull** (`K_h(S) ⊆ K_G(S)`, the
direct inclusion of the maximal-hull identity (13)).  At each radius the realized defect is a null
support fixed point (`confocalGlobalDefect_eq_nullSupport_fixedPoint`); a point whose null
functionals are dominated by the support field therefore satisfies the interior sublevel form
(`liftedConfocalBranch_le_add_iff_nullFunctional_le_of_snd_le_add`) and its confocal branch stays
below the global envelope.  The `λ = 1` constraint supplies the height bound `q.2 ≤ G_S(R)` the
interior form requires, valid without any exterior `R > M` restriction. -/
theorem confocalNullSupportHull_subset_confocalHullOfField
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hcone : S ⊆ confocalLorentzCone) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    confocalNullSupportHull S ⊆
      confocalHullOfField (Set.Ioi 0) (confocalGlobalEnvelope S) := by
  rintro q ⟨hqCone, hqNull⟩
  refine ⟨hqCone, fun R hRmem => ?_⟩
  have hR : (0:ℝ) < R := hRmem
  set d := confocalGlobalDefect S R with hd_def
  have hGeq : confocalGlobalEnvelope S R = R + d := by
    rw [hd_def, confocalGlobalDefect]; ring
  obtain ⟨hd0, hdfp⟩ :=
    confocalGlobalDefect_eq_nullSupport_fixedPoint hne hM hR hcone hbound
  have hqsnd : q.2 ≤ confocalGlobalEnvelope S R := by
    have hq1 : confocalNullFunctional q 1 ≤ confocalNullSupport S 1 :=
      hqNull 1 ⟨zero_le_one, le_refl 1⟩
    have hnf1 : confocalNullFunctional q 1 = 2 * q.2 := by
      rw [confocalNullFunctional, confocalNullMinus, confocalNullPlus]; ring
    have hhub : confocalNullSupport S 1 ≤ 2 * confocalGlobalEnvelope S R := by
      apply (isLUB_confocalNullSupport hne hcone hbound (le_refl (1:ℝ))).2
      rintro _ ⟨p, hpS, rfl⟩
      have hpb : liftedConfocalBranch p R ≤ confocalGlobalEnvelope S R :=
        (isLUB_confocalGlobalEnvelope hne hM hR hcone hbound).1 ⟨p, hpS, rfl⟩
      have hpa : p.2 ≤ liftedConfocalBranch p R := by
        simp only [liftedConfocalBranch]
        linarith [Real.sqrt_nonneg ((R - p.1) ^ 2 + (p.2 ^ 2 - p.1 ^ 2))]
      show confocalNullFunctional p 1 ≤ 2 * confocalGlobalEnvelope S R
      rw [confocalNullFunctional, confocalNullMinus, confocalNullPlus]
      linarith
    rw [hnf1] at hq1; linarith
  rw [hGeq]
  refine (liftedConfocalBranch_le_add_iff_nullFunctional_le_of_snd_le_add
    hqCone hR hd0 (hGeq ▸ hqsnd)).mpr ?_
  have hlam : confocalProjectiveParameter R d ∈ Set.Icc (0:ℝ) 1 := by
    rw [Set.mem_Icc, confocalProjectiveParameter]
    have hden : (0:ℝ) < 2 * R + d := by linarith
    exact ⟨div_nonneg hd0 hden.le, by rw [div_le_one hden]; linarith⟩
  have hqlam := hqNull (confocalProjectiveParameter R d) hlam
  rw [confocalNullSupportOperator] at hdfp
  rwa [← hdfp] at hqlam

/-- Core recovery for the reverse hull inclusion `K_G(S) ⊆ K_h(S)`.  On the strictly-interior
projective directions where the null support is positive, a point of the all-radius confocal hull
has its null functional dominated by the source support field.  At `R = ρ_S(λ)` the realized defect
equals `h_S(λ)` (projective graph inversion, `confocalPositiveFixedPoint_eq_envelopeDefect_global`
with `confocalProjectiveParameter_radiusFromProjective`), so the interior sublevel form transports
the branch bound `b_q(R) ≤ G_S(R)` to `nullFunc q λ ≤ h_S(λ)`. -/
theorem confocalNullFunctional_le_nullSupport_of_mem_hull
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hcone : S ⊆ confocalLorentzCone) (hbound : ∀ q ∈ S, q.2 ≤ M)
    {q : ℝ × ℝ}
    (hqG : q ∈ confocalHullOfField (Set.Ioi 0) (confocalGlobalEnvelope S))
    {lambda : ℝ} (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    (hsupp0 : 0 < confocalNullSupport S lambda) :
    confocalNullFunctional q lambda ≤ confocalNullSupport S lambda := by
  obtain ⟨hqCone, hqField⟩ := hqG
  set d := confocalNullSupport S lambda with hd_def
  set R := confocalNullSupportRadius S lambda with hR_def
  have hd0 : 0 ≤ d := hsupp0.le
  have hR : (0:ℝ) < R := by
    rw [hR_def, confocalNullSupportRadius, confocalRadiusFromProjective]
    have : 0 < (1 - lambda) := by linarith
    positivity
  have hprojective : confocalProjectiveParameter R d = lambda := by
    rw [hR_def, confocalNullSupportRadius]
    exact confocalProjectiveParameter_radiusFromProjective hlam0 hsupp0
  have hfix : d = confocalNullSupportOperator S R d := by
    rw [confocalNullSupportOperator, hprojective]
  have hEq : d = confocalGlobalDefect S R :=
    confocalPositiveFixedPoint_eq_envelopeDefect_global hne hR hcone hbound
      (isLUB_confocalGlobalEnvelope hne hM hR hcone hbound) hsupp0 hfix
  have hGval : confocalGlobalEnvelope S R = R + d := by
    rw [hEq, confocalGlobalDefect]; ring
  have hbr : liftedConfocalBranch q R ≤ R + d := by
    rw [← hGval]; exact hqField R hR
  have hqsnd : q.2 ≤ R + d := by
    have hqb : q.2 ≤ liftedConfocalBranch q R := by
      simp only [liftedConfocalBranch]
      linarith [Real.sqrt_nonneg ((R - q.1) ^ 2 + (q.2 ^ 2 - q.1 ^ 2))]
    linarith
  have hnull := (liftedConfocalBranch_le_add_iff_nullFunctional_le_of_snd_le_add
    hqCone hR hd0 hqsnd).mp hbr
  rwa [hprojective] at hnull

end

end HTGeometry
