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

open Set Filter Topology

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

/-- **Confocal hull is contained in the null-support hull, non-degenerate case** (`K_G(S) ⊆ K_h(S)`
when `h_S(1) > 0`).  On `(0,1)` the null support is positive (a positive `h_S(1)` forces a source
point of positive height, which keeps every interior support value positive), so the core recovery
`confocalNullFunctional_le_nullSupport_of_mem_hull` applies; the boundary directions `λ ∈ {0,1}` follow
by continuity of the null support field (`confocalNullSupport_lipschitz`) and the affine null
functional. -/
theorem confocalHullOfField_subset_confocalNullSupportHull_of_pos
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hcone : S ⊆ confocalLorentzCone) (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hpos1 : 0 < confocalNullSupport S 1) :
    confocalHullOfField (Set.Ioi 0) (confocalGlobalEnvelope S) ⊆
      confocalNullSupportHull S := by
  rw [confocalNullSupport] at hpos1
  obtain ⟨c, hcmem, hc0⟩ := exists_lt_of_lt_csSup (hne.image _) hpos1
  obtain ⟨p, hpS, rfl⟩ := hcmem
  have hp := hcone hpS
  have hu0 : 0 ≤ confocalNullMinus p := confocalNullMinus_nonneg hp
  have hv0 : 0 ≤ confocalNullPlus p := confocalNullPlus_nonneg hp
  have hpsum : 0 < confocalNullMinus p + confocalNullPlus p := by
    have he : confocalNullFunctional p 1 = confocalNullMinus p + confocalNullPlus p := by
      rw [confocalNullFunctional]; ring
    rw [← he]; exact hc0
  have hpos_ioo : ∀ μ : ℝ, 0 < μ → μ < 1 → 0 < confocalNullSupport S μ := by
    intro μ hμ0 hμ1
    have hle : confocalNullFunctional p μ ≤ confocalNullSupport S μ :=
      (isLUB_confocalNullSupport hne hcone hbound (le_of_lt hμ1)).1 ⟨p, hpS, rfl⟩
    have hpμ : 0 < confocalNullFunctional p μ := by
      rw [confocalNullFunctional]
      rcases eq_or_lt_of_le hu0 with hu | hu
      · have hvpos : 0 < confocalNullPlus p := by rw [← hu] at hpsum; linarith
        have hmp := mul_pos hμ0 hvpos; linarith
      · have hmp := mul_nonneg hμ0.le hv0; linarith
    linarith
  intro q hqG
  refine ⟨hqG.1, ?_⟩
  have hmain : ∀ μ : ℝ, 0 < μ → μ < 1 →
      confocalNullFunctional q μ ≤ confocalNullSupport S μ := fun μ hμ0 hμ1 =>
    confocalNullFunctional_le_nullSupport_of_mem_hull hne hM hcone hbound hqG hμ0 hμ1
      (hpos_ioo μ hμ0 hμ1)
  have hcont_nf : Continuous (fun μ : ℝ => confocalNullFunctional q μ) := by
    unfold confocalNullFunctional; fun_prop
  have htend_lt : Tendsto (confocalNullSupport S) (𝓝[<] (1:ℝ))
      (𝓝 (confocalNullSupport S 1)) := by
    have hsq : Tendsto (fun t : ℝ => confocalNullSupport S t - confocalNullSupport S 1)
        (𝓝[<] 1) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun t : ℝ => 2 * M * |t - 1|) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with t ht
        rw [Real.norm_eq_abs]
        exact confocalNullSupport_lipschitz hne hcone hbound (le_of_lt ht) (le_refl 1)
      · exact ((by fun_prop : Continuous fun t : ℝ => 2 * M * |t - 1|).tendsto' 1 0
          (by simp)).mono_left nhdsWithin_le_nhds
    have := hsq.add (tendsto_const_nhds (x := confocalNullSupport S 1))
    simpa using this
  have htend_gt : Tendsto (confocalNullSupport S) (𝓝[>] (0:ℝ))
      (𝓝 (confocalNullSupport S 0)) := by
    have hsq : Tendsto (fun t : ℝ => confocalNullSupport S t - confocalNullSupport S 0)
        (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun t : ℝ => 2 * M * |t - 0|) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))] with t _ ht1
        rw [Real.norm_eq_abs]
        exact confocalNullSupport_lipschitz hne hcone hbound (le_of_lt ht1) (by norm_num)
      · exact ((by fun_prop : Continuous fun t : ℝ => 2 * M * |t - 0|).tendsto' 0 0
          (by simp)).mono_left nhdsWithin_le_nhds
    have := hsq.add (tendsto_const_nhds (x := confocalNullSupport S 0))
    simpa using this
  intro lam hlam
  rcases eq_or_lt_of_le hlam.1 with h0 | h0
  · subst h0
    refine le_of_tendsto_of_tendsto
      ((hcont_nf.tendsto 0).mono_left nhdsWithin_le_nhds) htend_gt ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))] with t ht0 ht1
    exact hmain t ht0 ht1
  · rcases eq_or_lt_of_le hlam.2 with h1 | h1
    · subst h1
      refine le_of_tendsto_of_tendsto
        ((hcont_nf.tendsto 1).mono_left nhdsWithin_le_nhds) htend_lt ?_
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioi_mem_nhds (show (0:ℝ) < 1 by norm_num))] with t ht1 ht0
      exact hmain t ht0 ht1
    · exact hmain lam h0 h1

/-- **Maximal-hull identity, non-degenerate case** (equation (13) for `h_S(1) > 0`).  The all-radius
confocal hull `K_G(S)` and the null-support hull `K_h(S)` coincide, removing the exterior `R > M`
restriction of the corpus's per-radius form. -/
theorem confocalHullOfField_eq_confocalNullSupportHull_of_pos
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hcone : S ⊆ confocalLorentzCone) (hbound : ∀ q ∈ S, q.2 ≤ M)
    (hpos1 : 0 < confocalNullSupport S 1) :
    confocalHullOfField (Set.Ioi 0) (confocalGlobalEnvelope S) = confocalNullSupportHull S :=
  Set.Subset.antisymm
    (confocalHullOfField_subset_confocalNullSupportHull_of_pos hne hM hcone hbound hpos1)
    (confocalNullSupportHull_subset_confocalHullOfField hne hM hcone hbound)


/-- **Confocal hull is contained in the null-support hull, unconditional** (`K_G(S) ⊆ K_h(S)`).  The
non-degenerate case `h_S(1) > 0` reduces to `confocalHullOfField_subset_confocalNullSupportHull_of_pos`;
in the degenerate case `h_S(1) = 0` the null support vanishes on all of `[0,1]`, forcing every global
defect and hence the whole envelope down to the radius, so any hull point collapses to the origin. -/
theorem confocalHullOfField_subset_confocalNullSupportHull
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hcone : S ⊆ confocalLorentzCone) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    confocalHullOfField (Set.Ioi 0) (confocalGlobalEnvelope S) ⊆
      confocalNullSupportHull S := by
  by_cases hpos1 : 0 < confocalNullSupport S 1
  · exact confocalHullOfField_subset_confocalNullSupportHull_of_pos hne hM hcone hbound hpos1
  · rw [not_lt] at hpos1
    obtain ⟨p0, hp0S⟩ := hne
    have hp0 := hcone hp0S
    have hs1ge : 0 ≤ confocalNullSupport S 1 := by
      have hle := (isLUB_confocalNullSupport ⟨p0, hp0S⟩ hcone hbound (le_refl (1:ℝ))).1 ⟨p0, hp0S, rfl⟩
      have h0 : 0 ≤ confocalNullFunctional p0 1 := by
        rw [confocalNullFunctional]
        have := confocalNullMinus_nonneg hp0; have := confocalNullPlus_nonneg hp0; linarith
      linarith
    have hs1 : confocalNullSupport S 1 = 0 := le_antisymm hpos1 hs1ge
    have hzero : ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → confocalNullSupport S μ = 0 := by
      intro μ hμ0 hμ1
      have hge : 0 ≤ confocalNullSupport S μ := by
        have hle := (isLUB_confocalNullSupport ⟨p0, hp0S⟩ hcone hbound hμ1).1 ⟨p0, hp0S, rfl⟩
        have h0 : 0 ≤ confocalNullFunctional p0 μ := by
          rw [confocalNullFunctional]
          have h1 := confocalNullMinus_nonneg hp0; have h2 := confocalNullPlus_nonneg hp0
          have := mul_nonneg hμ0 h2; linarith
        linarith
      have hle : confocalNullSupport S μ ≤ confocalNullSupport S 1 := by
        apply (isLUB_confocalNullSupport ⟨p0, hp0S⟩ hcone hbound hμ1).2
        rintro _ ⟨p, hpS, rfl⟩
        have hp := hcone hpS
        have h2 := confocalNullPlus_nonneg hp
        have hle1 := (isLUB_confocalNullSupport ⟨p0, hp0S⟩ hcone hbound (le_refl (1:ℝ))).1 ⟨p, hpS, rfl⟩
        have hstep : confocalNullFunctional p μ ≤ confocalNullFunctional p 1 := by
          rw [confocalNullFunctional, confocalNullFunctional]
          nlinarith [mul_le_of_le_one_left h2 hμ1]
        linarith
      rw [hs1] at hle; linarith
    have hGR : ∀ R : ℝ, 0 < R → confocalGlobalEnvelope S R = R := by
      intro R hR
      obtain ⟨hd0, hfix, _⟩ := confocalGlobalDefect_isGreatest_fixedPoint ⟨p0, hp0S⟩ hM hR hcone hbound
      have hden : (0:ℝ) < 2 * R + confocalGlobalDefect S R := by linarith
      have hlam0 : 0 ≤ confocalProjectiveParameter R (confocalGlobalDefect S R) := by
        rw [confocalProjectiveParameter]; exact div_nonneg hd0 hden.le
      have hlam1 : confocalProjectiveParameter R (confocalGlobalDefect S R) ≤ 1 := by
        rw [confocalProjectiveParameter, div_le_one hden]; linarith
      have hopz : confocalNullSupportOperator S R (confocalGlobalDefect S R) = 0 := by
        rw [confocalNullSupportOperator]; exact hzero _ hlam0 hlam1
      have hDz : confocalGlobalDefect S R = 0 := hfix.trans hopz
      rw [confocalGlobalDefect] at hDz; linarith
    rintro q ⟨hqCone, hqField⟩
    have hq2nn : 0 ≤ q.2 := (abs_nonneg q.1).trans hqCone
    have hu0 : confocalNullMinus q = 0 := by
      have hR0 : (0:ℝ) < q.2 + 1 := by linarith
      have hbr : liftedConfocalBranch q (q.2 + 1) ≤ (q.2 + 1) := by
        have h := hqField (q.2 + 1) hR0; rwa [hGR (q.2 + 1) hR0] at h
      have hsnd : q.2 ≤ (q.2 + 1) + 0 := by linarith
      have hnull := (liftedConfocalBranch_le_add_iff_nullFunctional_le_of_snd_le_add
        hqCone hR0 (le_refl 0) hsnd).mp (by rw [add_zero]; exact hbr)
      have hlz : confocalProjectiveParameter (q.2 + 1) 0 = 0 := by
        rw [confocalProjectiveParameter]; simp
      rw [hlz, confocalNullFunctional] at hnull
      simp only [zero_mul, add_zero] at hnull
      exact le_antisymm hnull (confocalNullMinus_nonneg hqCone)
    have hua : q.1 = q.2 := by rw [confocalNullMinus] at hu0; linarith
    have ha0 : q.2 = 0 := by
      by_contra hne0
      have hq2pos : 0 < q.2 := lt_of_le_of_ne hq2nn (Ne.symm hne0)
      have hR1 : (0:ℝ) < q.2 / 2 := by positivity
      have hbr : liftedConfocalBranch q (q.2 / 2) ≤ q.2 / 2 := by
        have h := hqField (q.2 / 2) hR1; rwa [hGR (q.2 / 2) hR1] at h
      rw [liftedConfocalBranch, hua] at hbr
      have hrad : Real.sqrt ((q.2 / 2 - q.2) ^ 2 + (q.2 ^ 2 - q.2 ^ 2)) = q.2 - q.2 / 2 := by
        rw [show q.2 ^ 2 - q.2 ^ 2 = 0 by ring, add_zero, Real.sqrt_sq_eq_abs,
          abs_of_nonpos (by linarith)]
        ring
      rw [hrad] at hbr; linarith
    refine ⟨hqCone, ?_⟩
    intro lam hlam
    have hqz : confocalNullFunctional q lam = 0 := by
      rw [confocalNullFunctional, confocalNullMinus, confocalNullPlus, hua, ha0]; ring
    rw [hqz]; exact le_of_eq (hzero lam hlam.1 hlam.2).symm

/-- **Maximal-hull identity (equation (13)), unconditional.**  For every nonempty bounded Lorentz
source the all-radius confocal hull and the null-support hull coincide, with no exterior radius
restriction and no nondegeneracy hypothesis. -/
theorem confocalHullOfField_eq_confocalNullSupportHull
    {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hcone : S ⊆ confocalLorentzCone) (hbound : ∀ q ∈ S, q.2 ≤ M) :
    confocalHullOfField (Set.Ioi 0) (confocalGlobalEnvelope S) = confocalNullSupportHull S :=
  Set.Subset.antisymm
    (confocalHullOfField_subset_confocalNullSupportHull hne hM hcone hbound)
    (confocalNullSupportHull_subset_confocalHullOfField hne hM hcone hbound)



theorem confocalNullSupport_eq_sSup_nullSupportHull
    {X : Set (ℝ × ℝ)} (hne : X.Nonempty) {M : ℝ} (_hM : 0 ≤ M)
    (hcone : X ⊆ confocalLorentzCone) (hbound : ∀ q ∈ X, q.2 ≤ M)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    confocalNullSupport X lam =
      sSup (confocalNullFunctional (lambda := lam) '' confocalNullSupportHull X) := by
  have hsub : X ⊆ confocalNullSupportHull X := by
    intro q hqX
    exact ⟨hcone hqX, fun μ hμ =>
      (isLUB_confocalNullSupport hne hcone hbound hμ.2).1 ⟨q, hqX, rfl⟩⟩
  have hbdd : BddAbove (confocalNullFunctional (lambda := lam) '' confocalNullSupportHull X) := by
    refine ⟨confocalNullSupport X lam, ?_⟩
    rintro _ ⟨q, hqKh, rfl⟩
    exact hqKh.2 lam ⟨hlam0, hlam1⟩
  have hKhne : (confocalNullFunctional (lambda := lam) '' confocalNullSupportHull X).Nonempty := by
    obtain ⟨p, hpX⟩ := hne
    exact ⟨_, ⟨p, hsub hpX, rfl⟩⟩
  apply le_antisymm
  · rw [confocalNullSupport]
    exact csSup_le_csSup hbdd (hne.image _) (Set.image_mono hsub)
  · apply csSup_le hKhne
    rintro _ ⟨q, hqKh, rfl⟩
    exact hqKh.2 lam ⟨hlam0, hlam1⟩

/-- **Defect-to-support faithfulness (reverse direction of (12)).**  If two nonempty bounded Lorentz
sources have the same all-radius confocal defect on `(0,∞)`, they have the same null support field on
`[0,1]`.  Equal defects give equal envelopes, hence equal all-radius confocal hulls; the maximal-hull
identity (13) turns these into equal null-support hulls, and the null support is the support function
of that hull. -/
theorem nullSupport_eqOn_of_globalDefect_eqOn
    {S T : Set (ℝ × ℝ)} (hSne : S.Nonempty) (hTne : T.Nonempty)
    {MS MT : ℝ} (hMS : 0 ≤ MS) (hMT : 0 ≤ MT)
    (hScone : S ⊆ confocalLorentzCone) (hTcone : T ⊆ confocalLorentzCone)
    (hSbound : ∀ q ∈ S, q.2 ≤ MS) (hTbound : ∀ q ∈ T, q.2 ≤ MT)
    (hD : Set.EqOn (confocalGlobalDefect S) (confocalGlobalDefect T) (Set.Ioi 0)) :
    Set.EqOn (confocalNullSupport S) (confocalNullSupport T) (Set.Icc 0 1) := by
  have hG : Set.EqOn (confocalGlobalEnvelope S) (confocalGlobalEnvelope T) (Set.Ioi 0) := by
    intro R hR
    have h := hD hR
    rw [confocalGlobalDefect, confocalGlobalDefect] at h
    linarith
  have hKh : confocalNullSupportHull S = confocalNullSupportHull T := by
    rw [← confocalHullOfField_eq_confocalNullSupportHull hSne hMS hScone hSbound,
        ← confocalHullOfField_eq_confocalNullSupportHull hTne hMT hTcone hTbound,
        confocalHullOfField_eq_of_eqOn hG]
  intro lam hlam
  rw [confocalNullSupport_eq_sSup_nullSupportHull hSne hMS hScone hSbound hlam.1 hlam.2,
      confocalNullSupport_eq_sSup_nullSupportHull hTne hMT hTcone hTbound hlam.1 hlam.2, hKh]

/-- **Transform faithfulness (equation (12)), full equivalence.**  Two nonempty bounded Lorentz
sources have the same all-radius confocal defect on `(0,∞)` if and only if they have the same null
support field on `[0,1]`. -/
theorem globalDefect_eqOn_iff_nullSupport_eqOn
    {S T : Set (ℝ × ℝ)} (hSne : S.Nonempty) (hTne : T.Nonempty)
    {MS MT : ℝ} (hMS : 0 ≤ MS) (hMT : 0 ≤ MT)
    (hScone : S ⊆ confocalLorentzCone) (hTcone : T ⊆ confocalLorentzCone)
    (hSbound : ∀ q ∈ S, q.2 ≤ MS) (hTbound : ∀ q ∈ T, q.2 ≤ MT) :
    Set.EqOn (confocalGlobalDefect S) (confocalGlobalDefect T) (Set.Ioi 0) ↔
      Set.EqOn (confocalNullSupport S) (confocalNullSupport T) (Set.Icc 0 1) :=
  ⟨nullSupport_eqOn_of_globalDefect_eqOn hSne hTne hMS hMT hScone hTcone hSbound hTbound,
    confocalGlobalDefect_eqOn_of_nullSupport_eqOn hSne hTne hMS hMT hScone hTcone hSbound hTbound⟩

end

end HTGeometry
