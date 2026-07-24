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

end

end HTGeometry
