/-
# The Diophantine exceptional directions of the chain shell are null

The projective gap ratios of a linear Hermitian family are invariant under positive rescaling of
the coefficients, so the very well approximable directions form a cone.  Its ambient Lebesgue
nullity is the global extremality statement for the escaping chain family, and polar disintegration
carries that nullity to the coefficient sphere and to the patch parametrization.

Main results:
* `chainVwaSphere`, `measurableSet_chainVwaSphere` — the exceptional directions form a Borel set.
* `toSphere_chainVwaSphere_eq_zero` — **they are shell-null**.
* `toSphere_preimage_chainVwaSphere_eq_zero` — the same in patch coordinates.
-/
import GaloisForLFunctions.HTGeometry.PatchChainPullback
import GaloisForLFunctions.HTGeometry.SortedGapRatioGlobalExtremality
import GaloisForLFunctions.HTGeometry.ChainPauliFinEscape
import GaloisForLFunctions.HTGeometry.SortedEnsembleSpectrumScaling
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.VwaMeasurable

open MeasureTheory Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false

variable {n : ℕ}

instance instNeZeroCardChainLabel (k : ℕ) : NeZero (Fintype.card (ChainLabel (k + 3))) :=
  ⟨(Fintype.card_pos_iff.mpr (instNonemptyChainLabel (k + 2))).ne'⟩

/-- The very well approximable directions of the numbered chain shell. -/
def chainVwaSphere (k : ℕ) (anchor clock : Fin (2 ^ (k + 3)))
    (ι : Fin n → Fin (2 ^ (k + 3))) :
    Set (coeffSphere (Fintype.card (ChainLabel (k + 3)))) :=
  {x | KleinbockMargulis.VWA fun j =>
      anchoredGapRatioMap
        (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k + 3)) (sphereCoeff x))
        anchor clock ι j}

theorem measurable_chainGapRatioMap (k : ℕ) (anchor clock : Fin (2 ^ (k + 3)))
    (ι : Fin n → Fin (2 ^ (k + 3))) :
    Measurable fun x : coeffSphere (Fintype.card (ChainLabel (k + 3))) =>
      anchoredGapRatioMap
        (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k + 3)) (sphereCoeff x))
        anchor clock ι := by
  have hcont : Continuous fun x : coeffSphere (Fintype.card (ChainLabel (k + 3))) =>
      sortedEnsembleSpectrum (chainPauliFin_isHermitian (k + 3)) (sphereCoeff x) :=
    (continuous_sortedEnsembleSpectrum _).comp continuous_sphereCoeff
  refine measurable_pi_lambda _ fun j => ?_
  exact ((((continuous_apply (ι j)).comp hcont).sub
    ((continuous_apply anchor).comp hcont)).measurable).div
      ((((continuous_apply clock).comp hcont).sub
        ((continuous_apply anchor).comp hcont)).measurable)

theorem measurableSet_chainVwaSphere (k : ℕ) (anchor clock : Fin (2 ^ (k + 3)))
    (ι : Fin n → Fin (2 ^ (k + 3))) :
    MeasurableSet (chainVwaSphere k anchor clock ι) :=
  (KleinbockMargulis.measurableSet_vwa).preimage (measurable_chainGapRatioMap k anchor clock ι)

/-- **The very well approximable directions are shell-null.**  The Diophantine condition on the
projective gap ratios is invariant under positive rescaling of the coefficients, so its exceptional
set is a cone, and the ambient extremality statement transfers to the sphere. -/
theorem toSphere_chainVwaSphere_eq_zero (k : ℕ) (hn : 0 < n)
    {anchor clock : Fin (2 ^ (k + 3))} {ι : Fin n → Fin (2 ^ (k + 3))}
    (hι : Function.Injective ι) (hanchor : ∀ j, ι j ≠ anchor) (hclock : ∀ j, ι j ≠ clock)
    (hac : anchor ≠ clock) :
    (volume : Measure (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))))).toSphere
      (chainVwaSphere k anchor clock ι) = 0 := by
  classical
  set hP := chainPauliFin_isHermitian (k + 3) with hPdef
  set Bamb : Set (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3))))) :=
    {x | WithLp.ofLp x ∉ simpleEnsembleLocus hP ∨
      KleinbockMargulis.VWA fun j =>
        anchoredGapRatioMap (sortedEnsembleSpectrum hP (WithLp.ofLp x)) anchor clock ι j}
    with hBdef
  have hmp := PiLp.volume_preserving_ofLp (Fin (Fintype.card (ChainLabel (k + 3))))
  have hnull1 : (volume : Measure (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3))))))
      {x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} = 0 := by
    have hsub : {θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ | θ ∉ simpleEnsembleLocus hP}
        ⊆ {θ | ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues} := by
      intro θ hθ hmax
      exact hθ hmax.injective
    have hbase : (volume : Measure (Fin (Fintype.card (ChainLabel (k + 3))) → ℝ))
        {θ | θ ∉ simpleEnsembleLocus hP} = 0 :=
      measure_mono_null hsub (volume_notMaximallyProjective_chain_eq_zero k)
    have hpre : {x : EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))) |
        WithLp.ofLp x ∉ simpleEnsembleLocus hP}
        = WithLp.ofLp ⁻¹' {θ | θ ∉ simpleEnsembleLocus hP} := rfl
    rw [hpre, hmp.measure_preimage (NullMeasurableSet.of_null hbase), hbase]
  have hnull2 : (volume : Measure (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3))))))
      {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
        KleinbockMargulis.VWA fun j =>
          anchoredGapRatioMap (sortedEnsembleSpectrum hP (WithLp.ofLp x)) anchor clock ι j} = 0 := by
    have hbase : (volume : Measure (Fin (Fintype.card (ChainLabel (k + 3))) → ℝ))
        {θ ∈ simpleEnsembleLocus hP |
          KleinbockMargulis.VWA fun j =>
            anchoredGapRatioMap (sortedEnsembleSpectrum hP θ) anchor clock ι j} = 0 :=
      volume_vwa_sortedGapRatio_eq_zero hn hP
        (chainPauliFin_spectrumEscapesRealRelations k) hι hanchor hclock hac
    have hpre : {x : EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))) |
        WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
          KleinbockMargulis.VWA fun j =>
            anchoredGapRatioMap (sortedEnsembleSpectrum hP (WithLp.ofLp x)) anchor clock ι j}
        = WithLp.ofLp ⁻¹' {θ ∈ simpleEnsembleLocus hP |
            KleinbockMargulis.VWA fun j =>
              anchoredGapRatioMap (sortedEnsembleSpectrum hP θ) anchor clock ι j} := rfl
    rw [hpre, hmp.measure_preimage (NullMeasurableSet.of_null hbase), hbase]
  have hnull : (volume : Measure (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3))))))
      Bamb = 0 := by
    have hsub : Bamb ⊆ {x | WithLp.ofLp x ∉ simpleEnsembleLocus hP}
        ∪ {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            KleinbockMargulis.VWA fun j =>
              anchoredGapRatioMap (sortedEnsembleSpectrum hP (WithLp.ofLp x)) anchor clock ι j} := by
      intro x hx
      rcases hx with h | h
      · exact Or.inl h
      · by_cases hs : WithLp.ofLp x ∈ simpleEnsembleLocus hP
        · exact Or.inr ⟨hs, h⟩
        · exact Or.inl hs
    exact measure_mono_null hsub (measure_union_null hnull1 hnull2)
  have hcone : ∀ r : ℝ, 0 < r → ∀ x ∈ Bamb, r • x ∈ Bamb := by
    intro r hr x hx
    have hofLp : WithLp.ofLp (r • x) = fun a => r * WithLp.ofLp x a := by
      funext a
      rw [PiLp.smul_apply]
      rfl
    rcases hx with hns | hvwa
    · refine Or.inl ?_
      rw [hofLp]
      intro hcon
      exact hns ((mem_simpleEnsembleLocus_const_mul_iff hP hr _).mp hcon)
    · refine Or.inr ?_
      rw [hofLp, anchoredGapRatioMap_sortedEnsembleSpectrum_const_mul hP hr]
      exact hvwa
  refine toSphere_eq_zero_of_scaleInvariant hnull hcone
    (measurableSet_chainVwaSphere k anchor clock ι) ?_
  intro θ hθ
  exact Or.inr hθ

/-- **The very well approximable directions are null in the patch parametrization.** -/
theorem toSphere_preimage_chainVwaSphere_eq_zero (k : ℕ) (hn : 0 < n)
    {anchor clock : Fin (2 ^ (k + 3))} {ι : Fin n → Fin (2 ^ (k + 3))}
    (hι : Function.Injective ι) (hanchor : ∀ j, ι j ≠ anchor) (hclock : ∀ j, ι j ≠ clock)
    (hac : anchor ≠ clock) :
    (volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere
      (patchToCoeff k ⁻¹' chainVwaSphere k anchor clock ι) = 0 := by
  rw [toSphere_preimage_patchToCoeff k (measurableSet_chainVwaSphere k anchor clock ι)]
  exact toSphere_chainVwaSphere_eq_zero k hn hι hanchor hclock hac

end

end GaloisForLFunctions.HTGeometry
