import GaloisForLFunctions.RHTower.FullProjectiveChoiFirstReturnLaw

open Set MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Physical anchored gaps ordered as clock first, then every retained level. -/
def fullAnchoredGapFrequency {I : Type*} {n : ℕ}
    (spec : I → ℝ) (anchor clock : I) (tail : Fin n → I) :
    Fin (n + 1) → ℝ :=
  Fin.cons (spec clock - spec anchor) (fun j => spec (tail j) - spec anchor)

theorem clockScaledFullProjectiveFrequency_anchoredGapRatioMap
    {I : Type*} {n : ℕ} (spec : I → ℝ) (anchor clock : I)
    (tail : Fin n → I) (hgap : spec clock - spec anchor ≠ 0) :
    clockScaledFullProjectiveFrequency (spec clock - spec anchor)
        (anchoredGapRatioMap spec anchor clock tail) =
      fullAnchoredGapFrequency spec anchor clock tail := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [clockScaledFullProjectiveFrequency, fullProjectiveFrequency,
      fullAnchoredGapFrequency]
  · simp only [clockScaledFullProjectiveFrequency, fullProjectiveFrequency,
      fullAnchoredGapFrequency, Fin.cons_succ, anchoredGapRatioMap]
    field_simp

theorem sortedEnsembleSpectrum_clockGap_pos
    {K D : ℕ} {P : Fin K → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) {x : Fin K → ℝ}
    (hx : x ∈ simpleEnsembleLocus hP)
    {anchor clock : Fin D} (hindex : anchor < clock) :
    0 < sortedEnsembleSpectrum hP x clock -
      sortedEnsembleSpectrum hP x anchor := by
  have hmono := monotone_sortedTuple
    (isHermitian_spectralEnsembleMatrix hP x).eigenvalues hindex.le
  have hne : sortedEnsembleSpectrum hP x anchor ≠
      sortedEnsembleSpectrum hP x clock := by
    intro heq
    exact (ne_of_lt hindex) (injective_sortedEnsembleSpectrum hP hx heq)
  exact sub_pos.mpr (lt_of_le_of_ne hmono hne)

theorem chainFullProjective_clockGap_pos
    (k : ℕ)
    {x : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ}
    (hx : x ∈ simpleEnsembleLocus (chainPauliFin_isHermitian (k + 3))) :
    0 < sortedEnsembleSpectrum (chainPauliFin_isHermitian (k + 3)) x
          (chainFullProjectiveClock k) -
        sortedEnsembleSpectrum (chainPauliFin_isHermitian (k + 3)) x
          (chainFullProjectiveAnchor k) := by
  apply sortedEnsembleSpectrum_clockGap_pos
    (chainPauliFin_isHermitian (k + 3)) hx
  exact Fin.mk_lt_mk.mpr (by norm_num)

def chainFullProjectiveSpectrum (k : ℕ)
    (x : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ) :
    Fin (2 ^ (k + 3)) → ℝ :=
  sortedEnsembleSpectrum (chainPauliFin_isHermitian (k + 3)) x

def chainFullProjectiveClockGap (k : ℕ)
    (x : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ) : ℝ :=
  chainFullProjectiveSpectrum k x (chainFullProjectiveClock k) -
    chainFullProjectiveSpectrum k x (chainFullProjectiveAnchor k)

def chainFullProjectiveRatioPacket (k : ℕ)
    (x : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ) :
    Fin (2 ^ (k + 3) - 2) → ℝ :=
  anchoredGapRatioMap (chainFullProjectiveSpectrum k x)
    (chainFullProjectiveAnchor k) (chainFullProjectiveClock k)
    (chainFullProjectiveTailIndex k)

def chainFullProjectivePhysicalFrequency (k : ℕ)
    (x : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ) :
    Fin ((2 ^ (k + 3) - 2) + 1) → ℝ :=
  fullAnchoredGapFrequency (chainFullProjectiveSpectrum k x)
    (chainFullProjectiveAnchor k) (chainFullProjectiveClock k)
    (chainFullProjectiveTailIndex k)

/-- **Physical one-draw full-spectrum law.** The lowest spectral gap is
positive, rescales the complete ratio packet back to every physical anchored
gap exactly, and the same draw satisfies the adaptive first-return law. -/
theorem chainFullSpectrum_hasPhysicalFullProjectiveChoiTensorFirstReturnLaw_ae_stdGaussian
    (k : ℕ) :
    ∀ᵐ z ∂(ProbabilityTheory.stdGaussian
      (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))))),
      let x := WithLp.ofLp z
      x ∈ simpleEnsembleLocus (chainPauliFin_isHermitian (k + 3)) ∧
      0 < chainFullProjectiveClockGap k x ∧
      HasFullProjectiveChoiTensorFirstReturnDichotomy
        (chainFullProjectiveRatioPacket k x) ∧
      clockScaledFullProjectiveFrequency (chainFullProjectiveClockGap k x)
          (chainFullProjectiveRatioPacket k x) =
        chainFullProjectivePhysicalFrequency k x := by
  filter_upwards
    [chainFullGapRatio_hasFullProjectiveChoiTensorFirstReturnDichotomy_ae_stdGaussian k]
      with z hz
  let x := WithLp.ofLp z
  have hgap : 0 < chainFullProjectiveClockGap k x := by
    exact chainFullProjective_clockGap_pos k hz.1
  have hfrequency :=
    clockScaledFullProjectiveFrequency_anchoredGapRatioMap
      (chainFullProjectiveSpectrum k x)
      (chainFullProjectiveAnchor k) (chainFullProjectiveClock k)
      (chainFullProjectiveTailIndex k) hgap.ne'
  exact ⟨hz.1, hgap, hz.2, by
    simpa only [chainFullProjectiveClockGap, chainFullProjectiveRatioPacket,
      chainFullProjectivePhysicalFrequency] using hfrequency⟩

end RHTower
