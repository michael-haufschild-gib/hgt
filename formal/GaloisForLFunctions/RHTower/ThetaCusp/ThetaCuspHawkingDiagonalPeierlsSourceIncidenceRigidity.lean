import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTargetIndependentFullCokernelPeierlsRealization

/-!
# Diagonal Peierls source-incidence rigidity

An arbitrary copy-diagonal symplectic Peierls propagator realizes exact unit BM source incidence
at a Xi fibre exactly when either the source vanishes on the critical line or the propagator weight
equals the canonical BM radial weight. Globally, all incidence-realizing diagonal Green jumps are
the canonical jump plus an arbitrary defect supported on critical-line copies.

`[NEW] [GREEN-JUMP RIGIDITY] [SOURCE INCIDENCE] [EXACT CLASSIFICATION] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Packet diagonal with an arbitrary copywise Green-jump weight. -/
def hbXiPeierlsWeightedDiagonal
    (w : XiZeroCopy → ℂ) (f : HBXiPeierlsPacket) : HBXiPeierlsPacket where
  support := f.support.filter (fun q => w q * f q ≠ 0)
  toFun := fun q => w q * f q
  mem_support_toFun := by
    intro q
    simp only [Finset.mem_filter, Finsupp.mem_support_iff]
    constructor
    · exact And.right
    · intro h
      refine ⟨?_, h⟩
      intro hf
      apply h
      rw [hf, mul_zero]

@[simp]
theorem hbXiPeierlsWeightedDiagonal_apply
    (w : XiZeroCopy → ℂ) (f : HBXiPeierlsPacket) (q : XiZeroCopy) :
    hbXiPeierlsWeightedDiagonal w f q = w q * f q := rfl

@[simp]
theorem hbXiPeierlsWeightedDiagonal_single
    (w : XiZeroCopy → ℂ) (q : XiZeroCopy) (c : ℂ) :
    hbXiPeierlsWeightedDiagonal w (Finsupp.single q c) =
      Finsupp.single q (w q * c) := by
  classical
  ext r
  by_cases h : r = q
  · subst r
    simp
  · simp [h]

/-- Arbitrary copy-diagonal packet map. -/
def hbXiPeierlsWeightedDiagonalLinear (w : XiZeroCopy → ℂ) :
    HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket where
  toFun := hbXiPeierlsWeightedDiagonal w
  map_add' f g := by
    ext q
    simp [mul_add]
  map_smul' c f := by
    ext q
    simp
    ring

/-- Arbitrary copy-diagonal symplectic Peierls propagator. -/
def hbXiPeierlsWeightedPropagator (w : XiZeroCopy → ℂ) :
    HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier where
  toFun f := (-hbXiPeierlsWeightedDiagonal w f.2,
    hbXiPeierlsWeightedDiagonal w f.1)
  map_add' f g := by
    ext q <;> simp [mul_add, add_comm]
  map_smul' c f := by
    ext q <;> simp <;> ring

@[simp]
theorem hbXiPeierlsWeightedPropagator_apply
    (w : XiZeroCopy → ℂ) (f : HBXiPeierlsCarrier) :
    hbXiPeierlsWeightedPropagator w f =
      (-hbXiPeierlsWeightedDiagonal w f.2,
        hbXiPeierlsWeightedDiagonal w f.1) := rfl

/-- The corpus's canonical BM propagator is exactly the arbitrary-weight construction specialized
to the BM radial weight. -/
theorem hbXiPeierlsWeightedPropagator_radialWeight (n : ℕ) :
    hbXiPeierlsWeightedPropagator (hbXiPeierlsRadialWeight n) =
      hbXiPeierlsPropagator n := by
  apply LinearMap.ext
  intro f
  apply Prod.ext <;> ext q <;> rfl

theorem hbXiPeierlsDot_weightedDiagonal_single_single
    (w : XiZeroCopy → ℂ) (q : XiZeroCopy) (c d : ℂ) :
    hbXiPeierlsDot (hbXiPeierlsWeightedDiagonal w (Finsupp.single q c))
        (Finsupp.single q d) = w q * c * d := by
  classical
  rw [hbXiPeierlsWeightedDiagonal_single]
  unfold hbXiPeierlsDot
  rw [Finsupp.linearCombination_apply, Finsupp.sum_single_index]
  · simp
  · simp

theorem hbXiPeierlsDot_weightedDiagonal_comm
    (w : XiZeroCopy → ℂ) (f g : HBXiPeierlsPacket) :
    hbXiPeierlsDot (hbXiPeierlsWeightedDiagonal w f) g =
      hbXiPeierlsDot f (hbXiPeierlsWeightedDiagonal w g) := by
  classical
  unfold hbXiPeierlsDot
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  change (∑ q ∈ (hbXiPeierlsWeightedDiagonal w f).support,
      w q * f q * g q) =
    ∑ q ∈ f.support, f q * (w q * g q)
  rw [Finset.sum_subset]
  · apply Finset.sum_congr rfl
    intro q hq
    ring
  · intro q hq
    change q ∈ f.support.filter (fun r => w r * f r ≠ 0) at hq
    exact (Finset.mem_filter.mp hq).1
  · intro q hq hnot
    have hprod : w q * f q = 0 := by
      by_contra hp
      apply hnot
      change q ∈ f.support.filter (fun r => w r * f r ≠ 0)
      exact Finset.mem_filter.mpr ⟨hq, hp⟩
    calc
      w q * f q * g q = (w q * f q) * g q := rfl
      _ = 0 := by rw [hprod, zero_mul]

/-- Every arbitrary copy-diagonal symplectic propagator remains Peierls-skew. -/
theorem hbXiPeierlsWeightedSourcePairing_skew
    (w : XiZeroCopy → ℂ) (f g : HBXiPeierlsCarrier) :
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
        (hbXiPeierlsWeightedPropagator w) f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
        (hbXiPeierlsWeightedPropagator w) g f := by
  simp only [d4GaugeFixedTeukolskyPeierlsSourcePairing,
    hbXiPeierlsPairing_apply, hbXiPeierlsWeightedPropagator_apply,
    hbXiPeierlsDot_neg_left]
  rw [hbXiPeierlsDot_comm (hbXiPeierlsWeightedDiagonal w g.2) f.1,
    hbXiPeierlsDot_comm (hbXiPeierlsWeightedDiagonal w g.1) f.2,
    hbXiPeierlsDot_weightedDiagonal_comm,
    hbXiPeierlsDot_weightedDiagonal_comm]
  ring

/-- Exact arbitrary-weight pairing of the literal BM source axes. -/
theorem hbXiPeierlsWeighted_sourcePairing_eq
    (w : XiZeroCopy → ℂ) (amplitude : ℂ) (q : XiZeroCopy) :
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
        (hbXiPeierlsWeightedPropagator w)
        (hbXiPeierlsPlusSource amplitude q)
        (hbXiPeierlsMinusSource amplitude q) =
      w q * Complex.normSq
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q) := by
  classical
  change hbXiPeierlsDot (0 : HBXiPeierlsPacket) 0 +
      hbXiPeierlsDot (hbXiPeierlsWeightedDiagonal w
        (Finsupp.single q (d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q)))
        (Finsupp.single q ((starRingEnd ℂ)
          (d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q))) = _
  rw [hbXiPeierlsDot_weightedDiagonal_single_single]
  simp only [hbXiPeierlsDot, map_zero, zero_add]
  rw [← Complex.mul_conj]
  ring

/-- Unit-source exact BM incidence for an arbitrary diagonal Green-jump field. -/
def HBXiPeierlsUnitDiagonalSourceIncidence
    (n : ℕ) (w : XiZeroCopy → ℂ) (q : XiZeroCopy) : Prop :=
  d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
      (hbXiPeierlsWeightedPropagator w)
      (hbXiPeierlsPlusSource 1 q)
      (hbXiPeierlsMinusSource 1 q) =
    d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q

/-- Sharp fibre classification: source incidence either sees the critical-line zero source or
forces the unique canonical BM radial Green-jump weight. -/
theorem hbXiPeierlsUnitDiagonalSourceIncidence_iff
    (n : ℕ) (w : XiZeroCopy → ℂ) (q : XiZeroCopy) :
    HBXiPeierlsUnitDiagonalSourceIncidence n w q ↔
      (q.1 : ℂ).re = 1 / 2 ∨ w q = hbXiPeierlsRadialWeight n q := by
  rw [HBXiPeierlsUnitDiagonalSourceIncidence,
    hbXiPeierlsWeighted_sourcePairing_eq,
    d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant_eq_radialWeight_mul_normSq]
  constructor
  · intro h
    by_cases hline : (q.1 : ℂ).re = 1 / 2
    · exact Or.inl hline
    · right
      have ha : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q ≠ 0 :=
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff
          (by norm_num) q).not.mpr hline
      have hnorm : (Complex.normSq
          (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]
        exact (Complex.normSq_eq_zero.not).2 ha
      exact mul_right_cancel₀ hnorm h
  · rintro (hline | hw)
    · have ha : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q = 0 :=
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff
          (show (1 : ℂ) ≠ 0 by norm_num) q).2 hline
      rw [ha]
      simp
    · rw [hw]

/-- Universal unit BM incidence for one arbitrary copy-diagonal Green-jump field. -/
def HBXiPeierlsUniversalUnitDiagonalSourceIncidence
    (n : ℕ) (w : XiZeroCopy → ℂ) : Prop :=
  ∀ q : XiZeroCopy, HBXiPeierlsUnitDiagonalSourceIncidence n w q

/-- Global rigidity: exact incidence fixes the Green jump precisely on source-active tilted
fibres and leaves only critical-line-supported freedom. -/
theorem hbXiPeierlsUniversalUnitDiagonalSourceIncidence_iff_tiltedAgreement
    (n : ℕ) (w : XiZeroCopy → ℂ) :
    HBXiPeierlsUniversalUnitDiagonalSourceIncidence n w ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
        w q = hbXiPeierlsRadialWeight n q := by
  unfold HBXiPeierlsUniversalUnitDiagonalSourceIncidence
  constructor
  · intro h q htilt
    exact ((hbXiPeierlsUnitDiagonalSourceIncidence_iff n w q).1
      (h q)).resolve_left htilt
  · intro h q
    apply (hbXiPeierlsUnitDiagonalSourceIncidence_iff n w q).2
    by_cases hline : (q.1 : ℂ).re = 1 / 2
    · exact Or.inl hline
    · exact Or.inr (h q hline)

/-- The residual freedom in a diagonal Green jump is supported only on source-extinct critical-line
copies. -/
def HBXiPeierlsDiagonalWeightDefectSupportedOnCriticalLine
    (n : ℕ) (w : XiZeroCopy → ℂ) : Prop :=
  ∀ q : XiZeroCopy, w q - hbXiPeierlsRadialWeight n q ≠ 0 →
    (q.1 : ℂ).re = 1 / 2

/-- Exact affine classification: universal source incidence means canonical BM radial weight plus
an arbitrary defect supported on critical-line copies. -/
theorem hbXiPeierlsUniversalUnitDiagonalSourceIncidence_iff_defectSupportedOnCriticalLine
    (n : ℕ) (w : XiZeroCopy → ℂ) :
    HBXiPeierlsUniversalUnitDiagonalSourceIncidence n w ↔
      HBXiPeierlsDiagonalWeightDefectSupportedOnCriticalLine n w := by
  rw [hbXiPeierlsUniversalUnitDiagonalSourceIncidence_iff_tiltedAgreement]
  unfold HBXiPeierlsDiagonalWeightDefectSupportedOnCriticalLine
  constructor
  · intro h q hdef
    by_contra htilt
    apply hdef
    rw [h q htilt, sub_self]
  · intro h q htilt
    by_contra hweight
    exact htilt (h q (sub_ne_zero.mpr hweight))

/-- Canonical BM radial weights satisfy universal exact incidence. -/
theorem hbXiPeierlsUniversalUnitDiagonalSourceIncidence_radialWeight
    (n : ℕ) :
    HBXiPeierlsUniversalUnitDiagonalSourceIncidence n
      (hbXiPeierlsRadialWeight n) := by
  rw [hbXiPeierlsUniversalUnitDiagonalSourceIncidence_iff_tiltedAgreement]
  intro q htilt
  rfl

end

end RHTower
