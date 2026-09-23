import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyContraction
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiTrueWienerHopfFactorization

/-!
# Unitary-saturation trichotomy for the Xi Ward--Hardy transport

The complete Schwarz-paired strict-right Xi phase is contractive for every
positive right-half-plane node and aperture. This module proves the sharp
global classification:

* if RH is false, every such phase is strictly contractive;
* if RH holds, the strict-right divisor is empty and every phase is one;
* hence unitary saturation, rather than contractivity, is exactly RH;
* equivalently, the complete anti-causal Ward transport vanishes exactly
  under RH.

The strict implication is genuinely cofinal. One actual strict-right Schwarz
pair gives a strict bound on every sufficiently large finite product, and the
bound passes to the existing infinite canonical-product transport. No finite
section, diagonal minor, estimate on zeta, or computation is used.
-/

open Complex Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A positive real aperture makes every right-half-plane Cayley factor
strictly contractive. -/
theorem norm_xiWardHalfPlaneCayleyFactor_lt_one
    {lam w : ℂ} {alpha : ℝ}
    (hlam : 0 < lam.re) (hw : 0 < w.re) (ha : 0 < alpha) :
    ‖xiWardHalfPlaneCayleyFactor lam w alpha‖ < 1 := by
  have hx : 0 < (w + lam).re := by
    simp only [Complex.add_re]
    linarith
  have hden : w + lam + (alpha : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith
  rw [xiWardHalfPlaneCayleyFactor, norm_div,
    div_lt_one (norm_pos_iff.mpr hden)]
  have hsquare :
      ‖w + lam - (alpha : ℂ)‖ ^ (2 : ℕ) <
        ‖w + lam + (alpha : ℂ)‖ ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith
  nlinarith [norm_nonneg (w + lam - (alpha : ℂ)),
    norm_nonneg (w + lam + (alpha : ℂ))]

/-- Source specialization of strict Cayley contractivity to one actual
strict-right Xi divisor copy. -/
theorem norm_xiWardCayleyFactor_lt_one
    (q : XiRightZeroCopy) {w : ℂ} {alpha : ℝ}
    (hw : 0 < w.re) (ha : 0 < alpha) :
    ‖xiWardCayleyFactor q w alpha‖ < 1 :=
  norm_xiWardHalfPlaneCayleyFactor_lt_one q.2 hw ha

/-- Every complete strict-right Schwarz pair is strictly contractive. -/
theorem norm_xiWardSchwarzPairCayleyFactor_lt_one
    (q : XiRightUpperZeroCopy) {w : ℂ} {alpha : ℝ}
    (hw : 0 < w.re) (ha : 0 < alpha) :
    ‖xiWardSchwarzPairCayleyFactor q w alpha‖ < 1 := by
  rw [xiWardSchwarzPairCayleyFactor, norm_mul]
  have hleft :=
    norm_xiWardCayleyFactor_lt_one q.1 hw ha
  have hright :=
    norm_xiWardCayleyFactor_lt_one
      (xiRightZeroCopyConjEquiv q.1) hw ha
  calc
    ‖xiWardCayleyFactor q.1 w alpha‖ *
          ‖xiWardCayleyFactor (xiRightZeroCopyConjEquiv q.1) w alpha‖
        ≤ ‖xiWardCayleyFactor q.1 w alpha‖ * 1 := by
          exact mul_le_mul_of_nonneg_left hright.le (norm_nonneg _)
    _ < 1 := by simpa only [mul_one] using hleft

/-- Failure of RH supplies an actual upper representative of a strict-right
Xi Schwarz pair. -/
theorem nonempty_xiRightUpperZeroCopy_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    Nonempty XiRightUpperZeroCopy := by
  obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
  obtain q' | q' := xiRightSchwarzPairEquiv.symm q
  · exact ⟨q'⟩
  · exact ⟨q'⟩

/-- **Strict cofinal contraction under false RH.** One actual Schwarz pair
bounds every sufficiently large product strictly below one, hence bounds the
complete canonical-product phase strictly below one. -/
theorem
    norm_xiRightWardBoundarySourcePhaseCrossRatio_lt_one_of_not_riemannHypothesis
    {w : ℂ} {alpha : ℝ} (hw : 0 < w.re) (ha : 0 < alpha)
    (hRH : ¬ RiemannHypothesis) :
    ‖xiRightWardBoundarySourcePhaseCrossRatio
        (I * w) (alpha : ℂ)‖ < 1 := by
  obtain ⟨q₀⟩ :=
    nonempty_xiRightUpperZeroCopy_of_not_riemannHypothesis hRH
  have hq₀ :
      ‖xiWardSchwarzPairCayleyFactor q₀ w alpha‖ < 1 :=
    norm_xiWardSchwarzPairCayleyFactor_lt_one q₀ hw ha
  have hprod :=
    xiRightWardBoundarySourcePhaseCrossRatio_hasProd_cayley hw ha.le
  have hnorm := hprod.norm
  have hle :
      ‖xiRightWardBoundarySourcePhaseCrossRatio
          (I * w) (alpha : ℂ)‖ ≤
        ‖xiWardSchwarzPairCayleyFactor q₀ w alpha‖ := by
    rw [HasProd] at hnorm
    apply le_of_tendsto hnorm
    filter_upwards
      [eventually_ge_atTop ({q₀} : Finset XiRightUpperZeroCopy)] with s hs
    have hqmem : q₀ ∈ s := hs (by simp)
    rw [← Finset.prod_erase_mul s
      (fun q : XiRightUpperZeroCopy =>
        ‖xiWardSchwarzPairCayleyFactor q w alpha‖) hqmem]
    have herase :
        (∏ q ∈ s.erase q₀,
          ‖xiWardSchwarzPairCayleyFactor q w alpha‖) ≤ 1 := by
      exact Finset.prod_le_one
        (fun q _ => norm_nonneg _)
        (fun q _ =>
          norm_xiWardSchwarzPairCayleyFactor_le_one q hw ha.le)
    exact mul_le_of_le_one_left (norm_nonneg _) herase
  exact hle.trans_lt hq₀

/-- Under RH the strict-right divisor is empty, so the complete normalized
Ward phase is the empty product. -/
theorem xiRightWardBoundarySourcePhaseCrossRatio_eq_one_of_riemannHypothesis
    (hRH : RiemannHypothesis) (w : ℂ) (alpha : ℝ) :
    xiRightWardBoundarySourcePhaseCrossRatio
        (I * w) (alpha : ℂ) = 1 := by
  letI := isEmpty_xiRightZeroCopy_of_riemannHypothesis hRH
  simp [xiRightWardBoundarySourcePhaseCrossRatio,
    xiRightWardSourcePhase, xiRightCanonicalProduct,
    canonicalProductE1Indexed,
    xiAntiCausalWardBoundarySourcePhase,
    xiAntiCausalWardBoundarySelfSymbol]

/-- **Unitary-saturation law.** At any one positive right-half-plane node
and positive aperture, saturation of the complete Ward--Hardy contraction is
equivalent to RH. -/
theorem
    riemannHypothesis_iff_norm_xiRightWardBoundarySourcePhaseCrossRatio_eq_one
    {w : ℂ} {alpha : ℝ} (hw : 0 < w.re) (ha : 0 < alpha) :
    RiemannHypothesis ↔
      ‖xiRightWardBoundarySourcePhaseCrossRatio
          (I * w) (alpha : ℂ)‖ = 1 := by
  constructor
  · intro hRH
    rw [xiRightWardBoundarySourcePhaseCrossRatio_eq_one_of_riemannHypothesis
      hRH w alpha]
    norm_num
  · intro hnorm
    by_contra hRH
    have hstrict :=
      norm_xiRightWardBoundarySourcePhaseCrossRatio_lt_one_of_not_riemannHypothesis
        hw ha hRH
    rw [hnorm] at hstrict
    exact (lt_irrefl 1) hstrict

/-- Exact complementary orientation: strict contractivity is equivalent to
failure of RH, not evidence for RH. -/
theorem
    not_riemannHypothesis_iff_norm_xiRightWardBoundarySourcePhaseCrossRatio_lt_one
    {w : ℂ} {alpha : ℝ} (hw : 0 < w.re) (ha : 0 < alpha) :
    ¬ RiemannHypothesis ↔
      ‖xiRightWardBoundarySourcePhaseCrossRatio
          (I * w) (alpha : ℂ)‖ < 1 := by
  constructor
  · exact
      norm_xiRightWardBoundarySourcePhaseCrossRatio_lt_one_of_not_riemannHypothesis
        hw ha
  · intro hstrict hRH
    rw [xiRightWardBoundarySourcePhaseCrossRatio_eq_one_of_riemannHypothesis
      hRH w alpha] at hstrict
    norm_num at hstrict

/-- Vanishing of the complete anti-causal Ward transport at any one positive
node and aperture is equivalent to RH. -/
theorem riemannHypothesis_iff_mobiusGammaXiAntiCausalWardTransportV_eq_zero
    {w : ℂ} {alpha : ℝ} (hw : 0 < w.re) (ha : 0 < alpha) :
    RiemannHypothesis ↔
      mobiusGammaXiAntiCausalWardTransportV w (alpha : ℂ) = 0 := by
  rw [mobiusGammaXiAntiCausalWardTransportV_eq_one_sub_phase hw]
  constructor
  · intro hRH
    rw [xiRightWardBoundarySourcePhaseCrossRatio_eq_one_of_riemannHypothesis
      hRH w alpha]
    ring
  · intro hzero
    have hphase :
        xiRightWardBoundarySourcePhaseCrossRatio
            (I * w) (alpha : ℂ) = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    apply
      (riemannHypothesis_iff_norm_xiRightWardBoundarySourcePhaseCrossRatio_eq_one
        hw ha).mpr
    rw [hphase]
    norm_num

/-- Nonvanishing of the complete anti-causal Ward transport has the opposite
classification: it is equivalent to failure of RH. -/
theorem
    not_riemannHypothesis_iff_mobiusGammaXiAntiCausalWardTransportV_ne_zero
    {w : ℂ} {alpha : ℝ} (hw : 0 < w.re) (ha : 0 < alpha) :
    ¬ RiemannHypothesis ↔
      mobiusGammaXiAntiCausalWardTransportV w (alpha : ℂ) ≠ 0 := by
  simpa only [ne_eq] using
    not_congr
      (riemannHypothesis_iff_mobiusGammaXiAntiCausalWardTransportV_eq_zero
        hw ha)

/-- Complete source-specific trichotomy. Ordinary contractivity is
unconditional; strict contraction detects false RH; unitary saturation and
transport vanishing detect RH. -/
theorem xiWardHardyUnitarySaturationTrichotomy
    {w : ℂ} {alpha : ℝ} (hw : 0 < w.re) (ha : 0 < alpha) :
    (‖xiRightWardBoundarySourcePhaseCrossRatio
        (I * w) (alpha : ℂ)‖ ≤ 1) ∧
    (RiemannHypothesis ↔
      ‖xiRightWardBoundarySourcePhaseCrossRatio
        (I * w) (alpha : ℂ)‖ = 1) ∧
    (¬ RiemannHypothesis ↔
      ‖xiRightWardBoundarySourcePhaseCrossRatio
        (I * w) (alpha : ℂ)‖ < 1) ∧
    (RiemannHypothesis ↔
      mobiusGammaXiAntiCausalWardTransportV w (alpha : ℂ) = 0) := by
  exact ⟨
    norm_xiRightWardBoundarySourcePhaseCrossRatio_le_one hw ha.le,
    riemannHypothesis_iff_norm_xiRightWardBoundarySourcePhaseCrossRatio_eq_one
      hw ha,
    not_riemannHypothesis_iff_norm_xiRightWardBoundarySourcePhaseCrossRatio_lt_one
      hw ha,
    riemannHypothesis_iff_mobiusGammaXiAntiCausalWardTransportV_eq_zero
      hw ha⟩

end

end RHTower
