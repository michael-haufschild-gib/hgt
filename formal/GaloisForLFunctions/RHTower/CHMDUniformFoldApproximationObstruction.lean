import GaloisForLFunctions.RHTower.CHMDShadowTemporalSpectrum
import GaloisForLFunctions.RHTower.CHMDArchimedeanBoundarySingularity

/-!
# Uniform finite-fold approximation is impossible

An actual zero gives an explicit positive separation from every finite fold
combination. The proof is unconditional: a putative small uniform error would
first imply boundedness and hence RH; the resulting zero atom then contradicts
that error bound. This excludes uniform approximation, not uniform boundedness.
-/

open MeasureTheory Filter Set Topology Zeta23
open scoped Real

namespace RHTower.CHMDChebyshevTransport

open RHTower.CHMDLightCone RHTower.CHMDForcedMeasure RHTower.CHMDGrowthCollapse
open WeilOneSided

noncomputable section

/-- Every actual zero supplies a positive uniform distance from all finite folds. -/
theorem finite_mobiusFold_uniform_separation {ι : Type*} (ρ : zetaZeroConfig.carrier)
    (s : Finset ι) (a v : ι → ℝ) (hs : ∀ i ∈ s, 0 ≤ v i) :
    ∃ y : ℝ, 0 ≤ y ∧ kgAtomWeight ρ / 2 ≤
      |foldedMobiusWave y - ∑ i ∈ s, a i * mobiusFold y (v i)| := by
  classical
  have hfinite := finite_mobiusFold_hasTemporalCoefficient_zero s a v hs
    (re_kgFreq_pos ρ) (poleFrequency_ne_kgAtom ρ)
  by_contra hnone
  have herror (y : ℝ) (hy : 0 ≤ y) :
      |foldedMobiusWave y - ∑ i ∈ s, a i * mobiusFold y (v i)| ≤ kgAtomWeight ρ / 2 :=
    (lt_of_not_ge (fun h => hnone ⟨y, hy, h⟩)).le
  obtain ⟨C, hC⟩ := hfinite.bound
  have hRH : RiemannHypothesis := by
    apply riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddBelow.mpr
    refine ⟨4 / π + C + kgAtomWeight ρ / 2, fun y hy => ?_⟩
    have ht := chebyshevDiscrepancyTransport_eq_sub_tsum_mobiusFold y
    change chebyshevDiscrepancyTransport y = chmdPrimeKernel y 0 - foldedMobiusWave y at ht
    have hk := (abs_le.mp (abs_chmdPrimeKernel_le y 0)).1
    have hg := (abs_le.mp (hC y)).2
    have he := (abs_le.mp (herror y hy)).2
    linarith
  have hdiff := (foldedMobiusWave_hasTemporalCoefficient_of_rh hRH
    (re_kgFreq_pos ρ)).sub hfinite
  have hmass : shadowTemporalMass (kgAtom ρ) - 0 ≤ kgAtomWeight ρ / 2 :=
    le_of_tendsto hdiff.limit ((eventually_ge_atTop (0 : ℝ)).mono fun T hT =>
      (le_abs_self _).trans (abs_temporalCosineAverage_le herror (kgAtom ρ) hT))
  have hpos := kgAtomWeight_pos ρ
  have hle := kgAtomWeight_le_shadowTemporalMass ρ
  linarith

/-- There is one positive separation constant for every finite fold combination. -/
theorem exists_uniform_separation_finite_mobiusFold :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (s : Finset ℝ) (a : ℝ → ℝ),
      (∀ v ∈ s, 0 ≤ v) → ∃ y : ℝ, 0 ≤ y ∧
        δ ≤ |foldedMobiusWave y - ∑ v ∈ s, a v * mobiusFold y v| := by
  obtain ⟨z, hz⟩ := zetaZeroConfig_carrier_infinite.nonempty
  let ρ : zetaZeroConfig.carrier := ⟨z, hz⟩
  exact ⟨kgAtomWeight ρ / 2, div_pos (kgAtomWeight_pos ρ) (by norm_num),
    fun s a hs => finite_mobiusFold_uniform_separation ρ s a id hs⟩

/-- Truncating the actual Möbius series leaves an error bounded away from zero
at some nonnegative rapidity, for every cutoff. -/
theorem exists_uniform_separation_mobiusFold_truncations :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ y : ℝ, 0 ≤ y ∧
      δ ≤ |foldedMobiusWave y -
        ∑ m ∈ Finset.range N, moebiusCoeff m * mobiusFold y (Real.log m)| := by
  obtain ⟨z, hz⟩ := zetaZeroConfig_carrier_infinite.nonempty
  let ρ : zetaZeroConfig.carrier := ⟨z, hz⟩
  refine ⟨kgAtomWeight ρ / 2, div_pos (kgAtomWeight_pos ρ) (by norm_num), fun N => ?_⟩
  exact finite_mobiusFold_uniform_separation ρ (Finset.range N) moebiusCoeff
    (fun m => Real.log m) (fun m _ => Real.log_natCast_nonneg m)

end

end RHTower.CHMDChebyshevTransport
