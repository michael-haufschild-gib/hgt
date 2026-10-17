import GaloisForLFunctions.BiScaleUncertainty.DyadicSchurCollarEnergy

/-!
# Monotone optimized Schur-capped source certificates

Optimize physical allocations, then take the finite envelope over grid cutoffs.
The resulting monotone sequence dominates every previous full-grid capped
certificate, is bounded by total physical tail mass, and bounds the actual
normalized source energy. Its limit is not identified with the sharp source
infimum or with the earlier paired-sphere limit.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
namespace PhysicalCollarPartition

def schurCappedOptimalCoefficient (n : ℕ) : ℝ :=
  sSup (Set.range (fun ρ : PhysicalCollarPartition n => ρ.schurCappedCoefficient))

theorem schurCappedCoefficient_range_bddAbove {n : ℕ} (hn : 2 ≤ n) :
    BddAbove (Set.range (fun ρ : PhysicalCollarPartition n => ρ.schurCappedCoefficient)) := by
  refine ⟨collarTailMass, ?_⟩
  rintro c ⟨ρ, rfl⟩
  exact ρ.schurCappedCoefficient_le_tailMass hn

theorem schurCappedCoefficient_le_optimal {n : ℕ} (hn : 2 ≤ n) (ρ : PhysicalCollarPartition n) :
    ρ.schurCappedCoefficient ≤ schurCappedOptimalCoefficient n :=
  le_csSup (schurCappedCoefficient_range_bddAbove hn) ⟨ρ, rfl⟩

theorem schurCappedOptimalCoefficient_le_tailMass {n : ℕ} (hn : 2 ≤ n) :
    schurCappedOptimalCoefficient n ≤ collarTailMass := by
  apply csSup_le
  · exact ⟨(equalMultiplicity n).schurCappedCoefficient, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact ρ.schurCappedCoefficient_le_tailMass hn

theorem cappedOptimalCoefficient_le_schurCappedOptimal {n : ℕ} (hn : 2 ≤ n) :
    cappedOptimalCoefficient n (productAdmittedCutoff n) ≤ schurCappedOptimalCoefficient n := by
  apply csSup_le
  · exact ⟨(equalMultiplicity n).cappedCoefficient (productAdmittedCutoff n), equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact (ρ.cappedCoefficient_le_schurCappedCoefficient hn).trans (ρ.schurCappedCoefficient_le_optimal hn)

theorem schurCappedOptimalCoefficient_source_energy {n : ℕ} (hn : 2 ≤ n)
    (f : LogarithmicGridSource n) :
    ENNReal.ofReal (schurCappedOptimalCoefficient n * autocorr f.1 0) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  let E := ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
    continuousArchIncrementDensity (compactAutocorrKernel f.1) x
  change ENNReal.ofReal (schurCappedOptimalCoefficient n * autocorr f.1 0) ≤ E
  by_cases hE : E = ∞
  · rw [hE]
    exact le_top
  by_cases hR : autocorr f.1 0 = 0
  · simp [hR]
  have hRp : 0 < autocorr f.1 0 := lt_of_le_of_ne (autocorr_zero_nonneg f.1) (Ne.symm hR)
  apply (ENNReal.ofReal_le_iff_le_toReal hE).2
  apply (le_div_iff₀ hRp).1
  apply csSup_le
  · exact ⟨(equalMultiplicity n).schurCappedCoefficient, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact (le_div_iff₀ hRp).2
      ((ENNReal.ofReal_le_iff_le_toReal hE).1 (ρ.schurCappedCoefficient_source_energy hn f))

end PhysicalCollarPartition

/-- The small grids retain their already verified independent certificate. -/
def rawSchurCappedCoefficient (n : ℕ) : ℝ :=
  if 2 ≤ n then PhysicalCollarPartition.schurCappedOptimalCoefficient n
  else PhysicalCollarPartition.optimalCoefficient n

def monotoneSchurCappedCoefficient (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, by simp⟩ rawSchurCappedCoefficient

theorem rawSchurCappedCoefficient_le_tailMass (n : ℕ) : rawSchurCappedCoefficient n ≤ collarTailMass := by
  unfold rawSchurCappedCoefficient
  split_ifs with hn
  · exact PhysicalCollarPartition.schurCappedOptimalCoefficient_le_tailMass hn
  · exact optimalCoefficient_le_collarTailMass n

theorem fullGridCapped_le_rawSchurCapped (n : ℕ) :
    fullGridCappedCollarCoefficient n ≤ rawSchurCappedCoefficient n := by
  unfold fullGridCappedCollarCoefficient rawSchurCappedCoefficient
  split_ifs with hn
  · exact PhysicalCollarPartition.cappedOptimalCoefficient_le_schurCappedOptimal hn
  · exact le_rfl

theorem rawSchurCapped_le_monotone (n : ℕ) :
    rawSchurCappedCoefficient n ≤ monotoneSchurCappedCoefficient n :=
  Finset.le_sup' _ (Finset.mem_range.mpr (by omega))

theorem fullGridCapped_le_monotoneSchurCapped (n : ℕ) :
    fullGridCappedCollarCoefficient n ≤ monotoneSchurCappedCoefficient n :=
  (fullGridCapped_le_rawSchurCapped n).trans (rawSchurCapped_le_monotone n)

theorem monotoneSchurCappedCoefficient_monotone : Monotone monotoneSchurCappedCoefficient := by
  intro n m hnm
  apply Finset.sup'_le
  intro k hk
  exact Finset.le_sup' _ (Finset.mem_range.mpr (by
    have h := Finset.mem_range.mp hk
    omega))

theorem monotoneSchurCappedCoefficient_pos (n : ℕ) : 0 < monotoneSchurCappedCoefficient n :=
  (fullGridCappedCollarCoefficient_pos n).trans_le (fullGridCapped_le_monotoneSchurCapped n)

theorem monotoneSchurCappedCoefficient_le_tailMass (n : ℕ) :
    monotoneSchurCappedCoefficient n ≤ collarTailMass :=
  Finset.sup'_le _ _ (fun k _ => rawSchurCappedCoefficient_le_tailMass k)

theorem rawSchurCappedCoefficient_source_energy {n : ℕ} (f : LogarithmicGridSource n) :
    ENNReal.ofReal (rawSchurCappedCoefficient n * autocorr f.1 0) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  unfold rawSchurCappedCoefficient
  split_ifs with hn
  · exact PhysicalCollarPartition.schurCappedOptimalCoefficient_source_energy hn f
  · exact PhysicalCollarPartition.optimalCoefficient_source_energy f

/-- Every finite-envelope member is evaluated against the same literal grid source. -/
theorem monotoneSchurCappedCoefficient_source_energy {n : ℕ} (f : LogarithmicGridSource n) :
    ENNReal.ofReal (monotoneSchurCappedCoefficient n * autocorr f.1 0) ≤
      ∫⁻ x in Ioi 0, continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (n + 1)) ⟨0, by simp⟩
    rawSchurCappedCoefficient
  have hkn : k ≤ n := by have h := Finset.mem_range.mp hk; omega
  have hb := (rawSchurCappedCoefficient_source_energy (f.restrict hkn)).trans
    (lintegral_mono_set (show Ioo 0 (logarithmicCollarEndpoint k) ⊆ Ioi 0 from fun _ hx => hx.1))
  change ENNReal.ofReal (rawSchurCappedCoefficient k * autocorr f.1 0) ≤ _ at hb
  simpa only [monotoneSchurCappedCoefficient, he, LogarithmicGridSource.restrict] using hb

theorem monotoneSchurCappedCoefficient_le_normalized_energy (n : ℕ)
    (f : SmoothLogarithmicGridSource n) :
    monotoneSchurCappedCoefficient n ≤ biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 := by
  have hb := monotoneSchurCappedCoefficient_source_energy f.1
  have hi := integrableOn_biScaleLevyIntegrand f.2.1 f.1.1.hasCompactSupport
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun x => (autocorr f.1.1 0 - autocorr f.1.1 x) * archLevySinhWeight x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (autocorr_sub_nonneg f.1.1.hasCompactSupport f.1.1.continuous x)
      (archLevySinhWeight_pos hx).le
  have he : ENNReal.ofReal (biScaleLevyEnergy f.1.1) =
      ∫⁻ x in Ioi 0, continuousArchIncrementDensity (compactAutocorrKernel f.1.1) x :=
    ofReal_integral_eq_lintegral_ofReal hi hn
  rw [← he] at hb
  exact (le_div_iff₀ f.2.2).2 ((ENNReal.ofReal_le_ofReal_iff
    (biScaleLevyEnergy_nonneg f.1.1.hasCompactSupport f.1.1.continuous)).1 hb)

theorem monotoneSchurCappedCoefficient_bddAbove : BddAbove (Set.range monotoneSchurCappedCoefficient) :=
  ⟨collarTailMass, by rintro c ⟨n, rfl⟩; exact monotoneSchurCappedCoefficient_le_tailMass n⟩

def limitingSchurCappedCoefficient : ℝ := ⨆ n, monotoneSchurCappedCoefficient n

theorem limitingSchurCappedCoefficient_bounds :
    limitingProductCoupledCoefficient ≤ limitingSchurCappedCoefficient ∧
      limitingSchurCappedCoefficient ≤ collarTailMass := by
  constructor
  · rw [← iSup_fullGridCappedCollarCoefficient_eq]
    apply ciSup_le
    intro n
    exact (fullGridCapped_le_monotoneSchurCapped n).trans
      (le_ciSup monotoneSchurCappedCoefficient_bddAbove n)
  · exact ciSup_le monotoneSchurCappedCoefficient_le_tailMass

theorem monotoneSchurCappedCoefficient_tendsto :
    Filter.Tendsto monotoneSchurCappedCoefficient Filter.atTop (nhds limitingSchurCappedCoefficient) :=
  tendsto_atTop_ciSup monotoneSchurCappedCoefficient_monotone monotoneSchurCappedCoefficient_bddAbove

/-- Actual-source capstone: all earlier bounds survive Schur refinement, which is
positive, monotone in the grid cutoff, and bounded independently of that cutoff. -/
theorem schur_capped_actual_source_certificate (n : ℕ) (f : SmoothLogarithmicGridSource n) :
    fullGridCappedCollarCoefficient n ≤ monotoneSchurCappedCoefficient n ∧
      monotoneSchurCappedCoefficient n ≤ biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 ∧
      0 < monotoneSchurCappedCoefficient n ∧ monotoneSchurCappedCoefficient n ≤ collarTailMass :=
  ⟨fullGridCapped_le_monotoneSchurCapped n, monotoneSchurCappedCoefficient_le_normalized_energy n f,
    monotoneSchurCappedCoefficient_pos n, monotoneSchurCappedCoefficient_le_tailMass n⟩

end
end GaloisForLFunctions.BiScaleUncertainty
