import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Exterior
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Eigenvector

/-! # A continuous physical section of every finite spectral projection -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

private theorem prefixWave_ne {m : ℕ} (b : PrefixData m) : prefixWave b ≠ 0 :=
  norm_ne_zero_iff.mp ((prefixWave_norm b).trans_ne one_ne_zero)

private theorem prescribed_dimension {m : ℕ} (b : PrefixData m) : MissingDimension (omitLine (prefixWave b)) 1 :=
  (missingDimension_one_iff _).mpr ⟨_,prefixWave_ne b,rfl⟩

private theorem prescribed_conserves {m : ℕ} (b : PrefixData m) : Conserving (projected (omitLine (prefixWave b))) :=
  ((nonzero_line_conserves_iff _).mpr (prefixWave_exterior b)).2

/-- The complete conserving spectrum produced by the continuously prescribed missing wave. -/
def prescribedSpectrum {m : ℕ} (b : PrefixData m) : SpectralBand 1 :=
  physicalSpectrum (omitLine (prefixWave b)) (prescribed_dimension b) (prescribed_conserves b)

theorem prescribedSpectrum_physical {m : ℕ} (b : PrefixData m) : prescribedSpectrum b ∈ physicalSpectra 1 :=
  ⟨_,prescribed_dimension b,prescribed_conserves b,rfl⟩

theorem prescribedSpectrum_continuous (m : ℕ) : Continuous (prescribedSpectrum (m := m)) := by
  apply continuous_pi
  intro k
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro b
  have ht := (continuousAt_omitted_root (prefixWave_ne b)).comp (prefixWave_continuous m).continuousAt
  exact (_root_.RHTower.approxNumber_lipschitz k).continuous.continuousAt.comp (ht.pow 2)

/-- Every closed finite prescription is realized at its exact ordered indices, including coincident endpoints. -/
theorem prescribedSpectrum_prefix {m : ℕ} (b : PrefixData m) (j : Fin m) : (prescribedSpectrum b j.val).val = (b j).val := by
  obtain ⟨c,hstrict,ht⟩ := strict_prefix_limit b
  have he (n : ℕ) : (prescribedSpectrum (c n) j.val).val = (c n j).val := by
    obtain ⟨y,hy,hE⟩ := mixed_gap_eigenvector (hstrict n) j
    exact line_gap_index (prefixWave (c n)) (fun _ => rfl) (hstrict n j) hy hE
  have hleft := ((continuous_subtype_val.comp ((continuous_apply j.val).comp (prescribedSpectrum_continuous m))).tendsto b).comp ht
  have hright := ((continuous_subtype_val.comp (continuous_apply j)).tendsto b).comp ht
  exact tendsto_nhds_unique (hleft.congr (fun n => he n)) hright

/-- A continuous right inverse of the finite-prefix reading, taking values among actual conserving rank-one spectra. -/
theorem physical_prefix_section (m : ℕ) :
    ∃ s : C(PrefixData m, SpectralBand 1), ∀ b, s b ∈ physicalSpectra 1 ∧ ∀ j : Fin m, (s b j.val).val = (b j).val :=
  ⟨⟨prescribedSpectrum,prescribedSpectrum_continuous m⟩,fun b => ⟨prescribedSpectrum_physical b,prescribedSpectrum_prefix b⟩⟩

#print axioms prescribedSpectrum_continuous
#print axioms prescribedSpectrum_prefix
#print axioms physical_prefix_section

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
