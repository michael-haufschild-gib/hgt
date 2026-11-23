import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.GibbsRange

/-! # Total error between two interlacing occupation spectra

A monotone response bounds every coordinate discrepancy by its drop
between the two interlacing edges. This also controls all tail sums.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- Regard a spectrum with at most r omissions in a wider interlacing band. -/
def widenSpectrum {q r : ℕ} (h : q ≤ r) (b : SpectralBand q) : SpectralBand r := fun n =>
  ⟨(b n).val,(occupationWeight_antitone (Nat.add_le_add_left h n)).trans (b n).property.1,(b n).property.2⟩

def levelError (f : SpectralResponse) {r q : ℕ} (b : SpectralBand r) (c : SpectralBand q) (n : ℕ) : ℝ :=
  |f.value (b n).val - f.value (c n).val|

def detectorTail (f : SpectralResponse) {r q : ℕ} (b : SpectralBand r) (c : SpectralBand q) (N : ℕ) : ℝ :=
  ∑' k, levelError f b c (k+N)

/-- Total absolute error in the measured levels, including when each absolute measurement sum diverges. -/
def detectorError (f : SpectralResponse) {r q : ℕ} (b : SpectralBand r) (c : SpectralBand q) : ℝ :=
  detectorTail f b c 0

theorem levelError_le_edge (f : SpectralResponse) {r : ℕ} (b c : SpectralBand r) (n : ℕ) :
    levelError f b c n ≤ spectralDrop f (coldEdge r) n := by
  have h₁ := drop_nonneg f b n
  have h₂ := drop_nonneg f c n
  have h₃ := drop_le_edge f b n
  have h₄ := drop_le_edge f c n
  have he : levelError f b c n = |spectralDrop f c n - spectralDrop f b n| := by
    unfold levelError spectralDrop
    congr 1
    abel
  rw [he,abs_le]
  exact ⟨by linarith only [h₂,h₃],by linarith only [h₁,h₄]⟩

theorem summable_levelError (f : SpectralResponse) {r : ℕ} (b c : SpectralBand r) :
    Summable (levelError f b c) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (levelError_le_edge f b c) (hasSum_edge_drop f r).summable

private theorem continuous_levelValue (f : SpectralResponse) (r n : ℕ) :
    Continuous (fun b : SpectralBand r => f.value (b n).val) :=
  f.cont.comp_continuous (continuous_subtype_val.comp (continuous_apply n)) (fun b => band_in_unit b n)

theorem continuous_detectorTail (f : SpectralResponse) (r N : ℕ) :
    Continuous (fun p : SpectralBand r × SpectralBand r => detectorTail f p.1 p.2 N) := by
  apply continuous_tsum (u := fun k => spectralDrop f (coldEdge r) (k+N))
  · intro k
    have h := continuous_levelValue f r (k+N)
    exact ((h.comp continuous_fst).sub (h.comp continuous_snd)).abs
  · exact (summable_nat_add_iff N).mpr (hasSum_edge_drop f r).summable
  · intro k p
    rw [Real.norm_of_nonneg (show 0 ≤ levelError f p.1 p.2 (k+N) from abs_nonneg _)]
    exact levelError_le_edge f p.1 p.2 _

theorem continuous_detectorError (f : SpectralResponse) (r : ℕ) :
    Continuous (fun p : SpectralBand r × SpectralBand r => detectorError f p.1 p.2) :=
  continuous_detectorTail f r 0

theorem detectorError_self (f : SpectralResponse) {r : ℕ} (b : SpectralBand r) : detectorError f b b = 0 := by
  simp [detectorError,detectorTail,levelError]

theorem detectorError_eq_prefix_add_tail (f : SpectralResponse) {r : ℕ} (b c : SpectralBand r) (N : ℕ) :
    detectorError f b c = (∑ n ∈ Finset.range N, levelError f b c n) + detectorTail f b c N :=
  ((summable_levelError f b c).sum_add_tsum_nat_add N).symm

#print axioms summable_levelError
#print axioms continuous_detectorError
#print axioms detectorError_eq_prefix_add_tail

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
