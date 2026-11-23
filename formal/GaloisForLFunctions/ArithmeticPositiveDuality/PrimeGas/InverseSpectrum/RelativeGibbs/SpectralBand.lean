import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.Telescope
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.OccupationGaps

/-! # Relative measurements on the interlacing intervals

The product topology controls every continuous increasing response of the
occupation levels. A summable majorant comes from the two extreme spectra.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- A detector with a continuous strictly increasing response over the occupied energy weights. -/
structure SpectralResponse where
  value : ℝ → ℝ
  cont : ContinuousOn value (Icc 0 1)
  inc : StrictMonoOn value (Icc 0 1)

theorem occupation_in_unit (n : ℕ) : occupationWeight n ∈ Icc (0:ℝ) 1 :=
  ⟨(occupationWeight_pos n).le,(occupationWeight_antitone (Nat.zero_le n)).trans_eq occupationWeight_zero⟩

/-- All spectra compatible with finite-rank interlacing. -/
abbrev SpectralBand (r : ℕ) := (n : ℕ) → Icc (occupationWeight (n+r)) (occupationWeight n)

def hotEdge (r : ℕ) : SpectralBand r := fun n =>
  ⟨occupationWeight n,occupationWeight_antitone (Nat.le_add_right n r),le_rfl⟩

def coldEdge (r : ℕ) : SpectralBand r := fun n =>
  ⟨occupationWeight (n+r),le_rfl,occupationWeight_antitone (Nat.le_add_right n r)⟩

theorem band_in_unit {r : ℕ} (b : SpectralBand r) (n : ℕ) : (b n).val ∈ Icc (0:ℝ) 1 :=
  ⟨(occupationWeight_pos _).le.trans (b n).property.1,(b n).property.2.trans (occupation_in_unit n).2⟩

def relativeHead (f : SpectralResponse) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, (f.value (occupationWeight j)-f.value 0)

def spectralDrop (f : SpectralResponse) {r : ℕ} (b : SpectralBand r) (n : ℕ) : ℝ :=
  f.value (occupationWeight n)-f.value (b n).val

def relativeReading (f : SpectralResponse) {r : ℕ} (b : SpectralBand r) : ℝ :=
  ∑' n, spectralDrop f b n

theorem drop_nonneg (f : SpectralResponse) {r : ℕ} (b : SpectralBand r) (n : ℕ) :
    0 ≤ spectralDrop f b n :=
  sub_nonneg.mpr (f.inc.monotoneOn (band_in_unit b n) (occupation_in_unit n) (b n).property.2)

theorem drop_le_edge (f : SpectralResponse) {r : ℕ} (b : SpectralBand r) (n : ℕ) :
    spectralDrop f b n ≤ spectralDrop f (coldEdge r) n :=
  sub_le_sub_left (f.inc.monotoneOn (occupation_in_unit (n+r)) (band_in_unit b n) (b n).property.1) _

/-- The bound is the centered finite prefix even for divergent absolute response sums. -/
theorem hasSum_edge_drop (f : SpectralResponse) (r : ℕ) :
    HasSum (spectralDrop f (coldEdge r)) (relativeHead f r) := by
  let a (n : ℕ) := f.value (occupationWeight n)-f.value 0
  have ha : Antitone a := fun i j h => sub_le_sub_right
    (f.inc.monotoneOn (occupation_in_unit j) (occupation_in_unit i) (occupationWeight_antitone h)) _
  have h0 : Tendsto (fun n => f.value (occupationWeight n)) atTop (𝓝 (f.value 0)) :=
    (f.cont 0 (show (0:ℝ) ∈ Icc 0 1 from ⟨le_rfl,zero_le_one⟩)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨occupationWeight_tendsto,Eventually.of_forall occupation_in_unit⟩)
  have hz : Tendsto a atTop (𝓝 0) := by simpa only [sub_self] using h0.sub (tendsto_const_nhds (x := f.value 0))
  apply (hasSum_shift_drop ha hz r).congr_fun
  intro n
  change f.value (occupationWeight n)-f.value (occupationWeight (n+r)) =
    (f.value (occupationWeight n)-f.value 0)-(f.value (occupationWeight (n+r))-f.value 0)
  abel

theorem summable_spectralDrop (f : SpectralResponse) {r : ℕ} (b : SpectralBand r) :
    Summable (spectralDrop f b) :=
  .of_nonneg_of_le (drop_nonneg f b) (drop_le_edge f b) (hasSum_edge_drop f r).summable

/-- Relative readings are continuous even when neither absolute trace converges. -/
theorem continuous_relativeReading (f : SpectralResponse) (r : ℕ) :
    Continuous (fun b : SpectralBand r => relativeReading f b) := by
  refine continuous_tsum (u := spectralDrop f (coldEdge r)) ?_ (hasSum_edge_drop f r).summable ?_
  · intro n
    change Continuous (fun b : SpectralBand r => f.value (occupationWeight n)-f.value (b n).val)
    apply continuous_const.sub
    exact f.cont.comp_continuous (continuous_subtype_val.comp (continuous_apply n)) (fun b => band_in_unit b n)
  · intro n b
    rw [Real.norm_of_nonneg (drop_nonneg f b n)]
    exact drop_le_edge f b n

#print axioms hasSum_edge_drop
#print axioms summable_spectralDrop
#print axioms continuous_relativeReading

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
