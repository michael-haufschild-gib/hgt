import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFrequencyPartition
import GaloisForLFunctions.RHTower.Sieve.LogPolySetScaling

/-!
# Adapted moments for Menon's harmonic frequency partition

The prime-power moment estimate is stated in the reflected Dirichlet frequency.  This module
transports it exactly to Menon's Gallagher frequency, including the factor `(2π)⁻¹`, then sums the
result over the literal some-large block cover.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Lebesgue measure under a reflected positive dilation. -/
theorem volume_real_preimage_neg_mul_left {S : Set ℝ} {c : ℝ} (hc : 0 < c) :
    volume.real ((fun v : ℝ => -c * v) ⁻¹' S) = c⁻¹ * volume.real S := by
  have hcne : -c ≠ 0 := neg_ne_zero.mpr (ne_of_gt hc)
  have h := Real.volume_preimage_mul_left hcne S
  rw [Measure.real, Measure.real, h, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, abs_neg, abs_of_pos hc]

/-- Exact reflected-frequency moment cost of one harmonic geometric prime block. -/
def menonHarmonicBlockMomentCost
    (k N : ℕ) (Q eta W : ℝ) (j : ℕ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    (2 * (((2 * Real.pi * W) + 4 * ((N ^ k : ℕ) : ℝ) *
          (1 + Real.log ((N ^ k : ℕ) : ℝ))) *
      ((k : ℝ) ^ k *
        (((Q * (1 + eta) ^ j * eta + 1) /
          (Q * (1 + eta) ^ j) ^ 2) ^ k))))

/-- One actual harmonic block-large set satisfies the adapted prime moment bound in Gallagher
frequency.  The change of variables is exact and retains the relative-width energy. -/
theorem volume_menonHarmonicBlockLarge_pow_le
    (k N : ℕ) (hk : 1 ≤ k) {P : Finset ℕ} {Q eta V W : ℝ} (j : ℕ)
    (hP : P ⊆ Finset.Icc 1 N) (hPprime : ∀ p ∈ P, p.Prime)
    (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 0 ≤ W) (hV : 0 ≤ V) :
    V ^ (2 * k) * volume.real (menonHarmonicBlockLarge P Q eta (fun _ => V) W j) ≤
      menonHarmonicBlockMomentCost k N Q eta W j := by
  let T : ℝ := 2 * Real.pi * W
  let E : Set ℝ :=
    {x ∈ Set.Icc (-T) T |
      V ≤ ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j)
        (-x / (2 * Real.pi))‖}
  have hpi : 0 < 2 * Real.pi := by positivity
  have hset : menonHarmonicBlockLarge P Q eta (fun _ => V) W j =
      (fun w : ℝ => -(2 * Real.pi) * w) ⁻¹' E := by
    ext w
    simp only [menonHarmonicBlockLarge, Set.mem_setOf_eq, Set.mem_preimage, E, T,
      Set.mem_Icc]
    have harg : -(-(2 * Real.pi) * w) / (2 * Real.pi) = w := by
      field_simp [Real.pi_ne_zero]
    constructor
    · rintro ⟨⟨hw₁, hw₂⟩, hlarge⟩
      refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
      simpa only [harg] using hlarge
    · rintro ⟨⟨hw₁, hw₂⟩, hlarge⟩
      refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
      simpa only [harg] using hlarge
  have hbase := volume_harmonicGeomPrimeBlock_largeValues_pow_le
    k N hk (P := P) (Q := Q) (eta := eta) (T := T) (V := V) j
      hP hPprime hQ heta (by dsimp only [T]; positivity) hV
  dsimp only at hbase
  rw [hset, volume_real_preimage_neg_mul_left hpi]
  calc
    V ^ (2 * k) * ((2 * Real.pi)⁻¹ * volume.real E) =
        (2 * Real.pi)⁻¹ * (V ^ (2 * k) * volume.real E) := by ring
    _ ≤ (2 * Real.pi)⁻¹ *
        (2 * (((2 * Real.pi * W) + 4 * ((N ^ k : ℕ) : ℝ) *
              (1 + Real.log ((N ^ k : ℕ) : ℝ))) *
          ((k : ℝ) ^ k *
            (((Q * (1 + eta) ^ j * eta + 1) /
              (Q * (1 + eta) ^ j) ^ 2) ^ k)))) :=
      mul_le_mul_of_nonneg_left (by simpa only [T, E] using hbase) (by positivity)
    _ = menonHarmonicBlockMomentCost k N Q eta W j := rfl

/-- The literal some-large set has the sum of the adapted moment bounds of its blocks. -/
theorem volume_menonHarmonicSomeBlockLarge_le_moments
    (k N : ℕ) (hk : 1 ≤ k) {P : Finset ℕ} {Q eta W : ℝ} {L : ℕ}
    (hP : P ⊆ Finset.Icc 1 N) (hPprime : ∀ p ∈ P, p.Prime)
    (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 0 ≤ W)
    (V : ℕ → ℝ) (hV : ∀ j ∈ Finset.range L, 0 < V j) :
    volume.real (menonHarmonicSomeBlockLarge P Q eta L V W) ≤
      ∑ j ∈ Finset.range L,
        menonHarmonicBlockMomentCost k N Q eta W j / (V j) ^ (2 * k) := by
  classical
  have hfin : ∀ j ∈ Finset.range L,
      volume (menonHarmonicBlockLarge P Q eta V W j) ≠ ⊤ := by
    intro j _
    refine ne_of_lt (lt_of_le_of_lt
      (measure_mono (fun _ hw => hw.1)) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hmono : volume (menonHarmonicSomeBlockLarge P Q eta L V W) ≤
      ∑ j ∈ Finset.range L, volume (menonHarmonicBlockLarge P Q eta V W j) :=
    volume_menonHarmonicSomeBlockLarge_le P Q eta L V W
  have hsumfin :
      (∑ j ∈ Finset.range L, volume (menonHarmonicBlockLarge P Q eta V W j)) ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun j hj => lt_top_iff_ne_top.2 (hfin j hj)).ne
  have hcast :
      (∑ j ∈ Finset.range L, volume (menonHarmonicBlockLarge P Q eta V W j)).toReal =
        ∑ j ∈ Finset.range L, volume.real (menonHarmonicBlockLarge P Q eta V W j) := by
    rw [ENNReal.toReal_sum hfin]
    rfl
  have hreal : volume.real (menonHarmonicSomeBlockLarge P Q eta L V W) ≤
      ∑ j ∈ Finset.range L, volume.real (menonHarmonicBlockLarge P Q eta V W j) := by
    rw [MeasureTheory.measureReal_def, ← hcast]
    exact ENNReal.toReal_mono hsumfin hmono
  refine hreal.trans (Finset.sum_le_sum fun j hj => ?_)
  have hmoment := volume_menonHarmonicBlockLarge_pow_le
    k N hk (P := P) (Q := Q) (eta := eta) (V := V j) (W := W) j
      hP hPprime hQ heta hW (hV j hj).le
  rw [show menonHarmonicBlockLarge P Q eta (fun _ => V j) W j =
      menonHarmonicBlockLarge P Q eta V W j by rfl] at hmoment
  exact (le_div_iff₀ (pow_pos (hV j hj) (2 * k))).2 (by
    simpa only [mul_comm] using hmoment)

/-- Exact reflected-frequency moment cost with the Dirichlet polynomial truncated at the
literal upper endpoint of the geometric prime block.  This avoids padding every block to the
global endpoint of Menon's final range. -/
def menonHarmonicLocalBlockMomentCost
    (k : ℕ) (Q eta W : ℝ) (j : ℕ) : ℝ :=
  menonHarmonicBlockMomentCost k ⌊Q * (1 + eta) ^ (j + 1)⌋₊ Q eta W j

/-- One actual harmonic block-large set satisfies the adapted prime moment bound with its own
literal upper endpoint as the polynomial length.  The full relative-width saving is retained. -/
theorem volume_menonHarmonicBlockLarge_pow_le_local
    (k : ℕ) (hk : 1 ≤ k) {P : Finset ℕ} {Q eta V W : ℝ} (j : ℕ)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 0 ≤ W) (hV : 0 ≤ V) :
    V ^ (2 * k) * volume.real (menonHarmonicBlockLarge P Q eta (fun _ => V) W j) ≤
      menonHarmonicLocalBlockMomentCost k Q eta W j := by
  let N : ℕ := ⌊Q * (1 + eta) ^ (j + 1)⌋₊
  let B : Finset ℕ := geomBlock P Q (1 + eta) j
  let T : ℝ := 2 * Real.pi * W
  let E : Set ℝ :=
    {x ∈ Set.Icc (-T) T |
      V ≤ ‖harmonicPrimeBlockPoly B (-x / (2 * Real.pi))‖}
  have htop0 : 0 ≤ Q * (1 + eta) ^ (j + 1) := by positivity
  have hB : B ⊆ Finset.Icc 1 N := by
    intro p hp
    have hp' := Finset.mem_filter.1 hp
    refine Finset.mem_Icc.2 ⟨(hPprime p hp'.1).one_le, ?_⟩
    exact (Nat.le_floor_iff htop0).2 hp'.2.2
  have hBprime : ∀ p ∈ B, p.Prime := by
    intro p hp
    exact hPprime p (geomBlock_subset P Q (1 + eta) j hp)
  let Qj : ℝ := Q * (1 + eta) ^ j
  have hQj : 0 < Qj := by
    dsimp only [Qj]
    positivity
  have hlower : ∀ p ∈ B, Qj < (p : ℝ) := by
    intro p hp
    exact (Finset.mem_filter.1 hp).2.1
  have hpi : 0 < 2 * Real.pi := by positivity
  have hset : menonHarmonicBlockLarge P Q eta (fun _ => V) W j =
      (fun w : ℝ => -(2 * Real.pi) * w) ⁻¹' E := by
    ext w
    simp only [menonHarmonicBlockLarge, Set.mem_setOf_eq, Set.mem_preimage, E, T, B,
      Set.mem_Icc]
    have harg : -(-(2 * Real.pi) * w) / (2 * Real.pi) = w := by
      field_simp [Real.pi_ne_zero]
    constructor
    · rintro ⟨⟨hw₁, hw₂⟩, hlarge⟩
      refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
      simpa only [harg] using hlarge
    · rintro ⟨⟨hw₁, hw₂⟩, hlarge⟩
      refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
      simpa only [harg] using hlarge
  have hbase := volume_harmonicPrimeBlock_largeValues_pow_le
    k N hk (B := B) (q := Qj) (T := T) (V := V)
      hB hBprime hQj hlower (by dsimp only [T]; positivity) hV
  have hcard := card_geomBlock_le P hQ heta j
  have hbase' : V ^ (2 * k) * volume.real E ≤
      2 * (((2 * Real.pi * W) + 4 * ((N ^ k : ℕ) : ℝ) *
            (1 + Real.log ((N ^ k : ℕ) : ℝ))) *
        ((k : ℝ) ^ k *
          (((Q * (1 + eta) ^ j * eta + 1) /
            (Q * (1 + eta) ^ j) ^ 2) ^ k))) := by
    refine hbase.trans ?_
    dsimp only [T, Qj, B] at hbase ⊢
    gcongr
  rw [hset, volume_real_preimage_neg_mul_left hpi]
  calc
    V ^ (2 * k) * ((2 * Real.pi)⁻¹ * volume.real E) =
        (2 * Real.pi)⁻¹ * (V ^ (2 * k) * volume.real E) := by ring
    _ ≤ (2 * Real.pi)⁻¹ *
        (2 * (((2 * Real.pi * W) + 4 * ((N ^ k : ℕ) : ℝ) *
              (1 + Real.log ((N ^ k : ℕ) : ℝ))) *
          ((k : ℝ) ^ k *
            (((Q * (1 + eta) ^ j * eta + 1) /
              (Q * (1 + eta) ^ j) ^ 2) ^ k)))) :=
      mul_le_mul_of_nonneg_left hbase' (by positivity)
    _ = menonHarmonicLocalBlockMomentCost k Q eta W j := by
      rfl

/-- The literal some-large set has the sum of the block-local adapted moment bounds. -/
theorem volume_menonHarmonicSomeBlockLarge_le_local_moments
    (k : ℕ) (hk : 1 ≤ k) {P : Finset ℕ} {Q eta W : ℝ} {L : ℕ}
    (hPprime : ∀ p ∈ P, p.Prime)
    (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 0 ≤ W)
    (V : ℕ → ℝ) (hV : ∀ j ∈ Finset.range L, 0 < V j) :
    volume.real (menonHarmonicSomeBlockLarge P Q eta L V W) ≤
      ∑ j ∈ Finset.range L,
        menonHarmonicLocalBlockMomentCost k Q eta W j / (V j) ^ (2 * k) := by
  classical
  have hfin : ∀ j ∈ Finset.range L,
      volume (menonHarmonicBlockLarge P Q eta V W j) ≠ ⊤ := by
    intro j _
    refine ne_of_lt (lt_of_le_of_lt
      (measure_mono (fun _ hw => hw.1)) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hmono : volume (menonHarmonicSomeBlockLarge P Q eta L V W) ≤
      ∑ j ∈ Finset.range L, volume (menonHarmonicBlockLarge P Q eta V W j) :=
    volume_menonHarmonicSomeBlockLarge_le P Q eta L V W
  have hsumfin :
      (∑ j ∈ Finset.range L, volume (menonHarmonicBlockLarge P Q eta V W j)) ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun j hj => lt_top_iff_ne_top.2 (hfin j hj)).ne
  have hcast :
      (∑ j ∈ Finset.range L, volume (menonHarmonicBlockLarge P Q eta V W j)).toReal =
        ∑ j ∈ Finset.range L, volume.real (menonHarmonicBlockLarge P Q eta V W j) := by
    rw [ENNReal.toReal_sum hfin]
    rfl
  have hreal : volume.real (menonHarmonicSomeBlockLarge P Q eta L V W) ≤
      ∑ j ∈ Finset.range L,
        volume.real (menonHarmonicBlockLarge P Q eta V W j) := by
    rw [MeasureTheory.measureReal_def, ← hcast]
    exact ENNReal.toReal_mono hsumfin hmono
  refine hreal.trans (Finset.sum_le_sum fun j hj => ?_)
  have hmoment := volume_menonHarmonicBlockLarge_pow_le_local
    k hk (P := P) (Q := Q) (eta := eta) (V := V j) (W := W) j
      hPprime hQ heta hW (hV j hj).le
  rw [show menonHarmonicBlockLarge P Q eta (fun _ => V j) W j =
      menonHarmonicBlockLarge P Q eta V W j by rfl] at hmoment
  exact (le_div_iff₀ (pow_pos (hV j hj) (2 * k))).2 (by
    simpa only [mul_comm] using hmoment)

end

end RHTower.Sieve
