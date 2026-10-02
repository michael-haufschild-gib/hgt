import GaloisForLFunctions.RHTower.ZetaChiDualSpatialAmplitude

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower


private theorem sum_int_Ioc_nat_eq {A B : ℕ} (hA : 0 < A) (f : ℝ → ℂ) :
    ∑ z ∈ Finset.Ioc ((A : ℤ) - 1) (B : ℤ), f z = ∑ n ∈ Finset.Icc A B, f n := by
  symm
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    have := Finset.mem_Icc.mp hn
    apply Finset.mem_Ioc.mpr
    constructor <;> omega
  · intro n _ m _ hnm
    omega
  · intro z hz
    have := Finset.mem_Ioc.mp hz
    refine ⟨z.toNat, Finset.mem_Icc.mpr ?_, ?_⟩
    · constructor <;> omega
    · omega
  · intro n _
    simp only [Int.cast_natCast]

/-- Exact Poisson decomposition of the complete literal Gaussian-smoothed
integer block. Half-integer endpoints include every selected natural sample;
the full signed Fourier tail remains in the limit. -/
theorem tendsto_zetaChi_dual_integer_block_poisson
    (s : ℂ) {N : ℝ} (hN : 0 < N) (t : ℝ) {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    Tendsto (fun K : ℕ => zetaChi (s + (t : ℂ) * I) *
      ((∫ x in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2), zetaChiDualSpatialAmplitude s N t x) +
        ∑ n ∈ Finset.range K, (2 : ℂ) *
          ∫ x in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2), zetaChiDualSpatialAmplitude s N t x *
            ((Real.cos (2 * Real.pi * x * ((n : ℝ) + 1)) : ℝ) : ℂ))) atTop
      (𝓝 (∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t)) := by
  have hfloorA : ⌊(A : ℝ) - 1 / 2⌋ = (A : ℤ) - 1 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> push_cast <;> linarith
  have hfloorB : ⌊(B : ℝ) + 1 / 2⌋ = (B : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> push_cast <;> linarith
  have hna : ∀ z : ℤ, (A : ℝ) - 1 / 2 ≠ (z : ℝ) := by
    intro z hz
    have he := congrArg Int.floor hz
    rw [hfloorA, Int.floor_intCast] at he
    rw [← he] at hz
    push_cast at hz
    linarith
  have hnb : ∀ z : ℤ, (B : ℝ) + 1 / 2 ≠ (z : ℝ) := by
    intro z hz
    have he := congrArg Int.floor hz
    rw [hfloorB, Int.floor_intCast] at he
    rw [← he] at hz
    push_cast at hz
    linarith
  have ha : 0 < (A : ℝ) - 1 / 2 := by
    have hAR : (1 : ℝ) ≤ A := by exact_mod_cast (by omega : 1 ≤ A)
    linarith
  have hab : (A : ℝ) - 1 / 2 ≤ (B : ℝ) + 1 / 2 := by
    have hABR : (A : ℝ) ≤ B := by exact_mod_cast hAB
    linarith
  have hp := tendsto_zetaChiDualSpatialAmplitude_cosTransform s hN t ha hab hna hnb
  rw [hfloorA, hfloorB, sum_int_Ioc_nat_eq hA] at hp
  have hc : Tendsto (fun _ : ℕ => ∫ x in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2),
      zetaChiDualSpatialAmplitude s N t x) atTop
      (𝓝 (∫ x in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2), zetaChiDualSpatialAmplitude s N t x)) :=
    tendsto_const_nhds
  have hl := (hc.add hp).const_mul (zetaChi (s + (t : ℂ) * I))
  have hlimit : zetaChi (s + (t : ℂ) * I) *
      ((∫ x in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2), zetaChiDualSpatialAmplitude s N t x) +
        ((∑ n ∈ Finset.Icc A B, zetaChiDualSpatialAmplitude s N t n) -
          ∫ x in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2), zetaChiDualSpatialAmplitude s N t x)) =
      ∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t := by
    rw [show (∫ x in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2), zetaChiDualSpatialAmplitude s N t x) +
        ((∑ n ∈ Finset.Icc A B, zetaChiDualSpatialAmplitude s N t n) -
          ∫ x in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2), zetaChiDualSpatialAmplitude s N t x) =
        ∑ n ∈ Finset.Icc A B, zetaChiDualSpatialAmplitude s N t n by ring]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => zetaChiDualSpatialAmplitude_nat s N t n)
  simpa only [hlimit] using hl

end RHTower
