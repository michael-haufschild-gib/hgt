import GaloisForLFunctions.ArithmeticCouplingTheory.TheCompleteFormOnTheCoherentSector

/-!
# Nonpositive packets are nearly dilation-invariant

The complete Weil energy of strictly separated atoms keeps a fixed fraction `(1 − c)/4` of the pole
defect (RAPT `eventually_completeWeilEnergy_ge_primeDefect`). In packet coordinates the pole defect
is the dilation jump energy (`jumpEnergy_eq_poleDefect`), whose kernel is the pole line `F ≡ const`
(RAPT `poleDefect_eq_zero_iff_horizonPoleVector`). Hence (`eventually_jumpEnergy_le_of_nonpos`):

  for each ratio `0 < c < 1` there is `K` such that eventually every packet `F` with nonpositive
  complete energy has `J_N(F) ≤ K Σ_{n ≤ N} F(n)²/n`.

So in the strictly separated regime every nonpositive direction lies, uniformly in `N`, within a
bounded Dirichlet distance of the joint kernel of the prime dilations: the coherent receiving modes
and the pole. This is the localization half of the coherent-sector question below touching.
-/

open Finset Filter Topology
open scoped RealInnerProductSpace
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SpacingScaleHarmonicAnalysis

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- The pole defect reads only the horizon `[1, N]`. -/
theorem poleDefect_congr {N : ℕ} {x y : ℕ → ℝ} (h : ∀ n ∈ Icc 1 N, x n = y n) :
    poleDefect N x = poleDefect N y := by
  unfold poleDefect
  refine sum_congr rfl fun m hm => sum_congr rfl fun t ht => ?_
  have hm' := mem_Icc.mp hm
  have ht' := mem_Icc.mp ht
  have hmt : m * t ∈ Icc 1 N := mem_Icc.mpr ⟨Nat.mul_pos hm'.1 ht'.1, by
    rw [mul_comm]; exact (Nat.le_div_iff_mul_le hm'.1).mp ht'.2⟩
  rw [h _ hmt, h _ hm]

/-- **Nonpositive packets are nearly dilation-invariant.** For strictly separated atoms
(`0 < c < 1`), eventually every packet with nonpositive complete energy has jump energy at most a
fixed multiple of its mass. -/
theorem eventually_jumpEnergy_le_of_nonpos {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ K : ℝ, ∀ᶠ N : ℕ in atTop, ∀ F : ℕ → ℝ,
      completeWeilEnergy φ c N (horizonProfileVector (atomAmplitude F) N) ≤ 0 →
        jumpEnergy N F ≤ K * ∑ n ∈ Icc 1 N, F n ^ 2 / n := by
  obtain ⟨a, ha⟩ := eventually_completeWeilEnergy_ge_primeDefect hφ hsupp hM hc0 hc1
  have hpos : 0 < (1 - c) / 4 := by linarith
  refine ⟨-a / ((1 - c) / 4), ?_⟩
  filter_upwards [ha] with N hN F hE
  set x := horizonProfileVector (atomAmplitude F) N
  have hext : ∀ n ∈ Icc 1 N, primeHorizonExtension x n = atomAmplitude F n := fun n hn => by
    simp [primeHorizonExtension, hn, x, horizonProfileVector]
  have hnorm : ‖x‖ ^ 2 = ∑ n ∈ Icc 1 N, F n ^ 2 / n := by
    rw [horizonProfileVector_norm_sq]
    exact sum_congr rfl fun n hn => atomAmplitude_sq (mem_Icc.mp hn).1 F
  have h := hN x
  rw [poleDefect_congr hext, ← jumpEnergy_eq_poleDefect, hnorm] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith

end GaloisForLFunctions.ArithmeticCouplingTheory
