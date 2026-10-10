import GaloisForLFunctions.RHTower.XiCosineShiftAlmostEveryHeight
import GaloisForLFunctions.RHTower.ZetaZeroDensityInghamHuxley

/-!
# Power-saving sparsity of the defect heights of `cos(hD)Ξ`

For `0 < h ≤ ½` a non-real zero `z` of `A_h(z) = (Ξ(z + ih) + Ξ(z − ih))/2` sits within horizontal
distance `½` of the ordinate of a zero `ρ` of `ξ` with `Re ρ > ½ + h`
(`exists_zetaZero_of_cosineShift_nonreal`). The Ingham–Huxley estimate counts these zeros
(`exists_zeroHeightBox_ncard_le_ingham_huxley`). So for every `ε ∈ (0, 1]`, the heights
`x ∈ [T + ½, 2T − ½]` at which some `A_{h'}`, `h' ≥ h`, has a non-real zero with real part `x`
have measure

  `≤ D (1 + log T)^B T^{(A(½ + h) + ε)(½ − h)}`,

with the Ingham–Huxley exponent `A`
(`exists_volume_cosineShift_nonrealHeight_le_inghamHuxley`). Since `A(½ + h) ≤ 12/5` and
`A(½ + h) = 3/(3/2 − h)` near the line, the exponent is `1 − 4h/3 + O(h²) + ε/2 < 1` for small
`ε`. Defect heights are therefore power-sparse for every `h > 0`. For `h ≥ 1/12` the exponent is
below `1 − h` (`A ≤ 12/5`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

/-- A non-real zero of `cos(hD)Ξ` gives a divisor copy `q` of `ξ` with `Re q > ½ + h` and ordinate
within `½` of `Re z`. -/
theorem exists_xiZeroCopy_of_cosineShift_nonreal {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : z.im ≠ 0)
    (h0 : (XiC (z + h * I) + XiC (z - h * I)) / 2 = 0) :
    ∃ q : XiZeroCopy, 1 / 2 + h < (q.1 : ℂ).re ∧ |(q.1 : ℂ).im - z.re| < 1 / 2 := by
  obtain ⟨ρ, hζ, hlo, hρ1, hclose⟩ := exists_zetaZero_of_cosineShift_nonreal hh hz h0
  have hρne : ρ ≠ 1 := by intro h1; rw [h1] at hρ1; simp at hρ1
  have hxi : xi ρ = 0 := (xi_eq_zero_iff (by linarith) hρne).mpr hζ
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  exact ⟨q, by rw [hq]; exact hlo, by rw [hq]; exact hclose⟩

/-- **Power-saving defect heights.** For `0 < h ≤ ½` and `0 < ε ≤ 1` there are `D, B, T₀` such that
for `T ≥ T₀` the heights `x ∈ [T + ½, 2T − ½]` at which `cos(h'D)Ξ` has a non-real zero with
real part `x` for some `h' ≥ h` have measure at most `D (1 + log T)^B T^{(A(½ + h) + ε)(½ − h)}`. -/
theorem exists_volume_cosineShift_nonrealHeight_le_inghamHuxley {h ε : ℝ} (hh : 0 < h)
    (hh2 : h ≤ 1 / 2) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      volume {x : ℝ | x ∈ Icc (T + 1 / 2) (2 * T - 1 / 2) ∧
        ∃ h' : ℝ, h ≤ h' ∧ ∃ z : ℂ, z.re = x ∧ z.im ≠ 0 ∧
          (XiC (z + h' * I) + XiC (z - h' * I)) / 2 = 0}
        ≤ ENNReal.ofReal (D * (1 + Real.log T) ^ B *
          T ^ ((inghamHuxleyExponent (1 / 2 + h) + ε) * (1 / 2 - h))) := by
  classical
  obtain ⟨D, hD, B, T₀, hT₀, hbound⟩ :=
    exists_zeroHeightBox_ncard_le_ingham_huxley (σ := 1 / 2 + h) (by linarith) (by linarith) hε hε1
  refine ⟨D, hD, B, T₀, hT₀, fun T hT => ?_⟩
  have hfin := zeroHeightBox_finite (1 / 2 + h) T
  set Z := hfin.toFinset with hZ
  have hsub : {x : ℝ | x ∈ Icc (T + 1 / 2) (2 * T - 1 / 2) ∧
      ∃ h' : ℝ, h ≤ h' ∧ ∃ z : ℂ, z.re = x ∧ z.im ≠ 0 ∧
          (XiC (z + h' * I) + XiC (z - h' * I)) / 2 = 0} ⊆
      ⋃ q ∈ Z, Icc ((q.1 : ℂ).im - 1 / 2) ((q.1 : ℂ).im + 1 / 2) := by
    rintro x ⟨hx, h', hhh', z, hzx, hz, h0⟩
    obtain ⟨q, hqre, hqim⟩ :=
      exists_xiZeroCopy_of_cosineShift_nonreal (lt_of_lt_of_le hh hhh') hz h0
    rw [hzx] at hqim
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hqim
    have hqZ : q ∈ Z := by
      rw [hZ, Set.Finite.mem_toFinset]
      exact ⟨by linarith, by linarith [hx.1], by linarith [hx.2]⟩
    exact mem_iUnion₂.mpr ⟨q, hqZ, by linarith, by linarith⟩
  have hcard : (Z.card : ℝ) = ((zeroHeightBox (1 / 2 + h) T).ncard : ℝ) := by
    rw [hZ, Set.ncard_eq_toFinset_card _ hfin]
  have hexp : (1 - (1 / 2 + h)) = 1 / 2 - h := by ring
  calc volume {x : ℝ | x ∈ Icc (T + 1 / 2) (2 * T - 1 / 2) ∧
        ∃ h' : ℝ, h ≤ h' ∧ ∃ z : ℂ, z.re = x ∧ z.im ≠ 0 ∧
          (XiC (z + h' * I) + XiC (z - h' * I)) / 2 = 0}
      ≤ volume (⋃ q ∈ Z, Icc ((q.1 : ℂ).im - 1 / 2) ((q.1 : ℂ).im + 1 / 2)) := measure_mono hsub
    _ ≤ ∑ q ∈ Z, volume (Icc ((q.1 : ℂ).im - 1 / 2) ((q.1 : ℂ).im + 1 / 2)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ q ∈ Z, ENNReal.ofReal 1 := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Real.volume_Icc]
        congr 1
        ring
    _ = ENNReal.ofReal (Z.card : ℝ) := by
        rw [Finset.sum_const, ENNReal.ofReal_one, nsmul_eq_mul, mul_one, ENNReal.ofReal_natCast]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hcard]
        have := hbound T hT
        rwa [hexp] at this

end RHTower
