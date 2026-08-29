import GaloisForLFunctions.HTGeometry.LatticeZeroCounting
import GaloisForLFunctions.HTGeometry.LogPolyNegligible
import GaloisForLFunctions.HTGeometry.LogMaxSublinear
import GaloisForLFunctions.HTGeometry.BorelGoodRadii
import GaloisForLFunctions.HTGeometry.PosLogRpowAverage
import GaloisForLFunctions.HTGeometry.DriftPeriodicRamification

/-!
# Linear growth of the characteristic of a drifting function

A function whose characteristic grows at least linearly, up to a logarithmic correction, tends to
infinity and dominates every logarithm.  For a function satisfying `W(z+T) = W(z)+C` with `C ≠ 0`,
the difference `W(z) − (C/T)z − W(0)` vanishes at every lattice point `nT`, so the lattice counting
bound applies and gives exactly such a linear lower bound unless that difference vanishes
identically, i.e. unless `W` is affine.

* `tendsto_of_linear_lower_bound` — the two growth statements from a linear lower bound;
* `drift_characteristic_growth` — the growth statements for a non-affine drifting function.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real Set Filter ValueDistribution MeromorphicOn Function
open scoped Topology
open GaloisForLFunctions.Nevanlinna

/-- The logarithm of `1 + r` is sublinear. -/
theorem tendsto_log_one_add_div_atTop :
    Tendsto (fun r : ℝ => Real.log (1 + r) / r) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_log_add_div_atTop
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    refine div_le_div_of_nonneg_right ?_ (by linarith)
    · exact Real.log_le_log (by linarith) (by linarith)

/-- **A linear lower bound forces both Nevanlinna growth conditions.** -/
theorem tendsto_of_linear_lower_bound {T : ℝ → ℝ} {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hT1 : ∀ r, 1 ≤ T r)
    (hlow : ∀ r : ℝ, 1 ≤ r → c * r - B * Real.log (1 + r) - B ≤ T r) :
    Tendsto T atTop atTop ∧ Tendsto (fun r => Real.log r / T r) atTop (𝓝 0) := by
  have hquot : Tendsto (fun r : ℝ => (B * Real.log (1 + r) + B) / r) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => B * (Real.log (1 + r) / r)) atTop (𝓝 0) := by
      have := tendsto_log_one_add_div_atTop.const_mul B
      rwa [mul_zero] at this
    have h2 : Tendsto (fun r : ℝ => B / r) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop tendsto_id B
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    field_simp
  have hhalf : ∀ᶠ r : ℝ in atTop, c * r / 2 ≤ T r := by
    have hlt : ∀ᶠ r : ℝ in atTop, (B * Real.log (1 + r) + B) / r < c / 2 := by
      have := hquot.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < c / 2))
      exact this
    filter_upwards [hlt, eventually_ge_atTop (1 : ℝ)] with r hr hr1
    have hrpos : (0 : ℝ) < r := by linarith
    rw [div_lt_iff₀ hrpos] at hr
    have := hlow r hr1
    linarith
  have hlin : Tendsto (fun r : ℝ => c * r / 2) atTop atTop := by
    have : Tendsto (fun r : ℝ => (c / 2) * r) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by linarith) tendsto_id
    refine this.congr ?_
    intro r
    ring
  refine ⟨tendsto_atTop_mono' atTop hhalf hlin, ?_⟩
  refine squeeze_zero' ?_ ?_ (?_ : Tendsto (fun r : ℝ => (2 / c) * (Real.log r / r)) atTop (𝓝 0))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact div_nonneg (Real.log_nonneg hr) (by linarith [hT1 r])
  · filter_upwards [hhalf, eventually_ge_atTop (1 : ℝ)] with r hr hr1
    have hrpos : (0 : ℝ) < r := by linarith
    have hpos : (0 : ℝ) < c * r / 2 := by positivity
    have hTpos : (0 : ℝ) < T r := by linarith [hT1 r]
    have hlogr : (0 : ℝ) ≤ Real.log r := Real.log_nonneg hr1
    have hstep : Real.log r / T r ≤ Real.log r / (c * r / 2) :=
      div_le_div_of_nonneg_left hlogr hpos hr
    calc Real.log r / T r ≤ Real.log r / (c * r / 2) := hstep
      _ = (2 / c) * (Real.log r / r) := by field_simp
  · have := tendsto_log_div_atTop.const_mul (2 / c)
    rwa [mul_zero] at this

/-- **The characteristic of a non-affine drifting function grows linearly.**  The difference
`W(z) − (C/T)z − W(0)` vanishes at every lattice point `nT`; unless it vanishes identically the
lattice counting bound gives a linear lower bound for its characteristic, and subtracting the affine
part costs only a logarithm. -/
theorem drift_characteristic_growth {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    {T C : ℂ} (hT : T ≠ 0)
    (hdrift : ∀ z, W (z + T) = W z + C)
    (hgo : ∀ z, meromorphicOrderAt (fun w => W w + (-(C / T) * w - W 0)) z ≠ ⊤) :
    Tendsto (charMajorant W) atTop atTop ∧
      Tendsto (fun r => Real.log r / charMajorant W r) atTop (𝓝 0) := by
  have hTpos : (0 : ℝ) < ‖T‖ := norm_pos_iff.mpr hT
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set k : ℂ := C / T with hk
  set aff : ℂ → ℂ := fun w => -k * w - W 0 with haff
  set g : ℂ → ℂ := fun w => W w + aff w with hg
  have hWan : AnalyticOnNhd ℂ W Set.univ := hW.differentiableOn.analyticOnNhd isOpen_univ
  have haffan : AnalyticOnNhd ℂ aff Set.univ := by
    intro z _
    exact ((analyticAt_const).mul (analyticAt_id)).sub analyticAt_const
  have hgan : AnalyticOnNhd ℂ g Set.univ := fun z hz => (hWan z hz).add (haffan z hz)
  -- the lattice zeros
  have hzeros : ∀ n : ℤ, g ((n : ℂ) * T) = 0 := by
    intro n
    have hd := drift_zsmul (W := W) (T := T) (C := C) hdrift 0 n
    have hpt : (0 : ℂ) + n • T = (n : ℂ) * T := by
      simp [zsmul_eq_mul]
    rw [hpt] at hd
    have hval : W ((n : ℂ) * T) = W 0 + (n : ℂ) * C := by
      rw [hd]
      simp [zsmul_eq_mul]
    simp only [hg, haff, hk]
    rw [hval]
    field_simp
    ring
  obtain ⟨K, hK⟩ := exists_characteristic_ge_of_lattice_zeros hgan hgo hT hzeros
  -- the affine part is logarithmically small
  set A : ℝ := Real.log (1 + ‖k‖ + ‖W 0‖) with hA
  have haffbound : ∀ r : ℝ, 1 ≤ r →
      ValueDistribution.characteristic aff ⊤ r ≤ A + Real.log (1 + r) := by
    intro r hr
    have hsphere : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, ‖aff z‖ ≤ ‖k‖ * r + ‖W 0‖ := by
      intro z hz
      have hznorm : ‖z‖ = r := by
        have := mem_sphere_zero_iff_norm.mp hz
        rw [this, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r)]
      calc ‖aff z‖ = ‖-k * z - W 0‖ := rfl
        _ ≤ ‖-k * z‖ + ‖W 0‖ := norm_sub_le _ _
        _ = ‖k‖ * r + ‖W 0‖ := by rw [norm_mul, norm_neg, hznorm]
    have h1 := characteristic_top_le_posLog_of_bound haffan hsphere
    have h2 : Real.posLog (‖k‖ * r + ‖W 0‖) ≤ Real.log (1 + (‖k‖ * r + ‖W 0‖)) :=
      posLog_le_log_one_add (by positivity)
    have h3 : Real.log (1 + (‖k‖ * r + ‖W 0‖)) ≤ A + Real.log (1 + r) := by
      rw [hA, ← Real.log_mul (by positivity) (by linarith)]
      refine Real.log_le_log (by positivity) ?_
      nlinarith [norm_nonneg k, norm_nonneg (W 0), hr]
    linarith
  -- assemble the lower bound for the characteristic of `W`
  set B : ℝ := max (2 * Real.log 2 + K + Real.log 2 + A) 1 with hB
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  have hBge : 2 * Real.log 2 + K + Real.log 2 + A ≤ B := le_max_left _ _
  have hlow : ∀ r : ℝ, 1 ≤ r →
      (Real.log 2 / ‖T‖) * r - B * Real.log (1 + r) - B ≤ charMajorant W r := by
    intro r hr
    have hsub := characteristic_add_le hWan haffan r
    have hgle : ValueDistribution.characteristic g ⊤ r
        ≤ ValueDistribution.characteristic W ⊤ r
          + ValueDistribution.characteristic aff ⊤ r + Real.log 2 := hsub
    have hlow0 := hK r hr
    have haff0 := haffbound r hr
    have hmaj := characteristic_le_charMajorant (f := W) hr
    have hlogr : (0 : ℝ) ≤ Real.log (1 + r) := Real.log_nonneg (by linarith)
    have hkey : Real.log 2 * (r / ‖T‖ - 2) - K
        ≤ ValueDistribution.characteristic W ⊤ r + (A + Real.log (1 + r)) + Real.log 2 := by
      linarith
    have hexp : Real.log 2 * (r / ‖T‖ - 2) = (Real.log 2 / ‖T‖) * r - 2 * Real.log 2 := by
      field_simp
    rw [hexp] at hkey
    nlinarith [hlogr, hB1, hBge, hmaj]
  exact tendsto_of_linear_lower_bound (by positivity) (by linarith) (one_le_charMajorant W) hlow

end GaloisForLFunctions.HTGeometry
