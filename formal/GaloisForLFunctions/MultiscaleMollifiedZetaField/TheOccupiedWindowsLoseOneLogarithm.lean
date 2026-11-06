import GaloisForLFunctions.RHTower.SelbergNearLineCriticalGateDensity
import GaloisForLFunctions.RHTower.ZetaOffLineWeightedDensity
import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalScale
import GaloisForLFunctions.RHTower.BurnolRectangleResidue

/-!
# The occupied windows lose one logarithm

Let `L = log S`. For all large `S` there are heights `T₁ ≈ 2S/3`, `T₂ ≈ 4S/3` such that for every
`1 ≤ a ≤ L/100`, the heights `τ` whose unit window `[τ, τ+1]` holds a zero of depth at least
`(51/50) a/L` right of the critical line have measure at most

`(L/(2π a)) (T₂ − T₁) A e^{−22a/25} + K L²/(2π a)`

(`exists_volume_occupied_windows_le`).

**Mechanism.** A window is occupied only if `τ ∈ [γ−1, γ]` for a deep zero, so the occupied measure is at
most the number of deep zeros, and Selberg's near-line density at rate `22/25` counts them. Each zero is
charged a full unit window.

**The loss.** The proportion carries the factor `L/a`, one logarithm per unit window, against the
target `ε(a)`. It tends to zero once `(22/25) a ≥ (1+ε) log L`, that is at depth
`≥ (1+ε)(51/50)(25/22) log log V` (`tendsto_occupied_proportion`). So the union bound decides the windows
at depth `≍ log log V` and says nothing at fixed depth.
-/

noncomputable section

open Complex Set MeasureTheory Filter Topology
open RHTower

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The heights whose unit window holds a zero of depth at least `D` right of the line. -/
def occupiedHeights (D T₁ T₂ : ℝ) : Set ℝ :=
  {τ | T₁ ≤ τ ∧ τ + 1 ≤ T₂ ∧ ∃ w : ℂ, riemannZeta w = 0 ∧ 1 / 2 + D ≤ w.re ∧ τ ≤ w.im ∧ w.im ≤ τ + 1}

/-- A zero of `ζ` has positive order. -/
theorem one_le_order_of_zero {w : ℂ} (hw : riemannZeta w = 0) (hw1 : w ≠ 1) :
    1 ≤ ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
  have h := one_le_zeroMult ((zetaResidueUnit_eq_zero_iff hw1).2 hw)
  unfold zeroMult at h
  rwa [analyticOrderAt_zetaResidueUnit_eq_zeta hw1] at h

/-- **The occupied windows.** The measure of the heights whose unit window holds a zero of depth
`≥ (51/50) a/L` is at most the zero count of Selberg's near-line density. -/
theorem exists_volume_occupied_windows_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ S : ℝ in atTop,
      ∃ T₁ ∈ Ioo (2 * S / 3) (2 * S / 3 + 1), ∃ T₂ ∈ Ioo (4 * S / 3 - 1) (4 * S / 3),
        ∀ a : ℝ, 1 ≤ a → a ≤ Real.log S / 100 →
          volume (occupiedHeights (51 / 50 * (a / Real.log S)) T₁ T₂) ≤
            ENNReal.ofReal (Real.log S / (2 * Real.pi * a) *
              ((T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * Real.log S)) := by
  classical
  obtain ⟨A, K, hA, hK, hdens⟩ := exists_selberg_criticalGate_nearLine_zeroDensity
  refine ⟨A, K, hA, hK, ?_⟩
  filter_upwards [hdens, Real.tendsto_log_atTop.eventually_gt_atTop 0] with S hS hL0
  obtain ⟨T₁, hT₁, T₂, hT₂, hcount⟩ := hS
  refine ⟨T₁, hT₁, T₂, hT₂, fun a ha1 haL => ?_⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log S := ⟨_, rfl⟩
  rw [← hL] at hL0 haL hcount ⊢
  have ha0 : 0 < a := by linarith
  have hpi := Real.pi_pos
  -- the zeros of the rectangle
  obtain ⟨Z, hZdef⟩ : ∃ Z : Finset ℂ, Z = zetaZeroFinset
      (((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I) (((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I) := ⟨_, rfl⟩
  have hZmem : ∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0 := by
    intro z
    rw [hZdef, mem_zetaZeroFinset]
    simp [Rectangle]
  have hc := hcount a ha1 haL Z hZmem
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 51 / 50 * (a / L) := ⟨_, rfl⟩
  rw [← hD] at hc ⊢
  obtain ⟨Zd, hZd⟩ : ∃ Zd : Finset ℂ, Zd = Z.filter (fun w => 1 / 2 + D ≤ w.re) := ⟨_, rfl⟩
  rw [← hZd] at hc
  have hsub : occupiedHeights D T₁ T₂ ⊆ ⋃ w ∈ Zd, Icc (w.im - 1) w.im := by
    rintro τ ⟨hτ1, hτ2, w, hw, hwD, hτw, hwτ⟩
    refine mem_iUnion₂.mpr ⟨w, ?_, by linarith, hτw⟩
    rw [hZd, Finset.mem_filter]
    refine ⟨(hZmem w).mpr ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, hw⟩, hwD⟩
    · have hD0 : 0 ≤ D := by
        rw [hD]
        positivity
      have hlt : w.re < 1 := by
        by_contra hge
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hw
      rw [uIcc_of_le (by norm_num)]
      exact ⟨by linarith, by linarith⟩
    · have hT12 : T₁ ≤ T₂ := by linarith
      rw [uIcc_of_le hT12]
      exact ⟨by linarith, by linarith⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hunit : ∀ w ∈ Zd, volume (Icc (w.im - 1) w.im) ≤
      ENNReal.ofReal ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    intro w hw
    rw [Real.volume_Icc]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hZd, Finset.mem_filter] at hw
    have hzero := ((hZmem w).mp hw.1).2
    have hw1 : w ≠ 1 := by
      rintro rfl
      exact riemannZeta_one_ne_zero hzero
    have := one_le_order_of_zero hzero hw1
    linarith
  refine (Finset.sum_le_sum hunit).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun w _ => Nat.cast_nonneg _]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : 0 < 2 * Real.pi * (a / L) := by positivity
  have hdiv : ∑ w ∈ Zd, ((analyticOrderAt riemannZeta w).toNat : ℝ) ≤
      ((T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * L) / (2 * Real.pi * (a / L)) := by
    rw [le_div_iff₀ hpos, mul_comm]
    rw [mul_assoc]
    exact hc
  refine hdiv.trans (le_of_eq ?_)
  field_simp

/-- **The proportion of occupied windows.** Up to the error `C L²`, the occupied heights have
proportion at most `C (L/a) e^{−22a/25}`, one logarithm above the target. -/
theorem exists_volume_occupied_windows_le_proportion :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ S : ℝ in atTop,
      ∃ T₁ ∈ Ioo (2 * S / 3) (2 * S / 3 + 1), ∃ T₂ ∈ Ioo (4 * S / 3 - 1) (4 * S / 3),
        ∀ a : ℝ, 1 ≤ a → a ≤ Real.log S / 100 →
          volume (occupiedHeights (51 / 50 * (a / Real.log S)) T₁ T₂) ≤
            ENNReal.ofReal (C * S * (Real.log S / a * Real.exp (-(22 / 25 * a))) +
              C * Real.log S ^ 2) := by
  obtain ⟨A, K, hA, hK, hocc⟩ := exists_volume_occupied_windows_le
  have hpi := Real.pi_pos
  refine ⟨A + K + 1, by positivity, ?_⟩
  filter_upwards [hocc, eventually_ge_atTop 6, Real.tendsto_log_atTop.eventually_gt_atTop 0]
    with S hS hS6 hL0
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hS
  refine ⟨T₁, hT₁, T₂, hT₂, fun a ha1 haL => (hbound a ha1 haL).trans ?_⟩
  refine ENNReal.ofReal_le_ofReal ?_
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log S := ⟨_, rfl⟩
  rw [← hL] at hL0 ⊢
  have ha0 : 0 < a := by linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (-(22 / 25 * a)) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 < E := hE ▸ Real.exp_pos _
  have hT : T₂ - T₁ ≤ S := by linarith [hT₁.1, hT₂.2]
  have hT0 : 0 ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  have h2pi : 1 ≤ 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hfac : L / (2 * Real.pi * a) ≤ L / a := by
    refine div_le_div_of_nonneg_left hL0.le (by positivity) ?_
    nlinarith
  have hfac2 : L / (2 * Real.pi * a) ≤ L := by
    refine hfac.trans ?_
    exact div_le_self hL0.le ha1
  have hfac0 : 0 ≤ L / (2 * Real.pi * a) := by positivity
  have h1 : L / (2 * Real.pi * a) * ((T₂ - T₁) * (A * E)) ≤ L / a * (S * (A * E)) :=
    mul_le_mul hfac (mul_le_mul_of_nonneg_right hT (by positivity)) (by positivity) (by positivity)
  have h2 : L / (2 * Real.pi * a) * (K * L) ≤ L * (K * L) :=
    mul_le_mul_of_nonneg_right hfac2 (by positivity)
  have hS0 : 0 < S := by linarith
  have h3 : A * (S * (L / a * E)) ≤ (A + K + 1) * (S * (L / a * E)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h4 : K * L ^ 2 ≤ (A + K + 1) * L ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  calc L / (2 * Real.pi * a) * ((T₂ - T₁) * (A * E) + K * L)
      = L / (2 * Real.pi * a) * ((T₂ - T₁) * (A * E)) + L / (2 * Real.pi * a) * (K * L) := by ring
    _ ≤ L / a * (S * (A * E)) + L * (K * L) := add_le_add h1 h2
    _ = A * (S * (L / a * E)) + K * L ^ 2 := by ring
    _ ≤ (A + K + 1) * (S * (L / a * E)) + (A + K + 1) * L ^ 2 := add_le_add h3 h4
    _ = _ := by ring

/-- **The threshold of the union bound.** At depth parameter `a = (25/22)(1+ε) log L` the proportion
of occupied windows is at most `C L^{−ε}`: the windows are decided at `≍ log log S`, not at fixed depth. -/
theorem exists_volume_occupied_windows_le_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ S : ℝ in atTop,
      ∃ T₁ ∈ Ioo (2 * S / 3) (2 * S / 3 + 1), ∃ T₂ ∈ Ioo (4 * S / 3 - 1) (4 * S / 3),
        volume (occupiedHeights
          (51 / 50 * (25 / 22 * (1 + ε) * Real.log (Real.log S) / Real.log S)) T₁ T₂) ≤
          ENNReal.ofReal (C * S * Real.exp (-(ε * Real.log (Real.log S))) +
            C * Real.log S ^ 2) := by
  obtain ⟨C, hC, hocc⟩ := exists_volume_occupied_windows_le_proportion
  refine ⟨C, hC, ?_⟩
  have hlog : Tendsto (fun S : ℝ => Real.log (Real.log S)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 100 * (25 / 22 * (1 + ε)) := ⟨_, rfl⟩
  have hK0 : 0 < K := by
    rw [hK]
    positivity
  have ho := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / K by positivity)
  filter_upwards [hocc, hlog.eventually_ge_atTop 1, eventually_gt_atTop 0,
    Real.tendsto_log_atTop.eventually ho, Real.tendsto_log_atTop.eventually_gt_atTop 0]
    with S hS hu hS0 hsmall hL0
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hS
  refine ⟨T₁, hT₁, T₂, hT₂, ?_⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log S := ⟨_, rfl⟩
  rw [← hL] at hL0 hbound hu hsmall ⊢
  obtain ⟨u, hu'⟩ : ∃ u : ℝ, u = Real.log L := ⟨_, rfl⟩
  rw [← hu'] at hu ⊢
  simp only [id, Real.norm_eq_abs] at hsmall
  rw [← hu', abs_of_nonneg (by linarith), abs_of_pos hL0] at hsmall
  have hKu : K * u ≤ L := by
    have h1 := mul_le_mul_of_nonneg_left hsmall hK0.le
    have e : K * (1 / K * L) = L := by
      field_simp
    linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 25 / 22 * (1 + ε) * u := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by
    rw [ha]
    have h2 : (1 : ℝ) ≤ 25 / 22 * (1 + ε) := by nlinarith
    nlinarith
  have ha0 : 0 < a := by linarith
  have haL : a ≤ L / 100 := by
    rw [ha, le_div_iff₀ (by norm_num)]
    rw [hK] at hKu
    linarith
  have hmain := hbound a ha1 haL
  rw [ha] at hmain
  rw [← ha] at hmain
  have hD : 51 / 50 * (a / L) = 51 / 50 * (25 / 22 * (1 + ε) * u / L) := by
    rw [ha]
  rw [← hD]
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hexp : Real.exp (-(22 / 25 * a)) = 1 / L * Real.exp (-(ε * u)) := by
    have hLexp : L = Real.exp u := by
      rw [hu', Real.exp_log hL0]
    have e : -(22 / 25 * a) = -u + -(ε * u) := by
      rw [ha]
      ring
    rw [e, Real.exp_add, Real.exp_neg u, ← hLexp, one_div]
  rw [hexp]
  have hE0 : 0 < Real.exp (-(ε * u)) := Real.exp_pos _
  have hstep : L / a * (1 / L * Real.exp (-(ε * u))) ≤ Real.exp (-(ε * u)) := by
    have e : L / a * (1 / L * Real.exp (-(ε * u))) = 1 / a * Real.exp (-(ε * u)) := by
      field_simp
    rw [e]
    refine mul_le_of_le_one_left hE0.le ?_
    rw [div_le_one ha0]
    exact ha1
  have := mul_le_mul_of_nonneg_left hstep (show 0 ≤ C * S by positivity)
  linarith

end GaloisForLFunctions.MultiscaleMollifiedZetaField
