import GaloisForLFunctions.RHTower.SoninMixedBlockPolarizationSplit
import GaloisForLFunctions.RHTower.SoninBandLimitedShellVanishing
import GaloisForLFunctions.RHTower.SoninDilationSumFourierInjective
import GaloisForLFunctions.RHTower.SoninEulerTripleShellOverlap

/-!
# The physically polarized block of the coupling does not vanish

The block `(A_b - A_a) D_r (R_c - R_b)` sends every vector to something band-limited at `r c` and
supported, after the outer cutoff, only where the physical shell sees it.  If the block vanished,
each such image would be band-limited and would vanish on the shell `(a, b)`, hence be zero.  That
makes the dilation sum kill the whole Fourier annulus between `b` and `c`, which the annulus
injectivity forbids unless the annulus itself is trivial — and it is not.

So the physically polarized half of the aperture coupling is nonzero.
-/

noncomputable section


namespace RHTower

open ContinuousLinearMap

/-! ### The Fourier annulus is nontrivial -/

/-- The Fourier transform preserves evenness. -/
theorem fourierUnitary_mem_evenSubspace {f : SoninL2} (hf : f ∈ evenSubspace) :
    fourierUnitary f ∈ evenSubspace := by
  rw [mem_evenSubspace_iff, ← fourierUnitary_l2Reflection,
    (mem_evenSubspace_iff f).mp hf]

/-- **A nondegenerate Fourier annulus is a nonzero operator.**  Its witness is the Fourier
transform of a symmetric physical shell vector. -/
theorem evenFourierCutoff_sub_ne_zero {b c : ℝ} (hb : 0 < b) (hbc : b < c) :
    evenFourierCutoff c - evenFourierCutoff b ≠ 0 := by
  intro hzero
  set w : evenSubspace := evenShellVectorEven b c hbc 0 with hw
  have hwnorm : ‖w‖ = 1 := (evenShellVectorEven_orthonormal b c hb hbc).norm_eq_one 0
  have hwne : (w : SoninL2) ≠ 0 := by
    intro hc0
    have : ‖w‖ = 0 := by
      rw [show ‖w‖ = ‖(w : SoninL2)‖ from rfl, hc0, norm_zero]
    rw [hwnorm] at this
    exact one_ne_zero this
  have hmem : fourierUnitary (w : SoninL2) ∈ evenSubspace :=
    fourierUnitary_mem_evenSubspace w.property
  set u : evenSubspace := ⟨fourierUnitary (w : SoninL2), hmem⟩ with hu
  have hFu : fourierUnitary (u : SoninL2) = (w : SoninL2) :=
    fourierUnitary_fourierUnitary_of_mem_evenSubspace w.property
  have happ := DFunLike.congr_fun hzero u
  rw [sub_apply, zero_apply, sub_eq_zero] at happ
  have hcoe := congrArg (fun z : evenSubspace => (z : SoninL2)) happ
  simp only [coe_evenFourierCutoff_apply, fourierCutoff_apply] at hcoe
  rw [hFu] at hcoe
  have hAc : indicatorCutoff (centralInterval c) (measurableSet_centralInterval c)
      (w : SoninL2) = (w : SoninL2) := by
    have h := congrArg (fun z : evenSubspace => (z : SoninL2))
      (evenIndicatorCutoff_evenShellVectorEven_of_le b c c hbc le_rfl 0)
    simpa [hw] using h
  have hAb : indicatorCutoff (centralInterval b) (measurableSet_centralInterval b)
      (w : SoninL2) = 0 := by
    have h := congrArg (fun z : evenSubspace => (z : SoninL2))
      (evenIndicatorCutoff_evenShellVectorEven_eq_zero b c b hbc le_rfl 0)
    simpa [hw] using h
  rw [hAc, hAb, map_zero] at hcoe
  exact hwne (fourierUnitary.symm.injective (by simpa using hcoe))

/-! ### The image of the physical block is band-limited -/

/-- Dilating a Fourier annulus at `c` keeps it band-limited at `r c`. -/
theorem evenFourierCutoff_mul_evenDilationSum_mul_evenFourierCutoff
    {c r : ℝ} (hc : 0 ≤ c) (hr : 1 < r) :
    evenFourierCutoff (r * c) * (evenDilationSum r hr * evenFourierCutoff c) =
      evenDilationSum r hr * evenFourierCutoff c := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
  have hcov1 : evenFourierCutoff (r * c) * evenDilationCLM r hr0 =
      evenDilationCLM r hr0 * evenFourierCutoff c := by
    rw [evenFourierCutoff_mul_evenDilationCLM (r * c) r hr0,
      show r⁻¹ * (r * c) = c from inv_mul_cancel_left₀ hr0.ne' c]
  have hcov2 : evenFourierCutoff (r * c) * evenDilationCLM r⁻¹ hrinv =
      evenDilationCLM r⁻¹ hrinv * evenFourierCutoff (r * (r * c)) := by
    rw [evenFourierCutoff_mul_evenDilationCLM (r * c) r⁻¹ hrinv,
      show (r⁻¹)⁻¹ * (r * c) = r * (r * c) by rw [inv_inv]]
  have hnest1 : evenFourierCutoff c * evenFourierCutoff c = evenFourierCutoff c :=
    evenFourierCutoff_mul_of_le c c le_rfl
  have hrr : (1 : ℝ) ≤ r * r := one_le_mul_of_one_le_of_one_le hr.le hr.le
  have hcc : c ≤ r * (r * c) := by
    rw [← mul_assoc]
    exact le_mul_of_one_le_left hc hrr
  have hnest2 : evenFourierCutoff (r * (r * c)) * evenFourierCutoff c = evenFourierCutoff c :=
    evenFourierCutoff_mul_of_le_rev c (r * (r * c)) hcc
  calc evenFourierCutoff (r * c) * (evenDilationSum r hr * evenFourierCutoff c)
      = evenFourierCutoff (r * c) * evenDilationCLM r hr0 * evenFourierCutoff c +
          evenFourierCutoff (r * c) * evenDilationCLM r⁻¹ hrinv * evenFourierCutoff c := by
        rw [evenDilationSum_eq]; noncomm_ring
    _ = evenDilationCLM r hr0 * (evenFourierCutoff c * evenFourierCutoff c) +
          evenDilationCLM r⁻¹ hrinv *
            (evenFourierCutoff (r * (r * c)) * evenFourierCutoff c) := by
        rw [hcov1, hcov2]; noncomm_ring
    _ = evenDilationCLM r hr0 * evenFourierCutoff c +
          evenDilationCLM r⁻¹ hrinv * evenFourierCutoff c := by rw [hnest1, hnest2]
    _ = evenDilationSum r hr * evenFourierCutoff c := by
        rw [evenDilationSum_eq]; noncomm_ring

/-! ### Nonvanishing -/

/-- **The physically polarized block of the aperture coupling is nonzero.** -/
theorem soninMixedPhysicalBlock_ne_zero
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hr : 1 < r) :
    soninMixedPhysicalBlock a b c r hr ≠ 0 := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  intro hzero
  have hshellzero : evenFourierCutoff c - evenFourierCutoff b = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    have hidem :
        evenFourierCutoff c * (evenFourierCutoff c - evenFourierCutoff b) =
          evenFourierCutoff c - evenFourierCutoff b := by
      rw [mul_sub, evenFourierCutoff_mul_of_le c c le_rfl,
        evenFourierCutoff_mul_of_le_rev b c hbc.le]
    have hkill :
        evenFourierCutoff b * (evenFourierCutoff c - evenFourierCutoff b) = 0 := by
      rw [mul_sub, evenFourierCutoff_mul_of_le b c hbc.le,
        evenFourierCutoff_mul_of_le b b le_rfl, sub_self]
    set v : evenSubspace := (evenFourierCutoff c - evenFourierCutoff b) w with hv
    have hcv : evenFourierCutoff c v = v := by
      have h := DFunLike.congr_fun hidem w
      rw [mul_apply_eq_comp] at h
      exact h
    have hbv : evenFourierCutoff b v = 0 := by
      have h := DFunLike.congr_fun hkill w
      rw [mul_apply_eq_comp, zero_apply] at h
      exact h
    have hDzero : evenDilationSum r hr v = 0 := by
      have hRy :
          evenFourierCutoff (r * c) (evenDilationSum r hr v) = evenDilationSum r hr v := by
        have hband := evenFourierCutoff_mul_evenDilationSum_mul_evenFourierCutoff hc.le hr
        have h := DFunLike.congr_fun hband v
        rw [mul_apply_eq_comp, mul_apply_eq_comp, hcv] at h
        exact h
      have hshell :
          (evenIndicatorCutoff b - evenIndicatorCutoff a) (evenDilationSum r hr v) = 0 := by
        have h := DFunLike.congr_fun hzero w
        unfold soninMixedPhysicalBlock at h
        rw [zero_apply, mul_apply_eq_comp, mul_apply_eq_comp] at h
        exact h
      exact eq_zero_of_evenFourierCutoff_eq_self_of_shell_apply_eq_zero ha.le hab hRy hshell
    have := eq_zero_of_evenDilationSum_apply_eq_zero_of_fourierAnnulus hb hr hDzero hcv hbv
    simpa [hv] using this
  exact evenFourierCutoff_sub_ne_zero hb hbc hshellzero

/-- **The four mixed blocks of the aperture coupling do not cancel.**  The two polarizations can
only cancel by vanishing separately, and the physical one does not vanish. -/
theorem soninMixedPhysicalBlock_add_soninMixedFourierBlock_ne_zero
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hr : 1 < r) :
    soninMixedPhysicalBlock a b c r hr + soninMixedFourierBlock a b c r hr ≠ 0 := by
  intro h
  exact soninMixedPhysicalBlock_ne_zero ha hab hbc hr
    ((soninMixedPhysicalBlock_add_soninMixedFourierBlock_eq_zero_iff a b c r hr hab.le).mp h).1

/-- The same statement in the four-term form: the mixed expansion of the successive-layer coupling
is a nonzero operator. -/
theorem soninApertureCouplingMixedTerms_ne_zero
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hr : 1 < r) :
    (evenIndicatorCutoff b - evenIndicatorCutoff a) *
            evenDilationCLM r (zero_lt_one.trans hr) *
            (evenFourierCutoff c - evenFourierCutoff b) +
          (evenIndicatorCutoff b - evenIndicatorCutoff a) *
            evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) *
            (evenFourierCutoff c - evenFourierCutoff b) +
          (evenFourierCutoff b - evenFourierCutoff a) *
            evenDilationCLM r (zero_lt_one.trans hr) *
            (evenIndicatorCutoff c - evenIndicatorCutoff b) +
        (evenFourierCutoff b - evenFourierCutoff a) *
          evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) *
          (evenIndicatorCutoff c - evenIndicatorCutoff b) ≠ 0 := by
  rw [← soninMixedPhysicalBlock_add_soninMixedFourierBlock_eq a b c r hr]
  exact soninMixedPhysicalBlock_add_soninMixedFourierBlock_ne_zero ha hab hbc hr

/-- **The coupling vanishing question is an ideal-membership question.**  The successive-layer
coupling is congruent to the sum of the two polarized blocks, so it can only vanish if that sum lies
in the relative ideal. -/
theorem evenSoninApertureSuccessiveLayerTransition_ne_zero_of_polarizedBlocks_notMem_ideal
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) (hcr : c ≤ r * a)
    (hnot : ¬ IsSoninPrincipalRelativeIdeal
      (soninMixedPhysicalBlock a b c r hr + soninMixedFourierBlock a b c r hr)) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr ≠ 0 := by
  intro hzero
  have hcong := evenSoninApertureSuccessiveLayerTransition_principalRelativeEq_polarizedBlocks
    ha hb hc hab hbc hr hcr
  rw [hzero] at hcong
  have h2 : IsSoninPrincipalRelativeIdeal
      (0 - (soninMixedPhysicalBlock a b c r hr + soninMixedFourierBlock a b c r hr)) := hcong
  exact hnot (IsSoninPrincipalRelativeIdeal.of_eq h2.neg (by abel))

end RHTower
