import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedSplineKeepsAGammaReserveAtEveryOverlap

/-!
# Every profile without real Fourier zeros keeps a Gamma reserve

The Gamma reserve of the tilted spline uses only that its Fourier transform has no real zeros:
continuity then gives a positive floor on every compact band, and the logarithmic
Montgomery–Vaughan inequality retains coefficient mass in a band proportional to the horizon. The
same argument applies to every `C²` profile supported in `[0, 1]` whose Fourier transform has no
real zeros (`exists_noRealZero_archForm_reserve`).
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Finset Zeta23 RHTower

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticCastelnuovoSeveri BiScaleUncertainty.ChebyshevGauge
  ArithmeticElectrostatics ArithmeticPositivityTheory

theorem hasCompactSupport_of_unitSupport {φ : ℝ → ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) : HasCompactSupport φ :=
  HasCompactSupport.intro isCompact_Icc fun u hu => hsupp u hu

theorem atom_support_of_unitSupport {φ : ℝ → ℝ} (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {w : ℝ} (hw : 0 < w) : ∀ u, u ∉ Set.Icc 0 w → atomDilate φ w u = 0 := by
  intro u hu
  apply hsupp
  intro h
  apply hu
  exact ⟨by simpa only [zero_mul] using (le_div_iff₀ hw).mp h.1, (div_le_one hw).mp h.2⟩

/-- A profile with a nonzero transform at the origin has positive `L²` mass. -/
theorem integral_sq_pos_of_noRealZero {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0) : 0 < ∫ u, φ u ^ 2 := by
  have hc := hφ.continuous
  have hcs := hasCompactSupport_of_unitSupport hsupp
  have hft : paperFT (cx φ) 0 ≠ 0 := by simpa using hFT 0
  have hsqc : HasCompactSupport (fun u => φ u ^ 2) :=
    hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hi : Integrable (fun u => φ u ^ 2) :=
    (hc.pow 2).integrable_of_hasCompactSupport hsqc
  by_contra hpos
  have hz : (∫ u, φ u ^ 2) = 0 :=
    le_antisymm (le_of_not_gt hpos) (integral_nonneg fun u => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun u => sq_nonneg (φ u)) hi).mp hz
  have heq := (Continuous.ae_eq_iff_eq volume (hc.pow 2) continuous_const).mp hae
  have hfzero : ∀ u, φ u = 0 := by
    intro u
    have h := congrFun heq u
    change φ u ^ 2 = 0 at h
    nlinarith only [h]
  apply hft
  simp only [paperFT, cx, hfzero, Complex.ofReal_zero, zero_mul, integral_zero]

section NoRealZero

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
  (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
include hφ hsupp hFT

/-- A profile without real Fourier zeros has a positive Fourier floor on every compact band. -/
theorem exists_noRealZero_fourier_floor {c : ℝ} (hc : 0 < c) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc c (101 * c),
      m ≤ ‖paperFT (cx φ) (t : ℂ)‖ ^ 2 := by
  have hd := EvenSector.differentiable_paperFT_of_compact
    (Complex.continuous_ofReal.comp hφ.continuous)
    ((hasCompactSupport_of_unitSupport hsupp).comp_left Complex.ofReal_zero)
  have hcont : Continuous (fun t : ℝ => ‖paperFT (cx φ) (t : ℂ)‖ ^ 2) :=
    (hd.continuous.comp Complex.continuous_ofReal).norm.pow 2
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc c (101 * c)).Nonempty from ⟨c, le_rfl, by linarith only [hc]⟩)
    hcont.continuousOn
  refine ⟨_, ?_, fun r hr => hmin hr⟩
  exact sq_pos_of_pos (norm_pos_iff.mpr (hFT t))

omit hFT in
/-- **The band bound through the profile.** A floor `m ≤ |φ̂|²` on `[c, 101c]` transfers the
Montgomery–Vaughan band bound `∫_N^{101N} |D_x|² ≥ 48N Σ x_n²` to the atomic test of width `c/N`. -/
theorem noRealZero_highBand_mass {c m : ℝ} (hc : 0 < c) (hm : 0 < m)
    (hfloor : ∀ t ∈ Set.Icc c (101 * c), m ≤ ‖paperFT (cx φ) (t : ℂ)‖ ^ 2)
    {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    (48 * (c / N) ^ 2 * m * N) * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      ∫ t in (N : ℝ)..101 * N,
        ‖paperFT (cx (atomicTest N x (atomDilate φ (c / N)))) (t : ℂ)‖ ^ 2 := by
  let w := c / (N : ℝ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < w := div_pos hc hNR
  have hwN : w * (N : ℝ) = c := by dsimp only [w]; field_simp [hNR.ne']
  have hg : ContDiff ℝ 2 (atomDilate φ w) :=
    hφ.comp (contDiff_id.div_const _)
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest ((atom_support_of_unitSupport hsupp) hw) N x
  have hhat := EvenSector.differentiable_paperFT_of_compact
    (Complex.continuous_ofReal.comp hf.continuous) (hfc.comp_left Complex.ofReal_zero)
  have hFcont : Continuous (fun t : ℝ =>
      ‖paperFT (cx (atomicTest N x (atomDilate φ w))) (t : ℂ)‖ ^ 2) :=
    (hhat.continuous.comp Complex.continuous_ofReal).norm.pow 2
  have hDcont : Continuous (fun t : ℝ => ‖dirichletPoly N x (t : ℂ)‖ ^ 2) := by
    unfold dirichletPoly
    fun_prop
  have hpoint : ∀ t ∈ Set.Icc (N : ℝ) (101 * N),
      (w ^ 2 * m) * ‖dirichletPoly N x (t : ℂ)‖ ^ 2 ≤
        ‖paperFT (cx (atomicTest N x (atomDilate φ w))) (t : ℂ)‖ ^ 2 := by
    intro t ht
    have hlow := mul_le_mul_of_nonneg_left ht.1 hw.le
    have hhigh := mul_le_mul_of_nonneg_left ht.2 hw.le
    have hmem : w * t ∈ Set.Icc c (101 * c) := by
      constructor <;> nlinarith only [hlow, hhigh, hwN]
    have hmval := hfloor (w * t) hmem
    rw [paperFT_atomicTest_atomDilate hφ.continuous
      (hasCompactSupport_of_unitSupport hsupp) hw, ← Complex.ofReal_mul]
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hscaled := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hmval (sq_nonneg ‖dirichletPoly N x (t : ℂ)‖))
      (sq_nonneg w)
    simpa only [mul_assoc] using hscaled
  have hint := intervalIntegral.integral_mono_on (μ := volume)
    (show (N : ℝ) ≤ 101 * N by linarith only [hNR])
    ((hDcont.const_mul (w ^ 2 * m)).intervalIntegrable _ _)
    (hFcont.intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_const_mul] at hint
  have hMV := TransMetzlerWeilPositivity.BoundedOverlap.dirichletPoly_highBand_mass hN x
  calc
    _ = (w ^ 2 * m) * ((48 * N) * (∑ n ∈ Icc 1 N, x n ^ 2)) := by ring
    _ ≤ (w ^ 2 * m) * (∫ t in (N : ℝ)..101 * N, ‖dirichletPoly N x (t : ℂ)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hMV (mul_nonneg (sq_nonneg w) hm.le)
    _ ≤ _ := hint

/-- At every fixed overlap, the actual Gamma form of the explicit spline atoms
retains a positive logarithmic coefficient reserve, uniformly over all signed packets. -/
theorem exists_noRealZero_archForm_reserve {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, 0 ≤ b ∧ ∀ N : ℕ, 1 ≤ N → ∀ x : ℕ → ℝ,
      (a * Real.log N - b) * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
        archForm (atomicTest N x (atomDilate φ (c / N))) /
          ((c / N) * ∫ u, φ u ^ 2) := by
  obtain ⟨m, hm, hfloor⟩ := exists_noRealZero_fourier_floor hφ hsupp hFT hc
  let M := ∫ u, φ u ^ 2
  let a := 48 * c * m / (2 * Real.pi * M)
  let b := (factorialSpanGammaOffset + Real.log 2) * (1 + 2 * c * Real.exp c)
  have hM : 0 < M := (integral_sq_pos_of_noRealZero hφ hsupp hFT)
  have hoffset : 0 ≤ factorialSpanGammaOffset + Real.log 2 :=
    add_nonneg factorialSpanGammaOffset_nonneg (Real.log_nonneg (by norm_num))
  refine ⟨a, by dsimp only [a]; positivity, b,
    mul_nonneg hoffset (by positivity), fun N hN x => ?_⟩
  let w := c / (N : ℝ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < w := div_pos hc hNR
  have hg : ContDiff ℝ 2 (atomDilate φ w) :=
    hφ.comp (contDiff_id.div_const _)
  have hgc := hasCompactSupport_atomDilate hw.ne' (hasCompactSupport_of_unitSupport hsupp)
  have hgsupp := (atom_support_of_unitSupport hsupp) hw
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  have hgamma := archForm_ge_log_band_sub_mass hf hfc hNR
  have hband := noRealZero_highBand_mass hφ hsupp hc hm hfloor hN x
  have hphysical := integral_atomicTest_sq_le_fixed_overlap hg.continuous hgc hc hN hgsupp x
  rw [integral_atomDilate_sq hw] at hphysical
  have hbandCost := mul_le_mul_of_nonneg_left hband
    (div_nonneg (Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN))
      (by positivity : 0 ≤ 2 * Real.pi))
  have hmassCost := mul_le_mul_of_nonneg_left hphysical hoffset
  have hid : ((a * Real.log N - b) * (∑ n ∈ Icc 1 N, x n ^ 2)) * (w * M) =
      Real.log N / (2 * Real.pi) *
        ((48 * w ^ 2 * m * N) * (∑ n ∈ Icc 1 N, x n ^ 2)) -
      (factorialSpanGammaOffset + Real.log 2) *
        ((w * M) * (1 + 2 * c * Real.exp c) * (∑ n ∈ Icc 1 N, x n ^ 2)) := by
    dsimp only [a, b, w]
    field_simp [hM.ne', hNR.ne', Real.pi_ne_zero]
  apply (le_div_iff₀ (mul_pos hw hM)).mpr
  rw [hid]
  linarith only [hgamma, hbandCost, hmassCost]

end NoRealZero

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
