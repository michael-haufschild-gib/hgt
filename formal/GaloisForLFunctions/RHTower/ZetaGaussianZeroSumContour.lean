import GaloisForLFunctions.RHTower.ZetaChiGaussianKernel
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinNegativeHalfHorizontal
import GaloisForLFunctions.RHTower.LevinsonStripBound

/-!
# Zero sums of `ζ` over the rectangle `[−½, 11/10] × [t₀, Y]`

For `H` holomorphic near the closed rectangle `R = [−½, 11/10] × [t₀, Y]` (`0 < t₀ < Y`), with `ζ` free of
zeros on the two horizontal edges,

`2πi Σ_{ρ ∈ R} m_ρ H(ρ) = ∮_{∂R} H ζ'/ζ`

(`zeroSum_eq_rectIntegral`): the corpus argument principle for `(s − 1)ζ(s)`, and the rectangle Cauchy
theorem for `H/(s − 1)`.  The left edge `Re s = −½` carries no zero, because
`ζ(s) = χ(s) ζ(1 − s)` there.

Admissible edges:
* a fixed bottom height `t₀ ∈ [1, 2]` free of zeros (finiteness of the zeros in a box);
* for all large `T`, a top height `Y ∈ [T², T² + 3]` free of zeros, on which `|ζ'/ζ| ≤ C Y²`
  (corpus horizontal control, whose polylogarithmic bound is made polynomial here).

For a conjugation-symmetric integrand the left edge reduces to the full line:
`2 Re ∫_{t₀}^{Y} F(−½+iy) dy = Re ∫_ℝ F(−½+iy) dy − Re ∫_{−t₀}^{t₀} F − 2 Re ∫_{y > Y} F`
(`re_integral_leftEdge_eq`).
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower.GaussZeroSum

noncomputable section

/-- The zeros of `(s − 1)ζ(s)` in `[−½, 11/10] × [t₀, Y]`. -/
abbrev rectZeros (t₀ Y : ℝ) : Finset ℂ :=
  Sieve.zetaResidueUnitClosedRectangleZeros ((-1 / 2 : ℂ) + t₀ * I) ((11 / 10 : ℂ) + Y * I)

/-- The analytic multiplicity of a zero. -/
abbrev mult (w : ℂ) : ℕ := (analyticOrderAt zetaResidueUnit w).toNat

theorem gammaR_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Complex.Gammaℝ z ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  apply hz
  rw [hn]
  simp

/-- `ζ` has no zero on the line `Re s = −½` off the real axis. -/
theorem riemannZeta_leftLine_ne_zero {y : ℝ} (hy : y ≠ 0) :
    riemannZeta ((-1 / 2 : ℂ) + y * I) ≠ 0 := by
  set s : ℂ := (-1 / 2 : ℂ) + y * I with hs
  have hre : s.re = -1 / 2 := by simp [hs]
  have him : s.im = y := by simp [hs]
  have h0 : s ≠ 0 := by intro h; rw [h] at hre; norm_num at hre
  have h1 : s ≠ 1 := by intro h; rw [h] at hre; norm_num at hre
  have h1s : (1 - s).im ≠ 0 := by rw [Complex.sub_im, him]; simpa using hy
  have hG : Complex.Gammaℝ (1 - s) ≠ 0 := gammaR_ne_zero_of_im_ne_zero h1s
  rw [zeta_eq_zetaChi_mul h0 h1 hG]
  refine mul_ne_zero ?_ (riemannZeta_ne_zero_of_one_lt_re (by rw [Complex.sub_re, hre]; norm_num))
  unfold zetaChi
  exact div_ne_zero hG (gammaR_ne_zero_of_im_ne_zero (by rw [him]; exact hy))

theorem zetaResidueUnit_ne_zero_of {s : ℂ} (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    zetaResidueUnit s ≠ 0 := by
  rw [(zetaResidueUnit_eventuallyEq hs1).eq_of_nhds]
  exact mul_ne_zero (sub_ne_zero.mpr hs1) hz

theorem ne_one_of_im_pos {s : ℂ} (hs : 0 < s.im) : s ≠ 1 := by
  intro h; rw [h] at hs; simp at hs

/-- **A zero-free bottom edge.** -/
theorem exists_bottom_height :
    ∃ t₀ ∈ Icc (1 : ℝ) 2, ∀ x ∈ Icc (-1 / 2 : ℝ) (11 / 10), riemannZeta ((x : ℂ) + t₀ * I) ≠ 0 := by
  classical
  set S : Finset ℝ := (rectZeros 1 2).image Complex.im with hS
  obtain ⟨t₀, ht₀, hnot⟩ := (Set.Icc_infinite (by norm_num : (1 : ℝ) < 2)).exists_notMem_finset S
  refine ⟨t₀, ht₀, fun x hx hzero => hnot ?_⟩
  have hpt1 : ((x : ℂ) + t₀ * I) ≠ 1 := ne_one_of_im_pos (by simp; linarith [ht₀.1])
  have hZ : zetaResidueUnit ((x : ℂ) + t₀ * I) = 0 := by
    rw [(zetaResidueUnit_eventuallyEq hpt1).eq_of_nhds, hzero, mul_zero]
  have hmem : ((x : ℂ) + t₀ * I) ∈ rectZeros 1 2 := by
    rw [Sieve.mem_zetaResidueUnitClosedRectangleZeros]
    refine ⟨?_, hZ⟩
    rw [Complex.mem_reProdIm]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.add_im, Complex.mul_im]
    norm_num
    exact ⟨⟨by linarith [hx.1], hx.2⟩, ht₀⟩
  rw [hS, Finset.mem_image]
  exact ⟨_, hmem, by simp⟩

theorem logDeriv_zetaResidueUnit_eq {s : ℂ} (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv zetaResidueUnit s = 1 / (s - 1) + deriv riemannZeta s / riemannZeta s := by
  have hd : HasDerivAt (fun z => (z - 1) * riemannZeta z)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
    ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs1).hasDerivAt
  rw [logDeriv_apply, (zetaResidueUnit_eventuallyEq hs1).deriv_eq, hd.deriv,
    (zetaResidueUnit_eventuallyEq hs1).eq_of_nhds]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp

theorem horizontalLogDerivBound_eq (Ce Cj : ℝ) (Qe Qj X N : ℕ) :
    Sieve.inghamDetectorHorizontalLogDerivBound Ce Qe Cj Qj X N =
      4 * N * (Sieve.inghamDetectorTubeJensenBound Cj Qj X + 1) +
        280 * (Real.log (((Ce * (X : ℝ) ^ Qe) / ((1 : ℝ) / 4) ^ N) /
          (((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ N)) + 1) := by
  unfold Sieve.inghamDetectorHorizontalLogDerivBound
  dsimp only
  rw [div_inv_eq_mul]
  ring

/-- The polylogarithmic horizontal bound of the corpus is at most `K X²`. -/
theorem horizontalLogDerivBound_le {Ce Cj : ℝ} (hCe : 1 ≤ Ce) (hCj : 1 ≤ Cj) (Qe Qj : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 12 ≤ X → ∀ N : ℕ,
      (N : ℝ) ≤ Sieve.inghamDetectorTubeJensenBound Cj Qj X →
        Sieve.inghamDetectorHorizontalLogDerivBound Ce Qe Cj Qj X N ≤ K * (X : ℝ) ^ 2 := by
  set A : ℝ := 16 * (Real.log (2 * Cj) + Qj) with hA
  have hlog2Cj : 0 ≤ Real.log (2 * Cj) := Real.log_nonneg (by linarith)
  have hlog2Ce : 0 ≤ Real.log (2 * Ce) := Real.log_nonneg (by linarith)
  have hA0 : 0 ≤ A := by positivity
  set B : ℝ := Real.log (2 * Ce) + 1 + Qe + 15 * A with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨4 * A * (A + 1) + 280 * B, by positivity, fun X hX N hN => ?_⟩
  have hx : (12 : ℝ) ≤ X := by exact_mod_cast hX
  have hx1 : (1 : ℝ) ≤ X := by linarith
  have hx0 : (0 : ℝ) < X := by linarith
  have hlogx : Real.log X ≤ X := by
    have := Real.log_le_sub_one_of_pos hx0; linarith
  have hlogx0 : 0 ≤ Real.log X := Real.log_nonneg hx1
  have h1615 : (1 : ℝ) / 16 ≤ Real.log ((4 : ℝ) / (15 / 4)) := by
    have h := Real.add_one_le_exp (-(1 / 16 : ℝ))
    have hpos : (0 : ℝ) < 4 / (15 / 4) := by norm_num
    rw [← Real.exp_le_exp, Real.exp_log hpos]
    have hexp : Real.exp (1 / 16) * Real.exp (-(1 / 16)) = 1 := by
      rw [← Real.exp_add]; simp
    have hpos2 := Real.exp_pos (1 / 16 : ℝ)
    nlinarith
  -- the Jensen bound `L`
  have hLnum : Real.log ((Cj * (X : ℝ) ^ Qj) / ((1 : ℝ) / 2)) = Real.log (2 * Cj) + Qj * Real.log X := by
    rw [show (Cj * (X : ℝ) ^ Qj) / ((1 : ℝ) / 2) = (2 * Cj) * (X : ℝ) ^ Qj by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
  set L := Sieve.inghamDetectorTubeJensenBound Cj Qj X with hLdef
  have hL : L ≤ A * X := by
    rw [hLdef, Sieve.inghamDetectorTubeJensenBound, hLnum]
    have hden : 0 < Real.log ((4 : ℝ) / (15 / 4)) := by linarith
    rw [div_le_iff₀ hden]
    have h1 : Real.log (2 * Cj) + Qj * Real.log X ≤ (Real.log (2 * Cj) + Qj) * X := by
      have : (Qj : ℝ) * Real.log X ≤ Qj * X := mul_le_mul_of_nonneg_left hlogx (by positivity)
      nlinarith
    have h2 : (Real.log (2 * Cj) + Qj) * X ≤ A * X * Real.log ((4 : ℝ) / (15 / 4)) := by
      rw [hA]
      have hq : 0 ≤ (Real.log (2 * Cj) + Qj) * X := by positivity
      nlinarith
    linarith
  have hL0 : 0 ≤ L := by
    rw [hLdef, Sieve.inghamDetectorTubeJensenBound, hLnum]
    apply div_nonneg (by positivity)
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- unfold the horizontal bound
  have hlogM : Real.log (((Ce * (X : ℝ) ^ Qe) / ((1 : ℝ) / 4) ^ N) /
      (((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ N)) =
      Real.log (2 * Ce) + Qe * Real.log X + N * Real.log 15 := by
    rw [show ((Ce * (X : ℝ) ^ Qe) / ((1 : ℝ) / 4) ^ N) / (((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ N) =
      (2 * Ce) * (X : ℝ) ^ Qe * (15 : ℝ) ^ N by
        rw [div_pow, div_pow, one_pow]
        field_simp]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
  have hlog15 : Real.log 15 ≤ 15 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 15); linarith
  rw [horizontalLogDerivBound_eq, ← hLdef, hlogM]
  have hNL : (N : ℝ) ≤ A * X := hN.trans hL
  have hterm1 : 4 * (N : ℝ) * (L + 1) ≤ 4 * A * (A + 1) * (X : ℝ) ^ 2 := by
    have : (N : ℝ) * (L + 1) ≤ (A * X) * (A * X + 1) := by
      apply mul_le_mul hNL (by linarith) (by linarith) (by positivity)
    have h2 : (A * X) * (A * X + 1) ≤ A * (A + 1) * (X : ℝ) ^ 2 := by
      have : A * X ≤ A * X ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hA0; nlinarith
      nlinarith
    nlinarith
  have hlogbound : Real.log (2 * Ce) + Qe * Real.log X + N * Real.log 15 + 1 ≤ B * X := by
    have h1 : (Qe : ℝ) * Real.log X ≤ Qe * X := mul_le_mul_of_nonneg_left hlogx (by positivity)
    have h2 : (N : ℝ) * Real.log 15 ≤ 15 * A * X := by
      have h15 : 0 ≤ Real.log 15 := Real.log_nonneg (by norm_num)
      calc (N : ℝ) * Real.log 15 ≤ A * X * 15 := mul_le_mul hNL hlog15 h15 (by positivity)
        _ = 15 * A * X := by ring
    have h3 : Real.log (2 * Ce) ≤ Real.log (2 * Ce) * X := le_mul_of_one_le_right hlog2Ce hx1
    have h4 : B * X = Real.log (2 * Ce) * X + X + Qe * X + 15 * A * X := by rw [hB]; ring
    rw [h4]
    linarith
  have hBX : B * X ≤ B * X ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hB0
    rw [sq]; exact le_mul_of_one_le_left hx0.le hx1
  have hterm2 : 280 * (Real.log (2 * Ce) + Qe * Real.log X + N * Real.log 15 + 1) ≤
      280 * B * (X : ℝ) ^ 2 := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hlogbound.trans hBX) (by norm_num)
  linarith [hterm1, hterm2]

/-- **A zero-free top edge** at every large height, with a polynomial bound for `ζ'/ζ`. -/
theorem exists_top_height :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T → ∃ Y ∈ Icc (T ^ 2) (T ^ 2 + 3),
      ∀ x ∈ Icc (-1 / 2 : ℝ) 2, riemannZeta ((x : ℂ) + Y * I) ≠ 0 ∧
        ‖deriv riemannZeta ((x : ℂ) + Y * I) / riemannZeta ((x : ℂ) + Y * I)‖ ≤ C * Y ^ 2 := by
  obtain ⟨Ce, Qe, Cj, Qj, hCe, hCj, hctrl⟩ :=
    Sieve.exists_zetaResidueUnit_negativeHalf_horizontal_logDeriv_control
  obtain ⟨K, hK0, hK⟩ := horizontalLogDerivBound_le hCe hCj Qe Qj
  refine ⟨4 * K + 1, by positivity, fun T hT => ?_⟩
  set X : ℕ := ⌈T ^ 2⌉₊ + 1 with hX
  have hT2 : (16 : ℝ) ≤ T ^ 2 := by nlinarith
  have hXlow : T ^ 2 + 1 ≤ (X : ℝ) := by
    rw [hX]; push_cast; linarith [Nat.le_ceil (T ^ 2)]
  have hXhigh : (X : ℝ) ≤ T ^ 2 + 2 := by
    rw [hX]; push_cast; linarith [Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ T ^ 2)]
  have hX12 : 12 ≤ X := by
    have : (12 : ℝ) ≤ X := by linarith
    exact_mod_cast this
  have hXpos : (0 : ℝ) < X := by linarith
  obtain ⟨Y, hY, N, hN, hgood⟩ := hctrl (X := X) (tau := (X : ℝ)) hX12
    (by rw [abs_of_pos hXpos]; linarith) (by rw [abs_of_pos hXpos]; linarith)
  have hYlow : T ^ 2 ≤ Y := by linarith [hY.1]
  have hYhigh : Y ≤ T ^ 2 + 3 := by linarith [hY.2]
  refine ⟨Y, ⟨hYlow, hYhigh⟩, fun x hx => ?_⟩
  obtain ⟨hZ, hbound⟩ := hgood x hx
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hs1 : ((x : ℂ) + Y * I) ≠ 1 := ne_one_of_im_pos (by simp; linarith)
  have hz : riemannZeta ((x : ℂ) + Y * I) ≠ 0 := by
    intro h
    apply hZ
    rw [(zetaResidueUnit_eventuallyEq hs1).eq_of_nhds, h, mul_zero]
  refine ⟨hz, ?_⟩
  have hlog := logDeriv_zetaResidueUnit_eq hs1 hz
  have heq : deriv riemannZeta ((x : ℂ) + Y * I) / riemannZeta ((x : ℂ) + Y * I) =
      -Sieve.zetaLogDerivReg ((x : ℂ) + Y * I) - 1 / (((x : ℂ) + Y * I) - 1) := by
    unfold Sieve.zetaLogDerivReg
    rw [hlog]; ring
  rw [heq]
  have hnorm1 : ‖1 / (((x : ℂ) + Y * I) - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    apply div_le_one_of_le₀ _ (norm_nonneg _)
    calc (1 : ℝ) ≤ Y := hY1
      _ = |(((x : ℂ) + Y * I) - 1).im| := by simp; exact (abs_of_pos (by linarith)).symm
      _ ≤ ‖((x : ℂ) + Y * I) - 1‖ := Complex.abs_im_le_norm _
  have hKX := hK X hX12 N hN
  have hXY : (X : ℝ) ≤ 2 * Y := by linarith
  calc ‖-Sieve.zetaLogDerivReg ((x : ℂ) + Y * I) - 1 / (((x : ℂ) + Y * I) - 1)‖
      ≤ ‖Sieve.zetaLogDerivReg ((x : ℂ) + Y * I)‖ + ‖1 / (((x : ℂ) + Y * I) - 1)‖ := by
        rw [sub_eq_add_neg, ← neg_add]; rw [norm_neg]; exact norm_add_le _ _
    _ ≤ K * (X : ℝ) ^ 2 + 1 := by linarith [hbound.trans hKX]
    _ ≤ K * (2 * Y) ^ 2 + Y ^ 2 := by
        have : (X : ℝ) ^ 2 ≤ (2 * Y) ^ 2 := by nlinarith
        nlinarith
    _ = (4 * K + 1) * Y ^ 2 := by ring

/-! ## The contour identity -/

theorem analyticOnNhd_riemannZeta : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} :=
  DifferentiableOn.analyticOnNhd (fun _ hs => (differentiableAt_riemannZeta hs).differentiableWithinAt)
    isOpen_ne

theorem continuousAt_deriv_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    ContinuousAt (deriv riemannZeta) s :=
  (analyticOnNhd_riemannZeta.deriv s hs).continuousAt

theorem continuousAt_mul_logDeriv_zeta {H : ℂ → ℂ} {s : ℂ} (hH : ContinuousAt H s) (hs : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    ContinuousAt (fun z => H z * (deriv riemannZeta z / riemannZeta z)) s :=
  hH.mul ((continuousAt_deriv_riemannZeta hs).div
    (differentiableAt_riemannZeta hs).continuousAt hz)

theorem intervalIntegrable_comp_of_continuousAt {f : ℂ → ℂ} {γ : ℝ → ℂ} (hγ : Continuous γ)
    {a b : ℝ} (h : ∀ x ∈ uIcc a b, ContinuousAt f (γ x)) :
    IntervalIntegrable (fun x => f (γ x)) volume a b :=
  ContinuousOn.intervalIntegrable fun x hx => ((h x hx).comp hγ.continuousAt).continuousWithinAt

/-- **The zero sum as a boundary integral** of `H ζ'/ζ` around `[−½, 11/10] × [t₀, Y]`. -/
theorem zeroSum_eq_rectIntegral {H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hH : AnalyticOnNhd ℂ H U)
    {t₀ Y : ℝ} (ht₀ : 0 < t₀) (hY : t₀ < Y)
    (hsub : (uIcc (-1 / 2 : ℝ) (11 / 10) ×ℂ uIcc t₀ Y) ⊆ U)
    (hbot : ∀ x ∈ Icc (-1 / 2 : ℝ) (11 / 10), riemannZeta ((x : ℂ) + t₀ * I) ≠ 0)
    (htop : ∀ x ∈ Icc (-1 / 2 : ℝ) (11 / 10), riemannZeta ((x : ℂ) + Y * I) ≠ 0) :
    2 * Real.pi * I * ∑ w ∈ rectZeros t₀ Y, (mult w : ℂ) * H w =
      rectIntegral (fun s => H s * (deriv riemannZeta s / riemannZeta s))
        ((-1 / 2 : ℂ) + t₀ * I) ((11 / 10 : ℂ) + Y * I) := by
  set z₁ : ℂ := (-1 / 2 : ℂ) + t₀ * I with hz₁
  set z₂ : ℂ := (11 / 10 : ℂ) + Y * I with hz₂
  have h1re : z₁.re = -1 / 2 := by simp [hz₁]
  have h1im : z₁.im = t₀ := by simp [hz₁]
  have h2re : z₂.re = 11 / 10 := by simp [hz₂]
  have h2im : z₂.im = Y := by simp [hz₂]
  have hIcc1 : uIcc z₁.re z₂.re = Icc (-1 / 2 : ℝ) (11 / 10) := by
    rw [h1re, h2re, uIcc_of_le (by norm_num)]
  have hIcc2 : uIcc z₁.im z₂.im = Icc t₀ Y := by rw [h1im, h2im, uIcc_of_le hY.le]
  -- the edge points
  have hedge : ∀ s : ℂ, (s ∈ (fun x : ℝ => (x : ℂ) + z₁.im * I) '' Icc (-1 / 2 : ℝ) (11 / 10) ∨
      s ∈ (fun x : ℝ => (x : ℂ) + z₂.im * I) '' Icc (-1 / 2 : ℝ) (11 / 10) ∨
      s ∈ (fun y : ℝ => (z₂.re : ℂ) + y * I) '' Icc t₀ Y ∨
      s ∈ (fun y : ℝ => (z₁.re : ℂ) + y * I) '' Icc t₀ Y) →
      s ≠ 1 ∧ riemannZeta s ≠ 0 := by
    intro s hs
    rcases hs with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · refine ⟨ne_one_of_im_pos (by simp [h1im]; exact ht₀), ?_⟩
      rw [h1im]; exact hbot x hx
    · refine ⟨ne_one_of_im_pos (by simp [h2im]; linarith), ?_⟩
      rw [h2im]; exact htop x hx
    · have hy0 : 0 < y := by linarith [hy.1]
      refine ⟨ne_one_of_im_pos (by simp; exact hy0), ?_⟩
      rw [h2re]
      exact riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)
    · have hy0 : 0 < y := by linarith [hy.1]
      refine ⟨ne_one_of_im_pos (by simp; exact hy0), ?_⟩
      rw [h1re]
      push_cast
      exact riemannZeta_leftLine_ne_zero hy0.ne'
  have hZ : ∀ s : ℂ, s ≠ 1 ∧ riemannZeta s ≠ 0 → zetaResidueUnit s ≠ 0 :=
    fun s hs => zetaResidueUnit_ne_zero_of hs.1 hs.2
  have hsub' : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    rw [h1re, h2re, h1im, h2im]; exact hsub
  have hcorp := Sieve.rectIntegral_mul_logDeriv_zetaResidueUnit_eq_closedRectangleZeroSum hU hH hsub'
    (by rw [h1re, h2re]; norm_num) (by rw [h1im, h2im]; exact hY)
    (fun x hx => hZ _ (hedge _ (Or.inl ⟨x, by rwa [hIcc1] at hx, rfl⟩)))
    (fun x hx => hZ _ (hedge _ (Or.inr (Or.inl ⟨x, by rwa [hIcc1] at hx, rfl⟩))))
    (fun y hy => hZ _ (hedge _ (Or.inr (Or.inr (Or.inl ⟨y, by rwa [hIcc2] at hy, rfl⟩)))))
    (fun y hy => hZ _ (hedge _ (Or.inr (Or.inr (Or.inr ⟨y, by rwa [hIcc2] at hy, rfl⟩)))))
  -- split `logDeriv ((s − 1)ζ) = 1/(s − 1) + ζ'/ζ` on the edges
  have hsplit : rectIntegral (fun z => H z * logDeriv zetaResidueUnit z) z₁ z₂ =
      rectIntegral (fun z => H z * (deriv riemannZeta z / riemannZeta z) + H z * (z - 1)⁻¹) z₁ z₂ := by
    refine rectIntegral_congr (S := {s : ℂ | s ≠ 1 ∧ riemannZeta s ≠ 0}) (fun s hs => ?_)
      (fun x hx => hedge _ (Or.inl ⟨x, by rwa [hIcc1] at hx, rfl⟩))
      (fun x hx => hedge _ (Or.inr (Or.inl ⟨x, by rwa [hIcc1] at hx, rfl⟩)))
      (fun y hy => hedge _ (Or.inr (Or.inr (Or.inl ⟨y, by rwa [hIcc2] at hy, rfl⟩))))
      (fun y hy => hedge _ (Or.inr (Or.inr (Or.inr ⟨y, by rwa [hIcc2] at hy, rfl⟩))))
    rw [logDeriv_zetaResidueUnit_eq hs.1 hs.2]
    ring
  have hHc : ∀ s ∈ U, ContinuousAt H s := fun s hs => (hH s hs).continuousAt
  have hmem : ∀ s : ℂ, (s ∈ (fun x : ℝ => (x : ℂ) + z₁.im * I) '' Icc (-1 / 2 : ℝ) (11 / 10) ∨
      s ∈ (fun x : ℝ => (x : ℂ) + z₂.im * I) '' Icc (-1 / 2 : ℝ) (11 / 10) ∨
      s ∈ (fun y : ℝ => (z₂.re : ℂ) + y * I) '' Icc t₀ Y ∨
      s ∈ (fun y : ℝ => (z₁.re : ℂ) + y * I) '' Icc t₀ Y) → s ∈ U := by
    intro s hs
    apply hsub
    rw [Complex.mem_reProdIm]
    rcases hs with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, h1im]
      simp only [mul_zero, sub_zero, add_zero, mul_one, zero_add]
      rw [uIcc_of_le (by norm_num), uIcc_of_le hY.le]
      exact ⟨hx, left_mem_Icc.mpr hY.le⟩
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, h2im]
      simp only [mul_zero, sub_zero, add_zero, mul_one, zero_add]
      rw [uIcc_of_le (by norm_num), uIcc_of_le hY.le]
      exact ⟨hx, right_mem_Icc.mpr hY.le⟩
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, h2re]
      simp only [mul_zero, sub_zero, add_zero, mul_one, zero_add]
      rw [uIcc_of_le (by norm_num), uIcc_of_le hY.le]
      exact ⟨right_mem_Icc.mpr (by norm_num), hy⟩
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, h1re]
      simp only [mul_zero, sub_zero, add_zero, mul_one, zero_add]
      rw [uIcc_of_le (by norm_num), uIcc_of_le hY.le]
      exact ⟨left_mem_Icc.mpr (by norm_num), hy⟩
  -- edgewise continuity
  have hc1 : ∀ s : ℂ, (s ∈ (fun x : ℝ => (x : ℂ) + z₁.im * I) '' Icc (-1 / 2 : ℝ) (11 / 10) ∨
      s ∈ (fun x : ℝ => (x : ℂ) + z₂.im * I) '' Icc (-1 / 2 : ℝ) (11 / 10) ∨
      s ∈ (fun y : ℝ => (z₂.re : ℂ) + y * I) '' Icc t₀ Y ∨
      s ∈ (fun y : ℝ => (z₁.re : ℂ) + y * I) '' Icc t₀ Y) →
      ContinuousAt (fun z => H z * (deriv riemannZeta z / riemannZeta z)) s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hedge s hs
    exact continuousAt_mul_logDeriv_zeta (hHc s (hmem s hs)) h1 h2
  have hc2 : ∀ s : ℂ, (s ∈ (fun x : ℝ => (x : ℂ) + z₁.im * I) '' Icc (-1 / 2 : ℝ) (11 / 10) ∨
      s ∈ (fun x : ℝ => (x : ℂ) + z₂.im * I) '' Icc (-1 / 2 : ℝ) (11 / 10) ∨
      s ∈ (fun y : ℝ => (z₂.re : ℂ) + y * I) '' Icc t₀ Y ∨
      s ∈ (fun y : ℝ => (z₁.re : ℂ) + y * I) '' Icc t₀ Y) →
      ContinuousAt (fun z => H z * (z - 1)⁻¹) s := by
    intro s hs
    obtain ⟨h1, -⟩ := hedge s hs
    exact (hHc s (hmem s hs)).mul ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr h1))
  have hγ1 : Continuous fun x : ℝ => (x : ℂ) + z₁.im * I := by fun_prop
  have hγ2 : Continuous fun x : ℝ => (x : ℂ) + z₂.im * I := by fun_prop
  have hγ3 : Continuous fun y : ℝ => (z₂.re : ℂ) + y * I := by fun_prop
  have hγ4 : Continuous fun y : ℝ => (z₁.re : ℂ) + y * I := by fun_prop
  rw [hsplit, rectIntegral_add
    (intervalIntegrable_comp_of_continuousAt hγ1 fun x hx =>
      hc1 _ (Or.inl ⟨x, by rwa [hIcc1] at hx, rfl⟩))
    (intervalIntegrable_comp_of_continuousAt hγ1 fun x hx =>
      hc2 _ (Or.inl ⟨x, by rwa [hIcc1] at hx, rfl⟩))
    (intervalIntegrable_comp_of_continuousAt hγ2 fun x hx =>
      hc1 _ (Or.inr (Or.inl ⟨x, by rwa [hIcc1] at hx, rfl⟩)))
    (intervalIntegrable_comp_of_continuousAt hγ2 fun x hx =>
      hc2 _ (Or.inr (Or.inl ⟨x, by rwa [hIcc1] at hx, rfl⟩)))
    (intervalIntegrable_comp_of_continuousAt hγ3 fun y hy =>
      hc1 _ (Or.inr (Or.inr (Or.inl ⟨y, by rwa [hIcc2] at hy, rfl⟩))))
    (intervalIntegrable_comp_of_continuousAt hγ3 fun y hy =>
      hc2 _ (Or.inr (Or.inr (Or.inl ⟨y, by rwa [hIcc2] at hy, rfl⟩))))
    (intervalIntegrable_comp_of_continuousAt hγ4 fun y hy =>
      hc1 _ (Or.inr (Or.inr (Or.inr ⟨y, by rwa [hIcc2] at hy, rfl⟩))))
    (intervalIntegrable_comp_of_continuousAt hγ4 fun y hy =>
      hc2 _ (Or.inr (Or.inr (Or.inr ⟨y, by rwa [hIcc2] at hy, rfl⟩))))] at hcorp
  -- Cauchy for `H/(s − 1)`
  have hcauchy : rectIntegral (fun z => H z * (z - 1)⁻¹) z₁ z₂ = 0 := by
    refine rectIntegral_eq_zero_of_analyticOnNhd (U := U ∩ {s : ℂ | 0 < s.im}) ?_ ?_
    · intro s hs
      refine ⟨hsub' hs, ?_⟩
      rw [Complex.mem_reProdIm, h1im, h2im, uIcc_of_le hY.le] at hs
      show 0 < s.im
      linarith [hs.2.1]
    · intro s hs
      have hs1 : s ≠ 1 := ne_one_of_im_pos hs.2
      exact (hH s hs.1).mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hs1))
  rw [hcauchy, add_zero] at hcorp
  rw [← hcorp]

/-! ## The left edge of a conjugation-symmetric integrand -/

/-- For `f(−y) = conj f(y)`, `Re ∫_ℝ f = 2 Re (∫₀^{t₀} f + ∫_{t₀}^{Y} f + ∫_{y > Y} f)`. -/
theorem re_integral_eq_of_conj {f : ℝ → ℂ} (hf : Integrable f)
    (hconj : ∀ y, f (-y) = (starRingEnd ℂ) (f y)) {t₀ Y : ℝ} (h0 : 0 ≤ t₀) (hY : t₀ ≤ Y) :
    (∫ y, f y).re =
      2 * ((∫ y in (0 : ℝ)..t₀, f y).re + (∫ y in t₀..Y, f y).re + (∫ y in Ioi Y, f y).re) := by
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := 0) hf.integrableOn hf.integrableOn
  have hneg : ∫ y in Iic (0 : ℝ), f y = (starRingEnd ℂ) (∫ y in Ioi (0 : ℝ), f y) := by
    rw [← integral_conj, ← neg_zero, ← integral_comp_neg_Ioi]
    simp_rw [hconj]
    simp
  have hIoi : ∫ y in Ioi (0 : ℝ), f y =
      (∫ y in (0 : ℝ)..t₀, f y) + (∫ y in t₀..Y, f y) + ∫ y in Ioi Y, f y := by
    have hU : Ioi (0 : ℝ) = Ioc 0 Y ∪ Ioi Y := (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hf.integrableOn
      hf.integrableOn, ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_add_adjacent_intervals (b := t₀)
        (hf.intervalIntegrable) (hf.intervalIntegrable)]
  rw [← hsplit, hneg, Complex.add_re, Complex.conj_re, hIoi]
  simp only [Complex.add_re]
  ring

end

end RHTower.GaussZeroSum
