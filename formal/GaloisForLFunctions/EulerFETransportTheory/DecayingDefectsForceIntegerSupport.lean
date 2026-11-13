import GaloisForLFunctions.EulerFETransportTheory.DecayingDefectsVanishInTheUnitGap
import GaloisForLFunctions.EulerFETransportTheory.IntegrableDefectsForceIntegerSupport

/-!
# Decaying defects force integer support

For `‖g(t)‖ ≤ C (1 + |t|)^{-a}`, `a > 0`, the origin Fejér defect tends to zero
(`tendsto_integral_fejerDefectKernel_of_decay`), so every generalized-integer norm is a natural
number (`beurling_intNorm_nat_of_decaying_theta_defect`).

On the grid `δℤ`, `δ = 1/N`, the Fejér tent splits as
`(1 - |s|)₊ = Ψ + η(Λ_η(s - (1-η)) + Λ_η(s + (1-η))) + 2(1-η)Λ_{2η}(s) - (1-2η)Λ_η(s)`,
`η = R/N`, where `Ψ = Σ_j Ψ(jδ) Λ_δ(s - jδ)` has `Ψ(jδ) = 0` unless `η < |jδ| < 1 - η`
(`gridHat_eq_sum`, `fejerGrid_coeff_eq_zero`).  The `δ`-tents in `(η, 1 - η)` pair to zero in the
limit (unit-gap vanishing), the end tents carry weight `η`, and the two origin tents cost
`O(η^{1/2})` by double integration by parts.
-/

open Complex MeasureTheory Filter Topology Set Function
open RHTower.HamburgerStability
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ExactEventTheory
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-! ## Grid hats -/

/-- The hat of half-width `M` centred at `m`, `x ↦ (1 - |x - m|/M)₊`. -/
def gridHat (m M x : ℝ) : ℝ := max 0 (1 - |x - m| / M)

theorem continuous_gridHat (m M : ℝ) : Continuous (gridHat m M) := by
  unfold gridHat; fun_prop

theorem gridHat_eq_zero_of_le {m M x : ℝ} (hM : 0 < M) (h : M ≤ |x - m|) : gridHat m M x = 0 :=
  max_eq_left (by rw [sub_nonpos, le_div_iff₀ hM, one_mul]; exact h)

theorem unitTent_floor (x : ℝ) : unitTent (⌊x⌋ : ℝ) x = 1 - (x - ⌊x⌋) := by
  have h0 := Int.floor_le x
  have h1 := Int.lt_floor_add_one x
  rw [unitTent, abs_of_nonneg (by linarith)]
  exact max_eq_right (by linarith)

theorem unitTent_floor_add_one (x : ℝ) : unitTent ((⌊x⌋ + 1 : ℤ) : ℝ) x = x - ⌊x⌋ := by
  have h0 := Int.floor_le x
  have h1 := Int.lt_floor_add_one x
  push_cast
  rw [unitTent, abs_of_nonpos (by linarith)]
  rw [max_eq_right (by linarith)]
  ring

/-- The unit tent at `j` vanishes at `x` unless `j ∈ {⌊x⌋, ⌊x⌋ + 1}`. -/
theorem unitTent_eq_zero_of_ne {x : ℝ} {j : ℤ} (hj : j ≠ ⌊x⌋) (hj1 : j ≠ ⌊x⌋ + 1) :
    unitTent (j : ℝ) x = 0 := by
  have h0 := Int.floor_le x
  have h1 := Int.lt_floor_add_one x
  apply unitTent_eq_zero
  rcases lt_or_gt_of_ne hj with h | h
  · have : (j : ℝ) + 1 ≤ ⌊x⌋ := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith
  · have h' : ⌊x⌋ + 1 < j := lt_of_le_of_ne (by omega) (Ne.symm hj1)
    have h'' : ⌊x⌋ + 2 ≤ j := by omega
    have : (⌊x⌋ : ℝ) + 2 ≤ j := by exact_mod_cast h''
    rw [abs_of_nonpos (by linarith)]; linarith

/-- On the unit cell `[k, k+1]` a grid hat with integer centre and width is affine. -/
theorem gridHat_cell (m : ℤ) {M : ℕ} (hM : 1 ≤ M) (k : ℤ) {x : ℝ} (hx0 : (k : ℝ) ≤ x)
    (hx1 : x ≤ k + 1) :
    gridHat m M x = (1 - (x - k)) * gridHat m M k + (x - k) * gridHat m M ((k + 1 : ℤ) : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  push_cast
  unfold gridHat
  rcases le_or_gt (k + 1) (m - M) with h | h
  · -- the cell lies left of the support
    have h' : (k : ℝ) + 1 ≤ m - M := by exact_mod_cast h
    rw [max_eq_left, max_eq_left, max_eq_left]
    · ring
    all_goals
      rw [sub_nonpos, le_div_iff₀ hM0, one_mul]
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
  rcases le_or_gt (k + 1) m with h2 | h2
  · -- left flank `m - M ≤ k < k + 1 ≤ m`
    have hl : (m : ℝ) - M ≤ k := by
      have : m - M ≤ k := by omega
      exact_mod_cast this
    have hr : (k : ℝ) + 1 ≤ m := by exact_mod_cast h2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
      max_eq_right, max_eq_right, max_eq_right]
    · field_simp; ring
    all_goals
      rw [sub_nonneg, div_le_one hM0]; linarith
  rcases le_or_gt (m + M) k with h3 | h3
  · -- the cell lies right of the support
    have h' : (m : ℝ) + M ≤ k := by exact_mod_cast h3
    rw [max_eq_left, max_eq_left, max_eq_left]
    · ring
    all_goals
      rw [sub_nonpos, le_div_iff₀ hM0, one_mul]
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  · -- right flank `m ≤ k < k + 1 ≤ m + M`
    have hl : (m : ℝ) ≤ k := by
      have : m ≤ k := by omega
      exact_mod_cast this
    have hr : (k : ℝ) + 1 ≤ m + M := by
      have : k + 1 ≤ m + M := by omega
      exact_mod_cast this
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
      max_eq_right, max_eq_right, max_eq_right]
    · field_simp; ring
    all_goals
      rw [sub_nonneg, div_le_one hM0]; linarith

/-- **Grid interpolation of a hat**: for every finite set `S ⊇ [m - M, m + M]` of integers,
`(1 - |x - m|/M)₊ = Σ_{j ∈ S} (1 - |j - m|/M)₊ Λ(x - j)`. -/
theorem gridHat_eq_sum (m : ℤ) {M : ℕ} (hM : 1 ≤ M) {S : Finset ℤ}
    (hS : Finset.Icc (m - M) (m + M) ⊆ S) (x : ℝ) :
    gridHat m M x = ∑ j ∈ S, gridHat m M j * unitTent j x := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set k := ⌊x⌋ with hk
  have hzero : ∀ j : ℤ, j ∉ Finset.Icc (m - M) (m + M) → gridHat m M j = 0 := by
    intro j hj
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
    apply gridHat_eq_zero_of_le hM0
    rcases hj with h | h
    · have : (j : ℝ) + 1 ≤ m - M := by
        have : j + 1 ≤ m - M := by omega
        exact_mod_cast this
      rw [abs_of_nonpos (by linarith)]; linarith
    · have : (m : ℝ) + M + 1 ≤ j := by
        have : m + M + 1 ≤ j := by omega
        exact_mod_cast this
      rw [abs_of_nonneg (by linarith)]; linarith
  -- both sums equal the two-term sum over `{k, k + 1}`
  have hpair : ∑ j ∈ S ∪ {k, k + 1}, gridHat m M j * unitTent j x =
      ∑ j ∈ ({k, k + 1} : Finset ℤ), gridHat m M j * unitTent j x := by
    symm
    refine Finset.sum_subset Finset.subset_union_right fun j _ hj => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    rw [unitTent_eq_zero_of_ne hj.1 hj.2, mul_zero]
  have hS' : ∑ j ∈ S, gridHat m M j * unitTent j x =
      ∑ j ∈ S ∪ {k, k + 1}, gridHat m M j * unitTent j x := by
    refine Finset.sum_subset Finset.subset_union_left fun j hj hjS => ?_
    rw [hzero j fun h => hjS (hS h), zero_mul]
  rw [hS', hpair, Finset.sum_pair (by omega), hk, unitTent_floor, unitTent_floor_add_one,
    gridHat_cell m hM ⌊x⌋ (Int.floor_le x) (Int.lt_floor_add_one x).le]
  ring

/-! ## Hats against the defect -/

/-- `∫ Λ_w(s - c) φ(s) ds = ∫_{-1}^{1} w (1 - |u|) φ(c + w u) du`. -/
theorem integral_unitTent_scaled {φ : ℝ → ℝ} {w : ℝ} (hw : 0 < w) (n : ℝ) :
    ∫ s, unitTent n (s / w) * φ s = ∫ u in (-1 : ℝ)..1, w * (1 - |u|) * φ (w * (n + u)) := by
  set F : ℝ → ℝ := fun s => unitTent n (s / w) * φ s with hF
  have he (u : ℝ) : unitTent 0 u * φ (w * (n + u)) = F (w * (n + u)) := by
    simp only [hF, unitTent, sub_zero]
    congr 2
    rw [show w * (n + u) / w - n = u by field_simp; ring]
  have hcv : (∫ u, unitTent 0 u * φ (w * (n + u))) = w⁻¹ * ∫ s, F s := by
    calc _ = ∫ u, F (w * (n + u)) := integral_congr_ae (Eventually.of_forall he)
      _ = ∫ u, F (w * u) := integral_add_left_eq_self (fun u => F (w * u)) n
      _ = _ := by
        rw [Measure.integral_comp_mul_left]
        simp only [abs_of_pos (inv_pos.mpr hw), smul_eq_mul]
  symm
  calc _ = w * ∫ u in (-1 : ℝ)..1, (1 - |u|) * φ (w * (n + u)) := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr fun u _ => by ring
    _ = w * ∫ u, unitTent 0 u * φ (w * (n + u)) := by
        rw [intervalIntegral_window_eq_integral_unitTent]
    _ = w * (w⁻¹ * ∫ s, F s) := by rw [hcv]
    _ = ∫ s, F s := by rw [← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]

/-- The real part of the defect transform on the vertical line `Re τ = ε`. -/
def defectLine (g : ℝ → ℂ) (ε s : ℝ) : ℝ := (defectLaplace g ((ε : ℂ) + (s : ℂ) * I)).re

theorem continuous_defectLine {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) {ε : ℝ} (hε : 0 < ε) :
    Continuous (defectLine g ε) :=
  Complex.continuous_re.comp (continuous_defectLaplace_line hgm.aestronglyMeasurable hgb hε)

/-- A tent paired with the line `Re τ = ε` is a tent error:
`∫ Λ_w(s - c) Re J(ε + is) ds = T_{ε/w}(w, c)`. -/
theorem integral_unitTent_defectLine (g : ℝ → ℂ) {w ε : ℝ} (hw : 0 < w) (c : ℝ) :
    ∫ s, unitTent (c / w) (s / w) * defectLine g ε s = tentDefect g w c (ε / w) := by
  rw [integral_unitTent_scaled hw, tentDefect]
  refine intervalIntegral.integral_congr fun u _ => ?_
  have e1 : w * (ε / w) = ε := by field_simp
  have e2 : w * (c / w + u) = c + w * u := by field_simp
  rw [tentDefectKernel_div g w (ε / w) c u hw, defectLine, e1, e2]

/-- A rescaled unit tent times a continuous function is integrable (compact support). -/
theorem integrable_unitTent_mul {φ : ℝ → ℝ} (hφ : Continuous φ) {w : ℝ} (hw : 0 < w) (n : ℝ) :
    Integrable fun s => unitTent n (s / w) * φ s := by
  refine ((continuous_unitTent n).comp (continuous_id.div_const w) |>.mul hφ)
    |>.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := w * (n - 1)) (b := w * (n + 1))) fun s hs => ?_
  show unitTent n (s / w) * φ s = 0
  rw [unitTent_eq_zero, zero_mul]
  rw [mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with h | h
  · have : s / w < n - 1 := by rw [div_lt_iff₀ hw]; linarith
    rw [abs_of_neg (by linarith)]; linarith
  · have : n + 1 < s / w := by rw [lt_div_iff₀ hw]; linarith
    rw [abs_of_pos (by linarith)]; linarith

theorem gridHat_div {m M δ : ℝ} (hM : 0 < M) (hδ : 0 < δ) (s : ℝ) :
    gridHat m M (s / δ) = unitTent (m * δ / (M * δ)) (s / (M * δ)) := by
  unfold gridHat unitTent
  congr 2
  rw [show m * δ / (M * δ) = m / M by field_simp, show s / (M * δ) - m / M = (s / δ - m) / M by
    field_simp, abs_div, abs_of_pos hM]

theorem integrable_gridHat_mul {φ : ℝ → ℝ} (hφ : Continuous φ) {m M δ : ℝ} (hM : 0 < M)
    (hδ : 0 < δ) : Integrable fun s => gridHat m M (s / δ) * φ s := by
  simp only [gridHat_div hM hδ]
  exact integrable_unitTent_mul hφ (mul_pos hM hδ) _

/-- A grid hat paired with the line `Re τ = ε` is the tent error of width `Mδ` at `mδ`. -/
theorem integral_gridHat_defectLine (g : ℝ → ℂ) {m M δ : ℝ} (hM : 0 < M) (hδ : 0 < δ) (ε : ℝ) :
    ∫ s, gridHat m M (s / δ) * defectLine g ε s = tentDefect g (M * δ) (m * δ) (ε / (M * δ)) := by
  simp only [gridHat_div hM hδ]
  exact integral_unitTent_defectLine g (mul_pos hM hδ) _

/-- The grid coefficient `Ψ(j)` of the Fejér decomposition (in units `δ = 1/N`, `η = R/N`). -/
def fejerGridCoeff (N R x : ℝ) : ℝ :=
  gridHat 0 N x - R / N * (gridHat (N - R) R x + gridHat (-(N - R)) R x) -
    2 * (1 - R / N) * gridHat 0 (2 * R) x + (1 - 2 * R / N) * gridHat 0 R x

/-- `Ψ(j) = 0` near the origin. -/
theorem fejerGridCoeff_eq_zero_of_abs_le {N R x : ℝ} (hR : 0 < R) (hNR : 3 * R ≤ N)
    (hx : |x| ≤ R) : fejerGridCoeff N R x = 0 := by
  have hN : 0 < N := by linarith
  unfold fejerGridCoeff gridHat
  have h1 : max 0 (1 - |x - 0| / N) = 1 - |x| / N := by
    rw [sub_zero]; exact max_eq_right (by rw [sub_nonneg, div_le_one hN]; linarith)
  have h2 : max 0 (1 - |x - (N - R)| / R) = 0 := by
    refine max_eq_left ?_
    rw [sub_nonpos, le_div_iff₀ hR, one_mul, abs_sub_comm]
    have := abs_le.mp hx
    rw [abs_of_nonneg (by linarith)]; linarith
  have h3 : max 0 (1 - |x - -(N - R)| / R) = 0 := by
    refine max_eq_left ?_
    rw [sub_nonpos, le_div_iff₀ hR, one_mul]
    have := abs_le.mp hx
    rw [abs_of_nonneg (by linarith)]; linarith
  have h4 : max 0 (1 - |x - 0| / (2 * R)) = 1 - |x| / (2 * R) := by
    rw [sub_zero]; exact max_eq_right (by rw [sub_nonneg, div_le_one (by positivity)]; linarith)
  have h5 : max 0 (1 - |x - 0| / R) = 1 - |x| / R := by
    rw [sub_zero]; exact max_eq_right (by rw [sub_nonneg, div_le_one hR]; exact hx)
  rw [h1, h2, h3, h4, h5]
  field_simp
  ring

/-- `Ψ(j) = 0` near the right end. -/
theorem fejerGridCoeff_eq_zero_of_le {N R x : ℝ} (hR : 0 < R) (hNR : 3 * R ≤ N)
    (hx : N - R ≤ x) : fejerGridCoeff N R x = 0 := by
  have hN : 0 < N := by linarith
  unfold fejerGridCoeff gridHat
  have hx0 : 0 ≤ x := by linarith
  rcases le_or_gt x N with hxN | hxN
  · have h1 : max 0 (1 - |x - 0| / N) = 1 - x / N := by
      rw [sub_zero, abs_of_nonneg hx0]
      exact max_eq_right (by rw [sub_nonneg, div_le_one hN]; exact hxN)
    have h2 : max 0 (1 - |x - (N - R)| / R) = (N - x) / R := by
      rw [abs_of_nonneg (by linarith), max_eq_right]
      · field_simp; ring
      · rw [sub_nonneg, div_le_one hR]; linarith
    have h3 : max 0 (1 - |x - -(N - R)| / R) = 0 := by
      refine max_eq_left ?_
      rw [sub_nonpos, le_div_iff₀ hR, one_mul, abs_of_nonneg (by linarith)]; linarith
    have h4 : max 0 (1 - |x - 0| / (2 * R)) = 0 := by
      refine max_eq_left ?_
      rw [sub_nonpos, le_div_iff₀ (by positivity), one_mul, sub_zero, abs_of_nonneg hx0]; linarith
    have h5 : max 0 (1 - |x - 0| / R) = 0 := by
      refine max_eq_left ?_
      rw [sub_nonpos, le_div_iff₀ hR, one_mul, sub_zero, abs_of_nonneg hx0]; linarith
    rw [h1, h2, h3, h4, h5]
    field_simp
    ring
  · have z : ∀ {m M : ℝ}, 0 < M → M ≤ |x - m| → max 0 (1 - |x - m| / M) = 0 := fun hM h =>
      max_eq_left (by rw [sub_nonpos, le_div_iff₀ hM, one_mul]; exact h)
    rw [z hN (by rw [sub_zero, abs_of_nonneg hx0]; linarith),
      z hR (by rw [abs_of_nonneg (by linarith)]; linarith),
      z hR (by rw [abs_of_nonneg (by linarith)]; linarith),
      z (by positivity) (by rw [sub_zero, abs_of_nonneg hx0]; linarith),
      z hR (by rw [sub_zero, abs_of_nonneg hx0]; linarith)]
    ring

theorem fejerGridCoeff_neg (N R x : ℝ) : fejerGridCoeff N R (-x) = fejerGridCoeff N R x := by
  unfold fejerGridCoeff gridHat
  have e1 : |-x - (N - R)| = |x - -(N - R)| := by rw [← abs_neg]; ring_nf
  have e2 : |-x - -(N - R)| = |x - (N - R)| := by rw [← abs_neg]; ring_nf
  rw [e1, e2, sub_zero, sub_zero, abs_neg]
  ring

/-- `Ψ(j) = 0` unless `R < |j| < N - R`. -/
theorem fejerGridCoeff_eq_zero {N R x : ℝ} (hR : 0 < R) (hNR : 3 * R ≤ N)
    (hx : |x| ≤ R ∨ N - R ≤ |x|) : fejerGridCoeff N R x = 0 := by
  rcases hx with h | h
  · exact fejerGridCoeff_eq_zero_of_abs_le hR hNR h
  · rcases le_or_gt 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0] at h; exact fejerGridCoeff_eq_zero_of_le hR hNR h
    · rw [abs_of_neg hx0] at h
      rw [← neg_neg x, fejerGridCoeff_neg]
      exact fejerGridCoeff_eq_zero_of_le hR hNR h

/-- `Ψ` is the grid interpolation of its coefficients. -/
theorem fejerGrid_eq_sum {N R : ℕ} (hR : 1 ≤ R) (hNR : 3 * R ≤ N) (x : ℝ) :
    fejerGridCoeff N R x =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) N, fejerGridCoeff N R j * unitTent j x := by
  have hN : 1 ≤ N := by omega
  have hS0 : Finset.Icc ((0 : ℤ) - (N : ℕ)) (0 + (N : ℕ)) ⊆ Finset.Icc (-(N : ℤ)) N := by
    intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
  have hSR : Finset.Icc (((N : ℤ) - R) - (R : ℕ)) (((N : ℤ) - R) + (R : ℕ)) ⊆
      Finset.Icc (-(N : ℤ)) N := by
    intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
  have hSL : Finset.Icc ((-((N : ℤ) - R)) - (R : ℕ)) ((-((N : ℤ) - R)) + (R : ℕ)) ⊆
      Finset.Icc (-(N : ℤ)) N := by
    intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
  have hS2 : Finset.Icc ((0 : ℤ) - ((2 * R : ℕ) : ℕ)) (0 + ((2 * R : ℕ) : ℕ)) ⊆
      Finset.Icc (-(N : ℤ)) N := by
    intro j hj; simp only [Finset.mem_Icc] at hj ⊢; push_cast at hj; omega
  have hS1 : Finset.Icc ((0 : ℤ) - (R : ℕ)) (0 + (R : ℕ)) ⊆ Finset.Icc (-(N : ℤ)) N := by
    intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
  have e0 := gridHat_eq_sum 0 hN hS0 x
  have eR := gridHat_eq_sum ((N : ℤ) - R) hR hSR x
  have eL := gridHat_eq_sum (-((N : ℤ) - R)) hR hSL x
  have e2 := gridHat_eq_sum 0 (M := 2 * R) (by omega) hS2 x
  have e1 := gridHat_eq_sum 0 hR hS1 x
  push_cast at e0 eR eL e2 e1
  have hterm : ∀ j : ℤ, fejerGridCoeff N R j * unitTent j x =
      gridHat 0 N j * unitTent j x - R / N * (gridHat (N - R) R j * unitTent j x +
        gridHat (-(N - R)) R j * unitTent j x) - 2 * (1 - R / N) * (gridHat 0 (2 * R) j *
          unitTent j x) + (1 - 2 * R / N) * (gridHat 0 R j * unitTent j x) := fun j => by
    unfold fejerGridCoeff; ring
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold fejerGridCoeff
  rw [e0, eR, eL, e2, e1]

/-- **The Fejér decomposition** of the origin tent paired with the line `Re τ = ε`
(`δ = 1/N`, `η = R/N`). -/
theorem tentDefect_one_zero_eq {g : ℝ → ℂ} {Cg : ℝ} {N₀ : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N₀) {N R : ℕ} (hR : 1 ≤ R) (hNR : 3 * R ≤ N)
    {ε : ℝ} (hε : 0 < ε) :
    tentDefect g 1 0 ε =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) N, fejerGridCoeff N R j *
        tentDefect g (1 * (1 / N)) (j * (1 / N)) (ε / (1 * (1 / N))) +
      R / N * (tentDefect g (R * (1 / N)) ((N - R) * (1 / N)) (ε / (R * (1 / N))) +
        tentDefect g (R * (1 / N)) (-(N - R) * (1 / N)) (ε / (R * (1 / N)))) +
      2 * (1 - R / N) * tentDefect g (2 * R * (1 / N)) (0 * (1 / N)) (ε / (2 * R * (1 / N))) -
      (1 - 2 * R / N) * tentDefect g (R * (1 / N)) (0 * (1 / N)) (ε / (R * (1 / N))) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  set δ : ℝ := 1 / N with hδdef
  have hδ : 0 < δ := by positivity
  set φ := defectLine g ε with hφ
  have hφc : Continuous φ := continuous_defectLine hgm hgb hε
  -- the origin tent in grid units
  have hF : ∀ s, unitTent (0 / 1) (s / 1) = gridHat 0 N (s / δ) := by
    intro s
    unfold unitTent gridHat
    have e : |s / δ - 0| / N = |s / 1 - 0 / 1| := by
      rw [sub_zero, div_one, zero_div, sub_zero, hδdef, div_div_eq_mul_div, div_one, abs_mul,
        abs_of_pos hN, mul_div_cancel_right₀ _ hN.ne']
    rw [e]
  have hpt : ∀ s, gridHat 0 N (s / δ) * φ s =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) N, fejerGridCoeff N R j * (gridHat j 1 (s / δ) * φ s) +
      R / N * (gridHat (N - R) R (s / δ) * φ s + gridHat (-(N - R)) R (s / δ) * φ s) +
      2 * (1 - R / N) * (gridHat 0 (2 * R) (s / δ) * φ s) -
      (1 - 2 * R / N) * (gridHat 0 R (s / δ) * φ s) := by
    intro s
    have hut : ∀ j : ℤ, unitTent j (s / δ) = gridHat j 1 (s / δ) := fun j => by
      unfold unitTent gridHat; rw [div_one]
    have hsum := fejerGrid_eq_sum hR hNR (s / δ)
    simp only [hut] at hsum
    have hdef : gridHat 0 N (s / δ) = fejerGridCoeff N R (s / δ) +
        R / N * (gridHat (N - R) R (s / δ) + gridHat (-(N - R)) R (s / δ)) +
        2 * (1 - R / N) * gridHat 0 (2 * R) (s / δ) - (1 - 2 * R / N) * gridHat 0 R (s / δ) := by
      unfold fejerGridCoeff; ring
    rw [hdef, hsum]
    simp only [add_mul, sub_mul, Finset.sum_mul, mul_assoc]
  have i1 : ∀ (m : ℝ) {M : ℝ}, 0 < M → Integrable fun s => gridHat m M (s / δ) * φ s :=
    fun m M hM => integrable_gridHat_mul hφc hM hδ
  have iS : Integrable fun s => ∑ j ∈ Finset.Icc (-(N : ℤ)) N,
      fejerGridCoeff N R j * (gridHat j 1 (s / δ) * φ s) :=
    integrable_finsetSum _ fun (j : ℤ) _ =>
      (i1 (j : ℝ) one_pos).const_mul (fejerGridCoeff N R j)
  have iE : Integrable fun s => R / N * (gridHat (N - R) R (s / δ) * φ s +
      gridHat (-(N - R)) R (s / δ) * φ s) := ((i1 _ hR0).add (i1 _ hR0)).const_mul _
  have iO2 : Integrable fun s => 2 * (1 - R / N) * (gridHat 0 (2 * R) (s / δ) * φ s) :=
    (i1 0 (by positivity)).const_mul _
  have iO1 : Integrable fun s => (1 - 2 * R / N) * (gridHat 0 R (s / δ) * φ s) :=
    (i1 0 hR0).const_mul _
  rw [show tentDefect g 1 0 ε = tentDefect g 1 0 (ε / 1) by rw [div_one],
    ← integral_unitTent_defectLine g one_pos 0]
  simp only [hF]
  have iSE : Integrable fun s => ∑ j ∈ Finset.Icc (-(N : ℤ)) N,
      fejerGridCoeff N R j * (gridHat j 1 (s / δ) * φ s) +
      R / N * (gridHat (N - R) R (s / δ) * φ s + gridHat (-(N - R)) R (s / δ) * φ s) :=
    iS.add iE
  have iSEO : Integrable fun s => ∑ j ∈ Finset.Icc (-(N : ℤ)) N,
      fejerGridCoeff N R j * (gridHat j 1 (s / δ) * φ s) +
      R / N * (gridHat (N - R) R (s / δ) * φ s + gridHat (-(N - R)) R (s / δ) * φ s) +
      2 * (1 - R / N) * (gridHat 0 (2 * R) (s / δ) * φ s) := iSE.add iO2
  have iEE : Integrable fun s => gridHat (N - R) R (s / δ) * φ s +
      gridHat (-(N - R)) R (s / δ) * φ s := (i1 _ hR0).add (i1 _ hR0)
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub iSEO iO1,
    integral_add iSE iO2, integral_add iS iE, integral_finsetSum _
      fun (j : ℤ) _ => (i1 (j : ℝ) one_pos).const_mul (fejerGridCoeff N R j), integral_const_mul,
    integral_const_mul,
    integral_const_mul, integral_add (i1 _ hR0) (i1 _ hR0)]
  simp only [hφ]
  rw [integral_gridHat_defectLine g (m := ((N : ℝ) - R)) hR0 hδ,
    integral_gridHat_defectLine g (m := -((N : ℝ) - R)) hR0 hδ,
    integral_gridHat_defectLine g (m := 0) (M := 2 * R) (by positivity) hδ,
    integral_gridHat_defectLine g (m := 0) hR0 hδ]
  congr 3
  exact Finset.sum_congr rfl fun j _ => by
    rw [integral_const_mul, integral_gridHat_defectLine g (m := (j : ℝ)) one_pos hδ]

/-! ## The origin Fejér defect vanishes -/

/-- Tent errors are even in the centre (the theta law makes `Re J` even on vertical lines). -/
theorem tentDefect_neg_center {ν : Measure ℝ} (hsupp : ν (Iio 1) = 0)
    (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : Measurable g) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -(β : ℂ) +
        (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {w ε : ℝ} (hw : 0 < w) (hε : 0 < ε) (c : ℝ) :
    tentDefect g w (-c) ε = tentDefect g w c ε := by
  unfold tentDefect
  simp only [tentDefectKernel_div g w ε _ _ hw]
  have hF := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (fun s : ℝ => w * (1 - |s|) *
      (defectLaplace g (((w * ε : ℝ) : ℂ) + ((c + w * s : ℝ) : ℂ) * I)).re)
  simp only [neg_neg] at hF
  rw [← hF]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [abs_neg]
  rw [show c + w * -u = -(-c + w * u) by ring,
    defectLaplace_re_neg_of_theta_defect hsupp hmom hgm hgb hθ (mul_pos hw hε) (-c + w * u)]

theorem tendsto_div_nhdsGT {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ => ε / δ) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun ε hε =>
    div_pos hε hδ⟩
  simpa using ((continuous_id.div_const δ).tendsto 0).mono_left nhdsWithin_le_nhds

/-- The triangle inequality for the five pieces of the decomposition. -/
theorem abs_fejer_combo_le (S T₁ T₂ O₂ O₁ : ℝ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : 2 * η ≤ 1) :
    |S + η * (T₁ + T₂) + 2 * (1 - η) * O₂ - (1 - 2 * η) * O₁| ≤
      |S| + η * (|T₁| + |T₂|) + 2 * |O₂| + |O₁| := by
  have h1 := abs_add_le T₁ T₂
  have h2 : |η * (T₁ + T₂)| = η * |T₁ + T₂| := by rw [abs_mul, abs_of_nonneg hη0]
  have h3 : |2 * (1 - η) * O₂| ≤ 2 * |O₂| := by
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (by linarith)]
    nlinarith [abs_nonneg O₂]
  have h4 : |(1 - 2 * η) * O₁| ≤ |O₁| := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    nlinarith [abs_nonneg O₁]
  have hA := abs_add_le (S + η * (T₁ + T₂)) (2 * (1 - η) * O₂)
  have hB := abs_add_le S (η * (T₁ + T₂))
  have hC := abs_sub (S + η * (T₁ + T₂) + 2 * (1 - η) * O₂) ((1 - 2 * η) * O₁)
  nlinarith [mul_le_mul_of_nonneg_left h1 hη0]

/-- The grid terms of the decomposition vanish in the limit when the tents of width `δ` have no
error at the centres in `[η, 1 - η]`. -/
theorem tendsto_fejer_grid_term (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N₀ : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N₀)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {N R : ℕ} (hR1 : 1 ≤ R) (hNR : 3 * R ≤ N) {η : ℝ} (hRN : (R : ℝ) * (1 / N) = η)
    (hgap : ∀ y ∈ Icc η (1 - η), tentRecurrentPart B.intNorm β (1 / N) y = 0 ∧
      tentAtomMass B.intNorm (1 / N) y = 0) (j : ℤ) :
    Tendsto (fun ε => fejerGridCoeff N R j *
      tentDefect g (1 * (1 / N)) (j * (1 / N)) (ε / (1 * (1 / N)))) (𝓝[>] 0) (𝓝 0) := by
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp
    (integrable_rpow_beurlingSystemIntegerMeasure B hBsum)
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hδ0 : (0 : ℝ) < 1 / N := by positivity
  by_cases hj : |(j : ℝ)| ≤ R ∨ (N : ℝ) - R ≤ |(j : ℝ)|
  · simp only [fejerGridCoeff_eq_zero hR0 (by exact_mod_cast hNR) hj, zero_mul]
    exact tendsto_const_nhds
  push Not at hj
  have hy1 : η ≤ |(j : ℝ)| * (1 / N) := by
    rw [← hRN]; exact mul_le_mul_of_nonneg_right hj.1.le hδ0.le
  have hy2 : |(j : ℝ)| * (1 / N) ≤ 1 - η := by
    rw [← hRN]
    have h1 : (N : ℝ) * (1 / N) = 1 := by field_simp
    have := mul_le_mul_of_nonneg_right hj.2.le hδ0.le
    rw [sub_mul, h1] at this
    exact this
  have hj2 : 2 ≤ |(j : ℝ)| := by
    have hjint : (R : ℤ) < |j| := by
      have : (R : ℝ) < ((|j| : ℤ) : ℝ) := by push_cast; exact hj.1
      exact_mod_cast this
    have : (2 : ℤ) ≤ |j| := by omega
    exact_mod_cast this
  have hEz := hgap _ ⟨hy1, hy2⟩
  have hT : Tendsto (fun ε => tentDefect g (1 / N) (|(j : ℝ)| * (1 / N)) (ε / (1 / N)))
      (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_tentDefect B hBsum hgm hgb hθ hδ0
      (div_le_one_of_le₀ hN1 hN0.le) (show 1 / (N : ℝ) < |(j : ℝ)| * (1 / N) by nlinarith)).comp
      (tendsto_div_nhdsGT hδ0)
    rwa [hEz.1, hEz.2, sub_zero] at this
  have hsym : ∀ ε, 0 < ε → tentDefect g (1 * (1 / N)) (j * (1 / N)) (ε / (1 * (1 / N))) =
      tentDefect g (1 / N) (|(j : ℝ)| * (1 / N)) (ε / (1 / N)) := by
    intro ε hε
    rw [one_mul]
    rcases le_or_gt 0 (j : ℝ) with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0, neg_mul, tentDefect_neg_center hsupp hmom hgm hgb hθ hδ0
        (div_pos hε hδ0)]
  have := hT.const_mul (fejerGridCoeff N R j)
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hsym ε hε]

/-- **The origin Fejér defect vanishes**: `T_ε(1, 0) → 0` as `ε → 0⁺`. -/
theorem tendsto_tentDefect_one_zero_of_decay (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    Tendsto (fun ε => tentDefect g 1 0 ε) (𝓝[>] 0) (𝓝 0) := by
  have hgb := poly_of_decay ha.le hgd
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp
    (integrable_rpow_beurlingSystemIntegerMeasure B hBsum)
  obtain ⟨K₀, hK₀, horig⟩ := exists_abs_tentDefect_origin_le hgm ha hgd
  obtain ⟨K, ρ, hK, hρ, hsmall⟩ := exists_abs_tentDefect_le_smallWidth hgm ha hgd
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = K * ((1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) + 1) := ⟨_, rfl⟩
  -- the cost of the end and origin tents at scale `η`
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ → ℝ, Bd = fun η => η * (2 * (K₁ * η ^ ρ)) +
      2 * (K₀ * (2 * η) ^ (1 / 2 : ℝ)) + K₀ * η ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hBlim : Tendsto Bd (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous Bd := by
      rw [hBd]
      exact ((continuous_id.mul (continuous_const.mul (continuous_const.mul
        (continuous_id.rpow_const fun _ => Or.inr hρ.le)))).add
        (continuous_const.mul (continuous_const.mul ((continuous_const.mul continuous_id).rpow_const
          fun _ => Or.inr (by norm_num))))).add
        (continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr (by norm_num)))
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [hBd, Real.zero_rpow hρ.ne'] using this
  rw [Metric.tendsto_nhds]
  intro θ hθpos
  -- choose `η = 1/M`
  have hMlim : Tendsto (fun M : ℕ => (1 : ℝ) / ((M : ℝ) + 8)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 8 tendsto_natCast_atTop_atTop),
      Eventually.of_forall fun M => show (0 : ℝ) < 1 / ((M : ℝ) + 8) by positivity⟩
  obtain ⟨M', hM'⟩ := ((hBlim.comp hMlim).eventually (gt_mem_nhds (half_pos hθpos))).exists
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 1 / ((M' : ℝ) + 8) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hη8 : η ≤ 1 / 8 := by
    rw [hηdef]; exact one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg M' : (0 : ℝ) ≤ M')])
  have hBη : Bd η < θ / 2 := by rw [hηdef]; exact hM'
  -- choose `δ = 1/(M R)` in the unit-gap regime
  have hgap := eventually_tentRecurrentPart_eq_zero_of_decay B hBsum hgm ha hgd hθ hη0
    (by linarith)
  have hRlim : Tendsto (fun R : ℕ => (1 : ℝ) / ((((M' + 8 : ℕ) * (R + 1) : ℕ) : ℝ))) atTop
      (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.div_atTop ?_,
      Eventually.of_forall fun R => show (0 : ℝ) < 1 / (((M' + 8 : ℕ) * (R + 1) : ℕ) : ℝ) by
        positivity⟩
    refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop_atTop.mpr fun b => ⟨b, fun R hR => ?_⟩)
    nlinarith
  obtain ⟨R', hR'⟩ := (hRlim.eventually hgap).exists
  have hR1 : 1 ≤ R' + 1 := by omega
  have hNR : 3 * (R' + 1) ≤ (M' + 8) * (R' + 1) := by nlinarith
  have hRN : ((R' + 1 : ℕ) : ℝ) * (1 / (((M' + 8) * (R' + 1) : ℕ) : ℝ)) = η := by
    rw [hηdef]; push_cast; field_simp
  have hRN' : ((R' + 1 : ℕ) : ℝ) / (((M' + 8) * (R' + 1) : ℕ) : ℝ) = η := by
    rw [← hRN]; ring
  have hsum := tendsto_finsetSum (Finset.Icc (-(((M' + 8) * (R' + 1) : ℕ) : ℤ))
    (((M' + 8) * (R' + 1) : ℕ) : ℤ)) fun j _ =>
    tendsto_fejer_grid_term B hBsum hgm hgb hθ hR1 hNR hRN hR' j
  rw [Finset.sum_const_zero] at hsum
  filter_upwards [hsum.eventually (Metric.ball_mem_nhds 0 (half_pos hθpos)),
    Ioo_mem_nhdsGT hη0] with ε hεs hε
  have hε0 : 0 < ε := hε.1
  rw [Real.dist_eq, sub_zero] at hεs ⊢
  rw [tentDefect_one_zero_eq hgm hgb hR1 hNR hε0, hRN', mul_div_assoc, hRN', hRN,
    show (2 : ℝ) * ((R' + 1 : ℕ) : ℝ) * (1 / (((M' + 8) * (R' + 1) : ℕ) : ℝ)) = 2 * η by
      rw [mul_assoc, hRN],
    show (((((M' + 8) * (R' + 1) : ℕ) : ℝ) - ((R' + 1 : ℕ) : ℝ)) *
      (1 / (((M' + 8) * (R' + 1) : ℕ) : ℝ))) = 1 - η by
      rw [sub_mul, hRN]; field_simp,
    show (-((((M' + 8) * (R' + 1) : ℕ) : ℝ) - ((R' + 1 : ℕ) : ℝ)) *
      (1 / (((M' + 8) * (R' + 1) : ℕ) : ℝ))) = -(1 - η) by
      rw [neg_mul, sub_mul, hRN]; field_simp,
    zero_mul]
  -- end and origin tents
  have hend : |tentDefect g η (1 - η) (ε / η)| ≤ K₁ * η ^ ρ := by
    rw [hK₁]
    exact hsmall (1 / 4) η (1 - η) (ε / η) hη0 (by linarith) (by linarith) (by linarith)
      (by linarith) (div_pos hε0 hη0) (by rw [div_le_one hη0]; exact hε.2.le)
  have hend' : |tentDefect g η (-(1 - η)) (ε / η)| ≤ K₁ * η ^ ρ := by
    rw [tentDefect_neg_center hsupp hmom hgm hgb hθ hη0 (div_pos hε0 hη0)]; exact hend
  have ho2 := horig (2 * η) (ε / (2 * η)) (by positivity) (by positivity)
    (by rw [div_le_one (by positivity)]; linarith [hε.2])
  have ho1 := horig η (ε / η) hη0 (div_pos hε0 hη0) (by rw [div_le_one hη0]; exact hε.2.le)
  refine (abs_fejer_combo_le _ _ _ _ _ hη0.le (by linarith)).trans_lt ?_
  have hBη' : Bd η = η * (2 * (K₁ * η ^ ρ)) + 2 * (K₀ * (2 * η) ^ (1 / 2 : ℝ)) +
      K₀ * η ^ (1 / 2 : ℝ) := by rw [hBd]
  have : η * (|tentDefect g η (1 - η) (ε / η)| + |tentDefect g η (-(1 - η)) (ε / η)|) ≤
      η * (2 * (K₁ * η ^ ρ)) := by
    gcongr; linarith
  linarith

/-! ## Integer support -/

theorem integral_fejerDefectKernel_eq (g : ℝ → ℂ) (ε : ℝ) :
    ∫ s in (-1 : ℝ)..1, fejerDefectKernel g ε s = 2 * tentDefect g 1 0 ε := by
  rw [tentDefect, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have h := tentDefectKernel_div g 1 ε 0 s one_pos
  rw [h, fejerDefectKernel]
  simp only [one_mul, zero_add]
  ring

/-- **The origin Fejér defect vanishes** in the form of the Fejér pairing. -/
theorem beurling_tendsto_integral_fejerDefectKernel_of_decay (B : RHTower.BeurlingSystem)
    [Countable B.Label] (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    Tendsto (fun ε : ℝ => ∫ s in (-1 : ℝ)..1, fejerDefectKernel g ε s) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_tentDefect_one_zero_of_decay B hBsum hgm ha hgd hθ).const_mul 2
  rw [mul_zero] at h
  exact h.congr fun ε => (integral_fejerDefectKernel_eq g ε).symm

/-- The Fourier weight of the origin tent has zero mass for every decaying Beurling defect. -/
theorem beurling_integral_sinc_sq_eq_zero_of_decay (B : RHTower.BeurlingSystem)
    [Countable B.Label] (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    ∫ u : ℝ, (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂beurlingSystemIntegerMeasure B = 0 := by
  let ν := beurlingSystemIntegerMeasure B
  have hgb := poly_of_decay ha.le hgd
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp
    (integrable_rpow_beurlingSystemIntegerMeasure B hBsum)
  have hD (ε : ℝ) :
      (∫ u : ℝ, (∫ s in (-1 : ℝ)..1, tentDualKernel 1 0 ε s u) ∂ν) =
        ∫ u : ℝ, Real.exp (-2 * Real.pi * u * ε) *
          (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    rw [intervalIntegral_tentDualKernel zero_lt_one (zero_lt_one.trans_le hu)]
    simp only [one_mul, mul_zero, Real.cos_zero, tentFourierWeight]
  have hdual := (tendsto_integral_tentDualKernel hsupp hmom (h := 1) zero_lt_one 0).const_mul 2
  simp only [one_mul, mul_zero, Real.cos_zero, tentFourierWeight] at hdual
  have hdual' := hdual.congr' (Eventually.of_forall fun ε => congrArg (fun r : ℝ => 2 * r) (hD ε))
  have hright := ((tendsto_integral_fejerSeriesKernel_zero hsupp hmom).sub
    (tendsto_integral_fejerPolarKernel_neg (β : ℂ))).sub
      (beurling_tendsto_integral_fejerDefectKernel_of_decay B hBsum hgm ha hgd hθ)
  simp only [sub_zero] at hright
  have hzero : Tendsto (fun ε : ℝ => 2 * ∫ u : ℝ,
      Real.exp (-2 * Real.pi * u * ε) * (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν)
      (𝓝[>] 0) (𝓝 0) := by
    apply hright.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    exact (fejer_pairing_identity_of_theta_defect hsupp hmom hgm hgb hθ hε.1 hε.2.le).symm
  have he := tendsto_nhds_unique hdual' hzero
  linarith only [he]

/-- **Decaying theta defects force natural-number norms.** -/
theorem beurling_intNorm_nat_of_decaying_theta_defect (B : RHTower.BeurlingSystem)
    [Countable B.Label] (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    ∀ x : B.Integer, ∃ k : ℕ, B.intNorm x = k := by
  have hsum : Summable fun i : B.Integer =>
      (Real.sin (Real.pi * B.intNorm i) / (Real.pi * B.intNorm i)) ^ 2 := by
    refine (summable_norm_tentFourierCoefficient B.intNorm_pos (summable_beurling_inv_sq B hBsum)
      (h := 1) zero_lt_one).congr fun i => ?_
    simp only [tentFourierWeight, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (sq_nonneg _)
  have hz := beurling_integral_sinc_sq_eq_zero_of_decay B hBsum hgm ha hgd hθ
  rw [integral_beurlingSystemIntegerMeasure_eq_tsum] at hz
  intro x
  have ht := hsum.le_tsum x (fun _ _ => sq_nonneg _)
  rw [hz] at ht
  have hr := abs_sub_round_le_of_sinc_sq_le (B.one_le_intNorm x) ht
  simp only [mul_zero, Real.sqrt_zero, zero_mul] at hr
  have he : B.intNorm x = (round (B.intNorm x) : ℝ) :=
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hr (abs_nonneg _)))
  have hnonneg : (0 : ℤ) ≤ round (B.intNorm x) := by
    have hreal : (0 : ℝ) ≤ (round (B.intNorm x) : ℝ) := he ▸ (B.intNorm_pos x).le
    exact_mod_cast hreal
  refine ⟨(round (B.intNorm x)).toNat, ?_⟩
  have hm := congrArg (fun k : ℤ => (k : ℝ)) (Int.toNat_of_nonneg hnonneg)
  push_cast at hm
  exact he.trans hm.symm

end GaloisForLFunctions.EulerFETransportTheory
