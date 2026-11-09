import GaloisForLFunctions.SurfaceOfSpecZ.OnlyDeepOrdinatesNeedSeparation

/-!
# Chart-uniform windows for separated ordinates

The scale beyond which windows see an impure configuration with separated off-line ordinates is
explicit in three numbers of the configuration: the depth `x = Re ρ₁ − ½ > 0` and the coefficient
`|D_{ρ₁ − ½}|` of one zero off the line, and the mass `A = Σ |D_z|`. For `ℓ ≥ 40/δ`, an integer
`M ≥ 2ℓ` and every `a ≥ 0` with

`3(|K| + 1) e^{ℓ/2} + 3A e^{ℓ} < |D_{ρ₁ − ½}| e^{xa}`,

the window `[a, a + (M + 1)ℓ]` contains a scale with `2 Re S(u) < −K`
(`exists_lt_in_window_of_chart`).

The dominant depth is monotone in the scale (`re_le_re_of_dominant`), with values in `[−½, ½]`.
Among the `M` consecutive subwindows `[a + jℓ, a + (j + 2)ℓ]` one therefore has depth increment
`≤ 2/M ≤ 1/ℓ` (`exists_small_depth_increment`); there the weights drift by at most `e`
(`expWeight_drift_le_of_increment`) and Landau's inequality applies. No convergence of the dominant
depth is used, so the threshold depends on the chart `(x, |D|, A, δ, K)` only.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

variable {Z : ZeroConfig}

/-- **The dominant depth is monotone.** An exponent of maximal weight at a later scale is at least
as deep. -/
theorem re_le_re_of_dominant {u u' : ℝ} (huu' : u < u') {z z' : ℂ}
    (hz : evenCoeff Z (boxSpline 1 3) z ≠ 0) (hz' : evenCoeff Z (boxSpline 1 3) z' ≠ 0)
    (h : expWeight Z u z' ≤ expWeight Z u z) (h' : expWeight Z u' z ≤ expWeight Z u' z') :
    z.re ≤ z'.re := by
  by_contra hlt
  push Not at hlt
  have hD : 0 < ‖evenCoeff Z (boxSpline 1 3) z‖ := norm_pos_iff.mpr hz
  have hD' : 0 < ‖evenCoeff Z (boxSpline 1 3) z'‖ := norm_pos_iff.mpr hz'
  -- multiply the two dominance relations
  have e1 : expWeight Z u' z = expWeight Z u z * Real.exp (z.re * (u' - u)) := by
    rw [← expWeight_add]; congr 1; ring
  have e2 : expWeight Z u' z' = expWeight Z u z' * Real.exp (z'.re * (u' - u)) := by
    rw [← expWeight_add]; congr 1; ring
  rw [e1, e2] at h'
  have hlt' : Real.exp (z'.re * (u' - u)) < Real.exp (z.re * (u' - u)) :=
    Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right hlt (by linarith))
  have hw : 0 < expWeight Z u z := mul_pos hD (Real.exp_pos _)
  have hw' : 0 < expWeight Z u z' := mul_pos hD' (Real.exp_pos _)
  have h1 : expWeight Z u z' * Real.exp (z'.re * (u' - u)) <
      expWeight Z u z * Real.exp (z.re * (u' - u)) :=
    calc expWeight Z u z' * Real.exp (z'.re * (u' - u))
        < expWeight Z u z' * Real.exp (z.re * (u' - u)) := mul_lt_mul_of_pos_left hlt' hw'
      _ ≤ expWeight Z u z * Real.exp (z.re * (u' - u)) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  linarith

/-- **Drift on a window, from the depth increment.** If the dominant exponents at `u₀ − ℓ`, `u₀`,
`u₀ + ℓ` have depths within `η` of that at `u₀`, no weight exceeds `e^{ηℓ}` times the dominant one
on the window. -/
theorem expWeight_drift_le_of_increment {η ℓ u₀ : ℝ} (hℓ : 0 ≤ ℓ) {z₀ z₁ z₂ : ℂ}
    (h₀ : ∀ z', expWeight Z u₀ z' ≤ expWeight Z u₀ z₀)
    (h₁ : ∀ z', expWeight Z (u₀ + ℓ) z' ≤ expWeight Z (u₀ + ℓ) z₁) (hA : z₁.re - z₀.re ≤ η)
    (h₂ : ∀ z', expWeight Z (u₀ + -ℓ) z' ≤ expWeight Z (u₀ + -ℓ) z₂) (hB : z₀.re - z₂.re ≤ η)
    (z : ℂ) :
    expWeight Z u₀ z * Real.exp (|z.re - z₀.re| * ℓ) ≤ Real.exp (η * ℓ) * expWeight Z u₀ z₀ := by
  have hw0 := expWeight_nonneg (Z := Z) u₀ z₀
  rcases le_or_gt z₀.re z.re with h | h
  · rw [abs_of_nonneg (by linarith)]
    have e : expWeight Z u₀ z * Real.exp ((z.re - z₀.re) * ℓ) =
        expWeight Z (u₀ + ℓ) z * Real.exp (-z₀.re * ℓ) := by
      rw [expWeight_add, mul_assoc, ← Real.exp_add]; ring_nf
    have e1 : expWeight Z (u₀ + ℓ) z₁ * Real.exp (-z₀.re * ℓ) =
        expWeight Z u₀ z₁ * Real.exp ((z₁.re - z₀.re) * ℓ) := by
      rw [expWeight_add, mul_assoc, ← Real.exp_add]; ring_nf
    calc expWeight Z u₀ z * Real.exp ((z.re - z₀.re) * ℓ)
        = expWeight Z (u₀ + ℓ) z * Real.exp (-z₀.re * ℓ) := e
      _ ≤ expWeight Z (u₀ + ℓ) z₁ * Real.exp (-z₀.re * ℓ) :=
          mul_le_mul_of_nonneg_right (h₁ z) (Real.exp_pos _).le
      _ = expWeight Z u₀ z₁ * Real.exp ((z₁.re - z₀.re) * ℓ) := e1
      _ ≤ expWeight Z u₀ z₀ * Real.exp (η * ℓ) :=
          mul_le_mul (h₀ z₁) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA hℓ))
            (Real.exp_pos _).le hw0
      _ = Real.exp (η * ℓ) * expWeight Z u₀ z₀ := by ring
  · rw [abs_of_neg (by linarith)]
    have e : expWeight Z u₀ z * Real.exp (-(z.re - z₀.re) * ℓ) =
        expWeight Z (u₀ + -ℓ) z * Real.exp (z₀.re * ℓ) := by
      rw [expWeight_add, mul_assoc, ← Real.exp_add]; ring_nf
    have e2 : expWeight Z (u₀ + -ℓ) z₂ * Real.exp (z₀.re * ℓ) =
        expWeight Z u₀ z₂ * Real.exp ((z₀.re - z₂.re) * ℓ) := by
      rw [expWeight_add, mul_assoc, ← Real.exp_add]; ring_nf
    calc expWeight Z u₀ z * Real.exp (-(z.re - z₀.re) * ℓ)
        = expWeight Z (u₀ + -ℓ) z * Real.exp (z₀.re * ℓ) := e
      _ ≤ expWeight Z (u₀ + -ℓ) z₂ * Real.exp (z₀.re * ℓ) :=
          mul_le_mul_of_nonneg_right (h₂ z) (Real.exp_pos _).le
      _ = expWeight Z u₀ z₂ * Real.exp ((z₀.re - z₂.re) * ℓ) := e2
      _ ≤ expWeight Z u₀ z₀ * Real.exp (η * ℓ) :=
          mul_le_mul (h₀ z₂) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hB hℓ))
            (Real.exp_pos _).le hw0
      _ = Real.exp (η * ℓ) * expWeight Z u₀ z₀ := by ring

/-- **Pigeonhole for a bounded monotone sequence.** If `d` is nondecreasing with values in
`[−½, ½]`, some `j < M` has `d(j + 2) − d(j) ≤ 2/M`. -/
theorem exists_small_depth_increment {d : ℕ → ℝ} (hd : ∀ j, |d j| ≤ 1 / 2) {M : ℕ}
    (hM : 0 < M) : ∃ j < M, d (j + 2) - d j ≤ 2 / M := by
  by_contra h
  push Not at h
  have hsum : ∑ j ∈ Finset.range M, (d (j + 2) - d j) = (d (M + 1) - d 1) + (d M - d 0) := by
    have h1 := Finset.sum_range_sub (fun i => d (i + 1)) M
    have h2 := Finset.sum_range_sub d M
    simp only [zero_add] at h1
    rw [← h1, ← h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlt : ∑ _j ∈ Finset.range M, (2 / (M : ℝ)) < ∑ j ∈ Finset.range M, (d (j + 2) - d j) :=
    Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hM.ne')
      fun j hj => h j (Finset.mem_range.mp hj)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hM.ne'), hsum] at hlt
  have b1 := abs_le.mp (hd (M + 1))
  have b2 := abs_le.mp (hd 1)
  have b3 := abs_le.mp (hd M)
  have b4 := abs_le.mp (hd 0)
  linarith [b1.2, b2.1, b3.2, b4.1]

/-- **Chart-uniform windows.** Let `Z` be tempered, without real zeros, with `δ`-separated
ordinates off the line, and `ρ₁` a zero with `Re ρ₁ > ½`. Let `ℓ ≥ 40/δ` and `M ≥ 2ℓ`. For every
`a ≥ 0` with `3(|K| + 1)e^{ℓ/2} + 3(Σ|D_z|)e^{ℓ} < |D_{ρ₁ − ½}| e^{(Re ρ₁ − ½)a}`, the window
`[a, a + (M + 1)ℓ]` contains a scale with `2 Re S(u) < −K`. -/
theorem exists_lt_in_window_of_chart (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hsep : DeepSeparatedOrdinates Z 0 δ) {ρ₁ : ℂ} (hρ₁ : ρ₁ ∈ Z.carrier)
    (hρ₁re : 1 / 2 < ρ₁.re) {ℓ : ℝ} (hℓ : 40 / δ ≤ ℓ) {M : ℕ} (hM : 2 * ℓ ≤ M) (K : ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hchart : 3 * (|K| + 1) * Real.exp (ℓ / 2) +
        3 * ((∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * Real.exp ℓ) <
      ‖evenCoeff Z (boxSpline 1 3) (ρ₁ - 1 / 2)‖ * Real.exp ((ρ₁.re - 1 / 2) * a)) :
    ∃ u ∈ Icc a (a + (M + 1) * ℓ), 2 * (lagStructure Z (boxSpline 1 3) u).re < -K := by
  set zp : ℂ := ρ₁ - 1 / 2 with hzpdef
  have hzp : evenCoeff Z (boxSpline 1 3) zp ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z (contDiff_boxSpline (r := 1) one_pos 2).continuous
      (hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3))
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ₁
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero hρ₁re.ne'))
  have hzpre : zp.re = ρ₁.re - 1 / 2 := by simp [zp]
  have hδℓ : 40 ≤ δ * ℓ := by rw [div_le_iff₀ hδ] at hℓ; linarith
  have hℓ0 : 0 < ℓ := by
    by_contra h; push Not at h; nlinarith
  have hM0 : 0 < M := by
    have : (0 : ℝ) < M := lt_of_lt_of_le (by linarith) hM
    exact_mod_cast this
  set A := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have hs := summable_norm_evenCoeff_spline hZ
  -- dominant exponents on the grid `a + ℓj`
  set t : ℕ → ℝ := fun j => a + ℓ * j with ht
  choose z hzD hzdom using fun j : ℕ => exists_dominant hZ (t j) hzp
  have hmono : ∀ j, (z j).re ≤ (z (j + 1)).re := fun j =>
    re_le_re_of_dominant (by simp only [ht]; push_cast; nlinarith) (hzD j) (hzD (j + 1))
      (hzdom j _) (hzdom (j + 1) _)
  obtain ⟨j, hjM, hinc⟩ := exists_small_depth_increment (d := fun j => (z j).re)
    (fun j => abs_re_le_of_mem_zeroExps (mem_of_evenCoeff_ne_zero (hzD j))) hM0
  have hη : 2 / (M : ℝ) ≤ 1 / ℓ := by
    rw [div_le_div_iff₀ (by exact_mod_cast hM0) hℓ0]; linarith
  set u₀ := t (j + 1) with hu₀
  have e1 : t (j + 2) = u₀ + ℓ := by simp only [hu₀, ht]; push_cast; ring
  have e2 : t j = u₀ + -ℓ := by simp only [hu₀, ht]; push_cast; ring
  have hu00 : 0 ≤ u₀ := by simp only [hu₀, ht]; positivity
  have hau : a ≤ u₀ := by simp only [hu₀, ht]; nlinarith [Nat.cast_nonneg (α := ℝ) (j + 1)]
  by_contra hall
  push Not at hall
  -- the subwindow lies in the window
  have hjM' : ((j : ℝ) + 2) ≤ (M : ℝ) + 1 := by
    have : j + 1 ≤ M := hjM
    have : ((j + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast this
    push_cast at this; linarith
  have hall' : ∀ u ∈ Icc (u₀ - ℓ) (u₀ + ℓ),
      -|K| ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := fun u hu => by
    have h1 : a ≤ u := by
      have : a ≤ u₀ - ℓ := by
        simp only [hu₀, ht]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) j]
      linarith [hu.1]
    have h2 : u ≤ a + (M + 1) * ℓ := by
      have : u₀ + ℓ ≤ a + (M + 1) * ℓ := by
        simp only [hu₀, ht]; push_cast; nlinarith
      linarith [hu.2]
    linarith [hall u ⟨h1, h2⟩, le_abs_self K]
  set z₀ := z (j + 1) with hz₀def
  have hz₀ := hzD (j + 1)
  have h₀ : ∀ z', expWeight Z u₀ z' ≤ expWeight Z u₀ z₀ := hzdom (j + 1)
  have hA' : ∀ z', expWeight Z (u₀ + ℓ) z' ≤ expWeight Z (u₀ + ℓ) (z (j + 2)) := by
    rw [← e1]; exact hzdom (j + 2)
  have hB : ∀ z', expWeight Z (u₀ + -ℓ) z' ≤ expWeight Z (u₀ + -ℓ) (z j) := by
    rw [← e2]; exact hzdom j
  have hdrift := expWeight_drift_le_of_increment (η := 1 / ℓ) hℓ0.le h₀ hA'
    (by linarith [hmono j, hmono (j + 1)]) hB (by linarith [hmono j, hmono (j + 1)])
  have hM0' : 0 ≤ expWeight Z u₀ z₀ := expWeight_nonneg _ _
  have hBle : Real.exp (1 / ℓ * ℓ) * expWeight Z u₀ z₀ ≤ 3 * expWeight Z u₀ z₀ := by
    rw [one_div, inv_mul_cancel₀ hℓ0.ne']
    exact mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_lt_d9]) hM0'
  -- the dominant weight exceeds the chart threshold
  have hgr : 3 * (|K| + 1) * Real.exp (ℓ / 2) + 3 * (A * Real.exp ℓ) < expWeight Z u₀ z₀ :=
    calc _ < ‖evenCoeff Z (boxSpline 1 3) zp‖ * Real.exp ((ρ₁.re - 1 / 2) * a) := hchart
      _ ≤ ‖evenCoeff Z (boxSpline 1 3) zp‖ * Real.exp (zp.re * u₀) := by
          rw [hzpre]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left hau (by linarith))) (norm_nonneg _)
      _ ≤ expWeight Z u₀ z₀ := h₀ zp
  -- hence the dominant exponent is off the line to the right
  have hz₀c : 0 < z₀.re := by
    by_contra hle
    push Not at hle
    have h1 : expWeight Z u₀ z₀ ≤ A :=
      calc expWeight Z u₀ z₀ ≤ ‖evenCoeff Z (boxSpline 1 3) z₀‖ * 1 :=
            mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
              (mul_nonpos_of_nonpos_of_nonneg hle hu00)) (norm_nonneg _)
        _ = ‖evenCoeff Z (boxSpline 1 3) z₀‖ := mul_one _
        _ ≤ A := hs.le_tsum z₀ fun _ _ => norm_nonneg _
    have h2 : A ≤ 3 * (A * Real.exp ℓ) := by
      have := Real.one_le_exp hℓ0.le
      nlinarith
    have h3 : 0 ≤ 3 * (|K| + 1) * Real.exp (ℓ / 2) := by positivity
    linarith
  have hconj0 : evenCoeff Z (boxSpline 1 3) (conj z₀) ≠ 0 := by
    rw [evenCoeff_conj]; exact (map_ne_zero _).mpr hz₀
  classical
  obtain ⟨S, hTS, hSE, hlow⟩ := exists_finset_window_lower hZ u₀ ℓ hall' {z₀, conj z₀}
  have hz₀S : z₀ ∈ S := hTS z₀ (by simp) hz₀
  have hz₀'S : conj z₀ ∈ S := hTS _ (by simp) hconj0
  have hle := expWeight_le_of_window_lower_deep hZ hnoreal hδ hsep hSE hz₀S hz₀'S hz₀c hu00 hℓ0
    (by positivity : 0 ≤ |K| + 1) hδℓ hdrift hBle hlow
  rw [zero_mul, Real.exp_zero, mul_one] at hle
  linarith

end GaloisForLFunctions.SurfaceOfSpecZ
