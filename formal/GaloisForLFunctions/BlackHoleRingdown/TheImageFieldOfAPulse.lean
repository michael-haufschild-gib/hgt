import GaloisForLFunctions.BlackHoleRingdown.TheLiftOfAnyModularWave
import GaloisForLFunctions.RHTower.DeckIncompleteEisenstein

/-!
# The image field of a pulse

A compact pulse `h` sent down the cusp is the plane wave `Y^{½} h(τ + log Y)`, an exact solution of the
modular wave equation. The method of images makes it invariant:

`Π_h(τ, z) = ½ Σ_{(c,d)=1} y_γ^{½} h(τ + log y_γ)`,   `y_γ = Y/|cz+d|²`.

For `(τ, z)` in a compact set only finitely many rows contribute, because `y_γ ≥ a` confines `(c, d)` to a
bounded set. Each term solves the wave equation: `y_γ` is harmonic with `Y²|∇y_γ|² = y_γ²`, so
`Y²(∂_x²+∂_Y²)[F(y_γ)] = y_γ² F''(y_γ)`. So `Π_h` is an exact `SL₂(ℤ)`-invariant solution, by elementary
means, with no spectral theory and no zeta function. Time derivatives act on the pulse:
`∂_τ Π_h = Π_{h'}`.
-/

open Complex Set Filter Topology ModularGroup EisensteinSeries
open scoped UpperHalfPlane MatrixGroups ContDiff

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.DeckPointPair

/-! ### Compact pulses -/

/-- A smooth compactly supported pulse. -/
structure CompactPulse where
  toFun : ℝ → ℂ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun

instance : CoeFun CompactPulse fun _ => ℝ → ℂ := ⟨CompactPulse.toFun⟩

/-- The derivative of a pulse is a pulse. -/
def CompactPulse.D (h : CompactPulse) : CompactPulse where
  toFun := deriv h.toFun
  smooth := (contDiff_infty_iff_deriv.mp h.smooth).2
  compact := h.compact.deriv

theorem CompactPulse.hasDerivAt (h : CompactPulse) (s : ℝ) : HasDerivAt h (h.D s) s :=
  ((contDiff_infty_iff_deriv.mp h.smooth).1 s).hasDerivAt

theorem CompactPulse.exists_support_bound (h : CompactPulse) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ s : ℝ, S < |s| → h s = 0 := by
  obtain ⟨S, hS⟩ := h.compact.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max S 0, le_max_right _ _, fun s hs => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have := hS hmem
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at this
  exact absurd (this.trans (le_max_left S 0)) (not_le.mpr hs)

/-! ### The height of an image -/

/-- The denominator `|cz + d|²`. -/
def rowDen (c d x Y : ℝ) : ℝ := (c * x + d) ^ 2 + (c * Y) ^ 2

/-- The height `Y/|cz + d|²` of an image. -/
def rowHgt (c d x Y : ℝ) : ℝ := Y / rowDen c d x Y

/-- The first and second derivatives of the height. -/
def rowHgtX (c d x Y : ℝ) : ℝ := -(2 * c * (c * x + d) * Y) / rowDen c d x Y ^ 2
def rowHgtXX (c d x Y : ℝ) : ℝ :=
  -(2 * c ^ 2 * Y) / rowDen c d x Y ^ 2 + 8 * c ^ 2 * (c * x + d) ^ 2 * Y / rowDen c d x Y ^ 3
def rowHgtY (c d x Y : ℝ) : ℝ := ((c * x + d) ^ 2 - (c * Y) ^ 2) / rowDen c d x Y ^ 2
def rowHgtYY (c d x Y : ℝ) : ℝ :=
  -(6 * c ^ 2 * Y) / rowDen c d x Y ^ 2 + 8 * c ^ 4 * Y ^ 3 / rowDen c d x Y ^ 3

section Height

variable {c d x Y : ℝ}

theorem hasDerivAt_rowDen_x : HasDerivAt (fun q => rowDen c d q Y) (2 * c * (c * x + d)) x := by
  have hA : HasDerivAt (fun q : ℝ => c * q + d) c x := by
    simpa using ((hasDerivAt_id x).const_mul c).add_const d
  have h := (hA.mul hA).add_const ((c * Y) ^ 2)
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
  simp [rowDen, sq]

theorem hasDerivAt_rowDen_y : HasDerivAt (fun q => rowDen c d x q) (2 * c ^ 2 * Y) Y := by
  have hA : HasDerivAt (fun q : ℝ => c * q) c Y := by
    simpa using (hasDerivAt_id Y).const_mul c
  have h := (hA.mul hA).const_add ((c * x + d) ^ 2)
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
  simp [rowDen, sq]

theorem hasDerivAt_rowHgt_x (h : rowDen c d x Y ≠ 0) :
    HasDerivAt (fun q => rowHgt c d q Y) (rowHgtX c d x Y) x := by
  have := (hasDerivAt_const x Y).div hasDerivAt_rowDen_x h
  refine this.congr_deriv ?_
  rw [rowHgtX]
  ring

theorem hasDerivAt_rowHgt_y (h : rowDen c d x Y ≠ 0) :
    HasDerivAt (fun q => rowHgt c d x q) (rowHgtY c d x Y) Y := by
  have := (hasDerivAt_id Y).div hasDerivAt_rowDen_y h
  refine this.congr_deriv ?_
  rw [rowHgtY]
  simp only [id]
  rw [div_eq_div_iff (pow_ne_zero 2 h) (pow_ne_zero 2 h)]
  rw [rowDen]
  ring

theorem hasDerivAt_rowHgtX_x (h : rowDen c d x Y ≠ 0) :
    HasDerivAt (fun q => rowHgtX c d q Y) (rowHgtXX c d x Y) x := by
  have hA : HasDerivAt (fun q : ℝ => -(2 * c * (c * q + d) * Y)) (-(2 * c * c * Y)) x := by
    have h1 : HasDerivAt (fun q : ℝ => c * q + d) c x := by
      simpa using ((hasDerivAt_id x).const_mul c).add_const d
    exact ((h1.const_mul (2 * c)).mul_const Y).neg
  have hD : HasDerivAt (fun q => rowDen c d q Y ^ 2)
      (2 * rowDen c d x Y * (2 * c * (c * x + d))) x := by
    have := hasDerivAt_rowDen_x (c := c) (d := d) (x := x) (Y := Y)
    exact ((this.mul this).congr_deriv (by ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun q => by simp [sq])
  have := hA.div hD (pow_ne_zero 2 h)
  refine this.congr_deriv ?_
  rw [rowHgtXX]
  field_simp
  ring

theorem hasDerivAt_rowHgtY_y (h : rowDen c d x Y ≠ 0) :
    HasDerivAt (fun q => rowHgtY c d x q) (rowHgtYY c d x Y) Y := by
  have hA : HasDerivAt (fun q : ℝ => (c * x + d) ^ 2 - (c * q) ^ 2) (-(2 * c ^ 2 * Y)) Y := by
    have h1 : HasDerivAt (fun q : ℝ => c * q) c Y := by
      simpa using (hasDerivAt_id Y).const_mul c
    exact (((h1.mul h1).const_sub ((c * x + d) ^ 2)).congr_deriv (by ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun q => by simp [sq])
  have hD : HasDerivAt (fun q => rowDen c d x q ^ 2) (2 * rowDen c d x Y * (2 * c ^ 2 * Y)) Y := by
    have := hasDerivAt_rowDen_y (c := c) (d := d) (x := x) (Y := Y)
    exact ((this.mul this).congr_deriv (by ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun q => by simp [sq])
  have := hA.div hD (pow_ne_zero 2 h)
  refine this.congr_deriv ?_
  rw [rowHgtYY]
  have hR : rowDen c d x Y = (c * x + d) ^ 2 + (c * Y) ^ 2 := rfl
  field_simp
  rw [hR]
  ring

/-- The height has `|∇y|² = 1/|cz+d|⁴`. -/
theorem rowHgt_grad_sq (h : rowDen c d x Y ≠ 0) :
    rowHgtX c d x Y ^ 2 + rowHgtY c d x Y ^ 2 = 1 / rowDen c d x Y ^ 2 := by
  have hR : rowDen c d x Y = (c * x + d) ^ 2 + (c * Y) ^ 2 := rfl
  rw [rowHgtX, rowHgtY, div_pow, div_pow, ← add_div, div_eq_div_iff (by positivity) (by positivity)]
  rw [hR]
  ring

/-- The height is harmonic. -/
theorem rowHgt_harmonic (h : rowDen c d x Y ≠ 0) :
    rowHgtXX c d x Y + rowHgtYY c d x Y = 0 := by
  have hR : rowDen c d x Y = (c * x + d) ^ 2 + (c * Y) ^ 2 := rfl
  rw [rowHgtXX, rowHgtYY]
  field_simp
  rw [hR]
  ring

end Height

/-! ### The plane wave against the height -/

/-- The plane wave `y^{½} h(τ + log y)`. -/
def pulseF (h : ℝ → ℂ) (τ y : ℝ) : ℂ := ((Real.sqrt y : ℝ) : ℂ) * h (τ + Real.log y)

/-- Its first derivative in `y`. -/
def pulseF1 (h h' : ℝ → ℂ) (τ y : ℝ) : ℂ :=
  ((Real.sqrt y)⁻¹ : ℝ) * ((1 / 2 : ℂ) * h (τ + Real.log y) + h' (τ + Real.log y))

/-- Its second derivative in `y`. -/
def pulseF2 (h h'' : ℝ → ℂ) (τ y : ℝ) : ℂ :=
  ((y * Real.sqrt y)⁻¹ : ℝ) * (h'' (τ + Real.log y) - (1 / 4 : ℂ) * h (τ + Real.log y))

theorem hasDerivAt_pulse_comp (h : CompactPulse) (τ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun q => h (τ + Real.log q)) ((y⁻¹ : ℝ) * h.D (τ + Real.log y)) y := by
  have hin : HasDerivAt (fun q : ℝ => τ + Real.log q) y⁻¹ y :=
    (Real.hasDerivAt_log hy.ne').const_add τ
  have := (h.hasDerivAt (τ + Real.log y)).scomp y hin
  simpa [Function.comp_def, Complex.real_smul] using this

theorem hasDerivAt_sqrt_ofReal {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun q => ((Real.sqrt q : ℝ) : ℂ)) ((1 / (2 * Real.sqrt y) : ℝ) : ℂ) y :=
  (Real.hasDerivAt_sqrt hy.ne').ofReal_comp

theorem hasDerivAt_pulseF (h : CompactPulse) (τ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (pulseF h τ) (pulseF1 h h.D τ y) y := by
  have h1 := (hasDerivAt_sqrt_ofReal hy).mul (hasDerivAt_pulse_comp h τ hy)
  refine h1.congr_deriv ?_
  rw [pulseF1]
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy.le
  have hsC : ((Real.sqrt y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hyC : ((y : ℝ) : ℂ) = ((Real.sqrt y : ℝ) : ℂ) * ((Real.sqrt y : ℝ) : ℂ) := by
    exact_mod_cast hsq.symm
  push_cast
  rw [hyC]
  field_simp

theorem hasDerivAt_pulseF1 (h : CompactPulse) (τ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (pulseF1 h h.D τ) (pulseF2 h h.D.D τ y) y := by
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy.le
  have hin : HasDerivAt (fun q => ((Real.sqrt q)⁻¹ : ℝ))
      (-(1 / (2 * Real.sqrt y)) / Real.sqrt y ^ 2) y := (Real.hasDerivAt_sqrt hy.ne').inv hs
  have h1 := (hin.ofReal_comp).mul (((hasDerivAt_pulse_comp h τ hy).const_mul (1 / 2 : ℂ)).add
    (hasDerivAt_pulse_comp h.D τ hy))
  refine h1.congr_deriv ?_
  rw [pulseF2]
  simp only [Pi.add_apply]
  have hsC : ((Real.sqrt y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hyC : ((y : ℝ) : ℂ) = ((Real.sqrt y : ℝ) : ℂ) * ((Real.sqrt y : ℝ) : ℂ) := by
    exact_mod_cast hsq.symm
  push_cast
  rw [hyC]
  field_simp
  ring

theorem hasDerivAt_pulseF_time (h : CompactPulse) (τ y : ℝ) :
    HasDerivAt (fun s => pulseF h s y) (pulseF h.D τ y) τ := by
  have hin : HasDerivAt (fun s : ℝ => s + Real.log y) 1 τ := (hasDerivAt_id τ).add_const _
  have := (h.hasDerivAt (τ + Real.log y)).scomp τ hin
  have h2 := this.const_mul ((Real.sqrt y : ℝ) : ℂ)
  simpa [Function.comp_def, pulseF] using h2

/-! ### One row -/

section Row

variable (h : CompactPulse) (c d : ℝ) (τ : ℝ) {x Y : ℝ}

/-- The term of a row and its jets. -/
def imageTerm (h : ℝ → ℂ) (c d τ x Y : ℝ) : ℂ := pulseF h τ (rowHgt c d x Y)
def imageTermX (h : CompactPulse) (c d τ x Y : ℝ) : ℂ :=
  pulseF1 h h.D τ (rowHgt c d x Y) * (rowHgtX c d x Y : ℂ)
def imageTermY (h : CompactPulse) (c d τ x Y : ℝ) : ℂ :=
  pulseF1 h h.D τ (rowHgt c d x Y) * (rowHgtY c d x Y : ℂ)
def imageTermXX (h : CompactPulse) (c d τ x Y : ℝ) : ℂ :=
  pulseF2 h h.D.D τ (rowHgt c d x Y) * (rowHgtX c d x Y : ℂ) ^ 2 +
    pulseF1 h h.D τ (rowHgt c d x Y) * (rowHgtXX c d x Y : ℂ)
def imageTermYY (h : CompactPulse) (c d τ x Y : ℝ) : ℂ :=
  pulseF2 h h.D.D τ (rowHgt c d x Y) * (rowHgtY c d x Y : ℂ) ^ 2 +
    pulseF1 h h.D τ (rowHgt c d x Y) * (rowHgtYY c d x Y : ℂ)

variable {c d}

theorem rowHgt_pos (hY : 0 < Y) (hR : 0 < rowDen c d x Y) : 0 < rowHgt c d x Y := div_pos hY hR

theorem hasDerivAt_imageTerm_x (hY : 0 < Y) (hR : 0 < rowDen c d x Y) :
    HasDerivAt (fun q => imageTerm h c d τ q Y) (imageTermX h c d τ x Y) x := by
  have := (hasDerivAt_pulseF h τ (rowHgt_pos hY hR)).scomp x (hasDerivAt_rowHgt_x hR.ne')
  refine (this.congr_deriv ?_)
  rw [imageTermX, Complex.real_smul]
  ring

theorem hasDerivAt_imageTerm_y (hY : 0 < Y) (hR : 0 < rowDen c d x Y) :
    HasDerivAt (fun q => imageTerm h c d τ x q) (imageTermY h c d τ x Y) Y := by
  have := (hasDerivAt_pulseF h τ (rowHgt_pos hY hR)).scomp Y (hasDerivAt_rowHgt_y hR.ne')
  refine (this.congr_deriv ?_)
  rw [imageTermY, Complex.real_smul]
  ring

theorem hasDerivAt_imageTermX_x (hY : 0 < Y) (hR : 0 < rowDen c d x Y) :
    HasDerivAt (fun q => imageTermX h c d τ q Y) (imageTermXX h c d τ x Y) x := by
  have h1 := (hasDerivAt_pulseF1 h τ (rowHgt_pos hY hR)).scomp x (hasDerivAt_rowHgt_x hR.ne')
  have h2 := (hasDerivAt_rowHgtX_x hR.ne').ofReal_comp
  refine (h1.mul h2).congr_deriv ?_
  rw [imageTermXX, Complex.real_smul]
  simp only [Function.comp_apply]
  ring

theorem hasDerivAt_imageTermY_y (hY : 0 < Y) (hR : 0 < rowDen c d x Y) :
    HasDerivAt (fun q => imageTermY h c d τ x q) (imageTermYY h c d τ x Y) Y := by
  have h1 := (hasDerivAt_pulseF1 h τ (rowHgt_pos hY hR)).scomp Y (hasDerivAt_rowHgt_y hR.ne')
  have h2 := (hasDerivAt_rowHgtY_y hR.ne').ofReal_comp
  refine (h1.mul h2).congr_deriv ?_
  rw [imageTermYY, Complex.real_smul]
  simp only [Function.comp_apply]
  ring

/-- **Each row solves the wave equation.** -/
theorem imageTerm_wave (hY : 0 < Y) (hR : 0 < rowDen c d x Y) :
    imageTerm h.D.D c d τ x Y =
      (Y : ℂ) ^ 2 * (imageTermXX h c d τ x Y + imageTermYY h c d τ x Y) +
        imageTerm h c d τ x Y / 4 := by
  have hgrad : ((rowHgtX c d x Y : ℝ) : ℂ) ^ 2 + ((rowHgtY c d x Y : ℝ) : ℂ) ^ 2 =
      ((1 / rowDen c d x Y ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast rowHgt_grad_sq (c := c) (d := d) (x := x) (Y := Y) hR.ne'
  have hharm : ((rowHgtXX c d x Y : ℝ) : ℂ) + ((rowHgtYY c d x Y : ℝ) : ℂ) = 0 := by
    exact_mod_cast rowHgt_harmonic (c := c) (d := d) (x := x) (Y := Y) hR.ne'
  have hy := rowHgt_pos (c := c) (d := d) (x := x) hY hR
  set y := rowHgt c d x Y with hydef
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy.le
  have hYy : Y / rowDen c d x Y = y := rfl
  have hprod : Y ^ 2 * (1 / rowDen c d x Y ^ 2) * (y * Real.sqrt y)⁻¹ = Real.sqrt y := by
    have h1 : Y ^ 2 * (1 / rowDen c d x Y ^ 2) = y ^ 2 := by
      rw [← hYy, div_pow, mul_one_div]
    rw [h1]
    have hy0 := hy.ne'
    calc y ^ 2 * (y * Real.sqrt y)⁻¹ = y / Real.sqrt y := by field_simp
      _ = Real.sqrt y := by rw [div_eq_iff hs, hsq]
  have hprodC : (Y : ℂ) ^ 2 * ((1 / rowDen c d x Y ^ 2 : ℝ) : ℂ) * ((y * Real.sqrt y)⁻¹ : ℝ) =
      (Real.sqrt y : ℝ) := by
    exact_mod_cast hprod
  simp only [imageTerm, imageTermXX, imageTermYY, ← hydef, pulseF, pulseF2]
  have hkey : (Y : ℂ) ^ 2 * (((y * Real.sqrt y)⁻¹ : ℝ) * (h.D.D (τ + Real.log y) -
      (1 / 4 : ℂ) * h (τ + Real.log y)) * (((rowHgtX c d x Y : ℝ) : ℂ) ^ 2 +
        ((rowHgtY c d x Y : ℝ) : ℂ) ^ 2)) =
      (Real.sqrt y : ℝ) * (h.D.D (τ + Real.log y) - (1 / 4 : ℂ) * h (τ + Real.log y)) := by
    rw [hgrad, ← hprodC]
    ring
  linear_combination -hkey - (Y : ℂ) ^ 2 * pulseF1 h h.D τ y * hharm

end Row

/-! ### The sum over rows -/

/-- The bottom row of a coprime pair, as real numbers. -/
def rowC (p : gammaSet 1 1 0) : ℝ := ((p.1 0 : ℤ) : ℝ)
def rowD (p : gammaSet 1 1 0) : ℝ := ((p.1 1 : ℤ) : ℝ)

theorem rowDen_pos (p : gammaSet 1 1 0) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    0 < rowDen (rowC p) (rowD p) x Y := by
  by_contra hcon
  have h1 : (rowC p * x + rowD p) ^ 2 + (rowC p * Y) ^ 2 ≤ 0 := not_lt.mp hcon
  have h2 : (rowC p * Y) ^ 2 = 0 := by nlinarith [sq_nonneg (rowC p * x + rowD p), sq_nonneg (rowC p * Y)]
  have h3 : (rowC p * x + rowD p) ^ 2 = 0 := by nlinarith [sq_nonneg (rowC p * x + rowD p), sq_nonneg (rowC p * Y)]
  have hc : rowC p = 0 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h2
    exact (mul_eq_zero.mp this).resolve_right hY.ne'
  have hd : rowD p = 0 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h3
    rwa [hc, zero_mul, zero_add] at this
  have h0 : p.1 0 = 0 := by
    have : ((p.1 0 : ℤ) : ℝ) = 0 := hc
    exact_mod_cast this
  have h1 : p.1 1 = 0 := by
    have : ((p.1 1 : ℤ) : ℝ) = 0 := hd
    exact_mod_cast this
  apply gammaSet_val_ne_zero p
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- The chart height of a row is the height of the image. -/
theorem rowHgt_eq_im (p : gammaSet 1 1 0) (z : ℍ) :
    rowHgt (rowC p) (rowD p) z.re z.im = (gammaSetMatrix p • z).im := by
  rw [im_gammaSetMatrix_smul, normSq_int_mul_add, rowHgt, rowDen, rowC, rowD]
  ring_nf

/-- The image field `Π_h`. -/
def imageField (h : ℝ → ℂ) (τ x Y : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : gammaSet 1 1 0, imageTerm h (rowC p) (rowD p) τ x Y

/-- A point of the chart. -/
def chartPoint (x : ℝ) {Y : ℝ} (hY : 0 < Y) : ℍ := ⟨⟨x, Y⟩, hY⟩

/-- **Finitely many rows contribute on a box.** -/
theorem exists_finset_box (h : CompactPulse) (τ₀ x₀ : ℝ) {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    ∃ S : Finset (gammaSet 1 1 0), ∀ τ x Y : ℝ, |τ - τ₀| ≤ 1 → |x - x₀| ≤ 1 → Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      ∀ p ∉ S, imageTerm h (rowC p) (rowD p) τ x Y = 0 := by
  obtain ⟨S₀, hS₀, hsupp⟩ := h.exists_support_bound
  set a := Real.exp (-(S₀ + |τ₀| + 2)) with ha
  have ha0 : 0 < a := Real.exp_pos _
  set C : Set ℂ := Icc (x₀ - 1) (x₀ + 1) ×ℂ Icc (Y₀ / 2) (2 * Y₀) with hC
  have hCc : IsCompact C := isCompact_Icc.reProdIm isCompact_Icc
  have hCU : C ⊆ upperSet := by
    intro w hw
    have := (Complex.mem_reProdIm.mp hw).2.1
    show 0 < w.im
    linarith
  have hK := isCompact_preimage_coe hCc hCU
  refine ⟨(finite_rows_im_ge hK ha0).toFinset, fun τ x Y hτ hx hY p hp => ?_⟩
  have hYpos : 0 < Y := window_pos hY₀ hY
  rw [Set.Finite.mem_toFinset] at hp
  have hz : chartPoint x hYpos ∈ UpperHalfPlane.coe ⁻¹' C := by
    refine Complex.mem_reProdIm.mpr ⟨?_, hY⟩
    obtain ⟨h1, h2⟩ := abs_le.mp hx
    exact ⟨by show x₀ - 1 ≤ x; linarith, by show x ≤ x₀ + 1; linarith⟩
  have hlt : rowHgt (rowC p) (rowD p) x Y < a := by
    by_contra hge
    refine hp ⟨chartPoint x hYpos, hz, ?_⟩
    have := rowHgt_eq_im p (chartPoint x hYpos)
    rw [← this]
    exact not_lt.mp hge
  have hR := rowDen_pos p x hYpos
  have hy := rowHgt_pos hYpos hR
  have hlog : Real.log (rowHgt (rowC p) (rowD p) x Y) < -(S₀ + |τ₀| + 2) := by
    rw [ha] at hlt
    exact (Real.log_lt_iff_lt_exp hy).mpr hlt
  have hτ' : |τ| ≤ |τ₀| + 1 := by
    have := abs_sub_abs_le_abs_sub τ τ₀
    linarith
  have hneg : S₀ < |τ + Real.log (rowHgt (rowC p) (rowD p) x Y)| := by
    have h1 := le_abs_self τ
    have h2 := neg_abs_le (τ + Real.log (rowHgt (rowC p) (rowD p) x Y))
    linarith
  rw [imageTerm, pulseF, hsupp _ hneg, mul_zero]

/-- On a box the field is a finite sum over a set of rows, common to any finite family of pulses. -/
theorem imageField_eq_sum {h : CompactPulse} {S : Finset (gammaSet 1 1 0)} {τ₀ x₀ Y₀ : ℝ}
    (hS : ∀ τ x Y : ℝ, |τ - τ₀| ≤ 1 → |x - x₀| ≤ 1 → Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      ∀ p ∉ S, imageTerm h (rowC p) (rowD p) τ x Y = 0) {τ x Y : ℝ}
    (hτ : |τ - τ₀| ≤ 1) (hx : |x - x₀| ≤ 1) (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀)) :
    imageField h τ x Y = (1 / 2 : ℂ) * ∑ p ∈ S, imageTerm h (rowC p) (rowD p) τ x Y := by
  rw [imageField, tsum_eq_sum fun p hp => hS τ x Y hτ hx hY p hp]

/-- A set of rows good for the pulse and its first two derivatives. -/
theorem exists_finset_box_three (h : CompactPulse) (τ₀ x₀ : ℝ) {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    ∃ S : Finset (gammaSet 1 1 0), ∀ τ x Y : ℝ, |τ - τ₀| ≤ 1 → |x - x₀| ≤ 1 →
      Y ∈ Icc (Y₀ / 2) (2 * Y₀) → ∀ p ∉ S, imageTerm h (rowC p) (rowD p) τ x Y = 0 ∧
        imageTerm h.D (rowC p) (rowD p) τ x Y = 0 ∧ imageTerm h.D.D (rowC p) (rowD p) τ x Y = 0 := by
  classical
  obtain ⟨S₁, h₁⟩ := exists_finset_box h τ₀ x₀ hY₀
  obtain ⟨S₂, h₂⟩ := exists_finset_box h.D τ₀ x₀ hY₀
  obtain ⟨S₃, h₃⟩ := exists_finset_box h.D.D τ₀ x₀ hY₀
  refine ⟨S₁ ∪ S₂ ∪ S₃, fun τ x Y hτ hx hY p hp => ?_⟩
  simp only [Finset.mem_union, not_or] at hp
  exact ⟨h₁ τ x Y hτ hx hY p hp.1.1, h₂ τ x Y hτ hx hY p hp.1.2, h₃ τ x Y hτ hx hY p hp.2⟩

section Field

variable (h : CompactPulse) (x : ℝ) {Y : ℝ}

/-- **Time derivatives act on the pulse:** `∂_τ Π_h = Π_{h'}`. -/
theorem hasDerivAt_imageField_time (τ : ℝ) (hY : 0 < Y) :
    HasDerivAt (fun s => imageField h s x Y) (imageField h.D τ x Y) τ := by
  obtain ⟨S, hS⟩ := exists_finset_box_three h τ x hY
  have hxx : |x - x| ≤ 1 := by simp
  have hYm := mem_window_self hY
  have hS₁ := fun τ' x' Y' a b c p hp => (hS τ' x' Y' a b c p hp).1
  have hS₂ := fun τ' x' Y' a b c p hp => (hS τ' x' Y' a b c p hp).2.1
  have hsum : HasDerivAt (fun s => (1 / 2 : ℂ) * ∑ p ∈ S, imageTerm h (rowC p) (rowD p) s x Y)
      ((1 / 2 : ℂ) * ∑ p ∈ S, imageTerm h.D (rowC p) (rowD p) τ x Y) τ :=
    (HasDerivAt.fun_sum fun p _ => hasDerivAt_pulseF_time h τ _).const_mul _
  rw [imageField_eq_sum hS₂ (by simp) hxx hYm]
  refine hsum.congr_of_eventuallyEq ?_
  have hball : Metric.ball τ 1 ∈ 𝓝 τ := Metric.ball_mem_nhds _ one_pos
  filter_upwards [hball] with s hs
  have : |s - τ| ≤ 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at hs
    exact hs.le
  exact imageField_eq_sum hS₁ this hxx hYm

/-- The second space jets of the field at a point are the finite sums of the jets of the rows. -/
theorem deriv_deriv_imageField_x (τ x₀ : ℝ) (hY : 0 < Y) {S : Finset (gammaSet 1 1 0)}
    (hS : ∀ τ' x' Y' : ℝ, |τ' - τ| ≤ 1 → |x' - x₀| ≤ 1 → Y' ∈ Icc (Y / 2) (2 * Y) →
      ∀ p ∉ S, imageTerm h (rowC p) (rowD p) τ' x' Y' = 0) :
    deriv (deriv fun q => imageField h τ q Y) x₀ =
      (1 / 2 : ℂ) * ∑ p ∈ S, imageTermXX h (rowC p) (rowD p) τ x₀ Y := by
  have hYm := mem_window_self hY
  have hev : (fun q => imageField h τ q Y) =ᶠ[𝓝 x₀]
      fun q => (1 / 2 : ℂ) * ∑ p ∈ S, imageTerm h (rowC p) (rowD p) τ q Y := by
    filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with q hq
    have : |q - x₀| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hq
      exact hq.le
    exact imageField_eq_sum hS (by simp) this hYm
  have hd : ∀ q, HasDerivAt (fun q' => (1 / 2 : ℂ) * ∑ p ∈ S, imageTerm h (rowC p) (rowD p) τ q' Y)
      ((1 / 2 : ℂ) * ∑ p ∈ S, imageTermX h (rowC p) (rowD p) τ q Y) q := fun q =>
    (HasDerivAt.fun_sum fun p _ =>
      hasDerivAt_imageTerm_x h τ hY (rowDen_pos p q hY)).const_mul _
  have hev2 : (deriv fun q => imageField h τ q Y) =ᶠ[𝓝 x₀]
      fun q => (1 / 2 : ℂ) * ∑ p ∈ S, imageTermX h (rowC p) (rowD p) τ q Y := by
    filter_upwards [hev.eventually_nhds] with q hq
    have hq' : (fun q => imageField h τ q Y) =ᶠ[𝓝 q]
        fun q => (1 / 2 : ℂ) * ∑ p ∈ S, imageTerm h (rowC p) (rowD p) τ q Y := hq
    rw [hq'.deriv_eq]
    exact (hd q).deriv
  rw [hev2.deriv_eq]
  exact ((HasDerivAt.fun_sum fun p _ =>
    hasDerivAt_imageTermX_x h τ hY (rowDen_pos p x₀ hY)).const_mul _).deriv

theorem deriv_deriv_imageField_y (τ : ℝ) (hY : 0 < Y) {S : Finset (gammaSet 1 1 0)}
    (hS : ∀ τ' x' Y' : ℝ, |τ' - τ| ≤ 1 → |x' - x| ≤ 1 → Y' ∈ Icc (Y / 2) (2 * Y) →
      ∀ p ∉ S, imageTerm h (rowC p) (rowD p) τ' x' Y' = 0) :
    deriv (deriv fun q => imageField h τ x q) Y =
      (1 / 2 : ℂ) * ∑ p ∈ S, imageTermYY h (rowC p) (rowD p) τ x Y := by
  have hxx : |x - x| ≤ 1 := by simp
  have hbox : Ioo (Y / 2) (2 * Y) ∈ 𝓝 Y := Ioo_mem_nhds (by linarith) (by linarith)
  have hev : (fun q => imageField h τ x q) =ᶠ[𝓝 Y]
      fun q => (1 / 2 : ℂ) * ∑ p ∈ S, imageTerm h (rowC p) (rowD p) τ x q := by
    filter_upwards [hbox] with q hq
    exact imageField_eq_sum hS (by simp) hxx (Ioo_subset_Icc_self hq)
  have hd : ∀ q, 0 < q → HasDerivAt
      (fun q' => (1 / 2 : ℂ) * ∑ p ∈ S, imageTerm h (rowC p) (rowD p) τ x q')
      ((1 / 2 : ℂ) * ∑ p ∈ S, imageTermY h (rowC p) (rowD p) τ x q) q := fun q hq =>
    (HasDerivAt.fun_sum fun p _ =>
      hasDerivAt_imageTerm_y h τ hq (rowDen_pos p x hq)).const_mul _
  have hev2 : (deriv fun q => imageField h τ x q) =ᶠ[𝓝 Y]
      fun q => (1 / 2 : ℂ) * ∑ p ∈ S, imageTermY h (rowC p) (rowD p) τ x q := by
    filter_upwards [hev.eventually_nhds, lt_mem_nhds hY] with q hq hq0
    have hq' : (fun q => imageField h τ x q) =ᶠ[𝓝 q]
        fun q => (1 / 2 : ℂ) * ∑ p ∈ S, imageTerm h (rowC p) (rowD p) τ x q := hq
    rw [hq'.deriv_eq]
    exact (hd q hq0).deriv
  rw [hev2.deriv_eq]
  exact ((HasDerivAt.fun_sum fun p _ =>
    hasDerivAt_imageTermY_y h τ hY (rowDen_pos p x hY)).const_mul _).deriv

end Field

/-- **The image field solves the modular wave equation.** -/
theorem isModularWave_imageField (h : CompactPulse) : IsModularWave (imageField h) where
  diff := fun x y hy τ => (hasDerivAt_imageField_time h x τ hy).differentiableAt
  diff2 := fun x y hy τ => by
    have heq : (deriv fun s => imageField h s x y) = fun s => imageField h.D s x y :=
      funext fun s => (hasDerivAt_imageField_time h x s hy).deriv
    rw [heq]
    exact (hasDerivAt_imageField_time h.D x τ hy).differentiableAt
  wave := fun τ x y hy => by
    have heq : (deriv fun s => imageField h s x y) = fun s => imageField h.D s x y :=
      funext fun s => (hasDerivAt_imageField_time h x s hy).deriv
    rw [heq, (hasDerivAt_imageField_time h.D x τ hy).deriv]
    obtain ⟨S, hS⟩ := exists_finset_box_three h τ x hy
    have hS₁ := fun τ' x' Y' a b c p hp => (hS τ' x' Y' a b c p hp).1
    have hS₃ := fun τ' x' Y' a b c p hp => (hS τ' x' Y' a b c p hp).2.2
    have hYm := mem_window_self hy
    rw [deriv_deriv_imageField_x h τ x hy hS₁, deriv_deriv_imageField_y h x τ hy hS₁,
      imageField_eq_sum hS₃ (by simp) (by simp) hYm, imageField_eq_sum hS₁ (by simp) (by simp) hYm]
    have hterm : ∀ p ∈ S, imageTerm h.D.D (rowC p) (rowD p) τ x y =
        (y : ℂ) ^ 2 * (imageTermXX h (rowC p) (rowD p) τ x y + imageTermYY h (rowC p) (rowD p) τ x y) +
          imageTerm h (rowC p) (rowD p) τ x y / 4 :=
      fun p _ => imageTerm_wave h τ hy (rowDen_pos p x hy)
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
      ← Finset.sum_div]
    ring

/-- **The image field is invariant.** -/
theorem imageField_smul (h : ℝ → ℂ) (τ : ℝ) (γ : SL(2, ℤ)) (z : ℍ) :
    imageField h τ (γ • z : ℍ).re (γ • z : ℍ).im = imageField h τ z.re z.im := by
  have hterm : ∀ p : gammaSet 1 1 0,
      imageTerm h (rowC p) (rowD p) τ (γ • z : ℍ).re (γ • z : ℍ).im =
        imageTerm h (rowC (gammaSetSelfEquiv γ p)) (rowD (gammaSetSelfEquiv γ p)) τ z.re z.im := by
    intro p
    obtain ⟨n, hn⟩ := exists_eq_T_zpow_mul_of_bottomRow_eq (gammaSetMatrix p * γ)
      (gammaSetMatrix (gammaSetSelfEquiv γ p))
      (by rw [gammaSetMatrix_mul_apply_one, gammaSetMatrix_apply_one_zero,
        gammaSetSelfEquiv_apply_val])
      (by rw [gammaSetMatrix_mul_apply_one, gammaSetMatrix_apply_one_one,
        gammaSetSelfEquiv_apply_val])
    have him : (gammaSetMatrix p • γ • z).im = (gammaSetMatrix (gammaSetSelfEquiv γ p) • z).im := by
      rw [← mul_smul, hn, mul_smul, ModularGroup.im_T_zpow_smul]
    rw [imageTerm, imageTerm, rowHgt_eq_im, rowHgt_eq_im, him]
  rw [imageField, imageField]
  simp_rw [hterm]
  rw [(gammaSetSelfEquiv γ).tsum_eq
    (fun p => imageTerm h (rowC p) (rowD p) τ z.re z.im)]

end GaloisForLFunctions.BlackHoleRingdown

end
