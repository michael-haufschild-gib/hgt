import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheExponentialInterpolationErrorIsSmallAtDenseGrids
import GaloisForLFunctions.RHTower.HighBlockAsymptotics

section TheCalibratedNodesStayOnASeparatedImaginaryGrid

/-!
## Geometry of calibrated imaginary grids

A grid from `Γ` to `3Γ` has enough room for calibration: coordinate
perturbations at most one eighth of `Γ/k` retain half the index separation,
keep every ordinate positive, and bound all node norms by `4Γ`.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- An equally spaced upper imaginary grid. -/
def imaginaryInterpolationGrid (Γ : ℝ) (k : ℕ) (j : Fin (k + 1)) : ℂ :=
  ((Γ + (2 * Γ / k) * (j : ℕ) : ℝ) : ℂ) * I

/-- Distinct grid indices differ by at least one. -/
theorem one_le_abs_fin_index_sub {k : ℕ} {i j : Fin (k + 1)} (hij : i ≠ j) :
    (1 : ℝ) ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hh : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    rw [abs_of_nonpos (by linarith only [hh])]
    linarith only [hh]
  · have hh : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hgt
    rw [abs_of_nonneg (by linarith only [hh])]
    linarith only [hh]

/-- The reference grid lies between ordinates `Γ` and `3Γ`. -/
theorem imaginaryInterpolationGrid_bounds {Γ : ℝ} (hΓ : 0 < Γ) {k : ℕ} (hk : 0 < k)
    (j : Fin (k + 1)) :
    (imaginaryInterpolationGrid Γ k j).re = 0 ∧
      Γ ≤ (imaginaryInterpolationGrid Γ k j).im ∧
      (imaginaryInterpolationGrid Γ k j).im ≤ 3 * Γ ∧
      Γ ≤ ‖imaginaryInterpolationGrid Γ k j‖ ∧ ‖imaginaryInterpolationGrid Γ k j‖ ≤ 3 * Γ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hj : ((j : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.le_of_lt_succ j.2
  have hs : 0 ≤ 2 * Γ / k := by positivity
  have hm := mul_le_mul_of_nonneg_left hj hs
  have he : (2 * Γ / k) * k = 2 * Γ := by field_simp
  rw [he] at hm
  have h0 : 0 ≤ (2 * Γ / k) * (j : ℕ) := by positivity
  have hre : (imaginaryInterpolationGrid Γ k j).re = 0 := by
    simp [imaginaryInterpolationGrid]
  have him : (imaginaryInterpolationGrid Γ k j).im = Γ + (2 * Γ / k) * (j : ℕ) := by
    simp [imaginaryInterpolationGrid]
  have hn : ‖imaginaryInterpolationGrid Γ k j‖ = Γ + (2 * Γ / k) * (j : ℕ) := by
    simp only [imaginaryInterpolationGrid, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, abs_of_pos (by positivity : 0 < Γ + (2 * Γ / k) * (j : ℕ))]
  have hlo : Γ ≤ Γ + (2 * Γ / k) * (j : ℕ) := by linarith only [h0]
  have hhi : Γ + (2 * Γ / k) * (j : ℕ) ≤ 3 * Γ := by linarith only [hm]
  refine ⟨hre, ?_, ?_, ?_, ?_⟩
  · simpa only [him] using hlo
  · simpa only [him] using hhi
  · simpa only [hn] using hlo
  · simpa only [hn] using hhi


/-- Exact index separation of the reference grid. -/
theorem imaginaryInterpolationGrid_separation {Γ : ℝ} (hΓ : 0 < Γ) {k : ℕ} (hk : 0 < k)
    (i j : Fin (k + 1)) :
    ‖imaginaryInterpolationGrid Γ k i - imaginaryInterpolationGrid Γ k j‖ =
      |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (2 * Γ / k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have he : imaginaryInterpolationGrid Γ k i - imaginaryInterpolationGrid Γ k j =
      ((((2 * Γ / k) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) : ℝ) : ℂ)) * I := by
    unfold imaginaryInterpolationGrid
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    abs_mul, abs_of_pos (by positivity : 0 < 2 * Γ / k), mul_comm]

/-- Small coordinate perturbations preserve half the index separation and the frequency band. -/
theorem calibrated_grid_geometry {Γ r : ℝ} (hΓ : 0 < Γ) {k : ℕ} (hk : 0 < k)
    (hr : 0 ≤ r) (hsmall : 8 * r ≤ Γ / k) {z : Fin (k + 1) → ℂ}
    (hz : ∀ i, ‖z i - imaginaryInterpolationGrid Γ k i‖ ≤ r) :
    (∀ i, |(z i).re| ≤ r ∧ Γ / 2 ≤ (z i).im ∧ (z i).im ≤ 4 * Γ ∧ ‖z i‖ ≤ 4 * Γ) ∧
      ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (Γ / k) ≤ ‖z i - z j‖ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsΓ : Γ / k ≤ Γ := (div_le_iff₀ hk0).mpr (by nlinarith only [hk1, hΓ])
  have hrΓ : 2 * r ≤ Γ := by linarith only [hsmall, hsΓ, hr]
  constructor
  · intro i
    obtain ⟨hre, him0, him1, _, hn⟩ := imaginaryInterpolationGrid_bounds hΓ hk i
    have hi := (Complex.abs_im_le_norm (z i - imaginaryInterpolationGrid Γ k i)).trans (hz i)
    have hri := (Complex.abs_re_le_norm (z i - imaginaryInterpolationGrid Γ k i)).trans (hz i)
    simp only [Complex.sub_re, hre, sub_zero] at hri
    simp only [Complex.sub_im, abs_le] at hi
    have hnorm : ‖z i‖ ≤ r + 3 * Γ := by
      have hh := norm_add_le (z i - imaginaryInterpolationGrid Γ k i)
        (imaginaryInterpolationGrid Γ k i)
      rw [sub_add_cancel] at hh
      linarith only [hh, hz i, hn]
    exact ⟨hri, by linarith only [hi.1, him0, hrΓ],
      by linarith only [hi.2, him1, hrΓ, hr], by linarith only [hnorm, hrΓ, hr]⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      simp
    have hidx := one_le_abs_fin_index_sub hij
    have hs0 : 0 ≤ Γ / k := by positivity
    have hmult := mul_le_mul_of_nonneg_right hidx hs0
    have htri : ‖imaginaryInterpolationGrid Γ k i - imaginaryInterpolationGrid Γ k j‖ ≤
        2 * r + ‖z i - z j‖ := by
      calc
        _ = ‖(imaginaryInterpolationGrid Γ k i - z i) +
            (z i - z j) + (z j - imaginaryInterpolationGrid Γ k j)‖ := by congr 1; ring
        _ ≤ ‖imaginaryInterpolationGrid Γ k i - z i‖ + ‖z i - z j‖ +
            ‖z j - imaginaryInterpolationGrid Γ k j‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ _ := by rw [norm_sub_rev]; linarith only [hz i, hz j]
    rw [imaginaryInterpolationGrid_separation hΓ hk] at htri
    simp only [div_eq_mul_inv] at htri hmult hsmall ⊢
    nlinarith only [htri, hmult, hsmall, hr]

/-- Calibration preserves index separation of the ordinates themselves. -/
theorem calibrated_grid_ordinate_separation {Γ r : ℝ} (hΓ : 0 < Γ) {k : ℕ} (hk : 0 < k)
    (hr : 0 ≤ r) (hsmall : 8 * r ≤ Γ / k) {z : Fin (k + 1) → ℂ}
    (hz : ∀ i, ‖z i - imaginaryInterpolationGrid Γ k i‖ ≤ r) (i j : Fin (k + 1)) :
    |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (Γ / k) ≤ |(z i).im - (z j).im| := by
  by_cases hij : i = j
  · subst j
    simp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hidx := one_le_abs_fin_index_sub hij
  have hs0 : 0 ≤ Γ / k := by positivity
  have hmult := mul_le_mul_of_nonneg_right hidx hs0
  have hi := (Complex.abs_im_le_norm (z i - imaginaryInterpolationGrid Γ k i)).trans (hz i)
  have hj := (Complex.abs_im_le_norm (z j - imaginaryInterpolationGrid Γ k j)).trans (hz j)
  simp only [Complex.sub_im] at hi hj
  have htri : |(imaginaryInterpolationGrid Γ k i).im - (imaginaryInterpolationGrid Γ k j).im| ≤
      2 * r + |(z i).im - (z j).im| := by
    calc
      _ = |((imaginaryInterpolationGrid Γ k i).im - (z i).im) +
          ((z i).im - (z j).im) + ((z j).im - (imaginaryInterpolationGrid Γ k j).im)| := by
        congr 1
        ring
      _ ≤ |(imaginaryInterpolationGrid Γ k i).im - (z i).im| +
          |(z i).im - (z j).im| + |(z j).im - (imaginaryInterpolationGrid Γ k j).im| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by rw [abs_sub_comm (imaginaryInterpolationGrid Γ k i).im]; linarith only [hi, hj]
  have he : (imaginaryInterpolationGrid Γ k i).im - (imaginaryInterpolationGrid Γ k j).im =
      (2 * Γ / k) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) := by
    simp only [imaginaryInterpolationGrid, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
    ring
  rw [he, abs_mul, abs_of_pos (by positivity : 0 < 2 * Γ / k)] at htri
  simp only [div_eq_mul_inv] at htri hmult hsmall ⊢
  nlinarith only [htri, hmult, hsmall, hr]

/-- An explicit imaginary grid admits a positive literal exponential block after calibration. -/
theorem exists_positive_calibrated_grid {Γ r T R : ℝ} (hΓ : 0 < Γ)
    {k : ℕ} (hk : 0 < k) (hr : 0 < r) (hT : 0 < T) (hR : 0 ≤ R)
    (hsmall : 8 * r ≤ Γ / k)
    (hcontract : 12 * ((k + 1 : ℕ) : ℝ) ≤ (Γ / k) * T)
    (hsize : 2 * (2 * ((k + 1 : ℕ) : ℝ) *
      (|Real.log (Γ / k)| + |Real.log (6 * Γ)|) + 2 * Real.pi) ≤ r * T)
    (hwindow : 2048 * Γ * R ≤ k) :
    ∃ z : Fin (k + 1) → ℂ,
      (∀ i, ‖z i - imaginaryInterpolationGrid Γ k i‖ ≤ r) ∧ Function.Injective z ∧
      (∀ i, |(z i).re| ≤ r ∧ Γ / 2 ≤ (z i).im ∧ (z i).im ≤ 4 * Γ ∧ ‖z i‖ ≤ 4 * Γ) ∧
      (∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (Γ / k) ≤ |(z i).im - (z j).im|) ∧
      ∀ v : ℝ, |v| ≤ R → (3 / 4 : ℝ) ≤ (∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)).re := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : 0 < Γ / k := div_pos hΓ hk0
  have hsΓ : Γ / k ≤ Γ := (div_le_iff₀ hk0).mpr (by nlinarith only [hk1, hΓ])
  have hb : ∀ i, Γ / k ≤ ‖imaginaryInterpolationGrid Γ k i‖ :=
    fun i => hsΓ.trans (imaginaryInterpolationGrid_bounds hΓ hk i).2.2.2.1
  have hbu : ∀ i, ‖imaginaryInterpolationGrid Γ k i‖ ≤ 3 * Γ :=
    fun i => (imaginaryInterpolationGrid_bounds hΓ hk i).2.2.2.2
  have hbi : ∀ i, (imaginaryInterpolationGrid Γ k i).re = 0 :=
    fun i => (imaginaryInterpolationGrid_bounds hΓ hk i).1
  have hbsep : ∀ i j : Fin (k + 1), i ≠ j → Γ / k ≤
      ‖imaginaryInterpolationGrid Γ k i - imaginaryInterpolationGrid Γ k j‖ := by
    intro i j hij
    rw [imaginaryInterpolationGrid_separation hΓ hk]
    have hh := mul_le_mul_of_nonneg_right (one_le_abs_fin_index_sub hij) hs.le
    simp only [div_eq_mul_inv] at hh hs ⊢
    nlinarith only [hh, hs]
  have hsize' : 2 * (2 * (Fintype.card (Fin (k + 1)) : ℝ) *
      (|Real.log (Γ / k)| + |Real.log (2 * (3 * Γ))|) + 2 * Real.pi) ≤ r * T := by
    simpa only [Fintype.card_fin, show 2 * (3 * Γ) = 6 * Γ by ring] using hsize
  obtain ⟨z, hz, hzi, hzne, hcal⟩ := exists_self_consistent_nodes_near_imaginary_grid hs hr hT
    (by positivity : 0 < 3 * Γ) hsmall hb hbu hbi hbsep (by simpa using hcontract) hsize'
  obtain ⟨hgeom, hsep⟩ := calibrated_grid_geometry hΓ hk hr.le hsmall hz
  refine ⟨z, hz, hzi, hgeom, calibrated_grid_ordinate_separation hΓ hk hr.le hsmall hz, ?_⟩
  intro v hv
  apply calibrated_exponential_block_re_ge_three_quarters hk hzi hs
    (by positivity : 0 ≤ 4 * Γ) hR (fun i => (hgeom i).2.2.2) hsep hcal _ _ hv
  · have he : 2 * (4 * Γ) / (Γ / k) = 8 * k := by field_simp [hΓ.ne', hk0.ne'] <;> ring
    exact he.le
  · nlinarith only [hwindow]

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

end
end TheCalibratedNodesStayOnASeparatedImaginaryGrid

section TheGrowingImaginaryGridsMeetTheCalibrationBounds

/-!
## Calibration bounds for growing grids

At height `T=Γ⁴`, a grid with `⌈2048 Γ (R+8)⌉` gaps can be calibrated
inside any depth tolerance larger than `1/(8Γ)`. The elementary bounds
below apply once `R≤L`, `log Γ=L/4`, and `20000 L≤Γ`.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The number of gaps needed to control a window, including the spline support. -/
def calibratedGridDegree (Γ R : ℝ) : ℕ := ⌈2048 * Γ * (R + 8)⌉₊

/-- Explicit scalar conditions for a growing calibrated grid. -/
theorem growing_calibrated_grid_bounds {Γ L R η T : ℝ}
    (hL : 1 ≤ L) (hlog6 : Real.log 6 ≤ L) (hΓL : 20000 * L ≤ Γ)
    (hlogΓ : Real.log Γ = L / 4) (hT : Γ ^ 4 = T)
    (hR0 : 0 ≤ R) (hRL : R ≤ L) (hη : 1 / (8 * Γ) ≤ η) :
    let k := calibratedGridDegree Γ R
    let r := min ((Γ / k) / 8) η
    0 < k ∧ 0 < r ∧ 8 * r ≤ Γ / k ∧
      (k : ℝ) ≤ 18433 * Γ * L ∧ (k : ℝ) ≤ Γ ^ 2 ∧
      12 * ((k + 1 : ℕ) : ℝ) ≤ (Γ / k) * T ∧
      2 * (2 * ((k + 1 : ℕ) : ℝ) *
        (|Real.log (Γ / k)| + |Real.log (6 * Γ)|) + 2 * Real.pi) ≤ r * T ∧
      2048 * Γ * (R + 8) ≤ k := by
  dsimp only
  let k := calibratedGridDegree Γ R
  let s : ℝ := Γ / k
  let r : ℝ := min (s / 8) η
  have hΓ : 0 < Γ := by linarith only [hL, hΓL]
  have hΓ1 : 1 ≤ Γ := by linarith only [hL, hΓL]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have ha0 : 0 ≤ 2048 * Γ * (R + 8) := by positivity
  have hceil : 2048 * Γ * (R + 8) ≤ (k : ℝ) := Nat.le_ceil _
  have hceil' : (k : ℝ) < 2048 * Γ * (R + 8) + 1 := Nat.ceil_lt_add_one ha0
  have hΓk : Γ ≤ (k : ℝ) := by nlinarith only [hceil, mul_nonneg hΓ.le hR0, hΓ]
  have hk0 : (0 : ℝ) < k := hΓ.trans_le hΓk
  have hk : 0 < k := by exact_mod_cast hk0
  have hΓL1 : 1 ≤ Γ * L := by nlinarith only [hΓ1, hL, mul_nonneg (sub_nonneg.mpr hΓ1) (sub_nonneg.mpr hL)]
  have hkL : (k : ℝ) ≤ 18433 * Γ * L := by
    have hmul := mul_le_mul_of_nonneg_left hRL (show 0 ≤ 2048 * Γ by positivity)
    have hmul' := mul_le_mul_of_nonneg_left hL (show 0 ≤ 16384 * Γ by positivity)
    nlinarith only [hceil', hmul, hmul', hΓL1]
  have hkΓ : (k : ℝ) ≤ Γ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hΓL hΓ.le
    nlinarith only [hkL, hh, mul_nonneg hΓ.le hL0]
  have hs0 : 0 < s := div_pos hΓ hk0
  have hs1 : s ≤ 1 := (div_le_one hk0).mpr hΓk
  have hsinv : 1 / Γ ≤ s := by
    dsimp only [s]
    apply (div_le_div_iff₀ hΓ hk0).mpr
    nlinarith only [hkΓ]
  have hrlo : 1 / (8 * Γ) ≤ r := by
    apply le_min
    · have hh := div_le_div_of_nonneg_right hsinv (by norm_num : (0 : ℝ) ≤ 8)
      simpa only [div_div, mul_comm Γ] using hh
    · exact hη
  have hr : 0 < r := (by positivity : 0 < 1 / (8 * Γ)).trans_le hrlo
  have hrsmall : 8 * r ≤ s := by
    have hh : r ≤ s / 8 := min_le_left _ _
    linarith only [hh]
  have hM : ((k + 1 : ℕ) : ℝ) ≤ 2 * Γ ^ 2 := by
    push_cast
    nlinarith only [hkΓ, hΓ1]
  have hΓsq0 : 0 ≤ Γ ^ 2 := sq_nonneg _
  have hΓcube : 0 ≤ Γ ^ 3 := by positivity
  have hsT : Γ ^ 3 ≤ s * T := by
    have hh := mul_le_mul_of_nonneg_right hsinv (show 0 ≤ Γ ^ 4 by positivity)
    rw [hT] at hh
    have he : (1 / Γ) * T = Γ ^ 3 := by rw [← hT]; field_simp [hΓ.ne'] <;> ring
    rwa [he] at hh
  have hrT : Γ ^ 3 / 8 ≤ r * T := by
    have hh := mul_le_mul_of_nonneg_right hrlo (show 0 ≤ Γ ^ 4 by positivity)
    rw [hT] at hh
    have he : (1 / (8 * Γ)) * T = Γ ^ 3 / 8 := by
      rw [← hT]
      field_simp [hΓ.ne'] <;> ring
    rwa [he] at hh
  have hcontract : 12 * ((k + 1 : ℕ) : ℝ) ≤ s * T := by
    have hΓ24 : 24 ≤ Γ := by linarith only [hL, hΓL]
    have hh := mul_le_mul_of_nonneg_right hΓ24 hΓsq0
    nlinarith only [hM, hh, hsT]
  have hlogs0 : Real.log s ≤ 0 := Real.log_nonpos hs0.le hs1
  have hlogs1 : -Real.log Γ ≤ Real.log s := by
    have hh := Real.log_le_log (by positivity : 0 < 1 / Γ) hsinv
    simpa only [one_div, Real.log_inv] using hh
  have habss : |Real.log s| ≤ L / 4 := by
    rw [abs_of_nonpos hlogs0]
    rw [hlogΓ] at hlogs1
    linarith only [hlogs1]
  have hlog6Γ : Real.log (6 * Γ) = Real.log 6 + L / 4 := by
    rw [Real.log_mul (by norm_num) hΓ.ne', hlogΓ]
  have hlog6Γ0 : 0 ≤ Real.log (6 * Γ) := Real.log_nonneg (by linarith only [hΓ1])
  have hH : |Real.log s| + |Real.log (6 * Γ)| ≤ 2 * L := by
    rw [abs_of_nonneg hlog6Γ0, hlog6Γ]
    linarith only [habss, hlog6]
  have hMH := mul_le_mul hM hH (by positivity : 0 ≤ |Real.log s| + |Real.log (6 * Γ)|)
    (by positivity : 0 ≤ 2 * Γ ^ 2)
  have hΓsqL : 1 ≤ Γ ^ 2 * L := by
    have hh := mul_le_mul_of_nonneg_right hΓL1 hΓ.le
    nlinarith only [hh, hΓ1]
  have hΓ256 : 256 * L ≤ Γ := by linarith only [hΓL, hL]
  have h256 := mul_le_mul_of_nonneg_right hΓ256 hΓsq0
  have hsize : 2 * (2 * ((k + 1 : ℕ) : ℝ) *
      (|Real.log s| + |Real.log (6 * Γ)|) + 2 * Real.pi) ≤ r * T := by
    nlinarith only [hMH, Real.pi_lt_four, hΓsqL, h256, hrT]
  exact ⟨hk, hr, hrsmall, hkL, hkΓ, hcontract, hsize, hceil⟩

/-- A polynomial frequency scale supports a calibrated positive block throughout a prescribed window. -/
theorem exists_positive_growing_calibrated_grid {Γ L R η T : ℝ}
    (hL : 1 ≤ L) (hlog6 : Real.log 6 ≤ L) (hΓL : 20000 * L ≤ Γ)
    (hlogΓ : Real.log Γ = L / 4) (hT : Γ ^ 4 = T)
    (hR0 : 0 ≤ R) (hRL : R ≤ L) (hη : 1 / (8 * Γ) ≤ η) :
    let k := calibratedGridDegree Γ R
    ∃ z : Fin (k + 1) → ℂ,
      Function.Injective z ∧
      (∀ i, |(z i).re| ≤ η ∧ Γ / 2 ≤ (z i).im ∧ (z i).im ≤ 4 * Γ ∧ ‖z i‖ ≤ 4 * Γ) ∧
      (∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (Γ / k) ≤ |(z i).im - (z j).im|) ∧
      ∀ v : ℝ, |v| ≤ R + 8 →
        (3 / 4 : ℝ) ≤ (∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)).re := by
  dsimp only
  obtain ⟨hk, hr, hsmall, _, _, hcontract, hsize, hwindow⟩ :=
    growing_calibrated_grid_bounds hL hlog6 hΓL hlogΓ hT hR0 hRL hη
  have hΓ : 0 < Γ := by linarith only [hL, hΓL]
  have hT0 : 0 < T := by rw [← hT]; positivity
  obtain ⟨z, _, hzi, hgeom, hsep, hpos⟩ := exists_positive_calibrated_grid hΓ hk hr hT0
    (by linarith only [hR0] : 0 ≤ R + 8) hsmall hcontract hsize hwindow
  refine ⟨z, hzi, ?_, hsep, hpos⟩
  intro i
  exact ⟨(hgeom i).1.trans (min_le_right _ _), (hgeom i).2⟩

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

end
end TheGrowingImaginaryGridsMeetTheCalibrationBounds

section TheSublogarithmicGridsHaveVanishingNormalizedDensity

/-!
## Sublogarithmic windows and sparse calibrated grids

The scale `Γ=T^(1/4)` leaves enough room for calibration. A window
`R=o(log T)` needs `o(Γ log Γ)` nodes, and its normalized quadratic
mass tends to zero, allowing a tempered sparse sequence of blocks.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Frequency scale used for the growing interpolation blocks. -/
def calibratedGridFrequency (T : ℝ) : ℝ := T ^ (1 / 4 : ℝ)

private theorem gridFrequency_pos {T : ℝ} (hT : 0 < T) : 0 < calibratedGridFrequency T :=
  Real.rpow_pos_of_pos hT _

private theorem gridFrequency_fourth {T : ℝ} (hT : 0 < T) :
    calibratedGridFrequency T ^ 4 = T := by
  unfold calibratedGridFrequency
  rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
  norm_num

private theorem log_gridFrequency {T : ℝ} (hT : 0 < T) :
    Real.log (calibratedGridFrequency T) = Real.log T / 4 := by
  rw [calibratedGridFrequency, Real.log_rpow hT]
  ring

/-- Sublogarithmic radii meet all scalar calibration bounds eventually. -/
theorem eventually_sublogarithmic_grid_parameters {R : ℝ → ℝ}
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop,
      0 < T ∧ 1 ≤ Real.log T ∧ Real.log 6 ≤ Real.log T ∧
      20000 * Real.log T ≤ calibratedGridFrequency T ∧
      Real.log (calibratedGridFrequency T) = Real.log T / 4 ∧
      calibratedGridFrequency T ^ 4 = T ∧ R T ≤ Real.log T ∧
      1 / (8 * calibratedGridFrequency T) ≤ η := by
  have hpower := RHTower.eventually_const_mul_rpow_neg_mul_log_pow_le
    20000 (1 / 4) (by norm_num) 1 (by norm_num : (0 : ℝ) < 1)
  have hdepth := RHTower.eventually_const_mul_rpow_neg_le
    (1 / 8) (1 / 4) (by norm_num) hη
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 6),
    hpower, hdepth, hR.eventually_le_const (by norm_num : (0 : ℝ) < 1)]
    with T hT hL hL6 hp hd hratio
  have hΓ := gridFrequency_pos hT
  have hL0 : 0 < Real.log T := zero_lt_one.trans_le hL
  have he : T ^ (-(1 / 4 : ℝ)) = (calibratedGridFrequency T)⁻¹ :=
    Real.rpow_neg hT.le _
  have hp' : 20000 * Real.log T / calibratedGridFrequency T ≤ 1 := by
    simpa only [he, pow_one, div_eq_mul_inv, mul_left_comm, mul_comm, mul_assoc] using hp
  have hd' : 1 / (8 * calibratedGridFrequency T) ≤ η := by
    simpa only [he, one_div, mul_inv_rev, mul_comm] using hd
  exact ⟨hT, hL, hL6, (div_le_one hΓ).mp hp', log_gridFrequency hT,
    gridFrequency_fourth hT, (div_le_one hL0).mp hratio, hd'⟩

/-- Every sufficiently late sublogarithmic window has a calibrated positive block. -/
theorem eventually_exists_sublogarithmic_calibrated_grid {R : ℝ → ℝ}
    (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop,
      let Γ := calibratedGridFrequency T
      let k := calibratedGridDegree Γ (R T)
      ∃ z : Fin (k + 1) → ℂ,
        Function.Injective z ∧
        (∀ i, |(z i).re| ≤ η ∧ Γ / 2 ≤ (z i).im ∧ (z i).im ≤ 4 * Γ ∧ ‖z i‖ ≤ 4 * Γ) ∧
        (∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (Γ / k) ≤ |(z i).im - (z j).im|) ∧
        ∀ v : ℝ, |v| ≤ R T + 8 →
          (3 / 4 : ℝ) ≤ (∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)).re := by
  filter_upwards [eventually_sublogarithmic_grid_parameters hR hη] with T hT
  exact exists_positive_growing_calibrated_grid hT.2.1 hT.2.2.1 hT.2.2.2.1
    hT.2.2.2.2.1 hT.2.2.2.2.2.1 (hR0 T) hT.2.2.2.2.2.2.1 hT.2.2.2.2.2.2.2

/-- The quadratic normalized grid mass vanishes, permitting a summable choice of blocks. -/
theorem tendsto_sublogarithmic_grid_quadratic_mass {R : ℝ → ℝ}
    (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T => (calibratedGridDegree (calibratedGridFrequency T) (R T) : ℝ) /
      calibratedGridFrequency T ^ 2) atTop (𝓝 0) := by
  have hmajor := RHTower.tendsto_const_mul_rpow_neg_mul_log_pow
    18433 (1 / 4) (by norm_num) 1
  apply squeeze_zero_norm' _ hmajor
  filter_upwards [eventually_sublogarithmic_grid_parameters hR (by norm_num : (0 : ℝ) < 1)]
    with T hT
  have hΓ := gridFrequency_pos hT.1
  have hbound := growing_calibrated_grid_bounds hT.2.1 hT.2.2.1 hT.2.2.2.1
    hT.2.2.2.2.1 hT.2.2.2.2.2.1 (hR0 T) hT.2.2.2.2.2.2.1 hT.2.2.2.2.2.2.2
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (18433 * calibratedGridFrequency T * Real.log T) / calibratedGridFrequency T ^ 2 :=
      div_le_div_of_nonneg_right hbound.2.2.2.1 (by positivity)
    _ = 18433 * (T ^ (-(1 / 4 : ℝ)) * Real.log T ^ 1) := by
      rw [Real.rpow_neg hT.1.le]
      change 18433 * calibratedGridFrequency T * Real.log T / calibratedGridFrequency T ^ 2 =
        18433 * ((calibratedGridFrequency T)⁻¹ * Real.log T ^ 1)
      field_simp [hΓ.ne'] <;> ring

/-- The grid uses a vanishing fraction of the allowed logarithmic local density. -/
theorem tendsto_sublogarithmic_grid_logarithmic_density {R : ℝ → ℝ}
    (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T => (calibratedGridDegree (calibratedGridFrequency T) (R T) : ℝ) /
      (calibratedGridFrequency T * Real.log (calibratedGridFrequency T))) atTop (𝓝 0) := by
  have hinv : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hmajor : Tendsto (fun T => 8192 * (R T / Real.log T) +
      65540 * (Real.log T)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hR.const_mul 8192).add (hinv.const_mul 65540)
  apply squeeze_zero_norm' _ hmajor
  filter_upwards [eventually_sublogarithmic_grid_parameters hR (by norm_num : (0 : ℝ) < 1)]
    with T hT
  let Γ := calibratedGridFrequency T
  have hΓ : 0 < Γ := gridFrequency_pos hT.1
  have hΓ1 : 1 ≤ Γ := by linarith only [hT.2.1, hT.2.2.2.1]
  have hL : 0 < Real.log T := zero_lt_one.trans_le hT.2.1
  have hlog : Real.log Γ = Real.log T / 4 := hT.2.2.2.2.1
  have hlog0 : 0 < Real.log Γ := by rw [hlog]; positivity
  have hc : (calibratedGridDegree Γ (R T) : ℝ) < 2048 * Γ * (R T + 8) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hb : (calibratedGridDegree Γ (R T) : ℝ) ≤ Γ * (2048 * R T + 16385) := by
    nlinarith only [hc, hΓ1]
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (Γ * (2048 * R T + 16385)) / (Γ * Real.log Γ) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = 8192 * (R T / Real.log T) + 65540 * (Real.log T)⁻¹ := by
      rw [hlog]
      field_simp [hΓ.ne', hL.ne'] <;> ring

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

end
end TheSublogarithmicGridsHaveVanishingNormalizedDensity
