import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheExponentialInterpolationErrorIsSmallAtDenseGrids

/-!
# Geometry of calibrated imaginary grids

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
