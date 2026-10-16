import GaloisForLFunctions.RHTower.DeningerMeyerXiContourHeights
import GaloisForLFunctions.RHTower.DeningerMeyerGaussianSourceApproximation
import GaloisForLFunctions.HTGeometry.LagrangeRectangleContour

/-! # Gaussian quotient control on the actual Xi contour exhaustion -/

open Complex Set Filter Topology

namespace RHTower
noncomputable section

def deningerXiContourLeft (t : ℝ) : ℂ := -1+(t : ℂ)*I
def deningerXiContourRight (t : ℝ) : ℂ := 2+(t : ℂ)*I

@[simp] theorem deningerXiContourLeft_re (t : ℝ) : (deningerXiContourLeft t).re = -1 := by
  simp [deningerXiContourLeft]
@[simp] theorem deningerXiContourLeft_im (t : ℝ) : (deningerXiContourLeft t).im = t := by
  simp [deningerXiContourLeft]
@[simp] theorem deningerXiContourRight_re (t : ℝ) : (deningerXiContourRight t).re = 2 := by
  simp [deningerXiContourRight]
@[simp] theorem deningerXiContourRight_im (t : ℝ) : (deningerXiContourRight t).im = t := by
  simp [deningerXiContourRight]

theorem deningerXiContour_border_geometry {l h : ℝ} (hlh : l ≤ h) {z : ℂ}
    (hz : z ∈ RectangleBorder (deningerXiContourLeft l) (deningerXiContourRight h)) :
    -1 ≤ z.re ∧ z.re ≤ 2 ∧ l ≤ z.im ∧ z.im ≤ h ∧
      (z.re = -1 ∨ z.re = 2 ∨ z.im = l ∨ z.im = h) := by
  obtain ⟨hre, him⟩ := rectangleBorder_subset_rectangle _ _ hz
  have hr : z.re ∈ Icc (-1 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] using hre
  have hi : z.im ∈ Icc l h := by
    simpa [uIcc_of_le hlh] using him
  refine ⟨hr.1, hr.2, hi.1, hi.2, ?_⟩
  rcases hz with ((hz | hz) | hz) | hz
  · exact Or.inr (Or.inr (Or.inl (by simpa using hz.2)))
  · exact Or.inl (by simpa using hz.1)
  · exact Or.inr (Or.inr (Or.inr (by simpa using hz.2)))
  · exact Or.inr (Or.inl (by simpa using hz.1))

namespace DeningerMeyerXiContourSchedule

variable (S : DeningerMeyerXiContourSchedule)

theorem band_nonzero {l h : ℝ} (hlh : l ≤ h)
    (hl : ∃ n : ℕ, |l| = S.height n) (hh : ∃ n : ℕ, |h| = S.height n)
    {z : ℂ} (hz : z ∈ RectangleBorder (deningerXiContourLeft l) (deningerXiContourRight h)) :
    xi z ≠ 0 := by
  obtain ⟨hr₁, hr₂, _, _, he⟩ := deningerXiContour_border_geometry hlh hz
  rcases he with he | he | he | he
  · exact (deningerXiContour_inverse_of_floor (P := 1) (t := |z.im|)
      (by simpa using deningerXiContour_edge_floor z (Or.inl he))).1
  · exact (deningerXiContour_inverse_of_floor (P := 1) (t := |z.im|)
      (by simpa using deningerXiContour_edge_floor z (Or.inr he))).1
  · obtain ⟨n, hn⟩ := hl
    exact S.horizontal_ne_zero n hr₁ hr₂ (by rw [he]; exact hn)
  · obtain ⟨n, hn⟩ := hh
    exact S.horizontal_ne_zero n hr₁ hr₂ (by rw [he]; exact hn)

theorem inverse_near (n : ℕ) {z : ℂ} (hr₁ : -1 ≤ z.re) (hr₂ : z.re ≤ 2)
    (hi : |z.im| ≤ S.height n+5)
    (he : z.re = -1 ∨ z.re = 2 ∨ |z.im| = S.height n ∨ |z.im| = S.height (n+1)) :
    xi z ≠ 0 ∧ ‖(xi z)⁻¹‖ ≤
      3*Real.pi*(S.height n+5)^S.exponent*Real.exp (Real.pi*(S.height n+5)/4) := by
  have hP : 1 ≤ (S.height n+5)^S.exponent := one_le_pow₀ (by linarith [S.height_pos n])
  have hemono (t : ℝ) (ht : t ≤ S.height n+5) :
      Real.exp (-(Real.pi*(S.height n+5)/4))/(3*Real.pi) ≤
        Real.exp (-(Real.pi*t/4))/(3*Real.pi) := by
    apply div_le_div₀ (Real.exp_pos _).le ?_ (by positivity) le_rfl
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr ht)]
  apply deningerXiContour_inverse_of_floor
  rcases he with he | he | he | he
  · calc
      Real.exp (-(Real.pi*(S.height n+5)/4))/(3*Real.pi) ≤
          Real.exp (-(Real.pi*|z.im|/4))/(3*Real.pi) := hemono _ hi
      _ ≤ ‖xi z‖ := deningerXiContour_edge_floor z (Or.inl he)
      _ ≤ (S.height n+5)^S.exponent*‖xi z‖ := by
        simpa using mul_le_mul_of_nonneg_right hP (norm_nonneg (xi z))
  · calc
      Real.exp (-(Real.pi*(S.height n+5)/4))/(3*Real.pi) ≤
          Real.exp (-(Real.pi*|z.im|/4))/(3*Real.pi) := hemono _ hi
      _ ≤ ‖xi z‖ := deningerXiContour_edge_floor z (Or.inr he)
      _ ≤ (S.height n+5)^S.exponent*‖xi z‖ := by
        simpa using mul_le_mul_of_nonneg_right hP (norm_nonneg (xi z))
  · calc
      Real.exp (-(Real.pi*(S.height n+5)/4))/(3*Real.pi) ≤
          Real.exp (-(Real.pi*S.height n/4))/(3*Real.pi) := hemono _ (by linarith)
      _ ≤ (S.height n)^S.exponent*‖xi z‖ := S.floor_abs n hr₁ hr₂ he
      _ ≤ (S.height n+5)^S.exponent*‖xi z‖ := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (S.height_pos n).le (by linarith) _) (norm_nonneg _)
  · have hnext : S.height (n+1) ≤ S.height n+5 := by linarith [(S.height_next_gap n).2]
    calc
      Real.exp (-(Real.pi*(S.height n+5)/4))/(3*Real.pi) ≤
          Real.exp (-(Real.pi*S.height (n+1)/4))/(3*Real.pi) := hemono _ hnext
      _ ≤ (S.height (n+1))^S.exponent*‖xi z‖ := S.floor_abs (n+1) hr₁ hr₂ he
      _ ≤ (S.height n+5)^S.exponent*‖xi z‖ := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (S.height_pos (n+1)).le hnext _) (norm_nonneg _)

theorem upper_geometry (n : ℕ) {z : ℂ}
    (hz : z ∈ RectangleBorder (deningerXiContourLeft (S.height n))
      (deningerXiContourRight (S.height (n+1)))) :
    -1 ≤ z.re ∧ z.re ≤ 2 ∧ S.height n ≤ |z.im| ∧ |z.im| ≤ S.height n+5 ∧
      (z.re = -1 ∨ z.re = 2 ∨ |z.im| = S.height n ∨ |z.im| = S.height (n+1)) := by
  obtain ⟨hr₁, hr₂, hi₁, hi₂, he⟩ := deningerXiContour_border_geometry
    (by linarith [(S.height_next_gap n).1] : S.height n ≤ S.height (n+1)) hz
  have hi₀ : 0 ≤ z.im := (S.height_pos n).le.trans hi₁
  simpa only [abs_of_nonneg hi₀] using
    (show -1 ≤ z.re ∧ z.re ≤ 2 ∧ S.height n ≤ z.im ∧ z.im ≤ S.height n+5 ∧
      (z.re = -1 ∨ z.re = 2 ∨ z.im = S.height n ∨ z.im = S.height (n+1)) from
      ⟨hr₁, hr₂, hi₁, by linarith [(S.height_next_gap n).2], he⟩)

theorem lower_geometry (n : ℕ) {z : ℂ}
    (hz : z ∈ RectangleBorder (deningerXiContourLeft (-S.height (n+1)))
      (deningerXiContourRight (-S.height n))) :
    -1 ≤ z.re ∧ z.re ≤ 2 ∧ S.height n ≤ |z.im| ∧ |z.im| ≤ S.height n+5 ∧
      (z.re = -1 ∨ z.re = 2 ∨ |z.im| = S.height n ∨ |z.im| = S.height (n+1)) := by
  obtain ⟨hr₁, hr₂, hi₁, hi₂, he⟩ := deningerXiContour_border_geometry
    (by linarith [(S.height_next_gap n).1] : -S.height (n+1) ≤ -S.height n) hz
  have hi₀ : z.im ≤ 0 := by linarith [S.height_pos n]
  rw [abs_of_nonpos hi₀]
  refine ⟨hr₁, hr₂, by linarith, by linarith [(S.height_next_gap n).2], ?_⟩
  rcases he with he | he | he | he
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (Or.inr (by linarith)))
  · exact Or.inr (Or.inr (Or.inl (by linarith)))

/-- Gaussian damping pays the reciprocal Xi cost on both actual shell contours. -/
theorem gaussian_quotient (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (n : ℕ) (z : ℂ),
      (z ∈ RectangleBorder (deningerXiContourLeft (S.height n))
        (deningerXiContourRight (S.height (n+1))) ∨
       z ∈ RectangleBorder (deningerXiContourLeft (-S.height (n+1)))
        (deningerXiContourRight (-S.height n))) →
      ‖deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g) z / xi z‖ ≤
        A*(S.height n+5)^S.exponent*
          Real.exp ((Real.pi/4)*S.height n-ε*(S.height n)^2) := by
  obtain ⟨C, hC, hM⟩ := deningerMeyerStrongLogMellin_strip_bound g (-1) 2
  let A := C*3*Real.pi*Real.exp (4*ε+5*Real.pi/4)
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro n z hz
  have hgeom : -1 ≤ z.re ∧ z.re ≤ 2 ∧ S.height n ≤ |z.im| ∧ |z.im| ≤ S.height n+5 ∧
      (z.re = -1 ∨ z.re = 2 ∨ |z.im| = S.height n ∨ |z.im| = S.height (n+1)) := by
    rcases hz with hz | hz
    · exact S.upper_geometry n hz
    · exact S.lower_geometry n hz
  obtain ⟨hr₁, hr₂, hi₁, hi₂, he⟩ := hgeom
  have hsq : z.re^2 ≤ 4 := by
    have hprod := mul_nonneg (show 0 ≤ 2-z.re by linarith)
      (show 0 ≤ z.re+2 by linarith)
    nlinarith
  have hisq : (S.height n)^2 ≤ z.im^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (S.height_pos n).le hi₁ 2
  have hξ := (S.inverse_near n hr₁ hr₂ hi₂ he).2
  have hF : ‖deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g) z‖ ≤
      C*Real.exp (4*ε-ε*(S.height n)^2) := by
    rw [deningerGaussianMellinRegularization, norm_mul, Complex.norm_exp]
    have hex : ((ε : ℂ)*z^2).re = ε*(z.re^2-z.im^2) := by
      simp [pow_two, Complex.mul_re, Complex.mul_im]
    rw [hex, mul_comm C]
    exact mul_le_mul (Real.exp_le_exp.mpr (by nlinarith)) (hM z hr₁ hr₂)
      (norm_nonneg _) (Real.exp_pos _).le
  rw [div_eq_mul_inv, norm_mul]
  calc
    ‖deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g) z‖*‖(xi z)⁻¹‖ ≤
        (C*Real.exp (4*ε-ε*(S.height n)^2))*
          (3*Real.pi*(S.height n+5)^S.exponent*Real.exp (Real.pi*(S.height n+5)/4)) :=
      mul_le_mul hF hξ (norm_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
    _ = (C*3*Real.pi*(S.height n+5)^S.exponent)*
        Real.exp ((4*ε-ε*(S.height n)^2)+(Real.pi*(S.height n+5)/4)) := by
      rw [Real.exp_add]
      ring
    _ = A*(S.height n+5)^S.exponent*
        Real.exp ((Real.pi/4)*S.height n-ε*(S.height n)^2) := by
      rw [show (4*ε-ε*(S.height n)^2)+(Real.pi*(S.height n+5)/4) =
        (4*ε+5*Real.pi/4)+((Real.pi/4)*S.height n-ε*(S.height n)^2) by ring,
        Real.exp_add]
      dsimp [A]
      ring

end DeningerMeyerXiContourSchedule

end
end RHTower
