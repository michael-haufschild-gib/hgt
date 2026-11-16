import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTwistedSquarefreeCombinationHasASimplePole
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane

/-!
# The pole-cleared cube zeta factor

The regularized finite-order Hecke function equals the filled Dedekind product.
The Hecke zero-free half-plane then excludes zeros of the cube-removal factor
on `Re s > 5/4`; its reciprocal has quadratic vertical growth. In the
squarefree variable `w=s/2`, this permits contours to the right of `5/8`.
-/

noncomputable section
open Filter Set Topology
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover
open MetaplecticMobiusDescent MetaplecticMobiusDescent.CubicEisenstein
  FamilyContinuationTheory FamilyContinuationTheory.EisensteinNorm

/-- The finite-order Hecke completion and the filled Dedekind product agree globally. -/
theorem regularizedIdealZeta_eq_filled_product (s : ℂ) :
    HeckeBoundary.regularizedIdealZeta s =
      _root_.RHTower.zetaPoleFilled s * DirichletCharacter.LFunction chi3D s := by
  have hf : AnalyticOnNhd ℂ HeckeBoundary.regularizedIdealZeta univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr HeckeBoundary.regularizedIdealZeta_differentiable
  have hg : AnalyticOnNhd ℂ (fun s => _root_.RHTower.zetaPoleFilled s *
      DirichletCharacter.LFunction chi3D s) univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (_root_.RHTower.differentiable_zetaPoleFilled.mul (DirichletCharacter.differentiable_LFunction chi3D_ne_one))
  have hev : HeckeBoundary.regularizedIdealZeta =ᶠ[𝓝 (2 : ℂ)]
      (fun s => _root_.RHTower.zetaPoleFilled s * DirichletCharacter.LFunction chi3D s) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz1 : z ≠ 1 := by intro he; rw [he, Complex.one_re] at hz; exact lt_irrefl _ hz
    rw [HeckeBoundary.regularizedIdealZeta_eq z hz, fullIdealZeta_eq_dedekindZeta z hz,
      dedekindZeta_thirdCyclotomic (CyclotomicField 3 ℚ) hz,
      _root_.RHTower.zetaPoleFilled_of_ne hz1]
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (mem_univ (2 : ℂ)) hev (mem_univ s)


/-- Cube removal introduces no poles to the right of `Re s=5/4`. -/
theorem clearedCubeZeta_ne_zero_right_of_five_fourths (s : ℂ) (hs : 5 / 4 < s.re) :
    clearedCubeZeta s ≠ 0 := by
  let u : ℂ := 3 * (s / 2) - 1
  have hu : 7 / 8 < u.re := by dsimp only [u]; rw [cubeZeta_re]; linarith
  have hu0 : 0 < u.re := by linarith
  have hram : 1 - (3 : ℂ) ^ (-u) ≠ 0 := by
    have hnorm : ‖(3 : ℂ) ^ (-u)‖ < 1 := by
      rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by rw [Complex.neg_re]; linarith only [hu0])
    intro he
    rw [← sub_eq_zero.mp he, norm_one] at hnorm
    exact lt_irrefl _ hnorm
  have hreg : HeckeBoundary.regularizedIdealZeta u ≠ 0 := by
    by_cases hu1 : u = 1
    · rw [hu1]
      exact HeckeOrigin.poleRemoved_one_ne_zero HeckeBoundary.trivialCharacter rfl
    · have h0 : u ≠ 0 := by intro he; rw [he, Complex.zero_re] at hu0; exact lt_irrefl _ hu0
      rw [HeckeBoundary.regularizedIdealZeta, HeckeOrigin.poleRemoved_eq _ h0 hu1]
      apply mul_ne_zero (sub_ne_zero.mpr hu1)
      exact SubSevenEighthsZeroFree.hecke_ne_zero_of_sub_seven_eighths_lt_re
        HeckeBoundary.trivialCharacter u (by linarith) (Or.inl hu1)
  change (1 - (3 : ℂ) ^ (-u)) *
    (_root_.RHTower.zetaPoleFilled u * DirichletCharacter.LFunction chi3D u) ≠ 0
  rw [← regularizedIdealZeta_eq_filled_product]
  exact mul_ne_zero hram hreg

/-- The reciprocal pole-cleared cube zeta factor has quadratic vertical growth. -/
theorem clearedCubeZeta_inv_vertical_bound (a : ℝ) (ha : 5 / 4 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → 1 ≤ |s.im| →
      ‖(clearedCubeZeta s)⁻¹‖ ≤ C * (1 + |s.im| ^ 2) := by
  let η : ℝ := 3 * (a / 2) - 1
  have hη : 7 / 8 < η := by dsimp only [η]; linarith
  have hβ : HeckeZeroSupremum.beta < η :=
    SubSevenEighthsZeroFree.hecke_beta_le_sub_seven_eighths.trans_lt (by linarith)
  obtain ⟨D, hD, hd⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    HeckeBoundary.trivialCharacter η hβ
  let A : ℝ := 1 - (3 : ℝ) ^ (-η)
  have hA : 0 < A := by
    have h := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3)
      (by linarith : -η < 0)
    dsimp only [A]
    linarith only [h]
  refine ⟨A⁻¹ * (3 * D), by positivity, ?_⟩
  intro s hs ht
  let u : ℂ := 3 * (s / 2) - 1
  have hu : η ≤ u.re := by dsimp only [u, η]; rw [cubeZeta_re]; linarith
  have hui : u.im = (3 / 2) * s.im := by dsimp only [u]; simp; ring
  have hui1 : 1 ≤ |u.im| := by
    rw [hui, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    linarith
  have hu1 : u ≠ 1 := by intro he; rw [he, Complex.one_im, abs_zero] at hui1; linarith
  have hu0 : u ≠ 0 := by intro he; rw [he, Complex.zero_im, abs_zero] at hui1; linarith
  have hweight : ‖(3 : ℂ) ^ (-u)‖ ≤ (3 : ℝ) ^ (-η) := by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hu)
  have hlow : A ≤ ‖1 - (3 : ℂ) ^ (-u)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((3 : ℂ) ^ (-u))
    rw [norm_one] at h
    dsimp only [A]
    linarith only [h, hweight]
  have hram : ‖(1 - (3 : ℂ) ^ (-u))⁻¹‖ ≤ A⁻¹ := by
    rw [norm_inv, ← one_div, ← one_div, div_le_div_iff₀ (hA.trans_le hlow) hA]
    simpa only [one_mul] using hlow
  have hden : 1 ≤ ‖u - 1‖ := by
    have h : |u.im| ≤ ‖u - 1‖ := by
      simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.abs_im_le_norm (u - 1)
    exact hui1.trans h
  have hdeninv : ‖(u - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv, ← one_div]
    exact div_le_self zero_le_one hden
  have hr := hd u hu
  rw [HeckeReciprocal.reciprocal_eq_inv _ hu0 hu1] at hr
  have hreg : ‖(HeckeBoundary.regularizedIdealZeta u)⁻¹‖ ≤
      D * (1 + |u.im| ^ 2) := by
    rw [HeckeBoundary.regularizedIdealZeta, HeckeOrigin.poleRemoved_eq _ hu0 hu1,
      mul_inv_rev, norm_mul]
    calc
      _ ≤ (D * (1 + |u.im| ^ 2)) * 1 := by gcongr
      _ = _ := mul_one _
  have hheight : 1 + |u.im| ^ 2 ≤ 3 * (1 + |s.im| ^ 2) := by
    rw [hui, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    nlinarith only [sq_nonneg |s.im|]
  have heq : clearedCubeZeta s = (1 - (3 : ℂ) ^ (-u)) * HeckeBoundary.regularizedIdealZeta u := by
    rw [regularizedIdealZeta_eq_filled_product]
    rfl
  rw [heq, mul_inv_rev, norm_mul]
  calc
    _ ≤ (D * (3 * (1 + |s.im| ^ 2))) * A⁻¹ :=
      mul_le_mul (hreg.trans (mul_le_mul_of_nonneg_left hheight hD)) hram
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
