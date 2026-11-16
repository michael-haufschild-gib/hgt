import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslatedCorrelationHasADoublePole
import GaloisForLFunctions.MatomakiRadziwill.LFunctionLogDerivStrip
import GaloisForLFunctions.MetaplecticMobiusDescent.TheUnramifiedZetaReciprocalIsBounded

/-!
# Polynomial growth of the cubic cusp scattering

The pole-cleared scattering coefficient is a product of elementary powers,
`(u-1)ζ(u)L(u,χ₋₃)`, and the reciprocal unramified ideal zeta function.
Crude positive-half-plane bounds for `ζ` and `L`, together with absolute
Möbius inversion, give cubic growth for both theta-square cusp subtractions.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicEisenstein FamilyContinuationTheory
  FamilyContinuationTheory.EisensteinNorm


/-- The filled zeta factor times the quadratic `L`-function has cubic growth. -/
theorem zetaPoleFilled_mul_chi3D_bound (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, η ≤ u.re → 2 ≤ |u.im| →
      ‖_root_.RHTower.zetaPoleFilled u * DirichletCharacter.LFunction chi3D u‖ ≤
        C * (1 + ‖u‖) ^ 3 := by
  have hiη : 0 ≤ 1 / η := (one_div_pos.mpr hη).le
  refine ⟨(2 + 1 / η) * (6 * (1 + 1 / η)), by positivity, ?_⟩
  intro u hu ht
  have hu0 : 0 < u.re := hη.trans_le hu
  have hne : u ≠ 1 := by
    intro he
    rw [he, Complex.one_im, abs_zero] at ht
    linarith
  have hz := _root_.RHTower.Sieve.norm_riemannZeta_le_crude_of_re_ge hη hu ht
  have hL := MatomakiRadziwill.norm_LFunction_le_crude chi3D chi3D_ne_one hu0
  have hz' : ‖riemannZeta u‖ ≤ (2 + 1 / η) * (1 + ‖u‖) := by
    calc
      _ ≤ 2 + ‖u‖ / η := hz
      _ ≤ _ := by simp only [div_eq_mul_inv] at hiη ⊢
                  nlinarith only [hiη, norm_nonneg u]
  have hL' : ‖DirichletCharacter.LFunction chi3D u‖ ≤
      (6 * (1 + 1 / η)) * (1 + ‖u‖) := by
    have hdiv := div_le_div_of_nonneg_left (norm_nonneg u) hη hu
    norm_num only [Nat.cast_ofNat] at hL
    calc
      _ ≤ 6 * (1 + ‖u‖ / η) := hL.trans (by nlinarith only [hdiv])
      _ ≤ _ := by simp only [div_eq_mul_inv] at hiη ⊢
                  nlinarith only [hiη, norm_nonneg u]
  have hsub : ‖u - 1‖ ≤ 1 + ‖u‖ := by
    simpa only [norm_one, add_comm] using norm_sub_le u (1 : ℂ)
  rw [_root_.RHTower.zetaPoleFilled_of_ne hne, norm_mul, norm_mul]
  calc
    _ ≤ ((1 + ‖u‖) * ((2 + 1 / η) * (1 + ‖u‖))) *
        ((6 * (1 + 1 / η)) * (1 + ‖u‖)) := by gcongr
    _ = _ := by ring

/-- The cubic scattering coefficient has polynomial growth away from `Re s=1`. -/
theorem clearedScattering_vertical_bound (a : ℝ) (ha : 1 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → 1 ≤ |s.im| →
      ‖clearedScattering s‖ ≤ C * (1 + ‖s‖) ^ 3 := by
  let A : ℝ := (3 : ℝ) ^ (3 * a - 3) - 1
  have hA : 0 < A := by
    have h := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3) (by linarith : 0 < 3 * a - 3)
    dsimp only [A]
    linarith
  obtain ⟨Z, hZ, hz⟩ := unramifiedIdealZeta_inv_bounded (3 * a - 2) (by linarith)
  obtain ⟨L, hL, hl⟩ := zetaPoleFilled_mul_chi3D_bound (3 * a - 3) (by linarith)
  refine ⟨‖(2 : ℂ) / cuspArea‖ * A⁻¹ * 2 * (L * 64) * ‖(3 : ℂ)⁻¹‖ * Z,
    by positivity, ?_⟩
  intro s hs ht
  have hpow : ‖(3 : ℂ) ^ (3 * s - 3)‖ = (3 : ℝ) ^ (3 * s.re - 3) := by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    congr 1
    simp
  have hlow : A ≤ ‖(3 : ℂ) ^ (3 * s - 3) - 1‖ := by
    have hnorm := norm_sub_norm_le ((3 : ℂ) ^ (3 * s - 3)) (1 : ℂ)
    rw [hpow, norm_one] at hnorm
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by linarith : 3 * a - 3 ≤ 3 * s.re - 3)
    dsimp only [A]
    linarith only [hnorm, hp]
  have hdenpos : 0 < ‖(3 : ℂ) ^ (3 * s - 3) - 1‖ := hA.trans_le hlow
  have hinv : ‖((3 : ℂ) ^ (3 * s - 3) - 1)⁻¹‖ ≤ A⁻¹ := by
    rw [norm_inv, ← one_div, ← one_div, div_le_div_iff₀ hdenpos hA]
    simpa only [one_mul] using hlow
  have hnegpow : ‖(3 : ℂ) ^ (-(3 * s - 3))‖ ≤ 1 := by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    have hre : (-(3 * s - 3)).re ≤ 0 := by simp; linarith
    simpa only [Real.rpow_zero, Complex.ofReal_ofNat] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hre
  have hnum : ‖1 - (3 : ℂ) ^ (-(3 * s - 3))‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) ((3 : ℂ) ^ (-(3 * s - 3)))
    rw [norm_one] at h
    linarith only [h, hnegpow]
  have hζ := hz (3 * s - 2) (by simp; linarith)
  have hprod := hl (3 * s - 3) (by simp; linarith) (by
    have him : (3 * s - 3).im = 3 * s.im := by simp
    rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith)
  have harg : 1 + ‖3 * s - 3‖ ≤ 4 * (1 + ‖s‖) := by
    have h := norm_sub_le ((3 : ℂ) * s) (3 : ℂ)
    rw [norm_mul] at h
    norm_num at h
    linarith only [h, norm_nonneg s]
  have hprod' : ‖_root_.RHTower.zetaPoleFilled (3 * s - 3) *
      DirichletCharacter.LFunction chi3D (3 * s - 3)‖ ≤
        (L * 64) * (1 + ‖s‖) ^ 3 := by
    calc
      _ ≤ L * (1 + ‖3 * s - 3‖) ^ 3 := hprod
      _ ≤ L * (4 * (1 + ‖s‖)) ^ 3 := by gcongr
      _ = _ := by ring
  have heq : clearedScattering s =
      (2 / cuspArea) * ((3 : ℂ) ^ (3 * s - 3) - 1)⁻¹ * (1 - (3 : ℂ) ^ (-(3 * s - 3))) *
        (_root_.RHTower.zetaPoleFilled (3 * s - 3) * DirichletCharacter.LFunction chi3D (3 * s - 3)) *
          (3 : ℂ)⁻¹ * (unramifiedIdealZeta (3 * s - 2))⁻¹ := by
    rw [clearedScattering, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ ‖(2 : ℂ) / cuspArea‖ * A⁻¹ * 2 * ((L * 64) * (1 + ‖s‖) ^ 3) *
        ‖(3 : ℂ)⁻¹‖ * Z := by gcongr
    _ = _ := by ring

/-- Both cleared cusp scattering terms have polynomial growth on fixed vertical strips. -/
theorem clearedThetaScattering_vertical_bound (a B : ℝ) (ha : 1 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ B → 1 ≤ |s.im| →
      ‖clearedScatterTotal s‖ ≤ C * (1 + ‖s‖) ^ 3 ∧
      ‖clearedTransScatter s‖ ≤ C * (1 + ‖s‖) ^ 3 := by
  obtain ⟨D, hD, hd⟩ := clearedScattering_vertical_bound a ha
  let Q : ℝ := 3 * (3 : ℝ) ^ (3 * B - 3) + 1
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let C : ℝ := ‖(Real.pi : ℂ)‖ * ‖cuspArea‖ * D
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C * (Q + 1), by positivity, ?_⟩
  intro s hs hsb ht
  have hcorr := hd s hs ht
  have hone : 1 ≤ ‖s - 1‖ := by
    have h : |s.im| ≤ ‖s - 1‖ := by
      simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.abs_im_le_norm (s - 1)
    exact ht.trans h
  have hpi : ‖(Real.pi : ℂ) / (s - 1)‖ ≤ ‖(Real.pi : ℂ)‖ := by
    rw [norm_div]
    exact div_le_self (norm_nonneg _) hone
  have htrans : ‖clearedTransScatter s‖ ≤ C * (1 + ‖s‖) ^ 3 := by
    rw [clearedTransScatter, norm_mul, norm_mul]
    calc
      _ ≤ ‖(Real.pi : ℂ)‖ * ‖cuspArea‖ * (D * (1 + ‖s‖) ^ 3) := by gcongr
      _ = _ := by dsimp only [C]; ring
  have hq : ‖3 * (3 : ℂ) ^ (3 * s - 3) - 1‖ ≤ Q := by
    have hp : ‖(3 : ℂ) ^ (3 * s - 3)‖ ≤ (3 : ℝ) ^ (3 * B - 3) := by
      rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      simp
      linarith
    have h := norm_sub_le ((3 : ℂ) * (3 : ℂ) ^ (3 * s - 3)) (1 : ℂ)
    rw [norm_mul, norm_one] at h
    norm_num only [Complex.norm_ofNat] at h
    dsimp only [Q]
    linarith only [h, hp]
  constructor
  · have heq : clearedScatterTotal s = clearedTransScatter s *
        (3 * (3 : ℂ) ^ (3 * s - 3) - 1) / 2 := rfl
    rw [heq, norm_div, norm_mul]
    norm_num only [Complex.norm_ofNat]
    calc
      _ ≤ (C * (1 + ‖s‖) ^ 3) * Q / 2 := by gcongr
      _ ≤ C * (Q + 1) * (1 + ‖s‖) ^ 3 := by
        nlinarith only [mul_nonneg hC (pow_nonneg (by positivity : 0 ≤ 1 + ‖s‖) 3),
          mul_nonneg (mul_nonneg hC (pow_nonneg (by positivity : 0 ≤ 1 + ‖s‖) 3)) hQ]
  · refine htrans.trans ?_
    have h := mul_nonneg (mul_nonneg hC hQ) (pow_nonneg (by positivity : 0 ≤ 1 + ‖s‖) 3)
    nlinarith only [h]

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
