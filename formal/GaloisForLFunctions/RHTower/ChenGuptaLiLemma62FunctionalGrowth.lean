import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62GammaBounds
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteContour

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

structure CGLLemma62HighStripPoint where
  value : ℂ
  lower : (-1 : ℝ) ≤ value.re
  upper : value.re ≤ 1 / 2
  high : 2 ≤ |value.im|

private theorem cgl_norm_Gamma_real_sub_I (a r : ℝ) :
    ‖Complex.Gamma ((a : ℂ) - (r : ℂ) * I)‖ =
      ‖Complex.Gamma ((a : ℂ) + (r : ℂ) * I)‖ := by
  rw [show (a : ℂ) - (r : ℂ) * I =
      (starRingEnd ℂ) ((a : ℂ) + (r : ℂ) * I) by
        apply Complex.ext <;> simp,
    Complex.Gamma_conj, Complex.norm_conj]

private theorem cglGammaRatio_raw_high (z : ℂ)
    (hlower : (-1 : ℝ) ≤ z.re) (hupper : z.re ≤ 1 / 2)
    (hhigh : 2 ≤ |z.im|) (d : ℝ) (hd : d = 0 ∨ d = 1) :
    ‖Complex.Gamma ((1 - z + (d : ℂ)) / 2)‖ /
        ‖Complex.Gamma ((z + (d : ℂ)) / 2)‖ ≤
      (3 / 2 : ℝ) * Real.exp 8 * z.im ^ 2 := by
  let a : ℝ := (1 - z.re + d) / 2
  let b : ℝ := (z.re + d) / 2 + 2
  let y : ℝ := |z.im| / 2
  let B : ℂ := (z + (d : ℂ)) / 2
  have hy : 1 ≤ y := by
    dsimp only [y]
    linarith
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    rcases hd with rfl | rfl <;> linarith
  have hab : a ≤ b := by
    dsimp only [a, b]
    linarith
  have hwidth : b - a ≤ 2 := by
    dsimp only [a, b]
    linarith
  have hratio :
      ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ ≤ Real.exp 8 :=
    cglLemma62_norm_Gamma_vertical_ratio_le_exp_eight ha0 hab hwidth hy
  have hnumArg :
      (1 - z + (d : ℂ)) / 2 = (a : ℂ) - (z.im / 2 : ℝ) * I := by
    apply Complex.ext
    · dsimp only [a]
      simp
    · dsimp only [a]
      simp
      ring
  have hshiftArg : B + 2 = (b : ℂ) + (z.im / 2 : ℝ) * I := by
    apply Complex.ext
    · dsimp only [B, b]
      simp
    · dsimp only [B, b]
      simp
  have hnumNorm :
      ‖Complex.Gamma ((1 - z + (d : ℂ)) / 2)‖ =
        ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by
    rw [hnumArg]
    rcases le_total 0 z.im with him | him
    · have hyEq : y = z.im / 2 := by
        dsimp only [y]
        rw [abs_of_nonneg him]
      calc
        ‖Complex.Gamma ((a : ℂ) - (z.im / 2 : ℝ) * I)‖ =
            ‖Complex.Gamma ((a : ℂ) + ((z.im / 2 : ℝ) : ℂ) * I)‖ := by
              exact cgl_norm_Gamma_real_sub_I a (z.im / 2)
        _ = ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by rw [hyEq]
    · have hyEq : y = -z.im / 2 := by
        dsimp only [y]
        rw [abs_of_nonpos him]
      calc
        ‖Complex.Gamma ((a : ℂ) - (z.im / 2 : ℝ) * I)‖ =
            ‖Complex.Gamma ((a : ℂ) + ((-z.im / 2 : ℝ) : ℂ) * I)‖ := by
              congr 2
              push_cast
              ring
        _ = ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by rw [hyEq]
  have hshiftNorm :
      ‖Complex.Gamma (B + 2)‖ =
        ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ := by
    rw [hshiftArg]
    rcases le_total 0 z.im with him | him
    · have hyEq : y = z.im / 2 := by
        dsimp only [y]
        rw [abs_of_nonneg him]
      rw [hyEq]
    · have hyEq : y = -z.im / 2 := by
        dsimp only [y]
        rw [abs_of_nonpos him]
      calc
        ‖Complex.Gamma ((b : ℂ) + (z.im / 2 : ℝ) * I)‖ =
            ‖Complex.Gamma ((b : ℂ) - ((-z.im / 2 : ℝ) : ℂ) * I)‖ := by
              congr 2
              push_cast
              ring
        _ = ‖Complex.Gamma ((b : ℂ) + ((-z.im / 2 : ℝ) : ℂ) * I)‖ := by
              exact cgl_norm_Gamma_real_sub_I b (-z.im / 2)
        _ = ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ := by rw [hyEq]
  have hBim : B.im = z.im / 2 := by
    dsimp only [B]
    simp
  have hB0 : B ≠ 0 := by
    intro h
    have him := hBim
    rw [h] at him
    simp at him
    have hz : z.im = 0 := by linarith
    rw [hz] at hhigh
    norm_num at hhigh
  have hB1 : B + 1 ≠ 0 := by
    intro h
    have him : (B + 1).im = z.im / 2 := by rw [Complex.add_im, hBim]; simp
    rw [h] at him
    simp at him
    have hz : z.im = 0 := by linarith
    rw [hz] at hhigh
    norm_num at hhigh
  have hrec : Complex.Gamma (B + 2) = (B + 1) * B * Complex.Gamma B := by
    rw [show B + 2 = (B + 1) + 1 by ring, Complex.Gamma_add_one _ hB1,
      Complex.Gamma_add_one B hB0]
    ring
  have hdenNe : Complex.Gamma B ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have him := hBim
    rw [hm] at him
    simp at him
    have hz : z.im = 0 := by linarith
    rw [hz] at hhigh
    norm_num at hhigh
  have hshiftNe : Complex.Gamma (B + 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have him : (B + 2).im = z.im / 2 := by rw [Complex.add_im, hBim]; simp
    rw [hm] at him
    simp at him
    have hz : z.im = 0 := by linarith
    rw [hz] at hhigh
    norm_num at hhigh
  have hshiftNormNe : ‖Complex.Gamma (B + 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hshiftNe
  have hrecNorm :
      ‖Complex.Gamma (B + 2)‖ = ‖B + 1‖ * ‖B‖ * ‖Complex.Gamma B‖ := by
    rw [hrec, norm_mul, norm_mul]
  have hrawRatio :
      ‖Complex.Gamma ((1 - z + (d : ℂ)) / 2)‖ /
          ‖Complex.Gamma B‖ =
        ‖B‖ * ‖B + 1‖ *
          (‖Complex.Gamma ((1 - z + (d : ℂ)) / 2)‖ /
            ‖Complex.Gamma (B + 2)‖) := by
    rw [hrecNorm] at hshiftNormNe ⊢
    field_simp
  have hBre : B.re = (z.re + d) / 2 := by
    dsimp only [B]
    simp
  have hBimAbs : |B.im| = y := by
    rw [hBim]
    dsimp only [y]
    rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
  have hBreAbs : |B.re| ≤ 1 := by
    rw [abs_le]
    constructor <;> rw [hBre] <;> rcases hd with rfl | rfl <;> linarith
  have hBnorm : ‖B‖ ≤ 1 + y := by
    calc
      ‖B‖ = ‖(B.re : ℂ) + (B.im : ℂ) * I‖ := by rw [Complex.re_add_im]
      _ ≤ ‖(B.re : ℂ)‖ + ‖(B.im : ℂ) * I‖ := norm_add_le _ _
      _ = |B.re| + |B.im| := by simp
      _ ≤ 1 + y := by rw [hBimAbs]; gcongr
  have hB1norm : ‖B + 1‖ ≤ 2 + y := by
    calc
      ‖B + 1‖ ≤ ‖B‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖B‖ + 1 := by norm_num
      _ ≤ (1 + y) + 1 := by gcongr
      _ = 2 + y := by ring
  have hBsimple : 1 + y ≤ 2 * y := by linarith
  have hB1simple : 2 + y ≤ 3 * y := by linarith
  change ‖Complex.Gamma ((1 - z + (d : ℂ)) / 2)‖ /
      ‖Complex.Gamma B‖ ≤ (3 / 2 : ℝ) * Real.exp 8 * z.im ^ 2
  rw [hrawRatio, hnumNorm, hshiftNorm]
  calc
    ‖B‖ * ‖B + 1‖ *
          (‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
            ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖)
    _ ≤ (1 + y) * (2 + y) * Real.exp 8 := by gcongr
    _ ≤ (2 * y) * (3 * y) * Real.exp 8 := by gcongr
    _ = (3 / 2 : ℝ) * Real.exp 8 * z.im ^ 2 := by
      dsimp only [y]
      have habsSq : |z.im| ^ 2 = z.im ^ 2 := sq_abs z.im
      calc
        2 * (|z.im| / 2) * (3 * (|z.im| / 2)) * Real.exp 8 =
            (3 / 2 : ℝ) * Real.exp 8 * |z.im| ^ 2 := by ring
        _ = (3 / 2 : ℝ) * Real.exp 8 * z.im ^ 2 := by rw [habsSq]

private theorem cglGammaFactor_reflection_high (χ : DirichletCharacter ℂ q)
    (z : ℂ) (hlower : (-1 : ℝ) ≤ z.re) (hupper : z.re ≤ 1 / 2)
    (hhigh : 2 ≤ |z.im|) :
    ‖χ⁻¹.gammaFactor (1 - z) / χ.gammaFactor z‖ ≤
      (3 / 2 : ℝ) * Real.exp 8 * z.im ^ 2 := by
  obtain ⟨d, hd, hgamma⟩ := gammaFactor_eq_Gammaℝ χ
  have hpi : Real.pi ^ (z.re - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [Real.pi_gt_three]) (by linarith)
  have hratio :
      ‖Complex.Gamma ((1 - z + (d : ℂ)) / 2)‖ /
          ‖Complex.Gamma ((z + (d : ℂ)) / 2)‖ ≤
        (3 / 2 : ℝ) * Real.exp 8 * z.im ^ 2 :=
    cglGammaRatio_raw_high z hlower hupper hhigh d hd
  have hnorm :
      ‖χ⁻¹.gammaFactor (1 - z) / χ.gammaFactor z‖ =
        Real.pi ^ (z.re - 1 / 2) *
          (‖Complex.Gamma ((1 - z + (d : ℂ)) / 2)‖ /
            ‖Complex.Gamma ((z + (d : ℂ)) / 2)‖) := by
    rw [norm_div, gammaFactor_inv, hgamma (1 - z), hgamma z,
      GaloisForLFunctions.HTGeometry.norm_Gammaℝ,
      GaloisForLFunctions.HTGeometry.norm_Gammaℝ]
    have hre1 : -((1 - z + (d : ℂ)).re) / 2 = -(1 - z.re + d) / 2 := by
      simp [Complex.sub_re, Complex.add_re]
    have hre2 : -((z + (d : ℂ)).re) / 2 = -(z.re + d) / 2 := by
      simp [Complex.add_re]
    rw [hre1, hre2, mul_div_mul_comm, ← Real.rpow_sub Real.pi_pos]
    congr 2
    ring
  rw [hnorm]
  calc
    Real.pi ^ (z.re - 1 / 2) *
          (‖Complex.Gamma ((1 - z + (d : ℂ)) / 2)‖ /
            ‖Complex.Gamma ((z + (d : ℂ)) / 2)‖) ≤
        1 * (‖Complex.Gamma ((1 - z + (d : ℂ)) / 2)‖ /
            ‖Complex.Gamma ((z + (d : ℂ)) / 2)‖) := by
          gcongr
    _ ≤ 1 * ((3 / 2 : ℝ) * Real.exp 8 * z.im ^ 2) := by gcongr
    _ = (3 / 2 : ℝ) * Real.exp 8 * z.im ^ 2 := by ring

theorem cglLemma62_primitiveFunctionalFactor_highHeight_bound
    (P : CGLLemma62PrimitiveCharacter) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : CGLLemma62HighStripPoint,
      ‖cglLemma62PrimitiveFunctionalFactor P z.value‖ ≤ C * z.value.im ^ 2 := by
  let C : ℝ := (P.modulus.value : ℝ) ^ (3 / 2 : ℝ) * ‖P.character.rootNumber‖ *
    ((3 / 2 : ℝ) * Real.exp 8)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, fun z => ?_⟩
  have hqone : (1 : ℝ) ≤ P.modulus.value := by
    exact_mod_cast P.modulus.positive
  have hqpos : (0 : ℝ) < P.modulus.value := by
    exact_mod_cast P.modulus.positive
  have hqpow :
      ‖(P.modulus.value : ℂ) ^ ((1 / 2 : ℂ) - z.value)‖ ≤
        (P.modulus.value : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos P.modulus.positive]
    apply Real.rpow_le_rpow_of_exponent_le hqone
    have hre : ((1 / 2 : ℂ) - z.value).re = (1 / 2 : ℝ) - z.value.re := by
      rw [Complex.sub_re]
      norm_num
    rw [hre]
    linarith [z.lower]
  have hgamma := cglGammaFactor_reflection_high P.character z.value
    z.lower z.upper z.high
  rw [norm_div] at hgamma
  unfold cglLemma62PrimitiveFunctionalFactor
  rw [norm_div, norm_mul, norm_mul]
  calc
    ‖(P.modulus.value : ℂ) ^ ((1 / 2 : ℂ) - z.value)‖ * ‖P.character.rootNumber‖ *
          ‖P.character⁻¹.gammaFactor (1 - z.value)‖ /
            ‖P.character.gammaFactor z.value‖ =
        ‖(P.modulus.value : ℂ) ^ ((1 / 2 : ℂ) - z.value)‖ * ‖P.character.rootNumber‖ *
          (‖P.character⁻¹.gammaFactor (1 - z.value)‖ /
            ‖P.character.gammaFactor z.value‖) := by ring
    _ ≤ (P.modulus.value : ℝ) ^ (3 / 2 : ℝ) * ‖P.character.rootNumber‖ *
          ((3 / 2 : ℝ) * Real.exp 8 * z.value.im ^ 2) := by gcongr
    _ = C * z.value.im ^ 2 := by
      dsimp only [C]
      ring

end

end RHTower

