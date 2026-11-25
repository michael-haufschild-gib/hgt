import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.PerronEdgeIntegrals
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.PerronGoodHeight
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.PerronOriginRemainder
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.PerronResidueRectangle

/-! Shifting the unsmoothed Perron integral to the left edge gives a conductor-uniform error. -/

open Complex DirichletCharacter MeasureTheory Set

open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

def primitivePerronVertical {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (u T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t in -T..T,
    primitivePerronIntegrand χ u ((primitivePerronAbscissa u : ℂ) + t * I)

theorem norm_perron_vertical_factor_le_one : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
  rw [norm_div, norm_one, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    div_le_one (by positivity)]
  linarith only [Real.pi_gt_three]

private theorem norm_contour_error_le (H₁ H₂ V W M Z E : ℂ)
    (h : (1 / (2 * Real.pi * I) : ℂ) * (H₁ - H₂ + I * V - I * W) = M - Z - E) :
    ‖(1 / (2 * Real.pi) : ℂ) * V - M + Z‖ ≤ ‖E‖ + ‖W‖ + ‖H₁‖ + ‖H₂‖ := by
  let a : ℂ := 1 / (2 * Real.pi * I)
  let b : ℂ := 1 / (2 * Real.pi)
  have hI : a * I = b := by
    dsimp only [a, b]
    field_simp [I_ne_zero, ofReal_ne_zero.mpr Real.pi_ne_zero]
  have e : b * V - M + Z = -E + (b * W - a * (H₁ - H₂)) := by
    change a * (H₁ - H₂ + I * V - I * W) = M - Z - E at h
    linear_combination h - (V - W) * hI
  have hb : ‖b‖ ≤ 1 := norm_perron_vertical_factor_le_one
  have ha : ‖a‖ ≤ 1 := by
    calc
      ‖a‖ = ‖a * I‖ := by rw [norm_mul, norm_I, mul_one]
      _ ≤ _ := by simpa only [hI] using hb
  have hW : ‖b * W‖ ≤ ‖W‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hb
  have hH : ‖a * (H₁ - H₂)‖ ≤ ‖H₁‖ + ‖H₂‖ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (norm_sub_le _ _)
  change ‖b * V - M + Z‖ ≤ _
  rw [e]
  exact (norm_add_le _ _).trans
    ((add_le_add (norm_neg _).le ((norm_sub_le _ _).trans (add_le_add hW hH))).trans_eq (by ring))

/-- At a nearby good height the right-edge Perron integral equals the zero sum and principal term up to a uniform error. -/
theorem primitive_perron_shift :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ u T : ℝ, 2 ≤ T → T ≤ u → ∃ U : ℝ, T ≤ U ∧ U ≤ T + 1 ∧
        ‖primitivePerronVertical χ u U - (if χ = 1 then (u : ℂ) else 0) +
          ∑ᶠ ρ ∈ primitiveInteriorZeros χ U, (analyticOrderNatAt χ.LFunction ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
          C * (u * Real.log ((N : ℝ) * u * T) ^ 2 / T + Real.log ((N : ℝ) * u) +
            ∑ᶠ ρ ∈ primitiveInteriorZeros χ 1, (analyticOrderNatAt χ.LFunction ρ : ℝ) / ‖ρ‖) := by
  obtain ⟨A, hA, Hhor⟩ := primitive_logDeriv_good_height
  obtain ⟨B, hB, Hleft⟩ := norm_primitivePerron_left
  obtain ⟨C, hC, H0⟩ := primitive_logDeriv_near_origin
  refine ⟨1 + C + 6 * B + 18 * A, by positivity, ?_⟩
  intro N _ χ hχ u T hT hTu
  have hu : 2 ≤ u := hT.trans hTu
  have hT₀ : 0 < T := by linarith only [hT]
  have hu₀ : 0 < u := hT₀.trans_le hTu
  obtain ⟨U, hU₁, hU₂, huBound⟩ := Hhor N χ hχ T hT
  obtain ⟨m, g, hm, hg, he, h0⟩ := H0 N χ hχ
  refine ⟨U, hU₁, hU₂, ?_⟩
  let c := primitivePerronAbscissa u
  obtain ⟨hc, hc₂, -⟩ := primitivePerronAbscissa_bounds hu
  have hU : 0 < U := hT₀.trans_le hU₁
  let F := primitivePerronIntegrand χ u
  let E : ℂ := (m : ℂ) * (Real.log u : ℂ) + g 0
  let Z := ∑ᶠ ρ ∈ primitiveInteriorZeros χ U, (analyticOrderNatAt χ.LFunction ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)
  let M : ℂ := if χ = 1 then (u : ℂ) else 0
  let H (y : ℝ) := ∫ x : ℝ in (-(1 / 2 : ℝ))..c, F ((x : ℂ) + y * I)
  let V := ∫ t : ℝ in -U..U, F ((c : ℂ) + t * I)
  let W := ∫ t : ℝ in -U..U, F (((-(1 / 2 : ℝ)) : ℂ) + t * I)
  have rect := primitive_perron_rectangle hχ hu₀ hc hU hg he
    (fun s h₁ h₂ h₃ => (huBound s h₁ (h₂.trans (hc₂.trans (by norm_num))) h₃).1)
  have hrect : (1 / (2 * Real.pi * I) : ℂ) * (H (-U) - H U + I * V - I * W) = M - Z - E := by
    simpa only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul, Complex.ofReal_neg,
      H, V, W, c, F, E, Z, M]
      using rect
  have key := norm_contour_error_le _ _ _ _ _ _ _ hrect
  let X := (N : ℝ) * u * T
  let L := Real.log X
  let Q := u * L ^ 2 / T
  let R := Real.log ((N : ℝ) * u)
  let S := ∑ᶠ ρ ∈ primitiveInteriorZeros χ 1, (analyticOrderNatAt χ.LFunction ρ : ℝ) / ‖ρ‖
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hNT : (2 : ℝ) ≤ (N : ℝ) * T := by nlinarith only [hN, hT, mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (sub_nonneg.mpr hT)]
  have hX : 4 ≤ X := by
    dsimp only [X]
    have h := mul_le_mul hNT hu (by linarith only [hu]) (by positivity : 0 ≤ (N : ℝ) * T)
    nlinarith only [h]
  have hNTX : (N : ℝ) * T ≤ X := by
    dsimp only [X]
    have h := mul_le_mul_of_nonneg_left (by linarith only [hu] : (1 : ℝ) ≤ u)
      (by positivity : 0 ≤ (N : ℝ) * T)
    nlinarith only [h]
  have hTX : T ≤ X := (le_mul_of_one_le_left hT₀.le hN).trans hNTX
  have hL : 1 ≤ L :=
    (Real.le_log_iff_exp_le (by linarith only [hX])).mpr
      ((by linarith only [Real.exp_one_lt_d9] : Real.exp 1 ≤ 4).trans hX)
  have hlogNT := Real.log_le_log (by linarith only [hNT]) hNTX
  have hlogNT₀ : 0 ≤ Real.log ((N : ℝ) * T) := Real.log_nonneg (by linarith only [hNT])
  have hQ₀ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hR₀ : 0 ≤ R := Real.log_nonneg (by
    exact (by linarith only [hu] : (1 : ℝ) ≤ u).trans (le_mul_of_one_le_left hu₀.le hN))
  have hS₀ : 0 ≤ S := finsum_nonneg fun _ => finsum_nonneg fun _ => by positivity
  have hQL : L ^ 2 ≤ Q := by
    dsimp only [Q]
    rw [le_div_iff₀ hT₀]
    exact (mul_comm _ _).le.trans (mul_le_mul_of_nonneg_right hTu (sq_nonneg _))
  have hE : ‖E‖ ≤ (1 + C) * (R + S) := by
    have hlogu : 0 ≤ Real.log u := Real.log_nonneg (by linarith only [hu])
    have hmu : ‖(m : ℂ) * (Real.log u : ℂ)‖ ≤ R := by
      rw [norm_mul, Complex.norm_natCast, norm_real, Real.norm_of_nonneg hlogu]
      exact (mul_le_of_le_one_left hlogu (by exact_mod_cast hm)).trans
        (Real.log_le_log hu₀ (le_mul_of_one_le_left hu₀.le hN))
    have hlog2N : Real.log (2 * (N : ℝ)) ≤ R := Real.log_le_log (by positivity)
      (by rw [mul_comm 2]; exact mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg _))
    have hg' := h0.trans (mul_le_mul_of_nonneg_left (add_le_add hlog2N (le_refl S)) hC.le)
    refine (norm_add_le _ _).trans ((add_le_add hmu hg').trans ?_)
    nlinarith only [hS₀]
  have hlog_pow (w : ℝ) (hw : 0 < w) (hw' : w ≤ X ^ 2) : Real.log w ≤ 2 * L := by
    refine (Real.log_le_log hw hw').trans_eq ?_
    rw [Real.log_pow]
    norm_num [L]
  have hXsq : 4 * X ≤ X ^ 2 := by nlinarith only [mul_nonneg (show 0 ≤ X by linarith only [hX]) (sub_nonneg.mpr hX)]
  have hlogleft₁ : Real.log ((N : ℝ) * (U + 2)) ≤ 2 * L := by
    apply hlog_pow _ (by positivity)
    calc
      _ ≤ (N : ℝ) * (4 * T) := mul_le_mul_of_nonneg_left (by linarith only [hU₂, hT]) (Nat.cast_nonneg _)
      _ = 4 * ((N : ℝ) * T) := by ring
      _ ≤ 4 * X := mul_le_mul_of_nonneg_left hNTX (by norm_num)
      _ ≤ _ := hXsq
  have hlogleft₂ : 1 + Real.log (1 + 2 * U) ≤ 3 * L := by
    have h := hlog_pow (1 + 2 * U) (by positivity)
      (((by linarith only [hU₂, hT] : 1 + 2 * U ≤ 4 * T).trans
        (mul_le_mul_of_nonneg_left hTX (by norm_num))).trans hXsq)
    linarith only [h, hL]
  have hW : ‖W‖ ≤ 6 * B * Q := by
    refine (Hleft N χ hχ u U (by linarith only [hu]) hU.le).trans ?_
    have hn : 0 ≤ 1 + Real.log (1 + 2 * U) := by
      have h := Real.log_nonneg (by linarith only [hU.le] : (1 : ℝ) ≤ 1 + 2 * U)
      linarith only [h]
    have hmul := mul_le_mul hlogleft₁ hlogleft₂ hn (show 0 ≤ 2 * L by linarith only [hL])
    calc
      _ ≤ B * ((2 * L) * (3 * L)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hmul hB.le
      _ = 6 * B * L ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hQL (by positivity)
  have hH (y : ℝ) (hy : |y| = U) : ‖H y‖ ≤ 9 * A * Q := by
    let D := A * Real.log ((N : ℝ) * T) ^ 2
    have hD : 0 ≤ D := by dsimp only [D]; positivity
    have h := norm_primitivePerron_horizontal (χ := χ) hu hT₀ (hU₁.trans_eq hy.symm) hD
      (fun s h₁ h₂ hs => (huBound s h₁ (h₂.trans (hc₂.trans (by norm_num))) (hs ▸ hy)).2)
    have hm : Real.log ((N : ℝ) * T) ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ hlogNT₀ hlogNT 2
    refine h.trans ?_
    dsimp only [D, Q]
    calc
      _ = (9 * A * u / T) * Real.log ((N : ℝ) * T) ^ 2 := by ring
      _ ≤ (9 * A * u / T) * L ^ 2 := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by ring
  have hp := hH U (abs_of_pos hU)
  have hn := hH (-U) (by rw [abs_neg, abs_of_pos hU])
  refine key.trans ((add_le_add (add_le_add (add_le_add hE hW) hn) hp).trans ?_)
  change _ ≤ (1 + C + 6 * B + 18 * A) * (Q + R + S)
  have h₁ := mul_nonneg (add_nonneg hR₀ hS₀) (by positivity : 0 ≤ 6 * B + 18 * A)
  have h₂ := mul_nonneg hQ₀ (by positivity : 0 ≤ 1 + C)
  nlinarith only [h₁, h₂]

end QH.PrimeProgressions
