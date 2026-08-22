import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailMellinBounds
import GaloisForLFunctions.RHTower.GammaVerticalRatioUniform

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

private theorem cgl_norm_Gamma_real_sub_I_tail_strip (a r : ℝ) :
    ‖Complex.Gamma ((a : ℂ) - (r : ℂ) * I)‖ =
      ‖Complex.Gamma ((a : ℂ) + (r : ℂ) * I)‖ := by
  rw [show (a : ℂ) - (r : ℂ) * I =
      (starRingEnd ℂ) ((a : ℂ) + (r : ℂ) * I) by
        apply Complex.ext <;> simp,
    Complex.Gamma_conj, Complex.norm_conj]

private theorem cglGamma_add_nat_eq_tail_strip (B : ℂ) (m : ℕ) (hBim : B.im ≠ 0) :
    Complex.Gamma (B + (m : ℂ)) =
      (∏ j ∈ Finset.range m, (B + (j : ℂ))) * Complex.Gamma B := by
  induction m with
  | zero => simp
  | succ m hm =>
    have hne : B + (m : ℂ) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp [hBim] at him
    have harg : B + ((m + 1 : ℕ) : ℂ) = (B + (m : ℂ)) + 1 := by
      push_cast
      ring
    rw [harg, Complex.Gamma_add_one _ hne, hm, Finset.prod_range_succ]
    ring

private theorem cglGamma_ratio_tail_strip_high (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ∀ e : ℝ,
      -2 * (K : ℝ) ≤ z.re → z.re ≤ -1 → 2 ≤ |z.im| → e = 0 ∨ e = 1 →
        ‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
          ‖Complex.Gamma ((z + (e : ℂ)) / 2)‖ ≤
            C * (1 + |z.im|) ^ (2 * K + 1) := by
  obtain ⟨c, C0, hc, hC0, hbox⟩ :=
    GaloisForLFunctions.RHTower.exists_twoSided_gamma_vertical_ratio
      (a₁ := (K : ℝ) + 1) (δ₁ := 2 * (K : ℝ)) (by positivity) (by positivity)
  let C : ℝ := ((2 * K + 1 : ℕ) : ℝ) ^ (2 * K + 1) * C0
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro z e hlower hupper hhigh he
  let B : ℂ := (z + (e : ℂ)) / 2
  let a : ℝ := (1 - z.re + e) / 2
  let gap : ℝ := z.re + 2 * (K : ℝ) + 1 / 2
  let y : ℝ := |z.im| / 2
  have hy : 1 ≤ y := by
    dsimp [y]
    linarith
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have ha0 : 0 ≤ a := by
    dsimp [a]
    rcases he with rfl | rfl <;> linarith
  have haK : a ≤ (K : ℝ) + 1 := by
    dsimp [a]
    rcases he with rfl | rfl <;> linarith
  have hgap0 : 0 ≤ gap := by
    dsimp [gap]
    linarith
  have hgapK : gap ≤ 2 * (K : ℝ) := by
    dsimp [gap]
    linarith
  have hBim : B.im = z.im / 2 := by
    dsimp [B]
    simp
  have hBim_ne : B.im ≠ 0 := by
    intro h
    rw [hBim, div_eq_zero_iff] at h
    rcases h with h | h
    · rw [h] at hhigh
      norm_num at hhigh
    · norm_num at h
  have hBne : Complex.Gamma B ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := hBim
    rw [hn] at him
    simp at him
    exact hBim_ne (by linarith)
  have hBshift_im : (B + (2 * K + 1 : ℕ)).im = z.im / 2 := by
    rw [Complex.add_im, hBim]
    simp
  have hBshift_ne : Complex.Gamma (B + (2 * K + 1 : ℕ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := hBshift_im
    rw [hn] at him
    simp at him
    have : z.im = 0 := by linarith
    rw [this] at hhigh
    norm_num at hhigh
  have hnumArg :
      (1 - z + (e : ℂ)) / 2 = (a : ℂ) - (z.im / 2 : ℝ) * I := by
    apply Complex.ext
    · dsimp [a]
      simp
    · simp
      ring
  have hshiftArg : B + (2 * K + 1 : ℕ) = ((a + gap : ℝ) : ℂ) +
      (z.im / 2 : ℝ) * I := by
    apply Complex.ext
    · dsimp [B, a, gap]
      simp
      ring
    · dsimp [B]
      simp
  have hnumNorm :
      ‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ =
        ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by
    rw [hnumArg]
    rcases le_total 0 z.im with him | him
    · have hyEq : y = z.im / 2 := by
        dsimp [y]
        rw [abs_of_nonneg him]
      calc
        ‖Complex.Gamma ((a : ℂ) - (z.im / 2 : ℝ) * I)‖ =
            ‖Complex.Gamma ((a : ℂ) + ((z.im / 2 : ℝ) : ℂ) * I)‖ :=
              cgl_norm_Gamma_real_sub_I_tail_strip _ _
        _ = ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by rw [hyEq]
    · have hyEq : y = -z.im / 2 := by
        dsimp [y]
        rw [abs_of_nonpos him]
      calc
        ‖Complex.Gamma ((a : ℂ) - (z.im / 2 : ℝ) * I)‖ =
            ‖Complex.Gamma ((a : ℂ) + ((-z.im / 2 : ℝ) : ℂ) * I)‖ := by
              congr 2
              push_cast
              ring
        _ = ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by rw [hyEq]
  have hshiftNorm :
      ‖Complex.Gamma (B + (2 * K + 1 : ℕ))‖ =
        ‖Complex.Gamma (((a + gap : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
    rw [hshiftArg]
    rcases le_total 0 z.im with him | him
    · have hyEq : y = z.im / 2 := by
        dsimp [y]
        rw [abs_of_nonneg him]
      rw [hyEq]
    · have hyEq : y = -z.im / 2 := by
        dsimp [y]
        rw [abs_of_nonpos him]
      calc
        ‖Complex.Gamma (((a + gap : ℝ) : ℂ) + (z.im / 2 : ℝ) * I)‖ =
            ‖Complex.Gamma (((a + gap : ℝ) : ℂ) - ((-z.im / 2 : ℝ) : ℂ) * I)‖ := by
              congr 2
              push_cast
              ring
        _ = ‖Complex.Gamma (((a + gap : ℝ) : ℂ) + ((-z.im / 2 : ℝ) : ℂ) * I)‖ :=
              cgl_norm_Gamma_real_sub_I_tail_strip _ _
        _ = ‖Complex.Gamma (((a + gap : ℝ) : ℂ) + (y : ℂ) * I)‖ := by rw [hyEq]
  have hbase0 := (hbox a gap y ha0 haK hgap0 hgapK hy).2
  have hbase : ‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
      ‖Complex.Gamma (B + (2 * K + 1 : ℕ))‖ ≤ C0 := by
    rw [hnumNorm, hshiftNorm]
    calc
      ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma (((a + gap : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        C0 * y ^ (-gap) := hbase0
      _ ≤ C0 * 1 := by
        gcongr
        exact Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith [hgap0])
      _ = C0 := by ring
  have hrec := cglGamma_add_nat_eq_tail_strip B (2 * K + 1) hBim_ne
  have hrecNorm : ‖Complex.Gamma (B + (2 * K + 1 : ℕ))‖ =
      ‖∏ j ∈ Finset.range (2 * K + 1), (B + (j : ℂ))‖ * ‖Complex.Gamma B‖ := by
    rw [hrec, norm_mul]
  have hshiftNorm_ne : ‖Complex.Gamma (B + (2 * K + 1 : ℕ))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hBshift_ne
  have hratio : ‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
      ‖Complex.Gamma B‖ =
        ‖∏ j ∈ Finset.range (2 * K + 1), (B + (j : ℂ))‖ *
          (‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
            ‖Complex.Gamma (B + (2 * K + 1 : ℕ))‖) := by
    rw [hrecNorm] at hshiftNorm_ne ⊢
    have hprod_ne : ‖∏ j ∈ Finset.range (2 * K + 1), (B + (j : ℂ))‖ ≠ 0 := by
      intro h
      exact hshiftNorm_ne (by rw [h]; simp)
    field_simp [hprod_ne]
  let R : ℝ := ((2 * K + 1 : ℕ) : ℝ) * (1 + |z.im|)
  have hfactor : ∀ j ∈ Finset.range (2 * K + 1), ‖B + (j : ℂ)‖ ≤ R := by
    intro j hj
    have hjle : (j : ℝ) ≤ 2 * (K : ℝ) := by
      have hnat : j ≤ 2 * K := Nat.lt_succ_iff.mp
        (by simpa [Nat.succ_eq_add_one] using Finset.mem_range.mp hj)
      have : j ≤ 2 * K := hnat
      exact_mod_cast this
    have hRe : |(B + (j : ℂ)).re| ≤ 2 * (K : ℝ) := by
      rw [abs_le]
      constructor
      · dsimp [B]
        simp
        rcases he with rfl | rfl <;> linarith
      · dsimp [B]
        simp
        rcases he with rfl | rfl <;> linarith
    have hIm : |(B + (j : ℂ)).im| = |z.im| / 2 := by
      rw [Complex.add_im, hBim]
      simp
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      ‖B + (j : ℂ)‖ = ‖((B + (j : ℂ)).re : ℂ) + ((B + (j : ℂ)).im : ℂ) * I‖ := by
        rw [Complex.re_add_im]
      _ ≤ ‖((B + (j : ℂ)).re : ℂ)‖ + ‖((B + (j : ℂ)).im : ℂ) * I‖ := norm_add_le _ _
      _ = |(B + (j : ℂ)).re| + |(B + (j : ℂ)).im| := by
        simp only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          Complex.add_re]
      _ = |(B + (j : ℂ)).re| + |z.im| / 2 := by rw [hIm]
      _ ≤ 2 * (K : ℝ) + |z.im| / 2 := by gcongr
      _ ≤ R := by
        dsimp [R]
        have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        have him0 : (0 : ℝ) ≤ |z.im| := abs_nonneg _
        have hcross : 0 ≤ (2 * (K : ℝ)) * |z.im| := mul_nonneg (by positivity) him0
        norm_num
        nlinarith
  have hprod : ‖∏ j ∈ Finset.range (2 * K + 1), (B + (j : ℂ))‖ ≤ R ^ (2 * K + 1) := by
    rw [norm_prod]
    calc
      ∏ j ∈ Finset.range (2 * K + 1), ‖B + (j : ℂ)‖ ≤
          ∏ _j ∈ Finset.range (2 * K + 1), R := by
            apply Finset.prod_le_prod
            · intro j hj
              exact norm_nonneg _
            · intro j hj
              exact hfactor j hj
      _ = R ^ (2 * K + 1) := by simp
  change ‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ / ‖Complex.Gamma B‖ ≤ _
  rw [hratio]
  calc
    ‖∏ j ∈ Finset.range (2 * K + 1), (B + (j : ℂ))‖ *
          (‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
            ‖Complex.Gamma (B + (2 * K + 1 : ℕ))‖) ≤
        R ^ (2 * K + 1) * C0 := by gcongr
    _ = C * (1 + |z.im|) ^ (2 * K + 1) := by
      dsimp [R, C]
      rw [mul_pow]
      ring

private theorem cglGammaFactor_reflection_tail_strip_high (χ : DirichletCharacter ℂ q)
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      -2 * (K : ℝ) ≤ z.re → z.re ≤ -1 → 2 ≤ |z.im| →
      ‖χ⁻¹.gammaFactor (1 - z) / χ.gammaFactor z‖ ≤
        C * (1 + |z.im|) ^ (2 * K + 1) := by
  obtain ⟨e, he, hgamma⟩ := gammaFactor_eq_Gammaℝ χ
  obtain ⟨C, hC, hratio⟩ := cglGamma_ratio_tail_strip_high K
  refine ⟨C, hC, ?_⟩
  intro z hlower hupper hhigh
  have hratio' := hratio z e hlower hupper hhigh he
  have hpi : Real.pi ^ (z.re - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [Real.pi_gt_three]) (by linarith)
  have hnorm : ‖χ⁻¹.gammaFactor (1 - z) / χ.gammaFactor z‖ =
      Real.pi ^ (z.re - 1 / 2) *
        (‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
          ‖Complex.Gamma ((z + (e : ℂ)) / 2)‖) := by
    rw [norm_div, gammaFactor_inv, hgamma (1 - z), hgamma z,
      GaloisForLFunctions.HTGeometry.norm_Gammaℝ,
      GaloisForLFunctions.HTGeometry.norm_Gammaℝ]
    have hre1 : -((1 - z + (e : ℂ)).re) / 2 = -(1 - z.re + e) / 2 := by
      simp [Complex.sub_re, Complex.add_re]
    have hre2 : -((z + (e : ℂ)).re) / 2 = -(z.re + e) / 2 := by
      simp [Complex.add_re]
    rw [hre1, hre2, mul_div_mul_comm, ← Real.rpow_sub Real.pi_pos]
    congr 2
    ring
  rw [hnorm]
  calc
    Real.pi ^ (z.re - 1 / 2) *
        (‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
          ‖Complex.Gamma ((z + (e : ℂ)) / 2)‖) ≤
        1 * (‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
          ‖Complex.Gamma ((z + (e : ℂ)) / 2)‖) := by gcongr
    _ ≤ 1 * (C * (1 + |z.im|) ^ (2 * K + 1)) := by gcongr
    _ = C * (1 + |z.im|) ^ (2 * K + 1) := by ring

/-- A high point of CGL's complete reflected tail rectangle. -/
structure CGLLemma62TailFunctionalStripHighPoint (d : CGLLemma62TailContourDepth) where
  value : ℂ
  lower : -2 * (d.value : ℝ) ≤ value.re
  upper : value.re ≤ -1
  high : 2 ≤ |value.im|

/-- A closed polynomial high-height envelope for the primitive functional
factor throughout CGL's tail rectangle. -/
theorem cglLemma62_primitiveFunctionalFactor_tail_strip_high_bound
    (P : CGLLemma62PrimitiveCharacter) (d : CGLLemma62TailContourDepth) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : CGLLemma62TailFunctionalStripHighPoint d,
      ‖cglLemma62PrimitiveFunctionalFactor P z.value‖ ≤
        C * (1 + |z.value.im|) ^ (2 * d.value + 1) := by
  obtain ⟨Cg, hCg, hgamma⟩ :=
    cglGammaFactor_reflection_tail_strip_high P.character d.value
  let C : ℝ := (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
    ‖P.character.rootNumber‖ * Cg
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro z
  have hqpow :
      ‖(P.modulus.value : ℂ) ^ ((1 / 2 : ℂ) - z.value)‖ ≤
        (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos P.modulus.positive]
    have hbase : (1 : ℝ) ≤ P.modulus.value := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt P.modulus.positive)
    have hexp : (1 / 2 : ℝ) - z.value.re ≤ 1 / 2 + 2 * (d.value : ℝ) := by
      linarith [z.lower]
    convert Real.rpow_le_rpow_of_exponent_le hbase hexp using 1; norm_num
  have hfac := hgamma z.value z.lower z.upper z.high
  rw [norm_div] at hfac
  unfold cglLemma62PrimitiveFunctionalFactor
  rw [norm_div, norm_mul, norm_mul]
  calc
    ‖(P.modulus.value : ℂ) ^ (1 / 2 - z.value)‖ * ‖P.character.rootNumber‖ *
        ‖P.character⁻¹.gammaFactor (1 - z.value)‖ /
          ‖P.character.gammaFactor z.value‖ =
        ‖(P.modulus.value : ℂ) ^ (1 / 2 - z.value)‖ * ‖P.character.rootNumber‖ *
          (‖P.character⁻¹.gammaFactor (1 - z.value)‖ /
            ‖P.character.gammaFactor z.value‖) := by ring
    _ ≤
        (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) * ‖P.character.rootNumber‖ *
          (Cg * (1 + |z.value.im|) ^ (2 * d.value + 1)) := by
            gcongr
    _ = ((P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        ‖P.character.rootNumber‖ * Cg) *
          (1 + |z.value.im|) ^ (2 * d.value + 1) := by ring
    _ = C * (1 + |z.value.im|) ^ (2 * d.value + 1) := by rfl

end

end RHTower
