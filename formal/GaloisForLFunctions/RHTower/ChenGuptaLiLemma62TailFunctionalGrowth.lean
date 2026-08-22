import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailBounds
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62RootNumberNorm
import GaloisForLFunctions.RHTower.GammaVerticalRatioUniform

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

private theorem cglGamma_reverse_half_bound (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a y : ℝ, 0 ≤ a → a ≤ (K : ℝ) + 1 → 1 ≤ y →
      ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ /
        ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ ≤ C * y ^ (1 / 2 : ℝ) := by
  obtain ⟨c, C, hc, hC, hbox⟩ :=
    GaloisForLFunctions.RHTower.exists_twoSided_gamma_vertical_ratio
      (a₁ := (K : ℝ) + 1) (δ₁ := 1 / 2) (by positivity) (by norm_num)
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro a y ha haK hy
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hy0le : 0 ≤ y := hy0.le
  have hlow := (hbox a (1 / 2) y ha haK (by norm_num) (by norm_num) hy).1
  have hden : 0 < ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ :=
    norm_pos_iff.mpr (_root_.RHTower.gammaArg_Gamma_ne_zero hy0 a)
  have hnum : 0 < ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ :=
    norm_pos_iff.mpr (_root_.RHTower.gammaArg_Gamma_ne_zero hy0 (a + 1 / 2))
  have hmult : c * y ^ (-(1 / 2 : ℝ)) *
      ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by
    rw [le_div_iff₀ hnum] at hlow
    exact hlow
  rw [div_le_iff₀ hden]
  have hyhalf0 : 0 < y ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hy0 _
  have hfac : (1 : ℝ) ≤ c⁻¹ * y ^ (1 / 2 : ℝ) * (c * y ^ (-(1 / 2 : ℝ))) := by
    rw [Real.rpow_neg hy0le]
    field_simp [ne_of_gt hc, ne_of_gt hyhalf0]
    rfl
  calc
    ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ =
        1 * ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by ring
    _ ≤ (c⁻¹ * y ^ (1 / 2 : ℝ) * (c * y ^ (-(1 / 2 : ℝ)))) *
        ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by gcongr
    _ = c⁻¹ * y ^ (1 / 2 : ℝ) * (c * y ^ (-(1 / 2 : ℝ)) *
        ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖) := by ring
    _ ≤ c⁻¹ * y ^ (1 / 2 : ℝ) * ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by gcongr
    _ = (c⁻¹ * y ^ (1 / 2 : ℝ)) * ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by ring

private theorem cglGamma_add_nat_eq (B : ℂ) (m : ℕ) (hBim : B.im ≠ 0) :
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

private theorem cgl_norm_Gamma_real_sub_I_tail (a r : ℝ) :
    ‖Complex.Gamma ((a : ℂ) - (r : ℂ) * I)‖ =
      ‖Complex.Gamma ((a : ℂ) + (r : ℂ) * I)‖ := by
  rw [show (a : ℂ) - (r : ℂ) * I =
      (starRingEnd ℂ) ((a : ℂ) + (r : ℂ) * I) by
        apply Complex.ext <;> simp,
    Complex.Gamma_conj, Complex.norm_conj]

private theorem cglGamma_ratio_tail_high (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ∀ e : ℝ,
      z.re = -2 * (K : ℝ) → 2 ≤ |z.im| → e = 0 ∨ e = 1 →
        ‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
          ‖Complex.Gamma ((z + (e : ℂ)) / 2)‖ ≤
            C * (1 + |z.im|) ^ (2 * (K : ℝ) + 1 / 2) := by
  obtain ⟨C0, hC0, hbase⟩ := cglGamma_reverse_half_bound K
  let C : ℝ := ((K : ℝ) + 1) ^ (2 * K) * C0
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro z e hzre hhigh he
  let B : ℂ := (z + (e : ℂ)) / 2
  let a : ℝ := (K : ℝ) + e / 2
  let y : ℝ := |z.im| / 2
  have hy : 1 ≤ y := by
    dsimp [y]
    linarith
  have hy0 : 0 < y := zero_lt_one.trans_le hy
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
  have hBshift_im : (B + (2 * K : ℕ)).im = z.im / 2 := by
    rw [Complex.add_im, hBim]
    simp
  have hBshift_ne : Complex.Gamma (B + (2 * K : ℕ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := hBshift_im
    rw [hn] at him
    simp at him
    have : z.im = 0 := by linarith
    rw [this] at hhigh
    norm_num at hhigh
  have hnumArg :
      (1 - z + (e : ℂ)) / 2 = ((a + 1 / 2 : ℝ) : ℂ) -
        (z.im / 2 : ℝ) * I := by
    apply Complex.ext
    · dsimp [a]
      simp [hzre]
      ring
    · simp
      ring
  have hshiftArg : B + (2 * K : ℕ) = (a : ℂ) + (z.im / 2 : ℝ) * I := by
    apply Complex.ext
    · dsimp [B, a]
      simp [hzre]
      ring
    · dsimp [B]
      simp
  have hnumNorm :
      ‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ =
        ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
    rw [hnumArg]
    rcases le_total 0 z.im with him | him
    · have hyEq : y = z.im / 2 := by
        dsimp [y]
        rw [abs_of_nonneg him]
      calc
        ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) - (z.im / 2 : ℝ) * I)‖ =
            ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + ((z.im / 2 : ℝ) : ℂ) * I)‖ :=
              cgl_norm_Gamma_real_sub_I_tail _ _
        _ = ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by rw [hyEq]
    · have hyEq : y = -z.im / 2 := by
        dsimp [y]
        rw [abs_of_nonpos him]
      calc
        ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) - (z.im / 2 : ℝ) * I)‖ =
            ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + ((-z.im / 2 : ℝ) : ℂ) * I)‖ := by
              congr 2
              push_cast
              ring
        _ = ‖Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by rw [hyEq]
  have hshiftNorm :
      ‖Complex.Gamma (B + (2 * K : ℕ))‖ =
        ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by
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
        ‖Complex.Gamma ((a : ℂ) + (z.im / 2 : ℝ) * I)‖ =
            ‖Complex.Gamma ((a : ℂ) - ((-z.im / 2 : ℝ) : ℂ) * I)‖ := by
              congr 2
              push_cast
              ring
        _ = ‖Complex.Gamma ((a : ℂ) + ((-z.im / 2 : ℝ) : ℂ) * I)‖ :=
              cgl_norm_Gamma_real_sub_I_tail _ _
        _ = ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by rw [hyEq]
  have ha0 : 0 ≤ a := by
    dsimp [a]
    rcases he with rfl | rfl <;> positivity
  have haK : a ≤ (K : ℝ) + 1 := by
    dsimp [a]
    rcases he with rfl | rfl <;> linarith
  have hbase' : ‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
      ‖Complex.Gamma (B + (2 * K : ℕ))‖ ≤ C0 * y ^ (1 / 2 : ℝ) := by
    rw [hnumNorm, hshiftNorm]
    exact hbase a y ha0 haK hy
  have hrec := cglGamma_add_nat_eq B (2 * K) hBim_ne
  have hrecNorm : ‖Complex.Gamma (B + (2 * K : ℕ))‖ =
      ‖∏ j ∈ Finset.range (2 * K), (B + (j : ℂ))‖ * ‖Complex.Gamma B‖ := by
    rw [hrec, norm_mul]
  have hshiftNorm_ne : ‖Complex.Gamma (B + (2 * K : ℕ))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hBshift_ne
  have hratio : ‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
      ‖Complex.Gamma B‖ =
        ‖∏ j ∈ Finset.range (2 * K), (B + (j : ℂ))‖ *
          (‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
            ‖Complex.Gamma (B + (2 * K : ℕ))‖) := by
    rw [hrecNorm] at hshiftNorm_ne ⊢
    have hprod_ne : ‖∏ j ∈ Finset.range (2 * K), (B + (j : ℂ))‖ ≠ 0 := by
      intro h
      exact hshiftNorm_ne (by rw [h]; simp)
    field_simp [hprod_ne]
  let R : ℝ := ((K : ℝ) + 1) * (1 + |z.im|)
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  have hfactor : ∀ j ∈ Finset.range (2 * K), ‖B + (j : ℂ)‖ ≤ R := by
    intro j hj
    have hjle : (j : ℝ) ≤ 2 * (K : ℝ) := by
      have : j ≤ 2 * K := Nat.le_of_lt (Finset.mem_range.mp hj)
      exact_mod_cast this
    have hRe : |(B + (j : ℂ)).re| ≤ (K : ℝ) + 1 := by
      rw [abs_le]
      constructor
      · dsimp [B]
        simp [hzre]
        rcases he with rfl | rfl <;> linarith
      · dsimp [B]
        simp [hzre]
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
      _ ≤ ((K : ℝ) + 1) + |z.im| / 2 := by gcongr
      _ ≤ R := by
        dsimp [R]
        have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        have him0 : (0 : ℝ) ≤ |z.im| := abs_nonneg _
        have hcross : 0 ≤ (K : ℝ) * |z.im| := mul_nonneg hK0 him0
        nlinarith
  have hprod : ‖∏ j ∈ Finset.range (2 * K), (B + (j : ℂ))‖ ≤ R ^ (2 * K) := by
    rw [norm_prod]
    calc
      ∏ j ∈ Finset.range (2 * K), ‖B + (j : ℂ)‖ ≤
          ∏ _j ∈ Finset.range (2 * K), R := by
            apply Finset.prod_le_prod
            · intro j hj
              exact norm_nonneg _
            · intro j hj
              exact hfactor j hj
      _ = R ^ (2 * K) := by simp
  change ‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ / ‖Complex.Gamma B‖ ≤ _
  rw [hratio]
  calc
    ‖∏ j ∈ Finset.range (2 * K), (B + (j : ℂ))‖ *
          (‖Complex.Gamma ((1 - z + (e : ℂ)) / 2)‖ /
            ‖Complex.Gamma (B + (2 * K : ℕ))‖) ≤
        R ^ (2 * K) * (C0 * y ^ (1 / 2 : ℝ)) := by gcongr
    _ ≤ C * (1 + |z.im|) ^ (2 * (K : ℝ) + 1 / 2) := by
      have hyu : y ≤ 1 + |z.im| := by
        dsimp [y]
        nlinarith [abs_nonneg z.im]
      have hu0 : 0 ≤ 1 + |z.im| := by positivity
      have hroot : y ^ (1 / 2 : ℝ) ≤ (1 + |z.im|) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by dsimp [y]; positivity) hyu (by norm_num)
      calc
        R ^ (2 * K) * (C0 * y ^ (1 / 2 : ℝ)) =
            (((K : ℝ) + 1) ^ (2 * K) * C0) *
              ((1 + |z.im|) ^ (2 * K) * y ^ (1 / 2 : ℝ)) := by
                dsimp [R]
                rw [mul_pow]
                ring
        _ ≤ (((K : ℝ) + 1) ^ (2 * K) * C0) *
              ((1 + |z.im|) ^ (2 * K) * (1 + |z.im|) ^ (1 / 2 : ℝ)) := by
                gcongr
        _ = C * (1 + |z.im|) ^ (2 * (K : ℝ) + 1 / 2) := by
          dsimp [C]
          have hpow : (1 + |z.im|) ^ (2 * K) * (1 + |z.im|) ^ (1 / 2 : ℝ) =
              (1 + |z.im|) ^ (2 * (K : ℝ) + 1 / 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity : 0 < 1 + |z.im|)]
            push_cast
            ring
          rw [hpow]

private theorem cglGammaFactor_reflection_tail_high (χ : DirichletCharacter ℂ q)
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re = -2 * (K : ℝ) → 2 ≤ |z.im| →
      ‖χ⁻¹.gammaFactor (1 - z) / χ.gammaFactor z‖ ≤
        C * (1 + |z.im|) ^ (2 * (K : ℝ) + 1 / 2) := by
  obtain ⟨e, he, hgamma⟩ := gammaFactor_eq_Gammaℝ χ
  obtain ⟨C, hC, hratio⟩ := cglGamma_ratio_tail_high K
  refine ⟨C, hC, ?_⟩
  intro z hzre hhigh
  have hratio' := hratio z e hzre hhigh he
  have hpi : Real.pi ^ (z.re - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [Real.pi_gt_three]) (by rw [hzre]; linarith)
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
    _ ≤ 1 * (C * (1 + |z.im|) ^ (2 * (K : ℝ) + 1 / 2)) := by gcongr
    _ = C * (1 + |z.im|) ^ (2 * (K : ℝ) + 1 / 2) := by ring

/-- A high point on CGL's far-left tail line. -/
structure CGLLemma62TailFunctionalHighPoint (d : CGLLemma62TailContourDepth) where
  value : ℂ
  real_eq : value.re = -2 * (d.value : ℝ)
  high : 2 ≤ |value.im|

/-- CGL's primitive functional multiplier has its exact
`2k + 1/2` far-left vertical growth exponent. -/
theorem cglLemma62_primitiveFunctionalFactor_tail_high_bound
    (P : CGLLemma62PrimitiveCharacter) (d : CGLLemma62TailContourDepth) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : CGLLemma62TailFunctionalHighPoint d,
      ‖cglLemma62PrimitiveFunctionalFactor P z.value‖ ≤
        C * (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
  obtain ⟨Cg, hCg, hgamma⟩ :=
    cglGammaFactor_reflection_tail_high P.character d.value
  let C : ℝ := (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
    ‖P.character.rootNumber‖ * Cg
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro z
  have hqpow :
      ‖(P.modulus.value : ℂ) ^ ((1 / 2 : ℂ) - z.value)‖ =
        (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos P.modulus.positive]
    congr 1
    simp only [Complex.sub_re]
    norm_num
    rw [z.real_eq]
    ring
  have hfac := hgamma z.value z.real_eq z.high
  rw [norm_div] at hfac
  unfold cglLemma62PrimitiveFunctionalFactor
  rw [norm_div, norm_mul, norm_mul, hqpow]
  calc
    (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) * ‖P.character.rootNumber‖ *
        ‖P.character⁻¹.gammaFactor (1 - z.value)‖ /
          ‖P.character.gammaFactor z.value‖ =
        (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) * ‖P.character.rootNumber‖ *
          (‖P.character⁻¹.gammaFactor (1 - z.value)‖ /
            ‖P.character.gammaFactor z.value‖) := by ring
    _ ≤
        (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) * ‖P.character.rootNumber‖ *
          (Cg * (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2)) := by
            gcongr
    _ = ((P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        ‖P.character.rootNumber‖ * Cg) *
          (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2) := by ring
    _ = C * (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2) := by rfl

/-- Source-factorized version of the far-left primitive functional estimate.
The primitive conductor power remains visible for CGL's `I₂` arithmetic. -/
theorem cglLemma62_primitiveFunctionalFactor_tail_high_factorized_bound
    (P : CGLLemma62PrimitiveCharacter) (d : CGLLemma62TailContourDepth) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : CGLLemma62TailFunctionalHighPoint d,
      ‖cglLemma62PrimitiveFunctionalFactor P z.value‖ ≤
        C * (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
  obtain ⟨Cg, hCg, hgamma⟩ :=
    cglGammaFactor_reflection_tail_high P.character d.value
  have hroot := cglLemma62_primitive_rootNumber_norm_one P
  let C : ℝ := Cg
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro z
  have hqpow :
      ‖(P.modulus.value : ℂ) ^ ((1 / 2 : ℂ) - z.value)‖ =
        (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos P.modulus.positive]
    congr 1
    simp only [Complex.sub_re]
    norm_num
    rw [z.real_eq]
    ring
  have hfac := hgamma z.value z.real_eq z.high
  rw [norm_div] at hfac
  unfold cglLemma62PrimitiveFunctionalFactor
  rw [norm_div, norm_mul, norm_mul, hqpow, hroot]
  calc
    (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) * 1 *
        ‖P.character⁻¹.gammaFactor (1 - z.value)‖ /
          ‖P.character.gammaFactor z.value‖ =
        (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          (‖P.character⁻¹.gammaFactor (1 - z.value)‖ /
            ‖P.character.gammaFactor z.value‖) := by ring
    _ ≤ (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          (Cg * (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2)) := by
            gcongr
    _ = C * (P.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        (1 + |z.value.im|) ^ (2 * (d.value : ℝ) + 1 / 2) := by ring

end

end RHTower
