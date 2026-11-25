import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.MollifierHyperbola
import GaloisForLFunctions.MatomakiRadziwill.LFunctionGrowth
import GaloisForLFunctions.RHTower.ZeroDetectionEM

/-! Truncation at the hyperbola cutoff detects zeros near the one-line. -/

open Complex Finset ArithmeticFunction Filter RHTower
open scoped Topology

namespace QH.PrimeProgressions

private theorem mul_quotient_bounds {Q d : ℕ} (hQ : 2 ≤ Q) (hd : d ∈ Icc 1 (Q ^ 3)) :
    0 < d ∧ 0 < Q ^ 6 / d ∧ Q ^ 6 ≤ 2 * (d * (Q ^ 6 / d)) ∧ d * (Q ^ 6 / d) ≤ Q ^ 6 := by
  obtain ⟨hd₁, hd₂⟩ := mem_Icc.mp hd
  have hDX : Q ^ 3 ≤ Q ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hD : 2 ≤ Q ^ 3 := hQ.trans (Nat.le_self_pow (by omega) Q)
  have hXX : 2 * Q ^ 3 ≤ Q ^ 6 := by
    calc
      _ ≤ Q ^ 3 * Q ^ 3 := Nat.mul_le_mul_right _ hD
      _ = _ := by ring
  refine ⟨hd₁, Nat.div_pos (hd₂.trans hDX) hd₁, ?_, Nat.mul_div_le _ _⟩
  have h := Nat.div_add_mod (Q ^ 6) d
  have hm := Nat.mod_lt (Q ^ 6) hd₁
  omega

private theorem mul_quotient_rpow_bound {Q y σ : ℝ} (hQ : 1024 ≤ Q) (hy : Q ^ 6 ≤ 2 * y)
    (hσ : 11 / 12 ≤ σ) : y ^ (-σ) ≤ (16 * Q ^ 5)⁻¹ := by
  have hQ₀ : 0 < Q := by linarith
  have hQ₆ : (2 : ℝ) ^ 60 ≤ Q ^ 6 := by
    calc
      _ = 1024 ^ 6 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hQ 6
  have hy₁ : 1 ≤ y := by linarith only [hQ₆, hy]
  have hy₀ : 0 < y := zero_lt_one.trans_le hy₁
  have hpow : (y ^ ((11 : ℝ) / 12)) ^ 12 = y ^ 11 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy₀.le]
    norm_num
  have h12 : (16 * Q ^ 5) ^ 12 ≤ (y ^ ((11 : ℝ) / 12)) ^ 12 := by
    rw [hpow]
    calc
      _ = 2 ^ 48 * Q ^ 60 := by ring
      _ ≤ (Q ^ 6 / 2) ^ 11 := by
        have hpow₆₀ : 0 ≤ Q ^ 60 := by positivity
        have h := mul_le_mul_of_nonneg_right hQ₆ hpow₆₀
        rw [show (Q ^ 6 / 2) ^ 11 = Q ^ 6 * Q ^ 60 / 2 ^ 11 by ring, le_div_iff₀ (by norm_num)]
        linarith only [h, hpow₆₀]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith only [hy]) _
  have hkey : 16 * Q ^ 5 ≤ y ^ ((11 : ℝ) / 12) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h12
  rw [Real.rpow_neg hy₀.le]
  exact inv_anti₀ (by positivity) (hkey.trans (Real.rpow_le_rpow_of_exponent_le hy₁ hσ))

private theorem norm_moebius_character_power_le {q d : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hd : 0 < d) :
    ‖(moebius d : ℂ) * (χ (d : ZMod q) * (d : ℂ) ^ (-s))‖ ≤ (d : ℝ) ^ (-s.re) := by
  have hμ : ‖(moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hd, Complex.neg_re, ← mul_assoc]
  exact mul_le_of_le_one_left (by positivity)
    ((mul_le_mul hμ (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

private theorem inverse_le_rpow {n : ℕ} (hn : 0 < n) :
    (n : ℝ)⁻¹ ≤ (n : ℝ) ^ ((1 : ℝ) / 200 - 1) := by
  rw [← Real.rpow_neg_one]
  apply Real.rpow_le_rpow_of_exponent_le _ (by norm_num)
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')

private theorem detector_from_small_hyperbola {q Q : ℕ} (hQ : 0 < Q)
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) (B : ℕ → ℝ)
    (hterms : ∀ d ∈ Icc 1 (Q ^ 3),
      ‖(moebius d : ℂ) * (χ (d : ZMod q) * (d : ℂ) ^ (-ρ)) *
        ∑ m ∈ Icc 1 (Q ^ 6 / d), χ (m : ZMod q) * (m : ℂ) ^ (-ρ)‖ ≤ B d)
    (hB : ∑ d ∈ Icc 1 (Q ^ 3), B d ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ ‖mollifierTail Q χ ρ‖ := by
  rw [mollifierTail_eq_hyperbola hQ]
  let f (n : ℕ) := χ (n : ZMod q) * (n : ℂ) ^ (-ρ)
  let z := ∑ d ∈ Icc 1 (Q ^ 3), (moebius d : ℂ) * f d * ∑ m ∈ Icc 1 (Q ^ 6 / d), f m
  change (1 / 2 : ℝ) ≤ ‖z - 1‖
  have hz : ‖z‖ ≤ 1 / 2 := (norm_sum_le _ _).trans ((sum_le_sum hterms).trans hB)
  have h := norm_sub_norm_le (1 : ℂ) z
  rw [norm_one, norm_sub_rev] at h
  linarith only [h, hz]

/-- Every nonprincipal zero in the detector strip has a large Möbius detector value. -/
theorem mollifier_detects_character_zero {Q q : ℕ} [NeZero q] (hQ : 1024 ≤ Q) (hq : q ≤ Q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ρ : ℂ}
    (hre : 1 - 1 / 400 ≤ ρ.re) (him : |ρ.im| ≤ Q) (hzero : χ.LFunction ρ = 0) :
    (1 / 2 : ℝ) ≤ ‖mollifierTail Q χ ρ‖ := by
  have hQ₀ : 0 < Q := by omega
  have hQR : (1024 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hqR : (q : ℝ) ≤ Q := by exact_mod_cast hq
  have hσ : 0 < ρ.re := by linarith only [hre]
  have hσ' : (11 / 12 : ℝ) ≤ ρ.re := by linarith only [hre]
  have hn : ‖ρ‖ ≤ ρ.re + Q := by
    exact (Complex.norm_le_abs_re_add_abs_im ρ).trans
      (by rw [abs_of_pos hσ]; exact add_le_add le_rfl him)
  have hratio : ‖ρ‖ / ρ.re ≤ 1 + 2 * Q := by
    rw [div_le_iff₀ hσ]
    have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * ρ.re by linarith only [hσ'])
      (Nat.cast_nonneg Q)
    nlinarith only [hn, h]
  have hnorm : 1 + ‖ρ‖ / ρ.re ≤ 4 * Q := by
    linarith only [hratio, hQR]
  refine detector_from_small_hyperbola hQ₀ χ ρ (fun _ => (2 * (Q : ℝ) ^ 3)⁻¹) ?_ ?_
  · intro d hd
    set M := Q ^ 6 / d
    obtain ⟨hd₀, hM, hy, _⟩ := mul_quotient_bounds (by omega : 2 ≤ Q) hd
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have htail := norm_LFunction_sub_character_partial_le hχ hσ M
    rw [hzero, zero_sub, norm_neg, GaloisForLFunctions.MatomakiRadziwill.dirichletPartialSum_eq_sum_Icc] at htail
    have htail' : ‖∑ m ∈ Icc 1 M, χ (m : ZMod q) * (m : ℂ) ^ (-ρ)‖ ≤
        8 * (Q : ℝ) ^ 2 * (M : ℝ) ^ (-ρ.re) := by
      push_cast at htail
      refine htail.trans ?_
      have hpow := Real.rpow_le_rpow_of_nonpos hMR (le_add_of_nonneg_right (zero_le_one (α := ℝ))) (neg_nonpos.mpr hσ.le)
      calc
        _ ≤ (2 * (Q : ℝ) * (4 * Q)) * (M : ℝ) ^ (-ρ.re) := by gcongr
        _ = _ := by ring
    rw [norm_mul]
    refine (mul_le_mul (norm_moebius_character_power_le χ hd₀) htail'
      (norm_nonneg _) (by positivity)).trans ?_
    have hpow := mul_quotient_rpow_bound hQR (y := (d : ℝ) * M) (by exact_mod_cast hy) hσ'
    rw [Real.mul_rpow (Nat.cast_nonneg d) hMR.le] at hpow
    calc
      _ = 8 * (Q : ℝ) ^ 2 * ((d : ℝ) ^ (-ρ.re) * (M : ℝ) ^ (-ρ.re)) := by ring
      _ ≤ 8 * (Q : ℝ) ^ 2 * (16 * (Q : ℝ) ^ 5)⁻¹ := by gcongr
      _ = _ := by
        field_simp [show (Q : ℝ) ≠ 0 by positivity]
        ring
  · rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_pow]
    have h : (Q : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num

private theorem zeta_pole_sum_small :
    ∃ Q₀ : ℕ, 1024 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ Q →
      ∑ d ∈ Icc 1 (Q ^ 3), (d : ℝ)⁻¹ *
        (((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) / (Q : ℝ) ^ ((1 : ℝ) / 20)) ≤ 1 / 4 := by
  have ht : Tendsto (fun Q : ℕ => (Q : ℝ) ^ ((1 : ℝ) / 50)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨Q₁, hQ₁⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 800)
  refine ⟨max Q₁ 1024, le_max_right _ _, fun Q hQ => ?_⟩
  have hQ₀ : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q from (by omega : 0 < 1024).trans_le
    ((le_max_right Q₁ 1024).trans hQ))
  have hlarge := hQ₁ Q ((le_max_left _ _).trans hQ)
  have hsum : ∑ d ∈ Icc 1 (Q ^ 3), (d : ℝ)⁻¹ ≤ 200 * (Q : ℝ) ^ ((3 : ℝ) / 200) := by
    refine (sum_le_sum fun d hd => inverse_le_rpow (mem_Icc.mp hd).1).trans ?_
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    push_cast
    simp only [add_comm (1 : ℝ)]
    refine (HTGeometry.sum_rpow_sub_one_le (a := 1 / 200) (by norm_num) (by norm_num) _).trans_eq ?_
    rw [Nat.cast_pow, ← Real.rpow_natCast (Q : ℝ) 3, ← Real.rpow_mul hQ₀.le]
    norm_num <;> ring
  rw [← sum_mul]
  refine (mul_le_mul_of_nonneg_right hsum (by positivity)).trans ?_
  rw [← Real.rpow_natCast (Q : ℝ) 6, ← Real.rpow_mul hQ₀.le]
  have hpow : (Q : ℝ) ^ ((3 : ℝ) / 200) * (Q : ℝ) ^ (((6 : ℕ) : ℝ) * (1 / 400)) =
      (Q : ℝ) ^ ((1 : ℝ) / 20) / (Q : ℝ) ^ ((1 : ℝ) / 50) := by
    rw [← Real.rpow_add hQ₀, ← Real.rpow_sub hQ₀]
    norm_num
  have hden : 0 < (Q : ℝ) ^ ((1 : ℝ) / 50) := by positivity
  calc
    _ = 200 / (Q : ℝ) ^ ((1 : ℝ) / 50) := by
      rw [show (200 * (Q : ℝ) ^ ((3 : ℝ) / 200)) *
          ((Q : ℝ) ^ (((6 : ℕ) : ℝ) * (1 / 400)) / (Q : ℝ) ^ ((1 : ℝ) / 20)) =
          200 * ((Q : ℝ) ^ ((3 : ℝ) / 200) * (Q : ℝ) ^ (((6 : ℕ) : ℝ) * (1 / 400))) /
            (Q : ℝ) ^ ((1 : ℝ) / 20) by ring, hpow]
      field_simp
    _ ≤ _ := (div_le_iff₀ hden).mpr (by linarith only [hlarge])

/-- The principal detector also detects high zeta zeros. -/
theorem mollifier_detects_zeta_zero :
    ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q → ∀ (χ : DirichletCharacter ℂ 1) (ρ : ℂ),
      1 - 1 / 400 ≤ ρ.re → ρ.re < 1 → (Q : ℝ) ^ ((1 : ℝ) / 20) ≤ |ρ.im| →
      |ρ.im| ≤ Q → riemannZeta ρ = 0 → (1 / 2 : ℝ) ≤ ‖mollifierTail Q χ ρ‖ := by
  obtain ⟨Q₀, hQ₀, hsmall⟩ := zeta_pole_sum_small
  refine ⟨Q₀, fun Q hQ χ ρ hre hlt hhigh him hzero => ?_⟩
  have hQ' : 1024 ≤ Q := hQ₀.trans hQ
  have hQR : (1024 : ℝ) ≤ Q := by exact_mod_cast hQ'
  have hQ₁ : (1 : ℝ) ≤ Q := by linarith
  have hQpos : (0 : ℝ) < Q := by linarith
  have hχ (u : ZMod 1) : χ u = 1 := by rw [Subsingleton.elim u 1, map_one]
  have hσ : 0 < ρ.re := by linarith only [hre]
  have hσ' : (11 / 12 : ℝ) ≤ ρ.re := by linarith only [hre]
  have hne : ρ ≠ 1 := by
    rintro rfl
    simp at hlt
  have hn : ‖ρ‖ ≤ ρ.re + Q :=
    (Complex.norm_le_abs_re_add_abs_im _).trans
      (by rw [abs_of_pos hσ]; exact add_le_add le_rfl him)
  have hratio : ‖ρ‖ / ρ.re ≤ 4 * Q := by
    rw [div_le_iff₀ hσ]
    have h := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ 4 * ρ.re by linarith only [hσ']) hQpos.le
    linarith only [hn, h, hlt, hQ₁]
  let D := ((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) / (Q : ℝ) ^ ((1 : ℝ) / 20)
  let E := (4 * (Q : ℝ) ^ 3)⁻¹
  refine detector_from_small_hyperbola (show 0 < Q by omega) χ ρ
    (fun d => E + (d : ℝ)⁻¹ * D) ?_ ?_
  · intro d hd
    set M := Q ^ 6 / d
    obtain ⟨hd₀, hM, hy, hy'⟩ := mul_quotient_bounds (show 2 ≤ Q by omega) hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd₀
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hden : (Q : ℝ) ^ ((1 : ℝ) / 20) ≤ ‖ρ - 1‖ := hhigh.trans
      (by simpa only [sub_im, one_im, sub_zero] using Complex.abs_im_le_norm (ρ - 1))
    have hpole : ‖emPole M ρ‖ ≤ (M : ℝ) ^ (1 - ρ.re) / (Q : ℝ) ^ ((1 : ℝ) / 20) := by
      rw [norm_emPole hM]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have htail := zeta_sub_emCarrier_norm_le hM hσ hne
    rw [hzero, zero_sub, norm_neg, emCarrier] at htail
    have hpoly : ‖dirichletPoly M ρ‖ ≤ (4 * Q) * (M : ℝ) ^ (-ρ.re) +
        (M : ℝ) ^ (1 - ρ.re) / (Q : ℝ) ^ ((1 : ℝ) / 20) := by
      have h := norm_sub_le (dirichletPoly M ρ + emPole M ρ) (emPole M ρ)
      rw [add_sub_cancel_right] at h
      refine h.trans (add_le_add (htail.trans ?_) hpole)
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_right hratio (by positivity)
    have hmul := mul_quotient_rpow_bound hQR (y := (d : ℝ) * M) (by exact_mod_cast hy) hσ'
    rw [Real.mul_rpow hdR.le hMR.le] at hmul
    have h₁ : (d : ℝ) ^ (-ρ.re) * ((4 * Q) * (M : ℝ) ^ (-ρ.re)) ≤ E := by
      calc
        _ = 4 * Q * ((d : ℝ) ^ (-ρ.re) * (M : ℝ) ^ (-ρ.re)) := by ring
        _ ≤ 4 * Q * (16 * (Q : ℝ) ^ 5)⁻¹ :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
        _ = (4 * (Q : ℝ) ^ 4)⁻¹ := by
          field_simp
          norm_num
        _ ≤ E := inv_anti₀ (by positivity) (by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hQ₁ (by omega)) (by norm_num))
    have hdm : (1 : ℝ) ≤ (d : ℝ) * M := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hd₀ hM).ne')
    have hupper : (d : ℝ) * M ≤ (Q : ℝ) ^ 6 := by exact_mod_cast hy'
    have h₂ : (d : ℝ) ^ (-ρ.re) *
        ((M : ℝ) ^ (1 - ρ.re) / (Q : ℝ) ^ ((1 : ℝ) / 20)) ≤ (d : ℝ)⁻¹ * D := by
      have hpow : (d : ℝ) ^ (-ρ.re) = (d : ℝ)⁻¹ * (d : ℝ) ^ (1 - ρ.re) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hdR]
        ring_nf
      rw [hpow, mul_assoc, ← mul_div_assoc, ← Real.mul_rpow hdR.le hMR.le]
      dsimp [D]
      have hexp : 1 - ρ.re ≤ (1 : ℝ) / 400 := by linarith only [hre]
      have hpower := (Real.rpow_le_rpow (mul_nonneg hdR.le hMR.le) hupper (sub_nonneg.mpr hlt.le)).trans
        (Real.rpow_le_rpow_of_exponent_le (hdm.trans hupper) hexp)
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hpower (by positivity))
        (by positivity)
    rw [norm_mul]
    have hpoly' : ‖∑ m ∈ Icc 1 M, χ (m : ZMod 1) * (m : ℂ) ^ (-ρ)‖ ≤
        (4 * Q) * (M : ℝ) ^ (-ρ.re) + (M : ℝ) ^ (1 - ρ.re) / (Q : ℝ) ^ ((1 : ℝ) / 20) := by
      simpa only [hχ, one_mul, dirichletPoly] using hpoly
    refine (mul_le_mul (norm_moebius_character_power_le χ hd₀) hpoly'
      (norm_nonneg _) (by positivity)).trans ?_
    rw [mul_add]
    exact add_le_add h₁ h₂
  · rw [sum_add_distrib]
    have hE : ∑ _ ∈ Icc 1 (Q ^ 3), E = 1 / 4 := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_pow]
      change (Q : ℝ) ^ 3 * (4 * (Q : ℝ) ^ 3)⁻¹ = 1 / 4
      field_simp [hQpos.ne']
    rw [hE]
    exact (add_le_add le_rfl (hsmall Q hQ)).trans_eq (by norm_num : (1 / 4 : ℝ) + 1 / 4 = 1 / 2)

end QH.PrimeProgressions
