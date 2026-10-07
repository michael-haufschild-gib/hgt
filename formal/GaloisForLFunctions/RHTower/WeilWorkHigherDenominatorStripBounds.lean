import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPoleClearing
import GaloisForLFunctions.RHTower.ZetaInverseWideHorizontal

/-!
# Actual strip bounds for a pole-cleared cubic quotient

Every polynomial multiple of the entire quotient `H = P E / xi` is bounded
on the strip from -1 to 2. The boundary estimates come from the cubic datum's
Dirichlet series and functional equation. No strip-growth premise is added.
-/

noncomputable section

open Complex Set Filter Topology Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilHigherDenominator

private lemma finiteOrderEnvelope_standard {f : ℂ → ℂ} (hf : FiniteOrderEnvelope f) :
    ∃ ρ C₀ : ℝ, ∀ z, ‖f z‖ ≤ C₀ * Real.exp (‖z‖ ^ ρ) := by
  obtain ⟨C, d, hC, hb⟩ := hf
  let A : ℝ := max 1 (C * 2 ^ d)
  let B : ℝ := C * (1 + A) ^ d
  have hA : 1 ≤ A := le_max_left _ _
  have hCA : C * 2 ^ d ≤ A := le_max_right _ _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(d + 1 : ℕ), Real.exp B, fun z => ?_⟩
  have he : C * (1 + ‖z‖) ^ d ≤ B + ‖z‖ ^ (d + 1) := by
    rcases le_or_gt ‖z‖ A with hz | hz
    · have ht : C * (1 + ‖z‖) ^ d ≤ B := by
        dsimp [B]
        gcongr
      exact ht.trans (le_add_of_nonneg_right (by positivity))
    · have h1 : 1 ≤ ‖z‖ := hA.trans hz.le
      calc
        C * (1 + ‖z‖) ^ d ≤ C * (2 * ‖z‖) ^ d := by gcongr; linarith
        _ = (C * 2 ^ d) * ‖z‖ ^ d := by rw [mul_pow]; ring
        _ ≤ ‖z‖ * ‖z‖ ^ d := mul_le_mul_of_nonneg_right (hCA.trans hz.le) (by positivity)
        _ = ‖z‖ ^ (d + 1) := by ring
        _ ≤ B + ‖z‖ ^ (d + 1) := le_add_of_nonneg_left hB
  calc
    ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ d) := hb z
    _ ≤ Real.exp (B + ‖z‖ ^ (d + 1)) := Real.exp_le_exp.mpr he
    _ = Real.exp B * Real.exp (‖z‖ ^ ((d + 1 : ℕ) : ℝ)) := by
      rw [Real.exp_add, Real.rpow_natCast]

/-- Gamma absorbs every polynomial on the right boundary used for the quotient. -/
theorem polynomial_mul_Gammaℝ_two_bounded (P : Polynomial ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ,
      ‖P.eval (2 + t * I) * Complex.Gammaℝ (2 + t * I)‖ ≤ B := by
  obtain ⟨M, d, hM, hP⟩ := exists_polynomial_norm_bound P
  obtain ⟨Cγ, N, hCγ, hγ⟩ := IntegerMassRigidity.exists_bound_Gammaℝ_two
  let B : ℝ := (4 / Real.pi) ^ (d + N) * (d + N).factorial * Real.exp Real.pi
  refine ⟨M * Cγ * B, by dsimp [B]; positivity, fun t => ?_⟩
  have hz : 1 + ‖(2 : ℂ) + t * I‖ ≤ |t| + 4 := by
    have hn := norm_add_le (2 : ℂ) ((t : ℂ) * I)
    simp at hn
    linarith
  have hPe : ‖P.eval (2 + t * I)‖ ≤ M * (|t| + 4) ^ d :=
    (hP _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hz d) hM)
  have hpow : (|t| + 4) ^ (d + N) * Real.exp (-(Real.pi * |t| / 4)) ≤ B := by
    have hp := MaassZetaSquaredConverse.pow_mul_exp_le
      (by positivity : (0 : ℝ) ≤ |t| + 4) (d + N)
    have he : Real.exp (-(Real.pi * |t| / 4)) =
        Real.exp (-(Real.pi * (|t| + 4) / 4)) * Real.exp Real.pi := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
  rw [norm_mul]
  calc
    ‖P.eval (2 + t * I)‖ * ‖Complex.Gammaℝ (2 + t * I)‖ ≤
        (M * (|t| + 4) ^ d) *
          (Cγ * ((|t| + 4) ^ N * Real.exp (-(Real.pi * |t| / 4)))) := by
      gcongr
      exact hγ t
    _ = (M * Cγ) * ((|t| + 4) ^ (d + N) * Real.exp (-(Real.pi * |t| / 4))) := by
      rw [pow_add]
      ring
    _ ≤ M * Cγ * B := mul_le_mul_of_nonneg_left hpow (mul_nonneg hM hCγ)

/-- Exact right-half-plane formula after removing one xi factor. -/
theorem cubicQuotient_eq_right {g : ℕ → ℂ} {E H : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (P : Polynomial ℂ)
    (hfac : ∀ z, P.eval z * E z = H z * xi z) {s : ℂ} (hs : 2 ≤ s.re) :
    H s = 2 * P.eval s * s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 *
      LSeries g s * (riemannZeta s)⁻¹ := by
  have hspos : 0 < s.re := by linarith
  have hsone : 1 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hΓ := Complex.Gammaℝ_ne_zero_of_re_pos hspos
  have hζ : riemannZeta s ≠ 0 := norm_pos_iff.mp
    (lt_of_lt_of_le (by norm_num) (norm_riemannZeta_ge_of_two_le_re hs))
  have hA : s * (s - 1) * Complex.Gammaℝ s ≠ 0 :=
    mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hΓ
  have hxi := MaassZetaSquaredConverse.two_xi_eq hspos hs1
  apply mul_right_cancel₀ (mul_ne_zero hA hζ)
  calc
    H s * (s * (s - 1) * Complex.Gammaℝ s * riemannZeta s) = 2 * (H s * xi s) := by
      rw [← hxi]
      ring
    _ = 2 * (P.eval s * E s) := by rw [← hfac s]
    _ = (2 * P.eval s * s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 *
        LSeries g s * (riemannZeta s)⁻¹) *
        (s * (s - 1) * Complex.Gammaℝ s * riemannZeta s) := by
      rw [hD.completion s hsone]
      field_simp

/-- The right boundary bound is supplied by the datum, not assumed. -/
theorem cubicQuotient_right_bounded {g : ℕ → ℂ} {E H : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (P : Polynomial ℂ)
    (hfac : ∀ z, P.eval z * E z = H z * xi z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, s.re = 2 → ‖H s‖ ≤ B := by
  let R : Polynomial ℂ := C 2 * P * X ^ 2 * (X - C 1) ^ 2
  obtain ⟨B₁, hB₁, hb₁⟩ := polynomial_mul_Gammaℝ_two_bounded R
  obtain ⟨B₂, hB₂, hb₂⟩ := polynomial_mul_Gammaℝ_two_bounded 1
  let M : ℝ := ∑' n, ‖LSeries.term g 2 n‖
  have hM : 0 ≤ M := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨B₁ * B₂ * M * 4, by positivity, fun s hs => ?_⟩
  have he : s = 2 + (s.im : ℂ) * I := by apply Complex.ext <;> simp [hs]
  have h₁ : ‖R.eval s * Complex.Gammaℝ s‖ ≤ B₁ := by rw [he]; exact hb₁ s.im
  have h₂ : ‖Complex.Gammaℝ s‖ ≤ B₂ := by
    simpa only [Polynomial.eval_one, one_mul, ← he] using hb₂ s.im
  have hG := CompletionGrowth.norm_LSeries_le_of_two_le (hD.summable 2 (by norm_num)) hs.ge
  have hζ := norm_zeta_inv_le_of_two_le_re hs.ge
  have hval : H s = (R.eval s * Complex.Gammaℝ s) * Complex.Gammaℝ s *
      LSeries g s * (riemannZeta s)⁻¹ := by
    rw [cubicQuotient_eq_right hD P hfac hs.ge]
    simp only [R, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub]
    ring
  rw [hval, norm_mul, norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) hB₁)
    hG (norm_nonneg _) (mul_nonneg hB₁ hB₂)) hζ (norm_nonneg _) (by positivity)

private lemma cubicQuotient_strip_bounded {g : ℕ → ℂ} {E H : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (P : Polynomial ℂ)
    (hH : Differentiable ℂ H) (hHfinite : FiniteOrderEnvelope H)
    (hfac : ∀ z, P.eval z * E z = H z * xi z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → ‖H s‖ ≤ B := by
  obtain ⟨B₂, hB₂, hb₂⟩ := cubicQuotient_right_bounded hD P hfac
  obtain ⟨ε, _, hsym⟩ := hD.exists_sign
  let R : Polynomial ℂ := C ε * P.comp (C 1 - X)
  have hfac' (s : ℂ) : R.eval s * E s = H (1 - s) * xi s := by
    calc
      R.eval s * E s = P.eval (1 - s) * (ε * E s) := by simp [R]; ring
      _ = P.eval (1 - s) * E (1 - s) := by rw [hsym]
      _ = H (1 - s) * xi (1 - s) := hfac (1 - s)
      _ = H (1 - s) * xi s := by rw [xi_one_sub]
  obtain ⟨B₁, hB₁, hb₁⟩ := cubicQuotient_right_bounded hD R hfac'
  obtain ⟨ρ, C₀, hfin⟩ := finiteOrderEnvelope_standard hHfinite
  refine ⟨max B₁ B₂, hB₁.trans (le_max_left _ _), fun s hs₁ hs₂ => ?_⟩
  apply PhragmenLindelof.vertical_strip hH.diffContOnCl
    (CompletionGrowth.isBigO_strip_of_finiteOrder hfin) _ _ hs₁ hs₂
  · intro z hz
    have hz' : (1 - z).re = 2 := by simp [hz]; norm_num
    have h := hb₁ (1 - z) hz'
    rw [sub_sub_cancel] at h
    exact h.trans (le_max_left _ _)
  · intro z hz
    exact (hb₂ z hz).trans (le_max_right _ _)

/-- Every polynomial weight of the actual entire quotient is bounded on the whole strip. -/
theorem cubicQuotient_polynomial_strip_bounded {g : ℕ → ℂ} {E H : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (P Q : Polynomial ℂ)
    (hH : Differentiable ℂ H) (hHfinite : FiniteOrderEnvelope H)
    (hfac : ∀ z, P.eval z * E z = H z * xi z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      ‖Q.eval s * H s‖ ≤ B := by
  apply cubicQuotient_strip_bounded hD (Q * P) (Q.differentiable.mul hH)
    ((finiteOrderEnvelope_polynomial Q).mul hHfinite)
  intro z
  change (Q * P).eval z * E z = (Q.eval z * H z) * xi z
  rw [Polynomial.eval_mul, mul_assoc, hfac z]
  ring

/-- The cubic datum supplies the entire quotient and all its polynomial strip bounds. -/
theorem degreeThree_infiniteDeficits_or_stripBounded {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0) :
    (xiDeficitSupport E).Infinite ∨
      ∃ (P : Polynomial ℂ) (H : ℂ → ℂ), P.Monic ∧ P.eval 1 ≠ 0 ∧
        (∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞)) ∧
        Differentiable ℂ H ∧ FiniteOrderEnvelope H ∧ H 1 ≠ 0 ∧
        (∀ z, P.eval z * E z = H z * xi z) ∧
        ∀ Q : Polynomial ℂ, ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ,
          -1 ≤ s.re → s.re ≤ 2 → ‖Q.eval s * H s‖ ≤ B := by
  rcases degreeThree_infiniteDeficits_or_poleCleared hD hE1 with h | ⟨P, H, hm, hp, ho, hd, hg, h₁, hf⟩
  · exact Or.inl h
  · exact Or.inr ⟨P, H, hm, hp, ho, hd, hg, h₁, hf,
      fun Q => cubicQuotient_polynomial_strip_bounded hD P Q hd hg hf⟩

end RHTower.WeilHigherDenominator
