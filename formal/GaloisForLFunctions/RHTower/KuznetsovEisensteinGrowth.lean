import GaloisForLFunctions.RHTower.KuznetsovEisensteinCoefficient
import GaloisForLFunctions.RHTower.UnitClassInverseLBounds
import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay
import GaloisForLFunctions.HTGeometry.GammaGaussianEnvelopeDecay
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound

/-!
# Polynomial growth of the Poincaré–Eisenstein pairing on `½ < Re s ≤ σ₀`

On a closed vertical strip in `Re > 0`, `|Γ(σ+iτ)| ≤ C(1+|τ|)^M e^{−π|τ|/2}` for every `τ`, and on
every closed strip `|Γ(z)⁻¹| ≤ B e^{π|Im z|}`.  With `|L_u(w)| ≤ C(1+|Im w|)^9` for `1 < Re w ≤ A`
(`UnitClassInverseLBounds`), the Eisenstein coefficient grows at most like `(1+|t|)^9 e^{π|t|}`, while
`Γ(s̄₁+s−1)Γ(s̄₁−s)` decays like `e^{−π(|t−t₁|+|t+t₁|)/2} ≤ e^{π|t₁|}e^{−π|t|}`.  Hence the explicit
pairing `Φ(s)` of the Poincaré series with the Eisenstein series is `O((1+|Im s|)^K)` uniformly on
`½ < Re s ≤ σ₀` for `σ₀ < Re s₁` (`exists_bound_poincEisPairing`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

namespace Kuznetsov

/-- `|Γ(σ+iτ)| ≤ C(1+|τ|)^M e^{−π|τ|/2}` for all `τ` and `σ ∈ [a₀, a₁]`, `a₀ > 0`. -/
theorem exists_bound_Gamma_strip_all {a₀ : ℝ} (ha₀ : 0 < a₀) (a₁ : ℝ) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ σ τ : ℝ, a₀ ≤ σ → σ ≤ a₁ →
      ‖Complex.Gamma ((σ : ℂ) + τ * Complex.I)‖ ≤
        C * (1 + |τ|) ^ M * Real.exp (-(Real.pi * |τ| / 2)) := by
  obtain ⟨C₁, M, hC₁0, hC₁⟩ := HTGeometry.exists_bound_norm_Gamma_vertical_strip ha₀ a₁
  set K : Set ℂ := Icc a₀ (max a₀ a₁) ×ℂ Icc (-1) 1
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn Complex.Gamma K := fun z hz =>
    (Complex.differentiableAt_Gamma z fun m h => by
      have h1 : a₀ ≤ z.re := hz.1.1
      rw [h] at h1
      simp only [Complex.neg_re, Complex.natCast_re] at h1
      linarith [Nat.cast_nonneg (α := ℝ) m]).continuousAt.continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hcont
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ (a₀ : ℂ) ⟨by simp, by simp⟩)
  refine ⟨C₁ + C₂ * Real.exp (Real.pi / 2), M, by positivity, fun σ τ hσ0 hσ1 => ?_⟩
  have hpow : 1 ≤ (1 + |τ|) ^ M := one_le_pow₀ (by linarith [abs_nonneg τ])
  by_cases hτ : 1 ≤ |τ|
  · have h := hC₁ σ τ hσ0 hσ1 hτ
    have h2 : |τ| ^ M ≤ (1 + |τ|) ^ M := pow_le_pow_left₀ (abs_nonneg _) (by linarith) M
    calc ‖Complex.Gamma ((σ : ℂ) + τ * Complex.I)‖ ≤ C₁ * |τ| ^ M * Real.exp (-(Real.pi * |τ| / 2)) := h
      _ ≤ (C₁ + C₂ * Real.exp (Real.pi / 2)) * (1 + |τ|) ^ M * Real.exp (-(Real.pi * |τ| / 2)) := by
          gcongr
          linarith [mul_nonneg hC₂0 (Real.exp_pos (Real.pi / 2)).le]
  · push Not at hτ
    have hz : ((σ : ℂ) + τ * Complex.I) ∈ K := by
      refine ⟨⟨by simpa using hσ0, ?_⟩, ?_⟩
      · have : ((σ : ℂ) + τ * Complex.I).re = σ := by simp
        show ((σ : ℂ) + τ * Complex.I).re ≤ max a₀ a₁
        rw [this]
        exact le_max_of_le_right hσ1
      · have : ((σ : ℂ) + τ * Complex.I).im = τ := by simp
        show ((σ : ℂ) + τ * Complex.I).im ∈ Icc (-1 : ℝ) 1
        rw [this]
        exact abs_le.mp hτ.le
    have h := hC₂ _ hz
    have hexp : Real.exp (-(Real.pi / 2)) ≤ Real.exp (-(Real.pi * |τ| / 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    have hone : C₂ ≤ C₂ * Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * |τ| / 2)) := by
      have : 1 ≤ Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * |τ| / 2)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by nlinarith [Real.pi_pos])
      nlinarith
    calc ‖Complex.Gamma ((σ : ℂ) + τ * Complex.I)‖ ≤ C₂ := h
      _ ≤ C₂ * Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * |τ| / 2)) := hone
      _ ≤ (C₁ + C₂ * Real.exp (Real.pi / 2)) * (1 + |τ|) ^ M * Real.exp (-(Real.pi * |τ| / 2)) := by
          have hE : 0 ≤ Real.exp (-(Real.pi * |τ| / 2)) := (Real.exp_pos _).le
          have h1 : C₂ * Real.exp (Real.pi / 2) ≤ (C₁ + C₂ * Real.exp (Real.pi / 2)) * (1 + |τ|) ^ M := by
            nlinarith [mul_nonneg hC₂0 (Real.exp_pos (Real.pi / 2)).le]
          exact mul_le_mul_of_nonneg_right h1 hE

/-- `|Γ(z)⁻¹| ≤ B e^{π|Im z|}` on every closed vertical strip. -/
theorem exists_bound_inv_Gamma_strip_all (a b : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖(Complex.Gamma z)⁻¹‖ ≤ B * Real.exp (Real.pi * |z.im|) := by
  obtain ⟨B₁, hB₁, hB₁'⟩ := exists_bound_norm_inv_Gamma_strip a b
  set K : Set ℂ := Icc a (max a b) ×ℂ Icc (-1) 1
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn (fun z => (Complex.Gamma z)⁻¹) K :=
    Complex.differentiable_one_div_Gamma.continuous.continuousOn
  obtain ⟨B₂, hB₂⟩ := hK.exists_bound_of_continuousOn hcont
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ (a : ℂ) ⟨by simp, by simp⟩)
  refine ⟨B₁ + B₂, by positivity, fun z hza hzb => ?_⟩
  have hE : 1 ≤ Real.exp (Real.pi * |z.im|) := Real.one_le_exp (by positivity)
  by_cases hz : 1 ≤ |z.im|
  · calc ‖(Complex.Gamma z)⁻¹‖ ≤ B₁ * Real.exp (Real.pi * |z.im|) := hB₁' z hza hzb hz
      _ ≤ (B₁ + B₂) * Real.exp (Real.pi * |z.im|) := by gcongr; linarith
  · push Not at hz
    have hzK : z ∈ K := ⟨⟨hza, le_max_of_le_right hzb⟩, abs_le.mp hz.le⟩
    calc ‖(Complex.Gamma z)⁻¹‖ ≤ B₂ := hB₂ z hzK
      _ ≤ (B₁ + B₂) * Real.exp (Real.pi * |z.im|) := by nlinarith

/-- Half-steps to the right lose at most `e²` each: `‖Γ(σ+iy)‖ ≥ e^{−2(m+1)} ‖Γ(½+iy)‖` for
`½ ≤ σ ≤ 1 + m/2`, `y ≥ 1`. -/
theorem norm_Gamma_ge_half_line (m : ℕ) {σ y : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 + m / 2)
    (hy : 1 ≤ y) :
    Real.exp (-(2 * (m + 1))) * ‖Complex.Gamma (1 / 2 + (y : ℂ) * Complex.I)‖ ≤
      ‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * Complex.I)‖ := by
  have hne : ∀ x : ℝ, 0 < x → Complex.Gamma ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := fun x hx =>
    Complex.Gamma_ne_zero_of_re_pos (by simpa using hx)
  have hratio : ∀ a b : ℝ, 0 < a → a ≤ b → b - a ≤ 1 / 2 →
      Real.exp (-2) * ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * Complex.I)‖ := fun a b ha hab hw => by
    have h := RHTower.norm_Gamma_vertical_ratio_le_exp_two ha.le hab hw hy
    have hb : 0 < ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * Complex.I)‖ :=
      norm_pos_iff.mpr (hne b (by linarith))
    rw [div_le_iff₀ hb] at h
    rw [Real.exp_neg]
    calc (Real.exp 2)⁻¹ * ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ (Real.exp 2)⁻¹ * (Real.exp 2 * ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * Complex.I)‖) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * Complex.I)‖ := by
          rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_pos 2).ne', one_mul]
  induction m generalizing σ with
  | zero =>
    have h := hratio (1 / 2) σ (by norm_num) hσ1 (by simp at hσ2; linarith)
    simpa using h
  | succ m ih =>
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    by_cases hσm : σ ≤ 1 + m / 2
    · refine le_trans ?_ (ih hσ1 hσm)
      gcongr
      linarith
    · push Not at hσm
      have h1 := ih (σ := σ - 1 / 2) (by linarith) (by push_cast at hσ2 ⊢; linarith)
      have h2 := hratio (σ - 1 / 2) σ (by linarith) (by linarith) (by linarith)
      have e : Real.exp (-(2 * (((m + 1 : ℕ) : ℝ) + 1))) =
          Real.exp (-2) * Real.exp (-(2 * ((m : ℝ) + 1))) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [e, mul_assoc]
      calc Real.exp (-2) * (Real.exp (-(2 * ((m : ℝ) + 1))) *
            ‖Complex.Gamma (1 / 2 + (y : ℂ) * Complex.I)‖)
          ≤ Real.exp (-2) * ‖Complex.Gamma (((σ - 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ ≤ _ := h2

theorem norm_Gamma_half_line_ge (y : ℝ) :
    Real.sqrt Real.pi * Real.exp (-(Real.pi * |y| / 2)) ≤
      ‖Complex.Gamma (1 / 2 + (y : ℂ) * Complex.I)‖ := by
  have hsq := HTGeometry.norm_Gamma_half_add_I_sq y
  have hcosh : Real.cosh (Real.pi * y) ≤ Real.exp (Real.pi * |y|) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (Real.pi * y) ≤ Real.exp (Real.pi * |y|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self y) Real.pi_pos.le)
    have h2 : Real.exp (-(Real.pi * y)) ≤ Real.exp (Real.pi * |y|) :=
      Real.exp_le_exp.mpr (by nlinarith [neg_abs_le y, Real.pi_pos])
    linarith
  have hlow : Real.pi * Real.exp (-(Real.pi * |y|)) ≤
      ‖Complex.Gamma (1 / 2 + (y : ℂ) * Complex.I)‖ ^ 2 := by
    rw [hsq, Real.exp_neg, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left Real.pi_pos.le (Real.cosh_pos _) hcosh
  have hl : (Real.sqrt Real.pi * Real.exp (-(Real.pi * |y| / 2))) ^ 2 =
      Real.pi * Real.exp (-(Real.pi * |y|)) := by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  rw [← hl] at hlow
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hlow

/-- **The sharp reciprocal bound** `|Γ(z)⁻¹| ≤ B e^{π|Im z|/2}` on `½ ≤ Re z ≤ A`. -/
theorem exists_bound_inv_Gamma_sharp (A : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ A →
      ‖(Complex.Gamma z)⁻¹‖ ≤ B * Real.exp (Real.pi * |z.im| / 2) := by
  obtain ⟨B₀, hB₀, hB₀'⟩ := exists_bound_inv_Gamma_strip_all (1 / 2) A
  set m : ℕ := ⌈2 * A⌉₊
  have hm : A ≤ 1 + m / 2 := by
    have := Nat.le_ceil (2 * A); simp only [m]; linarith
  set B : ℝ := Real.exp (2 * (m + 1)) / Real.sqrt Real.pi + B₀ * Real.exp Real.pi
  refine ⟨B, by positivity, fun z hz1 hzA => ?_⟩
  have hE : 1 ≤ Real.exp (Real.pi * |z.im| / 2) := Real.one_le_exp (by positivity)
  by_cases hy : 1 ≤ |z.im|
  · -- reduce to `y = |Im z| ≥ 1`
    have hz : ‖Complex.Gamma z‖ = ‖Complex.Gamma ((z.re : ℂ) + ((|z.im| : ℝ) : ℂ) * Complex.I)‖ := by
      rcases le_or_gt 0 z.im with h | h
      · rw [abs_of_nonneg h, Complex.re_add_im]
      · rw [abs_of_neg h]
        have : (z.re : ℂ) + ((-z.im : ℝ) : ℂ) * Complex.I = conj z := by
          apply Complex.ext <;> simp
        rw [this, Complex.Gamma_conj, Complex.norm_conj]
    have h1 := norm_Gamma_ge_half_line m hz1 (hzA.trans hm) hy
    have h2 := norm_Gamma_half_line_ge |z.im|
    rw [abs_abs] at h2
    have hpos : 0 < Real.exp (-(2 * ((m : ℝ) + 1))) * (Real.sqrt Real.pi *
        Real.exp (-(Real.pi * |z.im| / 2))) := by positivity
    have hG : Real.exp (-(2 * ((m : ℝ) + 1))) * (Real.sqrt Real.pi *
        Real.exp (-(Real.pi * |z.im| / 2))) ≤ ‖Complex.Gamma z‖ := by
      rw [hz]
      exact le_trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) h1
    rw [norm_inv]
    calc ‖Complex.Gamma z‖⁻¹ ≤ (Real.exp (-(2 * ((m : ℝ) + 1))) * (Real.sqrt Real.pi *
          Real.exp (-(Real.pi * |z.im| / 2))))⁻¹ := inv_anti₀ hpos hG
      _ = Real.exp (2 * (m + 1)) / Real.sqrt Real.pi * Real.exp (Real.pi * |z.im| / 2) := by
          rw [mul_inv, mul_inv, ← Real.exp_neg, ← Real.exp_neg, neg_neg, neg_neg]
          ring
      _ ≤ B * Real.exp (Real.pi * |z.im| / 2) := by
          gcongr
          simp only [B]
          linarith [mul_nonneg hB₀ (Real.exp_pos Real.pi).le]
  · push Not at hy
    have h := hB₀' z hz1 hzA
    calc ‖(Complex.Gamma z)⁻¹‖ ≤ B₀ * Real.exp (Real.pi * |z.im|) := h
      _ ≤ B₀ * Real.exp Real.pi := by
          gcongr; nlinarith [Real.pi_pos]
      _ ≤ B * Real.exp (Real.pi * |z.im| / 2) := by
          have : 0 ≤ Real.exp (2 * (m + 1)) / Real.sqrt Real.pi := by positivity
          nlinarith [mul_nonneg hB₀ (Real.exp_pos Real.pi).le]

/-- `|L_u(w)| ≤ C(1+|Im w|)^9` for `1 < Re w ≤ A`. -/
theorem exists_bound_LU_strip (L : ℕ) [NeZero L] (A : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (u : (ZMod L)ˣ) (w : ℂ), 1 < w.re → w.re ≤ A →
      ‖SelbergMoebiusUnitClassL.LU L u w‖ ≤ C * (1 + |w.im|) ^ 9 := by
  obtain ⟨C₁, hC₁⟩ := SelbergMoebiusUnitClassL.exists_bound_LU_rect L A 9
  obtain ⟨C₂, hC₂0, hC₂⟩ := SelbergMoebiusUnitClassL.exists_bound_LU_high L
  refine ⟨|C₁| + C₂, by positivity, fun u w hw1 hwA => ?_⟩
  have hpow : 1 ≤ (1 + |w.im|) ^ 9 := one_le_pow₀ (by linarith [abs_nonneg w.im])
  by_cases ht : |w.im| ≤ 9
  · calc ‖SelbergMoebiusUnitClassL.LU L u w‖ ≤ C₁ := hC₁ u w hw1 hwA ht
      _ ≤ |C₁| := le_abs_self _
      _ ≤ (|C₁| + C₂) * (1 + |w.im|) ^ 9 := by nlinarith [abs_nonneg C₁]
  · push Not at ht
    have hlog : 0 ≤ Real.log |w.im| := Real.log_nonneg (by linarith)
    have hlog2 : Real.log |w.im| ≤ 1 + |w.im| := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < |w.im|)
      linarith
    calc ‖SelbergMoebiusUnitClassL.LU L u w‖ ≤ C₂ * Real.log |w.im| ^ 9 := hC₂ u w hw1 ht.le
      _ ≤ C₂ * (1 + |w.im|) ^ 9 := by gcongr
      _ ≤ (|C₁| + C₂) * (1 + |w.im|) ^ 9 := by nlinarith [abs_nonneg C₁]

/-- `|D_n(s)| ≤ C(1+|Im s|)^9` for `½ < Re s ≤ A`. -/
theorem exists_bound_Dn_strip (L : ℕ) [NeZero L] (σc : SL(2, ℤ)) (n : ℤ) (A : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ A →
      ‖SelbergEisensteinCoefficientSeries.Dn L σc n s‖ ≤ C * (1 + |s.im|) ^ 9 := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_LU_strip L (2 * A)
  set c : ℝ := (Fintype.card (ZMod L)ˣ : ℝ)
  refine ⟨c * C * 2 ^ 9 * (2 * (n.natAbs : ℝ) ^ 2), by positivity, fun s hs hsA => ?_⟩
  refine (SelbergEisensteinStarCriticalLine.norm_Dn_le_sq L σc n (by linarith)).trans ?_
  have hw : 1 < (2 * s).re := by simp; linarith
  have hwA : (2 * s).re ≤ 2 * A := by simp; linarith
  have him : |(2 * s).im| = 2 * |s.im| := by simp [abs_mul]
  have hu : ∀ u : (ZMod L)ˣ, ‖SelbergMoebiusUnitClassL.LU L u (2 * s)‖ ≤
      C * 2 ^ 9 * (1 + |s.im|) ^ 9 := fun u => by
    refine (hC u (2 * s) hw hwA).trans ?_
    rw [him, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    calc (1 + 2 * |s.im|) ^ 9 ≤ (2 * (1 + |s.im|)) ^ 9 :=
          pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg s.im]) 9
      _ = 2 ^ 9 * (1 + |s.im|) ^ 9 := by ring
  calc (∑ u : (ZMod L)ˣ, ‖SelbergMoebiusUnitClassL.LU L u (2 * s)‖) * (2 * (n.natAbs : ℝ) ^ 2)
      ≤ (∑ _u : (ZMod L)ˣ, C * 2 ^ 9 * (1 + |s.im|) ^ 9) * (2 * (n.natAbs : ℝ) ^ 2) := by
        gcongr with u
        exact hu u
    _ = c * C * 2 ^ 9 * (2 * (n.natAbs : ℝ) ^ 2) * (1 + |s.im|) ^ 9 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring

end Kuznetsov

namespace DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

variable {N : ℕ}

/-- `|c_μ(s)| ≤ C(1+|t|)^9 e^{π|t|/2}` on `½ < Re s ≤ A`. -/
theorem exists_bound_eisCoeff (v w : DeckSpace N) {n : ℤ} (hn : n ≠ 0) (A : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ A →
      ‖eisCoeff s v w n‖ ≤ C * (1 + |s.im|) ^ 9 * Real.exp (Real.pi * |s.im| / 2) := by
  have hD := fun g : Deck N => Kuznetsov.exists_bound_Dn_strip (N + 1) (Quotient.out g) n A
  choose CD hCD0 hCD using hD
  obtain ⟨B, hB0, hB⟩ := Kuznetsov.exists_bound_inv_Gamma_sharp A
  set D : ℝ := ∑ g : Deck N, CD g
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun g _ => hCD0 g
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  set K : ℝ := ‖v‖ * ‖w‖ * (2 * Real.pi ^ A * B * |(n : ℝ)| ^ A) * D
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Real.pi ^ A := Real.rpow_nonneg Real.pi_pos.le _
    positivity
  set c : ℝ := (Fintype.card (Deck N) : ℝ)
  refine ⟨c * c * K, by positivity, fun s hs hsA => ?_⟩
  have hL1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
  set E := (1 + |s.im|) ^ 9 * Real.exp (Real.pi * |s.im| / 2)
  have hE0 : 0 ≤ E := by positivity
  have hterm : ∀ q g : Deck N, ‖conj (v q) * (w (q * g⁻¹) *
      (cexp (-s * (Real.log ((N + 1 : ℕ) : ℝ) : ℂ)) * (2 * (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ *
        (((|(n : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) * ((((N + 1 : ℕ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))))) *
        SelbergEisensteinCoefficientSeries.Dn (N + 1) (Quotient.out g) n s))‖ ≤ K * E := by
    intro q g
    have h1 : ‖cexp (-s * (Real.log ((N + 1 : ℕ) : ℝ) : ℂ))‖ ≤ 1 := by
      have := SelbergPoincareContinuation.norm_exp_neg_mul_log (s := s) (σ := 0) hL1 (by linarith)
      rwa [neg_zero, Real.rpow_zero] at this
    have h2 : ‖(Real.pi : ℂ) ^ s‖ ≤ Real.pi ^ A := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hsA
    have h3 := hB s hs.le hsA
    have h4 : ‖(((|(n : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))‖ ≤ |(n : ℝ)| ^ A := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by simp; linarith)
    have h5 : ‖((((N + 1 : ℕ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hL1 (by simp)
    have h6 := hCD g s hs hsA
    have h6' : ‖SelbergEisensteinCoefficientSeries.Dn (N + 1) (Quotient.out g) n s‖ ≤
        D * (1 + |s.im|) ^ 9 :=
      h6.trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun g _ => hCD0 g)
        (Finset.mem_univ g)) (by positivity))
    have hv : ‖conj (v q)‖ ≤ ‖v‖ := by rw [Complex.norm_conj]; exact PiLp.norm_apply_le v q
    have hw : ‖w (q * g⁻¹)‖ ≤ ‖w‖ := PiLp.norm_apply_le w _
    simp only [norm_mul, Complex.norm_two]
    calc ‖conj (v q)‖ * (‖w (q * g⁻¹)‖ * (‖cexp (-s * (Real.log ((N + 1 : ℕ) : ℝ) : ℂ))‖ *
          (2 * ‖(Real.pi : ℂ) ^ s‖ * ‖(Complex.Gamma s)⁻¹‖ *
            (‖(((|(n : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))‖ *
              ‖((((N + 1 : ℕ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))‖)) *
          ‖SelbergEisensteinCoefficientSeries.Dn (N + 1) (Quotient.out g) n s‖))
        ≤ ‖v‖ * (‖w‖ * (1 * (2 * Real.pi ^ A * (B * Real.exp (Real.pi * |s.im| / 2)) *
            (|(n : ℝ)| ^ A * 1)) * (D * (1 + |s.im|) ^ 9))) := by
          gcongr
      _ = K * E := by simp only [K, E]; ring
  rw [eisCoeff, norm_mul]
  have hpre : ‖(2 * ((N + 1 : ℕ) : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_mul, Complex.norm_two, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  calc ‖(2 * ((N + 1 : ℕ) : ℂ))⁻¹‖ * ‖∑ q : Deck N, conj (v q) * ∑ g : Deck N, w (q * g⁻¹) *
        (cexp (-s * (Real.log ((N + 1 : ℕ) : ℝ) : ℂ)) * (2 * (Real.pi : ℂ) ^ s *
          (Complex.Gamma s)⁻¹ * (((|(n : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) *
            ((((N + 1 : ℕ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))))) *
          SelbergEisensteinCoefficientSeries.Dn (N + 1) (Quotient.out g) n s)‖
      ≤ 1 * ∑ q : Deck N, ∑ g : Deck N, K * E := by
        refine mul_le_mul hpre ?_ (norm_nonneg _) zero_le_one
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
        rw [Finset.mul_sum]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => hterm q g)
    _ = c * c * K * E := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, one_mul]
        ring
    _ = c * c * K * ((1 + |s.im|) ^ 9 * Real.exp (Real.pi * |s.im| / 2)) := rfl
    _ = c * c * K * (1 + |s.im|) ^ 9 * Real.exp (Real.pi * |s.im| / 2) := by ring

/-- **Polynomial growth of the Poincaré–Eisenstein pairing** on `½ < Re s ≤ σ₀ < Re s₁`. -/
theorem exists_bound_poincEisPairing {s₁ : ℂ} (hs₁ : 1 < s₁.re) (μ : ℝ) (v w : DeckSpace N)
    {n : ℤ} (hn : n ≠ 0) {σ₀ : ℝ} (hσ₀ : σ₀ < s₁.re) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ σ₀ →
      ‖poincEisPairing s₁ μ v w n s‖ ≤ C * (1 + |s.im|) ^ K * Real.exp (-(Real.pi * |s.im| / 2)) := by
  obtain ⟨Ce, hCe0, hCe⟩ := exists_bound_eisCoeff v w hn σ₀
  obtain ⟨C1, M1, hC10, hC1⟩ := Kuznetsov.exists_bound_Gamma_strip_all
    (a₀ := s₁.re - 1 / 2) (by linarith) (s₁.re + σ₀ - 1)
  obtain ⟨C2, M2, hC20, hC2⟩ := Kuznetsov.exists_bound_Gamma_strip_all
    (a₀ := s₁.re - σ₀) (by linarith) (s₁.re - 1 / 2)
  set Kc : ℝ := ‖((2 * Real.pi * μ : ℝ) : ℂ) ^ (-(conj s₁ - 1 / 2))‖ *
    ‖(2 : ℂ) ^ (conj s₁ - 1 / 2 - 1)‖ * ‖Complex.Gamma (conj s₁ - 1 / 2)‖ *
      ‖Complex.Gamma (2 * (conj s₁ - 1 / 2))‖⁻¹
  set T : ℝ := 1 + |s₁.im|
  have hT1 : 1 ≤ T := by simp only [T]; linarith [abs_nonneg s₁.im]
  refine ⟨2 * Ce * Kc * C1 * C2 * T ^ (M1 + M2), 9 + M1 + M2, by positivity, fun s hs hsσ => ?_⟩
  set t := s.im
  have hΓ1 : Complex.Gamma (conj s₁ - 1 / 2 + (s - 1 / 2)) =
      Complex.Gamma (((s₁.re + s.re - 1 : ℝ) : ℂ) + ((t - s₁.im : ℝ) : ℂ) * Complex.I) := by
    congr 1
    apply Complex.ext <;> simp [t] <;> ring
  have hΓ2 : Complex.Gamma (conj s₁ - 1 / 2 - (s - 1 / 2)) =
      Complex.Gamma (((s₁.re - s.re : ℝ) : ℂ) + ((-s₁.im - t : ℝ) : ℂ) * Complex.I) := by
    congr 1
    apply Complex.ext <;> simp [t]
  have h1 := hC1 (s₁.re + s.re - 1) (t - s₁.im) (by linarith) (by linarith)
  have h2 := hC2 (s₁.re - s.re) (-s₁.im - t) (by linarith) (by linarith)
  have he := hCe s hs hsσ
  have hsum : 2 * |t| ≤ |t - s₁.im| + |-s₁.im - t| := by
    calc 2 * |t| = |t - (-t)| := by rw [sub_neg_eq_add, ← two_mul, abs_mul, abs_two]
      _ ≤ |t - s₁.im| + |s₁.im - -t| := abs_sub_le t s₁.im (-t)
      _ = |t - s₁.im| + |-s₁.im - t| := by
          rw [show s₁.im - -t = -(-s₁.im - t) by ring, abs_neg]
  have hexp : Real.exp (Real.pi * |t| / 2) * Real.exp (-(Real.pi * |t - s₁.im| / 2)) *
      Real.exp (-(Real.pi * |-s₁.im - t| / 2)) ≤ Real.exp (-(Real.pi * |t| / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hp1 : (1 + |t - s₁.im|) ^ M1 ≤ T ^ M1 * (1 + |t|) ^ M1 := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ M1
    have := abs_sub t s₁.im
    nlinarith [abs_nonneg t, abs_nonneg s₁.im]
  have hp2 : (1 + |-s₁.im - t|) ^ M2 ≤ T ^ M2 * (1 + |t|) ^ M2 := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ M2
    have : |-s₁.im - t| ≤ |s₁.im| + |t| := by
      rw [show -s₁.im - t = -(s₁.im + t) by ring, abs_neg]; exact abs_add_le _ _
    nlinarith [abs_nonneg t, abs_nonneg s₁.im]
  have hKc0 : 0 ≤ Kc := by positivity
  set G1 := ‖Complex.Gamma (((s₁.re + s.re - 1 : ℝ) : ℂ) + ((t - s₁.im : ℝ) : ℂ) * Complex.I)‖
  set G2 := ‖Complex.Gamma (((s₁.re - s.re : ℝ) : ℂ) + ((-s₁.im - t : ℝ) : ℂ) * Complex.I)‖
  set E1 := Real.exp (-(Real.pi * |t - s₁.im| / 2))
  set E2 := Real.exp (-(Real.pi * |-s₁.im - t| / 2))
  set E0 := Real.exp (Real.pi * |t| / 2)
  have hnorm : ‖poincEisPairing s₁ μ v w n s‖ = 2 * Kc * (‖eisCoeff s v w n‖ * G1 * G2) := by
    rw [poincEisPairing, hΓ1, hΓ2]
    simp only [norm_mul, norm_div, Complex.norm_two, Kc, G1, G2]
    ring
  have hG1 : G1 ≤ C1 * (T ^ M1 * (1 + |t|) ^ M1) * E1 :=
    h1.trans (by gcongr)
  have hG2 : G2 ≤ C2 * (T ^ M2 * (1 + |t|) ^ M2) * E2 :=
    h2.trans (by gcongr)
  have hE : ‖eisCoeff s v w n‖ ≤ Ce * (1 + |t|) ^ 9 * E0 := he
  have hpow : (1 + |t|) ^ 9 * (1 + |t|) ^ M1 * (1 + |t|) ^ M2 = (1 + |t|) ^ (9 + M1 + M2) := by
    rw [← pow_add, ← pow_add]
  rw [hnorm]
  calc 2 * Kc * (‖eisCoeff s v w n‖ * G1 * G2)
      ≤ 2 * Kc * ((Ce * (1 + |t|) ^ 9 * E0) * (C1 * (T ^ M1 * (1 + |t|) ^ M1) * E1) *
          (C2 * (T ^ M2 * (1 + |t|) ^ M2) * E2)) := by
        gcongr
    _ = 2 * Ce * Kc * C1 * C2 * T ^ (M1 + M2) *
          ((1 + |t|) ^ 9 * (1 + |t|) ^ M1 * (1 + |t|) ^ M2) * (E0 * E1 * E2) := by
        rw [pow_add]; ring
    _ ≤ 2 * Ce * Kc * C1 * C2 * T ^ (M1 + M2) * (1 + |t|) ^ (9 + M1 + M2) *
          Real.exp (-(Real.pi * |t| / 2)) := by
        rw [hpow]
        gcongr

end DeckPointPair

end

end GaloisForLFunctions.RHTower
