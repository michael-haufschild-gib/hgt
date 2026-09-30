import GaloisForLFunctions.RHTower.ZetaLogDerivSelbergExplicitFormula
import GaloisForLFunctions.RHTower.ZetaLogDerivReflectedLeftEdge
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinNegativeHalfHorizontal

/-!
# Selberg's explicit formula at a given height, with a uniform remainder

For every height `t ≥ 64` there are rectangle heights `T₁ ∈ (t/2 − 1, t/2 + 1)`,
`T₂ ∈ (3t/2 − 1, 3t/2 + 1)` (from the Route-T horizontal control, `‖G'/G‖ ≪ (1 + log t)²` on the
horizontal edges) such that for every `x > 1` and every `s₀` with `|Im s₀ − t| ≤ t/8`,
`1/2 ≤ Re s₀ ≤ 1`, `ζ(s₀) ≠ 0`,

`‖ζ'/ζ(s₀) + Σ Λ(n)W_x(n)n^{−s₀} + Σ_ρ m_ρ K_x(ρ − s₀)‖ ≤ E(K, x, t)`,

the zero sum over the zeros in `[σ_L(2t), 2] × [T₁, T₂]`
(`exists_selberg_explicit_formula_at_height`). The remainder `E` is explicit
(`selbergHeightError`): it is `≪ x⁴(1 + log t)²/t^2 + x⁴/t + log⁹ t · x^{−3/8}/log x + 1/t`, and it
is at most `1` once `(log t)^{40} ≤ x ≤ t^{1/8}` and `t` is large
(`eventually_selbergHeightError_le_one`).
-/

noncomputable section

open Complex Set Filter

namespace RHTower

open Sieve

/-- Polylogarithmic horizontal control at an arbitrary height `τ` with `X/2 ≤ |τ| ≤ 2X`. -/
theorem exists_horizontal_height_polylog :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {X : ℕ} {τ : ℝ}, 12 ≤ X → (X : ℝ) / 2 ≤ |τ| → |τ| ≤ 2 * (X : ℝ) →
      ∃ T ∈ Ioo (τ - 1 / 2) (τ + 1 / 2), ∀ u ∈ Icc (-1 / 2 : ℝ) 2,
        zetaResidueUnit ((u : ℂ) + (T : ℂ) * I) ≠ 0 ∧
          ‖logDeriv zetaResidueUnit ((u : ℂ) + (T : ℂ) * I)‖ ≤ K * (1 + Real.log X) ^ (2 : ℕ) := by
  obtain ⟨Ce, Qe, Cj, Qj, hCe, hCj, hcontrol⟩ :=
    exists_zetaResidueUnit_negativeHalf_horizontal_logDeriv_control
  let C : ℝ := inghamDetectorHorizontalPolylogConstant Ce Qe Cj Qj
  refine ⟨|C|, abs_nonneg C, ?_⟩
  intro X τ hX hlo hhi
  obtain ⟨T, hT, N, hNL, hbound⟩ := hcontrol hX hlo hhi
  have hpoly := inghamDetectorHorizontalLogDerivBound_le_polylog
    (Ce := Ce) (Cj := Cj) (Qe := Qe) (Qj := Qj) (X := X) (N := N)
    hCe hCj (show 1 ≤ X by omega) hNL
  refine ⟨T, hT, fun u hu => ?_⟩
  obtain ⟨hne, hb⟩ := hbound u hu
  refine ⟨hne, ?_⟩
  have hn : ‖logDeriv zetaResidueUnit ((u : ℂ) + (T : ℂ) * I)‖ =
      ‖zetaLogDerivReg ((u : ℂ) + (T : ℂ) * I)‖ := by rw [zetaLogDerivReg, norm_neg]
  rw [hn]
  refine hb.trans (hpoly.trans ?_)
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)

/-- The left-edge constant `(2240/A) log⁹ T + log T + 8`. -/
def selbergLeftEdgeConstant (T : ℝ) : ℝ := 2240 / zetaLowerA * Real.log T ^ (9 : ℕ) + Real.log T + 8

/-- The uniform remainder of the explicit formula at height `t`. -/
def selbergHeightError (K x t : ℝ) : ℝ :=
  (2 * (2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 4) ^ 2)) *
      (K * (1 + Real.log t) ^ (2 : ℕ)) * 2 +
    8 * (2 * Real.exp (4 * Real.log x) / Real.log x) * (2 * Real.pi / (t / 4)) +
    2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 2 - 1)) * Real.pi +
    selbergLeftEdgeConstant (2 * t) * (2 * Real.exp (-(3 / 8) * Real.log x) / Real.log x) *
      (Real.pi / (3 / 8))) / (2 * Real.pi) + 1 / (t / 2 - 1)

/-- The rectangle zeros at height `t`. -/
def selbergHeightZeros (t T₁ T₂ : ℝ) : Finset ℂ :=
  zetaResidueUnitClosedRectangleZeros ((reflectedLeftAbscissa (2 * t) : ℂ) + (T₁ : ℂ) * I)
    ((2 : ℝ) + (T₂ : ℂ) * I)

/-- **Selberg's explicit formula at height `t`, uniformly in `x` and in `s₀` near `t`.** -/
theorem exists_selberg_explicit_formula_at_height :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 64 ≤ t → ∃ T₁ T₂ : ℝ,
      t / 2 - 1 < T₁ ∧ T₁ < t / 2 + 1 ∧ 3 * t / 2 - 1 < T₂ ∧ T₂ < 3 * t / 2 + 1 ∧
      ∀ x : ℝ, 1 < x → ∀ s₀ : ℂ, |s₀.im - t| ≤ t / 8 → 1 / 2 ≤ s₀.re → s₀.re ≤ 1 →
        riemannZeta s₀ ≠ 0 →
        ‖logDeriv riemannZeta s₀ + selbergVonMangoldtPoly x s₀ +
          ∑ w ∈ selbergHeightZeros t T₁ T₂,
            ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s₀)‖ ≤
          selbergHeightError K x t := by
  obtain ⟨K, hK, hhor⟩ := exists_horizontal_height_polylog
  refine ⟨K, hK, fun t ht => ?_⟩
  set X : ℕ := ⌊t⌋₊ with hXdef
  have hXle : (X : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hXgt : t - 1 < X := by have := Nat.lt_floor_add_one t; linarith
  have hX12 : 12 ≤ X := by
    have : (12 : ℝ) < X + 1 := by linarith
    exact_mod_cast (show (11 : ℝ) < X by linarith)
  obtain ⟨T₁, hT₁, hb₁⟩ := hhor (X := X) (τ := t / 2) hX12
    (by rw [abs_of_pos (by linarith)]; linarith) (by rw [abs_of_pos (by linarith)]; linarith)
  obtain ⟨T₂, hT₂, hb₂⟩ := hhor (X := X) (τ := 3 * t / 2) hX12
    (by rw [abs_of_pos (by linarith)]; linarith) (by rw [abs_of_pos (by linarith)]; linarith)
  refine ⟨T₁, T₂, by linarith [hT₁.1], by linarith [hT₁.2], by linarith [hT₂.1],
    by linarith [hT₂.2], fun x hx s₀ hs₀t hσ₀ hσ₁ hs₀ => ?_⟩
  set σL : ℝ := reflectedLeftAbscissa (2 * t) with hσL
  have h2t : 16 ≤ 2 * t := by linarith
  have hσL0 : 0 < σL := reflectedLeftAbscissa_pos h2t
  have hl2 := log_ge_of_sixteen_le h2t
  have hσL8 : σL ≤ 1 / 8 := by
    refine (reflectedLeftAbscissa_le h2t).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ^ 9 ≤ Real.log (2 * t) ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) hl2 9
    nlinarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hlogX : Real.log X ≤ Real.log t :=
    Real.log_le_log (by exact_mod_cast (show 0 < X by omega)) hXle
  set BH : ℝ := K * (1 + Real.log X) ^ (2 : ℕ) with hBH
  have hBH' : BH ≤ K * (1 + Real.log t) ^ (2 : ℕ) := by
    have h0 : 0 ≤ 1 + Real.log (X : ℝ) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ X by exact_mod_cast (show 1 ≤ X by omega))
      linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (by linarith) 2) hK
  have hs₀im : 7 * t / 8 ≤ s₀.im ∧ s₀.im ≤ 9 * t / 8 := by
    constructor <;> linarith [(abs_le.mp hs₀t).1, (abs_le.mp hs₀t).2]
  have hmain := norm_logDeriv_zeta_add_selberg_le (x := x) (c := 2) (σL := σL) (T₁ := T₁)
    (T₂ := T₂) (H := t / 4) (BH := BH) (BL := selbergLeftEdgeConstant (2 * t)) (s₀ := s₀)
    hx (by norm_num) le_rfl (by linarith) (by linarith) (by linarith [hT₁.1])
    (by linarith) (by linarith [hT₁.2, hs₀im.1]) (by linarith [hT₂.1, hs₀im.2]) hs₀
    (fun u hu => hb₁ u ⟨by linarith [hu.1], hu.2⟩)
    (fun u hu => hb₂ u ⟨by linarith [hu.1], hu.2⟩)
    (fun y hy => by
      have h := zetaResidueUnit_reflectedLeft_ne_zero_and_norm_logDeriv_le (T := 2 * t) (y := y)
        h2t (by rw [abs_of_pos (by linarith [hy.1, hT₁.1])]; linarith [hy.1, hT₁.1])
        (by rw [abs_of_pos (by linarith [hy.1, hT₁.1])]; linarith [hy.2, hT₂.2])
      exact ⟨h.1, h.2⟩)
  refine hmain.trans ?_
  -- uniform bounds on the four edge terms
  set A : ℝ := Real.exp (2 * (2 - s₀.re) * Real.log x) + Real.exp ((2 - s₀.re) * Real.log x)
    with hA
  have hA2 : A ≤ 2 * Real.exp (4 * Real.log x) := by
    have h1 : Real.exp (2 * (2 - s₀.re) * Real.log x) ≤ Real.exp (4 * Real.log x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp ((2 - s₀.re) * Real.log x) ≤ Real.exp (4 * Real.log x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hA0 : 0 ≤ A := by positivity
  have hE0 : 0 ≤ 2 * Real.exp (4 * Real.log x) := by positivity
  have hT₁0 : t / 2 - 1 ≤ T₁ := by linarith [hT₁.1]
  have hT₁pos : 0 < t / 2 - 1 := by linarith
  have hBH0 : 0 ≤ BH := by rw [hBH]; positivity
  have hBL0 : 0 ≤ selbergLeftEdgeConstant (2 * t) := by
    unfold selbergLeftEdgeConstant
    have := zetaLowerA_pos
    positivity
  have t1 : 2 * (A / (Real.log x * (t / 4) ^ 2) * BH * (2 - σL)) ≤
      2 * (2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 4) ^ 2)) *
        (K * (1 + Real.log t) ^ (2 : ℕ)) * 2 := by
    have h1 : A / (Real.log x * (t / 4) ^ 2) ≤
        2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 4) ^ 2) :=
      div_le_div_of_nonneg_right hA2 (by positivity)
    have h2 : 2 - σL ≤ 2 := by linarith
    have h3 : A / (Real.log x * (t / 4) ^ 2) * BH * (2 - σL) ≤
        2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 4) ^ 2) *
          (K * (1 + Real.log t) ^ (2 : ℕ)) * 2 := by
      apply mul_le_mul (mul_le_mul h1 hBH' hBH0 (by positivity)) h2 (by linarith)
      have : 0 ≤ K * (1 + Real.log t) ^ (2 : ℕ) := by positivity
      positivity
    linarith
  have t2 : 8 / (2 - 1) ^ 2 * (A / Real.log x) * (2 * Real.pi / (t / 4)) ≤
      8 * (2 * Real.exp (4 * Real.log x) / Real.log x) * (2 * Real.pi / (t / 4)) := by
    norm_num
    gcongr
  have t3 : A / (Real.log x * T₁) * (Real.pi / (2 - s₀.re)) ≤
      2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 2 - 1)) * Real.pi := by
    have h1 : A / (Real.log x * T₁) ≤ 2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 2 - 1)) :=
      div_le_div₀ hE0 hA2 (by positivity) (mul_le_mul_of_nonneg_left hT₁0 hl.le)
    have h2 : Real.pi / (2 - s₀.re) ≤ Real.pi :=
      div_le_self Real.pi_pos.le (by linarith)
    exact mul_le_mul h1 h2 (div_nonneg Real.pi_pos.le (by linarith)) (by positivity)
  have t4 : selbergLeftEdgeConstant (2 * t) *
        (2 * Real.exp ((σL - s₀.re) * Real.log x) / Real.log x) * (Real.pi / (s₀.re - σL)) ≤
      selbergLeftEdgeConstant (2 * t) * (2 * Real.exp (-(3 / 8) * Real.log x) / Real.log x) *
        (Real.pi / (3 / 8)) := by
    have h1 : Real.exp ((σL - s₀.re) * Real.log x) ≤ Real.exp (-(3 / 8) * Real.log x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.pi / (s₀.re - σL) ≤ Real.pi / (3 / 8) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
    apply mul_le_mul (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (by linarith) hl.le) hBL0) h2
      (by have := Real.pi_pos; exact div_nonneg this.le (by linarith)) (by positivity)
  have t5 : 1 / T₁ ≤ 1 / (t / 2 - 1) := one_div_le_one_div_of_le hT₁pos hT₁0
  unfold selbergHeightError
  have hπ : 0 < 2 * Real.pi := by positivity
  have hsum := add_le_add (add_le_add (add_le_add t1 t2) t3) t4
  have := div_le_div_of_nonneg_right hsum hπ.le
  linarith

/-- The left-edge constant is `≤ C (log t)⁹` with `C = 2⁹(2240/A + 9)`. -/
theorem selbergLeftEdgeConstant_two_mul_le {t : ℝ} (ht : 16 ≤ t) :
    selbergLeftEdgeConstant (2 * t) ≤ 2 ^ 9 * (2240 / zetaLowerA + 9) * Real.log t ^ (9 : ℕ) := by
  have hl := log_ge_of_sixteen_le ht
  have hl2 : Real.log (2 * t) ≤ 2 * Real.log t := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hl2' : 1 ≤ Real.log (2 * t) := by
    have := log_ge_of_sixteen_le (show 16 ≤ 2 * t by linarith); linarith
  have hA := zetaLowerA_pos
  have h9 : Real.log (2 * t) ^ (9 : ℕ) ≤ (2 * Real.log t) ^ (9 : ℕ) :=
    pow_le_pow_left₀ (by linarith) hl2 9
  have hpow1 : Real.log (2 * t) ≤ Real.log (2 * t) ^ (9 : ℕ) := by
    calc Real.log (2 * t) = Real.log (2 * t) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ Real.log (2 * t) ^ (9 : ℕ) := pow_le_pow_right₀ hl2' (by norm_num)
  have hpow0 : (1 : ℝ) ≤ Real.log (2 * t) ^ (9 : ℕ) := one_le_pow₀ hl2'
  unfold selbergLeftEdgeConstant
  have e : (2 * Real.log t) ^ (9 : ℕ) = 2 ^ 9 * Real.log t ^ (9 : ℕ) := by ring
  have hC : 0 ≤ 2240 / zetaLowerA := by positivity
  calc 2240 / zetaLowerA * Real.log (2 * t) ^ (9 : ℕ) + Real.log (2 * t) + 8
      ≤ (2240 / zetaLowerA + 9) * Real.log (2 * t) ^ (9 : ℕ) := by nlinarith
    _ ≤ (2240 / zetaLowerA + 9) * (2 * Real.log t) ^ (9 : ℕ) :=
        mul_le_mul_of_nonneg_left h9 (by positivity)
    _ = 2 ^ 9 * (2240 / zetaLowerA + 9) * Real.log t ^ (9 : ℕ) := by rw [e]; ring

/-- **The remainder is at most one** for `(log t)^{40} ≤ x ≤ t^{1/8}` and large `t`. -/
theorem eventually_selbergHeightError_le_one {K : ℝ} (hK : 0 ≤ K) :
    ∀ᶠ t in atTop, ∀ x : ℝ, Real.log t ^ (40 : ℕ) ≤ x → x ≤ t ^ ((1 : ℝ) / 8) →
      selbergHeightError K x t ≤ 1 := by
  set C : ℝ := 2 ^ 9 * (2240 / zetaLowerA + 9) with hCdef
  have hC0 : 0 ≤ C := by have := zetaLowerA_pos; positivity
  -- the dominating function tends to zero
  set h : ℝ → ℝ := fun t => (3200 * K / t + 136 * Real.pi * t ^ (-(1 / 2 : ℝ)) +
    C * 2 * (8 * Real.pi / 3) * (Real.log t ^ (6 : ℕ))⁻¹) / (2 * Real.pi) + 4 / t with hh
  have hlim : Tendsto h atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => 3200 * K / t) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun t : ℝ => 136 * Real.pi * t ^ (-(1 / 2 : ℝ))) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
        (136 * Real.pi)
    have h3 : Tendsto (fun t : ℝ => C * 2 * (8 * Real.pi / 3) * (Real.log t ^ (6 : ℕ))⁻¹)
        atTop (nhds 0) := by
      have hl6 : Tendsto (fun t : ℝ => Real.log t ^ (6 : ℕ)) atTop atTop :=
        (tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop
      simpa using (tendsto_inv_atTop_zero.comp hl6).const_mul (C * 2 * (8 * Real.pi / 3))
    have h4 : Tendsto (fun t : ℝ => 4 / t) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.div_atTop tendsto_id
    have := (((h1.add h2).add h3).div_const (2 * Real.pi)).add h4
    simpa [hh] using this
  have hev := hlim.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hev, eventually_ge_atTop (Real.exp (Real.exp 1)), eventually_ge_atTop 16]
    with t hht htexp ht16
  intro x hx1 hx2
  have ht0 : 0 < t := by linarith
  have hlt : Real.exp 1 ≤ Real.log t := by
    have := Real.log_le_log (Real.exp_pos _) htexp
    rwa [Real.log_exp] at this
  have hlt1 : 1 ≤ Real.log t := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hlt
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx1
  -- `log x ≥ 1`
  have hlx : 1 ≤ Real.log x := by
    have h1 : Real.log (Real.log t ^ (40 : ℕ)) ≤ Real.log x := Real.log_le_log (by positivity) hx1
    rw [Real.log_pow] at h1
    have h2 : 1 ≤ Real.log (Real.log t) := by
      have := Real.log_le_log (Real.exp_pos 1) hlt
      rwa [Real.log_exp] at this
    push_cast at h1
    linarith
  have hlx0 : 0 < Real.log x := by linarith
  -- `x⁴ ≤ t^{1/2}` and `x^{−3/8} ≤ (log t)^{−15}`
  have hx4 : Real.exp (4 * Real.log x) ≤ t ^ ((1 : ℝ) / 2) := by
    rw [show Real.exp (4 * Real.log x) = x ^ (4 : ℕ) by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hx0]; ring_nf]
    calc x ^ (4 : ℕ) ≤ (t ^ ((1 : ℝ) / 8)) ^ (4 : ℕ) := pow_le_pow_left₀ hx0.le hx2 4
      _ = t ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have hx38 : Real.exp (-(3 / 8) * Real.log x) ≤ (Real.log t ^ (15 : ℕ))⁻¹ := by
    have hxl : Real.log (Real.log t ^ (40 : ℕ)) ≤ Real.log x := Real.log_le_log (by positivity) hx1
    rw [Real.log_pow] at hxl
    push_cast at hxl
    rw [← Real.exp_log (show 0 < (Real.log t ^ (15 : ℕ))⁻¹ from
      inv_pos.mpr (pow_pos (by linarith) 15)), Real.log_inv, Real.log_pow]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  -- `(1 + log t)² ≤ 25 t^{1/2}`
  have hlogt : Real.log t ≤ 4 * t ^ ((1 : ℝ) / 4) := by
    have := Real.log_le_rpow_div ht0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    linarith [this]
  have ht14 : 1 ≤ t ^ ((1 : ℝ) / 4) := Real.one_le_rpow (by linarith) (by norm_num)
  have hsq : (1 + Real.log t) ^ (2 : ℕ) ≤ 25 * t ^ ((1 : ℝ) / 2) := by
    have e : t ^ ((1 : ℝ) / 2) = (t ^ ((1 : ℝ) / 4)) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
    rw [e]
    have h5 : 1 + Real.log t ≤ 5 * t ^ ((1 : ℝ) / 4) := by linarith
    calc (1 + Real.log t) ^ (2 : ℕ) ≤ (5 * t ^ ((1 : ℝ) / 4)) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (by linarith) h5 2
      _ = 25 * (t ^ ((1 : ℝ) / 4)) ^ (2 : ℕ) := by ring
  have hLE := selbergLeftEdgeConstant_two_mul_le ht16
  have hBL0 : 0 ≤ selbergLeftEdgeConstant (2 * t) := by
    unfold selbergLeftEdgeConstant
    have := zetaLowerA_pos
    have hl2 : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
    positivity
  have hsl : t ^ ((1 : ℝ) / 2) ≤ t ^ ((1 : ℝ) / 2) * Real.log x := by
    have := mul_le_mul_of_nonneg_left hlx (show 0 ≤ t ^ ((1 : ℝ) / 2) by positivity)
    linarith
  have ht12 : t ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2) = t := by
    rw [← Real.rpow_add ht0]; norm_num
  have ht12pos : 0 < t ^ ((1 : ℝ) / 2) := by positivity
  -- term bounds
  have T1 : 2 * (2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 4) ^ 2)) *
      (K * (1 + Real.log t) ^ (2 : ℕ)) * 2 ≤ 3200 * K / t := by
    have h1 : 2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 4) ^ 2) ≤
        2 * t ^ ((1 : ℝ) / 2) / (t / 4) ^ 2 := by
      have hQ : 0 < (t / 4) ^ 2 := by positivity
      calc 2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 4) ^ 2)
          ≤ 2 * Real.exp (4 * Real.log x) / (t / 4) ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) hQ (by nlinarith)
        _ ≤ 2 * t ^ ((1 : ℝ) / 2) / (t / 4) ^ 2 :=
            div_le_div_of_nonneg_right (by linarith) hQ.le
    have h2 : K * (1 + Real.log t) ^ (2 : ℕ) ≤ K * (25 * t ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hsq hK
    calc 2 * (2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 4) ^ 2)) *
          (K * (1 + Real.log t) ^ (2 : ℕ)) * 2
        ≤ 2 * (2 * t ^ ((1 : ℝ) / 2) / (t / 4) ^ 2) * (K * (25 * t ^ ((1 : ℝ) / 2))) * 2 := by
          gcongr
      _ = 3200 * K * (t ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2)) / t ^ 2 := by ring
      _ = 3200 * K / t := by rw [ht12]; field_simp
  have T2 : 8 * (2 * Real.exp (4 * Real.log x) / Real.log x) * (2 * Real.pi / (t / 4)) ≤
      128 * Real.pi * t ^ (-(1 / 2 : ℝ)) := by
    have h1 : 2 * Real.exp (4 * Real.log x) / Real.log x ≤ 2 * t ^ ((1 : ℝ) / 2) := by
      rw [div_le_iff₀ hlx0]; nlinarith
    have hneg : t ^ (-(1 / 2 : ℝ)) = (t ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [Real.rpow_neg ht0.le]
    calc 8 * (2 * Real.exp (4 * Real.log x) / Real.log x) * (2 * Real.pi / (t / 4))
        ≤ 8 * (2 * t ^ ((1 : ℝ) / 2)) * (2 * Real.pi / (t / 4)) := by gcongr
      _ = 128 * Real.pi * (t ^ ((1 : ℝ) / 2) / t) := by ring
      _ = 128 * Real.pi * t ^ (-(1 / 2 : ℝ)) := by
          rw [show (-(1 / 2 : ℝ)) = 1 / 2 - 1 by norm_num, Real.rpow_sub ht0, Real.rpow_one]
  have T3 : 2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 2 - 1)) * Real.pi ≤
      8 * Real.pi * t ^ (-(1 / 2 : ℝ)) := by
    have ht2 : t / 4 ≤ t / 2 - 1 := by linarith
    have h1 : 2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 2 - 1)) ≤
        2 * t ^ ((1 : ℝ) / 2) / (t / 4) := by
      have hQ : 0 < t / 4 := by positivity
      calc 2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 2 - 1))
          ≤ 2 * Real.exp (4 * Real.log x) / (t / 4) :=
            div_le_div_of_nonneg_left (by positivity) hQ (by nlinarith)
        _ ≤ 2 * t ^ ((1 : ℝ) / 2) / (t / 4) :=
            div_le_div_of_nonneg_right (by linarith) hQ.le
    have hneg : t ^ (-(1 / 2 : ℝ)) = (t ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [Real.rpow_neg ht0.le]
    calc 2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 2 - 1)) * Real.pi
        ≤ 2 * t ^ ((1 : ℝ) / 2) / (t / 4) * Real.pi := by gcongr
      _ = 8 * Real.pi * (t ^ ((1 : ℝ) / 2) / t) := by ring
      _ = 8 * Real.pi * t ^ (-(1 / 2 : ℝ)) := by
          rw [show (-(1 / 2 : ℝ)) = 1 / 2 - 1 by norm_num, Real.rpow_sub ht0, Real.rpow_one]
  have T4 : selbergLeftEdgeConstant (2 * t) * (2 * Real.exp (-(3 / 8) * Real.log x) /
      Real.log x) * (Real.pi / (3 / 8)) ≤
      C * 2 * (8 * Real.pi / 3) * (Real.log t ^ (6 : ℕ))⁻¹ := by
    have h1 : 2 * Real.exp (-(3 / 8) * Real.log x) / Real.log x ≤
        2 * (Real.log t ^ (15 : ℕ))⁻¹ := by
      rw [div_le_iff₀ hlx0]
      have : 0 ≤ (Real.log t ^ (15 : ℕ))⁻¹ := by positivity
      nlinarith
    have e : Real.log t ^ (9 : ℕ) * (Real.log t ^ (15 : ℕ))⁻¹ = (Real.log t ^ (6 : ℕ))⁻¹ := by
      have : Real.log t ≠ 0 := by linarith
      field_simp
    calc selbergLeftEdgeConstant (2 * t) * (2 * Real.exp (-(3 / 8) * Real.log x) /
          Real.log x) * (Real.pi / (3 / 8))
        ≤ (C * Real.log t ^ (9 : ℕ)) * (2 * (Real.log t ^ (15 : ℕ))⁻¹) * (Real.pi / (3 / 8)) := by
          gcongr
      _ = C * 2 * (8 * Real.pi / 3) * (Real.log t ^ (9 : ℕ) * (Real.log t ^ (15 : ℕ))⁻¹) := by
          ring
      _ = C * 2 * (8 * Real.pi / 3) * (Real.log t ^ (6 : ℕ))⁻¹ := by rw [e]
  have T5 : 1 / (t / 2 - 1) ≤ 4 / t := by
    rw [div_le_div_iff₀ (by linarith) ht0]; linarith
  unfold selbergHeightError
  have hπ : 0 < 2 * Real.pi := by positivity
  have hsum := add_le_add (add_le_add (add_le_add T1 T2) T3) T4
  have hdiv := div_le_div_of_nonneg_right hsum hπ.le
  have hfin : (3200 * K / t + 128 * Real.pi * t ^ (-(1 / 2 : ℝ)) +
      8 * Real.pi * t ^ (-(1 / 2 : ℝ)) +
      C * 2 * (8 * Real.pi / 3) * (Real.log t ^ (6 : ℕ))⁻¹) / (2 * Real.pi) + 4 / t = h t := by
    rw [hh]; ring
  linarith

end RHTower
