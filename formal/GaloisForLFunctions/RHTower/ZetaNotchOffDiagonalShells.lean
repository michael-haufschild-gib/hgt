import GaloisForLFunctions.RHTower.ZetaNotchDetuningShells

/-!
# The off-diagonal of the twisted moment, with decay in the twist

The off-diagonal of the windowed twisted moment at the twist `h/k` was bounded in
`ZetaNotchTwistedOffDiagonal` uniformly in the twist. Here the far pairs keep their detuning
`Δ_P`:

* direct (`exists_norm_directOff_le_far`):
  `‖Σ_off‖ ≤ C (L 𝒩(h,k,δ) + L Σ_P farWeight(P))`, where `farWeight = pairWeight (LΔ_P)^{−K}` on the
  `δ`-detuned pairs. By `tsum_farWeight_le` this decays like `√(k/h)`.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

/-! ## The direct off-diagonal -/

/-- **Direct off-diagonal bound with detuning.** -/
theorem exists_norm_directOff_le_far (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L δ : ℝ}, 0 < L → 0 < δ → ∀ {h k : ℕ}, 0 < h → 0 < k →
      ‖directOff L h k‖ ≤
        C * (L * nearMass L h k δ + L * ∑' P, farWeight L δ K h k P) := by
  obtain ⟨CV, hCV, hV⟩ := exists_norm_smoothAFECutoff_le_min
  set A : ℝ := blockWindowConst K * 2 ^ K with hA
  have hA0 : 0 ≤ A := mul_nonneg (blockWindowConst_nonneg K) (by positivity)
  refine ⟨2 * CV * (1 + A), by positivity, fun {L δ} hL hδ {h k} hh hk => ?_⟩
  set ξ : ℝ := Real.log h - Real.log k with hξ
  set f : ℕ × ℕ → ℂ := fun P => (pairAmp P : ℂ) * smoothAFECutoff (pairProd P / L) *
    windowHat L (ξ - pairFreq P) with hf
  set S : Set (ℕ × ℕ) := {P : ℕ × ℕ | (P.1 + 1) * h = (P.2 + 1) * k}ᶜ with hS
  have hnear : Summable (fun P : ℕ × ℕ => if nearRes h k δ P then pairWeight L P else 0) := by
    refine Summable.of_nonneg_of_le (fun P => ?_) (fun P => ?_) (summable_pairWeight hL.le)
    · split_ifs
      · exact pairWeight_nonneg hL.le P
      · exact le_refl _
    · split_ifs
      · exact le_refl _
      · exact pairWeight_nonneg hL.le P
  have hK2 : Summable (farWeight L δ K h k) := by
    refine Summable.of_nonneg_of_le (farWeight_nonneg hL.le K h k) (fun P => ?_)
      ((summable_pairWeight hL.le).mul_right ((L * δ) ^ K)⁻¹)
    unfold farWeight
    split_ifs with hfar
    · exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hfar.2 hL.le) K))
        (pairWeight_nonneg hL.le P)
    · exact mul_nonneg (pairWeight_nonneg hL.le P) (inv_nonneg.mpr (by positivity))
  set b : ℕ × ℕ → ℝ := fun P => CV * (2 * L * (if nearRes h k δ P then pairWeight L P else 0) +
    2 * L * A * farWeight L δ K h k P) with hb
  have hb0 : ∀ P, 0 ≤ b P := fun P => by
    simp only [hb]
    apply mul_nonneg hCV
    apply add_nonneg
    · apply mul_nonneg (by positivity)
      split_ifs
      · exact pairWeight_nonneg hL.le P
      · exact le_refl _
    · exact mul_nonneg (by positivity) (farWeight_nonneg hL.le K h k P)
  have hbs : Summable b := ((hnear.mul_left (2 * L)).add (hK2.mul_left (2 * L * A))).mul_left CV
  have hpt : ∀ P ∈ S, ‖f P‖ ≤ b P := by
    intro P hP
    have hP' : (P.2 + 1) * k ≠ (P.1 + 1) * h := fun he => hP he.symm
    have hVb : pairAmp P * ‖smoothAFECutoff (pairProd P / L)‖ ≤ CV * pairWeight L P := by
      rw [pairWeight_eq]
      have := hV (div_pos (pairProd_pos P) hL)
      rw [one_div_div] at this
      calc pairAmp P * ‖smoothAFECutoff (pairProd P / L)‖
          ≤ pairAmp P * (CV * min 1 (L / pairProd P)) :=
            mul_le_mul_of_nonneg_left this (pairAmp_pos P).le
        _ = CV * (pairAmp P * min 1 (L / pairProd P)) := by ring
    have hfn : ‖f P‖ = pairAmp P * ‖smoothAFECutoff (pairProd P / L)‖ *
        ‖windowHat L (ξ - pairFreq P)‖ := by
      simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pairAmp_pos P)]
    rw [hfn]
    have hw0 := pairWeight_nonneg hL.le P
    have hfar0 := farWeight_nonneg hL.le (δ := δ) K h k P
    rcases nearRes_or_le hh hk hP' (δ := δ) with hn | hsep
    · have hw := norm_windowHat_le hL (ξ - pairFreq P)
      calc pairAmp P * ‖smoothAFECutoff (pairProd P / L)‖ * ‖windowHat L (ξ - pairFreq P)‖
          ≤ CV * pairWeight L P * (2 * L) :=
            mul_le_mul hVb hw (norm_nonneg _) (by positivity)
        _ ≤ b P := by
            simp only [hb, if_pos hn]
            have : 0 ≤ CV * (2 * L * A * farWeight L δ K h k P) := by positivity
            nlinarith
    · have hdet : detuning h k P = |ξ - pairFreq P| := by
        unfold detuning; rw [abs_sub_comm]
      have hη : δ ≤ |ξ - pairFreq P| := by rw [abs_sub_comm]; exact hsep
      have hη0 : ξ - pairFreq P ≠ 0 := fun h0 => by
        rw [h0, abs_zero] at hη; linarith
      have hfarP : farWeight L δ K h k P = pairWeight L P * ((L * |ξ - pairFreq P|) ^ K)⁻¹ := by
        unfold farWeight
        rw [if_pos ⟨hP', by rw [hdet]; exact hη⟩, hdet]
      have hw := norm_windowHat_le_pow K hL hη0
      rw [← hA] at hw
      calc pairAmp P * ‖smoothAFECutoff (pairProd P / L)‖ * ‖windowHat L (ξ - pairFreq P)‖
          ≤ CV * pairWeight L P * (2 * L * A / (L * |ξ - pairFreq P|) ^ K) :=
            mul_le_mul hVb hw (norm_nonneg _) (by positivity)
        _ = CV * (2 * L * A * farWeight L δ K h k P) := by
            rw [hfarP, div_eq_mul_inv]; ring
        _ ≤ b P := by
            simp only [hb]
            have : 0 ≤ CV * (2 * L * (if nearRes h k δ P then pairWeight L P else 0)) := by
              apply mul_nonneg hCV
              apply mul_nonneg (by positivity)
              split_ifs
              · exact hw0
              · exact le_refl _
            linarith
  have hfs : Summable (fun P : S => ‖f P‖) := (summable_directFamily hL ξ).norm.subtype S
  calc ‖directOff L h k‖ ≤ ∑' P : S, ‖f P‖ := norm_tsum_le_tsum_norm hfs
    _ ≤ ∑' P : S, b P := hfs.tsum_le_tsum (fun P => hpt P.1 P.2) (hbs.subtype S)
    _ ≤ ∑' P, b P := Summable.tsum_subtype_le b S hb0 hbs
    _ = CV * (2 * L * nearMass L h k δ + 2 * L * A * ∑' P, farWeight L δ K h k P) := by
        simp only [hb]
        rw [tsum_mul_left, Summable.tsum_add (hnear.mul_left _) (hK2.mul_left _), tsum_mul_left,
          tsum_mul_left]
        rfl
    _ ≤ 2 * CV * (1 + A) * (L * nearMass L h k δ + L * ∑' P, farWeight L δ K h k P) := by
        have hN := nearMass_nonneg hL.le h k δ
        have hW : 0 ≤ ∑' P, farWeight L δ K h k P := tsum_nonneg (farWeight_nonneg hL.le K h k)
        have h1 : 0 ≤ 2 * CV * A * (L * nearMass L h k δ) := by positivity
        have h2 : 0 ≤ 2 * CV * (L * ∑' P, farWeight L δ K h k P) := by positivity
        nlinarith

/-! ## The dual off-diagonal -/

/-- The small-pair weight `(MN)^{−1/4}/Δ_P` on the non-diagonal pairs with `MN < L` and
`δ ≤ Δ_P < 1/8` (twist `h/k`). -/
def smallWeight (L δ : ℝ) (h k : ℕ) (P : ℕ × ℕ) : ℝ :=
  if (P.2 + 1) * k ≠ (P.1 + 1) * h ∧ pairProd P < L ∧ δ ≤ detuning h k P ∧ detuning h k P < 1 / 8
  then pairProd P ^ (-(1 / 4 : ℝ)) / detuning h k P else 0

theorem smallWeight_nonneg (L δ : ℝ) (h k : ℕ) (P : ℕ × ℕ) : 0 ≤ smallWeight L δ h k P := by
  unfold smallWeight
  split_ifs
  · exact div_nonneg (Real.rpow_nonneg (pairProd_pos P).le _) (detuning_nonneg h k P)
  · exact le_refl _

theorem rpow_quarter_le {L x : ℝ} (hx : 0 < x) (hxL : x < L) :
    x ^ (-(1 / 4 : ℝ)) ≤ L ^ (5 / 4 : ℝ) * x ^ (-(3 / 2 : ℝ)) := by
  have e : x ^ (-(1 / 4 : ℝ)) = x ^ (5 / 4 : ℝ) * x ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hx]; norm_num
  rw [e]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx.le hxL.le (by norm_num))
    (Real.rpow_nonneg hx.le _)

theorem summable_smallWeight {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (h k : ℕ) :
    Summable (smallWeight L δ h k) := by
  refine Summable.of_nonneg_of_le (smallWeight_nonneg L δ h k) (fun P => ?_)
    ((summable_pairProd_rpow (s := 3 / 2) (by norm_num)).mul_left (L ^ (5 / 4 : ℝ) / δ))
  unfold smallWeight
  split_ifs with hc
  · obtain ⟨-, hPL, hδΔ, -⟩ := hc
    have hP := pairProd_pos P
    calc pairProd P ^ (-(1 / 4 : ℝ)) / detuning h k P ≤ pairProd P ^ (-(1 / 4 : ℝ)) / δ :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hP.le _) hδ hδΔ
      _ ≤ L ^ (5 / 4 : ℝ) * pairProd P ^ (-(3 / 2 : ℝ)) / δ :=
          div_le_div_of_nonneg_right (rpow_quarter_le hP hPL) hδ.le
      _ = L ^ (5 / 4 : ℝ) / δ * pairProd P ^ (-(3 / 2 : ℝ)) := by ring
  · exact mul_nonneg (by positivity) (Real.rpow_nonneg (pairProd_pos P).le _)

/-- The uniform tail factor `(L/8)^{−K} + e^{−L²/128}`. -/
def dualTailFactor (L : ℝ) (K : ℕ) : ℝ := ((L / 8) ^ K)⁻¹ + Real.exp (-(L ^ 2) / 128)

theorem dualTailFactor_nonneg {L : ℝ} (hL : 0 ≤ L) (K : ℕ) : 0 ≤ dualTailFactor L K := by
  unfold dualTailFactor; positivity

theorem detuning_swap_eq (h k : ℕ) (P : ℕ × ℕ) :
    detuning k h P = |Real.log h - Real.log k + pairFreq P| := by
  unfold detuning
  congr 1
  ring

theorem pairProd_rpow_three_halves (P : ℕ × ℕ) :
    pairProd P ^ (-(3 / 2 : ℝ)) = pairAmp P * (pairProd P)⁻¹ := by
  rw [show (-(3 / 2 : ℝ)) = -(1 + 1 / 2) by norm_num, ← pairAmp_mul_rpow P 1, Real.rpow_neg_one]

theorem L_sq_le_rpow {L : ℝ} (hL : 1 ≤ L) : L ^ 2 ≤ L ^ (5 / 2 : ℝ) := by
  rw [show (L ^ 2 : ℝ) = L ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

/-- The `K`-fold dual-line bound, per pair. -/
theorem pairAmp_mul_dual_le_Kfold {CK : ℝ} {K : ℕ} {L Δ : ℝ} (P : ℕ × ℕ) (hL : 0 < L) {J : ℝ}
    (hJ : J ≤ CK / (pairProd P * L) * (L ^ 3 / (L * Δ) ^ K + L ^ 3 * Real.exp (-(L ^ 2) / 32))) :
    pairAmp P * J ≤ CK * (L ^ 2 * pairProd P ^ (-(3 / 2 : ℝ))) *
      (((L * Δ) ^ K)⁻¹ + Real.exp (-(L ^ 2) / 32)) := by
  have hP := pairProd_pos P
  have e : pairAmp P * (CK / (pairProd P * L) * (L ^ 3 / (L * Δ) ^ K + L ^ 3 *
      Real.exp (-(L ^ 2) / 32))) = CK * (L ^ 2 * pairProd P ^ (-(3 / 2 : ℝ))) *
        (((L * Δ) ^ K)⁻¹ + Real.exp (-(L ^ 2) / 32)) := by
    rw [pairProd_rpow_three_halves]
    field_simp
  rw [← e]
  exact mul_le_mul_of_nonneg_left hJ (pairAmp_pos P).le

/-- Large pairs: the `K`-fold dual-line bound is sharp. -/
theorem dual_large_le {CK L Δ δ : ℝ} (hCK : 0 ≤ CK) {K : ℕ} (hL : 16 ≤ L) (P : ℕ × ℕ)
    (hbig : L ≤ pairProd P) {h k : ℕ} (hfarP : farWeight L δ K k h P =
      pairWeight L P * ((L * Δ) ^ K)⁻¹) {J : ℝ}
    (hJ : pairAmp P * J ≤ CK * (L ^ 2 * pairProd P ^ (-(3 / 2 : ℝ))) *
      (((L * Δ) ^ K)⁻¹ + Real.exp (-(L ^ 2) / 32))) :
    pairAmp P * J ≤ CK * L * farWeight L δ K k h P +
      CK * L ^ 2 * dualTailFactor L K * pairProd P ^ (-(3 / 2 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hPpos := pairProd_pos P
  have hpw : pairWeight L P = pairAmp P * (L / pairProd P) := by
    rw [pairWeight_eq, min_eq_right ((div_le_one hPpos).mpr hbig)]
  have hLw : L ^ 2 * pairProd P ^ (-(3 / 2 : ℝ)) = L * pairWeight L P := by
    rw [hpw, pairProd_rpow_three_halves]
    field_simp
  have he : Real.exp (-(L ^ 2) / 32) ≤ dualTailFactor L K := by
    unfold dualTailFactor
    have : Real.exp (-(L ^ 2) / 32) ≤ Real.exp (-(L ^ 2) / 128) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have : 0 ≤ ((L / 8) ^ K)⁻¹ := by positivity
    linarith
  have hq0 : 0 ≤ L ^ 2 * pairProd P ^ (-(3 / 2 : ℝ)) :=
    mul_nonneg (sq_nonneg L) (Real.rpow_nonneg hPpos.le _)
  calc pairAmp P * J ≤ CK * (L ^ 2 * pairProd P ^ (-(3 / 2 : ℝ))) *
        (((L * Δ) ^ K)⁻¹ + Real.exp (-(L ^ 2) / 32)) := hJ
    _ = CK * L * (pairWeight L P * ((L * Δ) ^ K)⁻¹) +
          CK * (L ^ 2 * pairProd P ^ (-(3 / 2 : ℝ))) * Real.exp (-(L ^ 2) / 32) := by
        rw [mul_add, hLw]; ring
    _ ≤ CK * L * (pairWeight L P * ((L * Δ) ^ K)⁻¹) +
          CK * (L ^ 2 * pairProd P ^ (-(3 / 2 : ℝ))) * dualTailFactor L K := by
        gcongr
    _ = _ := by rw [← hfarP]; ring

/-- Small pairs far from the twist line: the loss is absorbed by `(L/8)^{−K}`. -/
theorem dual_small_far_le {CK L Δ : ℝ} (hCK : 0 ≤ CK) {K : ℕ} (hL : 16 ≤ L) (P : ℕ × ℕ)
    (hfar8 : 1 / 8 ≤ Δ) {J : ℝ}
    (hJ : pairAmp P * J ≤ CK * (L ^ 2 * pairProd P ^ (-(3 / 2 : ℝ))) *
      (((L * Δ) ^ K)⁻¹ + Real.exp (-(L ^ 2) / 32))) :
    pairAmp P * J ≤ CK * L ^ 2 * dualTailFactor L K * pairProd P ^ (-(3 / 2 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hp8 : ((L * Δ) ^ K)⁻¹ ≤ ((L / 8) ^ K)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by nlinarith) K)
  have he : Real.exp (-(L ^ 2) / 32) ≤ Real.exp (-(L ^ 2) / 128) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hq0 : 0 ≤ CK * (L ^ 2 * pairProd P ^ (-(3 / 2 : ℝ))) :=
    mul_nonneg hCK (mul_nonneg (sq_nonneg L) (Real.rpow_nonneg (pairProd_pos P).le _))
  calc pairAmp P * J ≤ CK * (L ^ 2 * pairProd P ^ (-(3 / 2 : ℝ))) *
        (((L * Δ) ^ K)⁻¹ + Real.exp (-(L ^ 2) / 32)) := hJ
    _ ≤ CK * (L ^ 2 * pairProd P ^ (-(3 / 2 : ℝ))) * dualTailFactor L K := by
        unfold dualTailFactor
        exact mul_le_mul_of_nonneg_left (by linarith) hq0
    _ = _ := by ring

theorem pairAmp_mul_rpow_quarter (P : ℕ × ℕ) {L : ℝ} (hL : 0 < L) :
    pairAmp P * (pairProd P * L) ^ (1 / 4 : ℝ) = pairProd P ^ (-(1 / 4 : ℝ)) * L ^ (1 / 4 : ℝ) := by
  rw [Real.mul_rpow (pairProd_pos P).le hL.le, ← mul_assoc,
    show pairProd P ^ (1 / 4 : ℝ) = pairProd P ^ (-(-(1 / 4) : ℝ)) by norm_num, pairAmp_mul_rpow]
  norm_num

theorem rpow_quarter_mul_inv_sqrt {L : ℝ} (hL : 0 < L) :
    L ^ (1 / 4 : ℝ) * (1 / Real.sqrt L) = L ^ (-(1 / 4 : ℝ)) := by
  have e : 1 / Real.sqrt L = L ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hL.le, one_div]
  rw [e, ← Real.rpow_add hL]
  norm_num

theorem small_tail_le {L : ℝ} (hL : 0 < L) (P : ℕ × ℕ) (hsmall : pairProd P < L) :
    pairProd P ^ (-(1 / 4 : ℝ)) * L ^ (1 / 4 : ℝ) * L ≤
      L ^ (5 / 2 : ℝ) * pairProd P ^ (-(3 / 2 : ℝ)) := by
  have hPpos := pairProd_pos P
  have h1 := rpow_quarter_le hPpos hsmall
  have h2 : L ^ (1 / 4 : ℝ) * L = L ^ (5 / 4 : ℝ) := by
    calc L ^ (1 / 4 : ℝ) * L = L ^ (1 / 4 : ℝ) * L ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = L ^ (5 / 4 : ℝ) := by rw [← Real.rpow_add hL]; norm_num
  have h3 : L ^ (5 / 4 : ℝ) * L ^ (5 / 4 : ℝ) = L ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_add hL]; norm_num
  calc pairProd P ^ (-(1 / 4 : ℝ)) * L ^ (1 / 4 : ℝ) * L
      = pairProd P ^ (-(1 / 4 : ℝ)) * L ^ (5 / 4 : ℝ) := by rw [mul_assoc, h2]
    _ ≤ (L ^ (5 / 4 : ℝ) * pairProd P ^ (-(3 / 2 : ℝ))) * L ^ (5 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = L ^ (5 / 2 : ℝ) * pairProd P ^ (-(3 / 2 : ℝ)) := by rw [← h3]; ring

/-- Small pairs near the twist line: the right-line bound. -/
theorem dual_small_near_le {CR L Δ : ℝ} (hCR : 0 ≤ CR) {K : ℕ} (hL : 16 ≤ L) (P : ℕ × ℕ)
    (hsmall : pairProd P < L) {J W : ℝ} (hJW : J ≤ W +
      CR * (pairProd P * L) ^ (1 / 4 : ℝ) * (1 / Real.sqrt L / Δ + L * Real.exp (-(L ^ 2) / 128)))
    (hW : W ≤ 2 * L * (blockWindowConst K * 2 ^ K) / (L * Δ) ^ K) :
    pairAmp P * J ≤ 2 * L * (blockWindowConst K * 2 ^ K) *
        (pairWeight L P * ((L * Δ) ^ K)⁻¹) +
      CR * L ^ (-(1 / 4 : ℝ)) * (pairProd P ^ (-(1 / 4 : ℝ)) / Δ) +
      CR * L ^ (5 / 2 : ℝ) * dualTailFactor L K * pairProd P ^ (-(3 / 2 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hPpos := pairProd_pos P
  have hAmp := pairAmp_pos P
  have hpw : pairWeight L P = pairAmp P := by
    rw [pairWeight_eq, min_eq_left ((one_le_div hPpos).mpr hsmall.le), mul_one]
  have hq := pairAmp_mul_rpow_quarter P hL0
  have hLq := rpow_quarter_mul_inv_sqrt hL0
  have hLe := small_tail_le hL0 P hsmall
  have he : Real.exp (-(L ^ 2) / 128) ≤ dualTailFactor L K := by
    unfold dualTailFactor
    have : 0 ≤ ((L / 8) ^ K)⁻¹ := by positivity
    linarith
  set A : ℝ := blockWindowConst K * 2 ^ K
  calc pairAmp P * J ≤ pairAmp P * (W + CR * (pairProd P * L) ^ (1 / 4 : ℝ) *
        (1 / Real.sqrt L / Δ + L * Real.exp (-(L ^ 2) / 128))) :=
        mul_le_mul_of_nonneg_left hJW hAmp.le
    _ = pairAmp P * W + CR * (pairProd P ^ (-(1 / 4 : ℝ)) * L ^ (1 / 4 : ℝ)) * (1 / Real.sqrt L / Δ) +
        CR * (pairProd P ^ (-(1 / 4 : ℝ)) * L ^ (1 / 4 : ℝ)) * (L * Real.exp (-(L ^ 2) / 128)) := by
        rw [← hq]; ring
    _ = pairAmp P * W + CR * (L ^ (1 / 4 : ℝ) * (1 / Real.sqrt L)) *
          (pairProd P ^ (-(1 / 4 : ℝ)) / Δ) +
        CR * (pairProd P ^ (-(1 / 4 : ℝ)) * L ^ (1 / 4 : ℝ) * L) * Real.exp (-(L ^ 2) / 128) := by
        ring
    _ ≤ pairAmp P * (2 * L * A / (L * Δ) ^ K) + CR * L ^ (-(1 / 4 : ℝ)) *
          (pairProd P ^ (-(1 / 4 : ℝ)) / Δ) +
        CR * (L ^ (5 / 2 : ℝ) * pairProd P ^ (-(3 / 2 : ℝ))) * dualTailFactor L K := by
        rw [hLq]
        gcongr
    _ = _ := by rw [hpw, div_eq_mul_inv]; ring

/-- The dual envelope of a pair. -/
def dualEnv (CW CK CR L δ : ℝ) (K : ℕ) (h k : ℕ) (P : ℕ × ℕ) : ℝ :=
  2 * L * CW * (if nearRes k h δ P then pairWeight L P else 0) +
    (CK * L + 2 * L * (blockWindowConst K * 2 ^ K)) * farWeight L δ K k h P +
    CR * L ^ (-(1 / 4 : ℝ)) * smallWeight L δ k h P +
    (CK * L ^ 2 + CR * L ^ (5 / 2 : ℝ)) * dualTailFactor L K * pairProd P ^ (-(3 / 2 : ℝ))

/-- **Pointwise bound on a dual term.** -/
theorem norm_dualTerm_le_env {CW CK CR : ℝ} (hCW : 0 ≤ CW) (hCK : 0 ≤ CK) (hCR : 0 ≤ CR) {K : ℕ}
    (hW : ∀ {L : ℝ}, 2 ≤ L → ∀ (P : ℕ × ℕ) (η : ℝ),
      ‖dualOsc L (pairProd P * L) η‖ ≤ 2 * L * (CW * min 1 (L / pairProd P)))
    (hJ : ∀ {L Y ξ : ℝ}, 16 ≤ L → 0 < Y → ξ ≠ 0 →
      ‖dualOsc L Y ξ‖ ≤ CK / Y * (L ^ 3 / (L * |ξ|) ^ K + L ^ 3 * Real.exp (-(L ^ 2) / 32)))
    (hR : ∀ {L Y ξ : ℝ}, 16 ≤ L → 0 < Y → ξ ≠ 0 →
      ‖dualOsc L Y ξ - windowHat L ξ‖ ≤
        CR * Y ^ (1 / 4 : ℝ) * (1 / Real.sqrt L / |ξ| + L * Real.exp (-(L ^ 2) / 128)))
    {L δ : ℝ} (hL : 16 ≤ L) (hδ : 0 < δ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {P : ℕ × ℕ}
    (hP : (P.1 + 1) * k ≠ (P.2 + 1) * h) :
    pairAmp P * ‖dualOsc L (pairProd P * L) (Real.log h - Real.log k + pairFreq P)‖ ≤
      dualEnv CW CK CR L δ K h k P := by
  have hL0 : 0 < L := by linarith
  have hPpos := pairProd_pos P
  set η : ℝ := Real.log h - Real.log k + pairFreq P with hη
  set Δ : ℝ := detuning k h P with hΔ
  have hΔη : Δ = |η| := by rw [hΔ, detuning_swap_eq]
  have hw0 := pairWeight_nonneg hL0.le P
  have hfar0 := farWeight_nonneg hL0.le (δ := δ) K k h P
  have hsm0 := smallWeight_nonneg L δ k h P
  have hq0 : 0 ≤ pairProd P ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hPpos.le _
  have htail0 : 0 ≤ dualTailFactor L K := dualTailFactor_nonneg hL0.le K
  have hA0 : 0 ≤ blockWindowConst K * 2 ^ K := mul_nonneg (blockWindowConst_nonneg K) (by positivity)
  have hnear0 : 0 ≤ 2 * L * CW * (if nearRes k h δ P then pairWeight L P else 0) := by
    apply mul_nonneg (by positivity); split_ifs
    · exact hw0
    · exact le_refl _
  have hL52 := L_sq_le_rpow (by linarith : (1 : ℝ) ≤ L)
  have hP' : (P.2 + 1) * h ≠ (P.1 + 1) * k := fun he => hP he.symm
  unfold dualEnv
  rcases nearRes_or_le hk hh hP' (δ := δ) with hn | hsep
  · have hw := hW (by linarith : (2 : ℝ) ≤ L) P η
    have : pairAmp P * ‖dualOsc L (pairProd P * L) η‖ ≤ 2 * L * CW * pairWeight L P := by
      calc pairAmp P * ‖dualOsc L (pairProd P * L) η‖
          ≤ pairAmp P * (2 * L * (CW * min 1 (L / pairProd P))) :=
            mul_le_mul_of_nonneg_left hw (pairAmp_pos P).le
        _ = 2 * L * CW * pairWeight L P := by rw [pairWeight_eq]; ring
    rw [if_pos hn]
    have h1 : 0 ≤ (CK * L + 2 * L * (blockWindowConst K * 2 ^ K)) * farWeight L δ K k h P := by
      positivity
    have h2 : 0 ≤ CR * L ^ (-(1 / 4 : ℝ)) * smallWeight L δ k h P := by positivity
    have h3 : 0 ≤ (CK * L ^ 2 + CR * L ^ (5 / 2 : ℝ)) * dualTailFactor L K *
        pairProd P ^ (-(3 / 2 : ℝ)) := by positivity
    linarith
  · have hδΔ : δ ≤ Δ := by rw [hΔ]; exact hsep
    have hΔ0 : 0 < Δ := lt_of_lt_of_le hδ hδΔ
    have hη0 : η ≠ 0 := fun h0 => by rw [hΔη, h0, abs_zero] at hΔ0; exact lt_irrefl _ hΔ0
    have hY : 0 < pairProd P * L := mul_pos hPpos hL0
    have hfarP : farWeight L δ K k h P = pairWeight L P * ((L * Δ) ^ K)⁻¹ := by
      unfold farWeight; rw [if_pos ⟨hP', hδΔ⟩]
    have hKfold := hJ hL hY hη0
    rw [← hΔη] at hKfold
    have hK' := pairAmp_mul_dual_le_Kfold P hL0 hKfold
    rcases le_or_gt L (pairProd P) with hbig | hsmall
    · have hbd := dual_large_le hCK hL P hbig hfarP hK'
      have h1 : 0 ≤ 2 * L * (blockWindowConst K * 2 ^ K) * farWeight L δ K k h P := by positivity
      have h2 : 0 ≤ CR * L ^ (-(1 / 4 : ℝ)) * smallWeight L δ k h P := by positivity
      have h3 : 0 ≤ CR * L ^ (5 / 2 : ℝ) * dualTailFactor L K * pairProd P ^ (-(3 / 2 : ℝ)) := by
        positivity
      nlinarith
    · rcases le_or_gt (1 / 8) Δ with hfar8 | hnear8
      · have hbd := dual_small_far_le hCK hL P hfar8 hK'
        have h1 : 0 ≤ (CK * L + 2 * L * (blockWindowConst K * 2 ^ K)) * farWeight L δ K k h P := by
          positivity
        have h2 : 0 ≤ CR * L ^ (-(1 / 4 : ℝ)) * smallWeight L δ k h P := by positivity
        have h3 : 0 ≤ CR * L ^ (5 / 2 : ℝ) * dualTailFactor L K * pairProd P ^ (-(3 / 2 : ℝ)) := by
          positivity
        nlinarith
      · have hRb := hR hL hY hη0
        rw [← hΔη] at hRb
        have hsplit : ‖dualOsc L (pairProd P * L) η‖ ≤ ‖windowHat L η‖ +
            CR * (pairProd P * L) ^ (1 / 4 : ℝ) *
              (1 / Real.sqrt L / Δ + L * Real.exp (-(L ^ 2) / 128)) := by
          have := norm_le_norm_sub_add (dualOsc L (pairProd P * L) η) (windowHat L η)
          linarith
        have hω := norm_windowHat_le_pow K hL0 hη0
        rw [← hΔη] at hω
        have hbd := dual_small_near_le hCR hL P hsmall hsplit hω
        have hsmallP : smallWeight L δ k h P = pairProd P ^ (-(1 / 4 : ℝ)) / Δ := by
          unfold smallWeight; rw [if_pos ⟨hP', hsmall, hδΔ, hnear8⟩]
        rw [← hfarP, ← hsmallP] at hbd
        have h1 : 0 ≤ CK * L * farWeight L δ K k h P := by positivity
        have h3 : 0 ≤ CK * L ^ 2 * dualTailFactor L K * pairProd P ^ (-(3 / 2 : ℝ)) := by
          positivity
        nlinarith

/-- **Dual off-diagonal bound with detuning.** -/
theorem exists_norm_dualOff_le_far (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L δ : ℝ}, 16 ≤ L → 0 < δ → ∀ {h k : ℕ}, 0 < h → 0 < k →
      ‖dualOff L h k‖ ≤ C * (L * nearMass L k h δ + L * ∑' P, farWeight L δ K k h P +
        L ^ (-(1 / 4 : ℝ)) * ∑' P, smallWeight L δ k h P +
        L ^ (5 / 2 : ℝ) * dualTailFactor L K) := by
  obtain ⟨CW, hCW, hW⟩ := exists_norm_dualOsc_pair_le
  obtain ⟨CK, hCK, hJ⟩ := exists_norm_notchDualOscillation_le_pow K
  obtain ⟨CR, hCR, hR⟩ := exists_norm_notchDualOscillation_sub_window_le
  have hR' : ∀ {L Y ξ : ℝ}, 16 ≤ L → 0 < Y → ξ ≠ 0 →
      ‖dualOsc L Y ξ - windowHat L ξ‖ ≤
        CR * Y ^ (1 / 4 : ℝ) * (1 / Real.sqrt L / |ξ| + L * Real.exp (-(L ^ 2) / 128)) := by
    intro L Y ξ hL hY hξ
    have := hR hL hY hξ
    unfold rightAbscissa at this
    exact this
  have hZ : 0 ≤ pairZeta32 := tsum_nonneg fun P => Real.rpow_nonneg (pairProd_pos P).le _
  have hs32 := summable_pairProd_rpow (s := 3 / 2) (by norm_num)
  set A : ℝ := blockWindowConst K * 2 ^ K with hA
  have hA0 : 0 ≤ A := mul_nonneg (blockWindowConst_nonneg K) (by positivity)
  refine ⟨2 * CW + CK + 2 * A + CR + 2 * (CK + CR) * pairZeta32, by positivity,
    fun {L δ} hL hδ {h k} hh hk => ?_⟩
  have hL0 : 0 < L := by linarith
  have hh1 : 1 ≤ h := hh
  have hk1 : 1 ≤ k := hk
  set ξ : ℝ := Real.log h - Real.log k with hξ
  set g : ℕ × ℕ → ℂ := fun P => (pairAmp P : ℂ) * dualOsc L (pairProd P * L) (ξ + pairFreq P)
    with hg
  set S : Set (ℕ × ℕ) := {P : ℕ × ℕ | (P.1 + 1) * k = (P.2 + 1) * h}ᶜ with hS
  have hnear : Summable (fun P : ℕ × ℕ => if nearRes k h δ P then pairWeight L P else 0) := by
    refine Summable.of_nonneg_of_le (fun P => ?_) (fun P => ?_) (summable_pairWeight hL0.le)
    · split_ifs
      · exact pairWeight_nonneg hL0.le P
      · exact le_refl _
    · split_ifs
      · exact le_refl _
      · exact pairWeight_nonneg hL0.le P
  have hfar : Summable (farWeight L δ K k h) := by
    refine Summable.of_nonneg_of_le (farWeight_nonneg hL0.le K k h) (fun P => ?_)
      ((summable_pairWeight hL0.le).mul_right ((L * δ) ^ K)⁻¹)
    unfold farWeight
    split_ifs with hf
    · exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hf.2 hL0.le) K))
        (pairWeight_nonneg hL0.le P)
    · exact mul_nonneg (pairWeight_nonneg hL0.le P) (inv_nonneg.mpr (by positivity))
  have hsm := summable_smallWeight hL0 hδ k h
  have hbs : Summable (dualEnv CW CK CR L δ K h k) := by
    unfold dualEnv
    exact (((hnear.mul_left _).add (hfar.mul_left _)).add (hsm.mul_left _)).add (hs32.mul_left _)
  have hb0 : ∀ P, 0 ≤ dualEnv CW CK CR L δ K h k P := fun P => by
    unfold dualEnv
    have h1 : 0 ≤ 2 * L * CW * (if nearRes k h δ P then pairWeight L P else 0) := by
      apply mul_nonneg (by positivity); split_ifs
      · exact pairWeight_nonneg hL0.le P
      · exact le_refl _
    have h2 := farWeight_nonneg hL0.le (δ := δ) K k h P
    have h3 := smallWeight_nonneg L δ k h P
    have h4 := dualTailFactor_nonneg hL0.le K
    have h5 : 0 ≤ pairProd P ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (pairProd_pos P).le _
    positivity
  have hpt : ∀ P ∈ S, ‖g P‖ ≤ dualEnv CW CK CR L δ K h k P := by
    intro P hP
    have hgn : ‖g P‖ = pairAmp P * ‖dualOsc L (pairProd P * L) (ξ + pairFreq P)‖ := by
      simp only [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pairAmp_pos P)]
    rw [hgn]
    exact norm_dualTerm_le_env hCW hCK hCR hW hJ hR' hL hδ hh hk hP
  have hgs : Summable (fun P : S => ‖g P‖) :=
    (summable_dualFamily (by linarith) ξ).norm.subtype S
  have hL14 : 0 ≤ L ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hL0.le _
  have hL52 := L_sq_le_rpow (by linarith : (1 : ℝ) ≤ L)
  calc ‖dualOff L h k‖ ≤ ∑' P : S, ‖g P‖ := norm_tsum_le_tsum_norm hgs
    _ ≤ ∑' P : S, dualEnv CW CK CR L δ K h k P :=
        hgs.tsum_le_tsum (fun P => hpt P.1 P.2) (hbs.subtype S)
    _ ≤ ∑' P, dualEnv CW CK CR L δ K h k P := Summable.tsum_subtype_le _ S hb0 hbs
    _ = 2 * L * CW * nearMass L k h δ + (CK * L + 2 * L * A) * ∑' P, farWeight L δ K k h P +
          CR * L ^ (-(1 / 4 : ℝ)) * ∑' P, smallWeight L δ k h P +
          (CK * L ^ 2 + CR * L ^ (5 / 2 : ℝ)) * dualTailFactor L K * pairZeta32 := by
        unfold dualEnv
        rw [Summable.tsum_add (((hnear.mul_left _).add (hfar.mul_left _)).add (hsm.mul_left _))
            (hs32.mul_left _),
          Summable.tsum_add ((hnear.mul_left _).add (hfar.mul_left _)) (hsm.mul_left _),
          Summable.tsum_add (hnear.mul_left _) (hfar.mul_left _),
          tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left]
        rfl
    _ ≤ (2 * CW + CK + 2 * A + CR + 2 * (CK + CR) * pairZeta32) *
          (L * nearMass L k h δ + L * ∑' P, farWeight L δ K k h P +
            L ^ (-(1 / 4 : ℝ)) * ∑' P, smallWeight L δ k h P +
            L ^ (5 / 2 : ℝ) * dualTailFactor L K) := by
        have hN := nearMass_nonneg hL0.le k h δ
        have hF : 0 ≤ ∑' P, farWeight L δ K k h P := tsum_nonneg (farWeight_nonneg hL0.le K k h)
        have hSm : 0 ≤ ∑' P, smallWeight L δ k h P := tsum_nonneg (smallWeight_nonneg L δ k h)
        have hT := dualTailFactor_nonneg hL0.le K
        have hL52' : 0 ≤ L ^ (5 / 2 : ℝ) := by positivity
        have e1 : (CK * L ^ 2 + CR * L ^ (5 / 2 : ℝ)) * dualTailFactor L K * pairZeta32 ≤
            (2 * (CK + CR) * pairZeta32) * (L ^ (5 / 2 : ℝ) * dualTailFactor L K) := by
          have : CK * L ^ 2 + CR * L ^ (5 / 2 : ℝ) ≤ 2 * (CK + CR) * L ^ (5 / 2 : ℝ) := by nlinarith
          calc (CK * L ^ 2 + CR * L ^ (5 / 2 : ℝ)) * dualTailFactor L K * pairZeta32
              ≤ (2 * (CK + CR) * L ^ (5 / 2 : ℝ)) * dualTailFactor L K * pairZeta32 := by gcongr
            _ = _ := by ring
        have e2 : 2 * L * CW * nearMass L k h δ ≤ (2 * CW) * (L * nearMass L k h δ) := le_of_eq (by ring)
        have e3 : (CK * L + 2 * L * A) * ∑' P, farWeight L δ K k h P =
            (CK + 2 * A) * (L * ∑' P, farWeight L δ K k h P) := by ring
        have hLN : 0 ≤ L * nearMass L k h δ := by positivity
        have hLF : 0 ≤ L * ∑' P, farWeight L δ K k h P := by positivity
        have hLS : 0 ≤ L ^ (-(1 / 4 : ℝ)) * ∑' P, smallWeight L δ k h P := by positivity
        have hLT : 0 ≤ L ^ (5 / 2 : ℝ) * dualTailFactor L K := by positivity
        nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ CK + 2 * A + CR + 2 * (CK + CR) * pairZeta32) hLN,
          mul_nonneg (by positivity : (0:ℝ) ≤ 2 * CW + CR + 2 * (CK + CR) * pairZeta32) hLF,
          mul_nonneg (by positivity : (0:ℝ) ≤ 2 * CW + CK + 2 * A + 2 * (CK + CR) * pairZeta32) hLS,
          mul_nonneg (by positivity : (0:ℝ) ≤ 2 * CW + CK + 2 * A + CR) hLT]

/-! ## Symmetry under inverting the twist -/

theorem detuning_swap (h k : ℕ) (P : ℕ × ℕ) : detuning k h P.swap = detuning h k P := by
  unfold detuning pairFreq
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [← abs_neg]
  congr 1
  ring

theorem pairProd_swap (P : ℕ × ℕ) : pairProd P.swap = pairProd P := by
  unfold pairProd
  simp only [Prod.fst_swap, Prod.snd_swap]
  ring

theorem farWeight_swap (L δ : ℝ) (K : ℕ) (h k : ℕ) (P : ℕ × ℕ) :
    farWeight L δ K k h P.swap = farWeight L δ K h k P := by
  unfold farWeight
  simp only [Prod.fst_swap, Prod.snd_swap, detuning_swap, pairWeight_swap]
  congr 1
  apply propext
  constructor
  · rintro ⟨hne, hd⟩; exact ⟨fun he => hne he.symm, hd⟩
  · rintro ⟨hne, hd⟩; exact ⟨fun he => hne he.symm, hd⟩

theorem smallWeight_swap (L δ : ℝ) (h k : ℕ) (P : ℕ × ℕ) :
    smallWeight L δ k h P.swap = smallWeight L δ h k P := by
  unfold smallWeight
  simp only [Prod.fst_swap, Prod.snd_swap, detuning_swap, pairProd_swap]
  congr 1
  apply propext
  constructor
  · rintro ⟨hne, hd⟩; exact ⟨fun he => hne he.symm, hd⟩
  · rintro ⟨hne, hd⟩; exact ⟨fun he => hne he.symm, hd⟩

theorem tsum_farWeight_swap (L δ : ℝ) (K : ℕ) (h k : ℕ) :
    ∑' P, farWeight L δ K k h P = ∑' P, farWeight L δ K h k P := by
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq]
  congr 1
  ext P
  exact farWeight_swap L δ K h k P

theorem tsum_smallWeight_swap (L δ : ℝ) (h k : ℕ) :
    ∑' P, smallWeight L δ k h P = ∑' P, smallWeight L δ h k P := by
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq]
  congr 1
  ext P
  exact smallWeight_swap L δ h k P

/-! ## The small-pair mass -/

/-- No small pair is near a high twist: for `h ≥ 2kL` the small-pair weight vanishes. -/
theorem smallWeight_eq_zero_of_le {h k : ℕ} (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L)
    (hhk : 2 * k * L ≤ h) (P : ℕ × ℕ) : smallWeight L δ h k P = 0 := by
  unfold smallWeight
  rw [if_neg]
  rintro ⟨-, hPL, -, hΔ⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hh0 : (0 : ℝ) < h := by nlinarith
  have hM : (1 : ℝ) ≤ (P.1 : ℝ) + 1 := by linarith [(Nat.cast_nonneg P.1 : (0 : ℝ) ≤ P.1)]
  have hN0 : (0 : ℝ) < (P.2 : ℝ) + 1 := by positivity
  have hlog : Real.log (h / k) - 1 / 8 < Real.log (((P.2 : ℝ) + 1) / ((P.1 : ℝ) + 1)) := by
    have := (abs_lt.mp hΔ).1
    unfold detuning pairFreq at this
    rw [Real.log_div hh0.ne' hk0.ne', Real.log_div hN0.ne' (by positivity : ((P.1 : ℝ) + 1) ≠ 0)]
    linarith
  have hratio : (h / k) * Real.exp (-(1 / 8)) < ((P.2 : ℝ) + 1) / ((P.1 : ℝ) + 1) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < h / k), ← Real.exp_add,
      ← Real.exp_log (by positivity : (0 : ℝ) < ((P.2 : ℝ) + 1) / ((P.1 : ℝ) + 1))]
    exact Real.exp_lt_exp.mpr (by linarith)
  have he : (1 / 2 : ℝ) < Real.exp (-(1 / 8)) := by
    have := Real.add_one_le_exp (-(1 / 8 : ℝ))
    linarith
  have hN : (h / k) * (1 / 2) < (P.2 : ℝ) + 1 := by
    have h1 : ((P.2 : ℝ) + 1) / ((P.1 : ℝ) + 1) ≤ (P.2 : ℝ) + 1 :=
      div_le_self hN0.le hM
    have h2 : (h / k) * (1 / 2) < (h / k) * Real.exp (-(1 / 8)) :=
      mul_lt_mul_of_pos_left he (by positivity)
    linarith
  have hLk : L ≤ (h / k) * (1 / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hk0]; linarith
  have hprod : (P.2 : ℝ) + 1 ≤ pairProd P := by
    unfold pairProd; nlinarith
  linarith

/-- The shell count `J(δ)` is at most `log L / log 2` for `δ ≥ 1/L`. -/
theorem shell_count_le_log {δ L : ℝ} (hδ : 0 < δ) (hδL : 1 / L ≤ δ) (hL : 1 < L) :
    (Nat.find (exists_shell_count hδ) : ℝ) ≤ Real.log L / Real.log 2 := by
  classical
  set J := Nat.find (exists_shell_count hδ) with hJ
  rcases Nat.eq_zero_or_pos J with h0 | hpos
  · rw [h0, Nat.cast_zero]
    exact div_nonneg (Real.log_nonneg hL.le) (Real.log_nonneg (by norm_num))
  have hmin : ¬ (1 / 8 ≤ 2 ^ (J - 1) * δ) := Nat.find_min (exists_shell_count hδ) (by omega)
  push Not at hmin
  have hL0 : 0 < L := by linarith
  have h2 : (2 : ℝ) ^ J ≤ L := by
    have e : (2 : ℝ) ^ J = 2 * 2 ^ (J - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : 2 ^ (J - 1) * (1 / L) ≤ 2 ^ (J - 1) * δ := mul_le_mul_of_nonneg_left hδL (by positivity)
    rw [mul_one_div] at this
    have h8 : (2 : ℝ) ^ (J - 1) / L < 1 / 8 := lt_of_le_of_lt this hmin
    rw [div_lt_iff₀ hL0] at h8
    rw [e]; nlinarith
  have hlog := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  exact hlog

/-- **Small-pair mass**: `Σ (MN)^{−1/4}/Δ ≤ 48 k L^{3/4} J(δ)` over the near-line small pairs. -/
theorem tsum_smallWeight_le {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) :
    ∑' P, smallWeight L δ h k P ≤
      48 * k * L ^ (3 / 4 : ℝ) * (Nat.find (exists_shell_count hδ) : ℝ) := by
  classical
  set J := Nat.find (exists_shell_count hδ) with hJdef
  have hJ : 1 / 8 ≤ 2 ^ J * δ := Nat.find_spec (exists_shell_count hδ)
  set f : ℕ → ℕ × ℕ → ℝ := fun j P => if nearRes h k (2 ^ (j + 1) * δ) P then
    L ^ (1 / 4 : ℝ) * pairWeight L P / (2 ^ j * δ) else 0 with hf
  have hf0 : ∀ j P, 0 ≤ f j P := fun j P => by
    simp only [hf]; split_ifs
    · exact div_nonneg (mul_nonneg (by positivity) (pairWeight_nonneg hL.le P)) (by positivity)
    · exact le_refl _
  have hfs : ∀ j ∈ Finset.range J, Summable (f j) := by
    intro j _
    refine Summable.of_nonneg_of_le (hf0 j) (fun P => ?_)
      ((summable_pairWeight hL.le).mul_left (L ^ (1 / 4 : ℝ) / (2 ^ j * δ)))
    simp only [hf]; split_ifs
    · exact le_of_eq (by ring)
    · exact mul_nonneg (by positivity) (pairWeight_nonneg hL.le P)
  have hpt : ∀ P, smallWeight L δ h k P ≤ ∑ j ∈ Finset.range J, f j P := by
    intro P
    unfold smallWeight
    split_ifs with hc
    swap
    · exact Finset.sum_nonneg fun j _ => hf0 j P
    obtain ⟨hne, hPL, hδΔ, hΔ8⟩ := hc
    set Δ := detuning h k P
    obtain ⟨j, hj1, hj2⟩ := exists_shell hδ hδΔ
    have hjJ : j < J := by
      by_contra hc'
      push Not at hc'
      have : (2 : ℝ) ^ J ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hc'
      nlinarith
    have hnear : nearRes h k (2 ^ (j + 1) * δ) P :=
      (nearRes_iff_detuning hh hk _ P).mpr ⟨hne, hj2⟩
    have hPpos := pairProd_pos P
    have hpw : pairWeight L P = pairProd P ^ (-(1 / 2 : ℝ)) := by
      rw [pairWeight_eq, min_eq_left ((one_le_div hPpos).mpr hPL.le), mul_one, pairAmp_eq,
        Real.sqrt_eq_rpow, Real.rpow_neg hPpos.le]
    have hq : pairProd P ^ (-(1 / 4 : ℝ)) ≤ L ^ (1 / 4 : ℝ) * pairWeight L P := by
      rw [hpw]
      have e : pairProd P ^ (-(1 / 4 : ℝ)) = pairProd P ^ (1 / 4 : ℝ) * pairProd P ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hPpos]; norm_num
      rw [e]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hPpos.le hPL.le (by norm_num))
        (Real.rpow_nonneg hPpos.le _)
    have hterm : pairProd P ^ (-(1 / 4 : ℝ)) / Δ ≤ f j P := by
      simp only [hf, if_pos hnear]
      have hΔpos : 0 < 2 ^ j * δ := by positivity
      calc pairProd P ^ (-(1 / 4 : ℝ)) / Δ ≤ pairProd P ^ (-(1 / 4 : ℝ)) / (2 ^ j * δ) :=
            div_le_div_of_nonneg_left (Real.rpow_nonneg hPpos.le _) hΔpos hj1
        _ ≤ L ^ (1 / 4 : ℝ) * pairWeight L P / (2 ^ j * δ) :=
            div_le_div_of_nonneg_right hq hΔpos.le
    exact hterm.trans (Finset.single_le_sum (fun i _ => hf0 i P) (Finset.mem_range.mpr hjJ))
  have hmaj : Summable fun P => ∑ j ∈ Finset.range J, f j P := summable_sum hfs
  have hshell : ∀ j ∈ Finset.range J, ∑' P, f j P ≤ 48 * k * L ^ (3 / 4 : ℝ) := by
    intro j hj
    have hjJ : j < J := Finset.mem_range.mp hj
    have hjs : ¬ (1 / 8 ≤ 2 ^ j * δ) := Nat.find_min (exists_shell_count hδ) hjJ
    push Not at hjs
    have hj4 : 2 ^ (j + 1) * δ ≤ 1 / 4 := by rw [pow_succ]; linarith
    have e : (fun P => f j P) = fun P => (if nearRes h k (2 ^ (j + 1) * δ) P then
        pairWeight L P else 0) * (L ^ (1 / 4 : ℝ) / (2 ^ j * δ)) := by
      funext P
      simp only [hf]
      split_ifs <;> ring
    rw [e, tsum_mul_right]
    have hm := tsum_nearRes_le hh hk (by positivity : 0 < 2 ^ (j + 1) * δ) hj4 hL
    have hpos : 0 < 2 ^ j * δ := by positivity
    calc (∑' P, if nearRes h k (2 ^ (j + 1) * δ) P then pairWeight L P else 0) *
          (L ^ (1 / 4 : ℝ) / (2 ^ j * δ))
        ≤ 24 * (2 ^ (j + 1) * δ) * k * Real.sqrt L * (L ^ (1 / 4 : ℝ) / (2 ^ j * δ)) :=
          mul_le_mul_of_nonneg_right hm (by positivity)
      _ = 48 * k * (Real.sqrt L * L ^ (1 / 4 : ℝ)) := by
          field_simp
          ring
      _ = 48 * k * L ^ (3 / 4 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL]; norm_num
  calc ∑' P, smallWeight L δ h k P ≤ ∑' P, ∑ j ∈ Finset.range J, f j P :=
        (summable_smallWeight hL hδ h k).tsum_le_tsum hpt hmaj
    _ = ∑ j ∈ Finset.range J, ∑' P, f j P := Summable.tsum_finsetSum hfs
    _ ≤ ∑ _j ∈ Finset.range J, 48 * k * L ^ (3 / 4 : ℝ) := Finset.sum_le_sum hshell
    _ = 48 * k * L ^ (3 / 4 : ℝ) * J := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end RHTower.ZetaNotch
