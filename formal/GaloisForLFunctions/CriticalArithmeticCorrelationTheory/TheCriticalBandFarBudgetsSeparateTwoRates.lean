import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheEighthRootComplementKeepsItsBlockReserves

/-!
# Separate the two rates in the critical band–far cross

The eighth-power monomial has only a logarithmic bound at critical overlap.
It enters through the adjunction budget, accompanied by the conductor exponent.
All other norm costs retain a negative power of `log N`. Keeping these rates
separate permits an almost-polynomial conductor cutoff.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics CriticalScaleArithmeticRigidity

/-- The norm budget separates the critical eighth-power rate `σ` from the
strictly decaying rate `τ`. Only `σ / b` occurs, so `b` may grow logarithmically. -/
theorem budgetU_two_rates_le {L c θ D b Cpr Cnp Cup CupT Hc Kρ Λ σ τ Sg lR lc ρ NM Rr Nr : ℝ}
    (hL1 : 1 ≤ L) (hc1 : 1 ≤ c) (hcL : c ≤ L) (hθ : 0 < θ) (hD : 0 < D) (hb : 0 < b)
    (hCpr : 0 ≤ Cpr) (hCnp : 0 ≤ Cnp) (hCup : 0 ≤ Cup) (hCupT : 0 ≤ CupT) (hHc : 0 ≤ Hc)
    (hKρ : 0 ≤ Kρ) (hlc1 : 1 ≤ lc) (hSg1 : 1 ≤ Sg) (hΛ1 : 1 ≤ Λ)
    (hlR0 : 0 ≤ lR) (hlR : lR ≤ 2 * θ * L) (hR1 : 1 ≤ Rr) (hRN : L ^ 18 * Rr ^ 16 ≤ Nr)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Kρ * (c ^ 2 * lc ^ 3 * Λ / L)) (hNM : NM ≤ 2 * Hc * c)
    (hm1 : c ^ 8 * lc * Sg ^ 2 / L ≤ σ) (hm2 : c ^ 11 * lc ^ 3 * Sg * Λ / L ^ 2 ≤ τ)
    (hLσ : 1 / L ≤ σ) (hLτ : 1 / L ≤ τ) (h7τ : c ^ 7 * lc / L ≤ τ)
    (hσU : (1024 * D * Cpr + 1024 * D * Cpr / b +
      64 * D * Cnp * (4 * θ ^ 2 * Kρ + 880) / (b * θ) + 256 * D * Cup / θ +
      512 * D * CupT * Hc / (b * θ)) * τ + 1024 * D * Cnp / b * σ ≤ 1 / 4) :
    256 * Cpr * lR / (L * (θ * L / (2 * D))) +
        256 * c ^ 7 * Cpr * lR / (L * b * (θ * L / (2 * D))) +
        32 * c ^ 7 * Cnp * (((lR / L) ^ 2 * ρ + c ^ 2 * (24 + 780 * Sg + 72 * Rr ^ 15 / Nr) / L +
            c ^ 4 * lc / L + c ^ 3 * Rr ^ 2 * (L / Nr)) +
          2 * (lR * lc / L + c * (Sg ^ 2 * lc / L + c ^ 5 / Nr + c ^ 3 * Rr ^ 4 / (Nr * L)) * lR) +
          2 * (c ^ 2 * Rr ^ 5 / (Nr ^ 2 * L))) / (b * (θ * L / (2 * D))) +
        128 * Cup * c ^ 2 * lc / (θ * L / (2 * D)) +
        128 * c ^ 7 * CupT * c ^ 2 * NM * lc / (L * b * (θ * L / (2 * D))) ≤ 1 / 4 := by
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < c := by linarith
  have hτ0 : 0 ≤ τ := le_trans (by positivity) hLτ
  have hN0 : 0 < Nr := lt_of_lt_of_le (by positivity) hRN
  have hlRL : lR / L ≤ 2 * θ := by rw [div_le_iff₀ hL0]; linarith
  have h7 := h7τ
  have hc7 : c ^ 7 / L ≤ τ :=
    le_trans (div_le_div_of_nonneg_right (le_mul_of_one_le_right (by positivity) hlc1) hL0.le) h7
  have hU1 : 256 * Cpr * lR / (L * (θ * L / (2 * D))) ≤ 1024 * D * Cpr * τ := by
    have e : 256 * Cpr * lR / (L * (θ * L / (2 * D))) = 512 * D * Cpr / θ * (lR / L) * (1 / L) := by
      field_simp; ring
    rw [e]
    calc 512 * D * Cpr / θ * (lR / L) * (1 / L) ≤ 512 * D * Cpr / θ * (2 * θ) * τ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlRL (by positivity)) hLτ (by positivity)
            (by positivity)
      _ = 1024 * D * Cpr * τ := by field_simp; ring
  have hU2 : 256 * c ^ 7 * Cpr * lR / (L * b * (θ * L / (2 * D))) ≤ 1024 * D * Cpr / b * τ := by
    have e : 256 * c ^ 7 * Cpr * lR / (L * b * (θ * L / (2 * D))) =
        512 * D * Cpr / (b * θ) * (lR / L) * (c ^ 7 / L) := by
      field_simp; ring
    rw [e]
    calc 512 * D * Cpr / (b * θ) * (lR / L) * (c ^ 7 / L) ≤ 512 * D * Cpr / (b * θ) * (2 * θ) * τ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlRL (by positivity)) hc7 (by positivity)
            (by positivity)
      _ = 1024 * D * Cpr / b * τ := by field_simp; ring
  have hβA : c ^ 7 * (c ^ 2 * Rr ^ 5 / (Nr ^ 2 * L)) / L ≤ τ := by
    have e : c ^ 7 * (c ^ 2 * Rr ^ 5 / (Nr ^ 2 * L)) / L =
        (c ^ 9 * Rr ^ 5 / Nr) * (1 / (Nr * L ^ 2)) := by
      field_simp
    rw [e]
    have h1 := cpow_Rpow_div_le hL1 hc0.le hcL hR1 hRN hLτ (i := 9) (j := 5) (by norm_num)
      (by norm_num)
    have hN1 : 1 ≤ Nr := le_trans (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1)
      (one_le_pow₀ hR1)) hRN
    have h2 : 1 / (Nr * L ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_mul_of_one_le_of_one_le hN1 (one_le_pow₀ hL1)
    calc (c ^ 9 * Rr ^ 5 / Nr) * (1 / (Nr * L ^ 2)) ≤ τ * 1 :=
          mul_le_mul h1 h2 (by positivity) hτ0
      _ = τ := mul_one τ
  have hβU := budgetUpart_le hL1 hc1 hcL hKρ hlc1 hSg1 hΛ1 hlR0 hlR hR1 hRN hρ0 hρ hm2 hLτ
  have hβG := budgetG_le hθ hL1 hc1 hcL hlc1 hSg1 hlR hR1 hRN hm1 hLσ
  have hU3 : 32 * c ^ 7 * Cnp * (((lR / L) ^ 2 * ρ + c ^ 2 * (24 + 780 * Sg + 72 * Rr ^ 15 / Nr) / L +
            c ^ 4 * lc / L + c ^ 3 * Rr ^ 2 * (L / Nr)) +
          2 * (lR * lc / L + c * (Sg ^ 2 * lc / L + c ^ 5 / Nr + c ^ 3 * Rr ^ 4 / (Nr * L)) * lR) +
          2 * (c ^ 2 * Rr ^ 5 / (Nr ^ 2 * L))) / (b * (θ * L / (2 * D))) ≤
      64 * D * Cnp * (4 * θ ^ 2 * Kρ + 880) / (b * θ) * τ +
        1024 * D * Cnp / b * σ := by
    generalize hBU : (lR / L) ^ 2 * ρ + c ^ 2 * (24 + 780 * Sg + 72 * Rr ^ 15 / Nr) / L +
      c ^ 4 * lc / L + c ^ 3 * Rr ^ 2 * (L / Nr) = BU at hβU ⊢
    generalize hBG : lR * lc / L + c * (Sg ^ 2 * lc / L + c ^ 5 / Nr + c ^ 3 * Rr ^ 4 / (Nr * L)) *
      lR = BG at hβG ⊢
    generalize hBA : c ^ 2 * Rr ^ 5 / (Nr ^ 2 * L) = BA at hβA ⊢
    have e : 32 * c ^ 7 * Cnp * (BU + 2 * BG + 2 * BA) / (b * (θ * L / (2 * D))) =
        64 * D * Cnp / (b * θ) * (c ^ 7 * BU / L + 2 * (c ^ 7 * BG / L) + 2 * (c ^ 7 * BA / L)) := by
      field_simp; ring
    rw [e]
    have hsum : c ^ 7 * BU / L + 2 * (c ^ 7 * BG / L) + 2 * (c ^ 7 * BA / L) ≤
        (4 * θ ^ 2 * Kρ + 880) * τ + 16 * θ * σ := by
      have : (4 * θ ^ 2 * Kρ + 880) * τ + 16 * θ * σ =
          (4 * θ ^ 2 * Kρ + 878) * τ + 2 * (8 * θ * σ) + 2 * τ := by ring
      linarith only [hβU, hβG, hβA, this]
    calc 64 * D * Cnp / (b * θ) * (c ^ 7 * BU / L + 2 * (c ^ 7 * BG / L) + 2 * (c ^ 7 * BA / L)) ≤
        64 * D * Cnp / (b * θ) * ((4 * θ ^ 2 * Kρ + 880) * τ + 16 * θ * σ) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 64 * D * Cnp * (4 * θ ^ 2 * Kρ + 880) / (b * θ) * τ +
        1024 * D * Cnp / b * σ := by field_simp; ring
  have hU4 : 128 * Cup * c ^ 2 * lc / (θ * L / (2 * D)) ≤ 256 * D * Cup / θ * τ := by
    have e : 128 * Cup * c ^ 2 * lc / (θ * L / (2 * D)) = 256 * D * Cup / θ * (c ^ 2 * lc / L) := by
      field_simp; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left (le_trans (div_le_div_of_nonneg_right ?_ hL0.le) h7)
      (by positivity)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 (by norm_num)) (by linarith)
  have hU5 : 128 * c ^ 7 * CupT * c ^ 2 * NM * lc / (L * b * (θ * L / (2 * D))) ≤
      512 * D * CupT * Hc / (b * θ) * τ := by
    have e : 128 * c ^ 7 * CupT * c ^ 2 * NM * lc / (L * b * (θ * L / (2 * D))) =
        256 * D * CupT / (b * θ) * (NM * (c ^ 9 * lc / L ^ 2)) := by
      field_simp; ring
    rw [e]
    have h10 : c ^ 10 * lc / L ^ 2 ≤ τ := by
      refine le_trans (div_le_div_of_nonneg_right ?_ (by positivity)) hm2
      have h2 : 1 ≤ lc ^ 2 * Sg * Λ :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hlc1) hSg1) hΛ1
      calc c ^ 10 * lc ≤ c ^ 11 * lc :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 (by norm_num)) (by linarith)
        _ = c ^ 11 * lc * 1 := (mul_one _).symm
        _ ≤ c ^ 11 * lc * (lc ^ 2 * Sg * Λ) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = c ^ 11 * lc ^ 3 * Sg * Λ := by ring
    have h1 : NM * (c ^ 9 * lc / L ^ 2) ≤ 2 * Hc * τ :=
      calc NM * (c ^ 9 * lc / L ^ 2) ≤ (2 * Hc * c) * (c ^ 9 * lc / L ^ 2) :=
            mul_le_mul_of_nonneg_right hNM (by positivity)
        _ = 2 * Hc * (c ^ 10 * lc / L ^ 2) := by ring
        _ ≤ 2 * Hc * τ := mul_le_mul_of_nonneg_left h10 (by positivity)
    calc 256 * D * CupT / (b * θ) * (NM * (c ^ 9 * lc / L ^ 2)) ≤
        256 * D * CupT / (b * θ) * (2 * Hc * τ) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 512 * D * CupT * Hc / (b * θ) * τ := by ring
  have hexp : (1024 * D * Cpr + 1024 * D * Cpr / b +
      64 * D * Cnp * (4 * θ ^ 2 * Kρ + 880) / (b * θ) + 256 * D * Cup / θ +
      512 * D * CupT * Hc / (b * θ)) * τ = 1024 * D * Cpr * τ + 1024 * D * Cpr / b * τ +
      64 * D * Cnp * (4 * θ ^ 2 * Kρ + 880) / (b * θ) * τ + 256 * D * Cup / θ * τ +
      512 * D * CupT * Hc / (b * θ) * τ := by ring
  linarith only [hU1, hU2, hU3, hU4, hU5, hexp, hσU]

/-- At critical overlap, the eighth-power monomial grows at most cubically in
`log L`; the other monomials still decay like `L^(-1/16)`. -/
theorem eventually_critical_band_far_monomials {A : ℝ} (hA : 1 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ c Sg : ℝ, 1 ≤ c → c ≤ L ^ (1 / 8 : ℝ) →
      1 ≤ Sg → Sg ≤ A * (1 + Real.log L) →
      c ^ 8 * (1 + Real.log c) * Sg ^ 2 / L ≤ A ^ 2 * (1 + Real.log L) ^ 3 ∧
      c ^ 11 * (1 + Real.log c) ^ 3 * Sg * L ^ (1 / 16 : ℝ) / L ^ 2 ≤
        L ^ (-(1 / 16 : ℝ)) ∧
      1 / L ≤ L ^ (-(1 / 16 : ℝ)) ∧
      c ^ 7 * (1 + Real.log c) / L ≤ L ^ (-(1 / 16 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    RHTower.eventually_const_mul_polylog_le_rpow 1
      (by norm_num : (0 : ℝ) < 1 / 16) A] with L hL1 hpoly
  intro c Sg hc1 hc hSg1 hSg
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have ht1 : 1 ≤ 1 + Real.log L := by linarith only [Real.log_nonneg hL1]
  have hlc0 : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc1]
  have hcL : c ≤ L := hc.trans ((Real.rpow_le_rpow_of_exponent_le hL1
    (by norm_num : (1 / 8 : ℝ) ≤ 1)).trans_eq (Real.rpow_one L))
  have hlct : 1 + Real.log c ≤ 1 + Real.log L := by
    linarith only [Real.log_le_log hc0 hcL]
  have htA : 1 + Real.log L ≤ A * (1 + Real.log L) :=
    le_mul_of_one_le_left (by linarith only [ht1]) hA
  simp only [pow_one] at hpoly
  have hVc := hlct.trans (htA.trans hpoly)
  have hSgν := hSg.trans hpoly
  have hc8 : c ^ 8 ≤ L := by
    have h := pow_le_pow_left₀ hc0.le hc 8
    rwa [← Real.rpow_natCast (L ^ (1 / 8 : ℝ)), ← Real.rpow_mul hL0.le,
      show (1 / 8 : ℝ) * (8 : ℕ) = 1 by norm_num, Real.rpow_one] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hL0).mpr
    have h := mul_le_mul (mul_le_mul hc8 hlct hlc0 hL0.le)
      (pow_le_pow_left₀ (zero_le_one.trans hSg1) hSg 2) (sq_nonneg _) (by positivity)
    exact h.trans_eq (by ring)
  · have h₁ := monomial_le_rpow hL1 hc0.le hc hlc0 hVc 11 3 (25 / 16) (by norm_num)
    have h₂ : c ^ 11 * (1 + Real.log c) ^ 3 * Sg * L ^ (1 / 16 : ℝ) ≤
        L ^ (25 / 16 : ℝ) * L ^ (1 / 16 : ℝ) * L ^ (1 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul h₁ hSgν (zero_le_one.trans hSg1) (by positivity)) (by positivity)
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0] at h₂
    calc
      _ ≤ L ^ ((25 / 16 : ℝ) + 1 / 16 + 1 / 16) / L ^ (2 : ℝ) := by
        rw [Real.rpow_two]
        exact div_le_div_of_nonneg_right h₂ (sq_nonneg _)
      _ ≤ _ := rpow_div_rpow_le hL1 (by norm_num)
  · rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  · have h := monomial_le_rpow hL1 hc0.le hc hlc0 hVc 7 1 (15 / 16) (by norm_num)
    simp only [pow_one] at h
    calc
      _ ≤ L ^ (15 / 16 : ℝ) / L ^ (1 : ℝ) := by
        rw [Real.rpow_one]
        exact div_le_div_of_nonneg_right h hL0.le
      _ ≤ _ := rpow_div_rpow_le hL1 (by norm_num)

/-- The almost-polynomial cutoff pays both scalar cross budgets. The collar
parameter grows as the reciprocal conductor exponent, keeping `b θ` fixed. -/
theorem eventually_critical_cross_payment_constants
    {D B A Cpr Cnp Cup CupT CB Hc Kρ : ℝ}
    (hD : 0 < D) (hB : 0 < B) (hA : 1 ≤ A)
    (hCpr : 0 ≤ Cpr) (hCnp : 0 ≤ Cnp) (hCup : 0 ≤ Cup)
    (hCupT : 0 ≤ CupT) (hCB : 0 ≤ CB) (hHc : 0 ≤ Hc) (hKρ : 0 ≤ Kρ) :
    ∀ᶠ L : ℝ in atTop,
      let θ := 1 / (1 + Real.log L) ^ 5
      let b := B * (1 + Real.log L) ^ 5
      let σ := A ^ 2 * (1 + Real.log L) ^ 3
      let τ := L ^ (-(1 / 16 : ℝ))
      1024 * D * Cpr * θ ≤ 1 / 64 ∧
      (512 * D * Cpr * CB / b + 512 * D * Cnp / b) * σ ≤ 1 / 64 ∧
      (1024 * D * Cpr + 1024 * D * Cpr / b +
        64 * D * Cnp * (4 * θ ^ 2 * Kρ + 880) / (b * θ) +
        256 * D * Cup / θ + 512 * D * CupT * Hc / (b * θ)) * τ +
          1024 * D * Cnp / b * σ ≤ 1 / 4 := by
  let Y := 1024 * D * Cpr + 1024 * D * Cpr / B +
    64 * D * Cnp * (4 * Kρ + 880) / B + 512 * D * CupT * Hc / B
  let X := Y + 256 * D * Cup
  let XE := (512 * D * Cpr * CB + 512 * D * Cnp) * A ^ 2 / B
  let XG := 1024 * D * Cnp * A ^ 2 / B
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hXE : 0 ≤ XE := by dsimp only [XE]; positivity
  have hXG : 0 ≤ XG := by dsimp only [XG]; positivity
  let T := 1 + 65536 * D * Cpr + 64 * XE + 8 * XG
  filter_upwards [eventually_ge_atTop (Real.exp T), eventually_ge_atTop (1 : ℝ),
    RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 1 / 16) (8 * X)] with L hLT hL1 hpoly
  let t := 1 + Real.log L
  let θ := 1 / t ^ 5
  let b := B * t ^ 5
  let σ := A ^ 2 * t ^ 3
  let τ := L ^ (-(1 / 16 : ℝ))
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have ht1 : 1 ≤ t := by dsimp only [t]; linarith only [Real.log_nonneg hL1]
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have ht5 : 1 ≤ t ^ 5 := one_le_pow₀ ht1
  have ht2 : t ≤ t ^ 2 := by
    simpa only [pow_one] using pow_le_pow_right₀ ht1 (by norm_num : 1 ≤ 2)
  have ht15 : t ≤ t ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ ht1 (by norm_num : 1 ≤ 5)
  have hTt : T ≤ t := by
    have h := Real.log_le_log (Real.exp_pos T) hLT
    rw [Real.log_exp] at h
    dsimp only [t]
    linarith only [h]
  have hθ0 : 0 < θ := by dsimp only [θ]; positivity
  have hθ1 : θ ≤ 1 := (div_le_one (by positivity)).mpr ht5
  have hb0 : 0 < b := by dsimp only [b]; positivity
  have hBb : B ≤ b := le_mul_of_one_le_right hB.le ht5
  have hbθ : b * θ = B := by dsimp only [b, θ]; field_simp
  have hτ0 : 0 ≤ τ := Real.rpow_nonneg hL0.le _
  have hcancel : L ^ (1 / 16 : ℝ) * τ = 1 := by
    dsimp only [τ]
    rw [← Real.rpow_add hL0]; norm_num
  have hXτ : X * t ^ 5 * τ ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_right hpoly hτ0
    change 8 * X * t ^ 5 * τ ≤ L ^ (1 / 16 : ℝ) * τ at h
    rw [hcancel] at h
    linarith only [h]
  have hEt : 64 * XE ≤ t ^ 2 := by
    dsimp only [T] at hTt
    linarith only [hTt, ht2, hXG, mul_nonneg hD.le hCpr]
  have hGt : 8 * XG ≤ t ^ 2 := by
    dsimp only [T] at hTt
    linarith only [hTt, ht2, hXE, mul_nonneg hD.le hCpr]
  have hpr : 65536 * D * Cpr ≤ t ^ 5 := by
    dsimp only [T] at hTt
    linarith only [hTt, ht15, hXE, hXG]
  have hEid : (512 * D * Cpr * CB / b + 512 * D * Cnp / b) * σ = XE / t ^ 2 := by
    dsimp only [b, σ, XE]
    field_simp
  have hGid : 1024 * D * Cnp / b * σ = XG / t ^ 2 := by
    dsimp only [b, σ, XG]
    field_simp
  have hcoef : 1024 * D * Cpr + 1024 * D * Cpr / b +
      64 * D * Cnp * (4 * θ ^ 2 * Kρ + 880) / (b * θ) +
      256 * D * Cup / θ + 512 * D * CupT * Hc / (b * θ) ≤ X * t ^ 5 := by
    have hθsq : θ ^ 2 ≤ 1 := pow_le_one₀ hθ0.le hθ1
    have h₁ := div_le_div_of_nonneg_left
      (show 0 ≤ 1024 * D * Cpr by positivity) hB hBb
    have h₂ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (show 4 * θ ^ 2 * Kρ + 880 ≤ 4 * Kρ + 880 by
          nlinarith only [mul_le_mul_of_nonneg_right hθsq hKρ])
        (show 0 ≤ 64 * D * Cnp by positivity)) hB.le
    have h₃ : 256 * D * Cup / θ = 256 * D * Cup * t ^ 5 := by
      dsimp only [θ]; field_simp
    have h₄ : Y ≤ Y * t ^ 5 := le_mul_of_one_le_right hY ht5
    rw [hbθ, h₃]
    dsimp only [X, Y] at h₄ ⊢
    nlinarith only [h₁, h₂, h₄]
  change 1024 * D * Cpr * θ ≤ 1 / 64 ∧
    (512 * D * Cpr * CB / b + 512 * D * Cnp / b) * σ ≤ 1 / 64 ∧ _
  refine ⟨?_, ?_, ?_⟩
  · change 1024 * D * Cpr * (1 / t ^ 5) ≤ 1 / 64
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith only [hpr]
  · rw [hEid, div_le_iff₀ (by positivity)]
    linarith only [hEt]
  · have hG : 1024 * D * Cnp / b * σ ≤ 1 / 8 := by
      rw [hGid, div_le_iff₀ (by positivity)]
      linarith only [hGt]
    have h := (mul_le_mul_of_nonneg_right hcoef hτ0).trans hXτ
    exact (add_le_add h hG).trans (by norm_num)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
