import GaloisForLFunctions.RHTower.Sieve.MaynardMontgomeryHeightRaise
import GaloisForLFunctions.RHTower.Sieve.MaynardRaisedMontgomeryFiniteSet
import GaloisForLFunctions.RHTower.Sieve.MaynardMontgomeryFixedPolylogEnergy

/-!
# Literal amplitude fibres through raised Montgomery

An existing eligible selected fibre supplies one common grouped factor.  The height-crossing
schedule raises that factor through `T0`; the finite-set Montgomery theorem then counts the fibre
with exact fixed-polylog coefficient energy.  This is the receiver-tailored alternative to the
Huxley square-scale gate.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

/-- Exact cancellation of the Perron abscissa in a height-dominated Montgomery mean square. -/
theorem montgomery_amplitude_cancellation
    {R Y c alpha C G W B PL : ℝ}
    (hY : 0 < Y) (hG0 : 0 ≤ G)
    (hW0 : 0 ≤ W) (hB0 : 0 ≤ B)
    (hC : C ≤ W * Y * B) (hG : G ≤ W * Y * PL)
    (hraw : R * (Y ^ (alpha - c)) ^ 2 ≤
      C * (Y ^ (-c)) ^ 2 * G) :
    R ≤ W ^ 2 * B * PL * Y ^ (2 - 2 * alpha) := by
  have hY0 : 0 ≤ Y := hY.le
  have hV : 0 < (Y ^ (alpha - c)) ^ 2 := by positivity
  have hpower : Y * Y * (Y ^ (-c)) ^ 2 =
      Y ^ (2 - 2 * alpha) * (Y ^ (alpha - c)) ^ 2 := by
    have hneg : (Y ^ (-c)) ^ 2 = Y ^ (-2 * c) := by
      calc
        (Y ^ (-c)) ^ 2 = (Y ^ (-c)) ^ (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Y ^ ((-c) * 2) := (Real.rpow_mul hY0 _ _).symm
        _ = Y ^ (-2 * c) := by congr 1; ring
    have hamp : (Y ^ (alpha - c)) ^ 2 = Y ^ (2 * (alpha - c)) := by
      calc
        (Y ^ (alpha - c)) ^ 2 = (Y ^ (alpha - c)) ^ (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Y ^ ((alpha - c) * 2) := (Real.rpow_mul hY0 _ _).symm
        _ = Y ^ (2 * (alpha - c)) := by congr 1; ring
    rw [hneg, hamp]
    calc
      Y * Y * Y ^ (-2 * c) = Y ^ (1 : ℝ) * Y ^ (1 : ℝ) * Y ^ (-2 * c) := by
        simp
      _ = Y ^ (2 - 2 * c) := by
        rw [← Real.rpow_add hY, ← Real.rpow_add hY]
        congr 1
        ring
      _ = Y ^ (2 - 2 * alpha) * Y ^ (2 * (alpha - c)) := by
        rw [← Real.rpow_add hY]
        congr 1
        ring
  have hupper : C * (Y ^ (-c)) ^ 2 * G ≤
      (W * Y * B) * (Y ^ (-c)) ^ 2 * (W * Y * PL) := by
    gcongr
  have htarget :
      (W * Y * B) * (Y ^ (-c)) ^ 2 * (W * Y * PL) =
        (W ^ 2 * B * PL * Y ^ (2 - 2 * alpha)) *
          (Y ^ (alpha - c)) ^ 2 := by
    calc
      (W * Y * B) * (Y ^ (-c)) ^ 2 * (W * Y * PL) =
          W ^ 2 * B * PL * (Y * Y * (Y ^ (-c)) ^ 2) := by ring
      _ = (W ^ 2 * B * PL * Y ^ (2 - 2 * alpha)) *
          (Y ^ (alpha - c)) ^ 2 := by rw [hpower]; ring
  apply (mul_le_mul_iff_right₀ hV).mp
  simpa [mul_comm] using hraw.trans (hupper.trans_eq htarget)

/-- **Raw selected-fibre Montgomery inequality at independent Perron abscissa and amplitude.** -/
theorem montgomery_maynardEligibleSelection_fibre_at_amplitude
    (L X : ℕ) {T0 H t e mu c alpha delta : ℝ}
    (hT0 : 1 < T0) (hH : 0 ≤ H) (hc : 0 ≤ c)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (he : e = alpha - c)
    (label : HeathBrownSelectionLabel L X 60)
    (S : Finset ℕ) (hSne : S.Nonempty)
    (lam : ℕ → ℝ) (hdelta : 0 < delta)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ H)
    (hselection : ∀ r ∈ S,
      IsHeathBrownEligibleSelection L X 60
        (T0 := T0) (t := t) (e := e)
        ((c : ℂ) + (lam r : ℝ) * Complex.I) label) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 90 ∧
      T0 ≤ ((groupedDyadicLower
        (heathBrownSelectedExponent label)) ^ ell : ℕ) ∧
      (((groupedDyadicLower
        (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ≤
          T0 ^ (289 / 270 : ℝ) ∧
      (S.card : ℝ) *
          (((((groupedDyadicLower
            (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
              (alpha - c)) ^ 2) ≤
        (H + 4 * (((groupedDyadicUpper
            (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) *
            (1 + Real.log ((groupedDyadicUpper
              (heathBrownSelectedExponent label)) ^ ell))) *
          (1 / delta + 2 * Real.log ((groupedDyadicUpper
            (heathBrownSelectedExponent label)) ^ ell)) *
          ((((((groupedDyadicLower
            (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^ (-c)) ^ 2) *
            heathBrownSelectedRaisedEnergy label ell) := by
  obtain ⟨ell, hell, hell90, hYlo, hYhi, hlarge⟩ :=
    exists_maynardEligibleSelection_montgomery_raise
      L X 60 hT0 hmu_lo hmu_hi ht label S hSne
        (fun r => (c : ℂ) + (lam r : ℝ) * Complex.I) hselection
  obtain ⟨r0, hr0⟩ := hSne
  have hlabel : label.2.Nonempty := (hselection r0 hr0).2.1
  let Y : ℝ := (((groupedDyadicLower
    (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)
  have hlarge' : ∀ r ∈ S,
      Y ^ (alpha - c) ≤
        ‖(∏ i : HeathBrownSelectedFactor label, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (heathBrownSelectedKind label i))
            (heathBrownSelectedExponent label i)))
            ((c : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell‖ := by
    intro r hr
    rw [← he]
    simpa [Y] using hlarge r hr
  have hYpos : 0 < Y := by
    dsimp [Y]
    exact_mod_cast pow_pos (Nat.zero_lt_of_lt
      (one_le_groupedDyadicLower (heathBrownSelectedExponent label))) ell
  have hV : 0 < Y ^ (alpha - c) := by
    exact Real.rpow_pos_of_pos hYpos _
  have hMont := montgomery_heathBrown_selected_raised_large_values_finset
    label ell hell hlabel hc
      (show heathBrownSelectedRaisedEnergy label ell ≤
          heathBrownSelectedRaisedEnergy label ell from le_rfl)
      hdelta hH hV hgap hband hlarge'
  exact ⟨ell, hell, hell90, hYlo, hYhi, by simpa [Y] using hMont⟩

set_option maxHeartbeats 1000000 in
/-- **Rho-free Montgomery amplitude count.**  Once the raised lower edge dominates the height,
the two Montgomery length terms and fixed coefficient energy give exponent `2-2*alpha`; the
Perron abscissa cancels exactly. -/
theorem card_le_of_montgomery_at_amplitude_with_fixed_polylog
    {L X : ℕ} {T0 H c alpha delta : ℝ}
    (hT0 : 1 < T0) (hH : H ≤ 3 * T0)
    (hdelta : 0 < delta)
    (label : HeathBrownSelectionLabel L X 60)
    (S : Finset ℕ) (ell : ℕ) (hell : 0 < ell) (hell90 : ell ≤ 90)
    (hYlo : T0 ≤ ((groupedDyadicLower
      (heathBrownSelectedExponent label)) ^ ell : ℕ))
    (hMontgomery :
      (S.card : ℝ) *
          (((((groupedDyadicLower
            (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
              (alpha - c)) ^ 2) ≤
        (H + 4 * (((groupedDyadicUpper
            (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) *
            (1 + Real.log ((groupedDyadicUpper
              (heathBrownSelectedExponent label)) ^ ell))) *
          (1 / delta + 2 * Real.log ((groupedDyadicUpper
            (heathBrownSelectedExponent label)) ^ ell)) *
          ((((((groupedDyadicLower
            (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^ (-c)) ^ 2) *
            heathBrownSelectedRaisedEnergy label ell)) :
    (S.card : ℝ) ≤
      maynardMontgomeryRaisedWidthConstant ^ 2 *
        (7 + 4 * Real.log
          (maynardMontgomeryRaisedWidthConstant *
            ((((groupedDyadicLower
              (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) *
        (1 / delta + 2 * Real.log
          (maynardMontgomeryRaisedWidthConstant *
            ((((groupedDyadicLower
              (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) *
        (1 + Real.log
          (maynardMontgomeryRaisedWidthConstant *
            ((((groupedDyadicLower
              (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ^
          (2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
            (2 ^ (2 * ((Fintype.card
              (HeathBrownSelectedFactor label) + 1) * ell)) - 1)) *
        ((((groupedDyadicLower
          (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
            (2 - 2 * alpha)) := by
  let A : ℕ := groupedDyadicLower (heathBrownSelectedExponent label)
  let M : ℕ := groupedDyadicUpper (heathBrownSelectedExponent label)
  let Y : ℝ := ((A ^ ell : ℕ) : ℝ)
  let Z : ℝ := ((M ^ ell : ℕ) : ℝ)
  let W : ℝ := maynardMontgomeryRaisedWidthConstant
  let Q : ℕ := 2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
    (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1)
  let PL : ℝ := (1 + Real.log (W * Y)) ^ Q
  let B : ℝ := (7 + 4 * Real.log (W * Y)) *
    (1 / delta + 2 * Real.log (W * Y))
  let C : ℝ := (H + 4 * Z * (1 + Real.log Z)) *
    (1 / delta + 2 * Real.log Z)
  let G : ℝ := heathBrownSelectedRaisedEnergy label ell
  have hYlo' : T0 ≤ Y := by simpa [Y, A] using hYlo
  have hY1 : 1 ≤ Y := hT0.le.trans hYlo'
  have hYpos : 0 < Y := zero_lt_one.trans_le hY1
  have hW1 : 1 ≤ W := by
    simpa [W] using maynardMontgomeryRaisedWidthConstant_one_le
  have hW0 : 0 ≤ W := zero_le_one.trans hW1
  have hWY1 : 1 ≤ W * Y := one_le_mul_of_one_le_of_one_le hW1 hY1
  have hWYpos : 0 < W * Y := zero_lt_one.trans_le hWY1
  have hZwidth : Z ≤ W * Y := by
    simpa [Z, M, W, Y, A] using
      heathBrownSelected_raisedUpper_le_montgomeryWidth label hell90
  have hZ1 : 1 ≤ Z := by
    dsimp [Z, M]
    exact_mod_cast Nat.one_le_pow ell
      (groupedDyadicUpper (heathBrownSelectedExponent label))
      (one_le_groupedDyadicUpper _)
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hlogZ0 : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  have hlogWY0 : 0 ≤ Real.log (W * Y) := Real.log_nonneg hWY1
  have hlog : Real.log Z ≤ Real.log (W * Y) :=
    Real.log_le_log hZpos hZwidth
  have hHwidth : H ≤ 3 * (W * Y) := by
    calc
      H ≤ 3 * T0 := hH
      _ ≤ 3 * Y := mul_le_mul_of_nonneg_left hYlo' (by norm_num)
      _ ≤ 3 * (W * Y) := by
        gcongr
        exact (le_mul_iff_one_le_left hYpos).2 hW1
  have hfirst : H + 4 * Z * (1 + Real.log Z) ≤
      W * Y * (7 + 4 * Real.log (W * Y)) := by
    have hlogOne : 1 + Real.log Z ≤ 1 + Real.log (W * Y) := by linarith
    have hterm : 4 * Z * (1 + Real.log Z) ≤
        4 * (W * Y) * (1 + Real.log (W * Y)) := by
      have hprod : Z * (1 + Real.log Z) ≤
          (W * Y) * (1 + Real.log (W * Y)) :=
        mul_le_mul hZwidth hlogOne (by linarith) hWYpos.le
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 4 by norm_num))
    calc
      H + 4 * Z * (1 + Real.log Z) ≤
          3 * (W * Y) + 4 * (W * Y) * (1 + Real.log (W * Y)) :=
        add_le_add hHwidth hterm
      _ = W * Y * (7 + 4 * Real.log (W * Y)) := by ring
  have hsecond : 1 / delta + 2 * Real.log Z ≤
      1 / delta + 2 * Real.log (W * Y) := by linarith
  have hsecond0 : 0 ≤ 1 / delta + 2 * Real.log Z := by
    exact add_nonneg (one_div_nonneg.mpr hdelta.le)
      (mul_nonneg (by norm_num) hlogZ0)
  have hBfirst0 : 0 ≤ 7 + 4 * Real.log (W * Y) := by linarith
  have hBsecond0 : 0 ≤ 1 / delta + 2 * Real.log (W * Y) := by
    exact add_nonneg (one_div_nonneg.mpr hdelta.le)
      (mul_nonneg (by norm_num) hlogWY0)
  have hB0 : 0 ≤ B := by
    exact mul_nonneg hBfirst0 hBsecond0
  have hC : C ≤ W * Y * B := by
    dsimp [C, B]
    calc
      (H + 4 * Z * (1 + Real.log Z)) *
          (1 / delta + 2 * Real.log Z) ≤
        (W * Y * (7 + 4 * Real.log (W * Y))) *
          (1 / delta + 2 * Real.log (W * Y)) :=
        mul_le_mul hfirst hsecond hsecond0
          (mul_nonneg (mul_nonneg hW0 hYpos.le) hBfirst0)
      _ = W * Y * ((7 + 4 * Real.log (W * Y)) *
          (1 / delta + 2 * Real.log (W * Y))) := by ring
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact heathBrownSelectedRaisedEnergy_nonneg label ell
  have hG : G ≤ W * Y * PL := by
    simpa only [G, W, Y, A, PL, Q] using
      heathBrownSelectedRaisedEnergy_le_lower_montgomery_fixed_polylog
        label ell hell hell90
  have hraw : (S.card : ℝ) * (Y ^ (alpha - c)) ^ 2 ≤
      C * (Y ^ (-c)) ^ 2 * G := by
    simpa [C, G, Y, Z, A, M, mul_assoc] using hMontgomery
  simpa only [W, B, PL, Q, Y, A, mul_assoc] using
    (montgomery_amplitude_cancellation hYpos hG0 hW0 hB0
      hC hG hraw)

end RHTower.Sieve
