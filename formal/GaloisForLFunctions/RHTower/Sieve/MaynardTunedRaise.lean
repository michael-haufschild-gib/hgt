import GaloisForLFunctions.RHTower.Sieve.MaynardMontgomeryHeightRaise

/-!
# Tuned bounded raising of a robust Maynard group

The first-crossing argument works at every target exponent `theta ∈ (0,1]`, not only at the
height exponent `1`.  This lets Route T place a selected factor at the optimizer of the relevant
large-values inequality while retaining a uniform power bound `ell ≤ 90`.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- First crossing of an arbitrary target exponent by a robust group exponent. -/
theorem exists_maynard_tuned_raise_multiplier
    {beta theta : ℝ}
    (hbeta_lo : 1 / 90 ≤ beta) (hbeta_hi : beta ≤ 19 / 270)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 90 ∧
      theta ≤ (ell : ℝ) * beta ∧
        (ell : ℝ) * beta ≤ theta + 19 / 270 := by
  have hbeta : 0 < beta := lt_of_lt_of_le (by norm_num) hbeta_lo
  let ell : ℕ := ⌈theta / beta⌉₊
  have harg0 : 0 ≤ theta / beta := by positivity
  have hello : theta / beta ≤ (ell : ℝ) := Nat.le_ceil _
  have helhi : (ell : ℝ) ≤ theta / beta + 1 :=
    (Nat.ceil_lt_add_one harg0).le
  have hel90 : ell ≤ 90 := by
    rw [Nat.ceil_le, div_le_iff₀ hbeta]
    have htheta90 : theta ≤ 90 * beta := by
      have : (1 : ℝ) ≤ 90 * beta := by nlinarith
      exact hthetaOne.trans this
    simpa using htheta90
  have hcross := mul_le_mul_of_nonneg_right hello hbeta.le
  have hover := mul_le_mul_of_nonneg_right helhi hbeta.le
  have hcross' : theta ≤ (ell : ℝ) * beta := by
    rw [div_mul_cancel₀ _ hbeta.ne'] at hcross
    simpa [mul_comm] using hcross
  have helpos : 0 < ell := by
    have helposR : (0 : ℝ) < (ell : ℝ) := by nlinarith
    exact_mod_cast helposR
  refine ⟨ell, helpos, hel90, hcross', ?_⟩
  have hcancel : theta / beta * beta = theta := div_mul_cancel₀ _ hbeta.ne'
  rw [add_mul, hcancel, one_mul] at hover
  linarith

/-- First crossing of an arbitrary target by a selected sub-height cell.  Unlike the robust-group
version above, the overshoot is retained as the actual cell exponent.  This is the correct lower
Route-T interface: cells may contain one long atom, but their exponent is still below
`1 + mu / 60`. -/
theorem exists_maynard_wide_tuned_raise_multiplier
    {beta theta : ℝ}
    (hbeta_lo : 1 / 90 ≤ beta)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 90 ∧
      theta ≤ (ell : ℝ) * beta ∧
        (ell : ℝ) * beta < theta + beta := by
  have hbeta : 0 < beta := lt_of_lt_of_le (by norm_num) hbeta_lo
  let ell : ℕ := ⌈theta / beta⌉₊
  have harg0 : 0 ≤ theta / beta := by positivity
  have hello : theta / beta ≤ (ell : ℝ) := Nat.le_ceil _
  have helhi : (ell : ℝ) < theta / beta + 1 := Nat.ceil_lt_add_one harg0
  have hel90 : ell ≤ 90 := by
    rw [Nat.ceil_le, div_le_iff₀ hbeta]
    have hone : (1 : ℝ) ≤ 90 * beta := by nlinarith
    exact hthetaOne.trans hone
  have hcross := mul_le_mul_of_nonneg_right hello hbeta.le
  have hover := mul_lt_mul_of_pos_right helhi hbeta
  have hcross' : theta ≤ (ell : ℝ) * beta := by
    rw [div_mul_cancel₀ _ hbeta.ne'] at hcross
    simpa [mul_comm] using hcross
  have hover' : (ell : ℝ) * beta < theta + beta := by
    rw [add_mul, div_mul_cancel₀ _ hbeta.ne', one_mul] at hover
    simpa [mul_comm] using hover
  have helpos : 0 < ell := by
    have helposR : (0 : ℝ) < (ell : ℝ) := by nlinarith
    exact_mod_cast helposR
  exact ⟨ell, helpos, hel90, hcross', hover'⟩

/-- Tuned crossing for an actual lower edge `A=T^beta`. -/
theorem exists_maynard_tuned_raised_length
    {T A beta theta : ℝ} (hT : 1 ≤ T) (hA : A = T ^ beta)
    (hbeta_lo : 1 / 90 ≤ beta) (hbeta_hi : beta ≤ 19 / 270)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 90 ∧
      T ^ theta ≤ A ^ ell ∧ A ^ ell ≤ T ^ (theta + 19 / 270) := by
  obtain ⟨ell, hell, hell90, hcross, hover⟩ :=
    exists_maynard_tuned_raise_multiplier
      hbeta_lo hbeta_hi htheta hthetaOne
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hpow : A ^ ell = T ^ ((ell : ℝ) * beta) := by
    rw [hA, ← Real.rpow_natCast, ← Real.rpow_mul hT0]
    congr 1
    ring
  refine ⟨ell, hell, hell90, ?_, ?_⟩
  · rw [hpow]
    exact Real.rpow_le_rpow_of_exponent_le hT hcross
  · rw [hpow]
    exact Real.rpow_le_rpow_of_exponent_le hT hover

/-- One tuned bounded power works uniformly on every ordinate in a fixed nonempty selection
fibre and preserves its exact amplitude threshold. -/
theorem exists_maynardEligibleSelection_tuned_raise
    (L X k : ℕ) {T0 t e mu theta : ℝ}
    (hT0 : 1 < T0) (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (label : HeathBrownSelectionLabel L X k)
    (S : Finset ℕ) (hSne : S.Nonempty) (s : ℕ → ℂ)
    (hselection : ∀ r ∈ S,
      IsHeathBrownEligibleSelection L X k
        (T0 := T0) (t := t) (e := e) (s r) label) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 90 ∧
      T0 ^ theta ≤
        ((groupedDyadicLower
          (heathBrownSelectedExponent label)) ^ ell : ℕ) ∧
      (((groupedDyadicLower
        (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ≤
          T0 ^ (theta + 19 / 270) ∧
      ∀ r ∈ S,
        (((groupedDyadicLower
          (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^ e) ≤
          ‖(∏ i : HeathBrownSelectedFactor label, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownSelectedKind label i))
              (heathBrownSelectedExponent label i))) (s r)) ^ ell‖ := by
  obtain ⟨r0, hr0⟩ := hSne
  rcases hselection r0 hr0 with
    ⟨_helig, _hune, halower, haupper, _hcard, hAlength, _hlarge⟩
  let beta : ℝ := ∑ i ∈ label.2,
    dyadicLogExponent T0
      (heathBrownBoxFactorExponent label.1.a label.1.b label.1.q i)
  have hbeta_lo' : mu / 120 ≤ beta := by simpa [beta, ht] using halower
  have hbeta_hi' : beta ≤ 4 * mu / 120 := by
    rw [ht] at haupper
    dsimp [beta]
    linarith
  obtain ⟨hbeta_lo, hbeta_hi⟩ :=
    maynard_greedy_grouped_factor_exponent_window
      hmu_lo hmu_hi hbeta_lo' hbeta_hi'
  let A : ℝ := (groupedDyadicLower (heathBrownSelectedExponent label) : ℝ)
  have hAeq : A = T0 ^ beta := by simpa [A, beta] using hAlength
  obtain ⟨ell, hell, hell90, hYlo, hYhi⟩ :=
    exists_maynard_tuned_raised_length hT0.le hAeq
      hbeta_lo hbeta_hi htheta hthetaOne
  refine ⟨ell, hell, hell90, ?_, ?_, ?_⟩
  · simpa [A, Nat.cast_pow] using hYlo
  · simpa [A, Nat.cast_pow] using hYhi
  · intro r hr
    rcases hselection r hr with
      ⟨_helig, _hune, _halower, _hupper, _hcard, _hlength, hlarge⟩
    have hbase : A ^ e ≤
        ‖∏ i : HeathBrownSelectedFactor label, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (heathBrownSelectedKind label i))
            (heathBrownSelectedExponent label i))) (s r)‖ := by
      simpa [A] using hlarge
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (by positivity : 0 ≤ A) _)
      hbase ell
    have hrewrite :
        (((groupedDyadicLower
          (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^ e) =
            (A ^ e) ^ ell := by
      calc
        (((groupedDyadicLower
          (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^ e) =
            A ^ ((ell : ℝ) * e) := by
              rw [Nat.cast_pow, ← Real.rpow_natCast,
                ← Real.rpow_mul (by positivity : 0 ≤ A)]
        _ = A ^ (e * (ell : ℝ)) := by ring_nf
        _ = (A ^ e) ^ (ell : ℝ) := by
          rw [Real.rpow_mul (by positivity : 0 ≤ A)]
        _ = (A ^ e) ^ ell := Real.rpow_natCast _ _
    calc
      (((groupedDyadicLower
        (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^ e) =
          (A ^ e) ^ ell := hrewrite
      _ ≤ ‖∏ i : HeathBrownSelectedFactor label, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownSelectedKind label i))
              (heathBrownSelectedExponent label i))) (s r)‖ ^ ell := hpow
      _ = ‖(∏ i : HeathBrownSelectedFactor label, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownSelectedKind label i))
              (heathBrownSelectedExponent label i))) (s r)) ^ ell‖ := by
        rw [norm_pow]

end RHTower.Sieve
