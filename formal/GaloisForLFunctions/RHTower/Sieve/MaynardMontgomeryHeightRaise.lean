import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedRaise

/-!
# Raising a selected Maynard group through the height

The robust degree-`60` grouping window is `[1/90,19/270]` in height exponents.  Raising a
selected group by the first natural power which reaches `T` therefore uses at most `90` copies
and overshoots only to `T^(289/270)`.  Unlike the Huxley schedule, this height-crossing schedule
has no amplitude-dependent square-scale gate; it is the natural input to Montgomery's mean value
theorem.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- First height crossing in the robust selected-group exponent window. -/
theorem exists_maynard_montgomery_raise_multiplier {beta : ℝ}
    (hbeta_lo : 1 / 90 ≤ beta) (hbeta_hi : beta ≤ 19 / 270) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 90 ∧
      1 ≤ (ell : ℝ) * beta ∧ (ell : ℝ) * beta ≤ 289 / 270 := by
  have hbeta : 0 < beta := lt_of_lt_of_le (by norm_num) hbeta_lo
  let ell : ℕ := ⌈(1 : ℝ) / beta⌉₊
  have harg0 : 0 ≤ (1 : ℝ) / beta := by positivity
  have hello : (1 : ℝ) / beta ≤ (ell : ℝ) := Nat.le_ceil _
  have helhi : (ell : ℝ) ≤ (1 : ℝ) / beta + 1 :=
    (Nat.ceil_lt_add_one harg0).le
  have hel90 : ell ≤ 90 := by
    rw [Nat.ceil_le, div_le_iff₀ hbeta]
    norm_num at hbeta_lo ⊢
    linarith
  have hcross := mul_le_mul_of_nonneg_right hello hbeta.le
  have hover := mul_le_mul_of_nonneg_right helhi hbeta.le
  have hcross' : 1 ≤ (ell : ℝ) * beta := by
    rw [div_mul_cancel₀ _ hbeta.ne'] at hcross
    simpa [mul_comm] using hcross
  have helpos : 0 < ell := by
    have helposR : (0 : ℝ) < (ell : ℝ) := by
      nlinarith
    exact_mod_cast helposR
  refine ⟨ell, helpos, hel90, ?_, ?_⟩
  · exact hcross'
  · have hcancel : (1 : ℝ) / beta * beta = 1 := div_mul_cancel₀ _ hbeta.ne'
    rw [add_mul, hcancel, one_mul] at hover
    linarith

/-- The first height crossing for an actual selected lower edge. -/
theorem exists_maynard_montgomery_raised_length {T A beta : ℝ}
    (hT : 1 ≤ T) (hA : A = T ^ beta)
    (hbeta_lo : 1 / 90 ≤ beta) (hbeta_hi : beta ≤ 19 / 270) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 90 ∧
      T ≤ A ^ ell ∧ A ^ ell ≤ T ^ (289 / 270 : ℝ) := by
  obtain ⟨ell, hell, hell90, hcross, hover⟩ :=
    exists_maynard_montgomery_raise_multiplier hbeta_lo hbeta_hi
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hpow : A ^ ell = T ^ ((ell : ℝ) * beta) := by
    rw [hA, ← Real.rpow_natCast, ← Real.rpow_mul hT0]
    congr 1
    ring
  refine ⟨ell, hell, hell90, ?_, ?_⟩
  · calc
      T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ T ^ ((ell : ℝ) * beta) :=
        Real.rpow_le_rpow_of_exponent_le hT hcross
      _ = A ^ ell := hpow.symm
  · rw [hpow]
    exact Real.rpow_le_rpow_of_exponent_le hT hover

/-- **Uniform Montgomery raising on one nonempty selection fibre.**  One power crosses the
height and preserves the exact selected-product threshold at every ordinate in the fibre. -/
theorem exists_maynardEligibleSelection_montgomery_raise
    (L X k : ℕ) {T0 t e mu : ℝ}
    (hT0 : 1 < T0) (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120)
    (label : HeathBrownSelectionLabel L X k)
    (S : Finset ℕ) (hSne : S.Nonempty) (s : ℕ → ℂ)
    (hselection : ∀ r ∈ S,
      IsHeathBrownEligibleSelection L X k
        (T0 := T0) (t := t) (e := e) (s r) label) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 90 ∧
      T0 ≤ ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) ∧
      (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ≤
        T0 ^ (289 / 270 : ℝ) ∧
      ∀ r ∈ S,
        (((groupedDyadicLower (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^ e) ≤
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
    exists_maynard_montgomery_raised_length hT0.le hAeq hbeta_lo hbeta_hi
  refine ⟨ell, hell, hell90, ?_, ?_, ?_⟩
  · exact_mod_cast (by simpa [A, Nat.cast_pow] using hYlo)
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
        (((groupedDyadicLower (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^ e) =
          (A ^ e) ^ ell := by
      calc
        (((groupedDyadicLower (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^ e) =
            A ^ ((ell : ℝ) * e) := by
              rw [Nat.cast_pow, ← Real.rpow_natCast,
                ← Real.rpow_mul (by positivity : 0 ≤ A)]
        _ = A ^ (e * (ell : ℝ)) := by ring_nf
        _ = (A ^ e) ^ (ell : ℝ) := by
          rw [Real.rpow_mul (by positivity : 0 ≤ A)]
        _ = (A ^ e) ^ ell := Real.rpow_natCast _ _
    calc
      (((groupedDyadicLower (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^ e) =
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
