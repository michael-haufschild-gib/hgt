import GaloisForLFunctions.RHTower.Sieve.MaynardEligibleGreedySelection
import GaloisForLFunctions.RHTower.Sieve.MaynardAllShortHuxley

/-!
# Raising one uniform eligible-selection fibre

Once finite coloring fixes a Heath--Brown box and factor group, every ordinate in that color fibre
has the same grouped lower edge.  The robust grouping window chooses one common power
`1 <= ell <= 51`; the raised lower edge lies in the Huxley range and the selected pointwise lower
bound raises uniformly over the entire fibre.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Factor type selected by one finite aggregate label. -/
abbrev HeathBrownSelectedFactor {L X k : ℕ}
    (label : HeathBrownSelectionLabel L X k) :=
  {i : HeathBrownBoxFactorIndex k label.1.m // i ∈ label.2}

/-- Factor kinds on the selected subtype. -/
abbrev heathBrownSelectedKind {L X k : ℕ}
    (label : HeathBrownSelectionLabel L X k) :
    HeathBrownSelectedFactor label → HeathBrownFactorKind :=
  fun i => heathBrownBoxFactorKind k label.1.m i

/-- Dyadic exponents on the selected subtype. -/
abbrev heathBrownSelectedExponent {L X k : ℕ}
    (label : HeathBrownSelectionLabel L X k) :
    HeathBrownSelectedFactor label → ℕ :=
  fun i => heathBrownBoxFactorExponent label.1.a label.1.b label.1.q i

/-- **Uniform raising on a nonempty color fibre.**  One exponent works at every ordinate carrying
the same selection label. -/
theorem exists_maynardEligibleSelection_raise
    (L X k : ℕ) {T0 t e mu sigma : ℝ}
    (hT0 : 1 < T0) (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (he : e = 1 - sigma)
    (label : HeathBrownSelectionLabel L X k)
    (S : Finset ℕ) (hSne : S.Nonempty) (s : ℕ → ℂ)
    (hselection : ∀ r ∈ S,
      IsHeathBrownEligibleSelection L X k
        (T0 := T0) (t := t) (e := e) (s r) label) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 51 ∧
      T0 ^ (9 / 16 : ℝ) ≤
        ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) ∧
      (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ≤
        T0 ^ (1367 / 2160 : ℝ) ∧
      ∀ r ∈ S,
        (((groupedDyadicLower (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^
            (1 - sigma)) ≤
          ‖(∏ i : HeathBrownSelectedFactor label, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownSelectedKind label i))
              (heathBrownSelectedExponent label i))) (s r)) ^ ell‖ := by
  obtain ⟨r0, hr0⟩ := hSne
  have hsel0 := hselection r0 hr0
  rcases hsel0 with ⟨_helig, _hune, halower, haupper, _hcard, hAlength, _hlarge⟩
  let alpha : ℝ := ∑ i ∈ label.2,
    dyadicLogExponent T0
      (heathBrownBoxFactorExponent label.1.a label.1.b label.1.q i)
  have halower' : mu / 120 ≤ alpha := by simpa [alpha, ht] using halower
  have haupper' : alpha ≤ 4 * mu / 120 := by
    rw [ht] at haupper
    dsimp [alpha]
    linarith
  obtain ⟨halpha_lo, halpha_hi⟩ :=
    maynard_greedy_grouped_factor_exponent_window hmu_lo hmu_hi halower' haupper'
  let A : ℝ := (groupedDyadicLower (heathBrownSelectedExponent label) : ℝ)
  have hAeq : A = T0 ^ alpha := by
    simpa [A, alpha] using hAlength
  obtain ⟨ell, hell51, hYlo, hYhi⟩ :=
    exists_maynard_greedy_raised_length hT0.le hAeq halpha_lo halpha_hi
  have hell : 0 < ell := by
    by_contra hn
    have hell0 : ell = 0 := Nat.eq_zero_of_not_pos hn
    subst ell
    norm_num at hYlo
    have hgt : (1 : ℝ) < T0 ^ (9 / 16 : ℝ) :=
      Real.one_lt_rpow hT0 (by norm_num)
    linarith
  refine ⟨ell, hell, hell51, ?_, ?_, ?_⟩
  · simpa [A, Nat.cast_pow] using hYlo
  · simpa [A, Nat.cast_pow] using hYhi
  · intro r hr
    have hsel := hselection r hr
    rcases hsel with ⟨_helig, _hune, _halower, _hupper, _hcard, _hlength, hlarge⟩
    rw [he] at hlarge
    have hbase : A ^ (1 - sigma) ≤
        ‖∏ i : HeathBrownSelectedFactor label, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (heathBrownSelectedKind label i))
            (heathBrownSelectedExponent label i))) (s r)‖ := by
      simpa [A] using hlarge
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (by positivity : 0 ≤ A) _)
      hbase ell
    have hrewrite :
        (((groupedDyadicLower (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^
            (1 - sigma)) = (A ^ (1 - sigma)) ^ ell := by
      calc
        (((groupedDyadicLower (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^
            (1 - sigma)) = A ^ ((ell : ℝ) * (1 - sigma)) := by
          rw [Nat.cast_pow, ← Real.rpow_natCast,
            ← Real.rpow_mul (by positivity : 0 ≤ A)]
        _ = A ^ ((1 - sigma) * (ell : ℝ)) := by ring_nf
        _ = (A ^ (1 - sigma)) ^ (ell : ℝ) := by
          rw [Real.rpow_mul (by positivity : 0 ≤ A)]
        _ = (A ^ (1 - sigma)) ^ ell := Real.rpow_natCast _ _
    calc
      (((groupedDyadicLower (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^
          (1 - sigma)) = (A ^ (1 - sigma)) ^ ell := hrewrite
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
