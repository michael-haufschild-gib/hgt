import GaloisForLFunctions.RHTower.Sieve.MaynardUniformAbsorption

/-!
# Uniform grouped-factor coefficient energy

The divisor constants used for grouped Heath--Brown factors depend only on the chosen power loss,
not on cutoffs, dyadic boxes, or factor kinds.  This file puts the quantifiers in the form required
by uniform color-fibre counting: one pair of constants controls every literal selected group.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- One divisor constant controls grouped coefficient energy for every factor family and box. -/
theorem exists_uniform_sum_normSq_groupedDyadicCoeffVector_le
    {ι : Type*} [Fintype ι] {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ) (L : ℝ),
        0 ≤ L →
        (∀ i n, ‖arithmeticDyadicBlock (F i) (q i) n‖ ≤ L) →
        ∑ j : Fin (groupedDyadicUpper q), ‖groupedDyadicCoeffVector F q j‖ ^ 2
          ≤ (groupedDyadicUpper q : ℝ) *
            ((C * (groupedDyadicUpper q : ℝ) ^ eta * L) ^ Fintype.card ι) ^ 2 := by
  obtain ⟨C, hC, hdiv⟩ := RHTower.card_divisors_le_const_mul_rpow heta
  refine ⟨C, hC, ?_⟩
  intro F q L hL hfactor
  let M := groupedDyadicUpper q
  have hM1 : 1 ≤ M := by
    dsimp [M]
    exact one_le_groupedDyadicUpper q
  have hterm : ∀ j : Fin M,
      ‖groupedDyadicCoeffVector F q j‖ ^ 2
        ≤ ((C * (M : ℝ) ^ eta * L) ^ Fintype.card ι) ^ 2 := by
    intro j
    have hnpos : 0 < (j : ℕ) + 1 := by omega
    have hd := hdiv ((j : ℕ) + 1) hnpos
    have hjcast : ((((j : ℕ) + 1 : ℕ) : ℝ)) ≤ (M : ℝ) := by
      exact_mod_cast j.isLt
    have hmono : ((((j : ℕ) + 1 : ℕ) : ℝ) ^ eta) ≤ (M : ℝ) ^ eta :=
      Real.rpow_le_rpow (by positivity) hjcast heta.le
    have hdM : (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ))
        ≤ C * (M : ℝ) ^ eta :=
      hd.trans (mul_le_mul_of_nonneg_left hmono hC.le)
    have hbase : (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ)) * L
        ≤ (C * (M : ℝ) ^ eta) * L :=
      mul_le_mul_of_nonneg_right hdM hL
    have hnorm := norm_groupedDyadicProduct_le_divisors_mul_pow F q hL hfactor
      ((j : ℕ) + 1)
    have hnorm' : ‖groupedDyadicCoeffVector F q j‖
        ≤ (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ) * L) ^ Fintype.card ι := by
      simpa [groupedDyadicCoeffVector, complexCoeff_apply] using hnorm
    have hvec : ‖groupedDyadicCoeffVector F q j‖
        ≤ (C * (M : ℝ) ^ eta * L) ^ Fintype.card ι := by
      refine hnorm'.trans ?_
      simpa [mul_assoc] using
        pow_le_pow_left₀ (by positivity) hbase (Fintype.card ι)
    exact pow_le_pow_left₀ (norm_nonneg _) hvec 2
  calc
    ∑ j : Fin (groupedDyadicUpper q), ‖groupedDyadicCoeffVector F q j‖ ^ 2
        ≤ ∑ _j : Fin M,
            ((C * (M : ℝ) ^ eta * L) ^ Fintype.card ι) ^ 2 :=
          Finset.sum_le_sum fun j _ => hterm j
    _ = (M : ℝ) * ((C * (M : ℝ) ^ eta * L) ^ Fintype.card ι) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (groupedDyadicUpper q : ℝ) *
          ((C * (groupedDyadicUpper q : ℝ) ^ eta * L) ^ Fintype.card ι) ^ 2 := rfl

/-- Uniform base energy for all literal Heath--Brown factor kinds and dyadic boxes. -/
theorem exists_uniform_sum_normSq_heathBrownGroupedCoeffVector_le
    {ι : Type*} [Fintype ι] {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ),
        ∑ j : Fin (groupedDyadicUpper q),
            ‖groupedDyadicCoeffVector
              (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2
          ≤ (groupedDyadicUpper q : ℝ) *
            ((C * (groupedDyadicUpper q : ℝ) ^ eta *
              (1 + Real.log (groupedDyadicUpper q : ℝ))) ^ Fintype.card ι) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_sum_normSq_groupedDyadicCoeffVector_le (ι := ι) heta
  refine ⟨C, hC, ?_⟩
  intro L X kind q
  apply hbound
  · have hM1 := one_le_groupedDyadicUpper q
    have hlog : 0 ≤ Real.log (groupedDyadicUpper q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hM1)
    linarith
  · exact norm_heathBrownGroupedFactorBlock_le L X kind q

/-- **Uniform raised energy package.**  Constants are independent of cutoffs, factor kinds,
dyadic exponents, and selected labels. -/
theorem exists_uniform_sum_normSq_convPow_heathBrownGrouped_le
    {ι : Type*} [Fintype ι] (ell : ℕ) (hell : 0 < ell)
    {eta xi : ℝ} (heta : 0 < eta) (hxi : 0 < xi) :
    ∃ Cbase Craise : ℝ, 0 < Cbase ∧ 0 < Craise ∧
      ∀ (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ),
        ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
          ‖convPow (groupedDyadicUpper q) ell
            (groupedDyadicCoeffVector
              (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2
        ≤ Craise * (((groupedDyadicUpper q) ^ ell : ℕ) : ℝ) ^ xi *
          (((groupedDyadicUpper q : ℝ) *
            ((Cbase * (groupedDyadicUpper q : ℝ) ^ eta *
              (1 + Real.log (groupedDyadicUpper q : ℝ))) ^ Fintype.card ι) ^ 2) ^ ell) := by
  obtain ⟨Cbase, hCbase, hbase⟩ :=
    exists_uniform_sum_normSq_heathBrownGroupedCoeffVector_le (ι := ι) heta
  obtain ⟨Craise, hCraise, hraise⟩ :=
    exists_sum_normSq_convPow_le_rpow ell hell hxi
  refine ⟨Cbase, Craise, hCbase, hCraise, ?_⟩
  intro L X kind q
  have hraw := hraise (groupedDyadicUpper q) (one_le_groupedDyadicUpper q)
    (groupedDyadicCoeffVector (fun i => heathBrownFactorBase L X (kind i)) q)
  have hbase' := hbase L X kind q
  have hsum0 : 0 ≤ ∑ j : Fin (groupedDyadicUpper q),
      ‖groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hpow := pow_le_pow_left₀ hsum0 hbase' ell
  exact hraw.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

end RHTower.Sieve
