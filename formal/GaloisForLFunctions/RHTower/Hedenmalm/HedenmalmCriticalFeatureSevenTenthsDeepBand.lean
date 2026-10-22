import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureCanonicalHeightWindow
import GaloisForLFunctions.RHTower.Sieve.InghamDetectorDensity

/-!
# Seven-tenths deep-band discharge for the HCF route

Route T's unconditional Ingham detector bounds the analytic-multiplicity zeta-zero count in the
deep band `Re s ≥ 7/10` by a fixed power `X ^ α` with `α < 7/10`.  The canonical HCF normalizer is
the actual Riemann zero count and dominates the linear cardinality of its lattice window.  This file
welds those two already-proved facts: the deep-band zero count is `o(N(X))`.

No zero-dependent scalarization and no numerical input enter the statement or proof.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Zeros in the fixed deep off-line band `Re s ≥ 7/10` have density zero relative to the
canonical Riemann zero count. -/
theorem tendsto_zetaLittlewoodZeroCountAbove_sevenTenths_div_canonicalZeroCount :
    Tendsto
      (fun X : ℕ =>
        Sieve.zetaLittlewoodZeroCountAbove Sieve.inghamFixedGabrielSigma 4
            (X : ℝ) (7 / 10) /
          criticalFeatureCanonicalZeroCount X)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hdeep⟩ :=
    Sieve.exists_eventually_zetaLittlewoodZeroCountAbove_sevenTenths_le_routeTExponent
  have hdeepShift : ∀ᶠ X : ℕ in atTop,
      Sieve.zetaLittlewoodZeroCountAbove Sieve.inghamFixedGabrielSigma 4
          (X : ℝ) (7 / 10) ≤
        K * ((X + 2 : ℕ) : ℝ) ^ Sieve.inghamFixedGabrielRouteTExponent := by
    rw [eventually_atTop] at hdeep ⊢
    obtain ⟨X₀, hX₀⟩ := hdeep
    refine ⟨X₀, fun X hX => ?_⟩
    have h := hX₀ (X + 2) (by omega)
    norm_num [Nat.cast_add] at h ⊢
    exact h
  have hexponent : Sieve.inghamFixedGabrielRouteTExponent ≤ (1 : ℝ) :=
    (Sieve.inghamFixedGabrielRouteTExponent_lt_seven_tenths.trans (by norm_num)).le
  have hmajor : Tendsto
      (fun X : ℕ => K *
        (((criticalFeatureCanonicalLatticeWindow X).card : ℝ) /
          criticalFeatureCanonicalZeroCount X))
      atTop (𝓝 0) := by
    simpa using
      tendsto_const_nhds.mul
        tendsto_card_criticalFeatureCanonicalLatticeWindow_div_zeroCount
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with X hN
    have hcount : 0 ≤ Sieve.zetaLittlewoodZeroCountAbove
        Sieve.inghamFixedGabrielSigma 4 (X : ℝ) (7 / 10) := by
      rw [Sieve.zetaLittlewoodZeroCountAbove]
      apply Finset.sum_nonneg
      intro w hw
      exact Nat.cast_nonneg _
    exact div_nonneg hcount hN.le
  · filter_upwards [hdeepShift,
      eventually_criticalFeatureCanonicalZeroCount_pos] with X hdeepX hN
    have hbase : (1 : ℝ) ≤ ((X + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ X + 2)
    have hpow :
        ((X + 2 : ℕ) : ℝ) ^ Sieve.inghamFixedGabrielRouteTExponent ≤
          ((X + 2 : ℕ) : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hbase hexponent
    have hXcard :
        ((X + 2 : ℕ) : ℝ) ≤
          ((criticalFeatureCanonicalLatticeWindow X).card : ℝ) := by
      rw [card_criticalFeatureCanonicalLatticeWindow]
      push_cast
      linarith
    calc
      Sieve.zetaLittlewoodZeroCountAbove Sieve.inghamFixedGabrielSigma 4
            (X : ℝ) (7 / 10) /
          criticalFeatureCanonicalZeroCount X
          ≤ (K * ((X + 2 : ℕ) : ℝ) ^ Sieve.inghamFixedGabrielRouteTExponent) /
              criticalFeatureCanonicalZeroCount X :=
        div_le_div_of_nonneg_right hdeepX hN.le
      _ ≤ (K * ((X + 2 : ℕ) : ℝ)) / criticalFeatureCanonicalZeroCount X :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK) hN.le
      _ ≤ (K * ((criticalFeatureCanonicalLatticeWindow X).card : ℝ)) /
              criticalFeatureCanonicalZeroCount X :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hXcard hK) hN.le
      _ = K * (((criticalFeatureCanonicalLatticeWindow X).card : ℝ) /
              criticalFeatureCanonicalZeroCount X) := by ring

end

end RHTower
