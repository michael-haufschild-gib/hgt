import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicDyadicReceiver
import GaloisForLFunctions.RHTower.Sieve.GallagherAffineMeanSquare

/-!
# Menon's harmonic shell with a dyadically paid frequency tail

The earlier receiver paid every frequency beyond the analytic head by a pointwise polynomial
bound.  That loses a full factor of shell length.  Here Gallagher's dyadic tail uses the affine
Dirichlet-polynomial mean square instead.  For the localized harmonic Möbius shell, its plain
coefficient energy is at most `3/(A+1)` and its integer-weighted energy is at most `3`; hence a
head estimate at height `W` acquires only an `O(1/((A+1)W) + 1/W²)` tail.

All endpoint and coefficient identities remain literal.  No analytic estimate is assumed beyond
the supplied finite head integral in the receiver theorem.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- A generic dyadic short-interval receiver with a separately estimated frequency head and an
affine mean-square majorant for every higher dyadic band. -/
theorem dyadicMeanSquare_le_dyadicHead (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {ℓ A B M K' : ℕ} {ε W I α β : ℝ}
    (hℓ : 0 < ℓ) (hA : 0 < A) (hAB : A ≤ B + 1) (hε : 0 ≤ ε)
    (hW : 0 < W) (hI0 : 0 ≤ I) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hM : B + 1 + ℓ < M + 1)
    (hcover : (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) ≤ (A : ℝ) * (1 + ε) ^ K')
    (hHead : (∫ w in Set.Icc (-W) W,
      ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2) ≤ I)
    (hAffine : ∀ T : ℝ, W ≤ T →
      (∫ w in Set.Icc (-T) T,
        ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2) ≤ α * T + β) :
    dyadicMeanSquare f ℓ A B
      ≤ ((A : ℝ) * (1 + ε) ^ K')
          * ((K' : ℝ) * blockCostG (ℓ : ℝ) ε
              (2 * Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ 2 * I
                + (4 * α / (Real.pi ^ 2 * W)
                  + 4 * β / (3 * Real.pi ^ 2 * W ^ 2)))) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  set G : ℝ := 2 * Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ 2 * I
      + (4 * α / (Real.pi ^ 2 * W) + 4 * β / (3 * Real.pi ^ 2 * W ^ 2)) with hGdef
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    positivity
  refine dyadicMeanSquare_le_gen f hf hℓ hA hAB hε hG0 hM hcover ?_
  intro Y' hY' E
  have hY'0 : (0 : ℝ) < Y' := lt_of_lt_of_le hA0 hY'
  have hδ0 : 0 < Real.log (1 + (ℓ : ℝ) / Y') := by
    refine Real.log_pos ?_
    have : (0 : ℝ) < (ℓ : ℝ) / Y' := by positivity
    linarith
  let a : ℕ → ℂ := fun n => ((f n : ℝ) : ℂ)
  have hwhole := gallagher_split_integral_dyadic_head a (Finset.Icc 1 M)
    hδ0 hW hHead hAffine
  have hset : (∫ u in E,
        ‖logWindowSum a (Finset.Icc 1 M) (Real.log (1 + (ℓ : ℝ) / Y')) u‖ ^ 2)
      ≤ ∫ u : ℝ,
        ‖logWindowSum a (Finset.Icc 1 M) (Real.log (1 + (ℓ : ℝ) / Y')) u‖ ^ 2 := by
    exact MeasureTheory.setIntegral_le_integral
      (integrable_normSq_logWindowSum a (Finset.Icc 1 M) _)
      (Filter.Eventually.of_forall fun u : ℝ => by positivity)
  refine le_trans hset (le_trans hwhole ?_)
  have hmono : Real.log (1 + (ℓ : ℝ) / Y') ≤ Real.log (1 + (ℓ : ℝ) / (A : ℝ)) := by
    refine Real.log_le_log (by positivity) ?_
    have : (ℓ : ℝ) / Y' ≤ (ℓ : ℝ) / (A : ℝ) := by
      exact div_le_div_of_nonneg_left hℓ0.le hA0 hY'
    linarith
  have hsq : Real.log (1 + (ℓ : ℝ) / Y') ^ 2
      ≤ Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hδ0.le hmono 2
  rw [hGdef]
  nlinarith [hsq]

/-- Localized harmonic Möbius coefficients retain their exact reciprocal envelope. -/
theorem abs_localizedHarmonicMoebiusR_le_inv (A n : ℕ) (hn : 0 < n) :
    |localizedHarmonicMoebiusR A n| ≤ 1 / (n : ℝ) := by
  rw [localizedHarmonicMoebiusR]
  split_ifs with h
  · rw [harmonicMoebiusR, abs_div]
    have hnabs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    rw [hnabs]
    exact div_le_div_of_nonneg_right (abs_moebius_real_le_one n) (by positivity)
  · simp only [abs_zero]
    exact one_div_nonneg.mpr (Nat.cast_nonneg n)

/-- On an integer shell start, Menon's final endpoint is exactly `3(A+1)`. -/
theorem menonFinalRangeTopNat_nat (A : ℕ) :
    menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ) = 3 * (A + 1) := by
  rw [menonFinalRangeTopNat,
    show (3 : ℝ) * ((A + 1 : ℕ) : ℝ) = ((3 * (A + 1) : ℕ) : ℝ) by norm_num]
  exact Nat.floor_natCast _

/-- Plain coefficient energy of the zero-extended harmonic shell. -/
theorem localizedHarmonic_plainEnergy_le (A : ℕ) :
    (∑ m : Fin (menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ)),
      ‖((localizedHarmonicMoebiusR A ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ 2)
      ≤ 3 / ((A + 1 : ℕ) : ℝ) := by
  have hden : (0 : ℝ) < ((A + 1 : ℕ) : ℝ) := by positivity
  have hterm : ∀ m : Fin (menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ)),
      ‖((localizedHarmonicMoebiusR A ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ 2
        ≤ (1 / (((A + 1 : ℕ) : ℝ))) ^ 2 := by
    intro m
    rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases hm : A < (m : ℕ) + 1
    · have habs := abs_localizedHarmonicMoebiusR_le_inv A ((m : ℕ) + 1) (by omega)
      have hAn : ((A + 1 : ℕ) : ℝ) ≤ (((m : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast hm
      have hinv : 1 / ((((m : ℕ) + 1 : ℕ) : ℝ)) ≤ 1 / (((A + 1 : ℕ) : ℝ)) := by
        exact one_div_le_one_div_of_le hden hAn
      exact pow_le_pow_left₀ (abs_nonneg _) (le_trans habs hinv) 2
    · rw [localizedHarmonicMoebiusR, if_neg hm]
      norm_num
      positivity
  calc
    (∑ m : Fin (menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ)),
        ‖((localizedHarmonicMoebiusR A ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ 2)
      ≤ ∑ _m : Fin (menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ)),
          (1 / (((A + 1 : ℕ) : ℝ))) ^ 2 := Finset.sum_le_sum fun m _ => hterm m
    _ = 3 / ((A + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        menonFinalRangeTopNat_nat]
      rw [nsmul_eq_mul]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      rw [show (1 / ((A : ℝ) + 1)) ^ 2 = 1 / (((A : ℝ) + 1) ^ 2) by field_simp]
      field_simp [show (A : ℝ) + 1 ≠ 0 by positivity]

/-- Integer-weighted coefficient energy of the zero-extended harmonic shell. -/
theorem localizedHarmonic_weightedEnergy_le (A : ℕ) :
    (∑ m : Fin (menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ)),
      (((m : ℕ) : ℝ) + 1) *
        ‖((localizedHarmonicMoebiusR A ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ 2)
      ≤ 3 := by
  have hden : (0 : ℝ) < ((A + 1 : ℕ) : ℝ) := by positivity
  have hterm : ∀ m : Fin (menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ)),
      (((m : ℕ) : ℝ) + 1) *
          ‖((localizedHarmonicMoebiusR A ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ 2
        ≤ 1 / (((A + 1 : ℕ) : ℝ)) := by
    intro m
    have hn0 : (0 : ℝ) < (((m : ℕ) + 1 : ℕ) : ℝ) := by positivity
    rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases hm : A < (m : ℕ) + 1
    · have habs := abs_localizedHarmonicMoebiusR_le_inv A ((m : ℕ) + 1) (by omega)
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
      have hmul : (((m : ℕ) : ℝ) + 1) * |localizedHarmonicMoebiusR A ((m : ℕ) + 1)| ^ 2
          ≤ (((m : ℕ) : ℝ) + 1) * (1 / ((((m : ℕ) + 1 : ℕ) : ℝ))) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have heq : (((m : ℕ) : ℝ) + 1) * (1 / ((((m : ℕ) + 1 : ℕ) : ℝ))) ^ 2
          = 1 / ((((m : ℕ) + 1 : ℕ) : ℝ)) := by
        norm_num only [Nat.cast_add, Nat.cast_one]
        field_simp [hn0.ne']
      have hAn : ((A + 1 : ℕ) : ℝ) ≤ (((m : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast hm
      exact le_trans (le_trans hmul (le_of_eq heq))
        (one_div_le_one_div_of_le hden hAn)
    · rw [localizedHarmonicMoebiusR, if_neg hm]
      norm_num
      positivity
  calc
    (∑ m : Fin (menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ)),
        (((m : ℕ) : ℝ) + 1) *
          ‖((localizedHarmonicMoebiusR A ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ 2)
      ≤ ∑ _m : Fin (menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ)),
          1 / (((A + 1 : ℕ) : ℝ)) := Finset.sum_le_sum fun m _ => hterm m
    _ = 3 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        menonFinalRangeTopNat_nat]
      rw [nsmul_eq_mul]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      field_simp [show (A : ℝ) + 1 ≠ 0 by positivity]

/-- Height-linear coefficient in the affine mean square for Menon's harmonic shell. -/
def menonHarmonicAffineRate (A : ℕ) : ℝ :=
  15 * Real.pi / (2 * ((A + 1 : ℕ) : ℝ))

/-- Height-free coefficient in the affine mean square for Menon's harmonic shell. -/
def menonHarmonicAffineConst (A : ℕ) : ℝ :=
  15 * Real.exp 1 / 2 + 15 / (4 * ((A + 1 : ℕ) : ℝ))

/-- Uniform affine mean square for the literal final-range harmonic shell. -/
theorem integral_Icc_normSq_menonFinalRangeShell_le_affine
    (A : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ w in Set.Icc (-T) T,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell ((A + 1 : ℕ) : ℝ)) w‖ ^ 2)
      ≤ menonHarmonicAffineRate A * T + menonHarmonicAffineConst A := by
  let a : ℕ → ℂ := fun n => ((localizedHarmonicMoebiusR A n : ℝ) : ℂ)
  let M : ℕ := menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ)
  have hbase := integral_Icc_normSq_logPoly_le_affine_majorant a M hT
  have hplain : (∑ m : Fin M, ‖a ((m : ℕ) + 1)‖ ^ 2)
      ≤ 3 / ((A + 1 : ℕ) : ℝ) := by
    simpa [a, M] using localizedHarmonic_plainEnergy_le A
  have hweighted : (∑ m : Fin M,
      (((m : ℕ) : ℝ) + 1) * ‖a ((m : ℕ) + 1)‖ ^ 2) ≤ 3 := by
    simpa [a, M] using localizedHarmonic_weightedEnergy_le A
  have hrate := mul_le_mul_of_nonneg_left hplain
    (show 0 ≤ (5 * Real.pi / 2) * T by positivity)
  have hconstWeighted := mul_le_mul_of_nonneg_left hweighted
    (show 0 ≤ 5 * Real.exp 1 / 2 by positivity)
  have hconstPlain := mul_le_mul_of_nonneg_left hplain
    (show 0 ≤ (5 : ℝ) / 4 by positivity)
  rw [show logPoly a (Finset.Icc 1 M) =
      logPoly harmonicMoebiusC (menonFinalRangeShell ((A + 1 : ℕ) : ℝ)) by
    funext w
    exact logPoly_localizedHarmonic_eq_menonFinalRangeShell A w] at hbase
  refine le_trans hbase ?_
  calc
    (5 * Real.pi / 2 * (∑ m : Fin M, ‖a ((m : ℕ) + 1)‖ ^ 2)) * T
          + (5 * Real.exp 1 / 2 *
              (∑ m : Fin M, (((m : ℕ) : ℝ) + 1) * ‖a ((m : ℕ) + 1)‖ ^ 2)
            + 5 / 4 * (∑ m : Fin M, ‖a ((m : ℕ) + 1)‖ ^ 2))
      ≤ (5 * Real.pi / 2 * (3 / ((A + 1 : ℕ) : ℝ))) * T
          + (5 * Real.exp 1 / 2 * 3 + 5 / 4 * (3 / ((A + 1 : ℕ) : ℝ))) := by
        exact add_le_add
          (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hrate)
          (add_le_add hconstWeighted hconstPlain)
    _ = menonHarmonicAffineRate A * T + menonHarmonicAffineConst A := by
      simp only [menonHarmonicAffineRate, menonHarmonicAffineConst]
      ring

/-- Menon's harmonic shell receiver with the analytic head kept intact and every higher frequency
paid by the explicit affine coefficient energies. -/
theorem dyadicMeanSquare_harmonic_le_menonFinalRange_dyadicHead
    {l A B K' : ℕ} {ε W I : ℝ}
    (hl : 0 < l) (hA : 0 < A) (hAB : A ≤ B + 1) (hε : 0 ≤ ε)
    (hW : 0 < W) (hI0 : 0 ≤ I)
    (hM : B + 1 + l < menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ) + 1)
    (hcover : (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) ≤ (A : ℝ) * (1 + ε) ^ K')
    (hHead : (∫ w in Set.Icc (-W) W,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell ((A + 1 : ℕ) : ℝ)) w‖ ^ 2) ≤ I) :
    dyadicMeanSquare harmonicMoebiusR l A B ≤
      ((A : ℝ) * (1 + ε) ^ K') *
        ((K' : ℝ) * blockCostG (l : ℝ) ε
          (2 * Real.log (1 + (l : ℝ) / (A : ℝ)) ^ 2 * I
            + (4 * menonHarmonicAffineRate A / (Real.pi ^ 2 * W)
              + 4 * menonHarmonicAffineConst A /
                (3 * Real.pi ^ 2 * W ^ 2)))) := by
  rw [← dyadicMeanSquare_localizedHarmonic_eq A B l hl]
  refine dyadicMeanSquare_le_dyadicHead (localizedHarmonicMoebiusR A)
    (abs_localizedHarmonicMoebiusR_le_one A) hl hA hAB hε hW hI0
    (by dsimp [menonHarmonicAffineRate]; positivity)
    (by dsimp [menonHarmonicAffineConst]; positivity)
    hM hcover ?_ ?_
  · simpa only [logPoly_localizedHarmonic_eq_menonFinalRangeShell] using hHead
  · intro T hWT
    simpa only [logPoly_localizedHarmonic_eq_menonFinalRangeShell] using
      integral_Icc_normSq_menonFinalRangeShell_le_affine A (le_trans hW.le hWT)

end
end RHTower.Sieve
