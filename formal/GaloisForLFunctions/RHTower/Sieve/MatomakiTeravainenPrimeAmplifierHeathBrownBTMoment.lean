import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownEnergyMoment

/-!
# Brun--Titchmarsh envelope for the powered-prime Heath--Brown moment

The exact support cardinality in the energy-faithful moment is replaced by two unconditional
bounds: Brun--Titchmarsh for `ell! * R`, and the literal block-length bound `R ≤ B`.  The resulting
coefficient contains no unknown support statistic and is ready for source-schedule absorption.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Explicit one-piece coefficient after Brun--Titchmarsh and block-length substitution. -/
def mtTypeIPrimeRaisedHeathBrownBTPieceCoefficient
    (P ell B N' K : ℕ) (T eta z : ℝ) : ℝ :=
  let Q := 2 * (P : ℝ) / Real.log z + 6 * z * (1 + Real.log z) ^ 3 + 1 + ell
  heathBrownLemma34Coefficient eta *
    (heathBrownSquareDivisorScale N' eta) ^ 2 *
    ((ell.factorial : ℝ) * Q ^ ell / (B : ℝ) ^ 2 +
      (((K : ℝ) * T) ^ eta) *
        ((ell.factorial : ℝ) ^ 2 * T / ((B : ℝ) ^ 2 * (K : ℝ)) +
          (ell.factorial : ℝ) ^ 2 * (B : ℝ) ^ (3 / 4 : ℝ) *
            T ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ))))

/-- Exact energy coefficient is bounded by the support-free Brun--Titchmarsh coefficient. -/
theorem mtTypeIPrimeRaisedHeathBrownEnergyPieceCoefficient_le_bt
    (P ell : ℕ) {B N' K : ℕ} (hB : 1 ≤ B) (hK : 1 ≤ K)
    (T : Set.Ioi (0 : ℝ)) {eta z : ℝ} (heta : 0 < eta) (hz : 1 < z) :
    mtTypeIPrimeRaisedHeathBrownEnergyPieceCoefficient
        P ell B N' K (T : ℝ) eta ≤
      mtTypeIPrimeRaisedHeathBrownBTPieceCoefficient
        P ell B N' K (T : ℝ) eta z := by
  let R : ℝ := ((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ)
  let Q : ℝ := 2 * (P : ℝ) / Real.log z + 6 * z * (1 + Real.log z) ^ 3 + 1 + ell
  let F : ℝ := ell.factorial
  have hR0 : 0 ≤ R := by positivity
  have hF0 : 0 ≤ F := by positivity
  have hFR : F * R ≤ Q ^ ell := by
    have h := factorial_mul_card_mtTypeIPrimeRaisedBlockSupportPNat_le_bt
      P ell B hz
    simpa only [F, R, Q, Nat.cast_mul, Nat.cast_factorial,
      Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add] using h
  have hRB : R ≤ (B : ℝ) := by
    dsimp only [R]
    exact_mod_cast card_mtTypeIPrimeRaisedBlockSupportPNat_le_length P ell B
  have hfirst : F ^ 2 * (R / (B : ℝ) ^ 2) ≤
      F * Q ^ ell / (B : ℝ) ^ 2 := by
    calc
      F ^ 2 * (R / (B : ℝ) ^ 2) =
          F * (F * R) / (B : ℝ) ^ 2 := by ring
      _ ≤ F * Q ^ ell / (B : ℝ) ^ 2 := by gcongr
  have hRpow : R ^ (3 / 4 : ℝ) ≤ (B : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hR0 hRB (by norm_num)
  have hmixed : F ^ 2 *
        (R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
          ((B : ℝ) ^ 2 * (K : ℝ))) ≤
      F ^ 2 * (B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
        ((B : ℝ) ^ 2 * (K : ℝ)) := by
    have hden : 0 ≤ (B : ℝ) ^ 2 * (K : ℝ) := by positivity
    have hTpow : 0 ≤ (T : ℝ) ^ (3 / 4 : ℝ) :=
      Real.rpow_nonneg T.property.le _
    have hnum : F ^ 2 * R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) ≤
        F ^ 2 * (B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) := by
      gcongr
    calc
      F ^ 2 * (R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
          ((B : ℝ) ^ 2 * (K : ℝ))) =
          (F ^ 2 * R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ)) /
            ((B : ℝ) ^ 2 * (K : ℝ)) := by ring
      _ ≤ (F ^ 2 * (B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ)) /
            ((B : ℝ) ^ 2 * (K : ℝ)) := by gcongr
  have hpowKT : 0 ≤ ((K : ℝ) * (T : ℝ)) ^ eta :=
    Real.rpow_nonneg (mul_nonneg (by positivity) T.property.le) _
  have hC : 0 ≤ heathBrownLemma34Coefficient eta := by
    have hdiv : 0 < divisorBoundConst (eta / 4) :=
      divisorBoundConst_pos (by linarith)
    rw [heathBrownLemma34Coefficient, heathBrownLemma34PositiveCoefficient,
      heathBrownTheoremFourCoefficient, heathBrownTheoremFourUniversalCoefficient,
      heathBrownMeanSquareCoefficient]
    positivity
  rw [mtTypeIPrimeRaisedHeathBrownEnergyPieceCoefficient,
    mtTypeIPrimeRaisedHeathBrownBTPieceCoefficient]
  change F ^ 2 * heathBrownLemma34Coefficient eta *
      (heathBrownSquareDivisorScale N' eta) ^ 2 *
        (R / (B : ℝ) ^ 2 + ((K : ℝ) * (T : ℝ)) ^ eta *
          ((T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) +
            R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
              ((B : ℝ) ^ 2 * (K : ℝ)))) ≤
    heathBrownLemma34Coefficient eta *
      (heathBrownSquareDivisorScale N' eta) ^ 2 *
        (F * Q ^ ell / (B : ℝ) ^ 2 + ((K : ℝ) * (T : ℝ)) ^ eta *
          (F ^ 2 * (T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) +
            F ^ 2 * (B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
              ((B : ℝ) ^ 2 * (K : ℝ))))
  calc
    _ = heathBrownLemma34Coefficient eta *
        (heathBrownSquareDivisorScale N' eta) ^ 2 *
          (F ^ 2 * (R / (B : ℝ) ^ 2) + ((K : ℝ) * (T : ℝ)) ^ eta *
            (F ^ 2 * (T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) +
              F ^ 2 * (R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
                ((B : ℝ) ^ 2 * (K : ℝ))))) := by ring
    _ ≤ _ := by gcongr

/-- Combined Brun--Titchmarsh coefficient for both square-product dyadic pieces. -/
def mtTypeIPrimeRaisedHeathBrownBTMomentCoefficient
    (P ell B N N' : ℕ) (T eta z : ℝ) : ℝ :=
  2 * mtTypeIPrimeRaisedHeathBrownBTPieceCoefficient
      P ell B N' (N * N) T eta z +
    2 * mtTypeIPrimeRaisedHeathBrownBTPieceCoefficient
      P ell B N' (2 * (N * N)) T eta z

theorem mtTypeIPrimeRaisedHeathBrownEnergyMomentCoefficient_le_bt
    (P ell : ℕ) {B N N' : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N)
    (T : Set.Ioi (0 : ℝ)) {eta z : ℝ} (heta : 0 < eta) (hz : 1 < z) :
    mtTypeIPrimeRaisedHeathBrownEnergyMomentCoefficient
        P ell B N N' (T : ℝ) eta ≤
      mtTypeIPrimeRaisedHeathBrownBTMomentCoefficient
        P ell B N N' (T : ℝ) eta z := by
  have hKlow : 1 ≤ N * N := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hKhigh : 1 ≤ 2 * (N * N) := by omega
  have hlow := mtTypeIPrimeRaisedHeathBrownEnergyPieceCoefficient_le_bt
    P ell (N' := N') (K := N * N) hB hKlow T heta hz
  have hhigh := mtTypeIPrimeRaisedHeathBrownEnergyPieceCoefficient_le_bt
    P ell (N' := N') (K := 2 * (N * N)) hB hKhigh T heta hz
  rw [mtTypeIPrimeRaisedHeathBrownEnergyMomentCoefficient,
    mtTypeIPrimeRaisedHeathBrownBTMomentCoefficient]
  gcongr

/-- Literal mixed Watt moment with all exact support statistics removed. -/
theorem intervalIntegral_normPow_mtWattUnitBlock_mul_normSq_mtTypeIPrimeRaised_le_bt
    (P ell : ℕ) {B N N' : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N)
    (hN' : 1 ≤ N') (hN'le : N' ≤ 2 * N)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    {eta z : ℝ} (heta : 0 < eta) (hz : 1 < z) :
    (∫ t in ((T : ℝ) / 2)..(T : ℝ),
        ‖mtWattUnitBlock N N' t‖ ^ 4 *
          ‖mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t‖ ^ 2) ≤
      mtTypeIPrimeRaisedHeathBrownBTMomentCoefficient
          P ell B N N' (T : ℝ) eta z *
        (∑ m ∈ Finset.Ioc B (2 * B),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2) := by
  have hbase :=
    intervalIntegral_normPow_mtWattUnitBlock_mul_normSq_mtTypeIPrimeRaised_le_energy
      P ell hB hN hN' hN'le T hBT heta
  have hcoeff := mtTypeIPrimeRaisedHeathBrownEnergyMomentCoefficient_le_bt
    P ell (N' := N') hB hN T heta hz
  have henergy : 0 ≤ ∑ m ∈ Finset.Ioc B (2 * B),
      ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  exact hbase.trans (mul_le_mul_of_nonneg_right hcoeff henergy)

end

end RHTower.Sieve
