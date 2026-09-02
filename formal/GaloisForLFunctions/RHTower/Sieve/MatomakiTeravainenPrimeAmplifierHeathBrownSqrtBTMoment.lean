import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownBTMoment
import GaloisForLFunctions.RHTower.Sieve.AdaptiveGallagherBrunTitchmarsh

/-!
# Canonical square-root Brun--Titchmarsh envelope

Choosing the sieve level `sqrt P` makes the Brun--Titchmarsh support envelope
`292 P / log P + 1 + ell`.  This file performs that choice and removes the auxiliary real
parameter from the powered-prime Heath--Brown moment.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The square-root sieve level turns the explicit Brun--Titchmarsh base into `292 P / log P`. -/
theorem mtTypeIPrimeSqrtBTBase_le
    (P ell : ℕ) (hP : 2 ≤ P) :
    2 * (P : ℝ) / Real.log (Real.sqrt P) +
        6 * Real.sqrt P * (1 + Real.log (Real.sqrt P)) ^ 3 + 1 + ell ≤
      292 * (P : ℝ) / Real.log P + 1 + ell := by
  have hPR : (1 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < (P : ℝ) := zero_lt_one.trans hPR
  have herr := bt_error_le_main hPR
  have hlogsqrt : Real.log (Real.sqrt (P : ℝ)) = Real.log P / 2 := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hP0]
    ring
  rw [hlogsqrt] at herr
  have hmain : 2 * (P : ℝ) / Real.log (Real.sqrt (P : ℝ)) =
      4 * (P : ℝ) / Real.log P := by
    rw [hlogsqrt]
    field_simp [Real.log_pos hPR]
    ring
  rw [hmain, hlogsqrt]
  calc
    4 * (P : ℝ) / Real.log P +
        6 * Real.sqrt (P : ℝ) * (1 + Real.log P / 2) ^ 3 + 1 + ell ≤
        4 * (P : ℝ) / Real.log P +
          288 * (P : ℝ) / Real.log P + 1 + ell := by gcongr
    _ = 292 * (P : ℝ) / Real.log P + 1 + ell := by ring

/-- Canonical support estimate with no free Brun--Titchmarsh level. -/
theorem factorial_mul_card_mtTypeIPrimeRaisedBlockSupportPNat_le_sqrt_bt
    (P ell B : ℕ) (hP : 2 ≤ P) :
    (((ell.factorial *
        (mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℕ) : ℝ)) ≤
      (292 * (P : ℝ) / Real.log P + 1 + ell) ^ ell := by
  have hPR : (1 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < (P : ℝ) := zero_lt_one.trans hPR
  have hsqrt : (1 : ℝ) < Real.sqrt (P : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hPR
  have hgeneral := factorial_mul_card_mtTypeIPrimeRaisedBlockSupportPNat_le_bt
    P ell B hsqrt
  have hbase := mtTypeIPrimeSqrtBTBase_le P ell hP
  have hsource0 : 0 ≤
      2 * (P : ℝ) / Real.log (Real.sqrt (P : ℝ)) +
          6 * Real.sqrt (P : ℝ) * (1 + Real.log (Real.sqrt (P : ℝ))) ^ 3 +
          1 + ell := by
    have hlog : 0 < Real.log (Real.sqrt (P : ℝ)) := Real.log_pos hsqrt
    positivity
  exact hgeneral.trans (pow_le_pow_left₀ hsource0 hbase ell)

/-- One-piece coefficient after the canonical square-root sieve choice. -/
def mtTypeIPrimeRaisedHeathBrownSqrtBTPieceCoefficient
    (P ell B N' K : ℕ) (T eta : ℝ) : ℝ :=
  let Q := 292 * (P : ℝ) / Real.log P + 1 + ell
  heathBrownLemma34Coefficient eta *
    (heathBrownSquareDivisorScale N' eta) ^ 2 *
    ((ell.factorial : ℝ) * Q ^ ell / (B : ℝ) ^ 2 +
      (((K : ℝ) * T) ^ eta) *
        ((ell.factorial : ℝ) ^ 2 * T / ((B : ℝ) ^ 2 * (K : ℝ)) +
          (ell.factorial : ℝ) ^ 2 * (B : ℝ) ^ (3 / 4 : ℝ) *
            T ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ))))

/-- Generic Brun--Titchmarsh coefficient at `sqrt P` is bounded by the canonical coefficient. -/
theorem mtTypeIPrimeRaisedHeathBrownBTPieceCoefficient_sqrt_le
    (P ell : ℕ) {B N' K : ℕ} (hP : 2 ≤ P) (hB : 1 ≤ B) (hK : 1 ≤ K)
    (T : Set.Ioi (0 : ℝ)) {eta : ℝ} (heta : 0 < eta) :
    mtTypeIPrimeRaisedHeathBrownBTPieceCoefficient
        P ell B N' K (T : ℝ) eta (Real.sqrt P) ≤
      mtTypeIPrimeRaisedHeathBrownSqrtBTPieceCoefficient
        P ell B N' K (T : ℝ) eta := by
  let Qold : ℝ := 2 * (P : ℝ) / Real.log (Real.sqrt P) +
    6 * Real.sqrt P * (1 + Real.log (Real.sqrt P)) ^ 3 + 1 + ell
  let Qnew : ℝ := 292 * (P : ℝ) / Real.log P + 1 + ell
  have hPR : (1 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hsqrt : (1 : ℝ) < Real.sqrt (P : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hPR
  have hQ : Qold ≤ Qnew := mtTypeIPrimeSqrtBTBase_le P ell hP
  have hQold0 : 0 ≤ Qold := by
    have hlog : 0 < Real.log (Real.sqrt (P : ℝ)) := Real.log_pos hsqrt
    dsimp only [Qold]
    positivity
  have hQpow : Qold ^ ell ≤ Qnew ^ ell :=
    pow_le_pow_left₀ hQold0 hQ ell
  have hpowKT : 0 ≤ ((K : ℝ) * (T : ℝ)) ^ eta :=
    Real.rpow_nonneg (mul_nonneg (by positivity) T.property.le) _
  have hC : 0 ≤ heathBrownLemma34Coefficient eta := by
    have hdiv : 0 < divisorBoundConst (eta / 4) :=
      divisorBoundConst_pos (by linarith)
    rw [heathBrownLemma34Coefficient, heathBrownLemma34PositiveCoefficient,
      heathBrownTheoremFourCoefficient, heathBrownTheoremFourUniversalCoefficient,
      heathBrownMeanSquareCoefficient]
    positivity
  rw [mtTypeIPrimeRaisedHeathBrownBTPieceCoefficient,
    mtTypeIPrimeRaisedHeathBrownSqrtBTPieceCoefficient]
  change heathBrownLemma34Coefficient eta *
      (heathBrownSquareDivisorScale N' eta) ^ 2 *
        ((ell.factorial : ℝ) * Qold ^ ell / (B : ℝ) ^ 2 +
          ((K : ℝ) * (T : ℝ)) ^ eta *
            ((ell.factorial : ℝ) ^ 2 * (T : ℝ) /
                ((B : ℝ) ^ 2 * (K : ℝ)) +
              (ell.factorial : ℝ) ^ 2 * (B : ℝ) ^ (3 / 4 : ℝ) *
                (T : ℝ) ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)))) ≤
    heathBrownLemma34Coefficient eta *
      (heathBrownSquareDivisorScale N' eta) ^ 2 *
        ((ell.factorial : ℝ) * Qnew ^ ell / (B : ℝ) ^ 2 +
          ((K : ℝ) * (T : ℝ)) ^ eta *
            ((ell.factorial : ℝ) ^ 2 * (T : ℝ) /
                ((B : ℝ) ^ 2 * (K : ℝ)) +
              (ell.factorial : ℝ) ^ 2 * (B : ℝ) ^ (3 / 4 : ℝ) *
                (T : ℝ) ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ))))
  gcongr

/-- Combined canonical coefficient for both square-product dyadic pieces. -/
def mtTypeIPrimeRaisedHeathBrownSqrtBTMomentCoefficient
    (P ell B N N' : ℕ) (T eta : ℝ) : ℝ :=
  2 * mtTypeIPrimeRaisedHeathBrownSqrtBTPieceCoefficient
      P ell B N' (N * N) T eta +
    2 * mtTypeIPrimeRaisedHeathBrownSqrtBTPieceCoefficient
      P ell B N' (2 * (N * N)) T eta

theorem mtTypeIPrimeRaisedHeathBrownBTMomentCoefficient_sqrt_le
    (P ell : ℕ) {B N N' : ℕ} (hP : 2 ≤ P) (hB : 1 ≤ B) (hN : 2 ≤ N)
    (T : Set.Ioi (0 : ℝ)) {eta : ℝ} (heta : 0 < eta) :
    mtTypeIPrimeRaisedHeathBrownBTMomentCoefficient
        P ell B N N' (T : ℝ) eta (Real.sqrt P) ≤
      mtTypeIPrimeRaisedHeathBrownSqrtBTMomentCoefficient
        P ell B N N' (T : ℝ) eta := by
  have hKlow : 1 ≤ N * N :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hKhigh : 1 ≤ 2 * (N * N) := by omega
  have hlow := mtTypeIPrimeRaisedHeathBrownBTPieceCoefficient_sqrt_le
    P ell (N' := N') (K := N * N) hP hB hKlow T heta
  have hhigh := mtTypeIPrimeRaisedHeathBrownBTPieceCoefficient_sqrt_le
    P ell (N' := N') (K := 2 * (N * N)) hP hB hKhigh T heta
  rw [mtTypeIPrimeRaisedHeathBrownBTMomentCoefficient,
    mtTypeIPrimeRaisedHeathBrownSqrtBTMomentCoefficient]
  gcongr

/-- Literal mixed Watt moment with canonical support-free coefficient. -/
theorem intervalIntegral_normPow_mtWattUnitBlock_mul_normSq_mtTypeIPrimeRaised_le_sqrt_bt
    (P ell : ℕ) {B N N' : ℕ} (hP : 2 ≤ P) (hB : 1 ≤ B) (hN : 2 ≤ N)
    (hN' : 1 ≤ N') (hN'le : N' ≤ 2 * N)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in ((T : ℝ) / 2)..(T : ℝ),
        ‖mtWattUnitBlock N N' t‖ ^ 4 *
          ‖mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t‖ ^ 2) ≤
      mtTypeIPrimeRaisedHeathBrownSqrtBTMomentCoefficient
          P ell B N N' (T : ℝ) eta *
        (∑ m ∈ Finset.Ioc B (2 * B),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2) := by
  have hPR : (1 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hsqrt : (1 : ℝ) < Real.sqrt (P : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hPR
  have hbase :=
    intervalIntegral_normPow_mtWattUnitBlock_mul_normSq_mtTypeIPrimeRaised_le_bt
      P ell hB hN hN' hN'le T hBT heta hsqrt
  have hcoeff := mtTypeIPrimeRaisedHeathBrownBTMomentCoefficient_sqrt_le
    P ell (N' := N') hP hB hN T heta
  have henergy : 0 ≤ ∑ m ∈ Finset.Ioc B (2 * B),
      ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  exact hbase.trans (mul_le_mul_of_nonneg_right hcoeff henergy)

end

end RHTower.Sieve
