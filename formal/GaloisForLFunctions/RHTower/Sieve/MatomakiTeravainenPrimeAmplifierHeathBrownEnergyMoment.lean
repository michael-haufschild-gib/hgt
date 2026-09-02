import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierIntegralEnergy

/-!
# Energy-faithful Heath--Brown moment for the powered prime amplifier

Every nonzero coefficient of the literal powered prime amplifier is a positive integer.  The
resulting support-to-energy inequality converts the sparse-cardinality terms in Heath--Brown's
Lemma 3.4 into one exact factor of the Watt block's squared coefficient energy.  This is the
coefficient-faithful form needed by the Type-I source argument.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Coefficient multiplying exact block energy after one Heath--Brown dyadic piece is
linearized in support cardinality. -/
def mtTypeIPrimeRaisedHeathBrownEnergyPieceCoefficient
    (P ell B N' K : ℕ) (T eta : ℝ) : ℝ :=
  (ell.factorial : ℝ) ^ 2 *
    heathBrownLemma34Coefficient eta *
    (heathBrownSquareDivisorScale N' eta) ^ 2 *
    (((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) / (B : ℝ) ^ 2 +
      (((K : ℝ) * T) ^ eta) *
        (T / ((B : ℝ) ^ 2 * (K : ℝ)) +
          ((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) ^ (3 / 4 : ℝ) *
            T ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ))))

/-- One divisor-scale Heath--Brown piece is its explicit coefficient times exact block energy. -/
theorem factorial_sq_mul_mtTypeIPrimeRaisedHeathBrownDivisorPieceBound_le_energy
    (P ell : ℕ) {B N N' K : ℕ} (hB : 1 ≤ B) (hK : 1 ≤ K)
    (T : Set.Ioi (0 : ℝ)) {eta : ℝ} (heta : 0 < eta) :
    (ell.factorial : ℝ) ^ 2 *
        mtTypeIPrimeRaisedHeathBrownDivisorPieceBound
          P ell B N N' K (T : ℝ) eta ≤
      mtTypeIPrimeRaisedHeathBrownEnergyPieceCoefficient
          P ell B N' K (T : ℝ) eta *
        (∑ m ∈ Finset.Ioc B (2 * B),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2) := by
  let R : ℝ := ((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ)
  let E : ℝ := ∑ m ∈ Finset.Ioc B (2 * B),
    ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2
  have hR0 : 0 ≤ R := by positivity
  have hRE : R ≤ E := by
    exact card_mtTypeIPrimeRaisedBlockSupportPNat_le_energy P ell B
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hdenpos : (0 : ℝ) < (B : ℝ) ^ 2 * (K : ℝ) := by positivity
  have hfirst : (R / (B : ℝ)) ^ 2 ≤ R / (B : ℝ) ^ 2 * E := by
    field_simp [hBpos.ne']
    nlinarith
  have hlinear : R * (T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) ≤
      (T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) * E := by
    have hfactor : 0 ≤ (T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) :=
      div_nonneg T.property.le hdenpos.le
    calc
      R * (T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) =
          R * ((T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ))) := by ring
      _ ≤ E * ((T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ))) :=
        mul_le_mul_of_nonneg_right hRE hfactor
      _ = (T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) * E := by ring
  have hseven : R ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
        ((B : ℝ) ^ 2 * (K : ℝ)) ≤
      (R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
        ((B : ℝ) ^ 2 * (K : ℝ))) * E := by
    by_cases hRzero : R = 0
    · simp [hRzero]
    · have hRpos : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hRzero)
      have hsplit : R ^ (7 / 4 : ℝ) = R ^ (3 / 4 : ℝ) * R := by
        calc
          R ^ (7 / 4 : ℝ) = R ^ ((3 / 4 : ℝ) + 1) := by norm_num
          _ = R ^ (3 / 4 : ℝ) * R ^ (1 : ℝ) := Real.rpow_add hRpos _ _
          _ = R ^ (3 / 4 : ℝ) * R := by rw [Real.rpow_one]
      have hfactor : 0 ≤
          R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
            ((B : ℝ) ^ 2 * (K : ℝ)) := by
        exact div_nonneg
          (mul_nonneg (Real.rpow_nonneg hR0 _)
            (Real.rpow_nonneg T.property.le _)) hdenpos.le
      rw [hsplit]
      calc
        (R ^ (3 / 4 : ℝ) * R) * (T : ℝ) ^ (3 / 4 : ℝ) /
            ((B : ℝ) ^ 2 * (K : ℝ)) =
            R * (R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
              ((B : ℝ) ^ 2 * (K : ℝ))) := by ring
        _ ≤ E * (R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
              ((B : ℝ) ^ 2 * (K : ℝ))) := by
          gcongr
        _ = (R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
              ((B : ℝ) ^ 2 * (K : ℝ))) * E := by ring
  have hpowKT : 0 ≤ (((K : ℝ) * (T : ℝ)) ^ eta) :=
    Real.rpow_nonneg (mul_nonneg hKpos.le T.property.le) _
  have hscalar :
      (R / (B : ℝ)) ^ 2 + (((K : ℝ) * (T : ℝ)) ^ eta) *
          (R * (T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) +
            R ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
              ((B : ℝ) ^ 2 * (K : ℝ))) ≤
        (R / (B : ℝ) ^ 2 + (((K : ℝ) * (T : ℝ)) ^ eta) *
          ((T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) +
            R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
              ((B : ℝ) ^ 2 * (K : ℝ)))) * E := by
    calc
      _ ≤ R / (B : ℝ) ^ 2 * E + (((K : ℝ) * (T : ℝ)) ^ eta) *
          (((T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ))) * E +
            (R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
              ((B : ℝ) ^ 2 * (K : ℝ))) * E) := by
        gcongr
      _ = _ := by ring
  have hC : 0 ≤ heathBrownLemma34Coefficient eta := by
    have hdiv : 0 < divisorBoundConst (eta / 4) :=
      divisorBoundConst_pos (by linarith)
    rw [heathBrownLemma34Coefficient, heathBrownLemma34PositiveCoefficient,
      heathBrownTheoremFourCoefficient, heathBrownTheoremFourUniversalCoefficient,
      heathBrownMeanSquareCoefficient]
    positivity
  rw [mtTypeIPrimeRaisedHeathBrownDivisorPieceBound,
    mtTypeIPrimeRaisedHeathBrownEnergyPieceCoefficient]
  change (ell.factorial : ℝ) ^ 2 *
      (heathBrownLemma34Coefficient eta *
        (heathBrownSquareDivisorScale N' eta) ^ 2 *
          ((R / (B : ℝ)) ^ 2 + (((K : ℝ) * (T : ℝ)) ^ eta) *
            (R * (T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) +
              R ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
                ((B : ℝ) ^ 2 * (K : ℝ))))) ≤ _
  change _ ≤ ((ell.factorial : ℝ) ^ 2 *
      heathBrownLemma34Coefficient eta *
      (heathBrownSquareDivisorScale N' eta) ^ 2 *
        (R / (B : ℝ) ^ 2 + (((K : ℝ) * (T : ℝ)) ^ eta) *
          ((T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) +
            R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
              ((B : ℝ) ^ 2 * (K : ℝ))))) * E
  calc
    _ ≤ (ell.factorial : ℝ) ^ 2 *
        (heathBrownLemma34Coefficient eta *
          (heathBrownSquareDivisorScale N' eta) ^ 2 *
            ((R / (B : ℝ) ^ 2 + (((K : ℝ) * (T : ℝ)) ^ eta) *
              ((T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) +
                R ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
                  ((B : ℝ) ^ 2 * (K : ℝ)))) * E)) := by
      gcongr
    _ = _ := by ring

/-- Combined coefficient for the two dyadic pieces of the squared reciprocal unit block. -/
def mtTypeIPrimeRaisedHeathBrownEnergyMomentCoefficient
    (P ell B N N' : ℕ) (T eta : ℝ) : ℝ :=
  2 * mtTypeIPrimeRaisedHeathBrownEnergyPieceCoefficient
      P ell B N' (N * N) T eta +
    2 * mtTypeIPrimeRaisedHeathBrownEnergyPieceCoefficient
      P ell B N' (2 * (N * N)) T eta

/-- Literal Type-I Watt moment bounded by an explicit scalar times its exact coefficient energy. -/
theorem intervalIntegral_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le_energy
    (P ell : ℕ) {B N N' : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N)
    (hN' : 1 ≤ N') (hN'le : N' ≤ 2 * N)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in ((T : ℝ) / 2)..(T : ℝ),
        ‖mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t *
          (mtWattUnitBlock N N' t) ^ 2‖ ^ 2) ≤
      mtTypeIPrimeRaisedHeathBrownEnergyMomentCoefficient
          P ell B N N' (T : ℝ) eta *
        (∑ m ∈ Finset.Ioc B (2 * B),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2) := by
  let E : ℝ := ∑ m ∈ Finset.Ioc B (2 * B),
    ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2
  let Dlow := mtTypeIPrimeRaisedHeathBrownDivisorPieceBound
    P ell B N N' (N * N) (T : ℝ) eta
  let Dhigh := mtTypeIPrimeRaisedHeathBrownDivisorPieceBound
    P ell B N N' (2 * (N * N)) (T : ℝ) eta
  let Clow := mtTypeIPrimeRaisedHeathBrownEnergyPieceCoefficient
    P ell B N' (N * N) (T : ℝ) eta
  let Chigh := mtTypeIPrimeRaisedHeathBrownEnergyPieceCoefficient
    P ell B N' (2 * (N * N)) (T : ℝ) eta
  have hbase :=
    intervalIntegral_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le_divisorScale
      P ell hB hN hN' hN'le T hBT heta
  have hKlow : 1 ≤ N * N := by
    have := Nat.mul_le_mul (show 1 ≤ N by omega) (show 1 ≤ N by omega)
    simpa using this
  have hKhigh : 1 ≤ 2 * (N * N) := by omega
  have hlow : (ell.factorial : ℝ) ^ 2 * Dlow ≤ Clow * E := by
    exact factorial_sq_mul_mtTypeIPrimeRaisedHeathBrownDivisorPieceBound_le_energy
      P ell hB hKlow T heta
  have hhigh : (ell.factorial : ℝ) ^ 2 * Dhigh ≤ Chigh * E := by
    exact factorial_sq_mul_mtTypeIPrimeRaisedHeathBrownDivisorPieceBound_le_energy
      P ell hB hKhigh T heta
  change _ ≤ (2 * Clow + 2 * Chigh) * E
  change _ ≤ (ell.factorial : ℝ) ^ 2 * (2 * Dlow + 2 * Dhigh) at hbase
  calc
    _ ≤ (ell.factorial : ℝ) ^ 2 * (2 * Dlow + 2 * Dhigh) := hbase
    _ = 2 * ((ell.factorial : ℝ) ^ 2 * Dlow) +
        2 * ((ell.factorial : ℝ) ^ 2 * Dhigh) := by ring
    _ ≤ 2 * (Clow * E) + 2 * (Chigh * E) := by gcongr
    _ = (2 * Clow + 2 * Chigh) * E := by ring

/-- Product-of-norms presentation used directly by the restricted Type-I Cauchy receiver. -/
theorem intervalIntegral_normPow_mtWattUnitBlock_mul_normSq_mtTypeIPrimeRaised_le_energy
    (P ell : ℕ) {B N N' : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N)
    (hN' : 1 ≤ N') (hN'le : N' ≤ 2 * N)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in ((T : ℝ) / 2)..(T : ℝ),
        ‖mtWattUnitBlock N N' t‖ ^ 4 *
          ‖mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t‖ ^ 2) ≤
      mtTypeIPrimeRaisedHeathBrownEnergyMomentCoefficient
          P ell B N N' (T : ℝ) eta *
        (∑ m ∈ Finset.Ioc B (2 * B),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2) := by
  have h := intervalIntegral_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le_energy
    P ell hB hN hN' hN'le T hBT heta
  convert h using 1
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [norm_mul, norm_pow]
  ring

end

end RHTower.Sieve
