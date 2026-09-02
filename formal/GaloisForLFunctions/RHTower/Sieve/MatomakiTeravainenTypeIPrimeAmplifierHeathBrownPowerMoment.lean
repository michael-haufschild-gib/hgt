import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownCanonicalMoment

/-!
# Height-power absorption for the Heath--Brown Type-I coefficient

After factorial absorption, the remaining arithmetic losses are the square-divisor normalizer and
two factors `(K T)^eta`.  On the sub-height branch `N ≤ T`, both cost explicit powers of `T`.
The complete two-piece coefficient is a fixed constant times `T^(12 eta)` and the literal
Deshouillers--Iwaniec bracket.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The square-divisor normalizer costs at most four powers of height in exponent `eta`. -/
theorem heathBrownSquareDivisorScale_le_height_rpow
    {N N' : ℕ} {T eta : ℝ} (hN'le : N' ≤ 2 * N) (hNT : (N : ℝ) ≤ T)
    (hT : 2 ≤ T) (heta : 0 < eta) :
    heathBrownSquareDivisorScale N' eta ≤
      divisorBoundConst eta * T ^ (4 * eta) := by
  have hT0 : 0 ≤ T := zero_le_two.trans hT
  have hN'cast : (N' : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hN'le
  have hN'T : (N' : ℝ) ≤ 2 * T := hN'cast.trans (by gcongr)
  have hsquare1 : (N' : ℝ) ^ 2 ≤ (2 * T) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hN'T 2
  have hfour : (4 : ℝ) ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 2)]
  have hsquare2 : (2 * T) ^ 2 ≤ T ^ 4 := by
    calc
      (2 * T) ^ 2 = 4 * T ^ 2 := by ring
      _ ≤ T ^ 2 * T ^ 2 := mul_le_mul_of_nonneg_right hfour (sq_nonneg T)
      _ = T ^ 4 := by ring
  have hnatSquare : (((N' * N' : ℕ) : ℝ)) ≤ T ^ 4 := by
    simpa [pow_two] using hsquare1.trans hsquare2
  have hrpow : (((N' * N' : ℕ) : ℝ)) ^ eta ≤ (T ^ 4) ^ eta :=
    Real.rpow_le_rpow (by positivity) hnatSquare heta.le
  have hpow : (T ^ 4) ^ eta = T ^ (4 * eta) := by
    rw [← Real.rpow_natCast T 4, ← Real.rpow_mul hT0]
    norm_num
  rw [hpow] at hrpow
  rw [heathBrownSquareDivisorScale]
  exact mul_le_mul_of_nonneg_left hrpow (divisorBoundConst_pos heta).le

/-- Both square-product dyadic lengths cost at most four powers of height in exponent `eta`. -/
theorem mul_height_rpow_le_height_four_eta
    {N K : ℕ} {T eta : ℝ} (hNtwo : 2 ≤ N)
    (hKhi : K ≤ 2 * (N * N))
    (hNT : (N : ℝ) ≤ T) (hT : 2 ≤ T) (heta : 0 < eta) :
    (((K : ℝ) * T) ^ eta) ≤ T ^ (4 * eta) := by
  have hT0 : 0 ≤ T := zero_le_two.trans hT
  have hKcast : (K : ℝ) ≤ 2 * ((N : ℝ) * N) := by exact_mod_cast hKhi
  have hNsq : (N : ℝ) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by positivity) hNT 2
  have hNsqMul : (N : ℝ) * N ≤ T ^ 2 := by simpa [pow_two] using hNsq
  have hKT : (K : ℝ) * T ≤ T ^ 4 := by
    calc
      (K : ℝ) * T ≤ (2 * ((N : ℝ) * N)) * T := by gcongr
      _ ≤ (2 * T ^ 2) * T := by gcongr
      _ ≤ T * T ^ 2 * T := by gcongr
      _ = T ^ 4 := by ring
  have hrpow := Real.rpow_le_rpow (by positivity) hKT heta.le
  have hpow : (T ^ 4) ^ eta = T ^ (4 * eta) := by
    rw [← Real.rpow_natCast T 4, ← Real.rpow_mul hT0]
    norm_num
  rwa [hpow] at hrpow

/-- Fixed constant multiplying the height-power Type-I coefficient. -/
def mtTypeIPrimeHeathBrownPowerConstant (eta : ℝ) : ℝ :=
  heathBrownLemma34Coefficient eta * (divisorBoundConst eta) ^ 2

/-- A factorial-free piece is a fixed constant times `T^(12 eta)` and the literal DI bracket. -/
theorem mtTypeIPrimeRaisedHeathBrownAbsorbedPieceCoefficient_le_power
    {N N' K B : ℕ} (T : Set.Ioi (0 : ℝ)) {eta : ℝ}
    (hN : 2 ≤ N) (hN'le : N' ≤ 2 * N)
    (hKlo : N * N ≤ K) (hKhi : K ≤ 2 * (N * N))
    (hNT : (N : ℝ) ≤ (T : ℝ)) (hT : 2 ≤ (T : ℝ)) (heta : 0 < eta) :
    mtTypeIPrimeRaisedHeathBrownAbsorbedPieceCoefficient N' K B (T : ℝ) eta ≤
      mtTypeIPrimeHeathBrownPowerConstant eta * (T : ℝ) ^ (12 * eta) *
        (1 + (T : ℝ) / ((N : ℝ) ^ 2) +
          (B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) / ((N : ℝ) ^ 2)) := by
  have hT0 : (0 : ℝ) ≤ T := T.property.le
  have hT1 : (1 : ℝ) ≤ T := one_le_two.trans hT
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) hKlo
  have hNK : ((N : ℝ) ^ 2) ≤ (K : ℝ) := by
    have hNK' : (((N * N : ℕ) : ℝ)) ≤ (K : ℝ) := by exact_mod_cast hKlo
    simpa [pow_two] using hNK'
  have hdivT : (T : ℝ) / K ≤ (T : ℝ) / ((N : ℝ) ^ 2) :=
    div_le_div_of_nonneg_left hT0 (by positivity) hNK
  have hnum : 0 ≤ (B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) := by positivity
  have hdivB : (B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) / K ≤
      (B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) / ((N : ℝ) ^ 2) :=
    div_le_div_of_nonneg_left hnum (by positivity) hNK
  let R : ℝ := (T : ℝ) / ((N : ℝ) ^ 2) +
    (B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) / ((N : ℝ) ^ 2)
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hbracket : (T : ℝ) / K +
      (B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) / K ≤ R := by
    dsimp only [R]
    linarith
  have hD := heathBrownSquareDivisorScale_le_height_rpow hN'le hNT hT heta
  have hD0 : 0 ≤ heathBrownSquareDivisorScale N' eta := by
    rw [heathBrownSquareDivisorScale]
    exact mul_nonneg (divisorBoundConst_pos heta).le (Real.rpow_nonneg (by positivity) _)
  have hDbig0 : 0 ≤ divisorBoundConst eta * (T : ℝ) ^ (4 * eta) :=
    mul_nonneg (divisorBoundConst_pos heta).le (Real.rpow_nonneg hT0 _)
  have hDsq : (heathBrownSquareDivisorScale N' eta) ^ 2 ≤
      (divisorBoundConst eta) ^ 2 * (T : ℝ) ^ (8 * eta) := by
    calc
      (heathBrownSquareDivisorScale N' eta) ^ 2 ≤
          (divisorBoundConst eta * (T : ℝ) ^ (4 * eta)) ^ 2 :=
        pow_le_pow_left₀ hD0 hD 2
      _ = (divisorBoundConst eta) ^ 2 * (T : ℝ) ^ (8 * eta) := by
        rw [mul_pow]
        rw [← Real.rpow_natCast ((T : ℝ) ^ (4 * eta)) 2,
          ← Real.rpow_mul hT0]
        ring_nf
  have hKT := mul_height_rpow_le_height_four_eta hN hKhi hNT hT heta
  have hZ1 : (1 : ℝ) ≤ (T : ℝ) ^ (4 * eta) :=
    Real.one_le_rpow hT1 (by positivity)
  have hinner : 1 + (((K : ℝ) * (T : ℝ)) ^ eta) *
      ((T : ℝ) / K +
        (B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) / K) ≤
      (T : ℝ) ^ (4 * eta) * (1 + R) := by
    calc
      _ ≤ 1 + (T : ℝ) ^ (4 * eta) * R := by gcongr
      _ ≤ (T : ℝ) ^ (4 * eta) + (T : ℝ) ^ (4 * eta) * R := by linarith
      _ = (T : ℝ) ^ (4 * eta) * (1 + R) := by ring
  have hC : 0 ≤ heathBrownLemma34Coefficient eta := by
    have hdiv : 0 < divisorBoundConst (eta / 4) :=
      divisorBoundConst_pos (by linarith)
    rw [heathBrownLemma34Coefficient, heathBrownLemma34PositiveCoefficient,
      heathBrownTheoremFourCoefficient, heathBrownTheoremFourUniversalCoefficient,
      heathBrownMeanSquareCoefficient]
    positivity
  have hpowAdd : (T : ℝ) ^ (8 * eta) * (T : ℝ) ^ (4 * eta) =
      (T : ℝ) ^ (12 * eta) := by
    rw [← Real.rpow_add T.property]
    congr 1
    ring
  rw [mtTypeIPrimeRaisedHeathBrownAbsorbedPieceCoefficient,
    mtTypeIPrimeHeathBrownPowerConstant]
  calc
    _ ≤ heathBrownLemma34Coefficient eta *
        ((divisorBoundConst eta) ^ 2 * (T : ℝ) ^ (8 * eta)) *
          ((T : ℝ) ^ (4 * eta) * (1 + R)) := by gcongr
    _ = heathBrownLemma34Coefficient eta * (divisorBoundConst eta) ^ 2 *
        (T : ℝ) ^ (12 * eta) * (1 + R) := by
      rw [show heathBrownLemma34Coefficient eta *
          ((divisorBoundConst eta) ^ 2 * (T : ℝ) ^ (8 * eta)) *
            ((T : ℝ) ^ (4 * eta) * (1 + R)) =
          heathBrownLemma34Coefficient eta * (divisorBoundConst eta) ^ 2 *
            ((T : ℝ) ^ (8 * eta) * (T : ℝ) ^ (4 * eta)) * (1 + R) by ring,
        hpowAdd]
    _ = _ := by dsimp only [R]; ring

/-- Final height-power coefficient for both unit-square dyadic pieces. -/
def mtTypeIPrimeRaisedHeathBrownPowerMomentCoefficient
    (N B : ℕ) (T eta : ℝ) : ℝ :=
  4 * mtTypeIPrimeHeathBrownPowerConstant eta * T ^ (12 * eta) *
    (1 + T / ((N : ℝ) ^ 2) +
      (B : ℝ) ^ (3 / 4 : ℝ) * T ^ (3 / 4 : ℝ) / ((N : ℝ) ^ 2))

/-- Both factorial-free pieces are absorbed into one fixed `T^(12 eta)` coefficient. -/
theorem mtTypeIPrimeRaisedHeathBrownAbsorbedMomentCoefficient_le_power
    {N N' B : ℕ} (T : Set.Ioi (0 : ℝ)) {eta : ℝ}
    (hN : 2 ≤ N) (hN'le : N' ≤ 2 * N)
    (hNT : (N : ℝ) ≤ (T : ℝ)) (hT : 2 ≤ (T : ℝ)) (heta : 0 < eta) :
    mtTypeIPrimeRaisedHeathBrownAbsorbedMomentCoefficient N N' B (T : ℝ) eta ≤
      mtTypeIPrimeRaisedHeathBrownPowerMomentCoefficient N B (T : ℝ) eta := by
  have hNpos : 0 < N := by omega
  have hlowLo : N * N ≤ N * N := le_rfl
  have hlowHi : N * N ≤ 2 * (N * N) := by omega
  have hhighLo : N * N ≤ 2 * (N * N) := by omega
  have hhighHi : 2 * (N * N) ≤ 2 * (N * N) := le_rfl
  have hlow := mtTypeIPrimeRaisedHeathBrownAbsorbedPieceCoefficient_le_power
    (N' := N') (K := N * N) (B := B) T hN hN'le hlowLo hlowHi hNT hT heta
  have hhigh := mtTypeIPrimeRaisedHeathBrownAbsorbedPieceCoefficient_le_power
    (N' := N') (K := 2 * (N * N)) (B := B) T hN hN'le
      hhighLo hhighHi hNT hT heta
  rw [mtTypeIPrimeRaisedHeathBrownAbsorbedMomentCoefficient,
    mtTypeIPrimeRaisedHeathBrownPowerMomentCoefficient]
  linarith

/-- Published-epsilon form obtained by choosing the auxiliary divisor exponent `eta = epsilon/24`. -/
def mtTypeIPrimeRaisedHeathBrownEpsilonMomentCoefficient
    (N B : ℕ) (T epsilon : ℝ) : ℝ :=
  4 * mtTypeIPrimeHeathBrownPowerConstant (epsilon / 24) * T ^ (epsilon / 2) *
    (1 + T / ((N : ℝ) ^ 2) +
      (B : ℝ) ^ (3 / 4 : ℝ) * T ^ (3 / 4 : ℝ) / ((N : ℝ) ^ 2))

/-- Exact exponent identity `12 * (epsilon/24) = epsilon/2`. -/
theorem mtTypeIPrimeRaisedHeathBrownPowerMomentCoefficient_epsilon_eq
    (N B : ℕ) (T epsilon : ℝ) :
    mtTypeIPrimeRaisedHeathBrownPowerMomentCoefficient N B T (epsilon / 24) =
      mtTypeIPrimeRaisedHeathBrownEpsilonMomentCoefficient N B T epsilon := by
  rw [mtTypeIPrimeRaisedHeathBrownPowerMomentCoefficient,
    mtTypeIPrimeRaisedHeathBrownEpsilonMomentCoefficient]
  congr 3
  ring

end

end RHTower.Sieve
