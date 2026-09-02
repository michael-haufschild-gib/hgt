import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerSourceReceiver
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownPowerMoment

/-!
# Height absorption for the source-saving Heath--Brown layer root

On the sub-height branch `N ≤ T`, both square-product lengths and the square-divisor scale cost
explicit `T^(4 eta)` factors.  This module performs only those monotone substitutions and retains
the two negative amplifier powers unchanged.
-/

namespace RHTower.Sieve

noncomputable section

/-- One source-saving layer root after square-product and divisor scales are paid by height. -/
def mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound
    (P ell N : ℕ) (T eta rho : ℝ) : ℝ :=
  let M : ℝ := ((P ^ ell : ℕ) : ℝ)
  let L : ℝ := (((mtTypeIPrimeCoeffSupport P).card ^ ell : ℕ) : ℝ)
  Real.sqrt (heathBrownLemma34Coefficient eta) *
    (divisorBoundConst eta * T ^ (4 * eta)) *
    (L / M +
      Real.sqrt (T ^ (4 * eta) * T / ((N : ℝ) ^ 2)) *
        M ^ (-(1 - rho) / 2) +
      Real.sqrt (T ^ (4 * eta) * T ^ (3 / 4 : ℝ) / ((N : ℝ) ^ 2)) *
        M ^ (-(1 - rho) / 8))

/-- Either square-product dyadic piece is bounded by the same source-height root. -/
theorem mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound_le_height
    {P ell N N' K : ℕ} (T : Set.Ioi (0 : ℝ)) {eta rho : ℝ}
    (hN : 2 ≤ N) (hN'le : N' ≤ 2 * N)
    (hKlo : N * N ≤ K) (hKhi : K ≤ 2 * (N * N))
    (hNT : (N : ℝ) ≤ (T : ℝ)) (hT : 2 ≤ (T : ℝ)) (heta : 0 < eta) :
    mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound
        P ell N' K (T : ℝ) eta rho ≤
      mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound
        P ell N (T : ℝ) eta rho := by
  let M : ℝ := ((P ^ ell : ℕ) : ℝ)
  let L : ℝ := (((mtTypeIPrimeCoeffSupport P).card ^ ell : ℕ) : ℝ)
  let Q : ℝ := (((K : ℝ) * (T : ℝ)) ^ eta)
  let H : ℝ := (T : ℝ) ^ (4 * eta)
  let zHalf : ℝ := M ^ (-(1 - rho) / 2)
  let zSeven : ℝ := M ^ (-(1 - rho) / 8)
  have hT0 : (0 : ℝ) ≤ T := T.property.le
  have hNreal : (0 : ℝ) < N := by positivity
  have hKreal : (0 : ℝ) < K := by
    exact_mod_cast lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) hKlo
  have hNsqK : ((N : ℝ) ^ 2) ≤ (K : ℝ) := by
    have hcast : (((N * N : ℕ) : ℝ)) ≤ (K : ℝ) := by exact_mod_cast hKlo
    simpa [pow_two] using hcast
  have hQH : Q ≤ H := by
    dsimp only [Q, H]
    exact mul_height_rpow_le_height_four_eta hN hKhi hNT hT heta
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg (mul_nonneg hKreal.le hT0) _
  have hH0 : 0 ≤ H := Real.rpow_nonneg hT0 _
  have hhalfArg :
      Q * (T : ℝ) / (K : ℝ) ≤
        H * (T : ℝ) / ((N : ℝ) ^ 2) := by
    calc
      Q * (T : ℝ) / (K : ℝ) ≤ H * (T : ℝ) / (K : ℝ) := by gcongr
      _ ≤ H * (T : ℝ) / ((N : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hH0 hT0)
          (by positivity) hNsqK
  have hsevenArg :
      Q * (T : ℝ) ^ (3 / 4 : ℝ) / (K : ℝ) ≤
        H * (T : ℝ) ^ (3 / 4 : ℝ) / ((N : ℝ) ^ 2) := by
    calc
      Q * (T : ℝ) ^ (3 / 4 : ℝ) / (K : ℝ) ≤
          H * (T : ℝ) ^ (3 / 4 : ℝ) / (K : ℝ) := by gcongr
      _ ≤ H * (T : ℝ) ^ (3 / 4 : ℝ) / ((N : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left
          (mul_nonneg hH0 (Real.rpow_nonneg hT0 _)) (by positivity) hNsqK
  have hhalf := Real.sqrt_le_sqrt hhalfArg
  have hseven := Real.sqrt_le_sqrt hsevenArg
  have hD := heathBrownSquareDivisorScale_le_height_rpow
    hN'le hNT hT heta
  have hD0 : 0 ≤ heathBrownSquareDivisorScale N' eta := by
    rw [heathBrownSquareDivisorScale]
    exact mul_nonneg (divisorBoundConst_pos heta).le
      (Real.rpow_nonneg (by positivity) _)
  have hDbig0 : 0 ≤ divisorBoundConst eta * H :=
    mul_nonneg (divisorBoundConst_pos heta).le hH0
  have hzHalf : 0 ≤ zHalf := Real.rpow_nonneg (by positivity) _
  have hzSeven : 0 ≤ zSeven := Real.rpow_nonneg (by positivity) _
  rw [mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound,
    mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound]
  change Real.sqrt (heathBrownLemma34Coefficient eta) *
      heathBrownSquareDivisorScale N' eta *
        (L / M + Real.sqrt (Q * (T : ℝ) / (K : ℝ)) * zHalf +
          Real.sqrt (Q * (T : ℝ) ^ (3 / 4 : ℝ) / (K : ℝ)) * zSeven) ≤
    Real.sqrt (heathBrownLemma34Coefficient eta) *
      (divisorBoundConst eta * H) *
        (L / M + Real.sqrt (H * (T : ℝ) / ((N : ℝ) ^ 2)) * zHalf +
          Real.sqrt (H * (T : ℝ) ^ (3 / 4 : ℝ) / ((N : ℝ) ^ 2)) * zSeven)
  gcongr

/-- Both dyadic square-product pieces share twice one source-height root. -/
theorem add_mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound_le_height
    {P ell N N' : ℕ} (T : Set.Ioi (0 : ℝ)) {eta rho : ℝ}
    (hN : 2 ≤ N) (hN'le : N' ≤ 2 * N)
    (hNT : (N : ℝ) ≤ (T : ℝ)) (hT : 2 ≤ (T : ℝ)) (heta : 0 < eta) :
    mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound
        P ell N' (N * N) (T : ℝ) eta rho +
      mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound
        P ell N' (2 * (N * N)) (T : ℝ) eta rho ≤
      2 * mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound
        P ell N (T : ℝ) eta rho := by
  have hlow := mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound_le_height
    (P := P) (ell := ell) (eta := eta) (rho := rho) T
      hN hN'le le_rfl (by omega) hNT hT heta
  have hhigh := mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound_le_height
    (P := P) (ell := ell) (eta := eta) (rho := rho) T
      hN hN'le (by omega) le_rfl hNT hT heta
  linarith

end

end RHTower.Sieve
