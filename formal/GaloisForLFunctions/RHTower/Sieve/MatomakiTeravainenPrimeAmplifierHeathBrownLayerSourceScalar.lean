import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownLayerCanonical
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierSchedule

/-!
# Source-saving scalar collapse of the Heath--Brown layer root

The source schedule gives `ell ≤ P^rho`, hence `ell! ≤ (P^ell)^rho`.  Retaining this sharper
fact in the threshold-layer moments recovers the precise amplifier saving
`(P^ell)^(-(1-rho)/2)` in the square-root layer and
`(P^ell)^(-(1-rho)/8)` in the seven-eighths layer.
-/

namespace RHTower.Sieve

noncomputable section

/-- Canonical layer root with the exact source sparsity powers exposed. -/
def mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound
    (P ell N' K : ℕ) (T eta rho : ℝ) : ℝ :=
  let M : ℝ := ((P ^ ell : ℕ) : ℝ)
  let L : ℝ := (((mtTypeIPrimeCoeffSupport P).card ^ ell : ℕ) : ℝ)
  Real.sqrt (heathBrownLemma34Coefficient eta) *
    heathBrownSquareDivisorScale N' eta *
    (L / M +
      Real.sqrt ((((K : ℝ) * T) ^ eta) * T / (K : ℝ)) *
        M ^ (-(1 - rho) / 2) +
      Real.sqrt ((((K : ℝ) * T) ^ eta) * T ^ (3 / 4 : ℝ) / (K : ℝ)) *
        M ^ (-(1 - rho) / 8))

/-- The schedule bound on `ell` gives the sharp factorial power needed by layer Jensen. -/
theorem mtTypeIPrime_factorial_le_raisedLength_rpow
    {P ell : ℕ} {rho : ℝ} (hP : 1 ≤ P)
    (hell : (ell : ℝ) ≤ (P : ℝ) ^ rho) :
    (ell.factorial : ℝ) ≤ (((P ^ ell : ℕ) : ℝ)) ^ rho := by
  let M : ℝ := ((P ^ ell : ℕ) : ℝ)
  have hM : 0 < M := by
    dsimp only [M]
    have hPpos : 0 < P := Nat.zero_lt_of_lt hP
    positivity
  have henergy :
      (ell.factorial : ℝ) * M ≤ M ^ (1 + rho) := by
    have hraw := (mtTypeIPrimeRaisedCoeff_factorial_energy_le_power P ell).trans
      (mtTypeIPrimeRaisedCoeff_energy_absorb hP hell)
    simpa only [M, Nat.cast_pow] using hraw
  apply (le_div_iff₀ hM).2 at henergy
  calc
    (ell.factorial : ℝ) ≤ M ^ (1 + rho) / M := henergy
    _ = M ^ rho := by
      rw [div_eq_iff hM.ne']
      calc
        M ^ (1 + rho) = M ^ (rho + 1) := by congr 1; ring
        _ = M ^ rho * M ^ (1 : ℝ) := Real.rpow_add hM rho 1
        _ = M ^ rho * M := by rw [Real.rpow_one]

/-- Every canonical Watt block retains the exact source sparsity saving. -/
theorem mtTypeIPrimeRaisedHeathBrownLayerRootBound_le_source
    {P ell K : ℕ} (hP : 1 ≤ P) {rho : ℝ}
    (hell : (ell : ℝ) ≤ (P : ℝ) ^ rho) (hK : 1 ≤ K)
    (N' : ℕ) (T : Set.Ioi (0 : ℝ)) {eta : ℝ} (heta : 0 < eta)
    (r : Fin ell) :
    mtTypeIPrimeRaisedHeathBrownLayerRootBound P ell
        (mtTypeIPrimeHeathBrownBlockLength P ell r) N' K (T : ℝ) eta ≤
      mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound
        P ell N' K (T : ℝ) eta rho := by
  let M : ℝ := ((P ^ ell : ℕ) : ℝ)
  let L : ℝ := (((mtTypeIPrimeCoeffSupport P).card ^ ell : ℕ) : ℝ)
  let B : ℝ := (mtTypeIPrimeHeathBrownBlockLength P ell r : ℝ)
  let F : ℝ := (ell.factorial : ℝ)
  let Q : ℝ := (((K : ℝ) * (T : ℝ)) ^ eta)
  let zHalf : ℝ := M ^ (-(1 - rho) / 2)
  let zSeven : ℝ := M ^ (-(1 - rho) / 8)
  have hPpos : 0 < P := Nat.zero_lt_of_lt hP
  have hM : 0 < M := by dsimp only [M]; positivity
  have hB : 0 < B := by
    dsimp only [B, mtTypeIPrimeHeathBrownBlockLength]
    positivity
  have hKreal : (0 : ℝ) < K := by exact_mod_cast (Nat.zero_lt_of_lt hK)
  have hMB : M ≤ B := by
    have hMBNat : P ^ ell ≤ P ^ ell * 2 ^ (r : ℕ) := by
      exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
    dsimp only [M, B, mtTypeIPrimeHeathBrownBlockLength]
    exact_mod_cast hMBNat
  have hF0 : 0 ≤ F := by positivity
  have hL0 : 0 ≤ L := by positivity
  have hM0 : 0 ≤ M := hM.le
  have hLM : L ≤ M := by
    dsimp only [L, M]
    exact_mod_cast Nat.pow_le_pow_left (card_mtTypeIPrimeCoeffSupport_le P) ell
  have hFM : F ≤ M ^ rho := by
    simpa only [F, M] using mtTypeIPrime_factorial_le_raisedLength_rpow hP hell
  have hzHalf : 0 ≤ zHalf := Real.rpow_nonneg hM0 _
  have hzSeven : 0 ≤ zSeven := Real.rpow_nonneg hM0 _
  have hhalfNum : F ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) ≤ B * zHalf := by
    calc
      F ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) ≤
          (M ^ rho) ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by
        gcongr
      _ = M ^ ((1 + rho) / 2) := by
        rw [← Real.rpow_mul hM0, ← Real.rpow_add hM]
        congr 1
        ring
      _ = M * zHalf := by
        dsimp only [zHalf]
        calc
          M ^ ((1 + rho) / 2) = M ^ (1 + (-(1 - rho) / 2)) := by
            congr 1; ring
          _ = M ^ (1 : ℝ) * M ^ (-(1 - rho) / 2) :=
            Real.rpow_add hM 1 (-(1 - rho) / 2)
          _ = M * M ^ (-(1 - rho) / 2) := by rw [Real.rpow_one]
      _ ≤ B * zHalf := mul_le_mul_of_nonneg_right hMB hzHalf
  have hsevenNum : F ^ (1 / 8 : ℝ) * L ^ (7 / 8 : ℝ) ≤ B * zSeven := by
    calc
      F ^ (1 / 8 : ℝ) * L ^ (7 / 8 : ℝ) ≤
          (M ^ rho) ^ (1 / 8 : ℝ) * M ^ (7 / 8 : ℝ) := by
        gcongr
      _ = M ^ ((7 + rho) / 8) := by
        rw [← Real.rpow_mul hM0, ← Real.rpow_add hM]
        congr 1
        ring
      _ = M * zSeven := by
        dsimp only [zSeven]
        calc
          M ^ ((7 + rho) / 8) = M ^ (1 + (-(1 - rho) / 8)) := by
            congr 1; ring
          _ = M ^ (1 : ℝ) * M ^ (-(1 - rho) / 8) :=
            Real.rpow_add hM 1 (-(1 - rho) / 8)
          _ = M * M ^ (-(1 - rho) / 8) := by rw [Real.rpow_one]
      _ ≤ B * zSeven := mul_le_mul_of_nonneg_right hMB hzSeven
  have hQ : 0 ≤ Q := Real.rpow_nonneg (mul_nonneg hKreal.le T.property.le) _
  have hfirst : L / B ≤ L / M :=
    div_le_div_of_nonneg_left hL0 hM hMB
  have hsecond :
      Real.sqrt (Q * (T : ℝ) / (B ^ 2 * (K : ℝ))) *
          (F ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) ≤
        Real.sqrt (Q * (T : ℝ) / (K : ℝ)) * zHalf := by
    let c := Real.sqrt (Q * (T : ℝ) / (B ^ 2 * (K : ℝ)))
    have hc : 0 ≤ c := Real.sqrt_nonneg _
    calc
      _ ≤ c * (B * zHalf) := mul_le_mul_of_nonneg_left hhalfNum hc
      _ = (c * B) * zHalf := by ring
      _ ≤ Real.sqrt (Q * (T : ℝ) / (K : ℝ)) * zHalf :=
        mul_le_mul_of_nonneg_right
          (sqrt_div_sq_mul_le (mul_nonneg hQ T.property.le) hB hKreal
            hB.le le_rfl) hzHalf
  have hthird :
      Real.sqrt (Q * (T : ℝ) ^ (3 / 4 : ℝ) / (B ^ 2 * (K : ℝ))) *
          (F ^ (1 / 8 : ℝ) * L ^ (7 / 8 : ℝ)) ≤
        Real.sqrt (Q * (T : ℝ) ^ (3 / 4 : ℝ) / (K : ℝ)) * zSeven := by
    let c := Real.sqrt (Q * (T : ℝ) ^ (3 / 4 : ℝ) / (B ^ 2 * (K : ℝ)))
    have hc : 0 ≤ c := Real.sqrt_nonneg _
    calc
      _ ≤ c * (B * zSeven) := mul_le_mul_of_nonneg_left hsevenNum hc
      _ = (c * B) * zSeven := by ring
      _ ≤ Real.sqrt (Q * (T : ℝ) ^ (3 / 4 : ℝ) / (K : ℝ)) * zSeven :=
        mul_le_mul_of_nonneg_right
          (sqrt_div_sq_mul_le
            (mul_nonneg hQ (Real.rpow_nonneg T.property.le _)) hB hKreal
            hB.le le_rfl) hzSeven
  have hscale : 0 ≤ heathBrownSquareDivisorScale N' eta := by
    rw [heathBrownSquareDivisorScale]
    exact mul_nonneg (divisorBoundConst_pos heta).le
      (Real.rpow_nonneg (by positivity) _)
  rw [mtTypeIPrimeRaisedHeathBrownLayerRootBound,
    mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound]
  change Real.sqrt (heathBrownLemma34Coefficient eta) *
      heathBrownSquareDivisorScale N' eta *
        (L / B +
          Real.sqrt (Q * (T : ℝ) / (B ^ 2 * (K : ℝ))) *
            F ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) +
          Real.sqrt (Q * (T : ℝ) ^ (3 / 4 : ℝ) / (B ^ 2 * (K : ℝ))) *
            F ^ (1 / 8 : ℝ) * L ^ (7 / 8 : ℝ)) ≤ _
  have hinner :
      L / B +
          Real.sqrt (Q * (T : ℝ) / (B ^ 2 * (K : ℝ))) *
            F ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) +
          Real.sqrt (Q * (T : ℝ) ^ (3 / 4 : ℝ) / (B ^ 2 * (K : ℝ))) *
            F ^ (1 / 8 : ℝ) * L ^ (7 / 8 : ℝ) ≤
        L / M + Real.sqrt (Q * (T : ℝ) / (K : ℝ)) * zHalf +
          Real.sqrt (Q * (T : ℝ) ^ (3 / 4 : ℝ) / (K : ℝ)) * zSeven := by
    calc
      _ = L / B +
          Real.sqrt (Q * (T : ℝ) / (B ^ 2 * (K : ℝ))) *
            (F ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) +
          Real.sqrt (Q * (T : ℝ) ^ (3 / 4 : ℝ) / (B ^ 2 * (K : ℝ))) *
            (F ^ (1 / 8 : ℝ) * L ^ (7 / 8 : ℝ)) := by ring
      _ ≤ _ := add_le_add (add_le_add hfirst hsecond) hthird
  exact mul_le_mul_of_nonneg_left hinner
    (mul_nonneg (Real.sqrt_nonneg _) hscale)

end

end RHTower.Sieve
