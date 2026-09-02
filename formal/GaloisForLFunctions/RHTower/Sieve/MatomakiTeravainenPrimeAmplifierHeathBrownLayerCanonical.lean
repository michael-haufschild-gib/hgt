import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerReceiver
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownCanonicalMoment

/-!
# Canonical powered-block collapse of the Heath--Brown layer root

On a literal block `B = P^ell * 2^r`, the exact layer mass is `P^ell`.  The elementary bound
`ell! ≤ ell^ell ≤ P^ell` therefore makes both fractional layer moments at most `B`, cancelling
the full powered-block denominator retained by the layer-cake argument.
-/

namespace RHTower.Sieve

noncomputable section

/-- Root envelope after exact cancellation of the canonical powered-block denominator. -/
def mtTypeIPrimeRaisedHeathBrownLayerCanonicalRootBound
    (N' K : ℕ) (T eta : ℝ) : ℝ :=
  Real.sqrt (heathBrownLemma34Coefficient eta) *
    heathBrownSquareDivisorScale N' eta *
    (1 +
      Real.sqrt ((((K : ℝ) * T) ^ eta) * T / (K : ℝ)) +
      Real.sqrt ((((K : ℝ) * T) ^ eta) * T ^ (3 / 4 : ℝ) / (K : ℝ)))

theorem sqrt_div_sq_mul_le
    {x b k y : ℝ} (hx : 0 ≤ x) (hb : 0 < b) (hk : 0 < k)
    (hy0 : 0 ≤ y) (hy : y ≤ b) :
    Real.sqrt (x / (b ^ 2 * k)) * y ≤ Real.sqrt (x / k) := by
  have hden : 0 < b ^ 2 * k := by positivity
  have hleftArg : 0 ≤ x / (b ^ 2 * k) := div_nonneg hx hden.le
  have hrightArg : 0 ≤ x / k := div_nonneg hx hk.le
  have hysq : y ^ 2 ≤ b ^ 2 := by nlinarith
  have hsquare :
      (Real.sqrt (x / (b ^ 2 * k)) * y) ^ 2 ≤
        (Real.sqrt (x / k)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hleftArg, Real.sq_sqrt hrightArg]
    calc
      x / (b ^ 2 * k) * y ^ 2 ≤ x / (b ^ 2 * k) * b ^ 2 := by gcongr
      _ = x / k := by field_simp
  have hleft : 0 ≤ Real.sqrt (x / (b ^ 2 * k)) * y := by positivity
  have hright : 0 ≤ Real.sqrt (x / k) := Real.sqrt_nonneg _
  nlinarith

/-- Each literal powered-prime block is bounded by the same denominator-free canonical root. -/
theorem mtTypeIPrimeRaisedHeathBrownLayerRootBound_le_canonical
    {P ell K : ℕ} (hP : 1 ≤ P) (hellP : ell ≤ P) (hK : 1 ≤ K)
    (N' : ℕ) (T : Set.Ioi (0 : ℝ)) {eta : ℝ} (heta : 0 < eta)
    (r : Fin ell) :
    mtTypeIPrimeRaisedHeathBrownLayerRootBound P ell
        (mtTypeIPrimeHeathBrownBlockLength P ell r) N' K (T : ℝ) eta ≤
      mtTypeIPrimeRaisedHeathBrownLayerCanonicalRootBound N' K (T : ℝ) eta := by
  let M : ℝ := ((P ^ ell : ℕ) : ℝ)
  let L : ℝ := (((mtTypeIPrimeCoeffSupport P).card ^ ell : ℕ) : ℝ)
  let B : ℝ := (mtTypeIPrimeHeathBrownBlockLength P ell r : ℝ)
  let F : ℝ := (ell.factorial : ℝ)
  let Q : ℝ := (((K : ℝ) * (T : ℝ)) ^ eta)
  have hPpos : 0 < P := Nat.zero_lt_of_lt hP
  have hM : 0 < M := by
    dsimp only [M]
    positivity
  have hB : 0 < B := by
    dsimp only [B, mtTypeIPrimeHeathBrownBlockLength]
    positivity
  have hKreal : (0 : ℝ) < K := by exact_mod_cast (Nat.zero_lt_of_lt hK)
  have hMB : M ≤ B := by
    have hMBNat : P ^ ell ≤ P ^ ell * 2 ^ (r : ℕ) := by
      exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
    dsimp only [M, B, mtTypeIPrimeHeathBrownBlockLength]
    exact_mod_cast hMBNat
  have hfacNat : ell.factorial ≤ P ^ ell := by
    exact (nat_factorial_le_self_pow ell).trans
      (Nat.pow_le_pow_left hellP ell)
  have hFM : F ≤ M := by
    dsimp only [F, M]
    exact_mod_cast hfacNat
  have hLM : L ≤ M := by
    dsimp only [L, M]
    exact_mod_cast Nat.pow_le_pow_left (card_mtTypeIPrimeCoeffSupport_le P) ell
  have hF0 : 0 ≤ F := by positivity
  have hL0 : 0 ≤ L := by positivity
  have hM0 : 0 ≤ M := hM.le
  have hhalf : F ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) ≤ B := by
    calc
      F ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) ≤
          M ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by
        gcongr
      _ = M := by
        rw [← Real.rpow_add hM]
        norm_num
      _ ≤ B := hMB
  have hseven : F ^ (1 / 8 : ℝ) * L ^ (7 / 8 : ℝ) ≤ B := by
    calc
      F ^ (1 / 8 : ℝ) * L ^ (7 / 8 : ℝ) ≤
          M ^ (1 / 8 : ℝ) * M ^ (7 / 8 : ℝ) := by
        gcongr
      _ = M := by
        rw [← Real.rpow_add hM]
        norm_num
      _ ≤ B := hMB
  have hQ : 0 ≤ Q := Real.rpow_nonneg (mul_nonneg hKreal.le T.property.le) _
  have hfirst : L / B ≤ 1 := (div_le_one hB).2 (hLM.trans hMB)
  have hsecond :
      Real.sqrt (Q * (T : ℝ) / (B ^ 2 * (K : ℝ))) *
          (F ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) ≤
        Real.sqrt (Q * (T : ℝ) / (K : ℝ)) :=
    sqrt_div_sq_mul_le (mul_nonneg hQ T.property.le) hB hKreal
      (mul_nonneg (Real.rpow_nonneg hF0 _) (Real.rpow_nonneg hL0 _)) hhalf
  have hthird :
      Real.sqrt (Q * (T : ℝ) ^ (3 / 4 : ℝ) / (B ^ 2 * (K : ℝ))) *
          (F ^ (1 / 8 : ℝ) * L ^ (7 / 8 : ℝ)) ≤
        Real.sqrt (Q * (T : ℝ) ^ (3 / 4 : ℝ) / (K : ℝ)) :=
    sqrt_div_sq_mul_le
      (mul_nonneg hQ (Real.rpow_nonneg T.property.le _)) hB hKreal
      (mul_nonneg (Real.rpow_nonneg hF0 _) (Real.rpow_nonneg hL0 _)) hseven
  have hscale : 0 ≤ heathBrownSquareDivisorScale N' eta := by
    rw [heathBrownSquareDivisorScale]
    exact mul_nonneg (divisorBoundConst_pos heta).le
      (Real.rpow_nonneg (by positivity) _)
  rw [mtTypeIPrimeRaisedHeathBrownLayerRootBound,
    mtTypeIPrimeRaisedHeathBrownLayerCanonicalRootBound]
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
        1 + Real.sqrt (Q * (T : ℝ) / (K : ℝ)) +
          Real.sqrt (Q * (T : ℝ) ^ (3 / 4 : ℝ) / (K : ℝ)) := by
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
