import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownLayerMoment
import GaloisForLFunctions.HTGeometry.RankEnergyPowerSum

/-!
# Scalar collapse of the powered-prime Heath--Brown layer moment

Finite Jensen collapses the threshold layers at exponents `1/2` and `7/8`.  Their total
cardinality is the exact coefficient mass, at most `P^ell`, while their number is only `ell!`.
The resulting bound retains every `B^2` denominator from Lemma 3.4.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

private theorem sqrt_three_term_le
    {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (x + y + z) ≤ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
  have hsum : 0 ≤ x + y + z := by positivity
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have hsz := Real.sq_sqrt hz
  have hsxyz := Real.sq_sqrt hsum
  have hxy : 0 ≤ Real.sqrt x * Real.sqrt y := by positivity
  have hxz : 0 ≤ Real.sqrt x * Real.sqrt z := by positivity
  have hyz : 0 ≤ Real.sqrt y * Real.sqrt z := by positivity
  have hrhs : 0 ≤ Real.sqrt x + Real.sqrt y + Real.sqrt z := by positivity
  have hlhs := Real.sqrt_nonneg (x + y + z)
  nlinarith [sq_nonneg
    (Real.sqrt (x + y + z) - (Real.sqrt x + Real.sqrt y + Real.sqrt z))]

private theorem sqrt_rpow_eq_rpow_half
    {x p : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x ^ p) = x ^ (p / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

/-- Finite Jensen for all threshold-layer cardinalities, retaining the exact ordered-prime tuple
mass. -/
theorem sum_card_mtTypeIPrimeRaisedBlockLayer_rpow_le_primeMass
    (P ell B : ℕ) {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) :
    ∑ j ∈ Finset.range ell.factorial,
        ((mtTypeIPrimeRaisedBlockLayer P ell B j).card : ℝ) ^ k ≤
      (ell.factorial : ℝ) ^ (1 - k) *
        (((mtTypeIPrimeCoeffSupport P).card ^ ell : ℕ) : ℝ) ^ k := by
  let s := Finset.range ell.factorial
  let a : ℕ → ℝ := fun j =>
    ((mtTypeIPrimeRaisedBlockLayer P ell B j).card : ℝ)
  have ha : ∀ j ∈ s, 0 ≤ a j := by
    intro j hj
    positivity
  have hs : s.Nonempty := by
    refine ⟨0, ?_⟩
    simpa only [s, Finset.mem_range] using Nat.factorial_pos ell
  have hjensen :=
    GaloisForLFunctions.HTGeometry.sum_rpow_le_card_rpow_mul_sum_rpow
      s a ha hk hk1 hs
  have hmassNat :
      ∑ j ∈ Finset.range ell.factorial,
          (mtTypeIPrimeRaisedBlockLayer P ell B j).card ≤
        (mtTypeIPrimeCoeffSupport P).card ^ ell := by
    rw [sum_card_mtTypeIPrimeRaisedBlockLayer_eq]
    exact sum_mtTypeIPrimeRaisedBlockMultiplicity_le_card_pow P ell B
  have hmass :
      (∑ j ∈ s, a j) ≤
        (((mtTypeIPrimeCoeffSupport P).card ^ ell : ℕ) : ℝ) := by
    have hmass' :
        (∑ j ∈ Finset.range ell.factorial,
            ((mtTypeIPrimeRaisedBlockLayer P ell B j).card : ℝ)) ≤
          (((mtTypeIPrimeCoeffSupport P).card ^ ell : ℕ) : ℝ) := by
      exact_mod_cast hmassNat
    simpa only [s, a] using hmass'
  have hsum0 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg ha
  have hpow := Real.rpow_le_rpow hsum0 hmass hk.le
  have hfac0 : 0 ≤ (ell.factorial : ℝ) := by positivity
  change (∑ j ∈ s, a j ^ k) ≤ _
  have hjensen' :
      (∑ j ∈ s, a j ^ k) ≤
        (ell.factorial : ℝ) ^ (1 - k) * (∑ j ∈ s, a j) ^ k := by
    simpa only [s, a, Finset.card_range, div_one, Real.rpow_one] using hjensen
  exact hjensen'.trans (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hfac0 _))

/-- Coarse paper-length form of threshold-layer Jensen. -/
theorem sum_card_mtTypeIPrimeRaisedBlockLayer_rpow_le
    (P ell B : ℕ) {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) :
    ∑ j ∈ Finset.range ell.factorial,
        ((mtTypeIPrimeRaisedBlockLayer P ell B j).card : ℝ) ^ k ≤
      (ell.factorial : ℝ) ^ (1 - k) * (((P ^ ell : ℕ) : ℝ)) ^ k := by
  have hsharp := sum_card_mtTypeIPrimeRaisedBlockLayer_rpow_le_primeMass
    P ell B hk hk1
  have hmassNat : (mtTypeIPrimeCoeffSupport P).card ^ ell ≤ P ^ ell :=
    Nat.pow_le_pow_left (card_mtTypeIPrimeCoeffSupport_le P) ell
  have hmass :
      (((mtTypeIPrimeCoeffSupport P).card ^ ell : ℕ) : ℝ) ≤
        (((P ^ ell : ℕ) : ℝ)) := by
    exact_mod_cast hmassNat
  have hpow := Real.rpow_le_rpow (by positivity) hmass hk.le
  exact hsharp.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

/-- Closed root envelope for all coefficient layers against one dense dyadic block. -/
def mtTypeIPrimeRaisedHeathBrownLayerRootBound
    (P ell B N' K : ℕ) (T eta : ℝ) : ℝ :=
  let L : ℝ := (((mtTypeIPrimeCoeffSupport P).card ^ ell : ℕ) : ℝ)
  Real.sqrt (heathBrownLemma34Coefficient eta) *
    heathBrownSquareDivisorScale N' eta *
    ((L / (B : ℝ)) +
      Real.sqrt ((((K : ℝ) * T) ^ eta) * T /
          ((B : ℝ) ^ 2 * (K : ℝ))) *
        (ell.factorial : ℝ) ^ (1 / 2 : ℝ) *
        L ^ (1 / 2 : ℝ) +
      Real.sqrt ((((K : ℝ) * T) ^ eta) * T ^ (3 / 4 : ℝ) /
          ((B : ℝ) ^ 2 * (K : ℝ))) *
        (ell.factorial : ℝ) ^ (1 / 8 : ℝ) *
        L ^ (7 / 8 : ℝ))

/-- The scalar root envelope is nonnegative. -/
theorem mtTypeIPrimeRaisedHeathBrownLayerRootBound_nonneg
    (P ell B N' K : ℕ) (T : ℝ) {eta : ℝ} (heta : 0 < eta) :
    0 ≤ mtTypeIPrimeRaisedHeathBrownLayerRootBound P ell B N' K T eta := by
  rw [mtTypeIPrimeRaisedHeathBrownLayerRootBound]
  have hscale : 0 ≤ heathBrownSquareDivisorScale N' eta := by
    rw [heathBrownSquareDivisorScale]
    exact mul_nonneg (divisorBoundConst_pos heta).le
      (Real.rpow_nonneg (by positivity) _)
  positivity

private theorem sqrt_mtTypeIPrimeRaisedHeathBrownLayerPieceBound_le
    (P ell B N' K j : ℕ) (hB : 1 ≤ B) (hK : 1 ≤ K)
    (T : Set.Ioi (0 : ℝ)) {eta : ℝ} (heta : 0 < eta) :
    Real.sqrt (mtTypeIPrimeRaisedHeathBrownLayerPieceBound
      P ell B N' K j (T : ℝ) eta) ≤
      Real.sqrt (heathBrownLemma34Coefficient eta) *
        heathBrownSquareDivisorScale N' eta *
        ((((mtTypeIPrimeRaisedBlockLayer P ell B j).card : ℝ) / (B : ℝ)) +
          Real.sqrt ((((K : ℝ) * (T : ℝ)) ^ eta) * (T : ℝ) /
              ((B : ℝ) ^ 2 * (K : ℝ))) *
            ((mtTypeIPrimeRaisedBlockLayer P ell B j).card : ℝ) ^ (1 / 2 : ℝ) +
          Real.sqrt ((((K : ℝ) * (T : ℝ)) ^ eta) *
              (T : ℝ) ^ (3 / 4 : ℝ) /
              ((B : ℝ) ^ 2 * (K : ℝ))) *
            ((mtTypeIPrimeRaisedBlockLayer P ell B j).card : ℝ) ^ (7 / 8 : ℝ)) := by
  let C := heathBrownLemma34Coefficient eta
  let D := heathBrownSquareDivisorScale N' eta
  let R : ℝ := ((mtTypeIPrimeRaisedBlockLayer P ell B j).card : ℝ)
  let Q : ℝ := (((K : ℝ) * (T : ℝ)) ^ eta)
  let den : ℝ := (B : ℝ) ^ 2 * (K : ℝ)
  let u : ℝ := R / (B : ℝ)
  let v : ℝ := Q * (T : ℝ) / den
  let w : ℝ := Q * (T : ℝ) ^ (3 / 4 : ℝ) / den
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hC : 0 ≤ C := by
    have hdiv : 0 < divisorBoundConst (eta / 4) := divisorBoundConst_pos (by linarith)
    simp only [C]
    rw [heathBrownLemma34Coefficient, heathBrownLemma34PositiveCoefficient,
      heathBrownTheoremFourCoefficient, heathBrownTheoremFourUniversalCoefficient,
      heathBrownMeanSquareCoefficient]
    positivity
  have hD : 0 ≤ D := by
    simp only [D, heathBrownSquareDivisorScale]
    exact mul_nonneg (divisorBoundConst_pos heta).le
      (Real.rpow_nonneg (by positivity) _)
  have hR : 0 ≤ R := by positivity
  have hQ : 0 ≤ Q := Real.rpow_nonneg (mul_nonneg hKpos.le T.property.le) _
  have hden : 0 < den := by dsimp only [den]; positivity
  have hu : 0 ≤ u := div_nonneg hR hBpos.le
  have hv : 0 ≤ v := div_nonneg (mul_nonneg hQ T.property.le) hden.le
  have hw : 0 ≤ w := div_nonneg
    (mul_nonneg hQ (Real.rpow_nonneg T.property.le _)) hden.le
  have hR74 : 0 ≤ R ^ (7 / 4 : ℝ) := Real.rpow_nonneg hR _
  have hsplit := sqrt_three_term_le (sq_nonneg u)
    (mul_nonneg hv hR) (mul_nonneg hw hR74)
  have hrootR : Real.sqrt R = R ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow R
  have hrootR74 : Real.sqrt (R ^ (7 / 4 : ℝ)) = R ^ (7 / 8 : ℝ) := by
    rw [sqrt_rpow_eq_rpow_half hR]
    norm_num
  have hinner :
      Real.sqrt (u ^ 2 + v * R + w * R ^ (7 / 4 : ℝ)) ≤
        u + Real.sqrt v * R ^ (1 / 2 : ℝ) +
          Real.sqrt w * R ^ (7 / 8 : ℝ) := by
    calc
      _ ≤ Real.sqrt (u ^ 2) + Real.sqrt (v * R) +
          Real.sqrt (w * R ^ (7 / 4 : ℝ)) := hsplit
      _ = u + Real.sqrt v * R ^ (1 / 2 : ℝ) +
          Real.sqrt w * R ^ (7 / 8 : ℝ) := by
        rw [Real.sqrt_sq hu, Real.sqrt_mul hv, Real.sqrt_mul hw, hrootR, hrootR74]
  have hfactor :
      Real.sqrt (C * D ^ 2 *
          (u ^ 2 + v * R + w * R ^ (7 / 4 : ℝ))) =
        Real.sqrt C * D *
          Real.sqrt (u ^ 2 + v * R + w * R ^ (7 / 4 : ℝ)) := by
    rw [show C * D ^ 2 *
        (u ^ 2 + v * R + w * R ^ (7 / 4 : ℝ)) =
          C * (D ^ 2 * (u ^ 2 + v * R + w * R ^ (7 / 4 : ℝ))) by ring,
      Real.sqrt_mul hC, Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD]
    ring
  have hshape :
      mtTypeIPrimeRaisedHeathBrownLayerPieceBound
          P ell B N' K j (T : ℝ) eta =
        C * D ^ 2 * (u ^ 2 + v * R + w * R ^ (7 / 4 : ℝ)) := by
    rw [mtTypeIPrimeRaisedHeathBrownLayerPieceBound]
    dsimp only [C, D, R, Q, den, u, v, w]
    ring
  rw [hshape]
  rw [hfactor]
  change Real.sqrt C * D *
      Real.sqrt (u ^ 2 + v * R + w * R ^ (7 / 4 : ℝ)) ≤
    Real.sqrt C * D *
      (u + Real.sqrt v * R ^ (1 / 2 : ℝ) + Real.sqrt w * R ^ (7 / 8 : ℝ))
  exact mul_le_mul_of_nonneg_left hinner (mul_nonneg (Real.sqrt_nonneg C) hD)

/-- All unit threshold layers collapse to the exact coefficient mass and the factorial layer
count, without losing the powered-block denominator. -/
theorem sum_sqrt_mtTypeIPrimeRaisedHeathBrownLayerPieceBound_le
    (P ell B N' K : ℕ) (hB : 1 ≤ B) (hK : 1 ≤ K)
    (T : Set.Ioi (0 : ℝ)) {eta : ℝ} (heta : 0 < eta) :
    ∑ j ∈ Finset.range ell.factorial,
        Real.sqrt (mtTypeIPrimeRaisedHeathBrownLayerPieceBound
          P ell B N' K j (T : ℝ) eta) ≤
      mtTypeIPrimeRaisedHeathBrownLayerRootBound
        P ell B N' K (T : ℝ) eta := by
  let s := Finset.range ell.factorial
  let R : ℕ → ℝ := fun j =>
    ((mtTypeIPrimeRaisedBlockLayer P ell B j).card : ℝ)
  let L : ℝ := (((mtTypeIPrimeCoeffSupport P).card ^ ell : ℕ) : ℝ)
  let Croot := Real.sqrt (heathBrownLemma34Coefficient eta) *
    heathBrownSquareDivisorScale N' eta
  let v := Real.sqrt ((((K : ℝ) * (T : ℝ)) ^ eta) * (T : ℝ) /
    ((B : ℝ) ^ 2 * (K : ℝ)))
  let w := Real.sqrt ((((K : ℝ) * (T : ℝ)) ^ eta) *
    (T : ℝ) ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)))
  have hCroot : 0 ≤ Croot := by
    dsimp only [Croot]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (by
        rw [heathBrownSquareDivisorScale]
        exact mul_nonneg (divisorBoundConst_pos heta).le
          (Real.rpow_nonneg (by positivity) _))
  have hterm : ∀ j ∈ s,
      Real.sqrt (mtTypeIPrimeRaisedHeathBrownLayerPieceBound
        P ell B N' K j (T : ℝ) eta) ≤
        Croot * (R j / (B : ℝ) + v * R j ^ (1 / 2 : ℝ) +
          w * R j ^ (7 / 8 : ℝ)) := by
    intro j hj
    exact sqrt_mtTypeIPrimeRaisedHeathBrownLayerPieceBound_le
      P ell B N' K j hB hK T heta
  have hmassNat :
      ∑ j ∈ Finset.range ell.factorial,
          (mtTypeIPrimeRaisedBlockLayer P ell B j).card ≤
        (mtTypeIPrimeCoeffSupport P).card ^ ell := by
    rw [sum_card_mtTypeIPrimeRaisedBlockLayer_eq]
    exact sum_mtTypeIPrimeRaisedBlockMultiplicity_le_card_pow P ell B
  have hmass : (∑ j ∈ s, R j) ≤ L := by
    have hmass' :
        (∑ j ∈ Finset.range ell.factorial,
          ((mtTypeIPrimeRaisedBlockLayer P ell B j).card : ℝ)) ≤
            (((mtTypeIPrimeCoeffSupport P).card ^ ell : ℕ) : ℝ) := by
      exact_mod_cast hmassNat
    simpa only [s, R, L] using hmass'
  have hhalf := sum_card_mtTypeIPrimeRaisedBlockLayer_rpow_le_primeMass
    P ell B (k := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hseven := sum_card_mtTypeIPrimeRaisedBlockLayer_rpow_le_primeMass
    P ell B (k := (7 / 8 : ℝ)) (by norm_num) (by norm_num)
  have hhalf' :
      (∑ j ∈ s, R j ^ (1 / 2 : ℝ)) ≤
        (ell.factorial : ℝ) ^ (1 / 2 : ℝ) *
          L ^ (1 / 2 : ℝ) := by
    simpa only [s, R, L] using (by norm_num at hhalf ⊢; exact hhalf)
  have hseven' :
      (∑ j ∈ s, R j ^ (7 / 8 : ℝ)) ≤
        (ell.factorial : ℝ) ^ (1 / 8 : ℝ) *
          L ^ (7 / 8 : ℝ) := by
    simpa only [s, R, L] using (by norm_num at hseven ⊢; exact hseven)
  have hsum := Finset.sum_le_sum hterm
  change (∑ j ∈ s, Real.sqrt (mtTypeIPrimeRaisedHeathBrownLayerPieceBound
    P ell B N' K j (T : ℝ) eta)) ≤ _
  calc
    _ ≤ ∑ j ∈ s,
        Croot * (R j / (B : ℝ) + v * R j ^ (1 / 2 : ℝ) +
          w * R j ^ (7 / 8 : ℝ)) := hsum
    _ = Croot *
        ((∑ j ∈ s, R j) / (B : ℝ) +
          v * (∑ j ∈ s, R j ^ (1 / 2 : ℝ)) +
          w * (∑ j ∈ s, R j ^ (7 / 8 : ℝ))) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ Croot *
        (L / (B : ℝ) +
          v * ((ell.factorial : ℝ) ^ (1 / 2 : ℝ) *
            L ^ (1 / 2 : ℝ)) +
          w * ((ell.factorial : ℝ) ^ (1 / 8 : ℝ) *
            L ^ (7 / 8 : ℝ))) := by
      gcongr
    _ = mtTypeIPrimeRaisedHeathBrownLayerRootBound
        P ell B N' K (T : ℝ) eta := by
      rw [mtTypeIPrimeRaisedHeathBrownLayerRootBound]
      dsimp only [Croot, v, w, L]
      ring

/-- Full squared-unit-block moment with the two exact scalar root envelopes. -/
theorem integral_Icc_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le_layerRootBounds_sq
    (P ell : ℕ) {B N N' : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N)
    (hN' : 1 ≤ N') (hN'le : N' ≤ 2 * N)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t *
          (mtWattUnitBlock N N' t) ^ 2‖ ^ 2) ≤
      (mtTypeIPrimeRaisedHeathBrownLayerRootBound
          P ell B N' (N * N) (T : ℝ) eta +
        mtTypeIPrimeRaisedHeathBrownLayerRootBound
          P ell B N' (2 * (N * N)) (T : ℝ) eta) ^ 2 := by
  have hbase :=
    integral_Icc_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le_layerSums_sq
      P ell hB hN hN' hN'le T hBT heta
  have hlow := sum_sqrt_mtTypeIPrimeRaisedHeathBrownLayerPieceBound_le
    P ell B N' (N * N) hB (by nlinarith) T heta
  have hhigh := sum_sqrt_mtTypeIPrimeRaisedHeathBrownLayerPieceBound_le
    P ell B N' (2 * (N * N)) hB (by
      have hNN1 : 1 ≤ N * N := by nlinarith
      omega) T heta
  have hsum0 : 0 ≤
      (∑ j ∈ Finset.range ell.factorial,
        Real.sqrt (mtTypeIPrimeRaisedHeathBrownLayerPieceBound
          P ell B N' (N * N) j (T : ℝ) eta)) +
      ∑ j ∈ Finset.range ell.factorial,
        Real.sqrt (mtTypeIPrimeRaisedHeathBrownLayerPieceBound
          P ell B N' (2 * (N * N)) j (T : ℝ) eta) := by positivity
  have hsum := add_le_add hlow hhigh
  exact hbase.trans (pow_le_pow_left₀ hsum0 hsum 2)

end

end RHTower.Sieve
