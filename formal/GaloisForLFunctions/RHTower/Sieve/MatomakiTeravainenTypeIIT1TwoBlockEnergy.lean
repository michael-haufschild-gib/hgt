import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRealFinsetHalaszMontgomery
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRaisedLemma41Energy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRaisedAmplitudeCell
import GaloisForLFunctions.RHTower.Sieve.MaynardHuxleySchedule
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenUnraisedPolylogEnergy
import GaloisForLFunctions.RHTower.Sieve.HuxleyClosedLargeValues

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

noncomputable section

theorem matomakiTeravainen_typeII_T1_two_block_energy_of_raw_mass
    (N A : ℕ) (hA : 1 ≤ A) (a : Fin N → ℂ)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (henergy : ∑ j : Fin (N ^ 1), ‖convPow N 1 a j‖ ^ 2 ≤ Q * (A : ℝ))
    {S : Finset ℝ} {H B : ℝ} (hH : 0 ≤ H)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ H)
    (hheight : ∀ r : Fin 2,
      H ≤ 8 * Real.pi * ((A * 2 ^ (r : ℕ) : ℕ) : ℝ) ^ 2)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    (F : ℝ → ℝ) (hF0 : ∀ t ∈ S, 0 ≤ F t) (hF : ∀ t ∈ S, F t ≤ B) :
    ∑ t ∈ S, F t ^ 2 * matomakiTeravainenDirichletAmplitude N a t ^ 2 ≤
      2 * B ^ 2 * (∑ r : Fin 2,
        (((A * 2 ^ (r : ℕ) : ℕ) : ℝ) +
            12 * Real.pi * ((A * 2 ^ (r : ℕ) : ℕ) : ℝ) *
              (1 + Real.log S.card) +
            (S.card : ℝ) *
              (1 + 214 * Real.sqrt H +
                1536 * (((A * 2 ^ (r : ℕ) : ℕ) : ℝ) /
                  Real.sqrt (maynardHuxleyU (A * 2 ^ (r : ℕ)))))) *
          (Q / ((A * 2 ^ (r : ℕ) : ℕ) : ℝ))) := by
  let D : Fin 2 → ℕ := fun r => A ^ 1 * 2 ^ (r : ℕ)
  have hD : ∀ r, 1 ≤ D r := by
    intro r
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by norm_num)))
  have hblock : ∀ r : Fin 2,
      ∑ t ∈ S, F t ^ 2 *
          ‖blockPoly (D r) (anchoredCoeff (N ^ 1) (convPow N 1 a)) 1 t‖ ^ 2 ≤
        B ^ 2 *
          ((((D r : ℕ) : ℝ) + 12 * Real.pi * ((D r : ℕ) : ℝ) *
              (1 + Real.log S.card) +
              (S.card : ℝ) *
                (1 + 214 * Real.sqrt H +
                  1536 * (((D r : ℕ) : ℝ) / Real.sqrt (maynardHuxleyU (D r))))) *
            (Q / ((D r : ℕ) : ℝ))) := by
    intro r
    have hmass := raised_dyadic_block_mass_le_of_raw_energy hA a hQ
      (by simpa only [pow_one] using henergy) r
    have hreceiver := matomakiTeravainen_typeII_T1_real_finset_energy_of_mass
      (D r) (hD r) (anchoredCoeff (N ^ 1) (convPow N 1 a))
      (S := S) (delta := 1) (U := maynardHuxleyU (D r)) (T := H)
      (A := B) (G := Q / (D r : ℝ))
      (by norm_num) (maynardHuxleyU_pos (hD r)) hH hsep hspread
      maynardHuxleyU_near (logDyadicLambda_le_one_of_height_le (hD r)
        (by simpa only [D, pow_one] using hheight r))
      F hF0 hF
      (by simpa only [D, blockCoeff, dyadicWeightedCoeff] using hmass)
    simpa only [D, div_one] using hreceiver
  have hpoint : ∀ t ∈ S,
      F t ^ 2 * matomakiTeravainenDirichletAmplitude N a t ^ 2 ≤
        2 * ∑ r : Fin 2, F t ^ 2 *
          ‖blockPoly (D r) (anchoredCoeff (N ^ 1) (convPow N 1 a)) 1 t‖ ^ 2 := by
    intro t ht
    have hnorm := norm_raisedDirichletValue_le_sum_dyadic hA a
      hsupp 1 t (ℓ := 1)
    have hnorm' : matomakiTeravainenDirichletAmplitude N a t ≤
        ∑ r : Fin 2,
          ‖blockPoly (D r) (anchoredCoeff (N ^ 1) (convPow N 1 a)) 1 t‖ := by
      simpa only [matomakiTeravainenDirichletAmplitude, raisedDirichletValue_eq_pow,
        pow_one, D, blockPoly, inner_dyadicDirRow_dyadicWeightedCoeff,
        anchoredDirichletTerm] using hnorm
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm' 2
    have hcs :
        (∑ r : Fin 2,
          ‖blockPoly (D r) (anchoredCoeff (N ^ 1) (convPow N 1 a)) 1 t‖) ^ 2 ≤
          2 * ∑ r : Fin 2,
            ‖blockPoly (D r) (anchoredCoeff (N ^ 1) (convPow N 1 a)) 1 t‖ ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin 2)))
        (f := fun r =>
          ‖blockPoly (D r) (anchoredCoeff (N ^ 1) (convPow N 1 a)) 1 t‖))
    have hF2 : 0 ≤ F t ^ 2 := sq_nonneg _
    calc
      F t ^ 2 * matomakiTeravainenDirichletAmplitude N a t ^ 2
          ≤ F t ^ 2 *
              (∑ r : Fin 2,
                ‖blockPoly (D r) (anchoredCoeff (N ^ 1) (convPow N 1 a)) 1 t‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hF2
      _ ≤ F t ^ 2 *
          (2 * ∑ r : Fin 2,
            ‖blockPoly (D r) (anchoredCoeff (N ^ 1) (convPow N 1 a)) 1 t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcs hF2
      _ = 2 * ∑ r : Fin 2, F t ^ 2 *
          ‖blockPoly (D r) (anchoredCoeff (N ^ 1) (convPow N 1 a)) 1 t‖ ^ 2 := by
        rw [← Finset.mul_sum]
        ring
  calc
    ∑ t ∈ S, F t ^ 2 * matomakiTeravainenDirichletAmplitude N a t ^ 2
        ≤ ∑ t ∈ S, 2 * ∑ r : Fin 2, F t ^ 2 *
          ‖blockPoly (D r) (anchoredCoeff (N ^ 1) (convPow N 1 a)) 1 t‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = 2 * ∑ r : Fin 2, ∑ t ∈ S, F t ^ 2 *
          ‖blockPoly (D r) (anchoredCoeff (N ^ 1) (convPow N 1 a)) 1 t‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
    _ ≤ 2 * ∑ r : Fin 2, B ^ 2 *
          ((((D r : ℕ) : ℝ) + 12 * Real.pi * ((D r : ℕ) : ℝ) *
              (1 + Real.log S.card) +
              (S.card : ℝ) *
                (1 + 214 * Real.sqrt H +
                  1536 * (((D r : ℕ) : ℝ) / Real.sqrt (maynardHuxleyU (D r))))) *
            (Q / ((D r : ℕ) : ℝ))) := by
      gcongr with r
      exact hblock r
    _ = _ := by
      simp_rw [D, pow_one, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- The `T^(21 eps)` sparsity of `T₁` makes every normalized Halász--Montgomery off-diagonal
term bounded. The full receiver therefore costs only one logarithm, with no positive power of
the height. -/
theorem matomakiTeravainen_typeII_T1_normalized_halaszMontgomery_envelope
    {eps T Q : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 4000)
    (hT : 1 ≤ T) (hQ : 0 ≤ Q) {D : ℕ} (hD : 1 ≤ D)
    (hDlo : T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ (D : ℝ))
    (S : Finset ℝ) (hcard : (S.card : ℝ) ≤ T ^ (21 * eps)) :
    (((D : ℝ) + 12 * Real.pi * (D : ℝ) * (1 + Real.log S.card) +
        (S.card : ℝ) *
          (1 + 214 * Real.sqrt (2 * T) +
            1536 * ((D : ℝ) / Real.sqrt (maynardHuxleyU D)))) *
      (Q / (D : ℝ))) ≤ 2048 * (1 + |Real.log T|) * Q := by
  let beta : ℝ := (9 : ℝ) / 11 - 10 * eps
  let gamma : ℝ := 21 * eps
  let P : ℝ := 1 + |Real.log T|
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hT0 : 0 ≤ T := hTpos.le
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hP1 : 1 ≤ P := by dsimp only [P]; linarith [abs_nonneg (Real.log T)]
  have hgamma0 : 0 ≤ gamma := by dsimp only [gamma]; positivity
  have hgammaOne : gamma ≤ 1 := by dsimp only [gamma]; linarith
  have hgammaBeta : gamma ≤ beta := by dsimp only [gamma, beta]; linarith
  have hgammaHalfBeta : gamma + 1 / 2 ≤ beta := by
    dsimp only [gamma, beta]
    linarith
  have htwoGammaBeta : 2 * gamma ≤ beta := by
    dsimp only [gamma, beta]
    linarith
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hD0 : (0 : ℝ) ≤ D := hDpos.le
  have hcard0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hcardD : (S.card : ℝ) ≤ (D : ℝ) := by
    calc
      (S.card : ℝ) ≤ T ^ gamma := by simpa only [gamma] using hcard
      _ ≤ T ^ beta := Real.rpow_le_rpow_of_exponent_le hT hgammaBeta
      _ ≤ (D : ℝ) := by simpa only [beta] using hDlo
  have hlogCard : 1 + Real.log S.card ≤ P := by
    by_cases hzero : S.card = 0
    · simp only [hzero, Nat.cast_zero, Real.log_zero, add_zero]
      exact hP1
    · have hcardPos : (0 : ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hzero
      have hlog := Real.log_le_log hcardPos hcard
      rw [Real.log_rpow hTpos] at hlog
      have hgammaLog : gamma * Real.log T ≤ Real.log T := by
        nlinarith
      calc
        1 + Real.log S.card ≤ 1 + gamma * Real.log T := by linarith
        _ ≤ 1 + Real.log T := by linarith
        _ ≤ P := by dsimp only [P]; linarith [le_abs_self (Real.log T)]
  have hcardSqrtT : (S.card : ℝ) * Real.sqrt T ≤ (D : ℝ) := by
    have hsqrt : Real.sqrt T = T ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow T
    calc
      (S.card : ℝ) * Real.sqrt T
          ≤ T ^ gamma * T ^ ((1 : ℝ) / 2) := by
        rw [hsqrt]
        exact mul_le_mul hcard (le_rfl) (Real.rpow_nonneg hT0 _)
          (Real.rpow_nonneg hT0 _)
      _ = T ^ (gamma + 1 / 2) := (Real.rpow_add hTpos gamma (1 / 2)).symm
      _ ≤ T ^ beta := Real.rpow_le_rpow_of_exponent_le hT hgammaHalfBeta
      _ ≤ (D : ℝ) := by simpa only [beta] using hDlo
  have hsqrtTwo : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsqrtTwoT : Real.sqrt (2 * T) ≤ 2 * Real.sqrt T := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right hsqrtTwo (Real.sqrt_nonneg T)
  have hcardSqrtTwoT : (S.card : ℝ) * Real.sqrt (2 * T) ≤ 2 * (D : ℝ) := by
    calc
      (S.card : ℝ) * Real.sqrt (2 * T)
          ≤ (S.card : ℝ) * (2 * Real.sqrt T) :=
        mul_le_mul_of_nonneg_left hsqrtTwoT hcard0
      _ = 2 * ((S.card : ℝ) * Real.sqrt T) := by ring
      _ ≤ 2 * (D : ℝ) := by gcongr
  have hcardSq : (S.card : ℝ) ^ 2 ≤ (D : ℝ) := by
    calc
      (S.card : ℝ) ^ 2 ≤ (T ^ gamma) ^ 2 :=
        pow_le_pow_left₀ hcard0 hcard 2
      _ = T ^ (2 * gamma) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT0]
        congr 1
        ring
      _ ≤ T ^ beta := Real.rpow_le_rpow_of_exponent_le hT htwoGammaBeta
      _ ≤ (D : ℝ) := by simpa only [beta] using hDlo
  have hcardSqrtD : (S.card : ℝ) ≤ Real.sqrt D :=
    (Real.le_sqrt hcard0 hD0).2 hcardSq
  have hsqrtDpos : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
  have htail : (S.card : ℝ) * ((D : ℝ) / Real.sqrt (maynardHuxleyU D)) ≤ (D : ℝ) := by
    have hU : maynardHuxleyU D = (D : ℝ) := rfl
    rw [hU]
    calc
      (S.card : ℝ) * ((D : ℝ) / Real.sqrt D)
          ≤ Real.sqrt D * ((D : ℝ) / Real.sqrt D) :=
        mul_le_mul_of_nonneg_right hcardSqrtD (by positivity)
      _ = (D : ℝ) := by field_simp
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hdiag : (D : ℝ) ≤ P * (D : ℝ) := by nlinarith
  have hlogTerm :
      12 * Real.pi * (D : ℝ) * (1 + Real.log S.card) ≤
        48 * P * (D : ℝ) := by
    have hlog0 : 0 ≤ 1 + Real.log S.card := by
      by_cases hzero : S.card = 0
      · simp [hzero]
      · have hone : (1 : ℝ) ≤ S.card := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hzero
        linarith [Real.log_nonneg hone]
    nlinarith [mul_nonneg hD0 hlog0,
      mul_le_mul_of_nonneg_right hpi (mul_nonneg hD0 hlog0),
      mul_le_mul_of_nonneg_left hlogCard hD0]
  have hcardTerm : (S.card : ℝ) ≤ P * (D : ℝ) := hcardD.trans hdiag
  have hsqrtTerm : 214 * (S.card : ℝ) * Real.sqrt (2 * T) ≤
      428 * P * (D : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hcardSqrtTwoT (by norm_num : (0 : ℝ) ≤ 214)
    nlinarith
  have htailTerm : 1536 * (S.card : ℝ) *
      ((D : ℝ) / Real.sqrt (maynardHuxleyU D)) ≤ 1536 * P * (D : ℝ) := by
    have h := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 1536)
    nlinarith
  have henvelope :
      (D : ℝ) + 12 * Real.pi * (D : ℝ) * (1 + Real.log S.card) +
          (S.card : ℝ) *
            (1 + 214 * Real.sqrt (2 * T) +
              1536 * ((D : ℝ) / Real.sqrt (maynardHuxleyU D))) ≤
        2048 * P * (D : ℝ) := by
    nlinarith
  have hquot0 : 0 ≤ Q / (D : ℝ) := div_nonneg hQ hD0
  calc
    (((D : ℝ) + 12 * Real.pi * (D : ℝ) * (1 + Real.log S.card) +
        (S.card : ℝ) *
          (1 + 214 * Real.sqrt (2 * T) +
            1536 * ((D : ℝ) / Real.sqrt (maynardHuxleyU D)))) *
      (Q / (D : ℝ))) ≤ (2048 * P * (D : ℝ)) * (Q / (D : ℝ)) :=
        mul_le_mul_of_nonneg_right henvelope hquot0
    _ = 2048 * P * Q := by field_simp
    _ = 2048 * (1 + |Real.log T|) * Q := by rfl

/-- Exact two-block `T₁` energy with all Halász--Montgomery receiver tails absorbed. Only the
intrinsic coefficient mass `Q` and one logarithm remain. -/
theorem matomakiTeravainen_typeII_T1_two_block_energy_polylog
    {eps T Q : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 4000)
    (hT : 1 ≤ T) (hQ : 0 ≤ Q)
    (N A : ℕ) (hA : 1 ≤ A) (a : Fin N → ℂ)
    (henergy : ∑ j : Fin (N ^ 1), ‖convPow N 1 a j‖ ^ 2 ≤ Q * (A : ℝ))
    (hAlo : T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ (A : ℝ))
    {S : Finset ℝ}
    (hcard : (S.card : ℝ) ≤ T ^ (21 * eps))
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    (F : ℝ → ℝ) {B : ℝ} (hF0 : ∀ t ∈ S, 0 ≤ F t) (hF : ∀ t ∈ S, F t ≤ B) :
    ∑ t ∈ S, F t ^ 2 * matomakiTeravainenDirichletAmplitude N a t ^ 2 ≤
      8192 * B ^ 2 * (1 + |Real.log T|) * Q := by
  let beta : ℝ := (9 : ℝ) / 11 - 10 * eps
  let D : Fin 2 → ℕ := fun r => A * 2 ^ (r : ℕ)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hT0 : 0 ≤ T := hTpos.le
  have hbetaHalf : (1 : ℝ) / 2 ≤ beta := by
    dsimp only [beta]
    linarith
  have hD : ∀ r, 1 ≤ D r := by
    intro r
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (by omega) (pow_ne_zero _ (by norm_num)))
  have hDlo : ∀ r, T ^ beta ≤ (D r : ℝ) := by
    intro r
    have hAD : (A : ℝ) ≤ (D r : ℝ) := by
      dsimp only [D]
      exact_mod_cast Nat.le_mul_of_pos_right A (pow_pos (by omega) (r : ℕ))
    have hAlo' : T ^ beta ≤ (A : ℝ) := by simpa only [beta] using hAlo
    exact hAlo'.trans hAD
  have hheight : ∀ r : Fin 2,
      2 * T ≤ 8 * Real.pi * ((D r : ℕ) : ℝ) ^ 2 := by
    intro r
    have hTpow : T ≤ T ^ (2 * beta) := by
      have hexp : (1 : ℝ) ≤ 2 * beta := by linarith
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT hexp
    have hpowSq : T ^ (2 * beta) = (T ^ beta) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0]
      congr 1
      ring
    have hTDsq : T ≤ ((D r : ℕ) : ℝ) ^ 2 := by
      calc
        T ≤ T ^ (2 * beta) := hTpow
        _ = (T ^ beta) ^ 2 := hpowSq
        _ ≤ ((D r : ℕ) : ℝ) ^ 2 :=
          pow_le_pow_left₀ (Real.rpow_nonneg hT0 _) (hDlo r) 2
    have hpi : (2 : ℝ) ≤ 8 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith [sq_nonneg ((D r : ℕ) : ℝ)]
  have hbase := matomakiTeravainen_typeII_T1_two_block_energy_of_raw_mass
    N A hA a hQ henergy (S := S) (H := 2 * T) (B := B)
    (by positivity) hsep hspread
    (by intro r; simpa only [D] using hheight r) hsupp F hF0 hF
  have henv : ∀ r : Fin 2,
      ((((D r : ℕ) : ℝ) +
            12 * Real.pi * ((D r : ℕ) : ℝ) * (1 + Real.log S.card) +
            (S.card : ℝ) *
              (1 + 214 * Real.sqrt (2 * T) +
                1536 * (((D r : ℕ) : ℝ) / Real.sqrt (maynardHuxleyU (D r))))) *
          (Q / ((D r : ℕ) : ℝ))) ≤ 2048 * (1 + |Real.log T|) * Q := by
    intro r
    exact matomakiTeravainen_typeII_T1_normalized_halaszMontgomery_envelope
      heps hepss hT hQ (hD r) (by simpa only [beta] using hDlo r) S hcard
  calc
    ∑ t ∈ S, F t ^ 2 * matomakiTeravainenDirichletAmplitude N a t ^ 2
        ≤ 2 * B ^ 2 * ∑ r : Fin 2,
          ((((A * 2 ^ (r : ℕ) : ℕ) : ℝ) +
              12 * Real.pi * ((A * 2 ^ (r : ℕ) : ℕ) : ℝ) *
                (1 + Real.log S.card) +
              (S.card : ℝ) *
                (1 + 214 * Real.sqrt (2 * T) +
                  1536 * (((A * 2 ^ (r : ℕ) : ℕ) : ℝ) /
                    Real.sqrt (maynardHuxleyU (A * 2 ^ (r : ℕ)))))) *
            (Q / ((A * 2 ^ (r : ℕ) : ℕ) : ℝ))) := hbase
    _ ≤ 2 * B ^ 2 * ∑ _r : Fin 2, 2048 * (1 + |Real.log T|) * Q := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun r _hr => by simpa only [D] using henv r
    _ = 8192 * B ^ 2 * (1 + |Real.log T|) * Q := by
      rw [Fin.sum_univ_two]
      ring

/-- Literal divisor-bounded coefficients discharge the remaining intrinsic-mass premise in the
two-block `T₁` estimate. The result is a fixed polylogarithm, not a hidden positive height power. -/
theorem matomakiTeravainen_typeII_T1_unraised_factor_energy_divisor_bounded
    {eps T C : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 4000)
    (hT : 1 ≤ T) (hC : 0 ≤ C)
    (N A w : ℕ) (hN : 1 ≤ N) (hNA : N ≤ 2 * A) (hAT : (A : ℝ) ≤ T)
    (a : Fin N → ℂ)
    (hpoint : ∀ n : Fin N,
      ‖a n‖ ≤ C * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w))
    (hAlo : T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ (A : ℝ))
    {S : Finset ℝ}
    (hcard : (S.card : ℝ) ≤ T ^ (21 * eps))
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    (F : ℝ → ℝ) {B : ℝ} (hF0 : ∀ t ∈ S, 0 ≤ F t) (hF : ∀ t ∈ S, F t ≤ B) :
    ∑ t ∈ S, F t ^ 2 * matomakiTeravainenDirichletAmplitude N a t ^ 2 ≤
      16384 * B ^ 2 * (1 + |Real.log T|) * C ^ 2 *
        (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (w + 1)) - 1) := by
  let Q : ℝ := 2 * C ^ 2 *
    (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (w + 1)) - 1)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have henergy := matomakiTeravainen_unraised_energy_le_polylog
    hT hC hN hNA hAT a hpoint
  have hbase := matomakiTeravainen_typeII_T1_two_block_energy_polylog
    heps hepss hT hQ N A (by omega) a
    (by simpa only [Q] using henergy) hAlo hcard hsep hspread hsupp F hF0 hF
  calc
    ∑ t ∈ S, F t ^ 2 * matomakiTeravainenDirichletAmplitude N a t ^ 2
        ≤ 8192 * B ^ 2 * (1 + |Real.log T|) * Q := hbase
    _ = 16384 * B ^ 2 * (1 + |Real.log T|) * C ^ 2 *
        (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (w + 1)) - 1) := by
      dsimp only [Q]
      ring

/-- Exact two-block Cauchy--Schwarz gives a pointwise square bound from intrinsic raw energy.
This is the coefficient-faithful replacement for an unspecified divisor-bounded pointwise
constant in the elementary `T₃` branch. -/
theorem matomakiTeravainen_dirichletAmplitude_sq_le_four_mul_raw_mass
    (N A : ℕ) (hA : 1 ≤ A) (a : Fin N → ℂ)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (henergy : ∑ j : Fin (N ^ 1), ‖convPow N 1 a j‖ ^ 2 ≤ Q * (A : ℝ))
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    (t : ℝ) :
    matomakiTeravainenDirichletAmplitude N a t ^ 2 ≤ 4 * Q := by
  let D : Fin 2 → ℕ := fun r => A ^ 1 * 2 ^ (r : ℕ)
  have hD : ∀ r, 1 ≤ D r := by
    intro r
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by norm_num)))
  have hblockSq : ∀ r : Fin 2,
      ‖⟪dyadicDirRow (D r) t,
        dyadicWeightedCoeff (N ^ 1) (convPow N 1 a) 1 (D r)⟫_ℂ‖ ^ 2 ≤ Q := by
    intro r
    have hmass := raised_dyadic_block_mass_le_of_raw_energy hA a hQ
      (by simpa only [pow_one] using henergy) r
    have hsq := sq_le_of_large_value
      (dyadicWeightedCoeff (N ^ 1) (convPow N 1 a) 1 (D r))
      (t := t)
      (V := ‖⟪dyadicDirRow (D r) t,
        dyadicWeightedCoeff (N ^ 1) (convPow N 1 a) 1 (D r)⟫_ℂ‖)
      (G := Q / (D r : ℝ)) hmass (le_refl _) (norm_nonneg _)
    calc
      ‖⟪dyadicDirRow (D r) t,
        dyadicWeightedCoeff (N ^ 1) (convPow N 1 a) 1 (D r)⟫_ℂ‖ ^ 2
          ≤ (D r : ℝ) * (Q / (D r : ℝ)) := hsq
      _ = Q := by
        have hDpos : (0 : ℝ) < D r := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hD r))
        field_simp
  have hnorm := norm_raisedDirichletValue_le_sum_dyadic hA a hsupp 1 t (ℓ := 1)
  have hnorm' : matomakiTeravainenDirichletAmplitude N a t ≤
      ∑ r : Fin 2,
        ‖⟪dyadicDirRow (D r) t,
          dyadicWeightedCoeff (N ^ 1) (convPow N 1 a) 1 (D r)⟫_ℂ‖ := by
    simpa only [matomakiTeravainenDirichletAmplitude, raisedDirichletValue_eq_pow,
      pow_one, D] using hnorm
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm' 2
  have hcs :
      (∑ r : Fin 2,
        ‖⟪dyadicDirRow (D r) t,
          dyadicWeightedCoeff (N ^ 1) (convPow N 1 a) 1 (D r)⟫_ℂ‖) ^ 2 ≤
        2 * ∑ r : Fin 2,
          ‖⟪dyadicDirRow (D r) t,
            dyadicWeightedCoeff (N ^ 1) (convPow N 1 a) 1 (D r)⟫_ℂ‖ ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin 2)))
      (f := fun r =>
        ‖⟪dyadicDirRow (D r) t,
          dyadicWeightedCoeff (N ^ 1) (convPow N 1 a) 1 (D r)⟫_ℂ‖))
  calc
    matomakiTeravainenDirichletAmplitude N a t ^ 2
        ≤ (∑ r : Fin 2,
          ‖⟪dyadicDirRow (D r) t,
            dyadicWeightedCoeff (N ^ 1) (convPow N 1 a) 1 (D r)⟫_ℂ‖) ^ 2 := hsq
    _ ≤ 2 * ∑ r : Fin 2,
          ‖⟪dyadicDirRow (D r) t,
            dyadicWeightedCoeff (N ^ 1) (convPow N 1 a) 1 (D r)⟫_ℂ‖ ^ 2 := hcs
    _ ≤ 2 * ∑ _r : Fin 2, Q := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun r _hr => hblockSq r
    _ = 4 * Q := by rw [Fin.sum_univ_two]; ring

/-- Divisor-bounded source data turns the preceding pointwise square bound into an explicit fixed
polylogarithm. -/
theorem matomakiTeravainen_dirichletAmplitude_sq_le_polylog
    {T C : ℝ} (hT : 1 ≤ T) (hC : 0 ≤ C)
    (N A w : ℕ) (hN : 1 ≤ N) (hNA : N ≤ 2 * A) (hAT : (A : ℝ) ≤ T)
    (a : Fin N → ℂ)
    (hpoint : ∀ n : Fin N,
      ‖a n‖ ≤ C * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w))
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    (t : ℝ) :
    matomakiTeravainenDirichletAmplitude N a t ^ 2 ≤
      8 * C ^ 2 *
        (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (w + 1)) - 1) := by
  let Q : ℝ := 2 * C ^ 2 *
    (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (w + 1)) - 1)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have henergy := matomakiTeravainen_unraised_energy_le_polylog
    hT hC hN hNA hAT a hpoint
  have hbase := matomakiTeravainen_dirichletAmplitude_sq_le_four_mul_raw_mass
    N A (by omega) a hQ (by simpa only [Q] using henergy) hsupp t
  calc
    matomakiTeravainenDirichletAmplitude N a t ^ 2 ≤ 4 * Q := hbase
    _ = 8 * C ^ 2 *
        (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (w + 1)) - 1) := by
      dsimp only [Q]
      ring

end

end RHTower.Sieve
