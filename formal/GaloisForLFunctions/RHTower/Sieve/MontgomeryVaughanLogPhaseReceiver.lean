import GaloisForLFunctions.RHTower.Sieve.MontgomeryVaughanConvolutionReceiver
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockAbel

/-!
# Route T logarithmic phase receiver

Specializes the finite Montgomery--Vaughan convolution receiver to the product multiplicities and
height-uniform twisted logarithmic estimate produced by Route T.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

def routeTLogReceiverLength (C : ℕ) : ℕ :=
  (2 * C) ^ routeTLogCentreExponent

def routeTLogReceiverCutoff (C : ℕ) : ℕ :=
  4 * routeTLogReceiverLength C + 1

def routeTLogPhase (t : ℝ) (n : ℕ) : ℂ :=
  finitePhaseChar (t / (2 * Real.pi) * Real.log n)

def routeTLogPhaseIntervalSum (C : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (routeTLogReceiverLength C) (2 * routeTLogReceiverLength C),
    routeTLogPhase t n

def routeTLogPhasePartialIntervalSum (C N' : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (routeTLogReceiverLength C) N', routeTLogPhase t n

def routeTLogWeightedPartialIntervalSum (C N' : ℕ) (σ t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (routeTLogReceiverLength C) N',
    ((((n : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * routeTLogPhase t n

theorem routeTLogPhasePartialIntervalSum_eq_block
    {C N' : ℕ} (hN' : N' ≤ 2 * routeTLogReceiverLength C) (t : ℝ) :
    routeTLogPhasePartialIntervalSum C N' t =
      mvPhaseBlockSum (routeTLogReceiverCutoff C)
        (routeTLogReceiverLength C) N' (routeTLogPhase t) := by
  have hN'K : N' < routeTLogReceiverCutoff C := by
    unfold routeTLogReceiverCutoff
    omega
  unfold routeTLogPhasePartialIntervalSum mvPhaseBlockSum
  rw [Fin.sum_univ_eq_sum_range
    (fun n => routeTLogPhase t n *
      if routeTLogReceiverLength C < n ∧ n ≤ N' then 1 else 0)
    (routeTLogReceiverCutoff C)]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_range]
  change (routeTLogReceiverLength C < n ∧ n ≤ N') ↔
    n < routeTLogReceiverCutoff C ∧ routeTLogReceiverLength C < n ∧ n ≤ N'
  omega

theorem routeTLogPhaseIntervalSum_eq_block (C : ℕ) (t : ℝ) :
    routeTLogPhaseIntervalSum C t =
      mvPhaseBlockSum (routeTLogReceiverCutoff C)
        (routeTLogReceiverLength C) (2 * routeTLogReceiverLength C)
        (routeTLogPhase t) := by
  let N := routeTLogReceiverLength C
  let K := routeTLogReceiverCutoff C
  have hNK : 2 * N < K := by
    unfold N K routeTLogReceiverCutoff
    omega
  unfold routeTLogPhaseIntervalSum mvPhaseBlockSum
  rw [Fin.sum_univ_eq_sum_range
    (fun n => routeTLogPhase t n *
      if routeTLogReceiverLength C < n ∧ n ≤ 2 * routeTLogReceiverLength C
      then 1 else 0)
    (routeTLogReceiverCutoff C)]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_range]
  change (routeTLogReceiverLength C < n ∧ n ≤ 2 * routeTLogReceiverLength C) ↔
    n < routeTLogReceiverCutoff C ∧
      routeTLogReceiverLength C < n ∧ n ≤ 2 * routeTLogReceiverLength C
  omega

def routeTLogReceiverBaseThreshold (u : ℕ) : ℕ :=
  max (routeTLogBaseThreshold u)
    (8 ^ (4 * vinogradovRouteTMoment (4 * u) ^ 2))

def routeTLogOneDimensionalSavingExponent (u : ℕ) : ℝ :=
  99 * vinogradovRouteTPowerSavingExponent u / 400

theorem routeTLogOneDimensionalSavingExponent_pos
    {u : ℕ} (hu : 1 ≤ u) :
    0 < routeTLogOneDimensionalSavingExponent u := by
  unfold routeTLogOneDimensionalSavingExponent
  have := vinogradovRouteTPowerSavingExponent_pos hu
  positivity

theorem routeTLogOneDimensionalSavingExponent_lt_one
    {u : ℕ} (hu : 1 ≤ u) :
    routeTLogOneDimensionalSavingExponent u < 1 := by
  unfold routeTLogOneDimensionalSavingExponent
  have hδ := vinogradovRouteTPowerSavingExponent_le_one_hundredth hu
  linarith

/-- Polynomial order loss: the explicit Route-T moment is cubic in `u`, so the rooted saving is
at worst quartic.  This quantitative law is what makes the later zeta optimization nontrivial. -/
theorem routeTLogOneDimensionalSavingExponent_ge
    {u : ℕ} (hu : 1 ≤ u) :
    1 / (5000000000000000 * (u : ℝ) ^ 4) ≤
      routeTLogOneDimensionalSavingExponent u := by
  let b := vinogradovRouteTMoment (4 * u)
  let A := vinogradovRouteTMomentSaving u
  let δ := vinogradovRouteTPowerSavingExponent u
  have hbNat : b ≤ 16000000 * u ^ 3 := by
    unfold b vinogradovRouteTMoment vinogradovRouteTOrder
      vinogradovRouteTMomentSteps
    have hsub : 2500 * (4 * u) ^ 2 - 200 * (4 * u) ≤ 40000 * u ^ 2 := by
      calc
        2500 * (4 * u) ^ 2 - 200 * (4 * u) ≤ 2500 * (4 * u) ^ 2 :=
          Nat.sub_le _ _
        _ = 40000 * u ^ 2 := by ring
    calc
      100 * (4 * u) * (2500 * (4 * u) ^ 2 - 200 * (4 * u)) ≤
          400 * u * (40000 * u ^ 2) := by
            simpa only [show 100 * (4 * u) = 400 * u by ring] using
              Nat.mul_le_mul_left (400 * u) hsub
      _ = 16000000 * u ^ 3 := by ring
  have hb : (b : ℝ) ≤ 16000000 * (u : ℝ) ^ 3 := by exact_mod_cast hbNat
  have hA : 2 * (u : ℝ) ^ 2 ≤ A := by
    unfold A vinogradovRouteTMomentSaving
    have hnat : 2 * u ^ 2 ≤ 20 * u ^ 2 - 1 := by
      apply Nat.le_sub_of_add_le
      nlinarith [sq_nonneg (u - 1)]
    exact_mod_cast hnat
  have hb0 : (0 : ℝ) < b := by
    exact_mod_cast (Nat.pos_of_ne_zero
      (vinogradovRouteTMoment_ne_zero (s := 4 * u) (by omega)))
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hu)
  have hden : (0 : ℝ) < 4 * (b : ℝ) ^ 2 := by positivity
  have hscale : (0 : ℝ) < 1000000000000000 * (u : ℝ) ^ 4 := by positivity
  have hbsq : 4 * (b : ℝ) ^ 2 ≤
      1024000000000000 * (u : ℝ) ^ 6 := by
    have hsquare : (b : ℝ) ^ 2 ≤
        (16000000 * (u : ℝ) ^ 3) ^ 2 := by nlinarith [sq_nonneg ((b : ℝ) - 16000000 * u ^ 3)]
    nlinarith
  have hδlower : 1 / (1000000000000000 * (u : ℝ) ^ 4) ≤ δ := by
    unfold δ vinogradovRouteTPowerSavingExponent
    change 1 / (1000000000000000 * (u : ℝ) ^ 4) ≤
      (A : ℝ) / (4 * (b : ℝ) ^ 2)
    rw [div_le_div_iff₀ hscale hden]
    nlinarith [sq_nonneg (u : ℝ), sq_nonneg ((u : ℝ) ^ 2)]
  have hδpos : 0 < δ := vinogradovRouteTPowerSavingExponent_pos hu
  have hdivide :
      1 / (5000000000000000 * (u : ℝ) ^ 4) =
        (1 / (1000000000000000 * (u : ℝ) ^ 4)) / 5 := by
    field_simp
    ring
  rw [hdivide]
  calc
    (1 / (1000000000000000 * (u : ℝ) ^ 4)) / 5 ≤ δ / 5 := by gcongr
    _ ≤ 99 * δ / 400 := by nlinarith

theorem routeTLogReceiverBaseThreshold_ge_base
    {u B : ℕ} (hB : routeTLogReceiverBaseThreshold u ≤ B) :
    routeTLogBaseThreshold u ≤ B :=
  (le_max_left _ _).trans hB

/-- The symbolic receiver threshold absorbs the factor eight needed to place the twisted bilinear
bound below the coefficient-block length.  No numerical evaluation of the threshold occurs. -/
theorem routeTLogReceiverBaseThreshold_small
    {u C : ℕ} (hu : 141 ≤ u)
    (hC : routeTLogReceiverBaseThreshold u ≤ 2 * C) :
    2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
        (2 - vinogradovRouteTPowerSavingExponent u)) ≤
      ((routeTLogHalfBlock C : ℕ) : ℝ) ^ 2 := by
  let B := 2 * C
  let Q := routeTLogHalfBlock C
  let A := vinogradovRouteTMomentSaving u
  let D := 4 * vinogradovRouteTMoment (4 * u) ^ 2
  let δ := vinogradovRouteTPowerSavingExponent u
  let P := B ^ routeTLogHalfLengthExponent
  have hbase : routeTLogBaseThreshold u ≤ B :=
    routeTLogReceiverBaseThreshold_ge_base (by simpa only [B] using hC)
  have hB2 : 2 ≤ B := routeTLogBaseThreshold_ge_two hbase
  have hδpos : 0 < δ := vinogradovRouteTPowerSavingExponent_pos (by omega)
  have hbne : vinogradovRouteTMoment (4 * u) ≠ 0 :=
    vinogradovRouteTMoment_ne_zero (s := 4 * u) (by omega)
  have hDne : D ≠ 0 := by unfold D; positivity
  have hA1 : 1 ≤ A := by
    unfold A vinogradovRouteTMomentSaving
    have hs : 1 < 20 * u ^ 2 := by nlinarith
    omega
  have hδeq : δ = (A : ℝ) / (D : ℝ) := by
    unfold δ A D vinogradovRouteTPowerSavingExponent
    push_cast
    rfl
  have hhugeNat : 8 ^ D ≤ B := by
    exact (le_max_right (routeTLogBaseThreshold u)
      (8 ^ (4 * vinogradovRouteTMoment (4 * u) ^ 2))).trans
      (by simpa only [routeTLogReceiverBaseThreshold, D, B] using hC)
  have hhuge : (((8 ^ D : ℕ) : ℝ)) ≤ B := by exact_mod_cast hhugeNat
  have hroot : ((((8 ^ D : ℕ) : ℝ)) ^ δ) = (8 : ℝ) ^ A := by
    rw [hδeq]
    push_cast
    have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hDne
    calc
      ((8 : ℝ) ^ D) ^ ((A : ℝ) / (D : ℝ)) =
          (8 : ℝ) ^ ((D : ℝ) * ((A : ℝ) / (D : ℝ))) := by
        rw [← Real.rpow_natCast (8 : ℝ) D]
        exact (Real.rpow_mul (by positivity) _ _).symm
      _ = (8 : ℝ) ^ (A : ℝ) := by
        congr 1
        field_simp
      _ = (8 : ℝ) ^ A := Real.rpow_natCast _ _
  have heighth : (8 : ℝ) ≤ (8 : ℝ) ^ A := by
    simpa using (pow_le_pow_right₀ (a := (8 : ℝ)) (by norm_num) hA1)
  have hBsave : (8 : ℝ) ≤ (B : ℝ) ^ δ := by
    calc
      (8 : ℝ) ≤ (8 : ℝ) ^ A := heighth
      _ = (((8 ^ D : ℕ) : ℝ)) ^ δ := hroot.symm
      _ ≤ (B : ℝ) ^ δ := Real.rpow_le_rpow (by positivity) hhuge hδpos.le
  have hBP : B ≤ P := by
    unfold P
    simpa using (pow_le_pow_right₀ (a := B) (by omega)
      (show 1 ≤ routeTLogHalfLengthExponent by norm_num [routeTLogHalfLengthExponent]))
  have hPsave : (8 : ℝ) ≤ (P : ℝ) ^ δ :=
    hBsave.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hBP) hδpos.le)
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (lt_of_lt_of_le (by omega) hBP)
  have hmul :
      (P : ℝ) ^ (2 - δ) * (P : ℝ) ^ δ = (P : ℝ) ^ 2 := by
    calc
      (P : ℝ) ^ (2 - δ) * (P : ℝ) ^ δ =
          (P : ℝ) ^ ((2 - δ) + δ) := (Real.rpow_add hPpos _ _).symm
      _ = (P : ℝ) ^ (2 : ℝ) := by ring_nf
      _ = (P : ℝ) ^ 2 := Real.rpow_two _
  have hsaved : 8 * (P : ℝ) ^ (2 - δ) ≤ (P : ℝ) ^ 2 := by
    calc
      8 * (P : ℝ) ^ (2 - δ) ≤
          (P : ℝ) ^ δ * (P : ℝ) ^ (2 - δ) :=
        mul_le_mul_of_nonneg_right hPsave (Real.rpow_nonneg hPpos.le _)
      _ = (P : ℝ) ^ 2 := by rw [mul_comm, hmul]
  have hP2Q : P = 2 * Q := by
    simpa only [P, B, Q] using (two_mul_routeTLogHalfBlock C).symm
  have hPq : (P : ℝ) ^ 2 = 4 * (Q : ℝ) ^ 2 := by
    rw [hP2Q]
    push_cast
    ring
  rw [hPq] at hsaved
  simpa only [P, B, Q, δ] using (show
    2 * (P : ℝ) ^ (2 - δ) ≤ (Q : ℝ) ^ 2 by nlinarith)

theorem routeTLog_receiver_scales
    {u C : ℕ} (hC : routeTLogBaseThreshold u ≤ 2 * C) :
    8 ≤ routeTLogHalfBlock C ∧
      16 * (routeTLogHalfBlock C) ^ 2 ≤ routeTLogReceiverLength C := by
  let B := 2 * C
  let Q := routeTLogHalfBlock C
  have hB2 : 2 ≤ B := routeTLogBaseThreshold_ge_two (by simpa only [B] using hC)
  have hC1 : 1 ≤ C := by omega
  have hP : 2 * Q = B ^ routeTLogHalfLengthExponent := by
    simpa only [B, Q] using two_mul_routeTLogHalfBlock C
  constructor
  · change 8 ≤ Q
    have hpow : 8 ≤ B ^ 98 := by
      exact (by norm_num : 8 ≤ 2 ^ 98).trans (Nat.pow_le_pow_left hB2 98)
    change 8 ≤ C * B ^ 98
    nlinarith [Nat.mul_le_mul_right (B ^ 98) hC1]
  · change 16 * Q ^ 2 ≤ B ^ routeTLogCentreExponent
    have hBsq : 4 ≤ B ^ 2 := by nlinarith
    calc
      16 * Q ^ 2 = 4 * (2 * Q) ^ 2 := by ring
      _ = 4 * B ^ 198 := by
        rw [hP]
        simp only [routeTLogHalfLengthExponent]
        rw [← pow_mul]
      _ ≤ B ^ 2 * B ^ 198 := by
        exact Nat.mul_le_mul_right (B ^ 198) hBsq
      _ = B ^ routeTLogCentreExponent := by
        rw [← pow_add]
        norm_num [routeTLogCentreExponent]

/-- Exact MV24.10 specialization.  Only `hsmall` remains as a transparent elementary scale
condition: the Route-T twisted saving must be no larger than the coefficient block length. -/
theorem routeTLogPhase_receiver_inequality
    {u C N' : ℕ} {t : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogBaseThreshold u ≤ 2 * C)
    (hNN' : routeTLogReceiverLength C < N')
    (hN' : N' ≤ 2 * routeTLogReceiverLength C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ)))
    (hsmall :
      2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
        (2 - vinogradovRouteTPowerSavingExponent u)) ≤
        ((routeTLogHalfBlock C : ℕ) : ℝ) ^ 2) :
    (((routeTLogHalfBlock C : ℕ) : ℝ) ^ 2 / 64) *
        ‖mvPhaseBlockSum (routeTLogReceiverCutoff C)
          (routeTLogReceiverLength C) N'
          (routeTLogPhase t)‖ ≤
      ((routeTLogHalfBlock C) ^ 2 + N' : ℕ) *
        (7 * Real.sqrt
            (((routeTLogHalfBlock C : ℕ) : ℝ) ^ 2 *
              (2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
                (2 - vinogradovRouteTPowerSavingExponent u)))) +
          3 * routeTLogHalfBlock C + 7) := by
  let Q := routeTLogHalfBlock C
  let N := routeTLogReceiverLength C
  let K := routeTLogReceiverCutoff C
  let S : ℝ := 2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
    (2 - vinogradovRouteTPowerSavingExponent u))
  obtain ⟨hQ8, hscale⟩ := routeTLog_receiver_scales hC
  have hscale' : 16 * Q ^ 2 ≤ N := by simpa only [Q, N] using hscale
  have hQN : Q ^ 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by
    have hB2 : 2 ≤ 2 * C := routeTLogBaseThreshold_ge_two hC
    change 1 ≤ (2 * C) ^ routeTLogCentreExponent
    exact one_le_pow₀ (by omega)
  have hKprod : 4 * Q ^ 2 < K := by
    unfold K routeTLogReceiverCutoff
    omega
  have hmax : 2 * Q ^ 2 + N' < K := by
    unfold K routeTLogReceiverCutoff
    omega
  have hreceiver := norm_mvCoefficientBlockSum_mul_mvPhaseBlockSum_le
    (K := K) (Q := Q) (M := Q ^ 2) (N := N) (N' := N')
    (hQ := by omega) (hM := by nlinarith) hQN
    (by simpa only [N] using hNN') (by simpa only [N] using hN') hmax
    (routeTProductMultiplicity hKprod) (routeTLogPhase t)
    (norm_routeTProductMultiplicity_le (by omega) hKprod)
    (by
      intro n
      unfold routeTLogPhase
      rw [norm_finitePhaseChar])
    (S := S) (by positivity)
    (by simpa only [S, Q, Nat.cast_pow] using hsmall) (by
      intro r hr β
      have hrange := Finset.mem_Ioc.mp hr
      have hrprod : 4 * Q ^ 2 < r := by omega
      rw [← mvTrigSum_convolutionCoefficient]
      unfold routeTLogPhase
      rw [mvTrigSum_routeTLogConvolution_eq hKprod hrprod]
      apply norm_routeTLogTwistedShiftBilinearSum_le_two_rpow_of_shell
        hu hC ht hbottom htop
      · exact_mod_cast (show N ≤ r by omega)
      · have hmult : 4 ≤ routeTLogCentreMultiplier := by
          norm_num [routeTLogCentreMultiplier]
        exact_mod_cast (show r ≤ routeTLogCentreMultiplier * N by
          have : r ≤ 4 * N := by omega
          exact this.trans (Nat.mul_le_mul_right N hmult)))
  have hcoeff := routeTProductMultiplicity_block_lower hQ8 hKprod
  have hfactor : 0 ≤
      ‖mvPhaseBlockSum K N N' (routeTLogPhase t)‖ := norm_nonneg _
  calc
    ((Q : ℝ) ^ 2 / 64) *
        ‖mvPhaseBlockSum K N N' (routeTLogPhase t)‖ ≤
      ‖mvCoefficientBlockSum K (Q ^ 2) (routeTProductMultiplicity hKprod)‖ *
        ‖mvPhaseBlockSum K N N' (routeTLogPhase t)‖ :=
      mul_le_mul_of_nonneg_right hcoeff hfactor
    _ = ‖mvCoefficientBlockSum K (Q ^ 2) (routeTProductMultiplicity hKprod) *
        mvPhaseBlockSum K N N' (routeTLogPhase t)‖ := by rw [norm_mul]
    _ ≤ (Q ^ 2 + N' : ℕ) *
        (7 * Real.sqrt ((Q : ℝ) ^ 2 * S) + 3 * Q + 7) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, S]
        using hreceiver

/-- First unconditional one-dimensional consequence of Route T: a strict power saving for the
logarithmic phase on the full dyadic receiver block. -/
theorem norm_routeTLogPhasePartialBlock_le_powerSaving
    {u C N' : ℕ} {t : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogReceiverBaseThreshold u ≤ 2 * C)
    (hNN' : routeTLogReceiverLength C < N')
    (hN' : N' ≤ 2 * routeTLogReceiverLength C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ))) :
    ‖mvPhaseBlockSum (routeTLogReceiverCutoff C)
        (routeTLogReceiverLength C) N'
        (routeTLogPhase t)‖ ≤
      6912 * routeTLogReceiverLength C *
        (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
          (-vinogradovRouteTPowerSavingExponent u / 2)) := by
  let Q := routeTLogHalfBlock C
  let N := routeTLogReceiverLength C
  let K := routeTLogReceiverCutoff C
  let P := (2 * C) ^ routeTLogHalfLengthExponent
  let δ := vinogradovRouteTPowerSavingExponent u
  let R : ℝ := (P : ℝ) ^ (1 - δ / 2)
  have hbase : routeTLogBaseThreshold u ≤ 2 * C :=
    routeTLogReceiverBaseThreshold_ge_base hC
  have hsmall := routeTLogReceiverBaseThreshold_small hu hC
  have hNposNat : 0 < N := by
    have hB2 := routeTLogBaseThreshold_ge_two hbase
    unfold N routeTLogReceiverLength
    positivity
  have hrecv := routeTLogPhase_receiver_inequality (N' := N')
    hu hbase (by simpa only [N] using hNN') (by simpa only [N] using hN')
    ht hbottom htop hsmall
  obtain ⟨hQ8, hscale⟩ := routeTLog_receiver_scales hbase
  have hQN : Q ^ 2 ≤ N := by
    have : 16 * Q ^ 2 ≤ N := by simpa only [Q, N] using hscale
    omega
  have hP2Q : P = 2 * Q := by
    simpa only [P, Q] using (two_mul_routeTLogHalfBlock C).symm
  have hPpos : (0 : ℝ) < P := by
    exact_mod_cast (show 0 < P by rw [hP2Q]; omega)
  have hδpos : 0 < δ := vinogradovRouteTPowerSavingExponent_pos (by omega)
  have hδupper : δ ≤ 1 / 100 :=
    vinogradovRouteTPowerSavingExponent_le_one_hundredth (by omega)
  have hR1 : (1 : ℝ) ≤ R := by
    unfold R
    apply Real.one_le_rpow
    · exact_mod_cast (show 1 ≤ P by rw [hP2Q]; omega)
    · linarith
  have hRpow : R ^ 2 = (P : ℝ) ^ (2 - δ) := by
    unfold R
    rw [pow_two, ← Real.rpow_add hPpos]
    congr 1
    ring
  have hsqrt :
      Real.sqrt ((Q : ℝ) ^ 2 * (2 * (P : ℝ) ^ (2 - δ))) ≤
        2 * Q * R := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hsquare : (2 * (Q : ℝ) * R) ^ 2 = 4 * (Q : ℝ) ^ 2 * R ^ 2 := by
        ring
      rw [hsquare, hRpow]
      have hpnonneg : 0 ≤ (P : ℝ) ^ (2 - δ) := Real.rpow_nonneg hPpos.le _
      have hqnonneg : (0 : ℝ) ≤ Q := by positivity
      nlinarith [sq_nonneg (Q : ℝ)]
  have hfactor :
      7 * Real.sqrt ((Q : ℝ) ^ 2 * (2 * (P : ℝ) ^ (2 - δ))) +
          3 * Q + 7 ≤ 18 * Q * R := by
    have hqnonneg : (0 : ℝ) ≤ Q := by positivity
    have hqR : (Q : ℝ) ≤ Q * R := by nlinarith
    have hQreal8 : (8 : ℝ) ≤ Q := by exact_mod_cast hQ8
    have hQR8 : (8 : ℝ) ≤ Q * R := by
      simpa only [mul_one] using
        (mul_le_mul hQreal8 hR1 (by norm_num : (0 : ℝ) ≤ 1) hqnonneg)
    have hseven : (7 : ℝ) ≤ Q * R :=
      (show (7 : ℝ) ≤ 8 by norm_num).trans hQR8
    nlinarith
  have houter : (((Q ^ 2 + N' : ℕ) : ℝ)) ≤ 3 * N := by
    exact_mod_cast (show Q ^ 2 + N' ≤ 3 * N by omega)
  have hweighted :
      ((Q : ℝ) ^ 2 / 64) *
          ‖mvPhaseBlockSum K N N' (routeTLogPhase t)‖ ≤
        54 * N * Q * R := by
    calc
      ((Q : ℝ) ^ 2 / 64) *
          ‖mvPhaseBlockSum K N N' (routeTLogPhase t)‖ ≤
        (((Q ^ 2 + N' : ℕ) : ℝ)) *
          (7 * Real.sqrt ((Q : ℝ) ^ 2 *
              (2 * (P : ℝ) ^ (2 - δ))) + 3 * Q + 7) := by
        simpa only [Q, N, K, P, δ, Nat.cast_pow] using hrecv
      _ ≤ (3 * N) * (18 * Q * R) :=
        mul_le_mul houter hfactor (by positivity) (by positivity)
      _ = 54 * N * Q * R := by ring
  have hRsplit : R = (P : ℝ) * (P : ℝ) ^ (-δ / 2) := by
    unfold R
    calc
      (P : ℝ) ^ (1 - δ / 2) = (P : ℝ) ^ (1 + (-δ / 2)) := by ring_nf
      _ = (P : ℝ) ^ (1 : ℝ) * (P : ℝ) ^ (-δ / 2) :=
        Real.rpow_add hPpos _ _
      _ = (P : ℝ) * (P : ℝ) ^ (-δ / 2) := by rw [Real.rpow_one]
  have hPcast : (P : ℝ) = 2 * Q := by exact_mod_cast hP2Q
  have hcoeffpos : 0 < (Q : ℝ) ^ 2 / 64 := by positivity
  apply le_of_mul_le_mul_left (a := ((Q : ℝ) ^ 2 / 64)) (a0 := hcoeffpos)
  calc
    ((Q : ℝ) ^ 2 / 64) *
        ‖mvPhaseBlockSum K N N' (routeTLogPhase t)‖ ≤
      54 * N * Q * R := hweighted
    _ = ((Q : ℝ) ^ 2 / 64) *
        (6912 * N * (P : ℝ) ^ (-δ / 2)) := by
      rw [hRsplit, hPcast]
      ring

theorem norm_routeTLogPhaseBlock_le_powerSaving
    {u C : ℕ} {t : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogReceiverBaseThreshold u ≤ 2 * C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ))) :
    ‖mvPhaseBlockSum (routeTLogReceiverCutoff C)
        (routeTLogReceiverLength C) (2 * routeTLogReceiverLength C)
        (routeTLogPhase t)‖ ≤
      6912 * routeTLogReceiverLength C *
        (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
          (-vinogradovRouteTPowerSavingExponent u / 2)) := by
  have hbase := routeTLogReceiverBaseThreshold_ge_base hC
  have hNpos : 0 < routeTLogReceiverLength C := by
    unfold routeTLogReceiverLength
    have hB2 := routeTLogBaseThreshold_ge_two hbase
    positivity
  exact norm_routeTLogPhasePartialBlock_le_powerSaving hu hC
    (by omega) (by omega) ht hbottom htop

/-- Same saving in the natural one-dimensional scale `N=(2C)^(200 : ℕ)`; its exponent is strictly
below one by `routeTLogOneDimensionalSavingExponent_pos`. -/
theorem norm_routeTLogPhasePartialBlock_le_rpow
    {u C N' : ℕ} {t : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogReceiverBaseThreshold u ≤ 2 * C)
    (hNN' : routeTLogReceiverLength C < N')
    (hN' : N' ≤ 2 * routeTLogReceiverLength C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ))) :
    ‖mvPhaseBlockSum (routeTLogReceiverCutoff C)
        (routeTLogReceiverLength C) N'
        (routeTLogPhase t)‖ ≤
      6912 * (((routeTLogReceiverLength C : ℕ) : ℝ) ^
        (1 - routeTLogOneDimensionalSavingExponent u)) := by
  let B := 2 * C
  let P := B ^ routeTLogHalfLengthExponent
  let N := routeTLogReceiverLength C
  let δ := vinogradovRouteTPowerSavingExponent u
  let ε := routeTLogOneDimensionalSavingExponent u
  have hraw := norm_routeTLogPhasePartialBlock_le_powerSaving hu hC hNN' hN'
    ht hbottom htop
  have hBpos : (0 : ℝ) < B := by
    have hbase := routeTLogReceiverBaseThreshold_ge_base hC
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 2)
      (routeTLogBaseThreshold_ge_two hbase))
  have hNval : N = B ^ 200 := by rfl
  have hPN : (P : ℝ) ^ (-δ / 2) = (N : ℝ) ^ (-ε) := by
    change ((((B ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^ (-δ / 2)) =
      ((((B ^ 200 : ℕ) : ℝ)) ^
        (-(99 * δ / 400)))
    push_cast
    rw [← Real.rpow_natCast (B : ℝ) routeTLogHalfLengthExponent,
      ← Real.rpow_natCast (B : ℝ) 200,
      ← Real.rpow_mul hBpos.le, ← Real.rpow_mul hBpos.le]
    norm_num [routeTLogHalfLengthExponent]
    ring_nf
  have hNpos : (0 : ℝ) < N := by
    rw [hNval]
    exact_mod_cast (pow_pos (by exact_mod_cast hBpos) 200)
  have hcombine : (N : ℝ) * (N : ℝ) ^ (-ε) = (N : ℝ) ^ (1 - ε) := by
    calc
      (N : ℝ) * (N : ℝ) ^ (-ε) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-ε) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) + (-ε)) := (Real.rpow_add hNpos _ _).symm
      _ = (N : ℝ) ^ (1 - ε) := by ring_nf
  calc
    ‖mvPhaseBlockSum (routeTLogReceiverCutoff C)
        (routeTLogReceiverLength C) N'
        (routeTLogPhase t)‖ ≤
      6912 * (N : ℝ) * (P : ℝ) ^ (-δ / 2) := by
        simpa only [N, P, B, δ] using hraw
    _ = 6912 * (N : ℝ) * (N : ℝ) ^ (-ε) := by rw [hPN]
    _ = 6912 * (N : ℝ) ^ (1 - ε) := by rw [mul_assoc, hcombine]

theorem norm_routeTLogPhaseBlock_le_rpow
    {u C : ℕ} {t : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogReceiverBaseThreshold u ≤ 2 * C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ))) :
    ‖mvPhaseBlockSum (routeTLogReceiverCutoff C)
        (routeTLogReceiverLength C) (2 * routeTLogReceiverLength C)
        (routeTLogPhase t)‖ ≤
      6912 * (((routeTLogReceiverLength C : ℕ) : ℝ) ^
        (1 - routeTLogOneDimensionalSavingExponent u)) := by
  have hbase := routeTLogReceiverBaseThreshold_ge_base hC
  have hNpos : 0 < routeTLogReceiverLength C := by
    unfold routeTLogReceiverLength
    have hB2 := routeTLogBaseThreshold_ge_two hbase
    positivity
  exact norm_routeTLogPhasePartialBlock_le_rpow hu hC
    (by omega) (by omega) ht hbottom htop

theorem norm_routeTLogPhasePartialIntervalSum_le_rpow
    {u C N' : ℕ} {t : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogReceiverBaseThreshold u ≤ 2 * C)
    (hNN' : routeTLogReceiverLength C < N')
    (hN' : N' ≤ 2 * routeTLogReceiverLength C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ))) :
    ‖routeTLogPhasePartialIntervalSum C N' t‖ ≤
      6912 * (((routeTLogReceiverLength C : ℕ) : ℝ) ^
        (1 - routeTLogOneDimensionalSavingExponent u)) := by
  rw [routeTLogPhasePartialIntervalSum_eq_block hN']
  exact norm_routeTLogPhasePartialBlock_le_rpow hu hC hNN' hN' ht hbottom htop

/-- Abel transport of Route T's prefix-uniform phase saving to `n^{-σ}` weights. -/
theorem norm_routeTLogWeightedPartialIntervalSum_le
    {u C N' : ℕ} {σ t : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogReceiverBaseThreshold u ≤ 2 * C)
    (hNN' : routeTLogReceiverLength C < N')
    (hN' : N' ≤ 2 * routeTLogReceiverLength C)
    (hσ : 0 ≤ σ) (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ))) :
    ‖routeTLogWeightedPartialIntervalSum C N' σ t‖ ≤
      (6912 * (((routeTLogReceiverLength C : ℕ) : ℝ) ^
        (1 - routeTLogOneDimensionalSavingExponent u))) *
          (((routeTLogReceiverLength C + 1 : ℕ) : ℝ) ^ (-σ)) := by
  let N := routeTLogReceiverLength C
  let M := N' + 1
  let P : ℝ := 6912 * (N : ℝ) ^
    (1 - routeTLogOneDimensionalSavingExponent u)
  have hbase := routeTLogReceiverBaseThreshold_ge_base hC
  have hNpos : 0 < N := by
    unfold N routeTLogReceiverLength
    have hB2 := routeTLogBaseThreshold_ge_two hbase
    positivity
  have hNM : N + 1 ≤ M := by unfold M N; omega
  have hP0 : 0 ≤ P := by unfold P; positivity
  have hpref : ∀ m, N + 1 ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ico (N + 1) m, routeTLogPhase t n‖ ≤ P := by
    intro m hmN hmM
    rcases eq_or_lt_of_le hmN with rfl | hmNlt
    · simp only [Finset.Ico_self, Finset.sum_empty, norm_zero]
      exact hP0
    · have hendLower : N < m - 1 := by omega
      have hendUpper : m - 1 ≤ 2 * N := by
        unfold M at hmM
        have hN'local : N' ≤ 2 * N := by simpa only [N] using hN'
        omega
      have hbound := norm_routeTLogPhasePartialIntervalSum_le_rpow
        hu hC (C := C) (N' := m - 1) (t := t)
        (by simpa only [N] using hendLower) (by simpa only [N] using hendUpper)
        ht hbottom htop
      have hsum : (∑ n ∈ Finset.Ico (N + 1) m, routeTLogPhase t n) =
          routeTLogPhasePartialIntervalSum C (m - 1) t := by
        unfold routeTLogPhasePartialIntervalSum
        congr 1
        ext n
        simp only [Finset.mem_Ico, Finset.mem_Ioc]
        change (N + 1 ≤ n ∧ n < m) ↔ N < n ∧ n ≤ m - 1
        omega
      rw [hsum]
      simpa only [P, N] using hbound
  have hanti : ∀ m, N + 1 ≤ m → m < M →
      (((m + 1 : ℕ) : ℝ) ^ (-σ)) ≤ (((m : ℕ) : ℝ) ^ (-σ)) := by
    intro m hm _
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    exact Real.rpow_le_rpow_of_nonpos hm0 (by push_cast; linarith) (by linarith)
  have hM0 : (0 : ℝ) ≤ (M : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
  have hab := abel_block_bound (routeTLogPhase t)
    (fun n => (n : ℝ) ^ (-σ)) (N + 1) M hNM hM0 hanti P hpref
  have hsum : routeTLogWeightedPartialIntervalSum C N' σ t =
      ∑ n ∈ Finset.Ico (N + 1) M,
        ((((n : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * routeTLogPhase t n := by
    unfold routeTLogWeightedPartialIntervalSum M N
    congr 1
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hsum]
  simpa only [P, N] using hab

theorem norm_routeTLogPhaseIntervalSum_le_rpow
    {u C : ℕ} {t : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogReceiverBaseThreshold u ≤ 2 * C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ))) :
    ‖routeTLogPhaseIntervalSum C t‖ ≤
      6912 * (((routeTLogReceiverLength C : ℕ) : ℝ) ^
        (1 - routeTLogOneDimensionalSavingExponent u)) := by
  rw [routeTLogPhaseIntervalSum_eq_block]
  exact norm_routeTLogPhaseBlock_le_rpow hu hC ht hbottom htop

end

end RHTower.Sieve
