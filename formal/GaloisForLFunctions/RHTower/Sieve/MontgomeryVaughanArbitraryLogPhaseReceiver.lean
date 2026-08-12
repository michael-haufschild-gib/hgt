import GaloisForLFunctions.RHTower.Sieve.MontgomeryVaughanLogPhaseReceiver
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Arbitrary-centre Route T receiver

The original receiver was centered exactly at `B^200`.  A zeta decomposition needs the same
estimate at arbitrary integer locations.  The widened Taylor centre cone and the floor 200th root
reduce that problem to one fixed factor `2^200`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

def routeTLogArbitraryCutoff (X : ℕ) : ℕ := 4 * X + 1

def routeTLogArbitraryPhasePartialSum (X X' : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc X X', routeTLogPhase t n

def routeTLogArbitraryWeightedPartialSum (X X' : ℕ) (σ t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc X X',
    ((((n : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * routeTLogPhase t n

def routeTLogRootHalfBase (X : ℕ) : ℕ :=
  Nat.nthRoot routeTLogCentreExponent X / 2

def routeTLogRootBase (X : ℕ) : ℕ :=
  2 * routeTLogRootHalfBase X

def routeTLogShellIndex (X T : ℕ) : ℕ :=
  Nat.clog ((routeTLogRootBase X ^ routeTLogCentreExponent) ^ 4) T

def routeTLogRealShellIndex (X : ℕ) (t : ℝ) : ℕ :=
  routeTLogShellIndex X ⌈t⌉₊

theorem routeTLogShellIndex_bounds
    {X T : ℕ} (hB2 : 2 ≤ routeTLogRootBase X) (hT : 1 < T) :
    (routeTLogRootBase X ^ routeTLogCentreExponent) ^
          (4 * routeTLogShellIndex X T - 4) < T ∧
      T ≤ (routeTLogRootBase X ^ routeTLogCentreExponent) ^
          (4 * routeTLogShellIndex X T) := by
  let B0 := routeTLogRootBase X ^ routeTLogCentreExponent
  let A := B0 ^ 4
  let u := routeTLogShellIndex X T
  have hB0 : 1 < B0 := by
    unfold B0
    exact one_lt_pow₀ (by omega) (by norm_num [routeTLogCentreExponent])
  have hA : 1 < A := one_lt_pow₀ hB0 (by omega)
  have hu0 : 0 < u := by
    change 0 < Nat.clog A T
    exact Nat.clog_pos hA hT
  have hlower := Nat.pow_pred_clog_lt_self hA hT
  have hupper := Nat.le_pow_clog hA T
  constructor
  · change B0 ^ (4 * u - 4) < T
    calc
      B0 ^ (4 * u - 4) = B0 ^ (4 * (u - 1)) := by congr 1; omega
      _ = (B0 ^ 4) ^ (u - 1) := by rw [pow_mul]
      _ < T := by
        simpa only [u, routeTLogShellIndex, B0, A, Nat.pred_eq_sub_one] using hlower
  · change T ≤ B0 ^ (4 * u)
    calc
      T ≤ (B0 ^ 4) ^ u := by
        simpa only [u, routeTLogShellIndex, B0, A] using hupper
      _ = B0 ^ (4 * u) := by rw [pow_mul]

theorem routeTLogShellIndex_ge
    {X T v : ℕ} (hB2 : 2 ≤ routeTLogRootBase X)
    (hlarge : (routeTLogRootBase X ^ routeTLogCentreExponent) ^ (4 * v) < T) :
    v < routeTLogShellIndex X T := by
  let B0 := routeTLogRootBase X ^ routeTLogCentreExponent
  have hB0 : 1 < B0 := by
    unfold B0
    exact one_lt_pow₀ (by omega) (by norm_num [routeTLogCentreExponent])
  have hA : 1 < B0 ^ 4 := one_lt_pow₀ hB0 (by omega)
  have hlarge' : (B0 ^ 4) ^ v < T := by
    rw [← pow_mul]
    simpa only [B0] using hlarge
  exact (Nat.lt_clog_iff_pow_lt hA).mpr hlarge'

theorem routeTLogRealShellIndex_bounds
    {X : ℕ} {t : ℝ} (hB2 : 2 ≤ routeTLogRootBase X) (ht : 1 < t) :
    (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
          (4 * routeTLogRealShellIndex X t - 4) : ℕ) : ℝ) < t ∧
      t ≤ (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
          (4 * routeTLogRealShellIndex X t) : ℕ) : ℝ) := by
  have ht' : ((1 : ℕ) : ℝ) < t := by norm_num at ht ⊢; exact ht
  have hceil : 1 < ⌈t⌉₊ := Nat.lt_ceil.mpr ht'
  obtain ⟨hlower, hupper⟩ := routeTLogShellIndex_bounds
    (X := X) (T := ⌈t⌉₊) hB2 hceil
  constructor
  · exact Nat.lt_ceil.mp (by simpa only [routeTLogRealShellIndex] using hlower)
  · exact Nat.ceil_le.mp (by simpa only [routeTLogRealShellIndex] using hupper)

theorem routeTLogRealShellIndex_ge
    {X v : ℕ} {t : ℝ} (hB2 : 2 ≤ routeTLogRootBase X)
    (hlarge : (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * v) : ℕ) : ℝ) < t) :
    v < routeTLogRealShellIndex X t := by
  apply routeTLogShellIndex_ge hB2
  exact Nat.lt_ceil.mpr hlarge

theorem routeTLogRootBase_cell
    {X : ℕ} (hB2 : 2 ≤ routeTLogRootBase X) :
    routeTLogRootBase X ^ routeTLogCentreExponent ≤ X ∧
      X ≤ 2 ^ 200 * routeTLogRootBase X ^ routeTLogCentreExponent := by
  let R := Nat.nthRoot routeTLogCentreExponent X
  let B := routeTLogRootBase X
  have hdegree : routeTLogCentreExponent = 200 := rfl
  have hBR : B ≤ R := by
    unfold B R routeTLogRootBase routeTLogRootHalfBase
    have h := Nat.div_mul_le_self (Nat.nthRoot routeTLogCentreExponent X) 2
    omega
  have hRlt : R < B + 2 := by
    unfold B R routeTLogRootBase routeTLogRootHalfBase
    have h := Nat.mod_lt (Nat.nthRoot routeTLogCentreExponent X) (by omega : 0 < 2)
    omega
  have hlowerRoot : R ^ routeTLogCentreExponent ≤ X := by
    rw [Nat.pow_nthRoot_le_iff]
    left
    norm_num [routeTLogCentreExponent]
  have hlower : B ^ routeTLogCentreExponent ≤ X :=
    (Nat.pow_le_pow_left hBR _).trans hlowerRoot
  have hXroot : X < (R + 1) ^ routeTLogCentreExponent :=
    Nat.lt_pow_nthRoot_add_one (by norm_num [routeTLogCentreExponent]) X
  have hRone : R + 1 ≤ B + 2 := by omega
  have hBdouble : B + 2 ≤ 2 * B := by omega
  have hupperPow : (R + 1) ^ routeTLogCentreExponent ≤
      (2 * B) ^ routeTLogCentreExponent :=
    Nat.pow_le_pow_left (hRone.trans hBdouble) _
  have hpowSplit : (2 * B) ^ routeTLogCentreExponent =
      2 ^ 200 * B ^ routeTLogCentreExponent := by
    rw [mul_pow]
    norm_num [routeTLogCentreExponent]
  constructor
  · exact hlower
  · rw [← hpowSplit]
    exact (Nat.le_of_lt hXroot).trans hupperPow

theorem routeTLogRootBase_ge_threshold
    {u X : ℕ}
    (hroot : routeTLogReceiverBaseThreshold u + 1 ≤
      Nat.nthRoot routeTLogCentreExponent X) :
    routeTLogReceiverBaseThreshold u ≤ routeTLogRootBase X := by
  unfold routeTLogRootBase routeTLogRootHalfBase
  have hmod := Nat.mod_lt (Nat.nthRoot routeTLogCentreExponent X)
    (by omega : 0 < 2)
  omega

theorem routeTLogArbitraryPhasePartialSum_eq_block
    {X X' : ℕ} (hX' : X' ≤ 2 * X) (t : ℝ) :
    routeTLogArbitraryPhasePartialSum X X' t =
      mvPhaseBlockSum (routeTLogArbitraryCutoff X) X X' (routeTLogPhase t) := by
  have hX'K : X' < routeTLogArbitraryCutoff X := by
    unfold routeTLogArbitraryCutoff
    omega
  unfold routeTLogArbitraryPhasePartialSum mvPhaseBlockSum
  rw [Fin.sum_univ_eq_sum_range
    (fun n => routeTLogPhase t n * if X < n ∧ n ≤ X' then 1 else 0)
    (routeTLogArbitraryCutoff X)]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_range]
  change (X < n ∧ n ≤ X') ↔ n < routeTLogArbitraryCutoff X ∧ X < n ∧ n ≤ X'
  omega

/-- Exact MV24.10 receiver at an arbitrary centre `X` in the widened 200th-power cell. -/
theorem routeTLogArbitraryPhase_receiver_inequality
    {u C X X' : ℕ} {t : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogBaseThreshold u ≤ 2 * C)
    (hXlower : (2 * C) ^ routeTLogCentreExponent ≤ X)
    (hXupper : X ≤ 2 ^ 200 * (2 * C) ^ routeTLogCentreExponent)
    (hXX' : X < X') (hX' : X' ≤ 2 * X)
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
        ‖mvPhaseBlockSum (routeTLogArbitraryCutoff X) X X'
          (routeTLogPhase t)‖ ≤
      ((routeTLogHalfBlock C) ^ 2 + X' : ℕ) *
        (7 * Real.sqrt
            (((routeTLogHalfBlock C : ℕ) : ℝ) ^ 2 *
              (2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
                (2 - vinogradovRouteTPowerSavingExponent u)))) +
          3 * routeTLogHalfBlock C + 7) := by
  let Q := routeTLogHalfBlock C
  let B0 := (2 * C) ^ routeTLogCentreExponent
  let K := routeTLogArbitraryCutoff X
  let S : ℝ := 2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
    (2 - vinogradovRouteTPowerSavingExponent u))
  obtain ⟨hQ8, hscale⟩ := routeTLog_receiver_scales hC
  have hscale' : 16 * Q ^ 2 ≤ B0 := by
    simpa [Q, B0, routeTLogReceiverLength] using hscale
  have hQX : Q ^ 2 ≤ X := by omega
  have hKprod : 4 * Q ^ 2 < K := by
    unfold K routeTLogArbitraryCutoff
    omega
  have hmax : 2 * Q ^ 2 + X' < K := by
    unfold K routeTLogArbitraryCutoff
    omega
  have hreceiver := norm_mvCoefficientBlockSum_mul_mvPhaseBlockSum_le
    (K := K) (Q := Q) (M := Q ^ 2) (N := X) (N' := X')
    (hQ := by omega) (hM := by nlinarith) hQX hXX' hX' hmax
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
      · exact_mod_cast (show B0 ≤ r by omega)
      · have hr4X : r ≤ 4 * X := by omega
        have hmul : 4 * (2 ^ 200 * B0) = routeTLogCentreMultiplier * B0 := by
          unfold routeTLogCentreMultiplier
          ring
        have : r ≤ routeTLogCentreMultiplier * B0 := by
          calc
            r ≤ 4 * X := hr4X
            _ ≤ 4 * (2 ^ 200 * B0) := Nat.mul_le_mul_left 4 hXupper
            _ = routeTLogCentreMultiplier * B0 := hmul
        exact_mod_cast this)
  have hcoeff := routeTProductMultiplicity_block_lower hQ8 hKprod
  have hfactor : 0 ≤ ‖mvPhaseBlockSum K X X' (routeTLogPhase t)‖ := norm_nonneg _
  calc
    ((Q : ℝ) ^ 2 / 64) * ‖mvPhaseBlockSum K X X' (routeTLogPhase t)‖ ≤
      ‖mvCoefficientBlockSum K (Q ^ 2) (routeTProductMultiplicity hKprod)‖ *
        ‖mvPhaseBlockSum K X X' (routeTLogPhase t)‖ :=
      mul_le_mul_of_nonneg_right hcoeff hfactor
    _ = ‖mvCoefficientBlockSum K (Q ^ 2) (routeTProductMultiplicity hKprod) *
        mvPhaseBlockSum K X X' (routeTLogPhase t)‖ := by rw [norm_mul]
    _ ≤ (Q ^ 2 + X' : ℕ) *
        (7 * Real.sqrt ((Q : ℝ) ^ 2 * S) + 3 * Q + 7) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, S]
        using hreceiver

theorem norm_routeTLogArbitraryPhasePartialSum_le_powerSaving
    {u C X X' : ℕ} {t : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogReceiverBaseThreshold u ≤ 2 * C)
    (hXlower : (2 * C) ^ routeTLogCentreExponent ≤ X)
    (hXupper : X ≤ 2 ^ 200 * (2 * C) ^ routeTLogCentreExponent)
    (hXX' : X < X') (hX' : X' ≤ 2 * X)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ))) :
    ‖routeTLogArbitraryPhasePartialSum X X' t‖ ≤
      6912 * X *
        (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
          (-vinogradovRouteTPowerSavingExponent u / 2)) := by
  let Q := routeTLogHalfBlock C
  let P := (2 * C) ^ routeTLogHalfLengthExponent
  let δ := vinogradovRouteTPowerSavingExponent u
  let R : ℝ := (P : ℝ) ^ (1 - δ / 2)
  have hbase := routeTLogReceiverBaseThreshold_ge_base hC
  have hsmall := routeTLogReceiverBaseThreshold_small hu hC
  have hrecv := routeTLogArbitraryPhase_receiver_inequality hu hbase hXlower hXupper
    hXX' hX' ht hbottom htop hsmall
  obtain ⟨hQ8, _hscale⟩ := routeTLog_receiver_scales hbase
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
  have hQX : Q ^ 2 ≤ X := by
    have hscale := (routeTLog_receiver_scales hbase).2
    have hscale' : 16 * Q ^ 2 ≤ routeTLogReceiverLength C := by
      simpa only [Q] using hscale
    have hbaseX : routeTLogReceiverLength C ≤ X := by
      simpa [routeTLogReceiverLength] using hXlower
    omega
  have houter : (((Q ^ 2 + X' : ℕ) : ℝ)) ≤ 3 * X := by
    exact_mod_cast (show Q ^ 2 + X' ≤ 3 * X by omega)
  have hweighted :
      ((Q : ℝ) ^ 2 / 64) *
          ‖mvPhaseBlockSum (routeTLogArbitraryCutoff X) X X'
            (routeTLogPhase t)‖ ≤ 54 * X * Q * R := by
    calc
      ((Q : ℝ) ^ 2 / 64) *
          ‖mvPhaseBlockSum (routeTLogArbitraryCutoff X) X X'
            (routeTLogPhase t)‖ ≤
        (((Q ^ 2 + X' : ℕ) : ℝ)) *
          (7 * Real.sqrt ((Q : ℝ) ^ 2 *
              (2 * (P : ℝ) ^ (2 - δ))) + 3 * Q + 7) := by
        simpa only [Q, P, δ, Nat.cast_pow] using hrecv
      _ ≤ (3 * X) * (18 * Q * R) :=
        mul_le_mul houter hfactor (by positivity) (by positivity)
      _ = 54 * X * Q * R := by ring
  have hRsplit : R = (P : ℝ) * (P : ℝ) ^ (-δ / 2) := by
    unfold R
    calc
      (P : ℝ) ^ (1 - δ / 2) = (P : ℝ) ^ (1 + (-δ / 2)) := by ring_nf
      _ = (P : ℝ) ^ (1 : ℝ) * (P : ℝ) ^ (-δ / 2) :=
        Real.rpow_add hPpos _ _
      _ = (P : ℝ) * (P : ℝ) ^ (-δ / 2) := by rw [Real.rpow_one]
  have hPcast : (P : ℝ) = 2 * Q := by exact_mod_cast hP2Q
  have hcoeffpos : 0 < (Q : ℝ) ^ 2 / 64 := by positivity
  rw [routeTLogArbitraryPhasePartialSum_eq_block hX']
  apply le_of_mul_le_mul_left (a := ((Q : ℝ) ^ 2 / 64)) (a0 := hcoeffpos)
  calc
    ((Q : ℝ) ^ 2 / 64) *
        ‖mvPhaseBlockSum (routeTLogArbitraryCutoff X) X X'
          (routeTLogPhase t)‖ ≤ 54 * X * Q * R := hweighted
    _ = ((Q : ℝ) ^ 2 / 64) *
        (6912 * X * (P : ℝ) ^ (-δ / 2)) := by
      rw [hRsplit, hPcast]
      ring

/-- Floor-root form: every sufficiently large integer centre is assigned an even Route-T base,
with no perfect-power restriction. -/
theorem norm_routeTLogArbitraryPhasePartialSum_le_rootSaving
    {u X X' : ℕ} {t : ℝ} (hu : 141 ≤ u)
    (hroot : routeTLogReceiverBaseThreshold u + 1 ≤
      Nat.nthRoot routeTLogCentreExponent X)
    (hXX' : X < X') (hX' : X' ≤ 2 * X)
    (ht : 0 < t)
    (hbottom : ((((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ ((((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ))) :
    ‖routeTLogArbitraryPhasePartialSum X X' t‖ ≤
      6912 * X *
        ((((routeTLogRootBase X ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
          (-vinogradovRouteTPowerSavingExponent u / 2)) := by
  let C := routeTLogRootHalfBase X
  have hB : 2 * C = routeTLogRootBase X := rfl
  have hthreshold : routeTLogReceiverBaseThreshold u ≤ 2 * C := by
    rw [hB]
    exact routeTLogRootBase_ge_threshold hroot
  have hbase : routeTLogBaseThreshold u ≤ 2 * C :=
    routeTLogReceiverBaseThreshold_ge_base hthreshold
  have hB2 : 2 ≤ routeTLogRootBase X := by
    exact (routeTLogBaseThreshold_ge_two hbase).trans_eq hB
  obtain ⟨hcellLower, hcellUpper⟩ := routeTLogRootBase_cell hB2
  have hlower : (2 * C) ^ routeTLogCentreExponent ≤ X := by simpa only [hB]
    using hcellLower
  have hupper : X ≤ 2 ^ 200 * (2 * C) ^ routeTLogCentreExponent := by
    simpa only [hB] using hcellUpper
  have hbound := norm_routeTLogArbitraryPhasePartialSum_le_powerSaving
    hu hthreshold hlower hupper hXX' hX' ht
    (by simpa only [hB] using hbottom) (by simpa only [hB] using htop)
  simpa only [hB] using hbound

/-- Every sufficiently high real frequency selects its own logarithmic shell.  This removes the
height-band parameter from the arbitrary-centre receiver. -/
theorem norm_routeTLogArbitraryPhasePartialSum_le_automaticShell
    {X X' : ℕ} {t : ℝ}
    (hroot : routeTLogReceiverBaseThreshold (routeTLogRealShellIndex X t) + 1 ≤
      Nat.nthRoot routeTLogCentreExponent X)
    (hlarge : (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * 141) : ℕ) : ℝ) < t)
    (hXX' : X < X') (hX' : X' ≤ 2 * X) :
    ‖routeTLogArbitraryPhasePartialSum X X' t‖ ≤
      6912 * X *
        ((((routeTLogRootBase X ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
          (-vinogradovRouteTPowerSavingExponent (routeTLogRealShellIndex X t) / 2)) := by
  let u := routeTLogRealShellIndex X t
  have hthreshold : routeTLogReceiverBaseThreshold u ≤ routeTLogRootBase X :=
    routeTLogRootBase_ge_threshold hroot
  have hbase : routeTLogBaseThreshold u ≤ routeTLogRootBase X :=
    routeTLogReceiverBaseThreshold_ge_base hthreshold
  have hB2 : 2 ≤ routeTLogRootBase X := routeTLogBaseThreshold_ge_two hbase
  have hu : 141 ≤ u := by
    have := routeTLogRealShellIndex_ge (v := 141) hB2 hlarge
    omega
  have ht1 : 1 < t := by
    have hone : (1 : ℝ) ≤
        ((routeTLogRootBase X ^ routeTLogCentreExponent) ^ (4 * 141) : ℕ) := by
      have hinner : 1 ≤ routeTLogRootBase X ^ routeTLogCentreExponent :=
        one_le_pow₀ (by omega)
      exact_mod_cast (one_le_pow₀ hinner :
        1 ≤ (routeTLogRootBase X ^ routeTLogCentreExponent) ^ (4 * 141))
    linarith
  obtain ⟨hbottom, htop⟩ := routeTLogRealShellIndex_bounds hB2 ht1
  exact norm_routeTLogArbitraryPhasePartialSum_le_rootSaving hu hroot hXX' hX'
    (by linarith) hbottom.le htop

/-- Abel transport of the arbitrary-centre estimate.  Prefix uniformity is retained while the
shell and floor-root choices remain fixed by the left endpoint. -/
theorem norm_routeTLogArbitraryWeightedPartialSum_le_automaticShell
    {X X' : ℕ} {σ t : ℝ}
    (hroot : routeTLogReceiverBaseThreshold (routeTLogRealShellIndex X t) + 1 ≤
      Nat.nthRoot routeTLogCentreExponent X)
    (hlarge : (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * 141) : ℕ) : ℝ) < t)
    (hXX' : X < X') (hX' : X' ≤ 2 * X) (hσ : 0 ≤ σ) :
    ‖routeTLogArbitraryWeightedPartialSum X X' σ t‖ ≤
      (6912 * X *
        ((((routeTLogRootBase X ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
          (-vinogradovRouteTPowerSavingExponent (routeTLogRealShellIndex X t) / 2))) *
        ((((X + 1 : ℕ) : ℝ)) ^ (-σ)) := by
  let M := X' + 1
  let P : ℝ := 6912 * X *
    ((((routeTLogRootBase X ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
      (-vinogradovRouteTPowerSavingExponent (routeTLogRealShellIndex X t) / 2))
  have hXM : X + 1 ≤ M := by unfold M; omega
  have hP0 : 0 ≤ P := by unfold P; positivity
  have hpref : ∀ m, X + 1 ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ico (X + 1) m, routeTLogPhase t n‖ ≤ P := by
    intro m hmX hmM
    rcases eq_or_lt_of_le hmX with rfl | hmXlt
    · simp only [Finset.Ico_self, Finset.sum_empty, norm_zero]
      exact hP0
    · have hendLower : X < m - 1 := by omega
      have hendUpper : m - 1 ≤ 2 * X := by
        unfold M at hmM
        omega
      have hbound := norm_routeTLogArbitraryPhasePartialSum_le_automaticShell
        hroot hlarge hendLower hendUpper
      have hsum : (∑ n ∈ Finset.Ico (X + 1) m, routeTLogPhase t n) =
          routeTLogArbitraryPhasePartialSum X (m - 1) t := by
        unfold routeTLogArbitraryPhasePartialSum
        congr 1
        ext n
        simp only [Finset.mem_Ico, Finset.mem_Ioc]
        omega
      rw [hsum]
      simpa only [P] using hbound
  have hanti : ∀ m, X + 1 ≤ m → m < M →
      (((m + 1 : ℕ) : ℝ) ^ (-σ)) ≤ (((m : ℕ) : ℝ) ^ (-σ)) := by
    intro m hm _
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    exact Real.rpow_le_rpow_of_nonpos hm0 (by push_cast; linarith) (by linarith)
  have hM0 : (0 : ℝ) ≤ (M : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
  have hab := abel_block_bound (routeTLogPhase t)
    (fun n => (n : ℝ) ^ (-σ)) (X + 1) M hXM hM0 hanti P hpref
  have hsum : routeTLogArbitraryWeightedPartialSum X X' σ t =
      ∑ n ∈ Finset.Ico (X + 1) M,
        ((((n : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * routeTLogPhase t n := by
    unfold routeTLogArbitraryWeightedPartialSum M
    congr 1
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hsum]
  simpa only [P] using hab

end

end RHTower.Sieve
