import GaloisForLFunctions.RHTower.Sieve.RouteTZetaParameters

/-!
# Discharging the canonical Route-T depth condition

Degree nine is paid by one factor below the tenth-root height.  Once the tenth root exceeds one
explicit constant, the global receiver start lies below the binary height, hence below the cubic
zeta truncation.
-/

namespace RHTower.Sieve

noncomputable section

def routeTDepthRootThreshold : ℕ :=
  routeTLogCentreExponent * (routeTLogReceiverDegreeNineConstant + 1) * 3 ^ 9 + 1

theorem routeTDepthRootThreshold_pos : 1 ≤ routeTDepthRootThreshold := by
  unfold routeTDepthRootThreshold
  omega

theorem routeTGlobalExponent_add_one_le_of_root
    {L r : ℕ} (hr : r = Nat.nthRoot 10 L)
    (hroot : routeTDepthRootThreshold ≤ r) :
    routeTGlobalExponent (r + 1) + 1 ≤ L := by
  have hr1 : 1 ≤ r := routeTDepthRootThreshold_pos.trans hroot
  have hthree : r + 2 ≤ 3 * r := by omega
  have hpow : (r + 2) ^ 9 ≤ (3 * r) ^ 9 := Nat.pow_le_pow_left hthree 9
  have hpowSplit : (3 * r) ^ 9 = 3 ^ 9 * r ^ 9 := by rw [mul_pow]
  have hmoment : routeTGlobalMoment (r + 1) ≤
      (routeTLogReceiverDegreeNineConstant + 1) * (3 ^ 9 * r ^ 9) := by
    unfold routeTGlobalMoment
    have hone : 1 ≤ (r + 2) ^ 9 := Nat.one_le_pow _ _ (by omega)
    calc
      routeTLogReceiverDegreeNineConstant * (r + 2) ^ 9 + 1 ≤
          (routeTLogReceiverDegreeNineConstant + 1) * (r + 2) ^ 9 := by
        rw [add_mul]
        simpa only [one_mul] using
          Nat.add_le_add_left hone (routeTLogReceiverDegreeNineConstant * (r + 2) ^ 9)
      _ ≤ (routeTLogReceiverDegreeNineConstant + 1) * (3 * r) ^ 9 :=
        Nat.mul_le_mul_left _ hpow
      _ = (routeTLogReceiverDegreeNineConstant + 1) * (3 ^ 9 * r ^ 9) := by
        rw [hpowSplit]
  have hE : routeTGlobalExponent (r + 1) ≤
      (routeTDepthRootThreshold - 1) * r ^ 9 := by
    unfold routeTGlobalExponent routeTDepthRootThreshold
    calc
      routeTLogCentreExponent * routeTGlobalMoment (r + 1) ≤
          routeTLogCentreExponent *
            ((routeTLogReceiverDegreeNineConstant + 1) * (3 ^ 9 * r ^ 9)) :=
        Nat.mul_le_mul_left _ hmoment
      _ = (routeTLogCentreExponent *
          (routeTLogReceiverDegreeNineConstant + 1) * 3 ^ 9) * r ^ 9 := by ring
      _ = (routeTLogCentreExponent *
          (routeTLogReceiverDegreeNineConstant + 1) * 3 ^ 9 + 1 - 1) * r ^ 9 := by
        congr 2
  have hrpow : 1 ≤ r ^ 9 := Nat.one_le_pow _ _ hr1
  have hEone : routeTGlobalExponent (r + 1) + 1 ≤
      routeTDepthRootThreshold * r ^ 9 := by
    calc
      routeTGlobalExponent (r + 1) + 1 ≤
          (routeTDepthRootThreshold - 1) * r ^ 9 + 1 := Nat.add_le_add_right hE 1
      _ ≤ (routeTDepthRootThreshold - 1) * r ^ 9 + r ^ 9 :=
        Nat.add_le_add_left hrpow _
      _ = routeTDepthRootThreshold * r ^ 9 := by
        calc
          (routeTDepthRootThreshold - 1) * r ^ 9 + r ^ 9 =
              (routeTDepthRootThreshold - 1) * r ^ 9 + 1 * r ^ 9 := by rw [one_mul]
          _ = (routeTDepthRootThreshold - 1 + 1) * r ^ 9 := (add_mul _ _ _).symm
          _ = routeTDepthRootThreshold * r ^ 9 := by
            rw [Nat.sub_add_cancel routeTDepthRootThreshold_pos]
  have hKr : routeTDepthRootThreshold * r ^ 9 ≤ r ^ 10 := by
    calc
      routeTDepthRootThreshold * r ^ 9 ≤ r * r ^ 9 :=
        Nat.mul_le_mul_right (r ^ 9) hroot
      _ = r ^ 10 := by ring
  have hrL : r ^ 10 ≤ L := by
    rw [hr]
    exact Nat.pow_nthRoot_le (Or.inl (by norm_num))
  exact hEone.trans (hKr.trans hrL)

theorem routeTGlobalExponent_add_one_le_binaryHeight {t : ℝ}
    (hlarge : routeTDepthRootThreshold ^ 10 ≤ routeTBinaryHeight t) :
    routeTGlobalExponent (routeTGlobalShell t) + 1 ≤ routeTBinaryHeight t := by
  let L := routeTBinaryHeight t
  let r := Nat.nthRoot 10 L
  have hroot : routeTDepthRootThreshold ≤ r :=
    (Nat.le_nthRoot_iff (by norm_num)).2 (by simpa only [L] using hlarge)
  have hmain := routeTGlobalExponent_add_one_le_of_root (L := L) (r := r) rfl hroot
  simpa only [routeTGlobalShell, L, r] using hmain

/-- Beyond a fixed binary height, the cubic truncation exponent dominates the binary height itself. -/
theorem routeTBinaryHeight_le_topExponent {t : ℝ} (ht : 1 < t)
    (hL : 11 ≤ routeTBinaryHeight t) :
    routeTBinaryHeight t ≤ topExponent t := by
  let L := routeTBinaryHeight t
  let T := ⌈t⌉₊
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.le
  have hT1 : 1 < T := by
    dsimp only [T]
    apply Nat.lt_ceil.mpr
    norm_num
    exact ht
  have hclog : 2 ^ (L - 1) < T := by
    have h := Nat.pow_pred_clog_lt_self (b := 2) (by omega) hT1
    simpa only [L, routeTBinaryHeight, T, Nat.pred_eq_sub_one] using h
  have hceil : (T : ℝ) < t + 1 := by
    dsimp only [T]
    exact Nat.ceil_lt_add_one ht0
  have hpowStep : 2 ^ (L - 2) + 1 ≤ 2 ^ (L - 1) := by
    have hone : 1 ≤ 2 ^ (L - 2) := Nat.one_le_two_pow
    have hexp : L - 1 = (L - 2) + 1 := by
      have : 11 ≤ L := by simpa only [L] using hL
      omega
    calc
      2 ^ (L - 2) + 1 ≤ 2 ^ (L - 2) + 2 ^ (L - 2) :=
        Nat.add_le_add_left hone _
      _ = 2 * 2 ^ (L - 2) := by ring
      _ = 2 ^ ((L - 2) + 1) := by rw [pow_succ]; ring
      _ = 2 ^ (L - 1) := congrArg (fun e : ℕ => 2 ^ e) hexp.symm
  have hpwt : (((2 ^ (L - 2) : ℕ) : ℝ)) < t := by
    have hstep : (((2 ^ (L - 2) : ℕ) : ℝ)) + 1 ≤
        (((2 ^ (L - 1) : ℕ) : ℝ)) := by exact_mod_cast hpowStep
    have hclogR : (((2 ^ (L - 1) : ℕ) : ℝ)) < (T : ℝ) := by exact_mod_cast hclog
    linarith
  have hlogt : ((L : ℝ) - 2) * Real.log 2 ≤ Real.log t := by
    have hlog := Real.log_le_log
      (by positivity : (0 : ℝ) < (((2 ^ (L - 2) : ℕ) : ℝ))) hpwt.le
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog
    have hL2 : 2 ≤ L := by
      have : 11 ≤ L := by simpa only [L] using hL
      omega
    rw [Nat.cast_sub hL2] at hlog
    norm_num at hlog ⊢
    exact hlog
  have hden0 : (0 : ℝ) < 8 * Real.pi := by positivity
  have hdenle : 8 * Real.pi ≤ 32 := by nlinarith [Real.pi_lt_d2]
  have hlogden : Real.log (8 * Real.pi) ≤ 5 * Real.log 2 := by
    have hlog := Real.log_le_log hden0 hdenle
    have h32 : (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
    rw [h32, Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog
  have htpos : 0 < t := lt_trans one_pos ht
  have hratio : ((L : ℝ) - 7) * Real.log 2 ≤ Real.log (t / (8 * Real.pi)) := by
    rw [Real.log_div htpos.ne' hden0.ne']
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold topExponent
  apply Nat.le_floor
  rw [le_div_iff₀ hlog2]
  have hLreal : (11 : ℝ) ≤ L := by
    exact_mod_cast (by simpa only [L] using hL)
  nlinarith

/-- The explicit tenth-power binary threshold discharges the only canonical depth premise. -/
theorem routeTCanonicalDepth {t : ℝ} (ht : 1 < t)
    (hlarge : routeTDepthRootThreshold ^ 10 ≤ routeTBinaryHeight t) :
    routeTGlobalExponent (routeTGlobalShell t) + 1 ≤ topExponent t := by
  have hE := routeTGlobalExponent_add_one_le_binaryHeight hlarge
  have hK : 11 ≤ routeTDepthRootThreshold ^ 10 := by
    have hC : 1 ≤ routeTLogReceiverDegreeNineConstant := by
      unfold routeTLogReceiverDegreeNineConstant
      norm_num
    have hcentre : 1 ≤ routeTLogCentreExponent := by
      unfold routeTLogCentreExponent
      norm_num
    have hCplus : 1 ≤ routeTLogReceiverDegreeNineConstant + 1 := by omega
    have hthree : 1 ≤ 3 ^ 9 := by norm_num
    have hprod : 1 ≤ routeTLogCentreExponent *
        (routeTLogReceiverDegreeNineConstant + 1) * 3 ^ 9 := by
      calc
        1 = 1 * 1 * 1 := by norm_num
        _ ≤ routeTLogCentreExponent *
            (routeTLogReceiverDegreeNineConstant + 1) * 3 ^ 9 :=
          Nat.mul_le_mul (Nat.mul_le_mul hcentre hCplus) hthree
    have hK2 : 2 ≤ routeTDepthRootThreshold := by
      unfold routeTDepthRootThreshold
      omega
    calc
      11 ≤ 2 ^ 10 := by norm_num
      _ ≤ routeTDepthRootThreshold ^ 10 := Nat.pow_le_pow_left hK2 10
  have hL : 11 ≤ routeTBinaryHeight t := hK.trans hlarge
  exact hE.trans (routeTBinaryHeight_le_topExponent ht hL)

end

end RHTower.Sieve
