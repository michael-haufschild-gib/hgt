import GaloisForLFunctions.RHTower.Sieve.RouteTZetaFinalGrowth

/-!
# Height-band parameters for Route T

Landau discs move the ordinate by less than one.  A shell chosen from the centre therefore needs
one discrete reserve beyond the pointwise tenth-root shell.  Adding one to that shell supplies the
reserve without changing the degree-nine/tenth-root exponent.
-/

namespace RHTower.Sieve

noncomputable section

def routeTBandShell (t : ℝ) : ℕ :=
  Nat.nthRoot 10 (routeTBinaryHeight t) + 2

def routeTBandDepthRootThreshold : ℕ :=
  routeTLogCentreExponent * (routeTLogReceiverDegreeNineConstant + 1) * 4 ^ 9 + 1

theorem routeTBandDepthRootThreshold_pos : 2 ≤ routeTBandDepthRootThreshold := by
  have hcentre : 1 ≤ routeTLogCentreExponent := by
    unfold routeTLogCentreExponent
    norm_num
  have hC : 1 ≤ routeTLogReceiverDegreeNineConstant + 1 := by omega
  have hfour : 1 ≤ 4 ^ 9 := by norm_num
  have hprod : 1 ≤ routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant + 1) * 4 ^ 9 := by
    calc
      1 = 1 * 1 * 1 := by norm_num
      _ ≤ routeTLogCentreExponent *
          (routeTLogReceiverDegreeNineConstant + 1) * 4 ^ 9 :=
        Nat.mul_le_mul (Nat.mul_le_mul hcentre hC) hfour
  unfold routeTBandDepthRootThreshold
  omega

theorem routeTBandShell_pos (t : ℝ) : 2 ≤ routeTBandShell t := by
  unfold routeTBandShell
  omega

theorem routeTBinaryHeight_mono {s t : ℝ} (hst : s ≤ t) :
    routeTBinaryHeight s ≤ routeTBinaryHeight t := by
  unfold routeTBinaryHeight
  exact Nat.clog_mono_right 2 (Nat.ceil_mono hst)

theorem routeTBandShell_mono {s t : ℝ} (hst : s ≤ t) :
    routeTBandShell s ≤ routeTBandShell t := by
  have hL := routeTBinaryHeight_mono hst
  have hroot : Nat.nthRoot 10 (routeTBinaryHeight s) ≤
      Nat.nthRoot 10 (routeTBinaryHeight t) := by
    apply (Nat.le_nthRoot_iff (by norm_num)).2
    exact (Nat.pow_nthRoot_le (Or.inl (by norm_num))).trans hL
  unfold routeTBandShell
  omega

theorem routeTStripWidth_antitone {V W : ℕ} (hVW : V ≤ W) :
    routeTStripWidth W ≤ routeTStripWidth V := by
  have hpow : (V + 1) ^ 9 ≤ (W + 1) ^ 9 := Nat.pow_le_pow_left (by omega) 9
  have hnat : routeTStripDenominator * (V + 1) ^ 9 ≤
      routeTStripDenominator * (W + 1) ^ 9 := Nat.mul_le_mul_left _ hpow
  have hpos : (0 : ℝ) < (routeTStripDenominator * (V + 1) ^ 9 : ℕ) := by
    exact_mod_cast Nat.mul_pos routeTStripDenominator_pos (pow_pos (by omega) 9)
  unfold routeTStripWidth
  apply one_div_le_one_div_of_le hpos
  exact_mod_cast hnat

theorem routeTBandWidth_antitone {s t : ℝ} (hst : s ≤ t) :
    routeTStripWidth (routeTBandShell t) ≤ routeTStripWidth (routeTBandShell s) :=
  routeTStripWidth_antitone (routeTBandShell_mono hst)

/-- One extra tenth-root shell buys two exponent units, enough for shifting the ordinate down by
one before choosing the cubic truncation. -/
theorem routeTBandExponent_add_two_le_binaryHeight {t : ℝ}
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight t) :
    routeTGlobalExponent (routeTBandShell t) + 2 ≤ routeTBinaryHeight t := by
  let L := routeTBinaryHeight t
  let r := Nat.nthRoot 10 L
  have hroot : routeTBandDepthRootThreshold ≤ r :=
    (Nat.le_nthRoot_iff (by norm_num)).2 (by simpa only [L] using hlarge)
  have hr2 : 2 ≤ r := routeTBandDepthRootThreshold_pos.trans hroot
  have hfour : r + 3 ≤ 4 * r := by omega
  have hpow : (r + 3) ^ 9 ≤ (4 * r) ^ 9 := Nat.pow_le_pow_left hfour 9
  have hmoment : routeTGlobalMoment (r + 2) ≤
      (routeTLogReceiverDegreeNineConstant + 1) * (4 ^ 9 * r ^ 9) := by
    unfold routeTGlobalMoment
    have hone : 1 ≤ (r + 3) ^ 9 := Nat.one_le_pow _ _ (by omega)
    calc
      routeTLogReceiverDegreeNineConstant * (r + 3) ^ 9 + 1 ≤
          (routeTLogReceiverDegreeNineConstant + 1) * (r + 3) ^ 9 := by
        rw [add_mul]
        simpa only [one_mul] using Nat.add_le_add_left hone
          (routeTLogReceiverDegreeNineConstant * (r + 3) ^ 9)
      _ ≤ (routeTLogReceiverDegreeNineConstant + 1) * (4 * r) ^ 9 :=
        Nat.mul_le_mul_left _ hpow
      _ = (routeTLogReceiverDegreeNineConstant + 1) * (4 ^ 9 * r ^ 9) := by
        rw [mul_pow]
  have hE : routeTGlobalExponent (r + 2) ≤
      (routeTBandDepthRootThreshold - 1) * r ^ 9 := by
    unfold routeTGlobalExponent routeTBandDepthRootThreshold
    calc
      routeTLogCentreExponent * routeTGlobalMoment (r + 2) ≤
          routeTLogCentreExponent *
            ((routeTLogReceiverDegreeNineConstant + 1) * (4 ^ 9 * r ^ 9)) :=
        Nat.mul_le_mul_left _ hmoment
      _ = (routeTLogCentreExponent *
          (routeTLogReceiverDegreeNineConstant + 1) * 4 ^ 9) * r ^ 9 := by ring
      _ = (routeTLogCentreExponent *
          (routeTLogReceiverDegreeNineConstant + 1) * 4 ^ 9 + 1 - 1) * r ^ 9 := by
        congr 2
  have hrpow : 2 ≤ r ^ 9 := by
    calc
      2 ≤ r := hr2
      _ = r ^ (1 : ℕ) := (pow_one r).symm
      _ ≤ r ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have hE2 : routeTGlobalExponent (r + 2) + 2 ≤
      routeTBandDepthRootThreshold * r ^ 9 := by
    calc
      routeTGlobalExponent (r + 2) + 2 ≤
          (routeTBandDepthRootThreshold - 1) * r ^ 9 + 2 :=
        Nat.add_le_add_right hE 2
      _ ≤ (routeTBandDepthRootThreshold - 1) * r ^ 9 + r ^ 9 :=
        Nat.add_le_add_left hrpow _
      _ = routeTBandDepthRootThreshold * r ^ 9 := by
        calc
          (routeTBandDepthRootThreshold - 1) * r ^ 9 + r ^ 9 =
              (routeTBandDepthRootThreshold - 1) * r ^ 9 + 1 * r ^ 9 := by
                rw [one_mul]
          _ = (routeTBandDepthRootThreshold - 1 + 1) * r ^ 9 := (add_mul _ _ _).symm
          _ = routeTBandDepthRootThreshold * r ^ 9 := by
            have hthr : 1 ≤ routeTBandDepthRootThreshold :=
              (by norm_num : (1 : ℕ) ≤ 2).trans routeTBandDepthRootThreshold_pos
            rw [Nat.sub_add_cancel hthr]
  have hKr : routeTBandDepthRootThreshold * r ^ 9 ≤ r ^ 10 := by
    calc
      routeTBandDepthRootThreshold * r ^ 9 ≤ r * r ^ 9 :=
        Nat.mul_le_mul_right (r ^ 9) hroot
      _ = r ^ 10 := by ring
  have hrL : r ^ 10 ≤ L := by
    dsimp only [r]
    exact Nat.pow_nthRoot_le (Or.inl (by norm_num))
  simpa only [routeTBandShell, L, r] using hE2.trans (hKr.trans hrL)

/-- Moving the real height down by one decreases binary height by at most one. -/
theorem routeTBinaryHeight_le_prev_add_one {t : ℝ} (ht : 1 ≤ t) :
    routeTBinaryHeight t ≤ routeTBinaryHeight (t - 1) + 1 := by
  let L := routeTBinaryHeight (t - 1)
  have htprev : 0 ≤ t - 1 := by linarith
  have hceilLe : ⌈t⌉₊ ≤ ⌈t - 1⌉₊ + 1 := by
    calc
      ⌈t⌉₊ ≤ ⌈(t - 1) + 1⌉₊ := Nat.ceil_mono (by linarith)
      _ = ⌈t - 1⌉₊ + 1 := by
        simpa only [Nat.cast_one] using Nat.ceil_add_natCast htprev 1
  have hceilPrev : ⌈t - 1⌉₊ ≤ 2 ^ L := by
    dsimp only [L, routeTBinaryHeight]
    exact Nat.le_pow_clog (by omega) _
  have hceil : ⌈t⌉₊ ≤ 2 ^ (L + 1) := by
    rw [pow_succ]
    have hone : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    exact hceilLe.trans (by omega)
  unfold routeTBinaryHeight
  exact (Nat.clog_le_iff_le_pow (by norm_num)).2 hceil

/-- The band shell selected at `t` fits below the cubic exponent at `t-1`. -/
theorem routeTBandCanonicalDepth {t : ℝ} (ht : 2 < t)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight t) :
    routeTGlobalExponent (routeTBandShell t) + 1 ≤ topExponent (t - 1) := by
  have hE := routeTBandExponent_add_two_le_binaryHeight hlarge
  have hshift := routeTBinaryHeight_le_prev_add_one (by linarith : 1 ≤ t)
  have hLprev : 11 ≤ routeTBinaryHeight (t - 1) := by
    have hK : 12 ≤ routeTBandDepthRootThreshold ^ 10 := by
      calc
        12 ≤ 2 ^ 10 := by norm_num
        _ ≤ routeTBandDepthRootThreshold ^ 10 :=
          Nat.pow_le_pow_left routeTBandDepthRootThreshold_pos 10
    have hLt : 12 ≤ routeTBinaryHeight t := hK.trans hlarge
    clear hlarge hK
    omega
  have htop := routeTBinaryHeight_le_topExponent (t := t - 1) (by linarith) hLprev
  have hbridge : routeTGlobalExponent (routeTBandShell t) + 2 ≤
      routeTBinaryHeight (t - 1) + 1 := hE.trans hshift
  clear hlarge hE hshift
  omega

/-- Any height whose binary height is below `V^(10 : ℕ)` lies in the receiver's upper shell. -/
theorem routeTHeight_upper_of_binaryHeight {t : ℝ} {V : ℕ}
    (_hV : 1 ≤ V) (hL : routeTBinaryHeight t ≤ V ^ 10) :
    t ≤ (((routeTLogRootBase (routeTGlobalStart V) ^ routeTLogCentreExponent) ^
      (4 * V) : ℕ) : ℝ) := by
  let L := routeTBinaryHeight t
  have hceil : ⌈t⌉₊ ≤ 2 ^ L := by
    dsimp only [L, routeTBinaryHeight]
    exact Nat.le_pow_clog (by omega) _
  have hC : 1 ≤ routeTLogReceiverDegreeNineConstant := by
    unfold routeTLogReceiverDegreeNineConstant
    omega
  have hVpow : V ^ 9 ≤ routeTGlobalMoment V := by
    unfold routeTGlobalMoment
    calc
      V ^ 9 ≤ (V + 1) ^ 9 := Nat.pow_le_pow_left (Nat.le_succ V) 9
      _ = 1 * (V + 1) ^ 9 := (Nat.one_mul _).symm
      _ ≤ routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 :=
        Nat.mul_le_mul_right _ hC
      _ ≤ routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1 := Nat.le_succ _
  have hLE : L ≤ routeTGlobalExponent V * (4 * V) := by
    calc
      L ≤ V ^ 10 := by simpa only [L] using hL
      _ = V ^ 9 * V := by ring
      _ ≤ routeTGlobalMoment V * V := Nat.mul_le_mul_right V hVpow
      _ ≤ routeTGlobalExponent V * (4 * V) := by
        unfold routeTGlobalExponent
        norm_num [routeTLogCentreExponent]
        nlinarith [routeTGlobalMoment_pos V]
  have hnat : ⌈t⌉₊ ≤ (routeTGlobalStart V) ^ (4 * V) := by
    calc
      ⌈t⌉₊ ≤ 2 ^ L := hceil
      _ ≤ 2 ^ (routeTGlobalExponent V * (4 * V)) :=
        Nat.pow_le_pow_right (by omega) hLE
      _ = (routeTGlobalStart V) ^ (4 * V) := by
        unfold routeTGlobalStart
        rw [pow_mul]
  have hreal : t ≤ (((routeTGlobalStart V) ^ (4 * V) : ℕ) : ℝ) :=
    (Nat.le_ceil t).trans (by exact_mod_cast hnat)
  rw [show routeTLogRootBase (routeTGlobalStart V) ^ routeTLogCentreExponent =
      routeTGlobalStart V by
    rw [routeTLogRootBase_globalStart, ← routeTGlobalStart_eq_centrePower]]
  exact hreal

/-- Every ordinate in the unit band above the centre is admitted by the one-reserve shell. -/
theorem routeTBandHeight_upper {t y : ℝ} (ht : 1 ≤ t) (hy : y ≤ t + 1) :
    y ≤ (((routeTLogRootBase (routeTGlobalStart (routeTBandShell t)) ^
      routeTLogCentreExponent) ^ (4 * routeTBandShell t) : ℕ) : ℝ) := by
  have hyceil : ⌈y⌉₊ ≤ ⌈t⌉₊ + 1 := by
    have hmono := Nat.ceil_mono hy
    have hadd := Nat.ceil_add_natCast (by linarith : 0 ≤ t) 1
    norm_num at hadd
    simpa only [hadd] using hmono
  let L := routeTBinaryHeight t
  have htceil : ⌈t⌉₊ ≤ 2 ^ L := by
    dsimp only [L, routeTBinaryHeight]
    exact Nat.le_pow_clog (by omega) _
  have hyPow : ⌈y⌉₊ ≤ 2 ^ (L + 1) := by
    rw [pow_succ]
    have hone : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    omega
  have hyL : routeTBinaryHeight y ≤ L + 1 := by
    unfold routeTBinaryHeight
    exact (Nat.clog_le_iff_le_pow (by norm_num)).2 hyPow
  have hroot : L < (Nat.nthRoot 10 L + 1) ^ 10 :=
    (Nat.nthRoot_lt_iff (by norm_num)).1 (Nat.lt_succ_self _)
  have hLpow : L + 1 ≤ routeTBandShell t ^ 10 := by
    have hmono : (Nat.nthRoot 10 L + 1) ^ 10 ≤
        (Nat.nthRoot 10 L + 2) ^ 10 :=
      Nat.pow_le_pow_left (Nat.le_succ _) 10
    unfold routeTBandShell
    simpa only [L] using (Nat.succ_le_of_lt hroot).trans hmono
  exact routeTHeight_upper_of_binaryHeight
    ((by norm_num : (1 : ℕ) ≤ 2).trans (routeTBandShell_pos t)) (hyL.trans hLpow)

end

end RHTower.Sieve
