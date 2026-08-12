import GaloisForLFunctions.RHTower.Sieve.RouteTZetaGrowth
import GaloisForLFunctions.RHTower.Sieve.DirichletTopExponentChoice

/-!
# Canonical global parameters for Route-T zeta growth

The tenth-root shell is chosen from the binary logarithmic height.  Its ninth power pays the
receiver threshold; the remaining factor pays the height shell.  This is the exact degree-nine to
degree-ten mechanism behind the logarithmic exponent `9/10`.
-/

namespace RHTower.Sieve

noncomputable section

def routeTGlobalMoment (V : ℕ) : ℕ :=
  routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1

def routeTGlobalExponent (V : ℕ) : ℕ :=
  routeTLogCentreExponent * routeTGlobalMoment V

def routeTGlobalStart (V : ℕ) : ℕ :=
  2 ^ routeTGlobalExponent V

def routeTBinaryHeight (t : ℝ) : ℕ :=
  Nat.clog 2 ⌈t⌉₊

def routeTGlobalShell (t : ℝ) : ℕ :=
  Nat.nthRoot 10 (routeTBinaryHeight t) + 1

def routeTRouteStripScale : ℕ := 10000000000000000

def routeTDerivativeStripScale : ℕ := 3 * 2 ^ (566 : ℕ)

def routeTThresholdStripScale : ℕ :=
  routeTLogCentreExponent * (routeTLogReceiverDegreeNineConstant + 1)

def routeTStripDenominator : ℕ :=
  routeTRouteStripScale * routeTDerivativeStripScale * routeTThresholdStripScale

def routeTStripWidth (V : ℕ) : ℝ :=
  1 / (routeTStripDenominator * (V + 1) ^ 9 : ℕ)

def routeTStripAbscissa (V : ℕ) : ℝ :=
  1 - routeTStripWidth V

theorem routeTGlobalMoment_pos (V : ℕ) : 0 < routeTGlobalMoment V := by
  unfold routeTGlobalMoment
  omega

theorem routeTGlobalExponent_eq (V : ℕ) :
    routeTGlobalExponent V = routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1) := rfl

theorem routeTGlobalStart_size (V : ℕ) :
    2 ^ (routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1)) ≤
        routeTGlobalStart V := le_rfl

theorem routeTGlobalStart_two_le (V : ℕ) : 2 ≤ routeTGlobalStart V := by
  have hm := routeTGlobalMoment_pos V
  have hE : 1 ≤ routeTGlobalExponent V := by
    unfold routeTGlobalExponent
    have hc : 1 ≤ routeTLogCentreExponent := by
      norm_num [routeTLogCentreExponent]
    exact Nat.mul_pos hc hm
  unfold routeTGlobalStart
  calc
    2 = 2 ^ (1 : ℕ) := (pow_one 2).symm
    _ ≤ 2 ^ routeTGlobalExponent V := Nat.pow_le_pow_right (by norm_num) hE

theorem routeTGlobalStart_eq_centrePower (V : ℕ) :
    routeTGlobalStart V =
      (2 ^ routeTGlobalMoment V) ^ routeTLogCentreExponent := by
  calc
    routeTGlobalStart V =
        2 ^ (routeTLogCentreExponent * routeTGlobalMoment V) := rfl
    _ = 2 ^ (routeTGlobalMoment V * routeTLogCentreExponent) := by
      rw [Nat.mul_comm]
    _ = (2 ^ routeTGlobalMoment V) ^ routeTLogCentreExponent := by
      rw [pow_mul]

theorem nthRoot_routeTGlobalStart (V : ℕ) :
    Nat.nthRoot routeTLogCentreExponent (routeTGlobalStart V) =
      2 ^ routeTGlobalMoment V := by
  rw [routeTGlobalStart_eq_centrePower]
  exact Nat.nthRoot_pow (by norm_num [routeTLogCentreExponent]) _

theorem routeTLogRootBase_globalStart (V : ℕ) :
    routeTLogRootBase (routeTGlobalStart V) = 2 ^ routeTGlobalMoment V := by
  have hm : 0 < routeTGlobalMoment V := routeTGlobalMoment_pos V
  obtain ⟨m, hmEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  unfold routeTLogRootBase routeTLogRootHalfBase
  rw [nthRoot_routeTGlobalStart, hmEq, pow_succ]
  omega

theorem routeTGlobalShell_pos (t : ℝ) : 1 ≤ routeTGlobalShell t := by
  unfold routeTGlobalShell
  omega

theorem routeTBinaryHeight_lt_shell_pow (t : ℝ) :
    routeTBinaryHeight t < (routeTGlobalShell t) ^ 10 := by
  unfold routeTGlobalShell
  exact (Nat.nthRoot_lt_iff (by norm_num)).1 (Nat.lt_succ_self _)

theorem routeTBinaryHeight_le_globalExponent_mul_shell (t : ℝ) :
    routeTBinaryHeight t ≤
      routeTGlobalExponent (routeTGlobalShell t) * (4 * routeTGlobalShell t) := by
  let V := routeTGlobalShell t
  have hL : routeTBinaryHeight t ≤ V ^ 10 :=
    (routeTBinaryHeight_lt_shell_pow t).le
  have hC : 1 ≤ routeTLogReceiverDegreeNineConstant := by
    unfold routeTLogReceiverDegreeNineConstant
    omega
  have hV1 : V ^ 9 ≤ (V + 1) ^ 9 :=
    Nat.pow_le_pow_left (Nat.le_succ V) 9
  have hmoment : V ^ 9 ≤ routeTGlobalMoment V := by
    unfold routeTGlobalMoment
    calc
      V ^ 9 ≤ (V + 1) ^ 9 := hV1
      _ = 1 * (V + 1) ^ 9 := (Nat.one_mul _).symm
      _ ≤ routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 :=
        Nat.mul_le_mul_right _ hC
      _ ≤ routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1 := Nat.le_succ _
  calc
    routeTBinaryHeight t ≤ V ^ 10 := hL
    _ = V ^ 9 * V := by ring
    _ ≤ routeTGlobalMoment V * V := Nat.mul_le_mul_right V hmoment
    _ ≤ routeTGlobalExponent V * (4 * V) := by
      unfold routeTGlobalExponent
      norm_num [routeTLogCentreExponent]
      nlinarith [routeTGlobalMoment_pos V]

/-- The canonical tenth-root index always provides the required upper shell. -/
theorem routeTGlobalHeight_upper {t : ℝ} (_ht : 1 < t) :
    t ≤ (((routeTLogRootBase (routeTGlobalStart (routeTGlobalShell t)) ^
      routeTLogCentreExponent) ^ (4 * routeTGlobalShell t) : ℕ) : ℝ) := by
  let V := routeTGlobalShell t
  let L := routeTBinaryHeight t
  have hceil : ⌈t⌉₊ ≤ 2 ^ L := by
    dsimp only [L, routeTBinaryHeight]
    exact Nat.le_pow_clog (by omega) _
  have hLE : L ≤ routeTGlobalExponent V * (4 * V) := by
    simpa only [L, V] using routeTBinaryHeight_le_globalExponent_mul_shell t
  have hpows : 2 ^ L ≤ 2 ^ (routeTGlobalExponent V * (4 * V)) :=
    Nat.pow_le_pow_right (by omega) hLE
  have hnat : ⌈t⌉₊ ≤ (routeTGlobalStart V) ^ (4 * V) := by
    calc
      ⌈t⌉₊ ≤ 2 ^ L := hceil
      _ ≤ 2 ^ (routeTGlobalExponent V * (4 * V)) := hpows
      _ = (routeTGlobalStart V) ^ (4 * V) := by
        unfold routeTGlobalStart
        rw [pow_mul]
  have hreal : t ≤ (((routeTGlobalStart V) ^ (4 * V) : ℕ) : ℝ) :=
    (Nat.le_ceil t).trans (by exact_mod_cast hnat)
  rw [show routeTLogRootBase (routeTGlobalStart V) ^ routeTLogCentreExponent =
      routeTGlobalStart V by
    rw [routeTLogRootBase_globalStart, ← routeTGlobalStart_eq_centrePower]]
  simpa only [V] using hreal

theorem routeTStripDenominator_pos : 0 < routeTStripDenominator := by
  unfold routeTStripDenominator
  have hroute : 0 < routeTRouteStripScale := by
    norm_num [routeTRouteStripScale]
  have hderivative : 0 < routeTDerivativeStripScale := by
    unfold routeTDerivativeStripScale
    exact Nat.mul_pos (by norm_num) (pow_pos (by norm_num) 566)
  have hthreshold : 0 < routeTThresholdStripScale := by
    unfold routeTThresholdStripScale
    have hcentre : 0 < routeTLogCentreExponent := by
      norm_num [routeTLogCentreExponent]
    have hC : 0 < routeTLogReceiverDegreeNineConstant + 1 := by omega
    exact Nat.mul_pos hcentre hC
  exact Nat.mul_pos (Nat.mul_pos hroute hderivative) hthreshold

theorem routeTStripDenominator_ge_route :
    routeTRouteStripScale ≤ routeTStripDenominator := by
  have hd : 0 < routeTDerivativeStripScale := by
    unfold routeTDerivativeStripScale
    exact Nat.mul_pos (by norm_num) (pow_pos (by norm_num) 566)
  have hh : 0 < routeTThresholdStripScale := by
    unfold routeTThresholdStripScale
    exact Nat.mul_pos (by norm_num [routeTLogCentreExponent]) (by omega)
  unfold routeTStripDenominator
  exact (Nat.le_mul_of_pos_right _ hd).trans (Nat.le_mul_of_pos_right _ hh)

theorem routeTStripDenominator_ge_derivative :
    routeTDerivativeStripScale ≤ routeTStripDenominator := by
  have hr : 0 < routeTRouteStripScale := by norm_num [routeTRouteStripScale]
  have hh : 0 < routeTThresholdStripScale := by
    unfold routeTThresholdStripScale
    exact Nat.mul_pos (by norm_num [routeTLogCentreExponent]) (by omega)
  unfold routeTStripDenominator
  calc
    routeTDerivativeStripScale ≤ routeTDerivativeStripScale * routeTRouteStripScale :=
      Nat.le_mul_of_pos_right _ hr
    _ = routeTRouteStripScale * routeTDerivativeStripScale := Nat.mul_comm _ _
    _ ≤ (routeTRouteStripScale * routeTDerivativeStripScale) *
        routeTThresholdStripScale := Nat.le_mul_of_pos_right _ hh

theorem routeTStripDenominator_ge_threshold :
    routeTThresholdStripScale ≤ routeTStripDenominator := by
  have hr : 0 < routeTRouteStripScale := by norm_num [routeTRouteStripScale]
  have hd : 0 < routeTDerivativeStripScale := by
    unfold routeTDerivativeStripScale
    exact Nat.mul_pos (by norm_num) (pow_pos (by norm_num) 566)
  calc
    routeTThresholdStripScale ≤ routeTThresholdStripScale * routeTRouteStripScale :=
      Nat.le_mul_of_pos_right _ hr
    _ ≤ (routeTThresholdStripScale * routeTRouteStripScale) *
        routeTDerivativeStripScale := Nat.le_mul_of_pos_right _ hd
    _ = routeTStripDenominator := by
      unfold routeTStripDenominator
      calc
        (routeTThresholdStripScale * routeTRouteStripScale) *
            routeTDerivativeStripScale =
          routeTThresholdStripScale *
            (routeTRouteStripScale * routeTDerivativeStripScale) := Nat.mul_assoc _ _ _
        _ = (routeTRouteStripScale * routeTDerivativeStripScale) *
            routeTThresholdStripScale := Nat.mul_comm _ _

theorem routeTStripWidth_pos (V : ℕ) : 0 < routeTStripWidth V := by
  unfold routeTStripWidth
  have hnat : 0 < routeTStripDenominator * (V + 1) ^ 9 :=
    Nat.mul_pos routeTStripDenominator_pos (pow_pos (by omega) 9)
  have hreal : (0 : ℝ) < (routeTStripDenominator * (V + 1) ^ 9 : ℕ) := by
    exact_mod_cast hnat
  exact one_div_pos.mpr hreal

theorem routeTStripWidth_lt_one (V : ℕ) : routeTStripWidth V < 1 := by
  have hden : (1 : ℝ) < (routeTStripDenominator * (V + 1) ^ 9 : ℕ) := by
    have hD : 2 ≤ routeTStripDenominator := by
      exact (by norm_num [routeTRouteStripScale] : 2 ≤ routeTRouteStripScale).trans
        routeTStripDenominator_ge_route
    have hP : 1 ≤ (V + 1) ^ 9 := Nat.one_le_pow _ _ (by omega)
    have hmul : 2 ≤ routeTStripDenominator * (V + 1) ^ 9 := by
      calc
        2 = 2 * 1 := (Nat.mul_one 2).symm
        _ ≤ routeTStripDenominator * (V + 1) ^ 9 := Nat.mul_le_mul hD hP
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hmul)
  unfold routeTStripWidth
  simpa only [one_div_one] using
    (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hden)

theorem routeTStripAbscissa_pos (V : ℕ) : 0 < routeTStripAbscissa V := by
  unfold routeTStripAbscissa
  linarith [routeTStripWidth_lt_one V]

theorem routeTStripAbscissa_lt_one (V : ℕ) : routeTStripAbscissa V < 1 := by
  unfold routeTStripAbscissa
  linarith [routeTStripWidth_pos V]

theorem one_sub_routeTStripAbscissa (V : ℕ) :
    1 - routeTStripAbscissa V = routeTStripWidth V := by
  unfold routeTStripAbscissa
  ring

/-- Canonical width is inside the reciprocal-quartic Route-T strip. -/
theorem routeTStripWidth_route_condition {V : ℕ} (hV : 1 ≤ V) :
    2 * routeTStripWidth V ≤
      1 / (5000000000000000 * (V : ℝ) ^ 4) := by
  have hP : V ^ 4 ≤ (V + 1) ^ 9 := by
    calc
      V ^ 4 ≤ (V + 1) ^ 4 := Nat.pow_le_pow_left (Nat.le_succ V) 4
      _ ≤ (V + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have hnat : 2 * 5000000000000000 * V ^ 4 ≤
      routeTStripDenominator * (V + 1) ^ 9 := by
    have hD : 10000000000000000 ≤ routeTStripDenominator := by
      simpa only [routeTRouteStripScale] using routeTStripDenominator_ge_route
    calc
      2 * 5000000000000000 * V ^ 4 = 10000000000000000 * V ^ 4 := by norm_num
      _ ≤ 10000000000000000 * (V + 1) ^ 9 := Nat.mul_le_mul_left _ hP
      _ ≤ routeTStripDenominator * (V + 1) ^ 9 :=
        Nat.mul_le_mul_right ((V + 1) ^ 9) hD
  have hden : (0 : ℝ) < (routeTStripDenominator * (V + 1) ^ 9 : ℕ) := by
    exact_mod_cast Nat.mul_pos routeTStripDenominator_pos (pow_pos (by omega) 9)
  have hq : (0 : ℝ) < 5000000000000000 * (V : ℝ) ^ 4 := by
    have : (0 : ℝ) < V := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hV)
    positivity
  unfold routeTStripWidth
  rw [mul_one_div]
  rw [div_le_div_iff₀ hden hq]
  have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, one_mul, mul_assoc] using hcast

/-- Canonical width is inside the fixed derivative-test strip. -/
theorem routeTStripWidth_derivative_condition (V : ℕ) :
    routeTStripWidth V ≤ 1 / (3 * (2 : ℝ) ^ (566 : ℕ)) := by
  have hfactor : 3 * 2 ^ (566 : ℕ) ≤ routeTStripDenominator * (V + 1) ^ 9 := by
    have hP : 1 ≤ (V + 1) ^ 9 := Nat.one_le_pow _ _ (by omega)
    have hD : 3 * 2 ^ (566 : ℕ) ≤ routeTStripDenominator := by
      simpa only [routeTDerivativeStripScale] using routeTStripDenominator_ge_derivative
    calc
      3 * 2 ^ (566 : ℕ) ≤ routeTStripDenominator := hD
      _ = routeTStripDenominator * 1 := (Nat.mul_one _).symm
      _ ≤ routeTStripDenominator * (V + 1) ^ 9 := Nat.mul_le_mul_left _ hP
  have hleft : (0 : ℝ) < 3 * (2 : ℝ) ^ (566 : ℕ) := by positivity
  unfold routeTStripWidth
  apply one_div_le_one_div_of_le hleft
  exact_mod_cast hfactor

theorem routeTGlobalExponent_le_stripScale (V : ℕ) :
    routeTGlobalExponent V ≤ routeTStripDenominator * (V + 1) ^ 9 := by
  have hP : 1 ≤ (V + 1) ^ 9 := Nat.one_le_pow _ _ (by omega)
  have hmoment : routeTGlobalMoment V ≤
      (routeTLogReceiverDegreeNineConstant + 1) * (V + 1) ^ 9 := by
    unfold routeTGlobalMoment
    calc
      routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1 ≤
          routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + (V + 1) ^ 9 :=
        Nat.add_le_add_left hP _
      _ = (routeTLogReceiverDegreeNineConstant + 1) * (V + 1) ^ 9 := by ring
  have hthreshold : routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant + 1) ≤ routeTStripDenominator := by
    simpa only [routeTThresholdStripScale] using routeTStripDenominator_ge_threshold
  unfold routeTGlobalExponent
  calc
    routeTLogCentreExponent * routeTGlobalMoment V ≤
        routeTLogCentreExponent *
          ((routeTLogReceiverDegreeNineConstant + 1) * (V + 1) ^ 9) :=
      Nat.mul_le_mul_left _ hmoment
    _ = (routeTLogCentreExponent *
          (routeTLogReceiverDegreeNineConstant + 1)) * (V + 1) ^ 9 := by ring
    _ ≤ routeTStripDenominator * (V + 1) ^ 9 :=
      Nat.mul_le_mul_right ((V + 1) ^ 9) hthreshold

theorem routeTGlobalStart_rpow_width_le_two (V : ℕ) :
    (routeTGlobalStart V : ℝ) ^ (routeTStripWidth V) ≤ 2 := by
  have hE := routeTGlobalExponent_le_stripScale V
  have hden : (0 : ℝ) < (routeTStripDenominator * (V + 1) ^ 9 : ℕ) := by
    exact_mod_cast Nat.mul_pos routeTStripDenominator_pos (pow_pos (by omega) 9)
  have hexp : (routeTGlobalExponent V : ℝ) * routeTStripWidth V ≤ 1 := by
    unfold routeTStripWidth
    rw [mul_one_div]
    exact (div_le_one hden).2 (by exact_mod_cast hE)
  have hcast : (routeTGlobalStart V : ℝ) =
      (2 : ℝ) ^ (routeTGlobalExponent V : ℕ) := by
    simp only [routeTGlobalStart, Nat.cast_pow, Nat.cast_ofNat]
  rw [hcast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (2 : ℝ) ^ ((routeTGlobalExponent V : ℝ) * routeTStripWidth V) ≤
        (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = 2 := Real.rpow_one 2

theorem routeTGlobalStart_factorial (V : ℕ) :
    Nat.factorial 565 ≤ routeTGlobalStart V + 1 := by
  have hfac : Nat.factorial 565 ≤ 2 ^ (565 * 565) := factorial_le_two_pow_sq 565
  have hCbig : 565 * 565 ≤
      routeTLogCentreExponent * routeTLogReceiverDegreeNineConstant := by
    unfold routeTLogReceiverDegreeNineConstant
    norm_num [routeTLogCentreExponent, routeTLogGrowthOrderConstant,
      routeTLogGrowthStepsConstant]
    omega
  have hP : 1 ≤ (V + 1) ^ 9 := Nat.one_le_pow _ _ (by omega)
  have hE : 565 * 565 ≤ routeTGlobalExponent V := by
    unfold routeTGlobalExponent routeTGlobalMoment
    calc
      565 * 565 ≤ routeTLogCentreExponent * routeTLogReceiverDegreeNineConstant := hCbig
      _ ≤ routeTLogCentreExponent *
          (routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1) := by
        apply Nat.mul_le_mul_left
        calc
          routeTLogReceiverDegreeNineConstant =
              routeTLogReceiverDegreeNineConstant * 1 := (Nat.mul_one _).symm
          _ ≤ routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 :=
            Nat.mul_le_mul_left _ hP
          _ ≤ routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1 := Nat.le_succ _
  exact hfac.trans ((Nat.pow_le_pow_right (by omega) hE).trans
    (Nat.le_succ (routeTGlobalStart V)))

/-- The explicit head at canonical width is polynomial in the tenth-root shell. -/
theorem routeTGlobalHead_le (V : ℕ) :
    1 + ((routeTGlobalStart V : ℝ) ^
        (1 - routeTStripAbscissa V) - 1) /
          (1 - routeTStripAbscissa V) +
        (routeTGlobalStart V : ℝ) ^ (-routeTStripAbscissa V) ≤
      2 + (routeTStripDenominator * (V + 1) ^ 9 : ℕ) := by
  have hwidth := routeTStripWidth_pos V
  have hpow := routeTGlobalStart_rpow_width_le_two V
  have hA1 : (1 : ℝ) ≤ routeTGlobalStart V := by
    exact_mod_cast Nat.one_le_two_pow
  have hsigma := routeTStripAbscissa_pos V
  have hneg : -routeTStripAbscissa V ≤ 0 := by linarith
  have hlast : (routeTGlobalStart V : ℝ) ^ (-routeTStripAbscissa V) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hA1 hneg
  have hquot : ((routeTGlobalStart V : ℝ) ^ (routeTStripWidth V) - 1) /
      routeTStripWidth V ≤ 1 / routeTStripWidth V := by
    exact div_le_div_of_nonneg_right (by linarith) hwidth.le
  have hinv : 1 / routeTStripWidth V =
      (routeTStripDenominator * (V + 1) ^ 9 : ℕ) := by
    unfold routeTStripWidth
    have hden : (0 : ℝ) < (routeTStripDenominator * (V + 1) ^ 9 : ℕ) := by
      exact_mod_cast Nat.mul_pos routeTStripDenominator_pos (pow_pos (by omega) 9)
    field_simp
  rw [one_sub_routeTStripAbscissa]
  rw [hinv] at hquot
  linarith

def routeTGlobalBlocks (t : ℝ) : ℕ :=
  topExponent t - routeTGlobalExponent (routeTGlobalShell t)

private theorem two_pow_eq_two_mul_pred {R : ℕ} (hR : 1 ≤ R) :
    2 ^ R = 2 * 2 ^ (R - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, (Nat.sub_add_cancel hR).symm⟩
  rw [pow_succ]
  exact Nat.mul_comm _ _

theorem routeTGlobalBlocks_pos {t : ℝ}
    (hdepth : routeTGlobalExponent (routeTGlobalShell t) + 1 ≤ topExponent t) :
    1 ≤ routeTGlobalBlocks t := by
  unfold routeTGlobalBlocks
  omega

theorem routeTGlobalTruncation_eq {t : ℝ}
    (hdepth : routeTGlobalExponent (routeTGlobalShell t) ≤ topExponent t) :
    routeTGlobalStart (routeTGlobalShell t) * 2 ^ routeTGlobalBlocks t =
      2 ^ topExponent t := by
  have hsum : routeTGlobalExponent (routeTGlobalShell t) +
      (topExponent t - routeTGlobalExponent (routeTGlobalShell t)) = topExponent t :=
    Nat.add_sub_of_le hdepth
  calc
    routeTGlobalStart (routeTGlobalShell t) * 2 ^ routeTGlobalBlocks t =
        2 ^ routeTGlobalExponent (routeTGlobalShell t) *
          2 ^ (topExponent t - routeTGlobalExponent (routeTGlobalShell t)) := rfl
    _ = 2 ^ (routeTGlobalExponent (routeTGlobalShell t) +
          (topExponent t - routeTGlobalExponent (routeTGlobalShell t))) := (pow_add _ _ _).symm
    _ = 2 ^ topExponent t := congrArg (fun e : ℕ => 2 ^ e) hsum

/-- The last dyadic block of the canonical truncation remains inside the derivative lower window. -/
theorem routeTGlobalTruncation_low {t : ℝ} (ht8 : 8 * Real.pi ≤ t)
    (hdepth : routeTGlobalExponent (routeTGlobalShell t) + 1 ≤ topExponent t) :
    8 * Real.pi *
      (((routeTGlobalStart (routeTGlobalShell t) *
          2 ^ (routeTGlobalBlocks t - 1) + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) ≤ t := by
  let A := routeTGlobalStart (routeTGlobalShell t)
  let R := routeTGlobalBlocks t
  let T := topExponent t
  have hA : 1 ≤ A := by
    dsimp only [A, routeTGlobalStart]
    exact Nat.one_le_two_pow
  have hR : 1 ≤ R := by simpa only [R] using routeTGlobalBlocks_pos hdepth
  have hpowR : 2 ^ R = 2 * 2 ^ (R - 1) := two_pow_eq_two_mul_pred hR
  have hbase : A * 2 ^ (R - 1) + 1 ≤ A * 2 ^ R := by
    rw [hpowR]
    have hpos : 1 ≤ A * 2 ^ (R - 1) := by
      calc
        1 = 1 * 1 := (Nat.one_mul 1).symm
        _ ≤ A * 2 ^ (R - 1) := Nat.mul_le_mul hA Nat.one_le_two_pow
    calc
      A * 2 ^ (R - 1) + 1 ≤
          A * 2 ^ (R - 1) + A * 2 ^ (R - 1) := Nat.add_le_add_left hpos _
      _ = A * (2 * 2 ^ (R - 1)) := by ring
  have htopNat : A * 2 ^ R = 2 ^ T := by
    simpa only [A, R, T] using routeTGlobalTruncation_eq (t := t) (by omega)
  have hbaseTop : A * 2 ^ (R - 1) + 1 ≤ 2 ^ T := hbase.trans_eq htopNat
  have hcast : ((A * 2 ^ (R - 1) + 1 : ℕ) : ℝ) ≤ ((2 ^ T : ℕ) : ℝ) := by
    exact_mod_cast hbaseTop
  have hrpow : ((A * 2 ^ (R - 1) + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤
      ((2 ^ T : ℕ) : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcast (by norm_num)
  have htopShape : ((2 ^ T : ℕ) : ℝ) ^ ((1 : ℝ) / 3) =
      (2 : ℝ) ^ ((T : ℝ) / 3) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2 : ℝ) T,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply congrArg (fun e : ℝ => (2 : ℝ) ^ e)
    ring
  have htop := topExponent_bound ht8
  have hstep : 8 * Real.pi *
      ((A * 2 ^ (R - 1) + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤
        8 * Real.pi * ((2 ^ T : ℕ) : ℝ) ^ ((1 : ℝ) / 3) :=
    mul_le_mul_of_nonneg_left hrpow (by positivity)
  rw [htopShape] at hstep
  exact hstep.trans (by simpa only [T] using htop)

end

end RHTower.Sieve
