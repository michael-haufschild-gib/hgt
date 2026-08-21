import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryAmplitude
import GaloisForLFunctions.RHTower.Sieve.MaynardAdaptiveParityBadMeasure

noncomputable section
namespace RHTower.Sieve

open MeasureTheory Filter

/-- Exact scale-distortion exponent forced by the trivial-count amplitude boundary. -/
def routeTTrivialBoundaryDistortionExponent : ℝ :=
  (1 - routeTGapMomentNu) / 2

theorem routeTTrivialBoundaryDistortionExponent_pos :
    0 < routeTTrivialBoundaryDistortionExponent := by
  unfold routeTTrivialBoundaryDistortionExponent
  linarith [routeTGapMomentNu_lt_half]

/-- A negative power with lower exponent `-theta` pays at most `kappa^theta` when its base is
replaced by a comparable larger scale. -/
theorem negative_rpow_le_distortion
    {D X kappa p theta : ℝ}
    (hX : 0 < X) (hkappa : 1 ≤ kappa)
    (hcomparable : X ≤ kappa * D)
    (hpLower : -theta ≤ p) (hpUpper : p ≤ 0) :
    D ^ p ≤ kappa ^ theta * X ^ p := by
  have hkappaPos : 0 < kappa := zero_lt_one.trans_le hkappa
  have hquotient : X / kappa ≤ D := by
    rw [div_le_iff₀ hkappaPos]
    simpa only [mul_comm] using hcomparable
  have hreverse : D ^ p ≤ (X / kappa) ^ p :=
    Real.rpow_le_rpow_of_nonpos (div_pos hX hkappaPos) hquotient hpUpper
  have hkappaPower : kappa ^ (-p) ≤ kappa ^ theta :=
    Real.rpow_le_rpow_of_exponent_le hkappa (by linarith)
  calc
    D ^ p ≤ (X / kappa) ^ p := hreverse
    _ = X ^ p * kappa ^ (-p) := by
      rw [Real.div_rpow hX.le hkappaPos.le, div_eq_mul_inv,
        Real.rpow_neg hkappaPos.le]
    _ ≤ X ^ p * kappa ^ theta :=
      mul_le_mul_of_nonneg_left hkappaPower (Real.rpow_nonneg hX.le _)
    _ = kappa ^ theta * X ^ p := mul_comm _ _

/-- Receiver-scale adaptive envelope valid from the exact Route-T trivial-count boundary. -/
theorem routeTAdaptiveCellAmplitude_threshold_le_receiverScale_envelope_trivialBoundary
    (L X k : ℕ) (hk : 0 < k) (hX : 1 < X) {N V Y kappa : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ))
    (hV : 0 < V) (hY : 0 < Y) (hkappa : 1 ≤ kappa)
    (hSupport : (X : ℝ) ≤ Y)
    (hLowerComparable : Y ≤ kappa * (N / (2 ^ (2 * k) : ℝ)))
    (halphaLower : (1 + routeTGapMomentNu) / 2 ≤
      routeTAdaptiveCellAmplitude L X k N V) :
    V ≤ heathBrownEligibleBoxCost L X k *
      kappa ^ routeTTrivialBoundaryDistortionExponent *
      Y ^ (routeTAdaptiveCellAmplitude L X k N V - 1) := by
  let D : ℝ := N / (2 ^ (2 * k) : ℝ)
  let C : ℝ := heathBrownEligibleBoxCost L X k
  let W : ℝ := V / C
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X k N V
  let theta : ℝ := routeTTrivialBoundaryDistortionExponent
  have hC : 0 < C := heathBrownEligibleBoxCost_pos L X k hk
  have hW : 0 < W := div_pos hV hC
  have hXReal : (1 : ℝ) < X := by exact_mod_cast hX
  have hVC : V = C * W := by dsimp only [W]; field_simp
  by_cases hbelow : V ≤ C
  · have hWle : W ≤ 1 := (div_le_one hC).2 hbelow
    have halphaUpper : alpha ≤ 1 := by
      have hlogW : Real.log W ≤ 0 := Real.log_nonpos hW.le hWle
      have hlogD : 0 < Real.log D := Real.log_pos (by simpa only [D] using hD)
      dsimp only [alpha, routeTAdaptiveCellAmplitude]
      rw [if_pos hbelow]
      exact add_le_of_nonpos_right
        (div_nonpos_of_nonpos_of_nonneg hlogW hlogD.le)
    have hexact : D ^ (alpha - 1) = W := by
      dsimp only [alpha, routeTAdaptiveCellAmplitude]
      rw [if_pos hbelow]
      exact rpow_maynardAmplitude_sub_abscissa
        (by simpa only [D] using hD) hW
    have hpLower : -theta ≤ alpha - 1 := by
      dsimp only [theta, routeTTrivialBoundaryDistortionExponent, alpha] at ⊢
      linarith
    have henvelope : D ^ (alpha - 1) ≤
        kappa ^ theta * Y ^ (alpha - 1) :=
      negative_rpow_le_distortion hY hkappa
        (by simpa only [D] using hLowerComparable) hpLower (by linarith)
    calc
      V = C * W := hVC
      _ = C * D ^ (alpha - 1) := by rw [hexact]
      _ ≤ C * (kappa ^ theta * Y ^ (alpha - 1)) :=
        mul_le_mul_of_nonneg_left henvelope hC.le
      _ = C * kappa ^ theta * Y ^ (alpha - 1) := by ring
      _ = heathBrownEligibleBoxCost L X k *
          kappa ^ routeTTrivialBoundaryDistortionExponent *
          Y ^ (routeTAdaptiveCellAmplitude L X k N V - 1) := rfl
  · have hCV : C < V := lt_of_not_ge hbelow
    have hWone : 1 ≤ W := (one_le_div hC).2 hCV.le
    have halphaUpper : 1 ≤ alpha := by
      dsimp only [alpha, routeTAdaptiveCellAmplitude]
      rw [if_neg hbelow]
      apply le_maynardAmplitude_of_rpow_le hXReal
      simpa only [W, sub_self, Real.rpow_zero] using hWone
    have hexact : (X : ℝ) ^ (alpha - 1) = W := by
      dsimp only [alpha, routeTAdaptiveCellAmplitude]
      rw [if_neg hbelow]
      exact rpow_maynardAmplitude_sub_abscissa hXReal hW
    have hsupportPower : (X : ℝ) ^ (alpha - 1) ≤ Y ^ (alpha - 1) :=
      Real.rpow_le_rpow (by positivity) hSupport (by linarith)
    have hkappaPower : 1 ≤ kappa ^ theta :=
      Real.one_le_rpow hkappa (by
        dsimp only [theta]
        exact routeTTrivialBoundaryDistortionExponent_pos.le)
    have hYPower : 0 ≤ Y ^ (alpha - 1) := Real.rpow_nonneg hY.le _
    have hdistort : Y ^ (alpha - 1) ≤ kappa ^ theta * Y ^ (alpha - 1) := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hkappaPower hYPower)
    calc
      V = C * W := hVC
      _ = C * (X : ℝ) ^ (alpha - 1) := by rw [hexact]
      _ ≤ C * Y ^ (alpha - 1) :=
        mul_le_mul_of_nonneg_left hsupportPower hC.le
      _ ≤ C * (kappa ^ theta * Y ^ (alpha - 1)) :=
        mul_le_mul_of_nonneg_left hdistort hC.le
      _ = C * kappa ^ theta * Y ^ (alpha - 1) := by ring
      _ = heathBrownEligibleBoxCost L X k *
          kappa ^ routeTTrivialBoundaryDistortionExponent *
          Y ^ (routeTAdaptiveCellAmplitude L X k N V - 1) := rfl

/-- Squared receiver envelope at the exact trivial-count boundary. -/
theorem routeTAdaptiveCellAmplitude_threshold_sq_le_receiverScale_envelope_trivialBoundary
    (L X k : ℕ) (hk : 0 < k) (hX : 1 < X) {N V Y kappa : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ))
    (hV : 0 < V) (hY : 0 < Y) (hkappa : 1 ≤ kappa)
    (hSupport : (X : ℝ) ≤ Y)
    (hLowerComparable : Y ≤ kappa * (N / (2 ^ (2 * k) : ℝ)))
    (halphaLower : (1 + routeTGapMomentNu) / 2 ≤
      routeTAdaptiveCellAmplitude L X k N V) :
    V ^ 2 ≤ (heathBrownEligibleBoxCost L X k) ^ 2 *
      kappa ^ (1 - routeTGapMomentNu) *
      Y ^ (2 * routeTAdaptiveCellAmplitude L X k N V - 2) := by
  let C : ℝ := heathBrownEligibleBoxCost L X k
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X k N V
  let theta : ℝ := routeTTrivialBoundaryDistortionExponent
  have henvelope :=
    routeTAdaptiveCellAmplitude_threshold_le_receiverScale_envelope_trivialBoundary
      L X k hk hX hD hV hY hkappa hSupport hLowerComparable halphaLower
  have hsquare : V ^ 2 ≤
      (C * kappa ^ theta * Y ^ (alpha - 1)) ^ 2 :=
    pow_le_pow_left₀ hV.le (by simpa only [C, alpha, theta] using henvelope) 2
  calc
    V ^ 2 ≤ (C * kappa ^ theta * Y ^ (alpha - 1)) ^ 2 := hsquare
    _ = C ^ 2 * kappa ^ (1 - routeTGapMomentNu) *
        Y ^ (2 * alpha - 2) := by
      rw [mul_pow, mul_pow,
        ← Real.rpow_natCast (kappa ^ theta) 2,
        ← Real.rpow_mul (zero_le_one.trans hkappa),
        ← Real.rpow_natCast (Y ^ (alpha - 1)) 2,
        ← Real.rpow_mul hY.le]
      congr 1
      · dsimp only [theta, routeTTrivialBoundaryDistortionExponent]
        ring_nf
      · ring_nf
    _ = (heathBrownEligibleBoxCost L X k) ^ 2 *
        kappa ^ (1 - routeTGapMomentNu) *
        Y ^ (2 * routeTAdaptiveCellAmplitude L X k N V - 2) := rfl

/-- Universal critical cancellation with an arbitrary nonnegative amplitude-envelope prefactor. -/
theorem routeT_adaptive_spatial_second_count_cancellation_factor
    {P x X V R T alpha : ℝ}
    (hP : 0 ≤ P) (hx : 0 ≤ x) (hX : 0 < X)
    (hR : 0 ≤ R) (hxX : x ≤ X)
    (henvelope : V ^ 2 ≤ P * X ^ (2 * alpha - 2))
    (hsecond : R ≤ T * X ^ (1 + routeTGapMomentNu - 2 * alpha)) :
    x * V ^ 2 * R ≤ P * T * X ^ routeTGapMomentNu := by
  have hXa : 0 ≤ X ^ (2 * alpha - 2) := Real.rpow_nonneg hX.le _
  have hpower : X * X ^ (2 * alpha - 2) *
      X ^ (1 + routeTGapMomentNu - 2 * alpha) = X ^ routeTGapMomentNu := by
    calc
      X * X ^ (2 * alpha - 2) *
          X ^ (1 + routeTGapMomentNu - 2 * alpha) =
        X ^ (1 : ℝ) * X ^ (2 * alpha - 2) *
          X ^ (1 + routeTGapMomentNu - 2 * alpha) := by rw [Real.rpow_one]
      _ = X ^ ((1 : ℝ) + (2 * alpha - 2)) *
          X ^ (1 + routeTGapMomentNu - 2 * alpha) := by
        congr 1
        exact (Real.rpow_add hX _ _).symm
      _ = X ^ (((1 : ℝ) + (2 * alpha - 2)) +
          (1 + routeTGapMomentNu - 2 * alpha)) :=
        (Real.rpow_add hX _ _).symm
      _ = X ^ routeTGapMomentNu := by
        congr 1
        ring
  calc
    x * V ^ 2 * R ≤ x * (P * X ^ (2 * alpha - 2)) * R :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left henvelope hx) hR
    _ ≤ X * (P * X ^ (2 * alpha - 2)) * R :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hxX (mul_nonneg hP hXa)) hR
    _ ≤ X * (P * X ^ (2 * alpha - 2)) *
        (T * X ^ (1 + routeTGapMomentNu - 2 * alpha)) :=
      mul_le_mul_of_nonneg_left hsecond
        (mul_nonneg hX.le (mul_nonneg hP hXa))
    _ = P * T * (X * X ^ (2 * alpha - 2) *
        X ^ (1 + routeTGapMomentNu - 2 * alpha)) := by ring
    _ = P * T * X ^ routeTGapMomentNu := by rw [hpower]

/-- Exact adaptive second-count cancellation from the true trivial-count boundary. -/
theorem routeTAdaptiveCellAmplitude_receiverScale_second_count_cancellation_trivialBoundary
    (L X k : ℕ) (hk : 0 < k) (hX : 1 < X)
    {N V Y kappa R T : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ)) (hV : 0 < V)
    (hY : 0 < Y) (hkappa : 1 ≤ kappa)
    (hSupport : (X : ℝ) ≤ Y)
    (hLowerComparable : Y ≤ kappa * (N / (2 ^ (2 * k) : ℝ)))
    (hPhysical : N ≤ Y) (hR : 0 ≤ R)
    (halphaLower : (1 + routeTGapMomentNu) / 2 ≤
      routeTAdaptiveCellAmplitude L X k N V)
    (hsecond : R ≤ T * Y ^
      (1 + routeTGapMomentNu - 2 * routeTAdaptiveCellAmplitude L X k N V)) :
    N * V ^ 2 * R ≤
      (heathBrownEligibleBoxCost L X k) ^ 2 *
        kappa ^ (1 - routeTGapMomentNu) * T * Y ^ routeTGapMomentNu := by
  have hN : 0 ≤ N := by
    have hden : 0 < (2 ^ (2 * k) : ℝ) := by positivity
    have hquot : 0 < N / (2 ^ (2 * k) : ℝ) := zero_lt_one.trans hD
    rcases div_pos_iff.mp hquot with hpos | hneg
    · exact hpos.1.le
    · exact False.elim ((not_lt_of_ge hden.le) hneg.2)
  exact routeT_adaptive_spatial_second_count_cancellation_factor
    (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hkappa) _))
      hN hY hR hPhysical
      (routeTAdaptiveCellAmplitude_threshold_sq_le_receiverScale_envelope_trivialBoundary
        L X k hk hX hD hV hY hkappa hSupport hLowerComparable halphaLower)
      hsecond

/-- Canonical Route-T packet cancellation from the exact trivial-count amplitude boundary. -/
theorem eventually_routeTPrimeGapPacket_adaptive_second_count_cancellation_sixty_trivialBoundary :
    ∀ᶠ T0 : ℝ in Filter.atTop,
      ∀ {L : ℕ} {V R H : ℝ},
      0 < V → 0 ≤ R →
      (1 + routeTGapMomentNu) / 2 ≤
        routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T0) 60
          (routeTPrimeGapPacketBase T0) V →
      R ≤ H * (T0 ^ (8 / 5 : ℝ)) ^
        (1 + routeTGapMomentNu -
          2 * routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T0) 60
            (routeTPrimeGapPacketBase T0) V) →
      routeTPrimeGapPacketBase T0 * V ^ 2 * R ≤
        (heathBrownEligibleBoxCost L (routeTPrimeGapPacketSupport T0) 60) ^ 2 *
          (4 * (2 ^ 120 : ℝ)) ^ (1 - routeTGapMomentNu) * H *
            (T0 ^ (8 / 5 : ℝ)) ^ routeTGapMomentNu := by
  have hbaseTop : Filter.Tendsto routeTPrimeGapPacketBase
      Filter.atTop Filter.atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T0 : ℝ in Filter.atTop,
      (2 ^ 120 : ℝ) + 1 ≤ routeTPrimeGapPacketBase T0 :=
    hbaseTop.eventually_ge_atTop ((2 ^ 120 : ℝ) + 1)
  filter_upwards [hbaseLarge, Filter.eventually_gt_atTop (0 : ℝ)] with T0 hbase hT0
  intro L V R H hV hR halpha hsecond
  let N : ℝ := routeTPrimeGapPacketBase T0
  let X : ℕ := routeTPrimeGapPacketSupport T0
  let Y : ℝ := T0 ^ (8 / 5 : ℝ)
  have hN : 0 < N := by dsimp only [N]; linarith
  have hceilLower : 3 * N ≤ (X : ℝ) := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.le_ceil _
  have hceilUpper : (X : ℝ) < 3 * N + 1 := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.ceil_lt_add_one (by positivity)
  have hX : 1 < X := by
    have hXreal : (1 : ℝ) < X := by linarith
    exact_mod_cast hXreal
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have hYeq : Y = 4 * N := by
    dsimp only [Y, N, routeTPrimeGapPacketBase]
    field_simp
  have hSupport : (X : ℝ) ≤ Y := by
    rw [hYeq]
    linarith
  have hD : 1 < N / (2 ^ 120 : ℝ) := by
    apply (one_lt_div (by positivity : (0 : ℝ) < 2 ^ 120)).2
    dsimp only [N]
    linarith
  have hkappa : (1 : ℝ) ≤ 4 * (2 ^ 120 : ℝ) := by
    have hp : (1 : ℝ) ≤ 2 ^ 120 := one_le_pow₀ (by norm_num)
    nlinarith
  have hscale :
      (4 * (2 ^ 120 : ℝ)) * (N / (2 ^ (2 * 60) : ℝ)) = 4 * N := by
    norm_num only [Nat.reduceMul]
    field_simp
    ring
  have hLowerComparable : Y ≤
      (4 * (2 ^ 120 : ℝ)) * (N / (2 ^ (2 * 60) : ℝ)) := by
    rw [hYeq, hscale]
  have hPhysical : N ≤ Y := by rw [hYeq]; linarith
  simpa only [N, X, Y] using
    (routeTAdaptiveCellAmplitude_receiverScale_second_count_cancellation_trivialBoundary
      L X 60 (by norm_num) hX (by simpa only [Nat.reduceMul] using hD) hV
      hY hkappa hSupport hLowerComparable hPhysical hR halpha hsecond)

/-- Squared selector cost with exact trivial-boundary scale distortion is still absorbed by every
positive Route-T power. -/
theorem eventually_heathBrownEligibleBoxCost_sq_sixty_trivialBoundary_absorbed
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ L X : ℕ, 1 ≤ X → L ≤ X → (X : ℝ) ≤ T ^ (8 / 5 : ℝ) →
        (heathBrownEligibleBoxCost L X 60) ^ 2 *
          (4 * (2 ^ 120 : ℝ)) ^ (1 - routeTGapMomentNu) ≤ T ^ eta := by
  let eps : ℝ := eta / 2
  let kappa : ℝ := 4 * (2 ^ 120 : ℝ)
  let extra : ℝ := 1 / 2 - routeTGapMomentNu
  have heps : 0 < eps := by dsimp only [eps]; linarith
  have hcost := eventually_heathBrownEligibleBoxCost_sq_sixty_routeT_absorbed heps
  have hconst : ∀ᶠ T : ℝ in Filter.atTop, kappa ^ extra ≤ T ^ eps :=
    (tendsto_rpow_atTop heps).eventually_ge_atTop (kappa ^ extra)
  filter_upwards [hcost, hconst, Filter.eventually_gt_atTop (0 : ℝ)] with
    T hcostT hconstT hT
  intro L X hX hLX hXscale
  have hkappa : 0 < kappa := by dsimp only [kappa]; positivity
  have hextra0 : 0 ≤ kappa ^ extra := Real.rpow_nonneg hkappa.le _
  have hprod := mul_le_mul (hcostT L X hX hLX hXscale) hconstT
    hextra0 (Real.rpow_nonneg hT.le _)
  calc
    (heathBrownEligibleBoxCost L X 60) ^ 2 *
        (4 * (2 ^ 120 : ℝ)) ^ (1 - routeTGapMomentNu) =
      ((heathBrownEligibleBoxCost L X 60) ^ 2 * kappa ^ (1 / 2 : ℝ)) *
        kappa ^ extra := by
      change (heathBrownEligibleBoxCost L X 60) ^ 2 *
          kappa ^ (1 - routeTGapMomentNu) =
        ((heathBrownEligibleBoxCost L X 60) ^ 2 * kappa ^ (1 / 2 : ℝ)) *
          kappa ^ extra
      rw [show (1 - routeTGapMomentNu : ℝ) = 1 / 2 + extra by
        dsimp only [extra]; ring, Real.rpow_add hkappa]
      ring
    _ ≤ T ^ eps * T ^ eps := hprod
    _ = T ^ (eps + eps) := (Real.rpow_add hT eps eps).symm
    _ = T ^ eta := by
      congr 1
      dsimp only [eps]
      ring

/-- Exact-boundary adaptive cancellation after selector entropy absorption. -/
theorem eventually_routeTPrimeGapPacket_adaptive_second_count_cancellation_absorbed_sixty_trivialBoundary
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T0 : ℝ in Filter.atTop,
      ∀ {L : ℕ} {V R H : ℝ},
      L ≤ routeTPrimeGapPacketSupport T0 → 0 ≤ H → 0 < V → 0 ≤ R →
      (1 + routeTGapMomentNu) / 2 ≤
        routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T0) 60
          (routeTPrimeGapPacketBase T0) V →
      R ≤ H * (T0 ^ (8 / 5 : ℝ)) ^
        (1 + routeTGapMomentNu -
          2 * routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T0) 60
            (routeTPrimeGapPacketBase T0) V) →
      routeTPrimeGapPacketBase T0 * V ^ 2 * R ≤
        T0 ^ eta * H * (T0 ^ (8 / 5 : ℝ)) ^ routeTGapMomentNu := by
  have hcancel :=
    eventually_routeTPrimeGapPacket_adaptive_second_count_cancellation_sixty_trivialBoundary
  have hcost := eventually_heathBrownEligibleBoxCost_sq_sixty_trivialBoundary_absorbed heta
  have hbaseTop : Filter.Tendsto routeTPrimeGapPacketBase
      Filter.atTop Filter.atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T0 : ℝ in Filter.atTop,
      1 ≤ routeTPrimeGapPacketBase T0 := hbaseTop.eventually_ge_atTop 1
  filter_upwards [hcancel, hcost, hbaseLarge, Filter.eventually_gt_atTop (0 : ℝ)] with
    T0 hcancelT hcostT hbase hT0
  intro L V R H hLX hH hV hR halpha hsecond
  let N : ℝ := routeTPrimeGapPacketBase T0
  let X : ℕ := routeTPrimeGapPacketSupport T0
  let Y : ℝ := T0 ^ (8 / 5 : ℝ)
  have hceilLower : 3 * N ≤ (X : ℝ) := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.le_ceil _
  have hX : 1 ≤ X := by
    have hXreal : (1 : ℝ) ≤ X := by linarith
    exact_mod_cast hXreal
  have hYeq : Y = 4 * N := by
    dsimp only [Y, N, routeTPrimeGapPacketBase]
    field_simp
  have hSupport : (X : ℝ) ≤ Y := by
    have hceilUpper : (X : ℝ) < 3 * N + 1 := by
      dsimp only [X, routeTPrimeGapPacketSupport]
      exact Nat.ceil_lt_add_one (by positivity)
    rw [hYeq]
    linarith
  have hcostBound :
      (heathBrownEligibleBoxCost L X 60) ^ 2 *
          (4 * (2 ^ 120 : ℝ)) ^ (1 - routeTGapMomentNu) ≤ T0 ^ eta :=
    hcostT L X hX (by simpa only [X] using hLX) (by simpa only [Y] using hSupport)
  have hmain := hcancelT hV hR halpha hsecond
  have hreceiverNonneg : 0 ≤ H * Y ^ routeTGapMomentNu :=
    mul_nonneg hH (Real.rpow_nonneg (by positivity) _)
  calc
    routeTPrimeGapPacketBase T0 * V ^ 2 * R ≤
        (heathBrownEligibleBoxCost L X 60) ^ 2 *
          (4 * (2 ^ 120 : ℝ)) ^ (1 - routeTGapMomentNu) * H *
            Y ^ routeTGapMomentNu := by
      simpa only [X, Y] using hmain
    _ = ((heathBrownEligibleBoxCost L X 60) ^ 2 *
          (4 * (2 ^ 120 : ℝ)) ^ (1 - routeTGapMomentNu)) *
            (H * Y ^ routeTGapMomentNu) := by ac_rfl
    _ ≤ T0 ^ eta * (H * Y ^ routeTGapMomentNu) :=
      mul_le_mul_of_nonneg_right hcostBound hreceiverNonneg
    _ = T0 ^ eta * H * (T0 ^ (8 / 5 : ℝ)) ^ routeTGapMomentNu := by
      dsimp only [Y]
      ac_rfl

/-- Canonical amplitude-free equation-(111) throughout the full strip beginning at the exact
trivial-count boundary. -/
theorem eventually_volume_routeTPrimeGapPacket_adaptive_parity_forced_second_trivialBoundary
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {q K L cellCount : ℕ} {B : Finset ℕ} {a : ℝ → ℂ}
        {R H D V : ℝ},
      0 < R → 0 < H → 0 < D → 0 < V →
      0 ≤ 1 + 2 * (1 + Real.log cellCount) →
      L ≤ routeTPrimeGapPacketSupport T →
      B ⊆ Finset.range (2 * K) → B ⊆ Finset.range cellCount →
      Continuous a →
      (∀ m ∈ B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖a ((m : ℝ) + u)‖ ≤ 2 * V) →
      (1 + routeTGapMomentNu) / 2 ≤
        routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T) 60
          (routeTPrimeGapPacketBase T) V →
      4 * V * (T ^ (8 / 5 : ℝ)) ^
          (1 - routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T) 60
            (routeTPrimeGapPacketBase T) V) ≤
        (D / 2) * (Real.log T) ^ q →
      IsRouteTMaynardTwoAlternative q
          ((maynardEvenCellFibre B K).card : ℝ) T (T ^ (8 / 5 : ℝ))
          (routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T) 60
            (routeTPrimeGapPacketBase T) V) →
      IsRouteTMaynardTwoAlternative q
          ((maynardOddCellFibre B K).card : ℝ) T (T ^ (8 / 5 : ℝ))
          (routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T) 60
            (routeTPrimeGapPacketBase T) V) →
      (volume.restrict (Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T))).real
          {lambda | D ≤
            ‖maynardFixedAmbientPhysicalDefectPacket B a lambda 1 R H 1‖} ≤
        2 * ((128 *
          (T ^ eta * T * (T ^ (8 / 5 : ℝ)) ^ routeTGapMomentNu) *
          (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2) := by
  have henergy :=
    eventually_routeTPrimeGapPacket_adaptive_second_count_cancellation_absorbed_sixty_trivialBoundary
      heta
  have hbaseTop : Filter.Tendsto routeTPrimeGapPacketBase
      Filter.atTop Filter.atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T : ℝ in Filter.atTop,
      1 ≤ routeTPrimeGapPacketBase T := hbaseTop.eventually_ge_atTop 1
  filter_upwards [henergy, hbaseLarge, Filter.eventually_ge_atTop (1 : ℝ)] with
    T henergyT hbase hT
  intro q K L cellCount B a R H D V hR hH hD hV hcellLog hLX hB hBcell
    ha hsource halpha hthreshold heven hodd
  let Y : ℝ := T ^ (8 / 5 : ℝ)
  let alpha : ℝ := routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T) 60
    (routeTPrimeGapPacketBase T) V
  let countScale : ℝ := T * Y ^ (1 + routeTGapMomentNu - 2 * alpha)
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have hcountScale : 0 ≤ countScale := by
    dsimp only [countScale]
    positivity
  have henergyBound :
      routeTPrimeGapPacketBase T * V ^ 2 * countScale ≤
        T ^ eta * T * Y ^ routeTGapMomentNu := by
    apply henergyT hLX hT0 hV hcountScale
    · simpa only [alpha] using halpha
    · dsimp only [countScale]
      exact le_rfl
  have hmeasure :=
    volume_maynardFixedAmbientPhysicalDefectPacket_large_le_parity_forced_second
      (q := q) (K := K) (B := B) (a := a)
      (x := routeTPrimeGapPacketBase T) (N := 1) (R := R) (H := H)
      (D := D) (V := V) (T := T) (Y := Y) (alpha := alpha)
      (cellCount := cellCount) hbase (by norm_num) hR hH hD hV hT0 hY
      (Real.log_nonneg hT) hcellLog hB hBcell ha hsource
      (by simpa only [Y, alpha] using hthreshold)
      (by simpa only [Y, alpha] using heven)
      (by simpa only [Y, alpha] using hodd)
  have hnumer :
      4 * (2 * routeTPrimeGapPacketBase T) * (4 * V) ^ 2 * countScale *
          (1 + 2 * (1 + Real.log cellCount)) ≤
        128 * (T ^ eta * T * Y ^ routeTGapMomentNu) *
          (1 + 2 * (1 + Real.log cellCount)) := by
    calc
      4 * (2 * routeTPrimeGapPacketBase T) * (4 * V) ^ 2 * countScale *
          (1 + 2 * (1 + Real.log cellCount)) =
        128 * (routeTPrimeGapPacketBase T * V ^ 2 * countScale) *
          (1 + 2 * (1 + Real.log cellCount)) := by ring
      _ ≤ 128 * (T ^ eta * T * Y ^ routeTGapMomentNu) *
          (1 + 2 * (1 + Real.log cellCount)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left henergyBound (by norm_num)) hcellLog
  have hquot :
      (4 * (2 * routeTPrimeGapPacketBase T) * (4 * V) ^ 2 * countScale *
          (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2 ≤
        (128 * (T ^ eta * T * Y ^ routeTGapMomentNu) *
          (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2 :=
    div_le_div_of_nonneg_right hnumer (sq_nonneg (D / 2))
  calc
    (volume.restrict (Set.Icc (routeTPrimeGapPacketBase T)
        (2 * routeTPrimeGapPacketBase T))).real
        {lambda | D ≤
          ‖maynardFixedAmbientPhysicalDefectPacket B a lambda 1 R H 1‖} ≤
      2 * ((4 * (2 * routeTPrimeGapPacketBase T) * (4 * V) ^ 2 * countScale *
        (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2) := by
      simpa only [Y, alpha, countScale] using hmeasure
    _ ≤ 2 * ((128 * (T ^ eta * T * Y ^ routeTGapMomentNu) *
        (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hquot (by norm_num)
    _ = 2 * ((128 *
        (T ^ eta * T * (T ^ (8 / 5 : ℝ)) ^ routeTGapMomentNu) *
        (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2) := by
      dsimp only [Y]

end RHTower.Sieve
