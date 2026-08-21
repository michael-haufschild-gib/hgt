import GaloisForLFunctions.RHTower.Sieve.MaynardAmplitudeLayerExtraction
import GaloisForLFunctions.RHTower.Sieve.MaynardTwoAlternativeGapReceiver
import GaloisForLFunctions.RHTower.Sieve.MaynardPrimeFreeRangePacketCutoffSchedule

/-!
# Scale-covariant envelope for Route T's adaptive amplitude

The physical selected-cell normalization has two branches: sub-unit thresholds are measured at
the lower support edge, while super-unit thresholds are measured at the upper edge.  Comparable
support scales turn both branches into one upper envelope.  Its squared form is the missing scalar
interface between amplitude-sensitive spatial `L²` and the Maynard second-count receiver.
-/

noncomputable section
namespace RHTower.Sieve

/-- A negative real power pays at most a quarter-power distortion when its base is replaced by a
comparable larger scale and the exponent lies in `[-1/4,0]`. -/
theorem negative_rpow_le_quarter_distortion
    {D X kappa p : ℝ}
    (hX : 0 < X) (hkappa : 1 ≤ kappa)
    (hcomparable : X ≤ kappa * D)
    (hpLower : -(1 : ℝ) / 4 ≤ p) (hpUpper : p ≤ 0) :
    D ^ p ≤ kappa ^ (1 / 4 : ℝ) * X ^ p := by
  have hkappaPos : 0 < kappa := lt_of_lt_of_le zero_lt_one hkappa
  have hquotient : X / kappa ≤ D := by
    rw [div_le_iff₀ hkappaPos]
    simpa only [mul_comm] using hcomparable
  have hreverse : D ^ p ≤ (X / kappa) ^ p :=
    Real.rpow_le_rpow_of_nonpos (div_pos hX hkappaPos) hquotient hpUpper
  have hkappaPower : kappa ^ (-p) ≤ kappa ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hkappa (by linarith)
  calc
    D ^ p ≤ (X / kappa) ^ p := hreverse
    _ = X ^ p * kappa ^ (-p) := by
      rw [Real.div_rpow hX.le hkappaPos.le, div_eq_mul_inv,
        Real.rpow_neg hkappaPos.le]
    _ ≤ X ^ p * kappa ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hkappaPower (Real.rpow_nonneg hX.le _)
    _ = kappa ^ (1 / 4 : ℝ) * X ^ p := mul_comm _ _

/-- The two branches of the adaptive selected-cell normalization obey one physical-scale
envelope.  The only branch-change cost is the fourth root of the scale-comparability constant. -/
theorem routeTAdaptiveCellAmplitude_threshold_le_comparable_envelope
    (L X k : ℕ) (hk : 0 < k) (hX : 1 < X) {N V kappa : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ))
    (hV : 0 < V) (hkappa : 1 ≤ kappa)
    (hcomparable : (X : ℝ) ≤ kappa * (N / (2 ^ (2 * k) : ℝ)))
    (halphaLower : 3 / 4 ≤ routeTAdaptiveCellAmplitude L X k N V) :
    V ≤ heathBrownEligibleBoxCost L X k * kappa ^ (1 / 4 : ℝ) *
      (X : ℝ) ^ (routeTAdaptiveCellAmplitude L X k N V - 1) := by
  let D : ℝ := N / (2 ^ (2 * k) : ℝ)
  let C : ℝ := heathBrownEligibleBoxCost L X k
  let W : ℝ := V / C
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X k N V
  have hC : 0 < C := heathBrownEligibleBoxCost_pos L X k hk
  have hW : 0 < W := div_pos hV hC
  have hDPos : 0 < D := by dsimp only [D]; linarith
  have hXReal : (1 : ℝ) < X := by exact_mod_cast hX
  have hVC : V = C * W := by
    dsimp only [W]
    field_simp
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
    have henvelope : D ^ (alpha - 1) ≤
        kappa ^ (1 / 4 : ℝ) * (X : ℝ) ^ (alpha - 1) :=
      negative_rpow_le_quarter_distortion (by linarith) hkappa
        (by simpa only [D] using hcomparable) (by linarith) (by linarith)
    calc
      V = C * W := hVC
      _ = C * D ^ (alpha - 1) := by rw [hexact]
      _ ≤ C * (kappa ^ (1 / 4 : ℝ) * (X : ℝ) ^ (alpha - 1)) :=
        mul_le_mul_of_nonneg_left henvelope hC.le
      _ = C * kappa ^ (1 / 4 : ℝ) * (X : ℝ) ^ (alpha - 1) := by ring
  · have hexact : (X : ℝ) ^ (alpha - 1) = W := by
      dsimp only [alpha, routeTAdaptiveCellAmplitude]
      rw [if_neg hbelow]
      exact rpow_maynardAmplitude_sub_abscissa hXReal hW
    have hkappaPower : 1 ≤ kappa ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow hkappa (by norm_num)
    have hXPower : 0 ≤ (X : ℝ) ^ (alpha - 1) :=
      Real.rpow_nonneg (by positivity) _
    calc
      V = C * W := hVC
      _ = C * (X : ℝ) ^ (alpha - 1) := by rw [hexact]
      _ ≤ C * (kappa ^ (1 / 4 : ℝ) * (X : ℝ) ^ (alpha - 1)) := by
        have hinner : (X : ℝ) ^ (alpha - 1) ≤
            kappa ^ (1 / 4 : ℝ) * (X : ℝ) ^ (alpha - 1) := by
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hkappaPower hXPower)
        exact mul_le_mul_of_nonneg_left hinner hC.le
      _ = C * kappa ^ (1 / 4 : ℝ) * (X : ℝ) ^ (alpha - 1) := by ring

/-- Three-scale adaptive envelope.  The low branch compares the physical lower edge `D` with the
receiver scale `Y`; the high branch compares the integer support `X` with `Y`.  Thus the final
power is expressed at the actual Maynard receiver scale, not at a merely comparable support. -/
theorem routeTAdaptiveCellAmplitude_threshold_le_receiverScale_envelope
    (L X k : ℕ) (hk : 0 < k) (hX : 1 < X) {N V Y kappa : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ))
    (hV : 0 < V) (hY : 0 < Y) (hkappa : 1 ≤ kappa)
    (hSupport : (X : ℝ) ≤ Y)
    (hLowerComparable : Y ≤ kappa * (N / (2 ^ (2 * k) : ℝ)))
    (halphaLower : 3 / 4 ≤ routeTAdaptiveCellAmplitude L X k N V) :
    V ≤ heathBrownEligibleBoxCost L X k * kappa ^ (1 / 4 : ℝ) *
      Y ^ (routeTAdaptiveCellAmplitude L X k N V - 1) := by
  let D : ℝ := N / (2 ^ (2 * k) : ℝ)
  let C : ℝ := heathBrownEligibleBoxCost L X k
  let W : ℝ := V / C
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X k N V
  have hC : 0 < C := heathBrownEligibleBoxCost_pos L X k hk
  have hW : 0 < W := div_pos hV hC
  have hXReal : (1 : ℝ) < X := by exact_mod_cast hX
  have hVC : V = C * W := by
    dsimp only [W]
    field_simp
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
    have henvelope : D ^ (alpha - 1) ≤
        kappa ^ (1 / 4 : ℝ) * Y ^ (alpha - 1) :=
      negative_rpow_le_quarter_distortion hY hkappa
        (by simpa only [D] using hLowerComparable) (by linarith) (by linarith)
    calc
      V = C * W := hVC
      _ = C * D ^ (alpha - 1) := by rw [hexact]
      _ ≤ C * (kappa ^ (1 / 4 : ℝ) * Y ^ (alpha - 1)) :=
        mul_le_mul_of_nonneg_left henvelope hC.le
      _ = C * kappa ^ (1 / 4 : ℝ) * Y ^ (alpha - 1) := by ring
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
    have hkappaPower : 1 ≤ kappa ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow hkappa (by norm_num)
    have hYPower : 0 ≤ Y ^ (alpha - 1) := Real.rpow_nonneg hY.le _
    have hdistort : Y ^ (alpha - 1) ≤
        kappa ^ (1 / 4 : ℝ) * Y ^ (alpha - 1) := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hkappaPower hYPower)
    calc
      V = C * W := hVC
      _ = C * (X : ℝ) ^ (alpha - 1) := by rw [hexact]
      _ ≤ C * Y ^ (alpha - 1) :=
        mul_le_mul_of_nonneg_left hsupportPower hC.le
      _ ≤ C * (kappa ^ (1 / 4 : ℝ) * Y ^ (alpha - 1)) :=
        mul_le_mul_of_nonneg_left hdistort hC.le
      _ = C * kappa ^ (1 / 4 : ℝ) * Y ^ (alpha - 1) := by ring

/-- Squared receiver-scale envelope used by spatial `L²`. -/
theorem routeTAdaptiveCellAmplitude_threshold_sq_le_receiverScale_envelope
    (L X k : ℕ) (hk : 0 < k) (hX : 1 < X) {N V Y kappa : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ))
    (hV : 0 < V) (hY : 0 < Y) (hkappa : 1 ≤ kappa)
    (hSupport : (X : ℝ) ≤ Y)
    (hLowerComparable : Y ≤ kappa * (N / (2 ^ (2 * k) : ℝ)))
    (halphaLower : 3 / 4 ≤ routeTAdaptiveCellAmplitude L X k N V) :
    V ^ 2 ≤ (heathBrownEligibleBoxCost L X k) ^ 2 *
      kappa ^ (1 / 2 : ℝ) *
      Y ^ (2 * routeTAdaptiveCellAmplitude L X k N V - 2) := by
  let C : ℝ := heathBrownEligibleBoxCost L X k
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X k N V
  have henvelope :=
    routeTAdaptiveCellAmplitude_threshold_le_receiverScale_envelope
      L X k hk hX hD hV hY hkappa hSupport hLowerComparable halphaLower
  have hsquare : V ^ 2 ≤
      (C * kappa ^ (1 / 4 : ℝ) * Y ^ (alpha - 1)) ^ 2 := by
    exact pow_le_pow_left₀ hV.le (by simpa only [C, alpha] using henvelope) 2
  calc
    V ^ 2 ≤ (C * kappa ^ (1 / 4 : ℝ) * Y ^ (alpha - 1)) ^ 2 := hsquare
    _ = C ^ 2 * kappa ^ (1 / 2 : ℝ) * Y ^ (2 * alpha - 2) := by
      rw [mul_pow, mul_pow,
        ← Real.rpow_natCast (kappa ^ (1 / 4 : ℝ)) 2,
        ← Real.rpow_mul (zero_le_one.trans hkappa),
        ← Real.rpow_natCast (Y ^ (alpha - 1)) 2,
        ← Real.rpow_mul hY.le]
      congr 1 <;> ring_nf
    _ = (heathBrownEligibleBoxCost L X k) ^ 2 *
        kappa ^ (1 / 2 : ℝ) *
        Y ^ (2 * routeTAdaptiveCellAmplitude L X k N V - 2) := rfl

/-- Squared form consumed by spatial `L²`: the adaptive exponent is now explicit and its
selected-count contribution can cancel exactly. -/
theorem routeTAdaptiveCellAmplitude_threshold_sq_le_comparable_envelope
    (L X k : ℕ) (hk : 0 < k) (hX : 1 < X) {N V kappa : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ))
    (hV : 0 < V) (hkappa : 1 ≤ kappa)
    (hcomparable : (X : ℝ) ≤ kappa * (N / (2 ^ (2 * k) : ℝ)))
    (halphaLower : 3 / 4 ≤ routeTAdaptiveCellAmplitude L X k N V) :
    V ^ 2 ≤ (heathBrownEligibleBoxCost L X k) ^ 2 *
      kappa ^ (1 / 2 : ℝ) *
      (X : ℝ) ^ (2 * routeTAdaptiveCellAmplitude L X k N V - 2) := by
  let C : ℝ := heathBrownEligibleBoxCost L X k
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X k N V
  have henvelope :=
    routeTAdaptiveCellAmplitude_threshold_le_comparable_envelope
      L X k hk hX hD hV hkappa hcomparable halphaLower
  have hsquare : V ^ 2 ≤
      (C * kappa ^ (1 / 4 : ℝ) * (X : ℝ) ^ (alpha - 1)) ^ 2 := by
    exact pow_le_pow_left₀ hV.le (by simpa only [C, alpha] using henvelope) 2
  calc
    V ^ 2 ≤ (C * kappa ^ (1 / 4 : ℝ) *
        (X : ℝ) ^ (alpha - 1)) ^ 2 := hsquare
    _ = C ^ 2 * kappa ^ (1 / 2 : ℝ) *
        (X : ℝ) ^ (2 * alpha - 2) := by
      rw [mul_pow, mul_pow,
        ← Real.rpow_natCast (kappa ^ (1 / 4 : ℝ)) 2,
        ← Real.rpow_mul (zero_le_one.trans hkappa),
        ← Real.rpow_natCast ((X : ℝ) ^ (alpha - 1)) 2,
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ X)]
      congr 1 <;> ring_nf
    _ = (heathBrownEligibleBoxCost L X k) ^ 2 *
        kappa ^ (1 / 2 : ℝ) *
        (X : ℝ) ^ (2 * routeTAdaptiveCellAmplitude L X k N V - 2) := rfl

/-- Degree-60 packet specialization.  The packet support inequality `X <= 4N` pays the exact
fixed distortion `4 * 2^120`; no amplitude-dependent loss remains. -/
theorem routeTAdaptiveCellAmplitude_threshold_sq_le_fourSupport_envelope_sixty
    (L X : ℕ) (hX : 1 < X) {N V : ℝ}
    (hD : 1 < N / (2 ^ 120 : ℝ)) (hV : 0 < V)
    (hsupport : (X : ℝ) ≤ 4 * N)
    (halphaLower : 3 / 4 ≤ routeTAdaptiveCellAmplitude L X 60 N V) :
    V ^ 2 ≤ (heathBrownEligibleBoxCost L X 60) ^ 2 *
      (4 * (2 ^ 120 : ℝ)) ^ (1 / 2 : ℝ) *
      (X : ℝ) ^ (2 * routeTAdaptiveCellAmplitude L X 60 N V - 2) := by
  have hscale :
      (4 * (2 ^ 120 : ℝ)) * (N / (2 ^ (2 * 60) : ℝ)) = 4 * N := by
    norm_num only [Nat.reduceMul]
    field_simp
    ring
  have hkappa : (1 : ℝ) ≤ 4 * (2 ^ 120 : ℝ) := by
    have hp : (1 : ℝ) ≤ 2 ^ 120 := one_le_pow₀ (by norm_num)
    nlinarith
  apply routeTAdaptiveCellAmplitude_threshold_sq_le_comparable_envelope
    L X 60 (by norm_num) hX (by simpa only [Nat.reduceMul] using hD) hV hkappa
  · rw [hscale]
    exact hsupport
  · exact halphaLower

/-- Critical scalar cancellation.  A physical interval contributes one factor `x`; adaptive
spatial energy contributes `X^(2alpha-2)`; the Maynard second count contributes
`X^(1+nu-2alpha)`.  Under `x <= X` these exponents cancel to exactly `X^nu`. -/
theorem routeT_adaptive_spatial_second_count_cancellation
    {C kappa x X V R T alpha : ℝ}
    (hkappa : 0 ≤ kappa) (hx : 0 ≤ x) (hX : 0 < X)
    (hR : 0 ≤ R) (hxX : x ≤ X)
    (henvelope : V ^ 2 ≤ C ^ 2 * kappa ^ (1 / 2 : ℝ) * X ^ (2 * alpha - 2))
    (hsecond : R ≤ T * X ^ (1 + routeTGapMomentNu - 2 * alpha)) :
    x * V ^ 2 * R ≤
      C ^ 2 * kappa ^ (1 / 2 : ℝ) * T * X ^ routeTGapMomentNu := by
  let P : ℝ := C ^ 2 * kappa ^ (1 / 2 : ℝ)
  have hP : 0 ≤ P := by
    dsimp only [P]
    positivity
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
          (1 + routeTGapMomentNu - 2 * alpha)) := by
        exact (Real.rpow_add hX _ _).symm
      _ = X ^ routeTGapMomentNu := by congr 1 <;> ring
  calc
    x * V ^ 2 * R ≤ x * (P * X ^ (2 * alpha - 2)) * R := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by simpa only [P] using henvelope) hx) hR
    _ ≤ X * (P * X ^ (2 * alpha - 2)) * R := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hxX (mul_nonneg hP hXa)) hR
    _ ≤ X * (P * X ^ (2 * alpha - 2)) *
        (T * X ^ (1 + routeTGapMomentNu - 2 * alpha)) := by
      exact mul_le_mul_of_nonneg_left hsecond
        (mul_nonneg hX.le (mul_nonneg hP hXa))
    _ = P * T * (X * X ^ (2 * alpha - 2) *
        X ^ (1 + routeTGapMomentNu - 2 * alpha)) := by ring
    _ = P * T * X ^ routeTGapMomentNu := by rw [hpower]
    _ = C ^ 2 * kappa ^ (1 / 2 : ℝ) * T * X ^ routeTGapMomentNu := rfl

/-- Full three-scale critical cancellation: physical base `N`, integer support `X`, and Maynard
receiver scale `Y` may differ, provided the explicit comparisons hold. -/
theorem routeTAdaptiveCellAmplitude_receiverScale_second_count_cancellation
    (L X k : ℕ) (hk : 0 < k) (hX : 1 < X)
    {N V Y kappa R T : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ)) (hV : 0 < V)
    (hY : 0 < Y) (hkappa : 1 ≤ kappa)
    (hSupport : (X : ℝ) ≤ Y)
    (hLowerComparable : Y ≤ kappa * (N / (2 ^ (2 * k) : ℝ)))
    (hPhysical : N ≤ Y) (hR : 0 ≤ R)
    (halphaLower : 3 / 4 ≤ routeTAdaptiveCellAmplitude L X k N V)
    (hsecond : R ≤ T * Y ^
      (1 + routeTGapMomentNu - 2 * routeTAdaptiveCellAmplitude L X k N V)) :
    N * V ^ 2 * R ≤
      (heathBrownEligibleBoxCost L X k) ^ 2 * kappa ^ (1 / 2 : ℝ) *
        T * Y ^ routeTGapMomentNu := by
  have hN : 0 ≤ N := by
    have hden : 0 < (2 ^ (2 * k) : ℝ) := by positivity
    have hquot : 0 < N / (2 ^ (2 * k) : ℝ) := zero_lt_one.trans hD
    rcases div_pos_iff.mp hquot with hpos | hneg
    · exact hpos.1.le
    · exact False.elim ((not_lt_of_ge hden.le) hneg.2)
  exact routeT_adaptive_spatial_second_count_cancellation
    (zero_le_one.trans hkappa) hN hY hR hPhysical
      (routeTAdaptiveCellAmplitude_threshold_sq_le_receiverScale_envelope
        L X k hk hX hD hV hY hkappa hSupport hLowerComparable halphaLower)
      hsecond

/-- Bounding both lower- and upper-cutoff dyadic choices by the ambient support logarithm avoids
carrying a second cutoff-dependent logarithm into the adaptive packet energy. -/
theorem card_heathBrownBoxChoice_le_selfLog
    (L X k : ℕ) (hLX : L ≤ X) :
    Fintype.card (HeathBrownBoxChoice L X k) ≤
      k * (Nat.log 2 X + 1) ^ k * (Nat.log 2 X + 1) ^ k := by
  have hlogNat : Nat.log 2 L + 1 ≤ Nat.log 2 X + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right hLX) 1
  have hlogPowNat : (Nat.log 2 L + 1) ^ k ≤ (Nat.log 2 X + 1) ^ k :=
    pow_le_pow_left₀ (Nat.zero_le _) hlogNat k
  exact (card_heathBrownBoxChoice_le L X k).trans
    (Nat.mul_le_mul_left (k * (Nat.log 2 X + 1) ^ k) hlogPowNat)

/-- The dyadic natural logarithm count is dominated by the Route-T logarithm base. -/
theorem natLogTwo_add_one_cast_le_routeTLogBase
    (X : ℕ) (hX : 1 ≤ X) :
    ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤
      1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ)) := by
  let M : ℝ := (((2 ^ 120 * X : ℕ) : ℝ))
  have hC : (1 : ℝ) ≤ (2 : ℝ) ^ 120 := one_le_pow₀ (by norm_num)
  have hM_eq : M = (2 : ℝ) ^ 120 * (X : ℝ) := by
    simp only [M, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hXM : (X : ℝ) ≤ M := by
    rw [hM_eq]
    exact le_mul_of_one_le_left (by positivity) hC
  have hlogXM : Real.log (X : ℝ) ≤ Real.log M :=
    Real.log_le_log (by positivity) hXM
  have hlogXM' : Real.log (X : ℝ) ≤
      Real.log (((2 ^ 120 * X : ℕ) : ℝ)) := by simpa only [M] using hlogXM
  have hnat := natLogTwo_add_one_cast_le hX
  linarith

/-- Explicit fixed distortion incurred by squaring the degree-60 selector cost. -/
def routeTAdaptiveBoxEnergyConstant : ℝ :=
  ((60 : ℝ) * (2 : ℝ) ^ 60) ^ 2 *
    (4 * (2 ^ 120 : ℝ)) ^ (1 / 2 : ℝ)

/-- Degree-60 selector cost is a fixed power of the Route-T logarithm base. -/
theorem heathBrownEligibleBoxCost_sixty_le_routeTLogBase
    (L X : ℕ) (hX : 1 ≤ X) (hLX : L ≤ X) :
    heathBrownEligibleBoxCost L X 60 ≤
      ((60 : ℝ) * (2 : ℝ) ^ 60) *
        (1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))) ^ 120 := by
  let A : ℝ := ((Nat.log 2 X + 1 : ℕ) : ℝ)
  let B : ℝ := 1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))
  have hcard : (Fintype.card (HeathBrownBoxChoice L X 60) : ℝ) ≤
      60 * A ^ 60 * A ^ 60 := by
    dsimp only [A]
    exact_mod_cast card_heathBrownBoxChoice_le_selfLog L X 60 hLX
  have hAB : A ≤ B := by
    simpa only [A, B] using natLogTwo_add_one_cast_le_routeTLogBase X hX
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hB0 : 0 ≤ B := hA0.trans hAB
  have hpow : A ^ 60 ≤ B ^ 60 := pow_le_pow_left₀ hA0 hAB 60
  have hprod : 60 * A ^ 60 * A ^ 60 ≤ 60 * B ^ 60 * B ^ 60 := by
    calc
      60 * A ^ 60 * A ^ 60 ≤ 60 * B ^ 60 * A ^ 60 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by norm_num)) (pow_nonneg hA0 60)
      _ ≤ 60 * B ^ 60 * B ^ 60 :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (by norm_num) (pow_nonneg hB0 60))
  dsimp only [heathBrownEligibleBoxCost]
  calc
    (Fintype.card (HeathBrownBoxChoice L X 60) : ℝ) * (2 ^ 60 : ℝ) ≤
        (60 * A ^ 60 * A ^ 60) * (2 ^ 60 : ℝ) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ (60 * B ^ 60 * B ^ 60) * (2 ^ 60 : ℝ) :=
      mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = ((60 : ℝ) * (2 : ℝ) ^ 60) * (B ^ 60 * B ^ 60) := by ac_rfl
    _ = ((60 : ℝ) * (2 : ℝ) ^ 60) * B ^ 120 := by rw [← pow_add]
    _ = ((60 : ℝ) * (2 : ℝ) ^ 60) *
        (1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))) ^ 120 := rfl

/-- Squared degree-60 selector cost, including spatial distortion, remains polylogarithmic. -/
theorem heathBrownEligibleBoxCost_sq_sixty_le_routeTLogBase
    (L X : ℕ) (hX : 1 ≤ X) (hLX : L ≤ X) :
    (heathBrownEligibleBoxCost L X 60) ^ 2 *
        (4 * (2 ^ 120 : ℝ)) ^ (1 / 2 : ℝ) ≤
      routeTAdaptiveBoxEnergyConstant *
        (1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))) ^ 240 := by
  let B : ℝ := 1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))
  have hcost := heathBrownEligibleBoxCost_sixty_le_routeTLogBase L X hX hLX
  have hcost0 : 0 ≤ heathBrownEligibleBoxCost L X 60 := by
    dsimp only [heathBrownEligibleBoxCost]
    positivity
  have hsquare : (heathBrownEligibleBoxCost L X 60) ^ 2 ≤
      (((60 : ℝ) * (2 : ℝ) ^ 60) * B ^ 120) ^ 2 :=
    pow_le_pow_left₀ hcost0 (by simpa only [B] using hcost) 2
  have hdistortion0 : 0 ≤ (4 * (2 ^ 120 : ℝ)) ^ (1 / 2 : ℝ) := by positivity
  calc
    (heathBrownEligibleBoxCost L X 60) ^ 2 *
        (4 * (2 ^ 120 : ℝ)) ^ (1 / 2 : ℝ) ≤
      (((60 : ℝ) * (2 : ℝ) ^ 60) * B ^ 120) ^ 2 *
        (4 * (2 ^ 120 : ℝ)) ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hsquare hdistortion0
    _ = routeTAdaptiveBoxEnergyConstant * (B ^ 120) ^ 2 := by
      dsimp only [routeTAdaptiveBoxEnergyConstant]
      rw [mul_pow]
      ac_rfl
    _ = routeTAdaptiveBoxEnergyConstant * B ^ 240 := by rw [← pow_mul]
    _ = routeTAdaptiveBoxEnergyConstant *
        (1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))) ^ 240 := rfl

/-- Uniformly over every physical lower cutoff `L ≤ X`, squared selector cost is swallowed by an
arbitrarily small Route-T power. -/
theorem eventually_heathBrownEligibleBoxCost_sq_sixty_routeT_absorbed
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ L X : ℕ, 1 ≤ X → L ≤ X → (X : ℝ) ≤ T ^ (8 / 5 : ℝ) →
        (heathBrownEligibleBoxCost L X 60) ^ 2 *
          (4 * (2 ^ 120 : ℝ)) ^ (1 / 2 : ℝ) ≤ T ^ eta := by
  let eps : ℝ := eta / 2
  have heps : 0 < eps := by dsimp only [eps]; linarith
  have hBabs := eventually_routeTPrimeGapPacketLogBase_pow_absorbed 240 heps
  have hconst : ∀ᶠ T : ℝ in Filter.atTop,
      routeTAdaptiveBoxEnergyConstant ≤ T ^ eps :=
    (tendsto_rpow_atTop heps).eventually_ge_atTop routeTAdaptiveBoxEnergyConstant
  filter_upwards [hBabs, hconst, Filter.eventually_ge_atTop (1 : ℝ)] with
    T hBabsT hconstT hT
  intro L X hX hLX hXscale
  let B : ℝ := 1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hM1 : (1 : ℝ) ≤ (((2 ^ 120 * X : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_le_mul (Nat.one_le_two_pow) hX
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    linarith [Real.log_nonneg hM1]
  have hBpow : B ^ 240 ≤ T ^ eps := by
    simpa only [B] using hBabsT X hX hXscale
  have hTpow0 : 0 ≤ T ^ eps := Real.rpow_nonneg hTpos.le _
  calc
    (heathBrownEligibleBoxCost L X 60) ^ 2 *
        (4 * (2 ^ 120 : ℝ)) ^ (1 / 2 : ℝ) ≤
      routeTAdaptiveBoxEnergyConstant * B ^ 240 := by
        simpa only [B] using
          heathBrownEligibleBoxCost_sq_sixty_le_routeTLogBase L X hX hLX
    _ ≤ T ^ eps * T ^ eps :=
      mul_le_mul hconstT hBpow (pow_nonneg hB0 240) hTpow0
    _ = T ^ (eps + eps) := (Real.rpow_add hTpos eps eps).symm
    _ = T ^ eta := by
      congr 1
      dsimp only [eps]
      linarith

/-- Canonical packet specialization.  The actual receiver scale is `T0^(8/5)=4N`, while the
integer Heath--Brown support is `ceil(3N)`.  The three-scale envelope makes this mismatch harmless
and yields exact amplitude cancellation for every forced second alternative. -/
theorem eventually_routeTPrimeGapPacket_adaptive_second_count_cancellation_sixty :
    ∀ᶠ T0 : ℝ in Filter.atTop,
      ∀ {L : ℕ} {V R H : ℝ},
      0 < V → 0 ≤ R →
      3 / 4 ≤ routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T0) 60
        (routeTPrimeGapPacketBase T0) V →
      R ≤ H * (T0 ^ (8 / 5 : ℝ)) ^
        (1 + routeTGapMomentNu -
          2 * routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T0) 60
            (routeTPrimeGapPacketBase T0) V) →
      routeTPrimeGapPacketBase T0 * V ^ 2 * R ≤
        (heathBrownEligibleBoxCost L (routeTPrimeGapPacketSupport T0) 60) ^ 2 *
          (4 * (2 ^ 120 : ℝ)) ^ (1 / 2 : ℝ) * H *
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
    (routeTAdaptiveCellAmplitude_receiverScale_second_count_cancellation
      L X 60 (by norm_num) hX (by simpa only [Nat.reduceMul] using hD) hV
      hY hkappa hSupport hLowerComparable hPhysical hR halpha hsecond)

/-- After the exact adaptive exponent cancellation, every remaining degree-60 selector loss is
absorbed by an arbitrary positive Route-T power, uniformly in the physical cutoff. -/
theorem eventually_routeTPrimeGapPacket_adaptive_second_count_cancellation_absorbed_sixty
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T0 : ℝ in Filter.atTop,
      ∀ {L : ℕ} {V R H : ℝ},
      L ≤ routeTPrimeGapPacketSupport T0 → 0 ≤ H → 0 < V → 0 ≤ R →
      3 / 4 ≤ routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T0) 60
        (routeTPrimeGapPacketBase T0) V →
      R ≤ H * (T0 ^ (8 / 5 : ℝ)) ^
        (1 + routeTGapMomentNu -
          2 * routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T0) 60
            (routeTPrimeGapPacketBase T0) V) →
      routeTPrimeGapPacketBase T0 * V ^ 2 * R ≤
        T0 ^ eta * H * (T0 ^ (8 / 5 : ℝ)) ^ routeTGapMomentNu := by
  have hcancel :=
    eventually_routeTPrimeGapPacket_adaptive_second_count_cancellation_sixty
  have hcost := eventually_heathBrownEligibleBoxCost_sq_sixty_routeT_absorbed heta
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
  have hceilUpper : (X : ℝ) < 3 * N + 1 := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.ceil_lt_add_one (by positivity)
  have hX : 1 ≤ X := by
    have hXreal : (1 : ℝ) ≤ X := by linarith
    exact_mod_cast hXreal
  have hYeq : Y = 4 * N := by
    dsimp only [Y, N, routeTPrimeGapPacketBase]
    field_simp
  have hSupport : (X : ℝ) ≤ Y := by
    rw [hYeq]
    linarith
  have hcostBound :
      (heathBrownEligibleBoxCost L X 60) ^ 2 *
          (4 * (2 ^ 120 : ℝ)) ^ (1 / 2 : ℝ) ≤ T0 ^ eta :=
    hcostT L X hX (by simpa only [X] using hLX) (by simpa only [Y] using hSupport)
  have hmain := hcancelT hV hR halpha hsecond
  have hreceiverNonneg : 0 ≤ H * Y ^ routeTGapMomentNu :=
    mul_nonneg hH (Real.rpow_nonneg (by positivity) _)
  calc
    routeTPrimeGapPacketBase T0 * V ^ 2 * R ≤
        (heathBrownEligibleBoxCost L X 60) ^ 2 *
          (4 * (2 ^ 120 : ℝ)) ^ (1 / 2 : ℝ) * H *
            Y ^ routeTGapMomentNu := by
      simpa only [X, Y] using hmain
    _ = ((heathBrownEligibleBoxCost L X 60) ^ 2 *
          (4 * (2 ^ 120 : ℝ)) ^ (1 / 2 : ℝ)) *
            (H * Y ^ routeTGapMomentNu) := by ac_rfl
    _ ≤ T0 ^ eta * (H * Y ^ routeTGapMomentNu) :=
      mul_le_mul_of_nonneg_right hcostBound hreceiverNonneg
    _ = T0 ^ eta * H * (T0 ^ (8 / 5 : ℝ)) ^ routeTGapMomentNu := by
      dsimp only [Y]
      ac_rfl

/-- Degree-60 physical selected-cell cancellation.  This composes the two-edge amplitude envelope
with the second Maynard alternative at the literal packet base. -/
theorem routeTAdaptiveCellAmplitude_physical_second_count_cancellation_sixty
    (L X : ℕ) (hX : 1 < X) {N V R T : ℝ}
    (hD : 1 < N / (2 ^ 120 : ℝ)) (hV : 0 < V)
    (hsupportUpper : (X : ℝ) ≤ 4 * N) (hsupportLower : N ≤ (X : ℝ))
    (hR : 0 ≤ R)
    (halphaLower : 3 / 4 ≤ routeTAdaptiveCellAmplitude L X 60 N V)
    (hsecond : R ≤ T * (X : ℝ) ^
      (1 + routeTGapMomentNu - 2 * routeTAdaptiveCellAmplitude L X 60 N V)) :
    N * V ^ 2 * R ≤
      (heathBrownEligibleBoxCost L X 60) ^ 2 *
        (4 * (2 ^ 120 : ℝ)) ^ (1 / 2 : ℝ) * T *
          (X : ℝ) ^ routeTGapMomentNu := by
  have hN : 0 ≤ N := by
    have hXcast : (0 : ℝ) < X := by positivity
    nlinarith [hsupportUpper]
  exact routeT_adaptive_spatial_second_count_cancellation
    (by positivity) hN (by positivity) hR hsupportLower
      (routeTAdaptiveCellAmplitude_threshold_sq_le_fourSupport_envelope_sixty
        L X hX hD hV hsupportUpper halphaLower) hsecond

end RHTower.Sieve
