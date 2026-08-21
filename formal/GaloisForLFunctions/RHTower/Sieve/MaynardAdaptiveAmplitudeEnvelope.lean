import GaloisForLFunctions.RHTower.Sieve.MaynardAmplitudeLayerExtraction

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

end RHTower.Sieve
