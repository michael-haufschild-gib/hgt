import GaloisForLFunctions.RHTower.Sieve.MaynardAdaptiveAmplitudeEnvelope

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Physical amplitude threshold whose lower-edge logarithmic coordinate is exactly the
Route-T trivial-count boundary. -/
def routeTTrivialBoundaryAmplitudeThreshold
    (L X k : ℕ) (N : ℝ) : ℝ :=
  heathBrownEligibleBoxCost L X k *
    (N / (2 ^ (2 * k) : ℝ)) ^
      ((1 + routeTGapMomentNu) / 2 - 1)

theorem routeT_trivialCountBoundary_lt_one :
    (1 + routeTGapMomentNu) / 2 < 1 := by
  linarith [routeTGapMomentNu_lt_half]

theorem routeTTrivialBoundaryAmplitudeThreshold_pos
    (L X k : ℕ) (hk : 0 < k) {N : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ)) :
    0 < routeTTrivialBoundaryAmplitudeThreshold L X k N := by
  unfold routeTTrivialBoundaryAmplitudeThreshold
  exact mul_pos (heathBrownEligibleBoxCost_pos L X k hk)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hD) _)

/-- Lower-edge threshold comparison is precisely an adaptive-amplitude lower bound, even across
the low/high normalization branch. -/
theorem le_routeTAdaptiveCellAmplitude_of_lowerEdgeThreshold_le
    (L X k : ℕ) (hk : 0 < k) (hX : 1 < X) {N V alpha : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ))
    (halpha : alpha ≤ 1)
    (hthreshold : heathBrownEligibleBoxCost L X k *
      (N / (2 ^ (2 * k) : ℝ)) ^ (alpha - 1) ≤ V) :
    alpha ≤ routeTAdaptiveCellAmplitude L X k N V := by
  let C : ℝ := heathBrownEligibleBoxCost L X k
  let D : ℝ := N / (2 ^ (2 * k) : ℝ)
  have hC : 0 < C := heathBrownEligibleBoxCost_pos L X k hk
  by_cases hVC : V ≤ C
  · rw [routeTAdaptiveCellAmplitude, if_pos hVC]
    apply le_maynardAmplitude_of_rpow_le hD
    apply (le_div_iff₀ hC).2
    simpa only [C, D, mul_comm] using hthreshold
  · have hCV : C < V := lt_of_not_ge hVC
    have hXR : (1 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have hone : 1 ≤ maynardAmplitude 1 (X : ℝ) (V / C) := by
      apply le_maynardAmplitude_of_rpow_le hXR
      simpa using (one_le_div hC).2 hCV.le
    rw [routeTAdaptiveCellAmplitude, if_neg hVC]
    exact halpha.trans hone

/-- Every threshold above the canonical Route-T base has adaptive exponent at least the exact
trivial-count boundary. -/
theorem routeT_trivialCountBoundary_le_adaptive_of_threshold_le
    (L X k : ℕ) (hk : 0 < k) (hX : 1 < X) {N V : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ))
    (hthreshold : routeTTrivialBoundaryAmplitudeThreshold L X k N ≤ V) :
    (1 + routeTGapMomentNu) / 2 ≤
      routeTAdaptiveCellAmplitude L X k N V := by
  apply le_routeTAdaptiveCellAmplitude_of_lowerEdgeThreshold_le
    L X k hk hX hD routeT_trivialCountBoundary_lt_one.le
  simpa only [routeTTrivialBoundaryAmplitudeThreshold] using hthreshold

/-- The canonical base threshold has exactly the trivial-count adaptive exponent. -/
theorem routeTAdaptiveCellAmplitude_trivialBoundaryThreshold
    (L X k : ℕ) (hk : 0 < k) {N : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ)) :
    routeTAdaptiveCellAmplitude L X k N
        (routeTTrivialBoundaryAmplitudeThreshold L X k N) =
      (1 + routeTGapMomentNu) / 2 := by
  let C : ℝ := heathBrownEligibleBoxCost L X k
  let D : ℝ := N / (2 ^ (2 * k) : ℝ)
  let alpha : ℝ := (1 + routeTGapMomentNu) / 2
  let V : ℝ := C * D ^ (alpha - 1)
  have hC : 0 < C := heathBrownEligibleBoxCost_pos L X k hk
  have hD0 : 0 < D := zero_lt_one.trans hD
  have halpha : alpha < 1 := by
    simpa only [alpha] using routeT_trivialCountBoundary_lt_one
  have hpow : 0 < D ^ (alpha - 1) := Real.rpow_pos_of_pos hD0 _
  have hV : 0 < V := mul_pos hC hpow
  have hpowOne : D ^ (alpha - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hD.le (sub_nonpos.mpr halpha.le)
  have hVC : V ≤ C := by
    dsimp only [V]
    calc
      C * D ^ (alpha - 1) ≤ C * 1 := mul_le_mul_of_nonneg_left hpowOne hC.le
      _ = C := mul_one C
  have hquot : V / C = D ^ (alpha - 1) := by
    dsimp only [V]
    field_simp
  have hpows : D ^ (maynardAmplitude 1 D (V / C) - 1) =
      D ^ (alpha - 1) := by
    rw [rpow_maynardAmplitude_sub_abscissa hD (div_pos hV hC), hquot]
  have hexponents : maynardAmplitude 1 D (V / C) - 1 = alpha - 1 :=
    (Real.strictMono_rpow_of_base_gt_one hD).injective hpows
  change routeTAdaptiveCellAmplitude L X k N
      (routeTTrivialBoundaryAmplitudeThreshold L X k N) = _
  have hthresholdEq : routeTTrivialBoundaryAmplitudeThreshold L X k N = V := by
    rfl
  rw [hthresholdEq, routeTAdaptiveCellAmplitude, if_pos hVC]
  simpa only [D, C, alpha] using (show maynardAmplitude 1 D (V / C) = alpha by
    linarith)

/-- Every positive dyadic multiple of the canonical base remains above the exact trivial-count
adaptive boundary. -/
theorem routeT_trivialCountBoundary_le_adaptive_dyadicThreshold
    (L X k q : ℕ) (hk : 0 < k) (hX : 1 < X) {N : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ)) :
    (1 + routeTGapMomentNu) / 2 ≤
      routeTAdaptiveCellAmplitude L X k N
        (((2 ^ q : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L X k N) := by
  apply routeT_trivialCountBoundary_le_adaptive_of_threshold_le L X k hk hX hD
  have hv := routeTTrivialBoundaryAmplitudeThreshold_pos L X k hk hD
  have hp : (1 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  calc
    routeTTrivialBoundaryAmplitudeThreshold L X k N =
        1 * routeTTrivialBoundaryAmplitudeThreshold L X k N := by ring
    _ ≤ ((2 ^ q : ℕ) : ℝ) *
        routeTTrivialBoundaryAmplitudeThreshold L X k N :=
      mul_le_mul_of_nonneg_right hp hv.le

/-- Exact critical exponent identity: trivial cell cardinality contributes the missing height
power while the squared base threshold contributes `D^(nu-1)`. -/
theorem routeTTrivialBoundaryAmplitudeThreshold_sq
    (L X k : ℕ) {N : ℝ}
    (hD : 0 < N / (2 ^ (2 * k) : ℝ)) :
    (routeTTrivialBoundaryAmplitudeThreshold L X k N) ^ 2 =
      (heathBrownEligibleBoxCost L X k) ^ 2 *
        (N / (2 ^ (2 * k) : ℝ)) ^ (routeTGapMomentNu - 1) := by
  let D : ℝ := N / (2 ^ (2 * k) : ℝ)
  let a : ℝ := (1 + routeTGapMomentNu) / 2 - 1
  unfold routeTTrivialBoundaryAmplitudeThreshold
  rw [mul_pow]
  congr 1
  change (D ^ a) ^ 2 = D ^ (routeTGapMomentNu - 1)
  calc
    (D ^ a) ^ (2 : ℕ) = (D ^ a) ^ (2 : ℝ) :=
      (Real.rpow_natCast (D ^ a) 2).symm
    _ = D ^ (a * 2) := (Real.rpow_mul hD.le a 2).symm
    _ = D ^ (routeTGapMomentNu - 1) := by
      congr 1
      dsimp only [a]
      ring

end RHTower.Sieve
