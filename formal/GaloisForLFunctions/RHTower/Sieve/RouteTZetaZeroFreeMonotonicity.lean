import GaloisForLFunctions.RHTower.Sieve.RouteTZetaZeroFree

/-!
# Monotonicity of the Route-T zero-free width

The canonical parameters contain several integer roundings, but every rounding is oriented in the
same direction.  Consequently the growth budget increases and the certified zero-free width
decreases with height.  This converts the pointwise zero-free theorem into uniform control on a
unit ordinate band by evaluating the width at its upper endpoint.
-/

namespace RHTower.Sieve

noncomputable section

theorem routeTGlobalMoment_mono {V W : ℕ} (hVW : V ≤ W) :
    routeTGlobalMoment V ≤ routeTGlobalMoment W := by
  unfold routeTGlobalMoment
  have hpow : (V + 1) ^ (9 : ℕ) ≤ (W + 1) ^ (9 : ℕ) :=
    Nat.pow_le_pow_left (by omega) 9
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hpow) 1

theorem routeTGlobalExponent_mono {V W : ℕ} (hVW : V ≤ W) :
    routeTGlobalExponent V ≤ routeTGlobalExponent W := by
  unfold routeTGlobalExponent
  exact Nat.mul_le_mul_left _ (routeTGlobalMoment_mono hVW)

theorem routeTGlobalStart_mono {V W : ℕ} (hVW : V ≤ W) :
    routeTGlobalStart V ≤ routeTGlobalStart W := by
  unfold routeTGlobalStart
  exact Nat.pow_le_pow_right (by norm_num) (routeTGlobalExponent_mono hVW)

theorem topExponent_mono {s t : ℝ} (hs : 8 * Real.pi ≤ s) (hst : s ≤ t) :
    topExponent s ≤ topExponent t := by
  unfold topExponent
  apply Nat.floor_mono
  have hpi : 0 < 8 * Real.pi := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs0 : 0 < s / (8 * Real.pi) := by
    rw [div_pos_iff]
    exact Or.inl ⟨lt_of_lt_of_le hpi hs, hpi⟩
  have hdiv : s / (8 * Real.pi) ≤ t / (8 * Real.pi) :=
    div_le_div_of_nonneg_right hst hpi.le
  have hlog : Real.log (s / (8 * Real.pi)) ≤ Real.log (t / (8 * Real.pi)) :=
    Real.log_le_log hs0 hdiv
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by norm_num)) hlog2.le

theorem routeTBandGrowthBound_mono {s t : ℝ}
    (hs : 8 * Real.pi + 1 ≤ s) (hst : s ≤ t) :
    routeTBandGrowthBound s ≤ routeTBandGrowthBound t := by
  have hsTop : 8 * Real.pi ≤ s - 1 := by linarith
  have hTop := topExponent_mono hsTop (by linarith : s - 1 ≤ t - 1)
  have hStartNat := routeTGlobalStart_mono (routeTBandShell_mono hst)
  have hStart :
      (routeTGlobalStart (routeTBandShell s) : ℝ) ≤
        (routeTGlobalStart (routeTBandShell t) : ℝ) := by
    exact_mod_cast hStartNat
  have hStartPos : (0 : ℝ) < routeTGlobalStart (routeTBandShell s) := by
    exact_mod_cast Nat.zero_lt_of_lt (routeTGlobalStart_two_le (routeTBandShell s))
  have hLog := Real.log_le_log hStartPos hStart
  unfold routeTBandGrowthBound
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hLog (by norm_num)))
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hTop) (by norm_num))

theorem routeTLandauRadius_antitone {s t : ℝ} (hst : s ≤ t) :
    routeTLandauRadius t ≤ routeTLandauRadius s := by
  unfold routeTLandauRadius
  exact div_le_div_of_nonneg_right (routeTBandWidth_antitone (by linarith : 4 * s ≤ 4 * t))
    (by norm_num)

theorem routeTLandauPhi_mono {s t : ℝ}
    (hs : 8 * Real.pi + 1 ≤ s) (hst : s ≤ t) :
    routeTLandauPhi s ≤ routeTLandauPhi t := by
  have hs2 : 8 * Real.pi + 1 ≤ 2 * s := by
    have hpi := Real.pi_pos
    linarith
  have hs4 : 8 * Real.pi + 1 ≤ 4 * s := by
    have hpi := Real.pi_pos
    linarith
  have h1 := routeTBandGrowthBound_mono hs hst
  have h2 := routeTBandGrowthBound_mono hs2 (by linarith : 2 * s ≤ 2 * t)
  have h4 := routeTBandGrowthBound_mono hs4 (by linarith : 4 * s ≤ 4 * t)
  unfold routeTLandauPhi
  linarith

theorem routeTZeroFreeBudget_mono {A s t : ℝ}
    (hs : 8 * Real.pi + 1 ≤ s) (hst : s ≤ t) :
    routeTZeroFreeBudget A s ≤ routeTZeroFreeBudget A t := by
  have hPhi := routeTLandauPhi_mono hs hst
  have hPhiPos : 0 < routeTLandauPhi s :=
    lt_of_lt_of_le (by norm_num) (routeTLandauPhi_one_le s)
  have hlogPhi := Real.log_le_log hPhiPos hPhi
  have hR := routeTLandauRadius_antitone hst
  have hRs : 0 < routeTLandauRadius s := routeTLandauRadius_pos s
  have hRt : 0 < routeTLandauRadius t := routeTLandauRadius_pos t
  have hInv : 1 / routeTLandauRadius s ≤ 1 / routeTLandauRadius t := by
    exact one_div_le_one_div_of_le hRt hR
  have hArg : 1 + 1 / routeTLandauRadius s ≤ 1 + 1 / routeTLandauRadius t := by
    linarith
  have hArgPos : 0 < 1 + 1 / routeTLandauRadius s := by positivity
  have hlogR := Real.log_le_log hArgPos hArg
  unfold routeTZeroFreeBudget
  linarith

theorem routeTZeroFreeDelta_antitone {A s t : ℝ}
    (hs : 8 * Real.pi + 1 ≤ s) (hst : s ≤ t) :
    routeTZeroFreeDelta A t ≤ routeTZeroFreeDelta A s := by
  have hR := routeTLandauRadius_antitone hst
  have hRs : 0 ≤ routeTLandauRadius s := (routeTLandauRadius_pos s).le
  have hQt := routeTZeroFreeBudget_pos A t
  have hQs := routeTZeroFreeBudget_pos A s
  have hQ := routeTZeroFreeBudget_mono (A := A) hs hst
  have hQsq : routeTZeroFreeBudget A s ^ (2 : ℕ) ≤ routeTZeroFreeBudget A t ^ (2 : ℕ) :=
    pow_le_pow_left₀ hQs.le hQ 2
  have hDen : 10000 * routeTZeroFreeBudget A s ^ (2 : ℕ) ≤
      10000 * routeTZeroFreeBudget A t ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_left hQsq (by norm_num)
  have hDenS : 0 < 10000 * routeTZeroFreeBudget A s ^ (2 : ℕ) :=
    mul_pos (by norm_num) (sq_pos_of_pos hQs)
  have hDenT : 0 < 10000 * routeTZeroFreeBudget A t ^ (2 : ℕ) :=
    mul_pos (by norm_num) (sq_pos_of_pos hQt)
  unfold routeTZeroFreeDelta
  calc
    routeTLandauRadius t / (10000 * routeTZeroFreeBudget A t ^ (2 : ℕ)) ≤
        routeTLandauRadius s / (10000 * routeTZeroFreeBudget A t ^ (2 : ℕ)) :=
      div_le_div_of_nonneg_right hR hDenT.le
    _ ≤ routeTLandauRadius s / (10000 * routeTZeroFreeBudget A s ^ (2 : ℕ)) := by
      exact div_le_div_of_nonneg_left hRs hDenS hDen

/-- **The Route-T zero-free width decreases with height.** -/
theorem routeTZeroFreeWidth_antitone {A s t : ℝ}
    (hs : 8 * Real.pi + 1 ≤ s) (hst : s ≤ t) :
    routeTZeroFreeWidth A t ≤ routeTZeroFreeWidth A s := by
  unfold routeTZeroFreeWidth
  exact div_le_div_of_nonneg_right (routeTZeroFreeDelta_antitone hs hst) (by norm_num)

end

end RHTower.Sieve
