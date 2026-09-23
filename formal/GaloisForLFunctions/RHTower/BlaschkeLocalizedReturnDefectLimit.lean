import GaloisForLFunctions.RHTower.BlaschkeLocalizedReturnDefect

/-!
# Sublinear calibration of Blaschke recurrence accuracy

A square-root shift of logarithmic water depth is negligible relative to
the quadratic entropy clock but exponentially dominates the linear
active-mode prefactor. Consequently the constructive return defect at the
shifted level is eventually below the unshifted target `exp (-L)`.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- Square-root-shifted water level; the shift is sublinear but dominates
the linear active-mode prefactor exponentially. -/
def blaschkeSqrtShiftedScale (K : ℝ) (k : ℕ) : ℝ :=
  blaschkeShiftedScale K k + Real.sqrt (k : ℝ)

theorem tendsto_one_add_nat_mul_exp_neg_sqrt :
    Tendsto (fun k : ℕ =>
      (1 + (k : ℝ)) * Real.exp (-Real.sqrt (k : ℝ)))
      atTop (𝓝 0) := by
  have hsqrt :
      Tendsto (fun k : ℕ => Real.sqrt (k : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hzero :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hsqrt
  have htwo :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hsqrt
  have hlinear :
      Tendsto (fun k : ℕ =>
        (k : ℝ) * Real.exp (-Real.sqrt (k : ℝ)))
        atTop (𝓝 0) := by
    apply htwo.congr'
    filter_upwards with k
    change Real.sqrt (k : ℝ) ^ (2 : ℕ) *
        Real.exp (-Real.sqrt (k : ℝ)) =
      (k : ℝ) * Real.exp (-Real.sqrt (k : ℝ))
    rw [Real.sq_sqrt (Nat.cast_nonneg k)]
  have hconstant :
      Tendsto (fun k : ℕ =>
        Real.exp (-Real.sqrt (k : ℝ))) atTop (𝓝 0) := by
    apply hzero.congr'
    filter_upwards with k
    simp only [Function.comp_apply, pow_zero, one_mul]
  have hadd := hconstant.add hlinear
  simpa only [zero_add, add_mul, one_mul] using hadd

theorem tendsto_blaschkeActiveWaterReturnDefect_sqrtShift_ratio_zero
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKnonneg : 0 ≤ K) :
    Tendsto (fun k : ℕ =>
      blaschkeActiveWaterReturnDefect a
          (blaschkeSqrtShiftedScale K k) /
        Real.exp (-blaschkeShiftedScale K k))
      atTop (𝓝 0) := by
  let C : ℝ := blaschkeReturnDefectLinearConstant a
  let D : ℝ := C * (K + 2)
  have hC : 0 ≤ C := by
    dsimp only [C, blaschkeReturnDefectLinearConstant]
    have hrho := blaschkeSpectralSlope_pos a ha0 ha1
    have hbase : 0 < 1 - a ^ (2 : ℕ) := by nlinarith
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hmajor :
      Tendsto (fun k : ℕ =>
        D * ((1 + (k : ℝ)) *
          Real.exp (-Real.sqrt (k : ℝ)))) atTop (𝓝 0) :=
    by
      simpa only [mul_zero] using
        tendsto_one_add_nat_mul_exp_neg_sqrt.const_mul D
  apply squeeze_zero'
  · filter_upwards with k
    apply div_nonneg
    · rw [blaschkeActiveWaterReturnDefect]
      have hbase : 0 < 1 - a ^ (2 : ℕ) := by nlinarith
      positivity
    · exact (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop 1] with k hk
    let S := blaschkeSqrtShiftedScale K k
    let L := blaschkeShiftedScale K k
    have hStail : blaschkeSpectralOffset a ≤ S := by
      dsimp only [S, blaschkeSqrtShiftedScale,
        blaschkeShiftedScale]
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      have hsqrt0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      linarith
    have hSnonneg : 0 ≤ S := by
      dsimp only [S, blaschkeSqrtShiftedScale,
        blaschkeShiftedScale]
      positivity
    have hdefect :=
      blaschkeActiveWaterReturnDefect_linear_exp_bound
        a ha0 ha1 hStail hSnonneg
    have hsqrtLe :
        Real.sqrt (k : ℝ) ≤ (k : ℝ) := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · nlinarith [show (1 : ℝ) ≤ k by exact_mod_cast hk]
    have hscale :
        1 + S ≤ (K + 2) * (1 + (k : ℝ)) := by
      dsimp only [S, blaschkeSqrtShiftedScale,
        blaschkeShiftedScale]
      nlinarith
    have hfactor :
        C * (1 + S) ≤ D * (1 + (k : ℝ)) := by
      dsimp only [D]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hscale hC
    have hratio :
        blaschkeActiveWaterReturnDefect a S / Real.exp (-L) ≤
          (C * (1 + S)) * Real.exp (-Real.sqrt (k : ℝ)) := by
      have hden : 0 < Real.exp (-L) := Real.exp_pos _
      apply (div_le_iff₀ hden).2
      calc
        blaschkeActiveWaterReturnDefect a S ≤
            C * (1 + S) * Real.exp (-S) := by
          simpa only [C] using hdefect
        _ = (C * (1 + S) * Real.exp (-Real.sqrt (k : ℝ))) *
              Real.exp (-L) := by
          have hSL :
              S = L + Real.sqrt (k : ℝ) := by rfl
          rw [hSL, neg_add, Real.exp_add]
          ring
    calc
      blaschkeActiveWaterReturnDefect a
          (blaschkeSqrtShiftedScale K k) /
          Real.exp (-blaschkeShiftedScale K k) =
          blaschkeActiveWaterReturnDefect a S /
            Real.exp (-L) := by rfl
      _ ≤ (C * (1 + S)) *
          Real.exp (-Real.sqrt (k : ℝ)) := hratio
      _ ≤ D * (1 + (k : ℝ)) *
          Real.exp (-Real.sqrt (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
      _ = D * ((1 + (k : ℝ)) *
          Real.exp (-Real.sqrt (k : ℝ))) := by ring
  · exact hmajor

theorem eventually_blaschkeActiveWaterReturnDefect_sqrtShift_le
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKnonneg : 0 ≤ K) :
    ∀ᶠ k in atTop,
      blaschkeActiveWaterReturnDefect a
          (blaschkeSqrtShiftedScale K k) ≤
        Real.exp (-blaschkeShiftedScale K k) := by
  have hratio :=
    tendsto_blaschkeActiveWaterReturnDefect_sqrtShift_ratio_zero
      a ha0 ha1 hKtail hKnonneg
  have hevent :
      ∀ᶠ k in atTop,
        blaschkeActiveWaterReturnDefect a
            (blaschkeSqrtShiftedScale K k) /
          Real.exp (-blaschkeShiftedScale K k) < 1 :=
    (tendsto_order.1 hratio).2 1 zero_lt_one
  filter_upwards [hevent] with k hk
  exact (div_lt_one (Real.exp_pos _)).mp hk |>.le

/--
At the same unshifted target `exp (-(k+K))` used by the probabilistic lower
clock, every phase packet eventually has a finite constructive deadline
evaluated only a square-root depth farther out.
-/
theorem eventually_exists_blaschkeFirstCoherenceTimeDeadline_sqrtShift
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKzero : blaschkeSpectralSlope a ≤ K)
    (hKnonneg : 0 ≤ K) :
    ∀ᶠ k in atTop,
      ∃ T : ℕ,
        (∀ x : ℕ → UnitAddCircle,
          countableTorusWeightedFirstCoherenceTime
              (blaschkeLocalizedWeight a) x
              (Real.exp (-blaschkeShiftedScale K k)) ≤ T) ∧
        Real.log (T : ℝ) ≤
          blaschkeDepthWaterEntropy a
              (blaschkeSqrtShiftedScale K k) +
            (blaschkeActiveTailRadius a
                (blaschkeSqrtShiftedScale K k) + 1 : ℕ) *
              Real.log projectivePhaseResolutionConstant := by
  filter_upwards [
    eventually_blaschkeActiveWaterReturnDefect_sqrtShift_le
      a ha0 ha1 hKtail hKnonneg] with k hk
  have hStail :
      blaschkeSpectralOffset a ≤ blaschkeSqrtShiftedScale K k := by
    rw [blaschkeSqrtShiftedScale, blaschkeShiftedScale]
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    have hsqrt0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
    linarith
  have hSzero :
      blaschkeSpectralSlope a ≤ blaschkeSqrtShiftedScale K k := by
    rw [blaschkeSqrtShiftedScale, blaschkeShiftedScale]
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    have hsqrt0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
    linarith
  exact
    exists_blaschkeFirstCoherenceTimeDeadline_of_activeWaterDefect_le
      a ha0 ha1 hStail hSzero hk

end RHTower
