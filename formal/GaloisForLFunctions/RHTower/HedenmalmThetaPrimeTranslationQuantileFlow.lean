import GaloisForLFunctions.RHTower.FrankensteinThetaPrimeTranslationCommonForcing

/-!
# Prime translation is a parabolic flow of the theta quantile boundary

The rank-one connection absorbing Hedenmalm's integer-translation anomaly has a simple exact
normal form.  In theta probability coordinates, define

`Phi_n(t) = F(Q(t) + log n)`.

These maps form the positive-integer translation semigroup by composition.  Every `n > 1` moves
every interior quantile strictly toward the right boundary, so the common-forcing connection is
flat but not stationary.

More sharply, the covariant source inverse is

`U B_n U^-1 g = i q(t) (integral_0^t g - Phi_n(t) integral_0^1 g)`.

Thus the rank-one anomaly connection does not remove the universal pinned-Volterra boundary
current.  It replaces the pinning coordinate `t` by the strict parabolic translate `Phi_n(t)`.
This identifies the exact source of the remaining Route-P orientation: multiplicative flatness
transports the boundary port toward an endpoint rather than forcing Julia saturation.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmPrimeTranslation

namespace HedenmalmThetaSource

/-- Theta probability-coordinate action of normalized positive-integer translation. -/
def thetaIntegerQuantileFlow (n : ℕ) (t : ℝ) : ℝ :=
  thetaSource.cdfFun (thetaSource.quantileFun t + Real.log n)

theorem thetaIntegerQuantileFlow_mem_Ioo (n : ℕ) (t : ℝ) :
    thetaIntegerQuantileFlow n t ∈ Ioo (0 : ℝ) 1 := by
  exact thetaSource.cdfFun_mem_Ioo _

@[simp] theorem thetaIntegerQuantileFlow_one {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    thetaIntegerQuantileFlow 1 t = t := by
  rw [thetaIntegerQuantileFlow]
  norm_num
  exact thetaSource.cdfFun_quantile ht

/-- Multiplication of integer labels is composition of their quantile boundary flows. -/
theorem thetaIntegerQuantileFlow_mul
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    thetaIntegerQuantileFlow (m * n) t =
      thetaIntegerQuantileFlow m (thetaIntegerQuantileFlow n t) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [thetaIntegerQuantileFlow, thetaIntegerQuantileFlow,
    thetaIntegerQuantileFlow, thetaSource.quantile_cdfFun]
  congr 1
  rw [Nat.cast_mul, Real.log_mul hm0 hn0]
  ring

/-- Every genuine integer dilation moves every interior quantile strictly to the right. -/
theorem thetaIntegerQuantileFlow_gt
    {n : ℕ} (hn : 1 < n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    t < thetaIntegerQuantileFlow n t := by
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [thetaIntegerQuantileFlow]
  calc
    t = thetaSource.cdfFun (thetaSource.quantileFun t) :=
      (thetaSource.cdfFun_quantile ht).symm
    _ < thetaSource.cdfFun (thetaSource.quantileFun t + Real.log n) :=
      thetaSource.strictMono_cdfFun (by linarith [Real.log_pos hnR])

theorem thetaIntegerQuantileFlow_ne_self
    {n : ℕ} (hn : 1 < n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    thetaIntegerQuantileFlow n t ≠ t :=
  (thetaIntegerQuantileFlow_gt hn ht).ne'

/-- Function-level quantile transform respects subtraction. -/
theorem quantileTransform_sub_apply (f g : ℝ → ℂ) (t : ℝ) :
    quantileTransform thetaSource (fun x => f x - g x) t =
      quantileTransform thetaSource f t - quantileTransform thetaSource g t := by
  unfold quantileTransform
  ring

/-- Function-level quantile transform respects a constant complex multiplier. -/
theorem quantileTransform_const_mul_apply (c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    quantileTransform thetaSource (fun x => c * f x) t =
      c * quantileTransform thetaSource f t := by
  unfold quantileTransform
  ring

/-- The source mass functional becomes the pinned mean in quantile coordinates. -/
theorem sourceFunctional_eq_sqrt_mass_mul_pinnedMean
    (f : SourceSpace thetaSource) :
    sourceFunctional (fun x => f x) =
      (Real.sqrt thetaSource.mass : ℂ) *
        pinnedMean (quantileUnitary thetaSource f) := by
  have hmean := pinnedMean_quantileUnitary thetaSource f
  rw [integral_quantileTransform thetaSource
    (integrable_sourceSpace thetaSource f).aestronglyMeasurable] at hmean
  have hsqrt : (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
  rw [sourceFunctional, hmean]
  field_simp

/-- Exact quantile image of the universal integer-translation anomaly. -/
theorem quantileTransform_integerAnomaly_eq_primeBoundaryDisplacement
    {n : ℕ} (_hn : 0 < n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    quantileTransform thetaSource (integerAnomaly thetaSource n) t =
      Complex.I * thetaIntegerShiftScale n *
        (Real.sqrt thetaSource.mass : ℂ) *
          (quantileSpeed thetaSource t : ℂ) *
            ((thetaIntegerQuantileFlow n t : ℝ) - t : ℂ) := by
  have hk : (thetaSource.k (thetaSource.quantileFun t) : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.pos_k _).ne'
  have hmass : (thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast thetaSource.mass_ne_zero
  have hsqrtSq : (Real.sqrt thetaSource.mass : ℂ) ^ 2 =
      (thetaSource.mass : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt thetaSource.mass_pos.le]
  rw [quantileTransform, integerAnomaly_eq, thetaIntegerQuantileFlow,
    thetaSource.cdfFun_quantile ht, quantileSpeed, thetaIntegerShiftScale]
  push_cast
  field_simp [hk, hmass, hsqrtSq]

/-- **P-G103 covariant quantile normal form.**  Absorbing the rank-one prime anomaly changes the
universal pinned coordinate from `t` to its strict prime translate `Phi_n(t)` and does nothing
else. -/
theorem quantileTransform_thetaIntegerCovariantSourceInverse_eq_primePinned
    {n : ℕ} (hn : 0 < n) (f : SourceSpace thetaSource)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    quantileTransform thetaSource
        (thetaIntegerCovariantSourceInverse n (fun x => f x)) t =
      Complex.I * (quantileSpeed thetaSource t : ℂ) *
        (pinnedPrefix (quantileUnitary thetaSource f) t -
          (thetaIntegerQuantileFlow n t : ℂ) *
            pinnedMean (quantileUnitary thetaSource f)) := by
  have hscale : thetaIntegerShiftScale n ≠ 0 :=
    thetaIntegerShiftScale_ne_zero hn
  have hmass : (thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast thetaSource.mass_ne_zero
  have hsqrt : (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
  unfold thetaIntegerCovariantSourceInverse
  change quantileTransform thetaSource (fun x =>
    sourceInverse thetaSource (fun y => f y) x -
      (sourceFunctional (fun y => f y) /
        (thetaIntegerShiftScale n * (thetaSource.mass : ℂ))) *
          integerAnomaly thetaSource n x) t = _
  rw [quantileTransform_sub_apply,
    quantileTransform_const_mul_apply,
    quantileTransform_sourceInverse_eq_pinned thetaSource f ht,
    quantileTransform_integerAnomaly_eq_primeBoundaryDisplacement hn ht,
    sourceFunctional_eq_sqrt_mass_mul_pinnedMean]
  rw [pinnedVolterraFun]
  have hsqrtSq : (Real.sqrt thetaSource.mass : ℂ) ^ 2 =
      (thetaSource.mass : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt thetaSource.mass_pos.le]
  have hconnection :
      ((Real.sqrt thetaSource.mass : ℂ) *
          pinnedMean (quantileUnitary thetaSource f) /
            (thetaIntegerShiftScale n * (thetaSource.mass : ℂ))) *
        (Complex.I * thetaIntegerShiftScale n *
          (Real.sqrt thetaSource.mass : ℂ) *
            (quantileSpeed thetaSource t : ℂ) *
              ((thetaIntegerQuantileFlow n t : ℝ) - t : ℂ)) =
        Complex.I * (quantileSpeed thetaSource t : ℂ) *
          pinnedMean (quantileUnitary thetaSource f) *
            ((thetaIntegerQuantileFlow n t : ℝ) - t : ℂ) := by
    rw [← hsqrtSq]
    field_simp [hscale, hsqrt]
  rw [hconnection]
  ring

/-- On the constant boundary mode the covariant pinned primitive is strictly negative at every
interior point for every genuine prime translation.  Flat common forcing therefore transports,
rather than neutralizes, the boundary port. -/
theorem primePinnedConstantMode_strictly_negative
    {n : ℕ} (hn : 1 < n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    t - thetaIntegerQuantileFlow n t < 0 := by
  linarith [thetaIntegerQuantileFlow_gt hn ht]

end HedenmalmThetaSource

end

end RHTower
