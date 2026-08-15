import GaloisForLFunctions.RHTower.WallBoundaryTransportCancellation
import GaloisForLFunctions.RHTower.WallTailIntegrationByParts
import GaloisForLFunctions.RHTower.SuzukiWallTailAmplitude
import GaloisForLFunctions.HTGeometry.FrequencyLineSplit
import GaloisForLFunctions.RHTower.StripPropagatorRayMass

/-!
# Ray estimates for the propagated terms of the block expansion

Three of the four terms of the propagated two-fold expansion are square integrable on the terminal
ray by decay alone, and each for a different reason.

*The propagated datum* decays like `(1+|x|)^{-p}` with `p = 1/2 + σ > 1/2`, which is exactly the
threshold at which the square becomes integrable; it is square integrable on the whole line, hence on
any ray.

*The second boundary term* carries one power of the resolvent derivative, hence one power of
`(1+x)^{-1}`, and `2 > 1`.  No oscillation and no Laplace representation are used: the block average
only contributes the `L¹` mass of the profile, because the bound is uniform over the block.

*The remainder* is a Hardy average, and the scalar form of the weighted Hardy inequality applies
verbatim — the density is the same function for every block vector, only the mass changing, so the
block integral factors out before the Hardy estimate is used.

Only the first boundary term is left; it does not decay, and it is the one the accretive Laplace
representation is for.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

section Ray

variable {A : Type*} [NormedAddCommGroup A]

/-- **A power tail bounded only on a ray is square integrable there.** -/
theorem lintegral_sq_ray_powerTail_ne_top {f : ℝ → A} {C p Y : ℝ} (hp : 1 / 2 < p)
    (hf : ∀ x ∈ Ioi Y, ‖f x‖ ≤ C * (1 + |x|) ^ (-p)) :
    (∫⁻ x in Ioi Y, ‖f x‖ₑ ^ 2) ≠ ⊤ := by
  have hmaj : ∀ x ∈ Ioi Y, ‖f x‖ₑ ^ 2
      ≤ ENNReal.ofReal (C ^ 2) * oneAddAbsWeight (2 * p) x := by
    intro x hx
    have hx0 : (0 : ℝ) < 1 + |x| := by positivity
    have hbase := hf x hx
    have hsq : ‖f x‖ ^ 2 ≤ C ^ 2 * (1 + |x|) ^ (-(2 * p)) := by
      refine (pow_le_pow_left₀ (norm_nonneg _) hbase 2).trans (le_of_eq ?_)
      rw [mul_pow, ← Real.rpow_natCast ((1 + |x|) ^ (-p)) 2, ← Real.rpow_mul hx0.le]
      congr 2
      push_cast
      ring
    calc ‖f x‖ₑ ^ 2 = ENNReal.ofReal (‖f x‖ ^ 2) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (C ^ 2 * (1 + |x|) ^ (-(2 * p))) := ENNReal.ofReal_le_ofReal hsq
      _ = ENNReal.ofReal (C ^ 2) * oneAddAbsWeight (2 * p) x := by
          rw [oneAddAbsWeight, ← ENNReal.ofReal_mul (by positivity)]
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' measurableSet_Ioi hmaj)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  refine ne_top_of_le_ne_top
    (lintegral_oneAddAbsWeight_ne_top (s := 2 * p) (by linarith)) ?_
  exact setLIntegral_le_lintegral _ _

/-- **A power tail on a ray, quantitatively.**  The ray mass of the weight decays in the radius,
which is what turns a bound accumulated below the radius into a single power of it. -/
theorem lintegral_sq_ray_powerTail_le {f : ℝ → A} {C p Y : ℝ} (hp : 1 / 2 < p) (hY : 0 < Y)
    (hf : ∀ x ∈ Ioi Y, ‖f x‖ ≤ C * (1 + |x|) ^ (-p)) :
    (∫⁻ x in Ioi Y, ‖f x‖ₑ ^ 2)
      ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (Y ^ (1 - 2 * p) / (2 * p - 1)) := by
  have hmaj : ∀ x ∈ Ioi Y, ‖f x‖ₑ ^ 2
      ≤ ENNReal.ofReal (C ^ 2) * oneAddAbsWeight (2 * p) x := by
    intro x hx
    have hx0 : (0 : ℝ) < 1 + |x| := by positivity
    have hbase := hf x hx
    have hsq : ‖f x‖ ^ 2 ≤ C ^ 2 * (1 + |x|) ^ (-(2 * p)) := by
      refine (pow_le_pow_left₀ (norm_nonneg _) hbase 2).trans (le_of_eq ?_)
      rw [mul_pow, ← Real.rpow_natCast ((1 + |x|) ^ (-p)) 2, ← Real.rpow_mul hx0.le]
      congr 2
      push_cast
      ring
    calc ‖f x‖ₑ ^ 2 = ENNReal.ofReal (‖f x‖ ^ 2) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (C ^ 2 * (1 + |x|) ^ (-(2 * p))) := ENNReal.ofReal_le_ofReal hsq
      _ = ENNReal.ofReal (C ^ 2) * oneAddAbsWeight (2 * p) x := by
          rw [oneAddAbsWeight, ← ENNReal.ofReal_mul (by positivity)]
  calc (∫⁻ x in Ioi Y, ‖f x‖ₑ ^ 2)
      ≤ ∫⁻ x in Ioi Y, ENNReal.ofReal (C ^ 2) * oneAddAbsWeight (2 * p) x :=
        setLIntegral_mono' measurableSet_Ioi hmaj
    _ = ENNReal.ofReal (C ^ 2) * ∫⁻ x in Ioi Y, oneAddAbsWeight (2 * p) x :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (Y ^ (1 - 2 * p) / (2 * p - 1)) :=
        mul_le_mul' le_rfl (lintegral_oneAddAbsWeight_Ioi_le (by linarith) hY)

/-- **The weighted Hardy transfer with a scalar density, quantitatively.**  A profile obeying the
variation-of-constants bound with propagator decay `x^{-p}`, `p > 1/2`, and a purely accumulated
forcing has squared ray mass at most `K²(p−1/2)^{-2}` times the squared mass of the density.  The
density is scalar because in the block estimate it is the *same* function for every block vector,
only the mass changing. -/
theorem lintegral_sq_le_of_hardyBound_scalar {p : ℝ} (hp : 1 / 2 < p) {f : ℝ → A}
    {H : ℝ → ℝ≥0∞} {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x ∈ Ioi (1 : ℝ), ‖f x‖ₑ ≤ ENNReal.ofReal (K * x ^ (-p))
      * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t)
    (hmeas : AEMeasurable H (volume.restrict (Ioi (1 : ℝ)))) :
    (∫⁻ x in Ioi (1 : ℝ), ‖f x‖ₑ ^ 2)
      ≤ ENNReal.ofReal (K ^ 2)
        * (ENNReal.ofReal ((p - 1 / 2)⁻¹ ^ 2) * ∫⁻ t in Ioi (1 : ℝ), H t ^ 2) := by
  have hmaj : ∀ x ∈ Ioi (1 : ℝ), ‖f x‖ₑ ^ 2
      ≤ ENNReal.ofReal (K ^ 2)
        * (ENNReal.ofReal (x ^ (-p))
            * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2 := by
    intro x hx
    calc ‖f x‖ₑ ^ 2
        ≤ (ENNReal.ofReal (K * x ^ (-p))
            * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2 :=
          pow_le_pow_left' (hbound x hx) 2
      _ = ENNReal.ofReal (K ^ 2)
            * (ENNReal.ofReal (x ^ (-p))
                * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2 := by
          rw [ENNReal.ofReal_mul hK, mul_pow, mul_pow, ← ENNReal.ofReal_pow hK, mul_assoc,
            ← mul_pow]
  refine le_trans (setLIntegral_mono' measurableSet_Ioi hmaj) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul' le_rfl (HTGeometry.lintegral_hardyAverage_sq_le hp hmeas)

/-- **The scalar Hardy transfer on a terminal ray.**  The bound is needed only above the threshold;
the Hardy inequality is applied on the whole ray `(1,∞)` and restricted afterwards. -/
theorem lintegral_sq_ray_le_of_hardyBound_scalar {p Y : ℝ} (hp : 1 / 2 < p) (hY : 1 ≤ Y)
    {f : ℝ → A} {H : ℝ → ℝ≥0∞} {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x ∈ Ioi Y, ‖f x‖ₑ ≤ ENNReal.ofReal (K * x ^ (-p))
      * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t)
    (hmeas : AEMeasurable H (volume.restrict (Ioi (1 : ℝ)))) :
    (∫⁻ x in Ioi Y, ‖f x‖ₑ ^ 2)
      ≤ ENNReal.ofReal (K ^ 2)
        * (ENNReal.ofReal ((p - 1 / 2)⁻¹ ^ 2) * ∫⁻ t in Ioi (1 : ℝ), H t ^ 2) := by
  set G : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (x ^ (-p))
    * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t with hG
  have hmaj : ∀ x ∈ Ioi Y, ‖f x‖ₑ ^ 2 ≤ ENNReal.ofReal (K ^ 2) * G x ^ 2 := by
    intro x hx
    calc ‖f x‖ₑ ^ 2
        ≤ (ENNReal.ofReal (K * x ^ (-p))
            * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2 :=
          pow_le_pow_left' (hbound x hx) 2
      _ = ENNReal.ofReal (K ^ 2) * G x ^ 2 := by
          rw [hG, ENNReal.ofReal_mul hK, mul_pow, mul_pow, ← ENNReal.ofReal_pow hK, mul_assoc,
            ← mul_pow]
  have hsub : Ioi Y ⊆ Ioi (1 : ℝ) := by
    intro z hz
    exact lt_of_le_of_lt hY hz
  calc (∫⁻ x in Ioi Y, ‖f x‖ₑ ^ 2)
      ≤ ∫⁻ x in Ioi Y, ENNReal.ofReal (K ^ 2) * G x ^ 2 :=
        setLIntegral_mono' measurableSet_Ioi hmaj
    _ ≤ ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (K ^ 2) * G x ^ 2 := lintegral_mono_set hsub
    _ = ENNReal.ofReal (K ^ 2) * ∫⁻ x in Ioi (1 : ℝ), G x ^ 2 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (K ^ 2)
          * (ENNReal.ofReal ((p - 1 / 2)⁻¹ ^ 2) * ∫⁻ t in Ioi (1 : ℝ), H t ^ 2) :=
        mul_le_mul' le_rfl (HTGeometry.lintegral_hardyAverage_sq_le hp hmeas)

end Ray

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {T : X →L[ℂ] X}

/-- The propagated second boundary term of the two-fold expansion, as a block average. -/
def secondBoundary (T : X →L[ℂ] X) (g : ℝ → X) (m σ x : ℝ) : X :=
  ∫ L in Icc m (m + 1), Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) •
    (invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g L))

/-- **The propagated second boundary term is square integrable on the terminal ray.**  It carries
one power of the resolvent derivative, hence one power of `(1+x)^{-1}`, whose square has finite ray
mass — no Laplace representation and no oscillation are needed for this term, and the bound does not
grow with the threshold. -/
theorem lintegral_sq_secondBoundary_le {σ m μ₀ Y : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀) (hY : 1 ≤ Y)
    {g : ℝ → X} (hg : IntegrableOn g (Icc m (m + 1)))
    (hfloor : ∀ x ∈ Ioi Y, ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L) :
    (∫⁻ x in Ioi Y, ‖secondBoundary T g m σ x‖ₑ ^ 2)
      ≤ ENNReal.ofReal
          ((((μ₀⁻¹) ^ 3 * (3 + Real.pi)) * ∫ L in Icc m (m + 1), ‖g L‖) ^ 2) := by
  set c : ℝ := (μ₀⁻¹) ^ 3 * (3 + Real.pi) with hc
  have hcnn : 0 ≤ c := by
    have : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [hc]
    positivity
  set N : ℝ := ∫ L in Icc m (m + 1), ‖g L‖ with hN
  have hNnn : 0 ≤ N := by
    rw [hN]
    exact integral_nonneg fun L => norm_nonneg _
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  have hbase := lintegral_sq_ray_powerTail_le (f := secondBoundary T g m σ) (C := c * N)
    (p := 1) (Y := Y) (by norm_num) hY0 ?_
  · refine hbase.trans ?_
    have htail : ENNReal.ofReal (Y ^ (1 - 2 * (1 : ℝ)) / (2 * (1 : ℝ) - 1)) ≤ 1 := by
      have hval : Y ^ (1 - 2 * (1 : ℝ)) / (2 * (1 : ℝ) - 1) = Y ^ (-(1 : ℝ)) := by
        norm_num
      rw [hval]
      refine (ENNReal.ofReal_le_one).mpr ?_
      rw [Real.rpow_neg_one]
      exact inv_le_one_of_one_le₀ hY
    calc ENNReal.ofReal ((c * N) ^ 2)
          * ENNReal.ofReal (Y ^ (1 - 2 * (1 : ℝ)) / (2 * (1 : ℝ) - 1))
        ≤ ENNReal.ofReal ((c * N) ^ 2) * 1 := mul_le_mul' le_rfl htail
      _ = ENNReal.ofReal ((c * N) ^ 2) := mul_one _
  · intro x hx
    have hx1 : (1 : ℝ) ≤ x := le_trans hY (le_of_lt hx)
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    have habs : |x| = x := abs_of_pos hx0
    have hpt : ∀ L ∈ Icc m (m + 1),
        ‖Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) •
          (invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g L))‖
          ≤ (c * (1 + x)⁻¹) * ‖g L‖ := by
      intro L hL
      rw [norm_smul, norm_expPhase, one_mul]
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact norm_invFamilyProduct_wallGeneratorShift_le hσ0 hσ1 hμ hx1 (hfloor x hx L hL)
    have hint : IntegrableOn (fun L => (c * (1 + x)⁻¹) * ‖g L‖) (Icc m (m + 1)) :=
      hg.norm.const_mul _
    have hle := MeasureTheory.norm_integral_le_of_norm_le hint
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with L hL using hpt L hL)
    have hconst : (∫ L in Icc m (m + 1), (c * (1 + x)⁻¹) * ‖g L‖) = (c * (1 + x)⁻¹) * N := by
      rw [hN, integral_const_mul]
    have hbound : ‖secondBoundary T g m σ x‖ ≤ (c * (1 + x)⁻¹) * N := by
      rw [secondBoundary]
      rw [hconst] at hle
      exact hle
    have hrw : (1 + |x|) ^ (-(1 : ℝ)) = (1 + x)⁻¹ := by
      rw [habs, Real.rpow_neg_one]
    rw [hrw]
    calc ‖secondBoundary T g m σ x‖ ≤ (c * (1 + x)⁻¹) * N := hbound
      _ = c * N * (1 + x)⁻¹ := by ring

/-- **The propagated datum is square integrable on any ray**, being so on the whole line. -/
theorem lintegral_sq_ray_stripPropagator_apply_ne_top [Nontrivial X] {E : ℂ → ℂ}
    (hT : IsSelfAdjoint T) (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (Y : ℝ) (c : X) :
    (∫⁻ x in Ioi Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ₑ ^ 2) ≠ ⊤ :=
  ne_top_of_le_ne_top (lintegral_sq_stripPropagator_apply_ne_top hT hE hσ0 hσ1 c)
    (setLIntegral_le_lintegral _ _)

/-! ## The propagated remainder -/

section Remainder

variable [Nontrivial X] {E : ℂ → ℂ}

/-- The propagated remainder of the two-fold expansion, as a block average. -/
def tailRemainder (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (m σ Y x : ℝ) : X :=
  ∫ L in Icc m (m + 1), stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
    ((∫ t in Y..x, wallPhaseMap E T σ L t
        * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
            (wallGeneratorD2 X σ) t) (g L))

/-- The quadratic amplitude decay, transported and rescaled to the Hardy normalization. -/
theorem powerRatio_le_hardyDensity {p t : ℝ} (ht : 1 < t) :
    (1 + t) ^ p * ((1 + t)⁻¹) ^ 2 ≤ t ^ (p - 1) * wallTailDensity p t := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have h := hardyRescale_le_wallTailDensity (p := p) ht
  have hpow : t ^ (p - 1) * (t ^ (1 - p) * ((1 + t)⁻¹) ^ 2 * (1 + t) ^ p)
      = (1 + t) ^ p * ((1 + t)⁻¹) ^ 2 := by
    have hsum : t ^ (p - 1) * t ^ (1 - p) = 1 := by
      rw [← Real.rpow_add ht0, show (p - 1) + (1 - p) = (0 : ℝ) by ring, Real.rpow_zero]
    calc t ^ (p - 1) * (t ^ (1 - p) * ((1 + t)⁻¹) ^ 2 * (1 + t) ^ p)
        = (t ^ (p - 1) * t ^ (1 - p)) * (((1 + t)⁻¹) ^ 2 * (1 + t) ^ p) := by ring
      _ = (1 + t) ^ p * ((1 + t)⁻¹) ^ 2 := by rw [hsum, one_mul]; ring
  calc (1 + t) ^ p * ((1 + t)⁻¹) ^ 2
      = t ^ (p - 1) * (t ^ (1 - p) * ((1 + t)⁻¹) ^ 2 * (1 + t) ^ p) := hpow.symm
    _ ≤ t ^ (p - 1) * wallTailDensity p t :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ht0.le _)

/-- **The propagated remainder is square integrable on the terminal ray.**  Its amplitude decays
quadratically, so after transport it is a Hardy average whose density is `wallTailDensity`; the block
average contributes only the `L¹` mass of the profile, because the density does not depend on the
block variable. -/
theorem exists_bound_lintegral_sq_tailRemainder {σ μ₀ : ℝ}
    (hT : IsSelfAdjoint T) (hEbr : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m Y : ℝ, 1 ≤ Y → ∀ g : ℝ → X, IntegrableOn g (Icc m (m + 1)) →
      (∀ t ∈ Ioi Y, ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ t + L) →
      (∫⁻ x in Ioi Y, ‖tailRemainder E T g m σ Y x‖ₑ ^ 2)
        ≤ ENNReal.ofReal C * (∫⁻ L in Icc m (m + 1), ‖g L‖ₑ) ^ 2 := by
  obtain ⟨K₁, hK₁, hb₁⟩ := exists_bound_stripPropagator_line hT hEbr hσ0 hσ1
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_bound_stripPropagatorInv_line hT hEbr hσ0 hσ1
  set p : ℝ := 1 / 2 + σ with hpdef
  have hp2 : 1 / 2 < p := by rw [hpdef]; linarith
  set Camp : ℝ := wallAmplitudeConst μ₀ with hCampdef
  have hCampnn : 0 ≤ Camp := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [hCampdef, wallAmplitudeConst]
    positivity
  set Mwtd : ℝ≥0∞ := ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (wallTailDensity p t) ^ 2 with hMdef
  have hMfin : Mwtd ≠ ⊤ := by
    rw [hMdef]
    exact (lintegral_sq_wallTailDensity_lt_top (by linarith)).ne
  refine ⟨K₁ ^ 2 * ((p - 1 / 2)⁻¹ ^ 2 * ((K₂ * Camp) ^ 2 * Mwtd.toReal)), by positivity,
    fun m Y hY g hg hfloor => ?_⟩
  set Ne : ℝ≥0∞ := ∫⁻ L in Icc m (m + 1), ‖g L‖ₑ with hNedef
  have hNefin : Ne ≠ ⊤ := by
    rw [hNedef]
    exact hg.2.ne
  set D : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (K₂ * Camp * wallTailDensity p t) with hDdef
  set H : ℝ → ℝ≥0∞ := fun t => Ne * D t with hHdef
  have hDmeas : Measurable D := by
    rw [hDdef]
    unfold wallTailDensity
    fun_prop
  have hHmeas : AEMeasurable H (volume.restrict (Ioi (1 : ℝ))) :=
    (hDmeas.const_mul Ne).aemeasurable
  -- the amplitude bound on the tail
  have hamp : ∀ t ∈ Ioi Y, ∀ L ∈ Icc m (m + 1),
      ‖wallPhaseMap E T σ L t
        * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
            (wallGeneratorD2 X σ) t‖
        ≤ t ^ (p - 1) * (K₂ * Camp * wallTailDensity p t) := by
    intro t ht L hL
    have ht1 : (1 : ℝ) < t := lt_of_le_of_lt hY ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
    have habs : |t| = t := abs_of_pos ht0
    have hW : ‖wallPhaseMap E T σ L t‖ ≤ K₂ * (1 + t) ^ p := by
      rw [wallPhaseMap, norm_smul, norm_expPhase, one_mul]
      have hb := hb₂ t
      rwa [habs] at hb
    have hA : ‖invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
        (wallGeneratorD2 X σ) t‖ ≤ Camp * ((1 + t)⁻¹) ^ 2 :=
      norm_invFamilyProductDeriv_wallGeneratorShift_le hσ0 hσ1 hμ ht1.le (hfloor t ht L hL)
    calc ‖wallPhaseMap E T σ L t
          * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
              (wallGeneratorD2 X σ) t‖
        ≤ ‖wallPhaseMap E T σ L t‖
          * ‖invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
              (wallGeneratorD2 X σ) t‖ := norm_mul_le _ _
      _ ≤ (K₂ * (1 + t) ^ p) * (Camp * ((1 + t)⁻¹) ^ 2) :=
          mul_le_mul hW hA (norm_nonneg _) (by positivity)
      _ = (K₂ * Camp) * ((1 + t) ^ p * ((1 + t)⁻¹) ^ 2) := by ring
      _ ≤ (K₂ * Camp) * (t ^ (p - 1) * wallTailDensity p t) :=
          mul_le_mul_of_nonneg_left (powerRatio_le_hardyDensity ht1) (by positivity)
      _ = t ^ (p - 1) * (K₂ * Camp * wallTailDensity p t) := by ring
  -- the pointwise Hardy bound
  have hpt : ∀ x ∈ Ioi Y, ‖tailRemainder E T g m σ Y x‖ₑ
      ≤ ENNReal.ofReal (K₁ * x ^ (-p))
        * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t := by
    intro x hx
    have hxY : Y ≤ x := hx.le
    have hx1 : (1 : ℝ) ≤ x := le_trans hY hxY
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    have habsx : |x| = x := abs_of_pos hx0
    set J : ℝ≥0∞ := ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * D t with hJdef
    have hAe : ∀ L ∈ Icc m (m + 1),
        ‖∫ t in Y..x, wallPhaseMap E T σ L t
          * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
              (wallGeneratorD2 X σ) t‖ₑ ≤ J := by
      intro L hL
      refine le_trans (enorm_intervalIntegral_le _ Y x) ?_
      rw [uIoc_of_le hxY]
      have hmono : (∫⁻ t in Ioc Y x, ‖wallPhaseMap E T σ L t
            * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
                (wallGeneratorD2 X σ) t‖ₑ)
          ≤ ∫⁻ t in Ioc Y x, ENNReal.ofReal (t ^ (p - 1)) * D t := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
        have htY : t ∈ Ioi Y := ht.1
        have hbase := hamp t htY L hL
        have ht0 : (0 : ℝ) < t := lt_trans (lt_of_lt_of_le zero_lt_one hY) htY
        rw [← ofReal_norm, hDdef]
        refine le_trans (ENNReal.ofReal_le_ofReal hbase) (le_of_eq ?_)
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _)]
      refine hmono.trans ?_
      rw [hJdef]
      exact lintegral_mono_set (fun z hz => ⟨lt_of_le_of_lt hY hz.1, hz.2⟩)
    have hstep : ‖tailRemainder E T g m σ Y x‖ₑ
        ≤ ∫⁻ L in Icc m (m + 1), ENNReal.ofReal (K₁ * (1 + x) ^ (-p)) * (J * ‖g L‖ₑ) := by
      refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
      refine setLIntegral_mono' measurableSet_Icc fun L hL => ?_
      have hprop : ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
          ≤ K₁ * (1 + x) ^ (-p) := by
        have hb := hb₁ x
        rwa [habsx] at hb
      have h1 : ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
            ((∫ t in Y..x, wallPhaseMap E T σ L t
              * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
                  (wallGeneratorD2 X σ) t) (g L))‖ₑ
          ≤ ENNReal.ofReal (K₁ * (1 + x) ^ (-p))
            * ‖(∫ t in Y..x, wallPhaseMap E T σ L t
                * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
                    (wallGeneratorD2 X σ) t) (g L)‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        exact le_trans (ContinuousLinearMap.le_opNorm _ _)
          (mul_le_mul_of_nonneg_right hprop (norm_nonneg _))
      have h2 : ‖(∫ t in Y..x, wallPhaseMap E T σ L t
            * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
                (wallGeneratorD2 X σ) t) (g L)‖ₑ ≤ J * ‖g L‖ₑ := by
        refine le_trans ?_ (mul_le_mul' (hAe L hL) le_rfl)
        rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)
      exact le_trans h1 (mul_le_mul' le_rfl h2)
    have hconst : (∫⁻ L in Icc m (m + 1),
        ENNReal.ofReal (K₁ * (1 + x) ^ (-p)) * (J * ‖g L‖ₑ))
        = ENNReal.ofReal (K₁ * (1 + x) ^ (-p)) * (J * Ne) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hNedef]
      congr 1
      exact lintegral_const_mul'' _ hg.1.enorm
    have hJH : J * Ne = ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t := by
      rw [hJdef, mul_comm, ← lintegral_const_mul' _ _ hNefin]
      refine lintegral_congr fun t => ?_
      rw [hHdef]
      ring
    have hxle : ENNReal.ofReal (K₁ * (1 + x) ^ (-p)) ≤ ENNReal.ofReal (K₁ * x ^ (-p)) := by
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hK₁.le)
      refine Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
    calc ‖tailRemainder E T g m σ Y x‖ₑ
        ≤ ∫⁻ L in Icc m (m + 1),
            ENNReal.ofReal (K₁ * (1 + x) ^ (-p)) * (J * ‖g L‖ₑ) := hstep
      _ = ENNReal.ofReal (K₁ * (1 + x) ^ (-p)) * (J * Ne) := hconst
      _ = ENNReal.ofReal (K₁ * (1 + x) ^ (-p))
            * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t := by rw [hJH]
      _ ≤ ENNReal.ofReal (K₁ * x ^ (-p))
            * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t :=
          mul_le_mul' hxle le_rfl
  -- the Hardy transfer
  have hHsq : (∫⁻ t in Ioi (1 : ℝ), H t ^ 2)
      ≤ Ne ^ 2 * (ENNReal.ofReal ((K₂ * Camp) ^ 2) * Mwtd) := by
    have hDsq : (∫⁻ t in Ioi (1 : ℝ), D t ^ 2)
        ≤ ENNReal.ofReal ((K₂ * Camp) ^ 2)
          * ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (wallTailDensity p t) ^ 2 := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      have hnn : 0 ≤ wallTailDensity p t := wallTailDensity_nonneg ht0
      rw [hDdef, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hnn,
        ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
    have hNe2 : Ne ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hNefin
    have hrw : (∫⁻ t in Ioi (1 : ℝ), H t ^ 2) = Ne ^ 2 * ∫⁻ t in Ioi (1 : ℝ), D t ^ 2 := by
      rw [← lintegral_const_mul' _ _ hNe2]
      refine lintegral_congr fun t => ?_
      rw [hHdef, mul_pow]
    rw [hrw]
    exact mul_le_mul' le_rfl (hDsq.trans (le_of_eq (by rw [hMdef])))
  refine le_trans (lintegral_sq_ray_le_of_hardyBound_scalar hp2 hY hK₁.le hpt hHmeas) ?_
  refine le_trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hHsq)) (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hMfin]
  ring

end Remainder

end GaloisForLFunctions.RHTower
