import GaloisForLFunctions.RHTower.WallBoundaryTransportCancellation
import GaloisForLFunctions.RHTower.WallTailIntegrationByParts

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
one power of the resolvent derivative, hence one power of `(1+x)^{-1}`, whose square is integrable —
no Laplace representation and no oscillation are needed for this term. -/
theorem lintegral_sq_secondBoundary_ne_top {σ m μ₀ Y : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀) (hY : 1 ≤ Y)
    {g : ℝ → X} (hg : IntegrableOn g (Icc m (m + 1)))
    (hfloor : ∀ x ∈ Ioi Y, ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L) :
    (∫⁻ x in Ioi Y, ‖secondBoundary T g m σ x‖ₑ ^ 2) ≠ ⊤ := by
  set c : ℝ := (μ₀⁻¹) ^ 3 * (3 + Real.pi) with hc
  have hcnn : 0 ≤ c := by
    have : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [hc]
    positivity
  set N : ℝ := ∫ L in Icc m (m + 1), ‖g L‖ with hN
  have hNnn : 0 ≤ N := by
    rw [hN]
    exact integral_nonneg fun L => norm_nonneg _
  refine lintegral_sq_ray_powerTail_ne_top (C := c * N) (p := 1) (by norm_num) ?_
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := le_trans hY (le_of_lt hx)
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have habs : |x| = x := abs_of_pos hx0
  -- the pointwise bound on the block
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

end GaloisForLFunctions.RHTower
