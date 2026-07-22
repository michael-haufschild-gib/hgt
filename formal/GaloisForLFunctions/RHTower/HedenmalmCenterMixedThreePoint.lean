import GaloisForLFunctions.HilbertMetric.ThreePointCorrelation
import GaloisForLFunctions.RHTower.ThetaCuspKernelLogConcavity

/-!
# Radial and three-point positivity for the Hedenmalm center density

Strict log-concavity of the actual theta source makes every reflected source product decrease
with the absolute displacement.  Center mixing preserves this order.  The resulting radial law,
together with the exact three-point correlation algebra, proves an unconditional
far-separated three-node positive-semidefinite chamber.

The complementary near-center cubic inequality remains open.  Nothing in this file asserts the
all-node positive definiteness equivalent to RH.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

private def thetaCuspReflectionLogProduct (u t : ℝ) : ℝ :=
  thetaCuspLogSource (u + t) + thetaCuspLogSource (u - t)

private theorem hasDerivAt_thetaCuspLogSource_deriv (x : ℝ) :
    HasDerivAt thetaCuspLogSource (deriv thetaCuspLogSource x) x := by
  have h := hasDerivAt_thetaCuspLogSource x
  convert h using 1
  exact h.deriv

private theorem hasDerivAt_thetaCuspReflectionLogProduct (u t : ℝ) :
    HasDerivAt (thetaCuspReflectionLogProduct u)
      (deriv thetaCuspLogSource (u + t) - deriv thetaCuspLogSource (u - t)) t := by
  have hplus := (hasDerivAt_thetaCuspLogSource_deriv (u + t)).comp t
    ((hasDerivAt_id t).const_add u)
  have hminus := (hasDerivAt_thetaCuspLogSource_deriv (u - t)).comp t
    ((hasDerivAt_id t).const_sub u)
  convert hplus.add hminus using 1
  all_goals simp [sub_eq_add_neg]

/-- For every source center, the reflected theta product is strictly decreasing with the
nonnegative displacement. -/
theorem strictAntiOn_thetaCuspFullSource_mul_reflect (u : ℝ) :
    StrictAntiOn
      (fun t : ℝ => thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t))
      (Ici 0) := by
  have hderivAnti : StrictAnti (deriv thetaCuspLogSource) :=
    strictAntiOn_univ.mp <|
      strictConcaveOn_thetaCuspLogSource.strictAntiOn_deriv fun x _ =>
        (hasDerivAt_thetaCuspLogSource x).differentiableAt
  have hlogAnti : StrictAntiOn (thetaCuspReflectionLogProduct u) (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
    · have hlogContinuous : Continuous thetaCuspLogSource :=
        contDiff_thetaCuspFullSource.continuous.log fun x =>
          (thetaCuspFullSource_pos_all x).ne'
      have hcontinuous : Continuous (thetaCuspReflectionLogProduct u) := by
        simpa [thetaCuspReflectionLogProduct] using
          (hlogContinuous.comp (continuous_const.add continuous_id)).add
            (hlogContinuous.comp (continuous_const.sub continuous_id))
      exact hcontinuous.continuousOn
    · intro t ht
      have ht0 : 0 < t := by simpa using ht
      rw [(hasDerivAt_thetaCuspReflectionLogProduct u t).deriv]
      exact sub_neg.mpr (hderivAnti (by linarith : u - t < u + t))
  intro s hs t ht hst
  have hlog := hlogAnti hs ht hst
  have hsplus := thetaCuspFullSource_pos_all (u + s)
  have hsminus := thetaCuspFullSource_pos_all (u - s)
  have htplus := thetaCuspFullSource_pos_all (u + t)
  have htminus := thetaCuspFullSource_pos_all (u - t)
  change thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) <
    thetaCuspFullSource (u + s) * thetaCuspFullSource (u - s)
  rw [show thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) =
      Real.exp (thetaCuspReflectionLogProduct u t) by
    simp [thetaCuspReflectionLogProduct, thetaCuspLogSource, Real.exp_add,
      Real.exp_log htplus, Real.exp_log htminus],
    show thetaCuspFullSource (u + s) * thetaCuspFullSource (u - s) =
      Real.exp (thetaCuspReflectionLogProduct u s) by
    simp [thetaCuspReflectionLogProduct, thetaCuspLogSource, Real.exp_add,
      Real.exp_log hsplus, Real.exp_log hsminus]]
  exact Real.exp_lt_exp.mpr hlog

/-- The actual center-mixed Hedenmalm density is radially nonincreasing on the nonnegative
half-line. -/
theorem antitoneOn_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    AntitoneOn (thetaCuspCenterMixedDensity a) (Ici 0) := by
  intro s hs t ht hst
  unfold thetaCuspCenterMixedDensity
  apply MeasureTheory.integral_mono_ae
  · simpa using integrableOn_thetaCuspCenterMixedIntegrand ha0 ha t
  · simpa using integrableOn_thetaCuspCenterMixedIntegrand ha0 ha s
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hweight : 0 ≤ r * Real.sinh (a * r) :=
      mul_nonneg hr.le (Real.sinh_nonneg_iff.mpr (mul_nonneg ha0 hr.le))
    have hproduct :=
      (strictAntiOn_thetaCuspFullSource_mul_reflect (r / 2)).antitoneOn hs ht hst
    exact mul_le_mul_of_nonneg_left hproduct hweight

/-- At positive aperture, the radial center density is strictly smaller away from the reflection
center. -/
theorem thetaCuspCenterMixedDensity_lt_zero
    {a t : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht : 0 < t) :
    thetaCuspCenterMixedDensity a t < thetaCuspCenterMixedDensity a 0 := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f0 : ℝ → ℝ := fun r =>
    r * Real.sinh (a * r) *
      (thetaCuspFullSource (r / 2) * thetaCuspFullSource (r / 2))
  let ft : ℝ → ℝ := fun r =>
    r * Real.sinh (a * r) *
      (thetaCuspFullSource (r / 2 + t) * thetaCuspFullSource (r / 2 - t))
  have hf0 : Integrable f0 mu := by
    simpa [f0, mu] using integrableOn_thetaCuspCenterMixedIntegrand ha0.le ha 0
  have hft : Integrable ft mu := by
    simpa [ft, mu] using integrableOn_thetaCuspCenterMixedIntegrand ha0.le ha t
  have hnonneg : 0 ≤ᵐ[mu] fun r => f0 r - ft r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hweight : 0 ≤ r * Real.sinh (a * r) :=
      mul_nonneg hr.le (Real.sinh_nonneg_iff.mpr (mul_nonneg ha0.le hr.le))
    have hproduct :=
      (strictAntiOn_thetaCuspFullSource_mul_reflect (r / 2)).antitoneOn
        (by norm_num) ht.le ht.le
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left (by simpa using hproduct) hweight)
  have hgap : 0 < ∫ r : ℝ in Ioi 0, f0 r - ft r := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg (hf0.sub hft)).2
    have hcontinuous : Continuous (fun r => f0 r - ft r) := by
      have hk : Continuous thetaCuspFullSource :=
        contDiff_thetaCuspFullSource.continuous
      dsimp [f0, ft]
      fun_prop (disch := aesop)
    have hopen : IsOpen (Function.support (fun r => f0 r - ft r) ∩ Ioi (0 : ℝ)) :=
      hcontinuous.isOpen_support.inter isOpen_Ioi
    apply hopen.measure_pos (volume : Measure ℝ)
    refine ⟨1, ?_, by norm_num⟩
    change f0 1 - ft 1 ≠ 0
    have hproduct := strictAntiOn_thetaCuspFullSource_mul_reflect (1 / 2 : ℝ)
      (by norm_num) ht.le ht
    have hweight : 0 < (1 : ℝ) * Real.sinh (a * 1) := by
      simpa using Real.sinh_pos_iff.mpr ha0
    have hmul : ft 1 < f0 1 := by
      dsimp [f0, ft]
      exact mul_lt_mul_of_pos_left (by simpa using hproduct) hweight
    exact (sub_pos.mpr hmul).ne'
  simp only [thetaCuspCenterMixedDensity]
  have htarget : (∫ r : ℝ in Ioi 0, ft r) < ∫ r : ℝ in Ioi 0, f0 r := by
    apply sub_pos.mp
    rw [← integral_sub hf0 hft]
    exact hgap
  simpa [f0, ft] using htarget

/-- The actual three-node Bochner matrix at the ordered nodes `0`, `x`, and `x+y`. -/
def thetaCuspCenterMixedThreePointMatrix (a x y : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  HilbertMetric.threePointCorrelationMatrix
    (thetaCuspCenterMixedDensity a 0)
    (thetaCuspCenterMixedDensity a x)
    (thetaCuspCenterMixedDensity a y)
    (thetaCuspCenterMixedDensity a (x + y))

/-- The exact scalar order-three wall for the ordered Hedenmalm packet. -/
def thetaCuspCenterMixedThreePointDeterminant (a x y : ℝ) : ℝ :=
  HilbertMetric.threePointCorrelationDeterminant
    (thetaCuspCenterMixedDensity a 0)
    (thetaCuspCenterMixedDensity a x)
    (thetaCuspCenterMixedDensity a y)
    (thetaCuspCenterMixedDensity a (x + y))

/-- In the far-separated chamber, where the squared adjacent correlations fit within the squared
center value, the actual three-node Hedenmalm matrix is positive semidefinite unconditionally. -/
theorem thetaCuspCenterMixedThreePointMatrix_posSemidef_of_far_chamber
    {a x y : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfar : thetaCuspCenterMixedDensity a x ^ 2 +
        thetaCuspCenterMixedDensity a y ^ 2 ≤
          thetaCuspCenterMixedDensity a 0 ^ 2) :
    Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y) := by
  let d := thetaCuspCenterMixedDensity a 0
  let p := thetaCuspCenterMixedDensity a x
  let q := thetaCuspCenterMixedDensity a y
  let r := thetaCuspCenterMixedDensity a (x + y)
  have hnonneg : ∀ t, 0 ≤ thetaCuspCenterMixedDensity a t :=
    fun _ => thetaCuspCenterMixedDensity_nonneg ha0.le
  have hanti := antitoneOn_thetaCuspCenterMixedDensity ha0.le ha
  have hxy0 : 0 ≤ x + y := add_nonneg hx hy
  have hxxy : x ≤ x + y := le_add_of_nonneg_right hy
  have hyxy : y ≤ x + y := le_add_of_nonneg_left hx
  have hrp : r ≤ p := by
    dsimp [r, p]
    exact hanti hx hxy0 hxxy
  have hrq : r ≤ q := by
    dsimp [r, q]
    exact hanti hy hxy0 hyxy
  have hfar' : p ^ 2 + q ^ 2 ≤ d ^ 2 := by simpa [d, p, q] using hfar
  have hpsd := HilbertMetric.threePointCorrelationMatrix_posSemidef_of_far_chamber
    (hnonneg 0) (hnonneg x) (hnonneg y) (hnonneg (x + y)) hrp hrq hfar'
  simpa [thetaCuspCenterMixedThreePointMatrix, d, p, q, r] using hpsd

/-- Once the first adjacent correlation is known to be strictly below the center, three-node
positive semidefiniteness is exactly the named scalar determinant wall. -/
theorem thetaCuspCenterMixedThreePointMatrix_posSemidef_iff
    {a x y : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hx : 0 < x) :
    Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y) ↔
      0 ≤ thetaCuspCenterMixedThreePointDeterminant a x y := by
  simpa [thetaCuspCenterMixedThreePointMatrix,
    thetaCuspCenterMixedThreePointDeterminant] using
      HilbertMetric.threePointCorrelationMatrix_posSemidef_iff
        (thetaCuspCenterMixedDensity_pos ha0 ha 0)
        (thetaCuspCenterMixedDensity_nonneg ha0.le)
        (thetaCuspCenterMixedDensity_lt_zero ha0 ha hx)

/-- The exact open near-center scalar wall left after the unconditional far-separated chamber. -/
def ThetaCuspCenterMixedNearCenterThreePointWall : Prop :=
  ∀ a x y : ℝ, 0 < a → a < 1 / 2 → 0 < x → 0 < y →
    thetaCuspCenterMixedDensity a 0 ^ 2 <
      thetaCuspCenterMixedDensity a x ^ 2 + thetaCuspCenterMixedDensity a y ^ 2 →
    0 ≤ thetaCuspCenterMixedThreePointDeterminant a x y

/-- The named near-center wall is exactly what remains to make every ordered positive-gap
three-node theta packet positive semidefinite. -/
theorem thetaCuspCenterMixedThreePointMatrices_posSemidef_iff_nearCenterWall :
    (∀ a x y : ℝ, 0 < a → a < 1 / 2 → 0 < x → 0 < y →
      Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y)) ↔
      ThetaCuspCenterMixedNearCenterThreePointWall := by
  constructor
  · intro hall a x y ha0 ha hx hy _
    exact (thetaCuspCenterMixedThreePointMatrix_posSemidef_iff ha0 ha hx).1
      (hall a x y ha0 ha hx hy)
  · intro hwall a x y ha0 ha hx hy
    by_cases hfar :
        thetaCuspCenterMixedDensity a x ^ 2 +
            thetaCuspCenterMixedDensity a y ^ 2 ≤
          thetaCuspCenterMixedDensity a 0 ^ 2
    · exact thetaCuspCenterMixedThreePointMatrix_posSemidef_of_far_chamber
        ha0 ha hx.le hy.le hfar
    · apply (thetaCuspCenterMixedThreePointMatrix_posSemidef_iff ha0 ha hx).2
      exact hwall a x y ha0 ha hx hy (lt_of_not_ge hfar)

end

end RHTower
