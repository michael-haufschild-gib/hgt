import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayCoordinateEquiv
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayArithmeticPartition
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Global change of variables on one complete primitive theta ray

The existing primitive-ray identities were pointwise.  This file promotes the arithmetic polar
substitution to the exact two-dimensional Lebesgue integral on the positive source quadrant.
The active angular window is retained as part of the polar chamber; no endpoint, finite-core
translation defect, or density factor is estimated separately.
-/

open Complex Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- The inverse arithmetic-polar map `(r,u) ↦ (x,y)` for one positive direction. -/
def thetaCuspPrimitiveRayCartesianMap (a b : ℕ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2,
    thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2)

/-- The direct arithmetic-polar map `(x,y) ↦ (r,u)`. -/
def thetaCuspPrimitiveRayPolarMap (a b : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (thetaCuspPrimitiveRayRadialLog a b p.1 p.2,
    thetaCuspPrimitiveRayAngularWeight a b p.1 p.2)

/-- The positive source quadrant as a measurable subset of `ℝ²`. -/
def thetaCuspPositiveQuadrantSet : Set (ℝ × ℝ) :=
  Ioi 0 ×ˢ Ioi 0

/-- The full moving polar chamber cut out by the two positive-half-line constraints. -/
def thetaCuspPrimitiveRayActiveSet (a b : ℕ) : Set (ℝ × ℝ) :=
  {q | 0 < q.2 ∧ q.2 < 1 ∧
    0 < thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2 ∧
    0 < thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2}

/-- Derivative of the inverse arithmetic-polar map. -/
def thetaCuspPrimitiveRayCartesianFDeriv (q : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![1, 1 / (2 * q.2); 1, -(1 / (2 * (1 - q.2)))]).toContinuousLinearMap

/-- The first source displacement never exceeds the radial coordinate. -/
theorem thetaCuspPrimitiveRayArithmeticPolarX_le_radial
    {a : ℕ} (ha : 0 < a) (r : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    thetaCuspPrimitiveRayArithmeticPolarX a r u ≤ r := by
  have haOne : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hlogA : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg haOne
  have hlogU : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1.le
  unfold thetaCuspPrimitiveRayArithmeticPolarX
  linarith

/-- The second source displacement never exceeds the radial coordinate. -/
theorem thetaCuspPrimitiveRayArithmeticPolarY_le_radial
    {b : ℕ} (hb : 0 < b) (r : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    thetaCuspPrimitiveRayArithmeticPolarY b r u ≤ r := by
  have hbOne : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hlogB : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hbOne
  have hOneSub0 : 0 ≤ 1 - u := (sub_pos.mpr hu1).le
  have hOneSub1 : 1 - u ≤ 1 := by linarith
  have hlogOneSub : Real.log (1 - u) ≤ 0 :=
    Real.log_nonpos hOneSub0 hOneSub1
  unfold thetaCuspPrimitiveRayArithmeticPolarY
  linarith

/-- On the active chamber both finite translation displacements lie in the single interval
`[0,r]`; a radial logarithmic cutoff therefore controls the entire angular fibre at once. -/
theorem thetaCuspPrimitiveRayActiveSet_sourceCoordinates_mem_Icc_radial
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {q : ℝ × ℝ}
    (hq : q ∈ thetaCuspPrimitiveRayActiveSet a b) :
    thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2 ∈ Icc 0 q.1 ∧
      thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2 ∈ Icc 0 q.1 := by
  exact ⟨
    ⟨hq.2.2.1.le,
      thetaCuspPrimitiveRayArithmeticPolarX_le_radial ha q.1 hq.1 hq.2.1⟩,
    ⟨hq.2.2.2.le,
      thetaCuspPrimitiveRayArithmeticPolarY_le_radial hb q.1 hq.1 hq.2.1⟩⟩

theorem hasFDerivAt_thetaCuspPrimitiveRayCartesianMap
    (a b : ℕ) {q : ℝ × ℝ} (hu0 : 0 < q.2) (hu1 : q.2 < 1) :
    HasFDerivAt (thetaCuspPrimitiveRayCartesianMap a b)
      (thetaCuspPrimitiveRayCartesianFDeriv q) q := by
  have hu : q.2 ≠ 0 := hu0.ne'
  have hOneSub : 1 - q.2 ≠ 0 := (sub_pos.mpr hu1).ne'
  have hsnd : HasFDerivAt (fun p : ℝ × ℝ => p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) q := hasFDerivAt_snd
  have hfst : HasFDerivAt (fun p : ℝ × ℝ => p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) q := hasFDerivAt_fst
  have hx : HasFDerivAt
      (fun p : ℝ × ℝ =>
        thetaCuspPrimitiveRayArithmeticPolarX a p.1 p.2)
      (ContinuousLinearMap.fst ℝ ℝ ℝ +
        (1 / (2 * q.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ) q := by
    unfold thetaCuspPrimitiveRayArithmeticPolarX
    have hlog := (Real.hasDerivAt_log hu).comp_hasFDerivAt q hsnd
    have hraw := hfst.add (hlog.const_mul (1 / 2 : ℝ)) |>.sub_const
      (Real.log (a : ℝ))
    have hfun : (fun p : ℝ × ℝ => p.1 + Real.log p.2 / 2 - Real.log (a : ℝ)) =
        fun x : ℝ × ℝ =>
          ((fun p : ℝ × ℝ => p.1) +
            fun y : ℝ × ℝ => 1 / 2 * (Real.log ∘ Prod.snd) y) x -
            Real.log (a : ℝ) := by
      funext p
      simp only [Pi.add_apply, Function.comp_apply]
      ring
    have hclm : (ContinuousLinearMap.fst ℝ ℝ ℝ +
          (1 / (2 * q.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ) =
        ContinuousLinearMap.fst ℝ ℝ ℝ +
          (1 / 2 : ℝ) • q.2⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro p
      simp [smul_smul]
      left
      ring
    rw [hfun, hclm]
    exact hraw
  have hy : HasFDerivAt
      (fun p : ℝ × ℝ =>
        thetaCuspPrimitiveRayArithmeticPolarY b p.1 p.2)
      (ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-(1 / (2 * (1 - q.2)))) • ContinuousLinearMap.snd ℝ ℝ ℝ) q := by
    unfold thetaCuspPrimitiveRayArithmeticPolarY
    have hsub : HasFDerivAt (fun p : ℝ × ℝ => 1 - p.2)
        (-ContinuousLinearMap.snd ℝ ℝ ℝ) q := by
      have h2 : HasFDerivAt (fun p : ℝ × ℝ => 1 - p.2)
          ((0 : (ℝ × ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
        (hasFDerivAt_const (1 : ℝ) q).sub hsnd
      simpa using h2
    have hlog := (Real.hasDerivAt_log hOneSub).comp_hasFDerivAt q hsub
    have hraw := hfst.add (hlog.const_mul (1 / 2 : ℝ)) |>.sub_const
      (Real.log (b : ℝ))
    have hfun : (fun p : ℝ × ℝ =>
          p.1 + Real.log (1 - p.2) / 2 - Real.log (b : ℝ)) =
        fun x : ℝ × ℝ =>
          ((fun p : ℝ × ℝ => p.1) +
            fun y : ℝ × ℝ =>
              1 / 2 * (Real.log ∘ fun p : ℝ × ℝ => 1 - p.2) y) x -
            Real.log (b : ℝ) := by
      funext p
      simp only [Pi.add_apply, Function.comp_apply]
      ring
    have hclm : (ContinuousLinearMap.fst ℝ ℝ ℝ +
          (-(1 / (2 * (1 - q.2)))) • ContinuousLinearMap.snd ℝ ℝ ℝ) =
        ContinuousLinearMap.fst ℝ ℝ ℝ +
          (1 / 2 : ℝ) • (1 - q.2)⁻¹ • -ContinuousLinearMap.snd ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro p
      simp [smul_smul]
      left
      ring
    rw [hfun, hclm]
    exact hraw
  unfold thetaCuspPrimitiveRayCartesianFDeriv
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have hpair : HasFDerivAt
      (fun x : ℝ × ℝ =>
        (thetaCuspPrimitiveRayArithmeticPolarX a x.1 x.2,
          thetaCuspPrimitiveRayArithmeticPolarY b x.1 x.2))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ +
          (1 / (2 * q.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (ContinuousLinearMap.fst ℝ ℝ ℝ +
          (-(1 / (2 * (1 - q.2)))) • ContinuousLinearMap.snd ℝ ℝ ℝ)) q :=
    hx.prodMk hy
  have hfun : thetaCuspPrimitiveRayCartesianMap a b = fun x : ℝ × ℝ =>
      (thetaCuspPrimitiveRayArithmeticPolarX a x.1 x.2,
        thetaCuspPrimitiveRayArithmeticPolarY b x.1 x.2) := rfl
  rw [hfun]
  simpa only [one_smul] using hpair

theorem det_thetaCuspPrimitiveRayCartesianFDeriv
    {q : ℝ × ℝ} (hu0 : 0 < q.2) (hu1 : q.2 < 1) :
    (thetaCuspPrimitiveRayCartesianFDeriv q).det =
      thetaCuspPrimitiveRayArithmeticPolarSignedJacobian q.2 := by
  unfold thetaCuspPrimitiveRayCartesianFDeriv
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  exact thetaCuspPrimitiveRayArithmeticPolarSignedJacobian_eq hu0 hu1

theorem measurableSet_thetaCuspPrimitiveRayActiveSet (a b : ℕ) :
    MeasurableSet (thetaCuspPrimitiveRayActiveSet a b) := by
  unfold thetaCuspPrimitiveRayActiveSet
  have hX : Measurable (fun q : ℝ × ℝ =>
      thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2) := by
    unfold thetaCuspPrimitiveRayArithmeticPolarX
    fun_prop
  have hY : Measurable (fun q : ℝ × ℝ =>
      thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2) := by
    unfold thetaCuspPrimitiveRayArithmeticPolarY
    fun_prop
  exact (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_lt measurable_snd measurable_const).inter
      ((measurableSet_lt measurable_const hX).inter
        (measurableSet_lt measurable_const hY)))

theorem thetaCuspPrimitiveRayCartesianMap_injectiveOn
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Set.InjOn (thetaCuspPrimitiveRayCartesianMap a b)
      (thetaCuspPrimitiveRayActiveSet a b) := by
  intro q hq q' hq' hEq
  have hleft : thetaCuspPrimitiveRayPolarMap a b
      (thetaCuspPrimitiveRayCartesianMap a b q) = q := by
    apply Prod.ext
    · exact thetaCuspPrimitiveRayRadialLog_arithmeticPolar ha hb q.1 hq.1 hq.2.1
    · exact thetaCuspPrimitiveRayAngularWeight_arithmeticPolar ha hb q.1 hq.1 hq.2.1
  have hright : thetaCuspPrimitiveRayPolarMap a b
      (thetaCuspPrimitiveRayCartesianMap a b q') = q' := by
    apply Prod.ext
    · exact thetaCuspPrimitiveRayRadialLog_arithmeticPolar ha hb q'.1 hq'.1 hq'.2.1
    · exact thetaCuspPrimitiveRayAngularWeight_arithmeticPolar ha hb q'.1 hq'.1 hq'.2.1
  rw [hEq] at hleft
  exact hleft.symm.trans hright

theorem thetaCuspPrimitiveRayCartesianMap_image_activeSet
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    thetaCuspPrimitiveRayCartesianMap a b ''
        thetaCuspPrimitiveRayActiveSet a b =
      thetaCuspPositiveQuadrantSet := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq.2.2
  · intro hp
    have hp' : 0 < p.1 ∧ 0 < p.2 := hp
    let q := thetaCuspPrimitiveRayPolarMap a b p
    have hu0 : 0 < q.2 :=
      thetaCuspPrimitiveRayAngularWeight_pos ha hb p.1 p.2
    have hu1 : q.2 < 1 :=
      thetaCuspPrimitiveRayAngularWeight_lt_one ha hb p.1 p.2
    have hx : thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2 = p.1 :=
      thetaCuspPrimitiveRayArithmeticPolarX_radialLog_angularWeight ha hb p.1 p.2
    have hy : thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2 = p.2 :=
      thetaCuspPrimitiveRayArithmeticPolarY_radialLog_angularWeight ha hb p.1 p.2
    refine ⟨q, ⟨hu0, hu1, ?_, ?_⟩, ?_⟩
    · simpa [hx] using hp'.1
    · simpa [hy] using hp'.2
    · apply Prod.ext <;> simp [thetaCuspPrimitiveRayCartesianMap, hx, hy]

/-- **Measure-level primitive-ray bridge.**  The exact arithmetic-polar Jacobian transports an
arbitrary real integrand from the positive source quadrant to the full active chamber. -/
theorem integral_thetaCuspPositiveQuadrant_eq_primitiveRayActiveSet
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (f : ℝ × ℝ → ℝ) :
    (∫ p in thetaCuspPositiveQuadrantSet, f p) =
      ∫ q in thetaCuspPrimitiveRayActiveSet a b,
        thetaCuspPrimitiveRayArithmeticPolarJacobian q.2 *
          f (thetaCuspPrimitiveRayCartesianMap a b q) := by
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    (μ := volume)
    (measurableSet_thetaCuspPrimitiveRayActiveSet a b)
    (fun q hq =>
      (hasFDerivAt_thetaCuspPrimitiveRayCartesianMap a b hq.1 hq.2.1).hasFDerivWithinAt)
    (thetaCuspPrimitiveRayCartesianMap_injectiveOn ha hb) f
  rw [thetaCuspPrimitiveRayCartesianMap_image_activeSet ha hb] at hchange
  rw [hchange]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_thetaCuspPrimitiveRayActiveSet a b)] with q hq
  rw [det_thetaCuspPrimitiveRayCartesianFDeriv hq.1 hq.2.1,
    abs_thetaCuspPrimitiveRayArithmeticPolarSignedJacobian hq.1 hq.2.1]
  rfl

/-- **Exact integrated complete-ray disintegration.**  The full common-scale packet of one
coprime direction, coupled jointly to the finite theta-tail core current, is exactly the radial
packet times the canonical singular angular seam weight on the moving active chamber. -/
theorem integral_thetaCuspPrimitiveRayDensityPair_mul_coreCurrent_eq_polar
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (d : ℕ) (z : ℂ) :
    (∫ p in thetaCuspPositiveQuadrantSet,
      (∑' g : ℕ,
        thetaCuspTailSecondDensityAtom (a * (g + 1)) p.1 *
          thetaCuspTailSecondDensityAtom (b * (g + 1)) p.2) *
        xiCTaylorThetaTailCorePairCurrent d z p) =
      ∫ q in thetaCuspPrimitiveRayActiveSet a b,
        (8 * Real.exp
            (q.1 / 2 - (Real.log (a : ℝ) + Real.log (b : ℝ)) / 2) *
          (thetaCuspPrimitiveRayMoment q.2) ^ (-(3 / 4 : ℝ)) *
          thetaCuspPrimitiveRayRadialPacket q.2 q.1) *
        thetaCuspPrimitiveRayCorePolarKernel d z q.1
          (-Real.log (a : ℝ)) (-Real.log (b : ℝ)) q.2 := by
  rw [integral_thetaCuspPositiveQuadrant_eq_primitiveRayActiveSet ha hb]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_thetaCuspPrimitiveRayActiveSet a b)] with q hq
  have hweight :=
    tsum_thetaCuspTailSecondDensityAtom_arithmeticPolar_mul_jacobian_eq_seamWeight
      ha hb q.1 hq.1 hq.2.1
  unfold thetaCuspPrimitiveRayCartesianMap
  rw [show thetaCuspPrimitiveRayArithmeticPolarJacobian q.2 *
        ((∑' g : ℕ,
          thetaCuspTailSecondDensityAtom (a * (g + 1))
              (thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2) *
            thetaCuspTailSecondDensityAtom (b * (g + 1))
              (thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2)) *
          xiCTaylorThetaTailCorePairCurrent d z
            (thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2,
              thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2)) =
      ((∑' g : ℕ,
          thetaCuspTailSecondDensityAtom (a * (g + 1))
              (thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2) *
            thetaCuspTailSecondDensityAtom (b * (g + 1))
              (thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2)) *
        thetaCuspPrimitiveRayArithmeticPolarJacobian q.2) *
          xiCTaylorThetaTailCorePairCurrent d z
            (thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2,
              thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2) by ring,
    hweight]
  rw [thetaCuspPrimitiveRayArithmeticPolarX_eq_corePolarX,
    thetaCuspPrimitiveRayArithmeticPolarY_eq_corePolarY]
  unfold thetaCuspPrimitiveRayCorePolarKernel
  ring

/-- Product-restricted-measure form used by the theta-tail core correlation files. -/
theorem integral_thetaCuspPrimitiveRayDensityPair_mul_coreCurrent_prodMeasure_eq_polar
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (d : ℕ) (z : ℂ) :
    (∫ p : ℝ × ℝ,
      (∑' g : ℕ,
        thetaCuspTailSecondDensityAtom (a * (g + 1)) p.1 *
          thetaCuspTailSecondDensityAtom (b * (g + 1)) p.2) *
        xiCTaylorThetaTailCorePairCurrent d z p
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      ∫ q in thetaCuspPrimitiveRayActiveSet a b,
        (8 * Real.exp
            (q.1 / 2 - (Real.log (a : ℝ) + Real.log (b : ℝ)) / 2) *
          (thetaCuspPrimitiveRayMoment q.2) ^ (-(3 / 4 : ℝ)) *
          thetaCuspPrimitiveRayRadialPacket q.2 q.1) *
        thetaCuspPrimitiveRayCorePolarKernel d z q.1
          (-Real.log (a : ℝ)) (-Real.log (b : ℝ)) q.2 := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact integral_thetaCuspPrimitiveRayDensityPair_mul_coreCurrent_eq_polar ha hb d z

end

end RHTower
