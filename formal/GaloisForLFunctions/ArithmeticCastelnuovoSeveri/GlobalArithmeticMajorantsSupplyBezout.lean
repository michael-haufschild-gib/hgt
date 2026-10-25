import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticMajorantsSupplyBezout
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ExponentialSourceMassControlsTheFullPrimeSum
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PositiveQuadraticSourceCones

/-!
# A global arithmetic majorant on the original scaling surface

Exponential source mass pays the entire prime sum. The archimedean lower bound and
the two pole moments then give one positive quadratic reserve on every compact
source. Its source cone has Bézout and ampleness on the original pairing, while
the strictly positive extra mass prevents Riemann–Roch.
-/

noncomputable section
open MeasureTheory Filter RHTower RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private theorem weighted_source_pair_integrable (w : ℝ → ℝ) (hw : Continuous w)
    (x y : ScalingCycle) :
    Integrable (fun t : ℝ => (w t * x.2.2.1 t) * (w t * y.2.2.1 t)) :=
  ((hw.mul x.2.2.2.1.continuous).mul (hw.mul y.2.2.2.1.continuous)).integrable_of_hasCompactSupport
    x.2.2.2.2.mul_left.mul_right

/-- Weighted source mass as a symmetric bilinear form on the full scaling surface. -/
def weightedSourceBilinear (w : ℝ → ℝ) (hw : Continuous w) :
    ScalingCycle →ₗ[ℝ] ScalingCycle →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∫ t : ℝ, (w t * x.2.2.1 t) * (w t * y.2.2.1 t))
    (fun x y z => by
      change (∫ t : ℝ, (w t * (x.2.2.1 t + y.2.2.1 t)) * (w t * z.2.2.1 t)) = _
      simp_rw [mul_add, add_mul]
      exact integral_add (weighted_source_pair_integrable w hw x z)
        (weighted_source_pair_integrable w hw y z))
    (fun a x y => by
      change (∫ t : ℝ, (w t * (a * x.2.2.1 t)) * (w t * y.2.2.1 t)) =
        a * ∫ t : ℝ, (w t * x.2.2.1 t) * (w t * y.2.2.1 t)
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun t => by ring))
    (fun x y z => by
      change (∫ t : ℝ, (w t * x.2.2.1 t) * (w t * (y.2.2.1 t + z.2.2.1 t))) = _
      simp_rw [mul_add]
      exact integral_add (weighted_source_pair_integrable w hw x y)
        (weighted_source_pair_integrable w hw x z))
    (fun a x y => by
      change (∫ t : ℝ, (w t * x.2.2.1 t) * (w t * (a * y.2.2.1 t))) =
        a * ∫ t : ℝ, (w t * x.2.2.1 t) * (w t * y.2.2.1 t)
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun t => by ring))

theorem weightedSourceBilinear_symm (w : ℝ → ℝ) (hw : Continuous w) (x y : ScalingCycle) :
    weightedSourceBilinear w hw x y = weightedSourceBilinear w hw y x :=
  integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)

theorem weightedSourceBilinear_self (w : ℝ → ℝ) (hw : Continuous w) (x : ScalingCycle) :
    weightedSourceBilinear w hw x x = ∫ t : ℝ, (w t * x.2.2.1 t) ^ 2 :=
  integral_congr_ae (Eventually.of_forall fun _ => (sq _).symm)

/-- The odd pole moment is a linear reading of the actual compact source. -/
def oddSourceMoment : ScalingCycle →ₗ[ℝ] ℝ where
  toFun x := oddPoleMoment x.2.2
  map_add' x y := oddPoleMoment_add x.2.2.2.1.continuous x.2.2.2.2
    y.2.2.2.1.continuous y.2.2.2.2
  map_smul' a x := by
    change (∫ t : ℝ, (a * x.2.2.1 t) * Real.sinh (t / 2)) =
      a * ∫ t : ℝ, x.2.2.1 t * Real.sinh (t / 2)
    simp only [mul_assoc, integral_const_mul]

private def oddMomentBilinear : ScalingCycle →ₗ[ℝ] ScalingCycle →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => oddSourceMoment x * oddSourceMoment y)
    (fun x y z => by rw [map_add, add_mul])
    (fun a x y => by rw [map_smul, smul_eq_mul, smul_eq_mul]; ring)
    (fun x y z => by rw [map_add, mul_add])
    (fun a x y => by rw [map_smul, smul_eq_mul, smul_eq_mul]; ring)

/-- One global reserve paying the prime, archimedean, and odd pole lower bounds. -/
def globalArithmeticReserve (x : ScalingCycle) : ℝ :=
  (2 * |gammaHardyPhaseRate 0| + 1) * (∫ t : ℝ, x.2.2.1 t ^ 2) +
    2 * vonMangoldtThreeHalvesMass * exponentialSourceMass x.2.2 + 2 * oddPoleMoment x.2.2 ^ 2

/-- This arithmetic threshold uses only source integrals and the actual prime sum. -/
def globalArithmeticMajorant (x : ScalingCycle) : ℝ :=
  archForm x.2.2 - primeSum x.2.2 + 2 * oddPoleMoment x.2.2 ^ 2 +
    2 * evenPoleMoment x.2.2 ^ 2 +
    2 * (2 * |gammaHardyPhaseRate 0| + 1) * (∫ t : ℝ, x.2.2.1 t ^ 2) +
    4 * vonMangoldtThreeHalvesMass * exponentialSourceMass x.2.2

/-- The globally compatible arithmetic effective cone on the original compact scaling surface. -/
def globalArithmeticMajorantCone : Set ScalingCycle :=
  scalingSurface.sourceCone globalArithmeticMajorant

private theorem global_defect_source (x : ScalingCycle) :
    scalingSurface.defect x x = archForm x.2.2 - primeSum x.2.2 -
      2 * oddPoleMoment x.2.2 ^ 2 + 2 * evenPoleMoment x.2.2 ^ 2 := by
  rw [scalingSurface_defect_self, weilPair_self_eq_fullZeroForm x.2.2.2.1 x.2.2.2.2,
    fullZeroForm, markovEnergy_ofReal_eq_archForm_sub_primeSum x.2.2.2.1 x.2.2.2.2]

/-- The majorant adds exactly twice the independently positive reserve to the defect. -/
theorem globalArithmeticMajorant_eq_defect_add_two_reserve (x : ScalingCycle) :
    globalArithmeticMajorant x = scalingSurface.defect x x + 2 * globalArithmeticReserve x := by
  rw [global_defect_source]
  unfold globalArithmeticMajorant globalArithmeticReserve
  ring

theorem globalArithmeticReserve_mass_floor (x : ScalingCycle) :
    (∫ t : ℝ, x.2.2.1 t ^ 2) ≤ globalArithmeticReserve x := by
  have hm : 0 ≤ ∫ t : ℝ, x.2.2.1 t ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have ha := mul_nonneg (abs_nonneg (gammaHardyPhaseRate 0)) hm
  have hw := mul_nonneg vonMangoldtThreeHalvesMass_nonneg (exponentialSourceMass_nonneg x.2.2)
  unfold globalArithmeticReserve
  nlinarith only [ha, hw, sq_nonneg (oddPoleMoment x.2.2)]

/-- The global reserve pays the negative defect while retaining a positive source mass. -/
theorem globalArithmeticReserve_defect_floor (x : ScalingCycle) :
    (∫ t : ℝ, x.2.2.1 t ^ 2) + 2 * evenPoleMoment x.2.2 ^ 2 ≤
      scalingSurface.defect x x + globalArithmeticReserve x := by
  have ha := archForm_ge x.2.2.2.1 x.2.2.2.2
  have hp := primeSum_le_two_threeHalvesMass_mul_exponentialSourceMass
    x.2.2.2.1.continuous x.2.2.2.2
  have hm : 0 ≤ ∫ t : ℝ, x.2.2.1 t ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hg := mul_le_mul_of_nonneg_right (neg_le_abs (gammaHardyPhaseRate 0)) hm
  rw [global_defect_source]
  unfold globalArithmeticReserve
  linarith only [ha, hp, hg]

theorem globalArithmeticMajorant_mass_floor (x : ScalingCycle) :
    2 * (∫ t : ℝ, x.2.2.1 t ^ 2) ≤ globalArithmeticMajorant x := by
  rw [globalArithmeticMajorant_eq_defect_add_two_reserve]
  linarith only [globalArithmeticReserve_mass_floor x,
    globalArithmeticReserve_defect_floor x, sq_nonneg (evenPoleMoment x.2.2)]

theorem globalArithmeticMajorant_nonneg (x : ScalingCycle) : 0 ≤ globalArithmeticMajorant x :=
  (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)).trans
    (globalArithmeticMajorant_mass_floor x)

private def globalReserveBilinear : ScalingCycle →ₗ[ℝ] ScalingCycle →ₗ[ℝ] ℝ :=
  (2 * |gammaHardyPhaseRate 0| + 1) • weightedSourceBilinear (fun _ => 1) continuous_const +
    (2 * vonMangoldtThreeHalvesMass) • weightedSourceBilinear
      (fun t => Real.exp |t|) (Real.continuous_exp.comp continuous_abs) +
    (2 : ℝ) • oddMomentBilinear

private theorem globalReserveBilinear_self (x : ScalingCycle) :
    globalReserveBilinear x x = globalArithmeticReserve x := by
  change (2 * |gammaHardyPhaseRate 0| + 1) * weightedSourceBilinear _ _ x x +
    (2 * vonMangoldtThreeHalvesMass) * weightedSourceBilinear _ _ x x +
    2 * (oddSourceMoment x * oddSourceMoment x) = _
  rw [weightedSourceBilinear_self, weightedSourceBilinear_self]
  simp only [one_mul, globalArithmeticReserve, exponentialSourceMass, oddSourceMoment, pow_two]
  rfl

private theorem globalReserveBilinear_symm (x y : ScalingCycle) :
    globalReserveBilinear x y = globalReserveBilinear y x := by
  change (2 * |gammaHardyPhaseRate 0| + 1) * weightedSourceBilinear _ _ x y +
    (2 * vonMangoldtThreeHalvesMass) * weightedSourceBilinear _ _ x y +
    2 * (oddSourceMoment x * oddSourceMoment y) = _
  rw [weightedSourceBilinear_symm _ _ x y, weightedSourceBilinear_symm _ _ x y,
    mul_comm (oddSourceMoment x) (oddSourceMoment y)]
  rfl

private def globalMajorantBilinear : ScalingCycle →ₗ[ℝ] ScalingCycle →ₗ[ℝ] ℝ :=
  scalingSurface.defectLinearMap + (2 : ℝ) • globalReserveBilinear

private theorem globalMajorantBilinear_self (x : ScalingCycle) :
    globalMajorantBilinear x x = globalArithmeticMajorant x := by
  change scalingSurface.defect x x + 2 * globalReserveBilinear x x = _
  rw [globalReserveBilinear_self, globalArithmeticMajorant_eq_defect_add_two_reserve]

private theorem globalMajorantBilinear_symm (x y : ScalingCycle) :
    globalMajorantBilinear x y = globalMajorantBilinear y x := by
  change scalingSurface.defect x y + 2 * globalReserveBilinear x y =
    scalingSurface.defect y x + 2 * globalReserveBilinear y x
  rw [scalingSurface.defect_comm, globalReserveBilinear_symm]

private theorem globalMajorant_fibre (x : ScalingCycle) (a b : ℝ) :
    globalArithmeticMajorant (x + a • scalingSurface.H + b • scalingSurface.V) =
      globalArithmeticMajorant x := by
  have hs : (x + a • scalingSurface.H + b • scalingSurface.V).2.2 = x.2.2 := by
    change x.2.2 + a • (0 : realTests) + b • 0 = x.2.2
    simp only [smul_zero, add_zero]
  simp only [globalArithmeticMajorant, hs]

private theorem globalMajorant_even (x : ScalingCycle) :
    globalArithmeticMajorant (-x) = globalArithmeticMajorant x := by
  rw [← globalMajorantBilinear_self, ← globalMajorantBilinear_self]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

/-- One source-only majorant controls all mixed defects, with no shared aperture requirement. -/
theorem defect_sq_le_globalArithmeticMajorant (x y : ScalingCycle) :
    scalingSurface.defect x y ^ 2 ≤ globalArithmeticMajorant x * globalArithmeticMajorant y := by
  rw [← globalMajorantBilinear_self, ← globalMajorantBilinear_self]
  apply scalingSurface.defect_sq_le_of_quadratic_majorant globalMajorantBilinear
    globalMajorantBilinear_symm
  · intro z
    rw [globalMajorantBilinear_self, globalArithmeticMajorant_eq_defect_add_two_reserve]
    have hm : 0 ≤ ∫ t : ℝ, z.2.2.1 t ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith only [globalArithmeticReserve_mass_floor z, hm]
  · intro z
    rw [globalMajorantBilinear_self, globalArithmeticMajorant_eq_defect_add_two_reserve]
    have hm : 0 ≤ ∫ t : ℝ, z.2.2.1 t ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith only [globalArithmeticReserve_defect_floor z, hm, sq_nonneg (evenPoleMoment z.2.2)]

/-- Global arithmetic Bézout holds on the original intersection pairing. -/
theorem globalArithmeticMajorantCone_bezout : scalingSurface.BezoutAxiom globalArithmeticMajorantCone :=
  (scalingSurface.sourceCone_bezout_iff_defect_sq_le globalArithmeticMajorant_nonneg
    globalMajorant_even globalMajorant_fibre).mpr defect_sq_le_globalArithmeticMajorant

/-- Global majorant effectivity has the ample axiom on the original pairing. -/
theorem globalArithmeticMajorantCone_ample : scalingSurface.AmpleAxiom globalArithmeticMajorantCone := by
  apply (scalingSurface.sourceCone_ample_iff_defect_radical globalMajorant_fibre).mpr
  intro x hx y
  have hz := le_antisymm hx (globalArithmeticMajorant_nonneg x)
  have hb := defect_sq_le_globalArithmeticMajorant x y
  rw [hz, zero_mul] at hb
  nlinarith only [hb, sq_nonneg (scalingSurface.defect x y)]

/-- An effective class of ample degree zero is zero as an actual compact cycle. -/
theorem globalArithmeticMajorantCone_ample_zero (x : ScalingCycle)
    (hx : x ∈ globalArithmeticMajorantCone) (hA : scalingSurface.pair x scalingSurface.ample = 0) :
    x = 0 := by
  change x ∈ scalingSurface.sourceCone globalArithmeticMajorant at hx
  rw [scalingSurface.mem_sourceCone_iff] at hx
  rw [scalingSurface.pair_ample] at hA
  have hH : scalingSurface.pair x scalingSurface.H = 0 := by linarith only [hx.1, hx.2.1, hA]
  have hV : scalingSurface.pair x scalingSurface.V = 0 := by linarith only [hx.1, hx.2.1, hA]
  rw [scalingSurface.polar_self, hH, hV, mul_zero] at hx
  have hm := globalArithmeticMajorant_mass_floor x
  have hm0 : (∫ t : ℝ, x.2.2.1 t ^ 2) = 0 := by
    have hn : 0 ≤ ∫ t : ℝ, x.2.2.1 t ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith only [hm, hx.2.2, hn]
  have hf : x.2.2 = 0 := Subtype.ext
    (eq_zero_of_integral_sq_eq_zero_of_mem_realTests x.2.2.2 hm0)
  have hcoords : x = (x.1, x.2.1, 0) := by rw [← hf]
  rw [hcoords] at hH hV ⊢
  change scalingPairFun (x.1, x.2.1, 0) (1, 0, 0) = 0 at hH
  change scalingPairFun (x.1, x.2.1, 0) (0, 1, 0) = 0 at hV
  have hz : ((0 : realTests) : ℝ → ℝ) = 0 := rfl
  simp only [scalingPairFun, hz, poleA_zero, poleB_zero, localPair_zero_left,
    mul_zero, mul_one, add_zero, zero_add] at hH hV
  change (x.1, x.2.1, (0 : realTests)) = (0, 0, 0)
  rw [hH, hV]

/-- The positive added reserve prevents Riemann–Roch on this globally compatible cone. -/
theorem globalArithmeticMajorantCone_not_riemannRoch :
    ¬ scalingSurface.RiemannRochAxiom globalArithmeticMajorantCone := by
  intro hRR
  have hle := (scalingSurface.sourceCone_riemannRoch_iff_le_defect_without_symmetry
    globalArithmeticMajorant_nonneg globalMajorant_fibre).mp hRR
  obtain ⟨f, hm, -, -⟩ := exists_realTestAt_in_ker_weilPair_gt_mul_integral_sq
    (by norm_num : (0 : ℝ) < 1) 0 (0 : realTestsAt 1 →ₗ[ℝ] ℝ)
  have h := hle (0, 0, f.1)
  rw [globalArithmeticMajorant_eq_defect_add_two_reserve] at h
  have hr := globalArithmeticReserve_mass_floor (0, 0, f.1)
  linarith only [h, hr, hm]

theorem globalArithmeticMajorantCone_add_closed :
    ∀ x ∈ globalArithmeticMajorantCone, ∀ y ∈ globalArithmeticMajorantCone,
      x + y ∈ globalArithmeticMajorantCone := by
  have he : globalArithmeticMajorant = fun x => globalMajorantBilinear x x :=
    funext fun x => (globalMajorantBilinear_self x).symm
  rw [globalArithmeticMajorantCone, he]
  exact scalingSurface.sourceCone_quadratic_add_closed globalMajorantBilinear
    globalMajorantBilinear_symm (fun x => by rw [globalMajorantBilinear_self]; exact globalArithmeticMajorant_nonneg x)

theorem globalArithmeticMajorantCone_smul {a : ℝ} (ha : 0 ≤ a) {x : ScalingCycle}
    (hx : x ∈ globalArithmeticMajorantCone) : a • x ∈ globalArithmeticMajorantCone := by
  have he : globalArithmeticMajorant = fun x => globalMajorantBilinear x x :=
    funext fun x => (globalMajorantBilinear_self x).symm
  rw [globalArithmeticMajorantCone, he] at hx ⊢
  exact scalingSurface.smul_mem_sourceCone_quadratic globalMajorantBilinear ha hx

theorem zero_mem_globalArithmeticMajorantCone : (0 : ScalingCycle) ∈ globalArithmeticMajorantCone := by
  have he : globalArithmeticMajorant = fun x => globalMajorantBilinear x x :=
    funext fun x => (globalMajorantBilinear_self x).symm
  rw [globalArithmeticMajorantCone, he]
  exact scalingSurface.zero_mem_sourceCone_quadratic globalMajorantBilinear

/-- The global source reserve defines a convex cone on the original cycle space. -/
theorem globalArithmeticMajorantCone_convex : Convex ℝ globalArithmeticMajorantCone := by
  have he : globalArithmeticMajorant = fun x => globalMajorantBilinear x x :=
    funext fun x => (globalMajorantBilinear_self x).symm
  rw [globalArithmeticMajorantCone, he]
  exact scalingSurface.sourceCone_quadratic_convex globalMajorantBilinear
    globalMajorantBilinear_symm (fun x => by rw [globalMajorantBilinear_self]; exact globalArithmeticMajorant_nonneg x)

/-- Every compact cycle is a difference of two globally arithmetic effective cycles. -/
theorem globalArithmeticMajorantCone_generating (x : ScalingCycle) :
    ∃ y ∈ globalArithmeticMajorantCone, ∃ z ∈ globalArithmeticMajorantCone, x = y - z := by
  apply scalingSurface.sourceCone_generating globalMajorant_fibre _ x
  rw [← globalMajorantBilinear_self]
  simp only [map_zero, le_refl]

/-- The global arithmetic cone has no nonzero class together with its negative. -/
theorem globalArithmeticMajorantCone_pointed {x : ScalingCycle}
    (hx : x ∈ globalArithmeticMajorantCone) (hnx : -x ∈ globalArithmeticMajorantCone) : x = 0 := by
  apply globalArithmeticMajorantCone_ample_zero x hx
  change x ∈ scalingSurface.sourceCone globalArithmeticMajorant at hx
  change -x ∈ scalingSurface.sourceCone globalArithmeticMajorant at hnx
  rw [scalingSurface.mem_sourceCone_iff] at hx hnx
  simp only [map_neg, LinearMap.neg_apply] at hnx
  rw [scalingSurface.pair_ample]
  linarith only [hx.1, hx.2.1, hnx.1, hnx.2.1]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
