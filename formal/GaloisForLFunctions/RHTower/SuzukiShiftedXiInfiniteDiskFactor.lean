import GaloisForLFunctions.HTGeometry.UpperHalfPlaneNormalizedBlaschkeCayley
import GaloisForLFunctions.RHTower.SuzukiShiftedXiFiniteDiskFactor
import GaloisForLFunctions.RHTower.SuzukiShiftedXiInfiniteTailProduct

/-!
# Infinite shifted-Xi disk factor: finite closed packets

Schwarz-conjugation-closed finite packets identify the literal paired Xi tail quotient with the
phase-normalized disk Blaschke quotient at Hermitian cross-product level.  Working with cross
products makes every finite Cayley phase cancel and avoids imposing convergence on a standalone
infinite phase product.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open scoped Classical

theorem xiShiftRightCopyConjEquiv_involutive
    (omega : ℝ) (q : XiShiftRightZeroCopy omega) :
    xiShiftRightCopyConjEquiv omega
        (xiShiftRightCopyConjEquiv omega q) = q := by
  apply Subtype.ext
  exact xiZeroCopyConjEquiv_apply_apply q.1

/-- Cofinal finite-packet closure under Schwarz conjugation. -/
def xiShiftRightConjClosedFinset (omega : ℝ)
    (s : Finset (XiShiftRightZeroCopy omega)) :
    Finset (XiShiftRightZeroCopy omega) :=
  s ∪ s.image (xiShiftRightCopyConjEquiv omega)

theorem xiShiftRightConjClosedFinset_mono (omega : ℝ) :
    Monotone (xiShiftRightConjClosedFinset omega) := by
  intro s t hst
  exact Finset.union_subset_union hst (Finset.image_mono _ hst)

theorem xiShiftRightConjClosedFinset_tendsto_atTop (omega : ℝ) :
    Tendsto (xiShiftRightConjClosedFinset omega) atTop atTop := by
  apply (xiShiftRightConjClosedFinset_mono omega).tendsto_atTop_finset
  intro q
  refine ⟨{q}, ?_⟩
  simp [xiShiftRightConjClosedFinset]

theorem xiShiftRightConjClosedFinset_image
    (omega : ℝ) (s : Finset (XiShiftRightZeroCopy omega)) :
    (xiShiftRightConjClosedFinset omega s).image
        (xiShiftRightCopyConjEquiv omega) =
      xiShiftRightConjClosedFinset omega s := by
  ext q
  simp only [xiShiftRightConjClosedFinset, Finset.mem_image,
    Finset.mem_union]
  constructor
  · rintro ⟨u, hu | ⟨v, hv, rfl⟩, rfl⟩
    · right
      exact ⟨u, hu, rfl⟩
    · left
      simpa only [xiShiftRightCopyConjEquiv_involutive] using hv
  · rintro (hq | ⟨u, hu, rfl⟩)
    · refine ⟨xiShiftRightCopyConjEquiv omega q, ?_, ?_⟩
      · right
        exact ⟨q, hq, rfl⟩
      · exact xiShiftRightCopyConjEquiv_involutive omega q
    · exact ⟨u, Or.inl hu, rfl⟩

theorem prod_lowerNumerator_finset_eq_conjPole
    (omega : ℝ) (s : Finset (XiShiftRightZeroCopy omega))
    (hclosed : s.image (xiShiftRightCopyConjEquiv omega) = s)
    (z : ℂ) :
    s.prod (fun q => z - (xiSpectralPoint q.1 + (omega : ℂ) * I)) =
      s.prod (fun q => z - (starRingEnd ℂ) (xiShiftPoleCoordinate omega q)) := by
  calc
    s.prod (fun q => z - (xiSpectralPoint q.1 + (omega : ℂ) * I)) =
      s.prod (fun q => z - (starRingEnd ℂ)
        (xiShiftPoleCoordinate omega (xiShiftRightCopyConjEquiv omega q))) := by
          apply Finset.prod_congr rfl
          intro q hq
          rw [conj_xiShiftPoleCoordinate_copyConj]
    _ = (s.image (xiShiftRightCopyConjEquiv omega)).prod
        (fun q => z - (starRingEnd ℂ) (xiShiftPoleCoordinate omega q)) := by
          rw [Finset.prod_image]
          intro q hq r hr hqr
          exact (xiShiftRightCopyConjEquiv omega).injective hqr
    _ = _ := by rw [hclosed]

theorem prod_lowerPole_finset_eq_conjNumerator
    (omega : ℝ) (s : Finset (XiShiftRightZeroCopy omega))
    (hclosed : s.image (xiShiftRightCopyConjEquiv omega) = s)
    (z : ℂ) :
    s.prod (fun q => z - (xiSpectralPoint q.1 - (omega : ℂ) * I)) =
      s.prod (fun q => z - (starRingEnd ℂ)
        (xiShiftNumeratorCoordinate omega q)) := by
  calc
    s.prod (fun q => z - (xiSpectralPoint q.1 - (omega : ℂ) * I)) =
      s.prod (fun q => z - (starRingEnd ℂ)
        (xiShiftNumeratorCoordinate omega (xiShiftRightCopyConjEquiv omega q))) := by
          apply Finset.prod_congr rfl
          intro q hq
          rw [conj_xiShiftNumeratorCoordinate_copyConj]
    _ = (s.image (xiShiftRightCopyConjEquiv omega)).prod
        (fun q => z - (starRingEnd ℂ) (xiShiftNumeratorCoordinate omega q)) := by
          rw [Finset.prod_image]
          intro q hq r hr hqr
          exact (xiShiftRightCopyConjEquiv omega).injective hqr
    _ = _ := by rw [hclosed]

/-- Nonzero algebraic scale of one reflection-paired canonical factor. -/
def xiShiftPairScale (q : XiZeroCopy) : ℂ :=
  -(xiSpectralPoint q ^ 2)⁻¹

theorem xiShiftRightReflectionPairFactor_numerator_shift_scale
    (omega : ℝ) (z : ℂ) (q : XiShiftRightZeroCopy omega) :
    xiShiftRightReflectionPairFactor (z - (omega : ℂ) * I) q.1 =
      xiShiftPairScale q.1 *
        (z - (xiSpectralPoint q.1 + (omega : ℂ) * I)) *
        (z - xiShiftNumeratorCoordinate omega q) := by
  rw [xiShiftRightReflectionPairFactor_numerator_shift,
    xiShiftPairScale]
  field_simp [xiSpectralPoint_ne_zero q.1]

theorem xiShiftRightReflectionPairFactor_denominator_shift_scale
    (omega : ℝ) (z : ℂ) (q : XiShiftRightZeroCopy omega) :
    xiShiftRightReflectionPairFactor (-z - (omega : ℂ) * I) q.1 =
      xiShiftPairScale q.1 *
        (z - xiShiftPoleCoordinate omega q) *
        (z - (xiSpectralPoint q.1 - (omega : ℂ) * I)) := by
  rw [xiShiftRightReflectionPairFactor_denominator_shift,
    xiShiftPairScale]
  field_simp [xiSpectralPoint_ne_zero q.1]

/-- On a conjugation-closed finite packet, the literal paired canonical quotient is exactly the
upper-half-plane numerator Blaschke product divided by the pole Blaschke product. -/
theorem finset_pair_quotient_eq_halfPlane
    {omega : ℝ}
    (s : Finset (XiShiftRightZeroCopy omega))
    (hclosed : s.image (xiShiftRightCopyConjEquiv omega) = s)
    {z : ℂ} (hz : 0 < z.im)
    (hden : ∀ q ∈ s,
      xiShiftRightReflectionPairFactor (-z - (omega : ℂ) * I) q.1 ≠ 0) :
    s.prod (fun q =>
        xiShiftRightReflectionPairFactor (z - (omega : ℂ) * I) q.1 /
          xiShiftRightReflectionPairFactor (-z - (omega : ℂ) * I) q.1) =
      s.prod (fun q =>
        upperHalfPlaneBlaschkeFactor (xiShiftNumeratorCoordinate omega q) z /
          upperHalfPlaneBlaschkeFactor (xiShiftPoleCoordinate omega q) z) := by
  have hscale : s.prod (fun q => xiShiftPairScale q.1) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 (xiSpectralPoint_ne_zero q.1)))
  have hpole : s.prod (fun q => z - xiShiftPoleCoordinate omega q) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hqden := hden q hq
    rw [xiShiftRightReflectionPairFactor_denominator_shift_scale] at hqden
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hqden).1).2
  have hlowerPole :
      s.prod (fun q => z - (xiSpectralPoint q.1 - (omega : ℂ) * I)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hqden := hden q hq
    rw [xiShiftRightReflectionPairFactor_denominator_shift_scale] at hqden
    exact (mul_ne_zero_iff.mp hqden).2
  have hconjNum :
      s.prod (fun q => z - (starRingEnd ℂ)
        (xiShiftNumeratorCoordinate omega q)) ≠ 0 := by
    rw [← prod_lowerPole_finset_eq_conjNumerator omega s hclosed z]
    exact hlowerPole
  have hconjPole :
      s.prod (fun q => z - (starRingEnd ℂ)
        (xiShiftPoleCoordinate omega q)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    apply sub_ne_zero.mpr
    intro heq
    have him := congrArg Complex.im heq
    have hp := xiShiftPoleCoordinate_im_pos omega q
    norm_num at him
    linarith
  have hnumProd :
      s.prod (fun q => xiShiftRightReflectionPairFactor
        (z - (omega : ℂ) * I) q.1) =
        s.prod (fun q => xiShiftPairScale q.1) *
          s.prod (fun q => z - (xiSpectralPoint q.1 + (omega : ℂ) * I)) *
          s.prod (fun q => z - xiShiftNumeratorCoordinate omega q) := by
    simp only [xiShiftRightReflectionPairFactor_numerator_shift_scale]
    repeat' rw [Finset.prod_mul_distrib]
  have hdenProd :
      s.prod (fun q => xiShiftRightReflectionPairFactor
        (-z - (omega : ℂ) * I) q.1) =
        s.prod (fun q => xiShiftPairScale q.1) *
          s.prod (fun q => z - xiShiftPoleCoordinate omega q) *
          s.prod (fun q => z - (xiSpectralPoint q.1 - (omega : ℂ) * I)) := by
    simp only [xiShiftRightReflectionPairFactor_denominator_shift_scale]
    repeat' rw [Finset.prod_mul_distrib]
  rw [Finset.prod_div_distrib, hnumProd, hdenProd]
  simp only [upperHalfPlaneBlaschkeFactor]
  rw [Finset.prod_div_distrib]
  repeat' rw [Finset.prod_div_distrib]
  rw [prod_lowerNumerator_finset_eq_conjPole omega s hclosed z,
    prod_lowerPole_finset_eq_conjNumerator omega s hclosed z]
  field_simp

/-- Finite phase-normalized numerator product on a chosen right-tail packet. -/
def xiShiftFiniteNumeratorNormalizedProductOn
    (omega : ℝ) (s : Finset (XiShiftRightZeroCopy omega)) (u : ℂ) : ℂ :=
  s.prod (fun q =>
    normalizedBlaschkeFactor (xiShiftNumeratorDiskCoordinate omega q) u)

/-- Finite phase-normalized pole product on a chosen right-tail packet. -/
def xiShiftFinitePoleNormalizedProductOn
    (omega : ℝ) (s : Finset (XiShiftRightZeroCopy omega)) (u : ℂ) : ℂ :=
  s.prod (fun q =>
    normalizedBlaschkeFactor (xiShiftPoleDiskCoordinate omega q) u)

def xiShiftFiniteNumeratorNormalizedCayleyUnitOn
    (omega : ℝ) (s : Finset (XiShiftRightZeroCopy omega)) : ℂ :=
  s.prod (fun q =>
    normalizedCayleyBlaschkeUnit (xiShiftNumeratorCoordinate omega q))

def xiShiftFinitePoleNormalizedCayleyUnitOn
    (omega : ℝ) (s : Finset (XiShiftRightZeroCopy omega)) : ℂ :=
  s.prod (fun q =>
    normalizedCayleyBlaschkeUnit (xiShiftPoleCoordinate omega q))

theorem xiShiftFiniteNumeratorNormalizedProductOn_cayley
    {omega : ℝ} (homega : 0 ≤ omega)
    (s : Finset (XiShiftRightZeroCopy omega))
    {z : ℂ} (hz : 0 < z.im) :
    xiShiftFiniteNumeratorNormalizedProductOn omega s
        (upperToDiskCayley z) =
      xiShiftFiniteNumeratorNormalizedCayleyUnitOn omega s *
        s.prod (fun q => upperHalfPlaneBlaschkeFactor
          (xiShiftNumeratorCoordinate omega q) z) := by
  change s.prod (fun q => normalizedBlaschkeFactor
      (upperToDiskCayley (xiShiftNumeratorCoordinate omega q))
      (upperToDiskCayley z)) = _
  simp_rw [normalizedBlaschkeFactor_upperToDiskCayley
    (xiShiftNumeratorCoordinate_im_pos homega _) hz]
  rw [Finset.prod_mul_distrib]
  rfl

theorem xiShiftFinitePoleNormalizedProductOn_cayley
    (omega : ℝ) (s : Finset (XiShiftRightZeroCopy omega))
    {z : ℂ} (hz : 0 < z.im) :
    xiShiftFinitePoleNormalizedProductOn omega s
        (upperToDiskCayley z) =
      xiShiftFinitePoleNormalizedCayleyUnitOn omega s *
        s.prod (fun q => upperHalfPlaneBlaschkeFactor
          (xiShiftPoleCoordinate omega q) z) := by
  change s.prod (fun q => normalizedBlaschkeFactor
      (upperToDiskCayley (xiShiftPoleCoordinate omega q))
      (upperToDiskCayley z)) = _
  simp_rw [normalizedBlaschkeFactor_upperToDiskCayley
    (xiShiftPoleCoordinate_im_pos omega _) hz]
  rw [Finset.prod_mul_distrib]
  rfl

theorem norm_xiShiftFiniteNumeratorNormalizedCayleyUnitOn_eq_one
    {omega : ℝ} (homega : 0 ≤ omega)
    (s : Finset (XiShiftRightZeroCopy omega)) :
    ‖xiShiftFiniteNumeratorNormalizedCayleyUnitOn omega s‖ = 1 := by
  rw [xiShiftFiniteNumeratorNormalizedCayleyUnitOn, norm_prod]
  exact Finset.prod_eq_one fun q hq =>
    norm_normalizedCayleyBlaschkeUnit_eq_one
      (xiShiftNumeratorCoordinate_im_pos homega q)

theorem norm_xiShiftFinitePoleNormalizedCayleyUnitOn_eq_one
    (omega : ℝ) (s : Finset (XiShiftRightZeroCopy omega)) :
    ‖xiShiftFinitePoleNormalizedCayleyUnitOn omega s‖ = 1 := by
  rw [xiShiftFinitePoleNormalizedCayleyUnitOn, norm_prod]
  exact Finset.prod_eq_one fun q hq =>
    norm_normalizedCayleyBlaschkeUnit_eq_one
      (xiShiftPoleCoordinate_im_pos omega q)

/-- Finite closed packets already carry the exact Hermitian cross product of the literal tail
quotient.  Numerator and denominator normalization phases cancel independently. -/
theorem finset_normalized_cross_eq_pair_cross
    {omega : ℝ} (homega : 0 ≤ omega)
    (s : Finset (XiShiftRightZeroCopy omega))
    (hclosed : s.image (xiShiftRightCopyConjEquiv omega) = s)
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (hdenz : ∀ q ∈ s,
      xiShiftRightReflectionPairFactor (-z - (omega : ℂ) * I) q.1 ≠ 0)
    (hdenw : ∀ q ∈ s,
      xiShiftRightReflectionPairFactor (-w - (omega : ℂ) * I) q.1 ≠ 0) :
    (xiShiftFiniteNumeratorNormalizedProductOn omega s
          (upperToDiskCayley z) /
        xiShiftFinitePoleNormalizedProductOn omega s
          (upperToDiskCayley z)) *
        (starRingEnd ℂ)
          (xiShiftFiniteNumeratorNormalizedProductOn omega s
              (upperToDiskCayley w) /
            xiShiftFinitePoleNormalizedProductOn omega s
              (upperToDiskCayley w)) =
      s.prod (fun q =>
          xiShiftRightReflectionPairFactor (z - (omega : ℂ) * I) q.1 /
            xiShiftRightReflectionPairFactor (-z - (omega : ℂ) * I) q.1) *
        (starRingEnd ℂ) (s.prod (fun q =>
          xiShiftRightReflectionPairFactor (w - (omega : ℂ) * I) q.1 /
            xiShiftRightReflectionPairFactor (-w - (omega : ℂ) * I) q.1)) := by
  let un : ℂ := xiShiftFiniteNumeratorNormalizedCayleyUnitOn omega s
  let up : ℂ := xiShiftFinitePoleNormalizedCayleyUnitOn omega s
  let hn : ℂ → ℂ := fun v => s.prod (fun q =>
    upperHalfPlaneBlaschkeFactor (xiShiftNumeratorCoordinate omega q) v)
  let hp : ℂ → ℂ := fun v => s.prod (fun q =>
    upperHalfPlaneBlaschkeFactor (xiShiftPoleCoordinate omega q) v)
  have hun : ‖un‖ = 1 :=
    norm_xiShiftFiniteNumeratorNormalizedCayleyUnitOn_eq_one homega s
  have hup : ‖up‖ = 1 :=
    norm_xiShiftFinitePoleNormalizedCayleyUnitOn_eq_one omega s
  have hup0 : up ≠ 0 := norm_ne_zero_iff.mp (by rw [hup]; norm_num)
  have hphase : (un / up) * (starRingEnd ℂ) (un / up) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_div, hun, hup]
    norm_num
  have hp_ne (v : ℂ) (hv : 0 < v.im)
      (hdenv : ∀ q ∈ s,
        xiShiftRightReflectionPairFactor (-v - (omega : ℂ) * I) q.1 ≠ 0) :
      hp v ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hqden := hdenv q hq
    rw [xiShiftRightReflectionPairFactor_denominator_shift_scale] at hqden
    have hvp : v - xiShiftPoleCoordinate omega q ≠ 0 :=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hqden).1).2
    have hvc : v - (starRingEnd ℂ) (xiShiftPoleCoordinate omega q) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      have him := congrArg Complex.im heq
      have hpi := xiShiftPoleCoordinate_im_pos omega q
      norm_num at him
      linarith
    exact div_ne_zero hvp hvc
  have hpz : hp z ≠ 0 := hp_ne z hz hdenz
  have hpw : hp w ≠ 0 := hp_ne w hw hdenw
  have htransport (v : ℂ) (hv : 0 < v.im) :
      xiShiftFiniteNumeratorNormalizedProductOn omega s
            (upperToDiskCayley v) /
          xiShiftFinitePoleNormalizedProductOn omega s
            (upperToDiskCayley v) =
        (un / up) * (hn v / hp v) := by
    rw [xiShiftFiniteNumeratorNormalizedProductOn_cayley homega s hv,
      xiShiftFinitePoleNormalizedProductOn_cayley omega s hv]
    dsimp only [un, up, hn, hp]
    field_simp
  have hhalfPlaneProd (v : ℂ) :
      s.prod (fun q =>
          upperHalfPlaneBlaschkeFactor (xiShiftNumeratorCoordinate omega q) v /
            upperHalfPlaneBlaschkeFactor (xiShiftPoleCoordinate omega q) v) =
        hn v / hp v := by
    rw [Finset.prod_div_distrib]
  rw [htransport z hz, htransport w hw,
    finset_pair_quotient_eq_halfPlane s hclosed hz hdenz,
    finset_pair_quotient_eq_halfPlane s hclosed hw hdenw,
    hhalfPlaneProd z, hhalfPlaneProd w]
  change ((un / up) * (hn z / hp z)) *
      (starRingEnd ℂ) ((un / up) * (hn w / hp w)) =
    (hn z / hp z) * (starRingEnd ℂ) (hn w / hp w)
  simp only [map_mul]
  calc
    ((un / up) * (hn z / hp z)) *
        ((starRingEnd ℂ) (un / up) *
          (starRingEnd ℂ) (hn w / hp w)) =
      ((un / up) * (starRingEnd ℂ) (un / up)) *
        ((hn z / hp z) * (starRingEnd ℂ) (hn w / hp w)) := by ring
    _ = _ := by rw [hphase, one_mul]

end

end RHTower
