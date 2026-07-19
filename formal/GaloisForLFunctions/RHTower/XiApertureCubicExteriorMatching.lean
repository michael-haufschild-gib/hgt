import GaloisForLFunctions.RHTower.XiAperturePoissonResponseSignature
import GaloisForLFunctions.RHTower.XiMobiusDyadicCubicReflectionApertureNoGo

/-!
# Cubic determinant-line matching for the true aperture and Poisson response

The all-prime cubic germ of the true Möbius aperture is one positive source constant times the
diagonally dressed Cauchy kernel `x²y²/(x+y)`.  Its three-node determinant and the determinant of
the correctly oriented fine-minus-coarse Poisson response have the same Vandermonde collision
divisor.  After cancelling that divisor, this module constructs the resulting explicit positive
exterior gain and proves the exact matching identity, including colliding node packets.

This is a finite determinant-line theorem.  It does not construct the conjectural infinite
Gamma-conormal signature converter.
-/

namespace RHTower

noncomputable section

/-- The positive all-prime mass multiplying the cubic true-aperture Cauchy kernel. -/
def xiMobiusContinuousApertureCubicMass : ℝ :=
  (∑' p : Nat.Primes, xiMobiusPrimeContinuousApertureCubicSlopeTerm p) / 16

theorem xiMobiusContinuousApertureCubicMass_pos :
    0 < xiMobiusContinuousApertureCubicMass := by
  have hsum : 0 < ∑' p : Nat.Primes,
      xiMobiusPrimeContinuousApertureCubicSlopeTerm p :=
    summable_xiMobiusPrimeContinuousApertureCubicSlopeTerm.tsum_pos
      (fun p => (xiMobiusPrimeContinuousApertureCubicSlopeTerm_pos p).le)
      ⟨2, Nat.prime_two⟩
      (xiMobiusPrimeContinuousApertureCubicSlopeTerm_pos ⟨2, Nat.prime_two⟩)
  exact div_pos hsum (by norm_num)

/-- The completed cubic aperture source has one global positive normalization. -/
theorem xiMobiusContinuousApertureCubicKernel_eq_mass_mul
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    xiMobiusContinuousApertureCubicKernel x y =
      xiMobiusContinuousApertureCubicMass * (x ^ 2 * y ^ 2 / (x + y)) := by
  have hxy : x + y ≠ 0 := (add_pos hx hy).ne'
  rw [xiMobiusContinuousApertureCubicKernel,
    xiMobiusContinuousApertureCubicMass]
  calc
    (∑' p : Nat.Primes, xiMobiusPrimeContinuousApertureCubicCoefficient x y p) =
        ∑' p : Nat.Primes,
          (x ^ 2 * y ^ 2 / (16 * (x + y))) *
            xiMobiusPrimeContinuousApertureCubicSlopeTerm p := by
      apply tsum_congr
      intro p
      exact xiMobiusPrimeContinuousApertureCubicCoefficient_eq_slope hx hy p
    _ = (x ^ 2 * y ^ 2 / (16 * (x + y))) *
        ∑' p : Nat.Primes, xiMobiusPrimeContinuousApertureCubicSlopeTerm p := by
      rw [tsum_mul_left]
    _ = ((∑' p : Nat.Primes, xiMobiusPrimeContinuousApertureCubicSlopeTerm p) / 16) *
        (x ^ 2 * y ^ 2 / (x + y)) := by
      field_simp [hxy]

/-- Abstract normalized cubic aperture kernel. -/
def cubicApertureSourceKernel (kappa x y : ℝ) : ℝ :=
  kappa * (x ^ 2 * y ^ 2 / (x + y))

/-- Exact three-node determinant of the cubic aperture kernel. -/
theorem symmetricThreePointDet_cubicApertureSourceKernel
    {kappa x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    symmetricThreePointDet (cubicApertureSourceKernel kappa) x y z =
      kappa ^ 3 * x ^ 3 * y ^ 3 * z ^ 3 *
          (x - y) ^ 2 * (x - z) ^ 2 * (y - z) ^ 2 /
        (8 * (x + y) ^ 2 * (x + z) ^ 2 * (y + z) ^ 2) := by
  have hxx : x + x ≠ 0 := (add_pos hx hx).ne'
  have hyy : y + y ≠ 0 := (add_pos hy hy).ne'
  have hzz : z + z ≠ 0 := (add_pos hz hz).ne'
  have hxy : x + y ≠ 0 := (add_pos hx hy).ne'
  have hxz : x + z ≠ 0 := (add_pos hx hz).ne'
  have hyz : y + z ≠ 0 := (add_pos hy hz).ne'
  unfold symmetricThreePointDet cubicApertureSourceKernel
  field_simp [hxx, hyy, hzz, hxy, hxz, hyz]
  ring

/-- On distinct positive nodes, the completed cubic source determinant is strictly positive. -/
theorem symmetricThreePointDet_cubicApertureSourceKernel_pos
    {kappa x y z : ℝ} (hkappa : 0 < kappa)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    0 < symmetricThreePointDet (cubicApertureSourceKernel kappa) x y z := by
  rw [symmetricThreePointDet_cubicApertureSourceKernel hx hy hz]
  positivity

/-- Collision-regular squared exterior gain from cubic aperture source to Poisson refinement. -/
def xiApertureCubicResponseExteriorGainSq
    (kappa a b x y z : ℝ) : ℝ :=
  16 * (b ^ 2 - a ^ 2) ^ 3 *
      (x + y) ^ 2 * (x + z) ^ 2 * (y + z) ^ 2 /
    (kappa ^ 3 * x ^ 3 * y ^ 3 * z ^ 3 *
      ((b ^ 2 + (x - y) ^ 2) * (a ^ 2 + (x - y) ^ 2)) *
      ((b ^ 2 + (x - z) ^ 2) * (a ^ 2 + (x - z) ^ 2)) *
      ((b ^ 2 + (y - z) ^ 2) * (a ^ 2 + (y - z) ^ 2)))

theorem xiApertureCubicResponseExteriorGainSq_pos
    {kappa a b x y z : ℝ} (hkappa : 0 < kappa)
    (ha : 0 < a) (hab : a < b)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 < xiApertureCubicResponseExteriorGainSq kappa a b x y z := by
  have hb : 0 < b := ha.trans hab
  have hba : 0 < b ^ 2 - a ^ 2 := by nlinarith
  unfold xiApertureCubicResponseExteriorGainSq
  positivity

/-- **Cubic determinant-line matching.**  The negative determinant of the correctly oriented
Poisson refinement is the explicit positive exterior gain times the cubic true-aperture
determinant.  No distinctness assumption is needed: the identity remains valid through node
collisions because the common Vandermonde divisor has already cancelled from the gain. -/
theorem neg_symmetricThreePointDet_poissonScaleRefinementKernel_eq_exteriorGainSq_mul
    {kappa a b x y z : ℝ} (hkappa : 0 < kappa)
    (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    -symmetricThreePointDet (poissonScaleRefinementKernel a b) x y z =
      xiApertureCubicResponseExteriorGainSq kappa a b x y z *
        symmetricThreePointDet (cubicApertureSourceKernel kappa) x y z := by
  have hk : kappa ≠ 0 := hkappa.ne'
  have hxx : x ≠ 0 := hx.ne'
  have hyy : y ≠ 0 := hy.ne'
  have hzz : z ≠ 0 := hz.ne'
  have hxySum : x + y ≠ 0 := (add_pos hx hy).ne'
  have hxzSum : x + z ≠ 0 := (add_pos hx hz).ne'
  have hyzSum : y + z ≠ 0 := (add_pos hy hz).ne'
  have haxy : a ^ 2 + (x - y) ^ 2 ≠ 0 := by positivity
  have hbxy : b ^ 2 + (x - y) ^ 2 ≠ 0 := by positivity
  have haxz : a ^ 2 + (x - z) ^ 2 ≠ 0 := by positivity
  have hbxz : b ^ 2 + (x - z) ^ 2 ≠ 0 := by positivity
  have hayz : a ^ 2 + (y - z) ^ 2 ≠ 0 := by positivity
  have hbyz : b ^ 2 + (y - z) ^ 2 ≠ 0 := by positivity
  rw [symmetricThreePointDet_poissonScaleRefinementKernel_eq_neg,
    neg_neg,
    symmetricThreePointDet_poissonScaleIncrementKernel ha hb,
    poissonScaleIncrement_eq ha hb,
    poissonScaleIncrement_eq ha hb,
    poissonScaleIncrement_eq ha hb,
    symmetricThreePointDet_cubicApertureSourceKernel hx hy hz]
  unfold xiApertureCubicResponseExteriorGainSq
  field_simp [hk, hxx, hyy, hzz, hxySum, hxzSum, hyzSum,
    haxy, hbxy, haxz, hbxz, hayz, hbyz]
  ring

/-- Actual-source specialization of the exterior matching theorem. -/
theorem neg_symmetricThreePointDet_poissonScaleRefinementKernel_eq_actualCubicGainSq_mul
    {a b x y z : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    -symmetricThreePointDet (poissonScaleRefinementKernel a b) x y z =
      xiApertureCubicResponseExteriorGainSq
          xiMobiusContinuousApertureCubicMass a b x y z *
        symmetricThreePointDet
          (cubicApertureSourceKernel xiMobiusContinuousApertureCubicMass) x y z := by
  exact
    neg_symmetricThreePointDet_poissonScaleRefinementKernel_eq_exteriorGainSq_mul
      xiMobiusContinuousApertureCubicMass_pos ha hb hx hy hz

end

end RHTower
