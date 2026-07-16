import GaloisForLFunctions.HTGeometry.QuadraticPhysicalCharacterOsculation

/-!
# Orientation anomaly of a physical defect product

Full reversal of a finite source does not change its physical defect product arbitrarily.  The
change is the exact cocycle `(-1)^rank * exp(-(first source moment) * z)`.  Hence a balanced source
of even rank is invisible to reversal at the level of the complete analytic physical-character
germ, not merely at the level of support or topology.
-/

open Complex Finset

namespace GaloisForLFunctions

noncomputable section

/-- The complete physical-character product attached to a finite source family. -/
def physicalDefectProduct {ι : Type*} (s : Finset ι) (τ : ι → ℂ) (z : ℂ) : ℂ :=
  ∏ i ∈ s, (Complex.exp (τ i * z) - 1)

/-- The centered, self-dual factor in the physical defect product. -/
def centeredPhysicalDefectProduct {ι : Type*} (s : Finset ι) (τ : ι → ℂ) (z : ℂ) : ℂ :=
  ∏ i ∈ s, (2 * Complex.sinh (τ i * z / 2))

theorem physicalDefect_eq_midpoint (a z : ℂ) :
    Complex.exp (a * z) - 1 =
      Complex.exp (a * z / 2) * (2 * Complex.sinh (a * z / 2)) := by
  have hsq : Complex.exp (a * z) =
      Complex.exp (a * z / 2) * Complex.exp (a * z / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hinv : Complex.exp (a * z / 2) * Complex.exp (-(a * z / 2)) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc
    Complex.exp (a * z) - 1 =
        Complex.exp (a * z / 2) * Complex.exp (a * z / 2) - 1 := by rw [hsq]
    _ = Complex.exp (a * z / 2) *
        (Complex.exp (a * z / 2) - Complex.exp (-(a * z / 2))) := by
          rw [mul_sub]
          rw [hinv]
    _ = Complex.exp (a * z / 2) * (2 * Complex.sinh (a * z / 2)) := by
          unfold Complex.sinh
          ring

/-- **Midpoint polarization split.**  The complete physical boundary is the product of the
oriented first-moment character and a centered self-dual factor. -/
theorem physicalDefectProduct_midpoint_factorization (s : Finset ι) (τ : ι → ℂ) (z : ℂ) :
    physicalDefectProduct s τ z =
      Complex.exp ((∑ i ∈ s, τ i) * z / 2) * centeredPhysicalDefectProduct s τ z := by
  calc
    physicalDefectProduct s τ z =
        ∏ i ∈ s, (Complex.exp (τ i * z / 2) *
          (2 * Complex.sinh (τ i * z / 2))) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact physicalDefect_eq_midpoint (τ i) z
    _ = (∏ i ∈ s, Complex.exp (τ i * z / 2)) *
        centeredPhysicalDefectProduct s τ z := by
          rw [Finset.prod_mul_distrib]
          rfl
    _ = Complex.exp ((∑ i ∈ s, τ i) * z / 2) *
        centeredPhysicalDefectProduct s τ z := by
          rw [← Complex.exp_sum]
          congr 2
          calc
            (∑ i ∈ s, τ i * z / 2) = (∑ i ∈ s, τ i * z) / 2 := by
              rw [Finset.sum_div]
            _ = (∑ i ∈ s, τ i) * z / 2 := by rw [Finset.sum_mul]

/-- **Physical orientation-anomaly law.**  Full source reversal changes the complete physical
defect product by exactly its rank parity and first source moment. -/
theorem physicalDefectProduct_neg (s : Finset ι) (τ : ι → ℂ) (z : ℂ) :
    physicalDefectProduct s (-τ) z =
      (-1 : ℂ) ^ s.card * Complex.exp (-(∑ i ∈ s, τ i) * z) *
        physicalDefectProduct s τ z := by
  have hfactor : ∀ i ∈ s,
      Complex.exp ((-τ) i * z) - 1 =
        ((-1 : ℂ) * Complex.exp (-(τ i * z))) * (Complex.exp (τ i * z) - 1) := by
    intro i hi
    rw [show (-τ) i * z = -(τ i * z) by simp, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero]
    ring
  calc
    physicalDefectProduct s (-τ) z =
        ∏ i ∈ s, (((-1 : ℂ) * Complex.exp (-(τ i * z))) *
          (Complex.exp (τ i * z) - 1)) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact hfactor i hi
    _ = (∏ i ∈ s, ((-1 : ℂ) * Complex.exp (-(τ i * z)))) *
        (∏ i ∈ s, (Complex.exp (τ i * z) - 1)) := by
          rw [Finset.prod_mul_distrib]
    _ = ((∏ i ∈ s, (-1 : ℂ)) * (∏ i ∈ s, Complex.exp (-(τ i * z)))) *
        (∏ i ∈ s, (Complex.exp (τ i * z) - 1)) := by
          rw [Finset.prod_mul_distrib]
    _ = (-1 : ℂ) ^ s.card * Complex.exp (-(∑ i ∈ s, τ i) * z) *
        physicalDefectProduct s τ z := by
          rw [← Complex.exp_sum]
          have hsum : (∑ i ∈ s, -(τ i * z)) = -(∑ i ∈ s, τ i) * z := by
            calc
              (∑ i ∈ s, -(τ i * z)) = -(∑ i ∈ s, τ i * z) := by
                rw [Finset.sum_neg_distrib]
              _ = -((∑ i ∈ s, τ i) * z) := by rw [Finset.sum_mul]
              _ = -(∑ i ∈ s, τ i) * z := by ring
          rw [hsum]
          simp [physicalDefectProduct]

/-- The exact multiplicative anomaly carried by full physical-source reversal. -/
def physicalReversalAnomaly (s : Finset ι) (τ : ι → ℂ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ s.card * Complex.exp (-(∑ i ∈ s, τ i) * z)

theorem physicalDefectProduct_neg_eq_anomaly_mul (s : Finset ι) (τ : ι → ℂ) (z : ℂ) :
    physicalDefectProduct s (-τ) z =
      physicalReversalAnomaly s τ z * physicalDefectProduct s τ z := by
  exact physicalDefectProduct_neg s τ z

/-- The reversal multiplier is a genuine involutive cocycle. -/
theorem physicalReversalAnomaly_neg_mul (s : Finset ι) (τ : ι → ℂ) (z : ℂ) :
    physicalReversalAnomaly s (-τ) z * physicalReversalAnomaly s τ z = 1 := by
  unfold physicalReversalAnomaly
  rw [show (∑ i ∈ s, (-τ) i) = -(∑ i ∈ s, τ i) by simp]
  have hexp : -(-∑ i ∈ s, τ i) * z + -(∑ i ∈ s, τ i) * z = 0 := by ring
  have hsign : (-1 : ℂ) ^ s.card * (-1 : ℂ) ^ s.card = 1 := by
    rw [← pow_add]
    simp [← two_mul]
  calc
    (-1 : ℂ) ^ s.card * Complex.exp ((- -∑ i ∈ s, τ i) * z) *
        ((-1 : ℂ) ^ s.card * Complex.exp ((-∑ i ∈ s, τ i) * z)) =
      ((-1 : ℂ) ^ s.card * (-1 : ℂ) ^ s.card) *
        (Complex.exp ((- -∑ i ∈ s, τ i) * z) *
          Complex.exp ((-∑ i ∈ s, τ i) * z)) := by ring
    _ = 1 := by rw [hsign, ← Complex.exp_add, hexp]; simp

/-- Reverse precisely the source components selected by the Boolean mask. -/
def sourceSignSurgery (flip : ι → Bool) (τ : ι → ℂ) (i : ι) : ℂ :=
  if flip i = true then -τ i else τ i

/-- The one-component multiplier contributed by a selected sign surgery. -/
def physicalSignMultiplier (flip : ι → Bool) (τ : ι → ℂ) (z : ℂ) (i : ι) : ℂ :=
  if flip i = true then -Complex.exp (-(τ i * z)) else 1

/-- The anomaly multiplier for an arbitrary componentwise orientation surgery. -/
def componentwiseOrientationAnomaly
    (s : Finset ι) (flip : ι → Bool) (τ : ι → ℂ) (z : ℂ) : ℂ :=
  ∏ i ∈ s, physicalSignMultiplier flip τ z i

theorem physicalDefectProduct_sourceSignSurgery
    (s : Finset ι) (flip : ι → Bool) (τ : ι → ℂ) (z : ℂ) :
    physicalDefectProduct s (sourceSignSurgery flip τ) z =
      componentwiseOrientationAnomaly s flip τ z * physicalDefectProduct s τ z := by
  calc
    physicalDefectProduct s (sourceSignSurgery flip τ) z =
        ∏ i ∈ s, (physicalSignMultiplier flip τ z i *
          (Complex.exp (τ i * z) - 1)) := by
            apply Finset.prod_congr rfl
            intro i hi
            by_cases hflip : flip i = true
            · simp [sourceSignSurgery, physicalSignMultiplier, hflip]
              rw [Complex.exp_neg]
              field_simp [Complex.exp_ne_zero]
              ring
            · simp [sourceSignSurgery, physicalSignMultiplier, hflip]
    _ = componentwiseOrientationAnomaly s flip τ z * physicalDefectProduct s τ z := by
          rw [Finset.prod_mul_distrib]
          rfl

def xorSignSurgery (flip twist : ι → Bool) (i : ι) : Bool :=
  xor (flip i) (twist i)

/-- **Componentwise anomaly cocycle.**  Orientation multipliers compose by the cocycle law for the
Boolean sign-surgery group acting on the source. -/
theorem componentwiseOrientationAnomaly_cocycle
    (s : Finset ι) (flip twist : ι → Bool) (τ : ι → ℂ) (z : ℂ) :
    componentwiseOrientationAnomaly s (xorSignSurgery flip twist) τ z =
      componentwiseOrientationAnomaly s flip (sourceSignSurgery twist τ) z *
        componentwiseOrientationAnomaly s twist τ z := by
  unfold componentwiseOrientationAnomaly
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases hflip : flip i <;> cases htwist : twist i
  · simp [xorSignSurgery, physicalSignMultiplier, hflip, htwist]
  · simp [xorSignSurgery, physicalSignMultiplier, hflip, htwist]
  · simp [xorSignSurgery, physicalSignMultiplier, sourceSignSurgery, hflip, htwist]
  · simp [xorSignSurgery, physicalSignMultiplier, sourceSignSurgery, hflip, htwist,
      Complex.exp_neg]

/-- Every balanced even-rank source is completely invisible to full reversal on its physical
defect germ. -/
theorem physicalDefectProduct_neg_eq_of_even_balanced
    (s : Finset ι) (τ : ι → ℂ) (z : ℂ)
    (heven : Even s.card) (hbalanced : ∑ i ∈ s, τ i = 0) :
    physicalDefectProduct s (-τ) z = physicalDefectProduct s τ z := by
  rw [physicalDefectProduct_neg, hbalanced]
  simp [Even.neg_one_pow heven]

/-- On every balanced source the residual reversal anomaly is exactly rank parity. -/
theorem physicalDefectProduct_neg_eq_parity_of_balanced
    (s : Finset ι) (τ : ι → ℂ) (z : ℂ)
    (hbalanced : ∑ i ∈ s, τ i = 0) :
    physicalDefectProduct s (-τ) z =
      (-1 : ℂ) ^ s.card * physicalDefectProduct s τ z := by
  rw [physicalDefectProduct_neg, hbalanced]
  simp

end

end GaloisForLFunctions
