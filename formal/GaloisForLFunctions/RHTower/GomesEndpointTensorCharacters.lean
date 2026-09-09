import GaloisForLFunctions.RHTower.GomesClarkDiffuseRangeBoundary

/-!
# Integer tensor characters of the endpoint density

Section 5.2 of arXiv:2509.25276v7 derives an integral charge lattice from tensor powers and duals
of a generating line. Here this construction is applied to the corpus's scalar endpoint densities:
charge `n` of base exponent `b` has exponent `n*b`. The character laws hold away from the blind
endpoint and almost everywhere for the uniform source. This is an experimental scalar-density
model, not a formalization of the paper's vector-bundle theory.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

/-- The integer tensor charge of a chosen real endpoint exponent. -/
def gomesEndpointTensorDensity (b : ℝ) (n : ℤ) : HausdorffSourceSpace → ℝ :=
  gomesClarkEndpointDensity ((n : ℝ) * b)

/-- Neutral charge is the constant unit density. -/
theorem gomesEndpointTensorDensity_zero (b : ℝ) : gomesEndpointTensorDensity b 0 = 1 := by
  funext y
  simp [gomesEndpointTensorDensity, gomesClarkEndpointDensity]

/-- The generating charge is the original endpoint density. -/
theorem gomesEndpointTensorDensity_one (b : ℝ) :
    gomesEndpointTensorDensity b 1 = gomesClarkEndpointDensity b := by
  simp [gomesEndpointTensorDensity]

/-- The charged density is literally the integer power of the generating density. -/
theorem gomesEndpointTensorDensity_zpow (b : ℝ) (n : ℤ) (y : HausdorffSourceSpace) :
    gomesEndpointTensorDensity b n y = (gomesClarkEndpointDensity b y) ^ n := by
  dsimp [gomesEndpointTensorDensity, gomesClarkEndpointDensity]
  rw [mul_comm, Real.rpow_mul_intCast (sub_nonneg.mpr y.property.2)]

/-- Dual charge is the pointwise inverse, including the chosen zero-endpoint convention. -/
theorem gomesEndpointTensorDensity_neg (b : ℝ) (n : ℤ) :
    gomesEndpointTensorDensity b (-n) = fun y => (gomesEndpointTensorDensity b n y)⁻¹ := by
  funext y
  rw [gomesEndpointTensorDensity_zpow, gomesEndpointTensorDensity_zpow, zpow_neg]

/-- Every charge is strictly positive off the blind endpoint. -/
theorem gomesEndpointTensorDensity_pos (b : ℝ) (n : ℤ)
    (y : {y : HausdorffSourceSpace // y ≠ gomesHausdorffOne}) :
    0 < gomesEndpointTensorDensity b n y := by
  have hy : (y.val : ℝ) ≠ 1 := fun h => y.property (Subtype.ext h)
  exact Real.rpow_pos_of_pos (sub_pos.mpr (lt_of_le_of_ne y.val.property.2 hy)) _

/-- Tensor composition adds integer charges at every non-blind coordinate. -/
theorem gomesEndpointTensorDensity_add (b : ℝ) (m n : ℤ)
    (y : {y : HausdorffSourceSpace // y ≠ gomesHausdorffOne}) :
    gomesEndpointTensorDensity b (m + n) y =
      gomesEndpointTensorDensity b m y * gomesEndpointTensorDensity b n y := by
  have hy : (y.val : ℝ) ≠ 1 := fun h => y.property (Subtype.ext h)
  have hp : 0 < 1 - (y.val : ℝ) := sub_pos.mpr (lt_of_le_of_ne y.val.property.2 hy)
  dsimp [gomesEndpointTensorDensity, gomesClarkEndpointDensity]
  rw [Int.cast_add, add_mul, Real.rpow_add hp]

/-- Tensor composition holds almost everywhere on the actual compact source. -/
theorem gomesEndpointTensorDensity_add_ae (b : ℝ) (m n : ℤ) :
    gomesEndpointTensorDensity b (m + n) =ᵐ[
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace)]
        (fun y => gomesEndpointTensorDensity b m y * gomesEndpointTensorDensity b n y) := by
  have hone : ∀ᵐ y ∂(gomesHausdorffUniformSource : Measure HausdorffSourceSpace),
      y ≠ gomesHausdorffOne := by
    change ∀ᵐ y ∂(volume : Measure HausdorffSourceSpace), y ≠ gomesHausdorffOne
    simp [ae_iff]
  filter_upwards [hone] with y hy
  exact gomesEndpointTensorDensity_add b m n ⟨y, hy⟩

/-- A charge and its dual cancel almost everywhere. -/
theorem gomesEndpointTensorDensity_dual_cancel_ae (b : ℝ) (n : ℤ) :
    (fun y => gomesEndpointTensorDensity b n y * gomesEndpointTensorDensity b (-n) y) =ᵐ[
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace)] 1 := by
  simpa only [add_neg_cancel, gomesEndpointTensorDensity_zero] using
    (gomesEndpointTensorDensity_add_ae b n (-n)).symm

/-- Iterated tensoring agrees with multiplication of integer charges. -/
theorem gomesEndpointTensorDensity_mul (b : ℝ) (m n : ℤ) (y : HausdorffSourceSpace) :
    gomesEndpointTensorDensity b (m * n) y = (gomesEndpointTensorDensity b n y) ^ m := by
  rw [gomesEndpointTensorDensity_zpow, gomesEndpointTensorDensity_zpow, mul_comm, zpow_mul]

/-- Different generating exponents and charges agree exactly when their actual exponents agree. -/
theorem gomesEndpointTensorDensity_eq_iff (b c : ℝ) (m n : ℤ) :
    gomesEndpointTensorDensity b m = gomesEndpointTensorDensity c n ↔
      (m : ℝ) * b = (n : ℝ) * c := by
  constructor
  · intro h
    let y : HausdorffSourceSpace := ⟨1 / 2, by constructor <;> linarith⟩
    have he := congrFun h y
    change (1 - (1 / 2 : ℝ)) ^ ((m : ℝ) * b) = (1 - (1 / 2 : ℝ)) ^ ((n : ℝ) * c) at he
    exact (Real.rpow_right_inj (by linarith : (0 : ℝ) < 1 - 1 / 2)
      (by linarith : (1 : ℝ) - 1 / 2 ≠ 1)).mp he
  · intro h
    simp only [gomesEndpointTensorDensity, h]

/-- Only zero charge or a trivial generator produces the neutral character. -/
theorem gomesEndpointTensorDensity_neutral_iff (b : ℝ) (n : ℤ) :
    gomesEndpointTensorDensity b n = 1 ↔ n = 0 ∨ b = 0 := by
  rw [← gomesEndpointTensorDensity_zero b, gomesEndpointTensorDensity_eq_iff]
  simp only [Int.cast_zero, zero_mul, mul_eq_zero, Int.cast_eq_zero]

/-- Every nontrivial generator faithfully remembers the entire integer charge lattice. -/
theorem gomesEndpointTensorDensity_injective_iff (b : ℝ) :
    Function.Injective (gomesEndpointTensorDensity b) ↔ b ≠ 0 := by
  constructor
  · intro h hb
    have he : gomesEndpointTensorDensity b (0 : ℤ) = gomesEndpointTensorDensity b 1 :=
      (gomesEndpointTensorDensity_eq_iff b b 0 1).mpr (by simp [hb])
    exact zero_ne_one (h he)
  · intro hb m n h
    have he := (gomesEndpointTensorDensity_eq_iff b b m n).mp h
    exact Int.cast_inj.mp (mul_right_cancel₀ hb he)

/-- Analytic admissibility is an exact inequality on the integer charge lattice. -/
theorem gomesEndpointTensorDensity_integrable_iff (b : ℝ) (n : ℤ) :
    Integrable (gomesEndpointTensorDensity b n)
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) ↔ -1 < (n : ℝ) * b :=
  gomesClarkEndpointDensity_integrable_iff _

end RHTower
