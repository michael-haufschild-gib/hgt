import GaloisForLFunctions.TransMetzlerWeilPositivity.APositivePrefixGivesTheExactSchurReduction

/-!
# Uniform mixed-entry payment for the complete Weil prefix

The literal plateau endpoint energy exceeds one twentieth. Uniform spectral
control through touching therefore pays the complete prefix inverse with
constant twenty, simultaneously in both horizons and overlap. The resulting
Schur lower bound retains the signed prime, Gamma, and polar mixed block.
-/

noncomputable section

open Matrix Finset Filter Topology MeasureTheory
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms

open TransMetzlerWeilPositivity SpacingScaleHarmonicAnalysis
  CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory

/-- A coercivity cost for the full form is the same upper cost for its inverse form. -/
theorem inverseQuadratic_le_of_squareMass_bound {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.PosDef) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ v : I → ℝ, v ⬝ᵥ v ≤ C * (v ⬝ᵥ A *ᵥ v)) (b : I → ℝ) :
    b ⬝ᵥ A⁻¹ *ᵥ b ≤ C * (b ⬝ᵥ b) := by
  let u := A⁻¹ *ᵥ b
  have hu : A *ᵥ u = b := by
    dsimp only [u]
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), one_mulVec]
  have hl := hbound u
  rw [hu, dotProduct_comm u b] at hl
  have hs : 0 ≤ (C • b - u) ⬝ᵥ (C • b - u) :=
    sum_nonneg fun i hi => mul_self_nonneg _
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, dotProduct_comm u b] at hs
  change b ⬝ᵥ u ≤ C * (b ⬝ᵥ b)
  apply (mul_le_mul_left hC).mp
  nlinarith only [hl, hs]

/-- One actual horizon pays the prefix square mass with constant twenty across all admissible overlaps. -/
theorem eventually_plateauPrefix_squareMass_le_twenty_energy :
    ∀ᶠ M : ℕ in atTop, ∀ N : ℕ, ∀ hMN : M ≤ N, ∀ c : ℝ,
      0 < c → c * M ≤ N → ∀ v : PrimeHorizonIndex M → ℝ,
        v ⬝ᵥ v ≤ 20 * (v ⬝ᵥ plateauPrefixBlock hMN c *ᵥ v) := by
  have henergy := completeWeilAdjunctionEnergy_transMetzlerProfile_gt_one_twentieth
    (c := 1) (m := 1) zero_lt_one (by norm_num) (by norm_num)
  have heq : completeWeilAdjunctionEnergy transMetzlerProfile 1 1 =
      bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) +
        completeWeilPoleShift transMetzlerProfile 1 - Real.log (2 * Real.pi) := by
    rw [completeWeilAdjunctionEnergy, completeWeilSelfFinitePart,
      ramanujanAdjunctionEnergy_one, if_pos rfl, mul_one, one_div, Real.log_inv]
    ring
  rw [heq] at henergy
  have hspec := eventually_completeWeil_eigenvalues_ge_uniformly_at_touching
    contDiff_transMetzlerProfile (fun u hu => transMetzlerProfile_eq_zero hu)
    integral_transMetzlerProfile_sq_pos henergy
  filter_upwards [hspec, eventually_ge_atTop (1 : ℕ)] with M hM hM1
  intro N hMN c hc hcM v
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM1
  have hNp : (0 : ℝ) < N := by exact_mod_cast hM1.trans hMN
  rw [plateauPrefixBlock_eq hM1 hMN hc]
  let d := c * M / N
  have hd : 0 < d := div_pos (mul_pos hc hMp) hNp
  have hd1 : d ≤ 1 := (div_le_one hNp).mpr hcM
  let x : EuclideanSpace ℝ (PrimeHorizonIndex M) := WithLp.toLp 2 v
  have he : (1 / 20 : ℝ) * ‖x‖ ^ 2 ≤
      ⟪Matrix.toEuclideanLin (completeWeilMatrix transMetzlerProfile d M) x, x⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum
      (completeWeilMatrix_isHermitian transMetzlerProfile d M),
      ← (completeWeilMatrix_isHermitian transMetzlerProfile d M).eigenvectorBasis.sum_sq_inner_left x,
      mul_sum]
    exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hM d hd hd1 i) (sq_nonneg _)
  rw [← real_inner_self_eq_norm_sq] at he
  have hquad : (1 / 20 : ℝ) * (v ⬝ᵥ v) ≤
      v ⬝ᵥ completeWeilMatrix transMetzlerProfile d M *ᵥ v := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, star_trivial] using he
  change v ⬝ᵥ v ≤ 20 * (v ⬝ᵥ completeWeilMatrix transMetzlerProfile d M *ᵥ v)
  linarith only [hquad]

/-- The actual prefix inverse has a dimension-independent complete coupling cost. -/
theorem eventually_plateauPrefix_inverse_quadratic_le :
    ∀ᶠ M : ℕ in atTop, ∀ N : ℕ, ∀ hMN : M ≤ N, ∀ c : ℝ,
      0 < c → c * M ≤ N → ∀ b : PrimeHorizonIndex M → ℝ,
        0 ≤ b ⬝ᵥ (plateauPrefixBlock hMN c)⁻¹ *ᵥ b ∧
          b ⬝ᵥ (plateauPrefixBlock hMN c)⁻¹ *ᵥ b ≤ 20 * (b ⬝ᵥ b) := by
  filter_upwards [eventually_plateauPrefixBlock_posDef,
    eventually_plateauPrefix_squareMass_le_twenty_energy] with M hpos hbound
  intro N hMN c hc hcM b
  have hA := hpos N hMN c hc hcM
  refine ⟨?_, inverseQuadratic_le_of_squareMass_bound hA (by norm_num)
    (hbound N hMN c hc hcM) b⟩
  simpa only [star_trivial] using hA.inv.posSemidef.dotProduct_mulVec_nonneg b

private theorem real_adjoint_pair {I J : Type*} [Fintype I] [Fintype J]
    (B : Matrix I J ℝ) (y : J → ℝ) (z : I → ℝ) :
    y ⬝ᵥ Bᴴ *ᵥ z = (B *ᵥ y) ⬝ᵥ z := by
  simp only [dotProduct, Matrix.mulVec, conjTranspose_apply, star_trivial,
    Finset.mul_sum, Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

/-- The literal complete residual lies between the tail and its uniform mixed-entry debit. -/
theorem eventually_plateauPrefixSchur_quadratic_payment :
    ∀ᶠ M : ℕ in atTop, ∀ N : ℕ, ∀ hMN : M ≤ N, ∀ c : ℝ,
      0 < c → c * M ≤ N → ∀ y : HorizonTail M N → ℝ,
        y ⬝ᵥ plateauTailBlock M N c *ᵥ y -
          20 * ((plateauMixedBlock hMN c *ᵥ y) ⬝ᵥ (plateauMixedBlock hMN c *ᵥ y)) ≤
            y ⬝ᵥ plateauPrefixSchur hMN c *ᵥ y ∧
        y ⬝ᵥ plateauPrefixSchur hMN c *ᵥ y ≤ y ⬝ᵥ plateauTailBlock M N c *ᵥ y := by
  filter_upwards [eventually_plateauPrefix_inverse_quadratic_le] with M hM
  intro N hMN c hc hcM y
  obtain ⟨h0, hu⟩ := hM N hMN c hc hcM (plateauMixedBlock hMN c *ᵥ y)
  have he : y ⬝ᵥ plateauPrefixSchur hMN c *ᵥ y =
      y ⬝ᵥ plateauTailBlock M N c *ᵥ y -
        (plateauMixedBlock hMN c *ᵥ y) ⬝ᵥ (plateauPrefixBlock hMN c)⁻¹ *ᵥ
          (plateauMixedBlock hMN c *ᵥ y) := by
    rw [plateauPrefixSchur, sub_mulVec, dotProduct_sub,
      ← mulVec_mulVec, ← mulVec_mulVec, real_adjoint_pair]
  rw [he]
  constructor <;> linarith only [h0, hu]

#print axioms inverseQuadratic_le_of_squareMass_bound
#print axioms eventually_plateauPrefix_squareMass_le_twenty_energy
#print axioms eventually_plateauPrefix_inverse_quadratic_le
#print axioms eventually_plateauPrefixSchur_quadratic_payment

end GaloisForLFunctions.CompletedArithmeticForms
