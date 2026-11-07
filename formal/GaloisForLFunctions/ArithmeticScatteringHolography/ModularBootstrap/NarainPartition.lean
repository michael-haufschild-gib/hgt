import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMass
import GaloisForLFunctions.RHTower.ThetaChiEightSeries
import GaloisForLFunctions.HTGeometry.TruncatedConvolutionCommutator

/-!
# The convergent two-torus Narain partition function

Explicit mass coercivity dominates every charge by a product of four Gaussian
series. The spin phase has unit modulus, so the complete momentum-winding
partition sum converges absolutely at every worldsheet point in the upper half-plane.
-/

open Complex RHTower
open GaloisForLFunctions.HTGeometry MeasureTheory

namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

noncomputable section

/-- The real Boltzmann weight of a momentum-winding charge. -/
def narainBoltzmann (ρ σ : D4BMUpperHalfPlaneCoordinate) (y : ℝ)
    (q : (ℤ × ℤ) × (ℤ × ℤ)) : ℝ :=
  Real.exp (-(Real.pi * y * narainMassSq ρ σ q))

/-- A charge contributes its Boltzmann weight and integer spin phase. -/
def narainPartitionTerm (ρ σ : D4BMUpperHalfPlaneCoordinate) (x y : ℝ)
    (q : (ℤ × ℤ) × (ℤ × ℤ)) : ℂ :=
  (narainBoltzmann ρ σ y q : ℂ) *
    fourierChar (chargeSpin q) x

/-- The central-charge-two primary partition function, including the vacuum. -/
def narainPartition (ρ σ : D4BMUpperHalfPlaneCoordinate) (x y : ℝ) : ℂ :=
  (y : ℂ) * ∑' q, narainPartitionTerm ρ σ x y q

/-- The scalar primary partition function, including the vacuum. -/
def narainScalarPartition (ρ σ : D4BMUpperHalfPlaneCoordinate) (y : ℝ) : ℂ :=
  (y : ℂ) * ∑' q : {q : (ℤ × ℤ) × (ℤ × ℤ) // chargeSpin q = 0},
    (narainBoltzmann ρ σ y q.val : ℂ)

private theorem summable_chargeGaussian {c : ℝ} (hc : 0 < c) :
    Summable (fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      Real.exp (-(Real.pi * c * chargeEuclideanSq q))) := by
  have h₁ := summable_gauss_int hc
  have h₂ := h₁.mul_of_nonneg h₁
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have h₄ := h₂.mul_of_nonneg h₂ (by intro q; positivity) (by intro q; positivity)
  refine h₄.congr fun q => ?_
  simp only [← Real.exp_add]
  congr 1
  dsimp only [chargeEuclideanSq]
  ring

/-- The full real charge weights are summable at every positive worldsheet height. -/
theorem summable_narainBoltzmann (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {y : ℝ} (hy : 0 < y) : Summable (narainBoltzmann ρ σ y) := by
  have hC := massCoercivityConstant_pos ρ σ
  have hc : 0 < y / massCoercivityConstant ρ σ := div_pos hy hC
  refine Summable.of_nonneg_of_le (fun q => (Real.exp_pos _).le) ?_
    (summable_chargeGaussian hc)
  intro q
  apply Real.exp_le_exp.mpr
  have hmass : chargeEuclideanSq q / massCoercivityConstant ρ σ ≤ narainMassSq ρ σ q := by
    apply (div_le_iff₀ hC).mpr
    simpa only [mul_comm] using chargeEuclideanSq_le_mass ρ σ q
  calc
    -(Real.pi * y * narainMassSq ρ σ q) ≤
        -(Real.pi * y * (chargeEuclideanSq q / massCoercivityConstant ρ σ)) :=
      neg_le_neg (mul_le_mul_of_nonneg_left hmass (mul_pos Real.pi_pos hy).le)
    _ = -(Real.pi * (y / massCoercivityConstant ρ σ) * chargeEuclideanSq q) := by ring

/-- The spin phase does not alter the size of a partition term. -/
theorem norm_narainPartitionTerm (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (x y : ℝ) (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    ‖narainPartitionTerm ρ σ x y q‖ = narainBoltzmann ρ σ y q := by
  rw [narainPartitionTerm, fourierChar, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (show 0 ≤ narainBoltzmann ρ σ y q from (Real.exp_pos _).le),
    Complex.norm_exp]
  have hphase : (2 * Real.pi * Complex.I * (chargeSpin q : ℂ) * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hphase, Real.exp_zero, mul_one]

/-- Absolute convergence of the actual Narain partition sum. -/
theorem summable_norm_narainPartitionTerm (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Summable (fun q => ‖narainPartitionTerm ρ σ x y q‖) := by
  simp only [norm_narainPartitionTerm]
  exact summable_narainBoltzmann ρ σ hy

theorem summable_narainPartitionTerm (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (x : ℝ) {y : ℝ} (hy : 0 < y) : Summable (narainPartitionTerm ρ σ x y) :=
  (summable_norm_narainPartitionTerm ρ σ x hy).of_norm

private theorem continuous_narainPartitionTerm (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (y : ℝ) (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    Continuous (fun x => narainPartitionTerm ρ σ x y q) :=
  continuous_const.mul (continuous_fourierChar (chargeSpin q))

private theorem narainPartitionTerm_add_one (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (x y : ℝ) (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    narainPartitionTerm ρ σ (x + 1) y q = narainPartitionTerm ρ σ x y q := by
  have h : fourierChar (chargeSpin q) (x + 1) =
      fourierChar (chargeSpin q) x * fourierChar (chargeSpin q) 1 := by
    rw [fourierChar, fourierChar, fourierChar, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [narainPartitionTerm, h, fourierChar_one, mul_one]

/-- Integer spin gives the modular translation law. -/
theorem narainPartition_add_one (ρ σ : D4BMUpperHalfPlaneCoordinate) (x y : ℝ) :
    narainPartition ρ σ (x + 1) y = narainPartition ρ σ x y := by
  simp only [narainPartition, narainPartitionTerm_add_one]

private theorem integral_narainPartitionTerm (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (y : ℝ) (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    (∫ x in (0 : ℝ)..1, narainPartitionTerm ρ σ x y q) =
      if chargeSpin q = 0 then (narainBoltzmann ρ σ y q : ℂ) else 0 := by
  simp only [narainPartitionTerm]
  rw [intervalIntegral.integral_const_mul, integral_fourierChar]
  by_cases h : chargeSpin q = 0 <;> simp [h]

/-- Averaging the actual partition function retains exactly the scalar charges.
Gaussian domination justifies the interchange of the charge sum and integral. -/
theorem integral_narainPartition_eq_scalar (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {y : ℝ} (hy : 0 < y) :
    (∫ x in Set.Ioc (0 : ℝ) 1, narainPartition ρ σ x y) = narainScalarPartition ρ σ y := by
  have hInt : ∀ q, IntegrableOn (fun x => narainPartitionTerm ρ σ x y q)
      (Set.Ioc (0 : ℝ) 1) := fun q =>
    ((continuous_narainPartitionTerm ρ σ y q).intervalIntegrable 0 1).1
  have hnorm : ∀ q, (∫ x in Set.Ioc (0 : ℝ) 1, ‖narainPartitionTerm ρ σ x y q‖) =
      narainBoltzmann ρ σ y q := by
    intro q
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [norm_narainPartitionTerm, intervalIntegral.integral_const,
      sub_zero, one_smul]
  have hsum : Summable (fun q =>
      ∫ x in Set.Ioc (0 : ℝ) 1, ‖narainPartitionTerm ρ σ x y q‖) :=
    (summable_narainBoltzmann ρ σ hy).congr (fun q => (hnorm q).symm)
  simp only [narainPartition, narainScalarPartition]
  rw [integral_const_mul,
    integral_tsum_eq_tsum_integral_of_summable_integral_norm
      (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (F := fun q x => narainPartitionTerm ρ σ x y q) hInt hsum]
  congr 1
  calc
    _ = ∑' q, {q : (ℤ × ℤ) × (ℤ × ℤ) | chargeSpin q = 0}.indicator
        (fun q => (narainBoltzmann ρ σ y q : ℂ)) q := by
      apply tsum_congr
      intro q
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_narainPartitionTerm]
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    _ = _ := (tsum_subtype {q : (ℤ × ℤ) × (ℤ × ℤ) | chargeSpin q = 0}
      (fun q => (narainBoltzmann ρ σ y q : ℂ))).symm

end

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.summable_narainBoltzmann
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.summable_norm_narainPartitionTerm
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narainPartition_add_one
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.integral_narainPartition_eq_scalar
