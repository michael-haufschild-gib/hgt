import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainDirichlet
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPartition
import GaloisForLFunctions.RHTower.FiniteExponentialSumMellin
import GaloisForLFunctions.HTGeometry.DaiYoshikawa.SpectralZetaMellinSum

/-!
# The actual scalar Narain heat sum has the Eisenstein-product Mellin transform

Each nonvacuum charge has positive mass. Its Mellin integral is the scaled
Gamma integral, and the integral of its norm is a constant times its mass
Dirichlet term at the real part of the exponent. Absolute Dirichlet
convergence therefore justifies the full charge-sum interchange.
-/

open Complex RHTower MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

noncomputable section

/-- The actual scalar heat sum with the vacuum removed. -/
def narainScalarHeat (ρ σ : D4BMUpperHalfPlaneCoordinate) (y : ℝ) : ℂ :=
  ∑' q : NonzeroScalarCharge, (narainBoltzmann ρ σ y q.val : ℂ)

theorem summable_narainScalarHeatTerm (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : NonzeroScalarCharge => (narainBoltzmann ρ σ y q.val : ℂ)) := by
  apply Summable.of_norm
  have h : Summable (fun q : NonzeroScalarCharge => narainBoltzmann ρ σ y q.val) :=
    (summable_narainBoltzmann ρ σ hy).comp_injective Subtype.val_injective
  refine h.congr fun q => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg
    (show 0 ≤ narainBoltzmann ρ σ y q.val from (Real.exp_pos _).le)]

private def scalarZeroExtension (ρ σ : D4BMUpperHalfPlaneCoordinate) (y : ℝ)
    (q : (ℤ × ℤ) × (ℤ × ℤ)) : ℂ :=
  if chargeSpin q = 0 then (narainBoltzmann ρ σ y q : ℂ) else 0

/-- Removing the vacuum from the averaged partition function leaves exactly the heat sum. -/
theorem narainScalarPartition_eq_heat (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {y : ℝ} (hy : 0 < y) :
    narainScalarPartition ρ σ y = (y : ℂ) * (1 + narainScalarHeat ρ σ y) := by
  classical
  have hsum : Summable (scalarZeroExtension ρ σ y) := by
    refine Summable.of_norm_bounded (summable_narainBoltzmann ρ σ hy) fun q => ?_
    by_cases hj : chargeSpin q = 0
    · rw [scalarZeroExtension, if_pos hj, Complex.norm_real,
        Real.norm_of_nonneg (show 0 ≤ narainBoltzmann ρ σ y q from (Real.exp_pos _).le)]
    · rw [scalarZeroExtension, if_neg hj, norm_zero]
      exact (Real.exp_pos _).le
  have hvacuum : scalarZeroExtension ρ σ y ((0, 0), (0, 0)) = 1 := by
    simp [scalarZeroExtension, chargeSpin, narainBoltzmann, narainMassSq, targetQuadratic]
  have hscalar : (∑' q : {q : (ℤ × ℤ) × (ℤ × ℤ) // chargeSpin q = 0},
      (narainBoltzmann ρ σ y q.val : ℂ)) = ∑' q, scalarZeroExtension ρ σ y q := by
    calc
      _ = ∑' q, {q : (ℤ × ℤ) × (ℤ × ℤ) | chargeSpin q = 0}.indicator
          (fun q => (narainBoltzmann ρ σ y q : ℂ)) q :=
        tsum_subtype {q : (ℤ × ℤ) × (ℤ × ℤ) | chargeSpin q = 0}
          (fun q => (narainBoltzmann ρ σ y q : ℂ))
      _ = _ := by simp only [Set.indicator_apply, Set.mem_setOf_eq, scalarZeroExtension]
  have hheat : narainScalarHeat ρ σ y = ∑' q : (ℤ × ℤ) × (ℤ × ℤ),
      if q = ((0, 0), (0, 0)) then 0 else scalarZeroExtension ρ σ y q := by
    calc
      _ = ∑' q, {q : (ℤ × ℤ) × (ℤ × ℤ) |
          q.1.1 * q.2.1 + q.1.2 * q.2.2 = 0 ∧ q ≠ ((0, 0), (0, 0))}.indicator
            (fun q => (narainBoltzmann ρ σ y q : ℂ)) q :=
        tsum_subtype _ (fun q => (narainBoltzmann ρ σ y q : ℂ))
      _ = _ := by
        apply tsum_congr
        intro q
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
        change (if chargeSpin q = 0 ∧ q ≠ ((0, 0), (0, 0)) then
            (narainBoltzmann ρ σ y q : ℂ) else 0) = _
        by_cases hq : q = ((0, 0), (0, 0))
        · simp [hq]
        · by_cases hj : chargeSpin q = 0 <;> simp [scalarZeroExtension, hq, hj]
  change (y : ℂ) * _ = (y : ℂ) * _
  apply congrArg (fun z : ℂ => (y : ℂ) * z)
  calc
    _ = ∑' q, scalarZeroExtension ρ σ y q := hscalar
    _ = _ := by
      rw [hsum.tsum_eq_add_tsum_ite ((0, 0), (0, 0)), hvacuum, ← hheat]

private def scalarMellinTerm (ρ σ : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (q : NonzeroScalarCharge) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (s - 1) * (narainBoltzmann ρ σ y q.val : ℂ)

private theorem scalarMellinTerm_exp (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (s : ℂ) (q : NonzeroScalarCharge) (y : ℝ) :
    scalarMellinTerm ρ σ s q y = (y : ℂ) ^ (s - 1) *
      (Real.exp (-((Real.pi * narainMassSq ρ σ q.val) * y)) : ℂ) := by
  dsimp only [scalarMellinTerm, narainBoltzmann]
  congr 3
  ring

private theorem integrable_scalarMellinTerm (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 0 < s.re) (q : NonzeroScalarCharge) :
    IntegrableOn (scalarMellinTerm ρ σ s q) (Set.Ioi 0) := by
  have h := mellinConvergent_exp_neg_mul
    (mul_pos Real.pi_pos (narainMassSq_pos ρ σ q.property.2)) hs
  simp only [MellinConvergent, smul_eq_mul] at h
  exact h.congr_fun (fun y _ => (scalarMellinTerm_exp ρ σ s q y).symm)
    measurableSet_Ioi

private theorem integral_scalarMellinTerm (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 0 < s.re) (q : NonzeroScalarCharge) :
    (∫ y in Set.Ioi (0 : ℝ), scalarMellinTerm ρ σ s q y) =
      ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s) * narainDirichletTerm ρ σ s q := by
  have hmass := narainMassSq_pos ρ σ q.property.2
  have h := mellin_exp_neg_mul_finiteExponentialSumMellin
    (mul_pos Real.pi_pos hmass) hs
  simp only [mellin, smul_eq_mul] at h
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun y _ => scalarMellinTerm_exp ρ σ s q y), h, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le hmass.le]
  dsimp only [narainDirichletTerm]
  ring

private theorem integral_norm_scalarMellinTerm (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 0 < s.re) (q : NonzeroScalarCharge) :
    (∫ y in Set.Ioi (0 : ℝ), ‖scalarMellinTerm ρ σ s q y‖) =
      (Real.Gamma s.re * Real.pi ^ (-s.re)) * ‖narainDirichletTerm ρ σ s q‖ := by
  have hmass := narainMassSq_pos ρ σ q.property.2
  have hnorm (y : ℝ) (hy : y ∈ Set.Ioi (0 : ℝ)) :
      ‖scalarMellinTerm ρ σ s q y‖ =
        Real.exp (-((Real.pi * narainMassSq ρ σ q.val) * y)) * y ^ (s.re - 1) := by
    rw [scalarMellinTerm_exp, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_comm _ _
  rw [setIntegral_congr_fun measurableSet_Ioi hnorm,
    DaiYoshikawa.integral_exp_neg_mul_rpow (mul_pos Real.pi_pos hmass) hs,
    narainDirichletTerm, Complex.norm_cpow_eq_rpow_re_of_pos hmass]
  simp only [Complex.neg_re]
  rw [Real.mul_rpow Real.pi_pos.le hmass.le, Real.rpow_neg Real.pi_pos.le,
    Real.rpow_neg hmass.le]
  ring

/-- The integrals of the absolute Mellin terms form a convergent series. -/
private theorem summable_integral_norm_scalarMellinTerm
    (ρ σ : D4BMUpperHalfPlaneCoordinate) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun q => ∫ y in Set.Ioi (0 : ℝ), ‖scalarMellinTerm ρ σ s q y‖) := by
  exact ((summable_narainDirichletTerm ρ σ hs).norm.mul_left
    (Real.Gamma s.re * Real.pi ^ (-s.re))).congr
      (fun q => (integral_norm_scalarMellinTerm ρ σ (by linarith only [hs]) q).symm)

/-- The Mellin transform is taken from the literal nonvacuum scalar heat sum. -/
theorem mellin_narainScalarHeat (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (narainScalarHeat ρ σ) s =
      (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        (∑' q, narainDirichletTerm ρ σ s q) := by
  have hs0 : 0 < s.re := by linarith only [hs]
  have hint := integrable_scalarMellinTerm ρ σ hs0
  have hsum := summable_integral_norm_scalarMellinTerm ρ σ hs
  change (∫ y in Set.Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) • narainScalarHeat ρ σ y) = _
  simp only [smul_eq_mul, narainScalarHeat, ← tsum_mul_left]
  change (∫ y in Set.Ioi (0 : ℝ), ∑' q, scalarMellinTerm ρ σ s q y) = _
  rw [integral_tsum_eq_tsum_integral_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun q y => scalarMellinTerm ρ σ s q y) hint hsum]
  simp only [integral_scalarMellinTerm ρ σ hs0, tsum_mul_left]

/-- The scalar heat Mellin transform has the exact two-modulus Eisenstein normalization. -/
theorem mellin_narainScalarHeat_eq_eisenstein_product
    (ρ σ : D4BMUpperHalfPlaneCoordinate) {s : ℂ} (hs : 1 < s.re) :
    mellin (narainScalarHeat ρ σ) s =
      2 * ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s * riemannZeta (2 * s)) *
        d4BMRawEisensteinPoincareSeries ρ ⟨s, hs⟩ *
          d4BMRawEisensteinPoincareSeries σ ⟨s, hs⟩ := by
  rw [mellin_narainScalarHeat ρ σ hs, narainDirichlet_eq_eisenstein_product ρ σ hs]
  ring

/-- The unit-interval projection of the actual partition function has this
Mellin transform after division by height and subtraction of the vacuum. -/
theorem mellin_narainScalarProjection (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (fun y : ℝ =>
      (∫ x in Set.Ioc (0 : ℝ) 1, narainPartition ρ σ x y) / (y : ℂ) - 1) s =
      2 * ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s * riemannZeta (2 * s)) *
        d4BMRawEisensteinPoincareSeries ρ ⟨s, hs⟩ *
          d4BMRawEisensteinPoincareSeries σ ⟨s, hs⟩ := by
  rw [← mellin_narainScalarHeat_eq_eisenstein_product ρ σ hs]
  simp only [mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy)
  rw [integral_narainPartition_eq_scalar ρ σ hy, narainScalarPartition_eq_heat ρ σ hy]
  apply congrArg (fun z : ℂ => (y : ℂ) ^ (s - 1) • z)
  field_simp [hy0] <;> ring

end

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.mellin_narainScalarHeat
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.mellin_narainScalarHeat_eq_eisenstein_product
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narainScalarPartition_eq_heat
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.mellin_narainScalarProjection
