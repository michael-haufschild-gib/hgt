import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainDirichlet
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPartition
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-!
# The actual scalar Narain heat sum has the Eisenstein-product Mellin transform

Each nonvacuum charge has positive mass. Its Mellin integral is the scaled
Gamma integral, and the integral of its norm is a constant times its mass
Dirichlet term at the real part of the exponent. Absolute Dirichlet
convergence therefore justifies the full charge-sum interchange.
-/

open Complex RHTower MeasureTheory

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

/-- The Mellin transform is taken from the literal nonvacuum scalar heat sum. -/
theorem mellin_narainScalarHeat (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (narainScalarHeat ρ σ) s =
      (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        (∑' q, narainDirichletTerm ρ σ s q) := by
  have hmass (q : NonzeroScalarCharge) : 0 < narainMassSq ρ σ q.val :=
    narainMassSq_pos ρ σ q.property.2
  have hF : ∀ y ∈ Set.Ioi (0 : ℝ),
      HasSum (fun q : NonzeroScalarCharge =>
        (1 : ℂ) * (Real.exp (-Real.pi * narainMassSq ρ σ q.val * y) : ℂ))
          (narainScalarHeat ρ σ y) := by
    intro y hy
    refine (summable_narainScalarHeatTerm ρ σ hy).hasSum.congr_fun fun q => ?_
    rw [one_mul, narainBoltzmann]
    congr 2
    ring
  have hsum : Summable (fun q : NonzeroScalarCharge =>
      ‖(1 : ℂ)‖ / narainMassSq ρ σ q.val ^ s.re) := by
    refine (summable_narainDirichletTerm ρ σ hs).norm.congr fun q => ?_
    rw [narainDirichletTerm, Complex.norm_cpow_eq_rpow_re_of_pos (hmass q),
      Complex.neg_re, norm_one, Real.rpow_neg (hmass q).le, one_div]
  have hM := hasSum_mellin_pi_mul
    (a := fun _ : NonzeroScalarCharge => (1 : ℂ))
    (q := fun q : NonzeroScalarCharge => narainMassSq ρ σ q.val)
    (F := narainScalarHeat ρ σ) (s := s)
    (fun q => Or.inr (hmass q)) (by linarith only [hs]) hF hsum
  have hval : HasSum (fun q => ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s) *
      narainDirichletTerm ρ σ s q) (mellin (narainScalarHeat ρ σ) s) :=
    hM.congr_fun (fun q => by
      simp only [mul_one, narainDirichletTerm, Complex.cpow_neg, div_eq_mul_inv])
  exact hval.tsum_eq.symm.trans (tsum_mul_left)

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
  dsimp only
  rw [integral_narainPartition_eq_scalar ρ σ hy, narainScalarPartition_eq_heat ρ σ hy]
  apply congrArg (fun z : ℂ => (y : ℂ) ^ (s - 1) • z)
  field_simp [hy0]
  ring

end

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.mellin_narainScalarHeat
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.mellin_narainScalarHeat_eq_eisenstein_product
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narainScalarPartition_eq_heat
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.mellin_narainScalarProjection
