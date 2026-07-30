import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.XiHurwitzConstraintOrientation

/-!
# The Xi--Hurwitz scalar orientation energy

The Hurwitz monodromy character turns the horizontal position of every actual Xi zero into a
bounded orientation defect.  Weighting that defect by the positive divisor multiplicity and the
canonical centered reciprocal-square coordinate gives an absolutely convergent nonnegative real
number.  Its vanishing is equivalent to RH.

Thus the pointwise negative-character chamber has a single faithful scalar certificate.  The same
Xi-indexed family remains unconditionally differentially independent, so this scalar couples the
constraint and orientation axes without changing the differential relation lattice.
-/

open Complex Set Function MeromorphicOn
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit

/-- The squared, radius-normalized imaginary part of the Xi-zero Hurwitz character. -/
def xiHurwitzOrientationDefect (ρ : XiDivisorSupport) : ℝ :=
  (xiHurwitzMonodromyCharacter ρ).im ^ 2 /
    ‖xiHurwitzMonodromyCharacter ρ‖ ^ 2

theorem xiHurwitzMonodromyCharacter_ne_zero (ρ : XiDivisorSupport) :
    xiHurwitzMonodromyCharacter ρ ≠ 0 := by
  exact monoScalar_ne_zero (ρ : ℂ)

/-- The orientation defect is literally the squared sine of the horizontal zero angle. -/
theorem xiHurwitzOrientationDefect_eq_sin_sq (ρ : XiDivisorSupport) :
    xiHurwitzOrientationDefect ρ =
      Real.sin (2 * Real.pi * (ρ : ℂ).re) ^ 2 := by
  have hre : (-(2 * (Real.pi : ℂ) * I * (ρ : ℂ))).re =
      2 * Real.pi * (ρ : ℂ).im := by
    simp
  have him : (-(2 * (Real.pi : ℂ) * I * (ρ : ℂ))).im =
      -(2 * Real.pi * (ρ : ℂ).re) := by
    simp
  rw [xiHurwitzOrientationDefect, xiHurwitzMonodromyCharacter, monoScalar,
    Complex.exp_im, Complex.norm_exp, hre, him, Real.sin_neg]
  field_simp [ne_of_gt (Real.exp_pos (2 * Real.pi * (ρ : ℂ).im))]

theorem xiHurwitzOrientationDefect_nonneg (ρ : XiDivisorSupport) :
    0 ≤ xiHurwitzOrientationDefect ρ := by
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem xiHurwitzOrientationDefect_le_one (ρ : XiDivisorSupport) :
    xiHurwitzOrientationDefect ρ ≤ 1 := by
  let q := xiHurwitzMonodromyCharacter ρ
  have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr (xiHurwitzMonodromyCharacter_ne_zero ρ)
  have himnorm : |q.im| ≤ ‖q‖ := Complex.abs_im_le_norm q
  have hprod : 0 ≤ (‖q‖ - |q.im|) * (‖q‖ + |q.im|) :=
    mul_nonneg (sub_nonneg.mpr himnorm)
      (add_nonneg (norm_nonneg q) (abs_nonneg q.im))
  rw [xiHurwitzOrientationDefect]
  apply (div_le_iff₀ (sq_pos_of_pos hqnorm)).2
  dsimp [q] at himnorm hprod hqnorm ⊢
  nlinarith [sq_abs (xiHurwitzMonodromyCharacter ρ).im]

theorem xiHurwitzOrientationDefect_eq_zero_iff (ρ : XiDivisorSupport) :
    xiHurwitzOrientationDefect ρ = 0 ↔
      (xiHurwitzMonodromyCharacter ρ).im = 0 := by
  constructor
  · intro hzero
    rcases (div_eq_zero_iff.mp hzero) with hnum | hden
    · nlinarith
    · have hnorm : ‖xiHurwitzMonodromyCharacter ρ‖ = 0 := by
        nlinarith [norm_nonneg (xiHurwitzMonodromyCharacter ρ)]
      exact False.elim
        (xiHurwitzMonodromyCharacter_ne_zero ρ (norm_eq_zero.mp hnorm))
  · intro him
    simp [xiHurwitzOrientationDefect, him]

/-- The Hurwitz-character orientation and the centered reciprocal-square spectral orientation
have exactly the same zero locus on the actual Xi divisor. -/
theorem xiHurwitzOrientationDefect_eq_zero_iff_centralSpectrum_real
    (ρ : XiDivisorSupport) :
    xiHurwitzOrientationDefect ρ = 0 ↔
      (xiCentralReciprocalSquare (ρ : ℂ)).im = 0 := by
  rw [xiHurwitzOrientationDefect_eq_zero_iff,
    xiCentralReciprocalSquare_im_eq_zero_iff]
  change (monoScalar (ρ : ℂ)).im = 0 ↔ (ρ : ℂ).re = 1 / 2
  exact Complex.conj_eq_iff_im.symm.trans
    (openCriticalStrip_monoScalar_conj_fixed_iff
      (xi_divisor_support_re_mem_open_unit ρ))

theorem xiHurwitzOrientationDefect_eq_zero_iff_re_eq_half
    (ρ : XiDivisorSupport) :
    xiHurwitzOrientationDefect ρ = 0 ↔ (ρ : ℂ).re = 1 / 2 :=
  (xiHurwitzOrientationDefect_eq_zero_iff_centralSpectrum_real ρ).trans
    (xiCentralReciprocalSquare_im_eq_zero_iff ρ)

theorem xiHurwitzOrientationDefect_pos_iff_re_ne_half
    (ρ : XiDivisorSupport) :
    0 < xiHurwitzOrientationDefect ρ ↔ (ρ : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro hpos hre
    have hzero :=
      (xiHurwitzOrientationDefect_eq_zero_iff_re_eq_half ρ).mpr hre
    linarith
  · intro hne
    apply lt_of_le_of_ne (xiHurwitzOrientationDefect_nonneg ρ)
    intro hzero
    apply hne
    exact (xiHurwitzOrientationDefect_eq_zero_iff_re_eq_half ρ).mp hzero.symm

/-- The positive canonical trace-class weight: Xi multiplicity divided by centered squared
distance from the functional-equation fixed point. -/
def xiHurwitzOrientationWeight (ρ : XiDivisorSupport) : ℝ :=
  ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) /
    ‖(ρ : ℂ) - 1 / 2‖ ^ 2

theorem xiHurwitzOrientationWeight_pos (ρ : XiDivisorSupport) :
    0 < xiHurwitzOrientationWeight ρ := by
  have hmult : (0 : ℝ) < ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    exact_mod_cast xi_divisor_pos_on_support ρ
  have hcenter : 0 < ‖(ρ : ℂ) - 1 / 2‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (xi_divisor_support_ne_half ρ))
  exact div_pos hmult (sq_pos_of_pos hcenter)

theorem xiHurwitzOrientationWeight_summable :
    Summable xiHurwitzOrientationWeight := by
  simpa only [xiHurwitzOrientationWeight] using!
    xi_zero_multiplicity_centered_inv_sq_summable

/-- The nonnegative contribution of one Xi zero, with its exact divisor multiplicity retained. -/
def xiHurwitzOrientationEnergyTerm (ρ : XiDivisorSupport) : ℝ :=
  xiHurwitzOrientationWeight ρ * xiHurwitzOrientationDefect ρ

theorem xiHurwitzOrientationEnergyTerm_nonneg (ρ : XiDivisorSupport) :
    0 ≤ xiHurwitzOrientationEnergyTerm ρ := by
  exact mul_nonneg (le_of_lt (xiHurwitzOrientationWeight_pos ρ))
    (xiHurwitzOrientationDefect_nonneg ρ)

theorem xiHurwitzOrientationEnergyTerm_le_weight (ρ : XiDivisorSupport) :
    xiHurwitzOrientationEnergyTerm ρ ≤ xiHurwitzOrientationWeight ρ := by
  calc
    xiHurwitzOrientationEnergyTerm ρ =
        xiHurwitzOrientationWeight ρ * xiHurwitzOrientationDefect ρ := rfl
    _ ≤ xiHurwitzOrientationWeight ρ * 1 :=
      mul_le_mul_of_nonneg_left (xiHurwitzOrientationDefect_le_one ρ)
        (le_of_lt (xiHurwitzOrientationWeight_pos ρ))
    _ = xiHurwitzOrientationWeight ρ := mul_one _

theorem xiHurwitzOrientationEnergyTerm_summable :
    Summable xiHurwitzOrientationEnergyTerm :=
  Summable.of_nonneg_of_le xiHurwitzOrientationEnergyTerm_nonneg
    xiHurwitzOrientationEnergyTerm_le_weight xiHurwitzOrientationWeight_summable

/-- The canonical scalar orientation energy of the actual Xi divisor. -/
def xiHurwitzOrientationEnergy : ℝ :=
  ∑' ρ : XiDivisorSupport, xiHurwitzOrientationEnergyTerm ρ

/-- Exact divisor-value expansion of the scalar energy. -/
theorem xiHurwitzOrientationEnergy_eq_tsum_sin_sq :
    xiHurwitzOrientationEnergy =
      ∑' ρ : XiDivisorSupport,
        xiHurwitzOrientationWeight ρ *
          Real.sin (2 * Real.pi * (ρ : ℂ).re) ^ 2 := by
  rw [xiHurwitzOrientationEnergy]
  apply tsum_congr
  intro ρ
  rw [xiHurwitzOrientationEnergyTerm, xiHurwitzOrientationDefect_eq_sin_sq]

theorem xiHurwitzOrientationEnergy_nonneg :
    0 ≤ xiHurwitzOrientationEnergy := by
  exact tsum_nonneg xiHurwitzOrientationEnergyTerm_nonneg

theorem xiHurwitzOrientationEnergyTerm_le_energy (ρ : XiDivisorSupport) :
    xiHurwitzOrientationEnergyTerm ρ ≤ xiHurwitzOrientationEnergy := by
  classical
  have hle := xiHurwitzOrientationEnergyTerm_summable.sum_le_tsum {ρ}
    (fun τ _ => xiHurwitzOrientationEnergyTerm_nonneg τ)
  simpa only [Finset.sum_singleton, xiHurwitzOrientationEnergy] using hle

theorem xiHurwitzOrientationEnergy_eq_zero_iff_terms :
    xiHurwitzOrientationEnergy = 0 ↔
      ∀ ρ : XiDivisorSupport, xiHurwitzOrientationEnergyTerm ρ = 0 := by
  constructor
  · intro henergy ρ
    apply le_antisymm
    · simpa only [henergy] using xiHurwitzOrientationEnergyTerm_le_energy ρ
    · exact xiHurwitzOrientationEnergyTerm_nonneg ρ
  · intro hterm
    simp only [xiHurwitzOrientationEnergy, hterm, tsum_zero]

theorem xiHurwitzOrientationEnergyTerm_eq_zero_iff (ρ : XiDivisorSupport) :
    xiHurwitzOrientationEnergyTerm ρ = 0 ↔
      xiHurwitzOrientationDefect ρ = 0 := by
  rw [xiHurwitzOrientationEnergyTerm, mul_eq_zero]
  simp only [ne_of_gt (xiHurwitzOrientationWeight_pos ρ), false_or]

theorem xiHurwitzOrientationEnergy_eq_zero_iff_character_real :
    xiHurwitzOrientationEnergy = 0 ↔
      ∀ ρ : XiDivisorSupport, (xiHurwitzMonodromyCharacter ρ).im = 0 := by
  rw [xiHurwitzOrientationEnergy_eq_zero_iff_terms]
  exact forall_congr' fun ρ =>
    (xiHurwitzOrientationEnergyTerm_eq_zero_iff ρ).trans
      (xiHurwitzOrientationDefect_eq_zero_iff ρ)

/-- Vanishing of the scalar energy is exactly reality of the complete centered reciprocal-square
Xi spectrum used by the trace/Hankel criteria. -/
theorem xiHurwitzOrientationEnergy_eq_zero_iff_centralSpectrum_real :
    xiHurwitzOrientationEnergy = 0 ↔
      ∀ ρ : XiDivisorSupport,
        (xiCentralReciprocalSquare (ρ : ℂ)).im = 0 := by
  rw [xiHurwitzOrientationEnergy_eq_zero_iff_terms]
  exact forall_congr' fun ρ =>
    (xiHurwitzOrientationEnergyTerm_eq_zero_iff ρ).trans
      (xiHurwitzOrientationDefect_eq_zero_iff_centralSpectrum_real ρ)

/-- **Scalar RH orientation law.**  RH is equivalent to vanishing of one canonical, nonnegative,
absolutely convergent, multiplicity-sensitive scalar attached to the actual Xi divisor. -/
theorem riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero :
    RiemannHypothesis ↔ xiHurwitzOrientationEnergy = 0 := by
  constructor
  · intro hRH
    apply xiHurwitzOrientationEnergy_eq_zero_iff_character_real.mpr
    intro ρ
    exact Complex.conj_eq_iff_im.mp
      ((openCriticalStrip_monoScalar_conj_fixed_iff
        (xi_divisor_support_re_mem_open_unit ρ)).mpr
          (xi_divisor_support_re_eq_half_of_rh hRH ρ))
  · intro henergy
    have hreal := xiHurwitzOrientationEnergy_eq_zero_iff_character_real.mp henergy
    apply riemannHypothesis_iff_xiHurwitzNegativeCharacterChamber.mpr
    intro ρ
    have hre : (ρ : ℂ).re = 1 / 2 :=
      (openCriticalStrip_monoScalar_conj_fixed_iff
        (xi_divisor_support_re_mem_open_unit ρ)).mp
          (Complex.conj_eq_iff_im.mpr (hreal ρ))
    exact (openCriticalStrip_monoScalar_negativeReal_iff
      (xi_divisor_support_re_mem_open_unit ρ)).mpr hre

/-- The positive-energy chamber is exactly failure of RH.  This is the positive form of the
off-critical-line obstruction. -/
theorem xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis :
    0 < xiHurwitzOrientationEnergy ↔ ¬RiemannHypothesis := by
  constructor
  · intro hpos hRH
    have hzero :=
      riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mp hRH
    linarith
  · intro hnot
    apply lt_of_le_of_ne xiHurwitzOrientationEnergy_nonneg
    intro hzero
    apply hnot
    exact riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mpr hzero.symm

/-- Positive energy is equivalent to a concrete off-critical-line Xi-divisor witness. -/
theorem xiHurwitzOrientationEnergy_pos_iff_exists_offCriticalZero :
    0 < xiHurwitzOrientationEnergy ↔
      ∃ ρ : XiDivisorSupport, (ρ : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro henergy
    by_contra hnone
    push Not at hnone
    have hRH : RiemannHypothesis := by
      apply riemannHypothesis_iff_xiHurwitzNegativeCharacterChamber.mpr
      intro ρ
      exact (openCriticalStrip_monoScalar_negativeReal_iff
        (xi_divisor_support_re_mem_open_unit ρ)).mpr (hnone ρ)
    have hzero :=
      riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mp hRH
    linarith
  · rintro ⟨ρ, hρ⟩
    have hterm : 0 < xiHurwitzOrientationEnergyTerm ρ :=
      mul_pos (xiHurwitzOrientationWeight_pos ρ)
        ((xiHurwitzOrientationDefect_pos_iff_re_ne_half ρ).mpr hρ)
    exact lt_of_lt_of_le hterm (xiHurwitzOrientationEnergyTerm_le_energy ρ)

/-- Any single zero contributes an explicit lower bound to the global orientation energy. -/
theorem xiHurwitzOrientationWitness_le_energy (ρ : XiDivisorSupport) :
    xiHurwitzOrientationWeight ρ *
        Real.sin (2 * Real.pi * (ρ : ℂ).re) ^ 2 ≤
      xiHurwitzOrientationEnergy := by
  rw [← xiHurwitzOrientationDefect_eq_sin_sq,
    ← xiHurwitzOrientationEnergyTerm]
  exact xiHurwitzOrientationEnergyTerm_le_energy ρ

/-- **Xi--Hurwitz scalar constraint-orientation product law.**  The full Xi-indexed continued
Hurwitz family is unconditionally differentially free, while RH is exactly the zero-energy locus of
its canonical trace-class orientation coupling. -/
theorem xi_hurwitz_scalar_constraint_orientation_product_law :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
        (fun ρ : XiDivisorSupport => continuedHzetaUpperEndMero (ρ : ℂ)) ∧
      0 ≤ xiHurwitzOrientationEnergy ∧
      (RiemannHypothesis ↔ xiHurwitzOrientationEnergy = 0) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact ⟨xi_zero_hurwitz_differentialIndependent_all,
    xiHurwitzOrientationEnergy_nonneg,
    riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero⟩

end

end RHTower
