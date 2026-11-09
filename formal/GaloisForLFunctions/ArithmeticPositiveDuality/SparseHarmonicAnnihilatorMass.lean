import GaloisForLFunctions.ArithmeticPositiveDuality.HarmonicZeroPacketsForcePositiveAnnihilatorMass
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# The mass cost of the first and fourth harmonics

A positive trigonometric certificate supported at frequencies one and four forces a
bandwidth-independent mass cost. Its factorization also identifies every extremal phase.
-/

noncomputable section
set_option autoImplicit false

open Complex Finset
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

/-- The sharp mass cost of cancelling the first and fourth harmonics. -/
def sparseHarmonicMassConstant : ℝ := 2 / Real.goldenRatio

theorem sparseHarmonicMassConstant_eq : sparseHarmonicMassConstant = Real.sqrt 5 - 1 := by
  rw [sparseHarmonicMassConstant, div_eq_mul_inv, Real.inv_goldenRatio]
  unfold Real.goldenConj
  ring

theorem sparseHarmonicMassConstant_pos : 0 < sparseHarmonicMassConstant :=
  div_pos (by norm_num) Real.goldenRatio_pos

/-- The nonnegative certificate using only the two selected harmonics. -/
def sparseHarmonicCertificate (θ : ℝ) : ℝ :=
  5 * Real.goldenRatio / 2 + 4 * Real.cos θ + Real.cos (4 * θ)

private theorem golden_quartic_factor (p x : ℝ) (hp : p ^ 2 = p + 1) :
    8 * x ^ 4 - 8 * x ^ 2 + 4 * x + 1 + 5 * p / 2 =
      8 * (x + p / 2) ^ 2 * ((x - p / 2) ^ 2 + (p - 1) / 2) := by
  have hp3 : p ^ 3 = 2 * p + 1 := by
    calc p ^ 3 = p * p ^ 2 := by ring
      _ = _ := by rw [hp]; nlinarith only [hp]
  have hp4 : p ^ 4 = 3 * p + 2 := by
    calc p ^ 4 = (p ^ 2) ^ 2 := by ring
      _ = _ := by rw [hp]; nlinarith only [hp]
  ring_nf
  simp only [hp, hp3, hp4]
  ring

theorem sparseHarmonicCertificate_factor (θ : ℝ) :
    sparseHarmonicCertificate θ =
      8 * (Real.cos θ + Real.goldenRatio / 2) ^ 2 *
        ((Real.cos θ - Real.goldenRatio / 2) ^ 2 + (Real.goldenRatio - 1) / 2) := by
  have hc : Real.cos (4 * θ) = 8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1 := by
    rw [show 4 * θ = 2 * (2 * θ) by ring, Real.cos_two_mul, Real.cos_two_mul]
    ring
  rw [sparseHarmonicCertificate, hc]
  convert golden_quartic_factor Real.goldenRatio (Real.cos θ) Real.goldenRatio_sq using 1
  ring

theorem sparseHarmonicCertificate_nonneg (θ : ℝ) : 0 ≤ sparseHarmonicCertificate θ := by
  rw [sparseHarmonicCertificate_factor]
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (add_nonneg (sq_nonneg _) (half_pos (sub_pos.mpr Real.one_lt_goldenRatio)).le)

theorem sparseHarmonicCertificate_eq_zero_iff (θ : ℝ) :
    sparseHarmonicCertificate θ = 0 ↔ Real.cos θ = -Real.goldenRatio / 2 := by
  rw [sparseHarmonicCertificate_factor]
  have hp : 0 < (Real.cos θ - Real.goldenRatio / 2) ^ 2 +
      (Real.goldenRatio - 1) / 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (half_pos (sub_pos.mpr Real.one_lt_goldenRatio))
  rw [mul_eq_zero, or_iff_left hp.ne', mul_eq_zero,
    or_iff_right (by norm_num : (8 : ℝ) ≠ 0), sq_eq_zero_iff]
  constructor <;> intro h <;> linarith only [h]

private theorem harmonic_eval_re {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (β γ : ℝ) (k : ℕ) :
    (dirichletEval (harmonicPacketPoint β γ k) P).re = 1 +
      ∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) *
        Real.exp (-monomialLog d * β) * Real.cos ((k : ℝ) * (monomialLog d * γ)) := by
  rw [dirichletEval_eq_one_add_tail hP, Complex.add_re, Complex.one_re]
  congr 1
  change Complex.reAddGroupHom (∑ d ∈ P.support.erase 0,
    (((P.coeff d : ℝ≥0) : ℝ) : ℂ) *
      Complex.exp (-(monomialLog d : ℂ) * harmonicPacketPoint β γ k)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  simp only [harmonicPacketPoint, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_re, Complex.neg_re, Complex.neg_im, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im,
    Complex.I_re, Complex.I_im, mul_zero, add_zero, zero_add, mul_one, neg_zero,
    neg_mul, Real.cos_neg]
  rw [mul_assoc]
  congr 2
  ring

/-- The exact positive energy measuring joint cancellation at the sparse harmonic pair. -/
theorem sparseHarmonic_mass_energy {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (β γ : ℝ) :
    (∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) *
      Real.exp (-monomialLog d * β) * sparseHarmonicCertificate (monomialLog d * γ)) =
      (5 * Real.goldenRatio / 2) * dirichletTailMass P β +
        4 * (dirichletEval (harmonicPacketPoint β γ 1) P).re +
        (dirichletEval (harmonicPacketPoint β γ 4) P).re - 5 := by
  rw [harmonic_eval_re hP, harmonic_eval_re hP]
  simp only [Nat.cast_one, Nat.cast_ofNat, one_mul]
  have hs : (∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) *
      Real.exp (-monomialLog d * β) * sparseHarmonicCertificate (monomialLog d * γ)) =
      ∑ d ∈ P.support.erase 0,
        (5 * Real.goldenRatio / 2) * (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β)) +
        4 * (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β) *
          Real.cos (monomialLog d * γ)) +
        ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β) *
          Real.cos (4 * (monomialLog d * γ)) := by
    apply Finset.sum_congr rfl
    intro d _
    unfold sparseHarmonicCertificate
    ring
  rw [hs]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, dirichletTailMass]
  ring

private theorem certificate_mass_nonneg (P : MvPolynomial (Fin 2) ℝ≥0) (β γ : ℝ) :
    0 ≤ ∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) *
      Real.exp (-monomialLog d * β) * sparseHarmonicCertificate (monomialLog d * γ) :=
  Finset.sum_nonneg fun d _ => mul_nonneg
    (mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le)
    (sparseHarmonicCertificate_nonneg _)

private theorem certificate_constant_mul :
    (5 * Real.goldenRatio / 2) * sparseHarmonicMassConstant = 5 := by
  unfold sparseHarmonicMassConstant
  field_simp [Real.goldenRatio_ne_zero]

/-- Positive coefficient mass bounds the two real evaluations jointly, without a bandwidth
or zero assumption. -/
theorem sparseHarmonic_joint_evaluation_bound {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (β γ : ℝ) :
    5 - 4 * (dirichletEval (harmonicPacketPoint β γ 1) P).re -
        (dirichletEval (harmonicPacketPoint β γ 4) P).re ≤
      (5 * Real.goldenRatio / 2) * dirichletTailMass P β := by
  have h := certificate_mass_nonneg P β γ
  rw [sparseHarmonic_mass_energy hP β γ] at h
  linarith only [h]

/-- Simultaneous accuracy at the first and fourth harmonics has a sharp golden-ratio cost. -/
theorem sparseHarmonic_accuracy_mass_bound {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (β γ ε : ℝ)
    (h1 : ‖dirichletEval (harmonicPacketPoint β γ 1) P‖ ≤ ε)
    (h4 : ‖dirichletEval (harmonicPacketPoint β γ 4) P‖ ≤ ε) :
    sparseHarmonicMassConstant * (1 - ε) ≤ dirichletTailMass P β := by
  have hr1 := (Complex.re_le_norm _).trans h1
  have hr4 := (Complex.re_le_norm _).trans h4
  have h := sparseHarmonic_joint_evaluation_bound hP β γ
  have hA : 0 < 5 * Real.goldenRatio / 2 := by positivity
  apply (mul_le_mul_left hA).mp
  rw [← mul_assoc, certificate_constant_mul]
  linarith only [h, hr1, hr4]

/-- At exact cancellation, minimal mass is equivalent to concentration on the two extremal
fifth-root phases. -/
theorem sparseHarmonic_mass_eq_iff {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (β γ : ℝ)
    (h1 : dirichletEval (harmonicPacketPoint β γ 1) P = 0)
    (h4 : dirichletEval (harmonicPacketPoint β γ 4) P = 0) :
    dirichletTailMass P β = sparseHarmonicMassConstant ↔
      ∀ d ∈ P.support.erase 0, Real.cos (monomialLog d * γ) = -Real.goldenRatio / 2 := by
  have he := sparseHarmonic_mass_energy hP β γ
  rw [h1, h4, Complex.zero_re, mul_zero, add_zero, add_zero] at he
  have hw (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support.erase 0) :
      0 < ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β) := by
    refine mul_pos ?_ (Real.exp_pos _)
    have hn := MvPolynomial.mem_support_iff.mp (Finset.mem_of_mem_erase hd)
    exact_mod_cast (pos_iff_ne_zero.mpr hn : 0 < P.coeff d)
  constructor
  · intro hm
    rw [hm, certificate_constant_mul, sub_self] at he
    intro d hd
    have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun d hd =>
      mul_nonneg (hw d hd).le (sparseHarmonicCertificate_nonneg _))).mp he d hd
    exact (sparseHarmonicCertificate_eq_zero_iff _).mp
      ((mul_eq_zero.mp ht).resolve_left (hw d hd).ne')
  · intro hp
    have hz : (∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) *
        Real.exp (-monomialLog d * β) * sparseHarmonicCertificate (monomialLog d * γ)) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [(sparseHarmonicCertificate_eq_zero_iff _).mpr (hp d hd), mul_zero]
    rw [hz] at he
    have hA : 0 < 5 * Real.goldenRatio / 2 := by positivity
    apply mul_left_cancel₀ hA.ne'
    linarith only [he, certificate_constant_mul]

#print axioms sparseHarmonic_mass_energy
#print axioms sparseHarmonic_accuracy_mass_bound
#print axioms sparseHarmonic_mass_eq_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
