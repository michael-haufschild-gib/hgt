import GaloisForLFunctions.ArithmeticPositiveDuality.TheUnitMassBoundaryOfPositiveAnnihilators
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Arbitrary multiplicity near unit annihilator mass

Integrating `(1 + X^K)^r` for odd `K` gives a positive polynomial whose
normalized translate has a zero of order `r+1` at minus one. As `K` grows,
its nonconstant mass tends to one. Substitution of `2^(β-s)` preserves the
zero order and gives literal positive one-prime Dirichlet polynomials.
-/

noncomputable section
set_option autoImplicit false

open Complex Finset Filter Topology
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

/-- The positive coefficients of the primitive of `(1 + X^(2n+1))^r`. -/
def multiplicityPrimitiveCoefficient (r n j : ℕ) : ℝ≥0 :=
  (r.choose j : ℝ≥0) / ((1 + j * (2 * n + 1) : ℕ) : ℝ≥0)

/-- The normalization that places a zero at minus one. -/
def multiplicityPrimitiveNormalizer (r n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), (-1 : ℝ) ^ j *
    ((multiplicityPrimitiveCoefficient r n j : ℝ≥0) : ℝ)

/-- The unnormalized nonconstant mass at one. -/
def multiplicityPrimitiveMass (r n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), ((multiplicityPrimitiveCoefficient r n j : ℝ≥0) : ℝ)

/-- A positive Dirichlet polynomial built from an odd-power primitive. -/
def arbitraryMultiplicityAnnihilator (β : ℝ) (r n : ℕ) : MvPolynomial (Fin 2) ℝ≥0 :=
  1 + MvPolynomial.C ((Real.toNNReal (multiplicityPrimitiveNormalizer r n))⁻¹) *
    ∑ j ∈ Finset.range (r + 1), MvPolynomial.C (multiplicityPrimitiveCoefficient r n j) *
      scaledTwoMonomial β ^ (1 + j * (2 * n + 1))

theorem coe_multiplicityPrimitiveCoefficient (r n j : ℕ) :
    ((multiplicityPrimitiveCoefficient r n j : ℝ≥0) : ℝ) =
      (r.choose j : ℝ) / (1 + (j : ℝ) * (2 * (n : ℝ) + 1)) := by
  simp [multiplicityPrimitiveCoefficient]

/-- The alternating coefficient sum is the integral of a nonnegative polynomial. -/
theorem multiplicityPrimitiveNormalizer_eq_integral (r n : ℕ) :
    multiplicityPrimitiveNormalizer r n =
      ∫ t : ℝ in 0..1, (1 - t ^ (2 * n + 1)) ^ r := by
  unfold multiplicityPrimitiveNormalizer
  simp_rw [coe_multiplicityPrimitiveCoefficient]
  have hex (t : ℝ) : (1 - t ^ (2 * n + 1)) ^ r =
      ∑ j ∈ range (r + 1), ((-1 : ℝ) ^ j * (r.choose j : ℝ)) *
        t ^ (j * (2 * n + 1)) := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    rw [one_pow, mul_one, show -t ^ (2 * n + 1) = (-1 : ℝ) * t ^ (2 * n + 1) by ring,
      mul_pow, ← pow_mul, Nat.mul_comm (2 * n + 1) j]
    ring
  symm
  simp_rw [hex]
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    (by fun_prop : Continuous (fun t : ℝ => ((-1 : ℝ) ^ j * (r.choose j : ℝ)) *
      t ^ (j * (2 * n + 1)))).intervalIntegrable 0 1)]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
  push_cast
  ring

theorem multiplicityPrimitiveNormalizer_pos (r n : ℕ) :
    0 < multiplicityPrimitiveNormalizer r n := by
  rw [multiplicityPrimitiveNormalizer_eq_integral]
  apply intervalIntegral.integral_pos (by norm_num) (by fun_prop)
  · intro t ht
    exact pow_nonneg (sub_nonneg.mpr (pow_le_one₀ ht.1.le ht.2)) r
  · exact ⟨0, by norm_num, by simp⟩

theorem arbitraryMultiplicityAnnihilator_constantCoeff (β : ℝ) (r n : ℕ) :
    MvPolynomial.constantCoeff (arbitraryMultiplicityAnnihilator β r n) = 1 := by
  simp [arbitraryMultiplicityAnnihilator, scaledTwoMonomial, pow_add]

theorem dirichletEval_arbitraryMultiplicityAnnihilator (β : ℝ) (r n : ℕ) (s : ℂ) :
    dirichletEval s (arbitraryMultiplicityAnnihilator β r n) =
      1 + ((multiplicityPrimitiveNormalizer r n : ℂ)⁻¹) *
        ∑ j ∈ Finset.range (r + 1),
          (((multiplicityPrimitiveCoefficient r n j : ℝ≥0) : ℝ) : ℂ) *
            dirichletEval s (scaledTwoMonomial β) ^ (1 + j * (2 * n + 1)) := by
  simp only [arbitraryMultiplicityAnnihilator, map_add, map_one, map_mul, map_sum, map_pow]
  have hC (a : ℝ≥0) : dirichletEval s (MvPolynomial.C a) = (((a : ℝ≥0) : ℝ) : ℂ) := by
    simp [dirichletEval]
  simp only [hC]
  congr 2
  simp [(multiplicityPrimitiveNormalizer_pos r n).le]

@[simp] theorem multiplicityPrimitiveCoefficient_zero (r n : ℕ) :
    multiplicityPrimitiveCoefficient r n 0 = 1 := by
  simp [multiplicityPrimitiveCoefficient]

private theorem multiplicityPrimitiveMass_split (r n : ℕ) :
    multiplicityPrimitiveMass r n = 1 + ∑ j ∈ Finset.range r,
      ((multiplicityPrimitiveCoefficient r n (j + 1) : ℝ≥0) : ℝ) := by
  rw [multiplicityPrimitiveMass, Finset.sum_range_succ']
  simp only [multiplicityPrimitiveCoefficient_zero, NNReal.coe_one]
  ring

private theorem multiplicityPrimitiveNormalizer_split (r n : ℕ) :
    multiplicityPrimitiveNormalizer r n = 1 + ∑ j ∈ Finset.range r,
      (-1 : ℝ) ^ (j + 1) *
        ((multiplicityPrimitiveCoefficient r n (j + 1) : ℝ≥0) : ℝ) := by
  rw [multiplicityPrimitiveNormalizer, Finset.sum_range_succ']
  simp only [pow_zero, multiplicityPrimitiveCoefficient_zero, NNReal.coe_one, one_mul]
  ring

/-- All coefficients beyond the linear term have a uniform reciprocal-degree bound. -/
theorem multiplicityPrimitiveMass_sub_one_le (r n : ℕ) :
    multiplicityPrimitiveMass r n - 1 ≤ ((2 : ℝ) ^ r - 1) / (2 * (n : ℝ) + 2) := by
  have hchoose : (∑ j ∈ Finset.range r, (r.choose (j + 1) : ℝ)) = 2 ^ r - 1 := by
    have h := Nat.sum_range_choose r
    rw [Finset.sum_range_succ', Nat.choose_zero_right] at h
    have hc : (∑ j ∈ Finset.range r, (r.choose (j + 1) : ℝ)) + 1 = 2 ^ r := by
      exact_mod_cast h
    linarith only [hc]
  rw [multiplicityPrimitiveMass_split, add_sub_cancel_left, ← hchoose, Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  rw [coe_multiplicityPrimitiveCoefficient]
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
  push_cast
  nlinarith only [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) (by positivity : (0 : ℝ) ≤ 2 * n + 1)]

/-- The same tail controls the error in the alternating normalizer. -/
theorem multiplicityPrimitiveNormalizer_error_le (r n : ℕ) :
    |multiplicityPrimitiveNormalizer r n - 1| ≤ multiplicityPrimitiveMass r n - 1 := by
  rw [multiplicityPrimitiveNormalizer_split, multiplicityPrimitiveMass_split,
    add_sub_cancel_left, add_sub_cancel_left]
  calc
    _ ≤ ∑ j ∈ Finset.range r, |(-1 : ℝ) ^ (j + 1) *
        ((multiplicityPrimitiveCoefficient r n (j + 1) : ℝ≥0) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (multiplicityPrimitiveCoefficient r n (j + 1)).coe_nonneg]

private theorem exists_positive_multiplicity_normalizer (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < multiplicityPrimitiveNormalizer r n ∧
      multiplicityPrimitiveMass r n / multiplicityPrimitiveNormalizer r n < 1 + ε := by
  let A : ℝ := 2 ^ r - 1
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 * A) (4 * A / ε))
  have hnA : 2 * A < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hnε : 4 * A < (n : ℝ) * ε :=
    (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_right _ _) hn)
  let B : ℝ := A / (2 * (n : ℝ) + 2)
  have hD : (0 : ℝ) < 2 * (n : ℝ) + 2 := by positivity
  have hBhalf : B < 1 / 2 := by
    apply (div_lt_iff₀ hD).mpr
    linarith only [hnA, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hBε : B < ε / 4 := by
    apply (div_lt_iff₀ hD).mpr
    nlinarith only [hnε, hε, mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hε.le]
  have hmass : multiplicityPrimitiveMass r n - 1 ≤ B :=
    multiplicityPrimitiveMass_sub_one_le r n
  have herr : |multiplicityPrimitiveNormalizer r n - 1| ≤ B :=
    (multiplicityPrimitiveNormalizer_error_le r n).trans hmass
  have hlower := (abs_le.mp herr).1
  have hS : 1 / 2 < multiplicityPrimitiveNormalizer r n := by
    linarith only [hlower, hBhalf]
  refine ⟨n, by linarith only [hS], ?_⟩
  apply (div_lt_iff₀ (by linarith only [hS])).mpr
  nlinarith only [hmass, hlower, hBε,
    mul_pos hε (sub_pos.mpr hS)]

private theorem odd_primitive_power (n j : ℕ) :
    (-1 : ℂ) ^ (1 + j * (2 * n + 1)) = -((-1 : ℂ) ^ j) := by
  have he : 1 + j * (2 * n + 1) = (2 * n + 1) * j + 1 := by ring
  rw [he, pow_succ, pow_mul]
  simp [pow_add, pow_mul]

/-- Normalization places the marked zero exactly at `β + iπ/log 2`. -/
theorem arbitraryMultiplicityAnnihilator_zero (β : ℝ) (r n : ℕ) :
    dirichletEval (sharpBinomialRoot β) (arbitraryMultiplicityAnnihilator β r n) = 0 := by
  rw [dirichletEval_arbitraryMultiplicityAnnihilator, scaledTwoMonomial_at_root]
  have hsum : (∑ j ∈ Finset.range (r + 1),
      (((multiplicityPrimitiveCoefficient r n j : ℝ≥0) : ℝ) : ℂ) *
        (-1 : ℂ) ^ (1 + j * (2 * n + 1))) =
      -(multiplicityPrimitiveNormalizer r n : ℂ) := by
    rw [multiplicityPrimitiveNormalizer, Complex.ofReal_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [odd_primitive_power]
    push_cast
    ring
  rw [hsum]
  have hne : (multiplicityPrimitiveNormalizer r n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (multiplicityPrimitiveNormalizer_pos r n).ne'
  field_simp
  ring

theorem arbitraryMultiplicityAnnihilator_tail_mass (β : ℝ) (r n : ℕ) :
    dirichletTailMass (arbitraryMultiplicityAnnihilator β r n) β =
      multiplicityPrimitiveMass r n / multiplicityPrimitiveNormalizer r n := by
  have he := dirichletEval_ofReal_eq_one_add_tail
    (arbitraryMultiplicityAnnihilator_constantCoeff β r n) β
  rw [dirichletEval_arbitraryMultiplicityAnnihilator,
    scaledTwoMonomial_at_real] at he
  simp only [one_pow, mul_one] at he
  have hs : (∑ j ∈ Finset.range (r + 1),
      (((multiplicityPrimitiveCoefficient r n j : ℝ≥0) : ℝ) : ℂ)) =
      (multiplicityPrimitiveMass r n : ℂ) := by
    simp only [multiplicityPrimitiveMass, Complex.ofReal_sum]
  rw [hs, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_one,
    ← Complex.ofReal_add] at he
  have hr := Complex.ofReal_injective he
  rw [div_eq_mul_inv]
  linarith only [hr]

private theorem scaledTwoMonomial_hasDerivAt (β : ℝ) (s : ℂ) :
    HasDerivAt (fun z => dirichletEval z (scaledTwoMonomial β))
      (-(Real.log 2 : ℂ) * dirichletEval s (scaledTwoMonomial β)) s := by
  have h := (Complex.hasDerivAt_exp ((Real.log 2 : ℂ) * ((β : ℂ) - s))).comp s
    (((hasDerivAt_const s (β : ℂ)).sub (hasDerivAt_id s)).const_mul (Real.log 2 : ℂ))
  simpa only [Function.comp_def, Pi.sub_def, id_eq, zero_sub, mul_neg_one, neg_one_mul,
    dirichletEval_scaledTwoMonomial, mul_comm] using h

private theorem primitive_coefficient_mul_degree (r n j : ℕ) :
    (((multiplicityPrimitiveCoefficient r n j : ℝ≥0) : ℝ) : ℂ) *
      ((1 + j * (2 * n + 1) : ℕ) : ℂ) = (r.choose j : ℂ) := by
  have hc : (((multiplicityPrimitiveCoefficient r n j : ℝ≥0) : ℝ) : ℂ) =
      (r.choose j : ℂ) / ((1 + j * (2 * n + 1) : ℕ) : ℂ) := by
    simp [multiplicityPrimitiveCoefficient]
  rw [hc, div_mul_cancel₀ _ (by exact_mod_cast (show 1 + j * (2 * n + 1) ≠ 0 by omega))]

/-- Differentiation recovers the binomial whose odd-power root has prescribed order. -/
theorem arbitraryMultiplicityAnnihilator_hasDerivAt (β : ℝ) (r n : ℕ) (s : ℂ) :
    HasDerivAt (fun z => dirichletEval z (arbitraryMultiplicityAnnihilator β r n))
      (((multiplicityPrimitiveNormalizer r n : ℂ)⁻¹ *
        (-(Real.log 2 : ℂ) * dirichletEval s (scaledTwoMonomial β))) *
        (1 + dirichletEval s (scaledTwoMonomial β) ^ (2 * n + 1)) ^ r) s := by
  let V : ℂ → ℂ := fun z => dirichletEval z (scaledTwoMonomial β)
  let D : ℂ := -(Real.log 2 : ℂ) * V s
  have hterm (j : ℕ) :
      HasDerivAt (fun z => (((multiplicityPrimitiveCoefficient r n j : ℝ≥0) : ℝ) : ℂ) *
        V z ^ (1 + j * (2 * n + 1)))
        ((r.choose j : ℂ) * V s ^ (j * (2 * n + 1)) * D) s := by
    have h := ((scaledTwoMonomial_hasDerivAt β s).pow (1 + j * (2 * n + 1))).const_mul
      (((multiplicityPrimitiveCoefficient r n j : ℝ≥0) : ℝ) : ℂ)
    simpa only [V, D, Nat.add_sub_cancel_left, ← mul_assoc,
      primitive_coefficient_mul_degree] using! h
  have hsum := HasDerivAt.fun_sum (u := Finset.range (r + 1)) (fun j _ => hterm j)
  have h := (hsum.const_mul ((multiplicityPrimitiveNormalizer r n : ℂ)⁻¹)).const_add 1
  have hf : (fun z => dirichletEval z (arbitraryMultiplicityAnnihilator β r n)) =
      fun z => 1 + ((multiplicityPrimitiveNormalizer r n : ℂ)⁻¹) *
        ∑ j ∈ Finset.range (r + 1),
          (((multiplicityPrimitiveCoefficient r n j : ℝ≥0) : ℝ) : ℂ) *
            V z ^ (1 + j * (2 * n + 1)) := by
    funext z
    exact dirichletEval_arbitraryMultiplicityAnnihilator β r n z
  have hbinom : (1 + V s ^ (2 * n + 1)) ^ r =
      ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * V s ^ (j * (2 * n + 1)) := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    rw [one_pow, mul_one, ← pow_mul, Nat.mul_comm (2 * n + 1) j, mul_comm]
  have he : (((multiplicityPrimitiveNormalizer r n : ℂ)⁻¹ * D) *
      (1 + V s ^ (2 * n + 1)) ^ r) =
      (multiplicityPrimitiveNormalizer r n : ℂ)⁻¹ *
        ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * V s ^ (j * (2 * n + 1)) * D := by
    rw [hbinom, ← Finset.sum_mul]
    ring
  change HasDerivAt _ (((multiplicityPrimitiveNormalizer r n : ℂ)⁻¹ * D) *
    (1 + V s ^ (2 * n + 1)) ^ r) s
  rw [hf, he]
  exact h

/-- The marked zero has exact order `r+1`, including every positive multiplicity. -/
theorem arbitraryMultiplicityAnnihilator_order (β : ℝ) (r n : ℕ) :
    analyticOrderAt (fun s => dirichletEval s (arbitraryMultiplicityAnnihilator β r n))
      (sharpBinomialRoot β) = (r : ℕ∞) + 1 := by
  let ρ := sharpBinomialRoot β
  let V : ℂ → ℂ := fun s => dirichletEval s (scaledTwoMonomial β)
  let W : ℂ → ℂ := fun s => 1 + V s ^ (2 * n + 1)
  let A : ℂ → ℂ := fun s => (multiplicityPrimitiveNormalizer r n : ℂ)⁻¹ *
    (-(Real.log 2 : ℂ) * V s)
  have hV : AnalyticAt ℂ V ρ := (differentiable_dirichletEval (scaledTwoMonomial β)).analyticAt ρ
  have hW : AnalyticAt ℂ W ρ := analyticAt_const.add (hV.pow (2 * n + 1))
  have hA : AnalyticAt ℂ A ρ := analyticAt_const.mul (analyticAt_const.mul hV)
  have hroot : V ρ = -1 := scaledTwoMonomial_at_root β
  have hWzero : W ρ = 0 := by simp [W, hroot, pow_add, pow_mul]
  have hWd : deriv W ρ = ((2 * n + 1 : ℕ) : ℂ) * (Real.log 2 : ℂ) := by
    have h := ((scaledTwoMonomial_hasDerivAt_root β).pow (2 * n + 1)).const_add 1
    have hp : (-1 : ℂ) ^ (2 * n + 1 - 1) = 1 := by
      rw [Nat.add_sub_cancel, pow_mul]
      norm_num
    rw [scaledTwoMonomial_at_root, hp, mul_one] at h
    exact h.deriv
  have hlog : (Real.log 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  have hWorder : analyticOrderAt W ρ = 1 :=
    hW.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hWzero
      (by rw [hWd]; exact mul_ne_zero (by exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)) hlog)
  have hAorder : analyticOrderAt A ρ = 0 := by
    apply analyticOrderAt_eq_zero.mpr
    right
    dsimp [A]
    rw [hroot]
    exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (multiplicityPrimitiveNormalizer_pos r n).ne'))
      (mul_ne_zero (neg_ne_zero.mpr hlog) (by norm_num))
  have hderiv : deriv (fun s => dirichletEval s (arbitraryMultiplicityAnnihilator β r n)) =
      A * W ^ r := by
    funext s
    exact (arbitraryMultiplicityAnnihilator_hasDerivAt β r n s).deriv
  apply (analyticOrderAt_deriv_eq_iff
    ((differentiable_dirichletEval (arbitraryMultiplicityAnnihilator β r n)).analyticAt ρ)
    (arbitraryMultiplicityAnnihilator_zero β r n)).mpr
  rw [hderiv, analyticOrderAt_mul hA (hW.pow r), analyticOrderAt_pow hW,
    hAorder, hWorder, zero_add]
  simp

/-- Arbitrarily high exact multiplicity is compatible with tail mass arbitrarily close to one. -/
theorem exists_arbitrary_multiplicity_near_unit_mass (β : ℝ) (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0,
      MvPolynomial.constantCoeff P = 1 ∧
      dirichletEval (sharpBinomialRoot β) P = 0 ∧
      analyticOrderAt (fun s => dirichletEval s P) (sharpBinomialRoot β) = (r : ℕ∞) + 1 ∧
      1 ≤ dirichletTailMass P β ∧ dirichletTailMass P β < 1 + ε ∧
      (0 < r → 1 < dirichletTailMass P β) := by
  obtain ⟨n, _, hnear⟩ := exists_positive_multiplicity_normalizer r hε
  let P := arbitraryMultiplicityAnnihilator β r n
  have hP := arbitraryMultiplicityAnnihilator_constantCoeff β r n
  have hz := arbitraryMultiplicityAnnihilator_zero β r n
  refine ⟨P, hP, hz, arbitraryMultiplicityAnnihilator_order β r n, ?_, ?_, ?_⟩
  · simpa only [sharpBinomialRoot_re] using one_le_dirichletTailMass_of_zero hP hz
  · rw [arbitraryMultiplicityAnnihilator_tail_mass β r n]
    exact hnear
  · intro hr
    have hd : deriv (fun s => dirichletEval s P) (sharpBinomialRoot β) = 0 := by
      rw [(arbitraryMultiplicityAnnihilator_hasDerivAt β r n _).deriv]
      simp [scaledTwoMonomial_at_root, pow_add, pow_mul, zero_pow hr.ne']
    simpa only [sharpBinomialRoot_re] using one_lt_tail_mass_of_zero_deriv hP hz hd

#print axioms multiplicityPrimitiveNormalizer_eq_integral
#print axioms multiplicityPrimitiveNormalizer_pos
#print axioms multiplicityPrimitiveMass_sub_one_le
#print axioms multiplicityPrimitiveNormalizer_error_le
#print axioms arbitraryMultiplicityAnnihilator_order
#print axioms exists_arbitrary_multiplicity_near_unit_mass

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
