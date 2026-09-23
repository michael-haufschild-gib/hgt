import GaloisForLFunctions.RHTower.GibbsBatchParityCoarseGraining
import GaloisForLFunctions.RHTower.GibbsCriticalDissipationAntiscaleResonance
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Gibbs antiscale determinant odd-cube law

Exact signed/unsigned Euler norm difference is an odd Boolean cube.  Its first coordinate is
critical half-density, while every higher odd grade is forced by same literal determinant.
When every local coordinate lies strictly between -1 and 1, whole cube resums into one additive
rapidity coordinate through artanh.  These are finite identities with no limiting or arithmetic
assumption.
-/

open scoped BigOperators

namespace RHTower.GibbsGas

noncomputable section

/-- Sum of all odd subset monomials of a finite coordinate family. -/
def oddSubsetProductSum {ι : Type*} (s : Finset ι) (u : ι → ℝ) : ℝ :=
  ∑ U ∈ s.powerset with Odd U.card, ∏ i ∈ U, u i

/-- Full product expansion with parity coefficient retained explicitly. -/
theorem prod_one_add_sub_prod_one_sub_eq_paritySum
    {ι : Type*} (s : Finset ι) (u : ι → ℝ) :
    (∏ i ∈ s, (1 + u i)) - (∏ i ∈ s, (1 - u i)) =
      ∑ U ∈ s.powerset,
        (1 - (-1 : ℝ) ^ U.card) * ∏ i ∈ U, u i := by
  classical
  rw [Finset.prod_one_add]
  have hminus :
      (∏ i ∈ s, (1 - u i)) =
        ∑ U ∈ s.powerset, ∏ i ∈ U, (-u i) := by
    simpa [sub_eq_add_neg] using
      (Finset.prod_one_add (R := ℝ) (f := fun i => -u i) s)
  rw [hminus, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.prod_neg]
  ring

/-- **Odd-cube completion.**  Even grades cancel and every odd grade doubles. -/
theorem prod_one_add_sub_prod_one_sub_eq_two_oddSubsetProductSum
    {ι : Type*} (s : Finset ι) (u : ι → ℝ) :
    (∏ i ∈ s, (1 + u i)) - (∏ i ∈ s, (1 - u i)) =
      2 * oddSubsetProductSum s u := by
  classical
  rw [prod_one_add_sub_prod_one_sub_eq_paritySum]
  unfold oddSubsetProductSum
  rw [← Finset.sum_filter_add_sum_filter_not s.powerset (fun U => Odd U.card)
    (fun U => (1 - (-1 : ℝ) ^ U.card) * ∏ i ∈ U, u i)]
  have hodd :
      (∑ U ∈ s.powerset with Odd U.card,
          (1 - (-1 : ℝ) ^ U.card) * ∏ i ∈ U, u i) =
        2 * ∑ U ∈ s.powerset with Odd U.card, ∏ i ∈ U, u i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    have hUodd : Odd U.card := (Finset.mem_filter.mp hU).2
    rw [hUodd.neg_one_pow]
    ring
  have heven :
      (∑ U ∈ s.powerset with ¬Odd U.card,
          (1 - (-1 : ℝ) ^ U.card) * ∏ i ∈ U, u i) = 0 := by
    apply Finset.sum_eq_zero
    intro U hU
    have hUnot : ¬ Odd U.card := (Finset.mem_filter.mp hU).2
    have hUeven : Even U.card := (Nat.even_or_odd U.card).resolve_right hUnot
    rw [hUeven.neg_one_pow]
    ring
  rw [hodd, heven, add_zero]

/-- Critical transverse coordinate for one local Euler radius and phase. -/
def criticalEulerTransverseCoordinate (radius phase : ℝ) : ℝ :=
  2 * radius * Real.cos phase / (1 + radius ^ (2 : ℕ))

/-- Exact plus local norm-square factorization. -/
theorem normSq_one_add_radius_exp_eq
    (radius phase : ℝ) :
    Complex.normSq
        (1 + (radius : ℂ) * Complex.exp ((phase : ℂ) * Complex.I)) =
      (1 + radius ^ (2 : ℕ)) *
        (1 + criticalEulerTransverseCoordinate radius phase) := by
  rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal]
  simp [Complex.normSq_eq_norm_sq, Complex.norm_exp,
    Complex.exp_ofReal_mul_I_re]
  unfold criticalEulerTransverseCoordinate
  have hden : 0 < 1 + radius ^ (2 : ℕ) := by positivity
  field_simp

/-- Exact minus local norm-square factorization. -/
theorem normSq_one_sub_radius_exp_eq
    (radius phase : ℝ) :
    Complex.normSq
        (1 - (radius : ℂ) * Complex.exp ((phase : ℂ) * Complex.I)) =
      (1 + radius ^ (2 : ℕ)) *
        (1 - criticalEulerTransverseCoordinate radius phase) := by
  rw [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal]
  simp [Complex.normSq_eq_norm_sq, Complex.norm_exp,
    Complex.exp_ofReal_mul_I_re]
  unfold criticalEulerTransverseCoordinate
  have hden : 0 < 1 + radius ^ (2 : ℕ) := by positivity
  field_simp

/-- Exact finite Euler determinant factorization into baseline mass and transverse cube. -/
theorem prod_normSq_plus_sub_prod_normSq_minus_eq
    {ι : Type*} (s : Finset ι) (radius phase : ι → ℝ) :
    (∏ i ∈ s,
        Complex.normSq
          (1 + (radius i : ℂ) * Complex.exp ((phase i : ℂ) * Complex.I))) -
      (∏ i ∈ s,
        Complex.normSq
          (1 - (radius i : ℂ) * Complex.exp ((phase i : ℂ) * Complex.I))) =
      (∏ i ∈ s, (1 + radius i ^ (2 : ℕ))) *
        ((∏ i ∈ s, (1 + criticalEulerTransverseCoordinate (radius i) (phase i))) -
          ∏ i ∈ s, (1 - criticalEulerTransverseCoordinate (radius i) (phase i))) := by
  simp_rw [normSq_one_add_radius_exp_eq, normSq_one_sub_radius_exp_eq,
    Finset.prod_mul_distrib]
  ring

/-- Literal finite Euler determinant is baseline mass times complete odd cube. -/
theorem prod_normSq_plus_sub_prod_normSq_minus_eq_oddCube
    {ι : Type*} (s : Finset ι) (radius phase : ι → ℝ) :
    (∏ i ∈ s,
        Complex.normSq
          (1 + (radius i : ℂ) * Complex.exp ((phase i : ℂ) * Complex.I))) -
      (∏ i ∈ s,
        Complex.normSq
          (1 - (radius i : ℂ) * Complex.exp ((phase i : ℂ) * Complex.I))) =
      2 * (∏ i ∈ s, (1 + radius i ^ (2 : ℕ))) *
        oddSubsetProductSum s
          (fun i => criticalEulerTransverseCoordinate (radius i) (phase i)) := by
  rw [prod_normSq_plus_sub_prod_normSq_minus_eq]
  rw [prod_one_add_sub_prod_one_sub_eq_two_oddSubsetProductSum]
  ring

private theorem sqrt_one_sub_sq_mul_exp_artanh_eq_one_add
    {u : ℝ} (hu : u ∈ Set.Ioo (-1) 1) :
    √(1 - u ^ (2 : ℕ)) * Real.exp (Real.artanh u) = 1 + u := by
  have hsqrt : √(1 - u ^ (2 : ℕ)) ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    have hprod : 0 < (1 + u) * (1 - u) :=
      mul_pos (by linarith [hu.1]) (by linarith [hu.2])
    nlinarith
  rw [show Real.exp (Real.artanh u) =
      Real.cosh (Real.artanh u) + Real.sinh (Real.artanh u) by
        rw [Real.cosh_eq, Real.sinh_eq]
        ring]
  rw [Real.cosh_artanh hu, Real.sinh_artanh hu]
  field_simp

private theorem sqrt_one_sub_sq_mul_exp_neg_artanh_eq_one_sub
    {u : ℝ} (hu : u ∈ Set.Ioo (-1) 1) :
    √(1 - u ^ (2 : ℕ)) * Real.exp (-Real.artanh u) = 1 - u := by
  have hsqrt : √(1 - u ^ (2 : ℕ)) ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    have hprod : 0 < (1 + u) * (1 - u) :=
      mul_pos (by linarith [hu.1]) (by linarith [hu.2])
    nlinarith
  rw [show Real.exp (-Real.artanh u) =
      Real.cosh (Real.artanh u) - Real.sinh (Real.artanh u) by
        rw [Real.cosh_eq, Real.sinh_eq]
        ring]
  rw [Real.cosh_artanh hu, Real.sinh_artanh hu]
  field_simp

/-- **Rapidity resummation.**  Complete finite odd cube is one sinh of additive artanh
coordinates, multiplied by exact positive local amplitudes. -/
theorem prod_one_add_sub_prod_one_sub_eq_rapidity
    {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, u i ∈ Set.Ioo (-1) 1) :
    (∏ i ∈ s, (1 + u i)) - (∏ i ∈ s, (1 - u i)) =
      2 * (∏ i ∈ s, √(1 - u i ^ (2 : ℕ))) *
        Real.sinh (∑ i ∈ s, Real.artanh (u i)) := by
  have hplus :
      (∏ i ∈ s, (1 + u i)) =
        (∏ i ∈ s, √(1 - u i ^ (2 : ℕ))) *
          Real.exp (∑ i ∈ s, Real.artanh (u i)) := by
    calc
      ∏ i ∈ s, (1 + u i) =
          ∏ i ∈ s,
            (√(1 - u i ^ (2 : ℕ)) * Real.exp (Real.artanh (u i))) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (sqrt_one_sub_sq_mul_exp_artanh_eq_one_add (hu i hi)).symm
      _ = (∏ i ∈ s, √(1 - u i ^ (2 : ℕ))) *
          ∏ i ∈ s, Real.exp (Real.artanh (u i)) := Finset.prod_mul_distrib
      _ = (∏ i ∈ s, √(1 - u i ^ (2 : ℕ))) *
          Real.exp (∑ i ∈ s, Real.artanh (u i)) := by
        rw [Real.exp_sum]
  have hminus :
      (∏ i ∈ s, (1 - u i)) =
        (∏ i ∈ s, √(1 - u i ^ (2 : ℕ))) *
          Real.exp (-(∑ i ∈ s, Real.artanh (u i))) := by
    calc
      ∏ i ∈ s, (1 - u i) =
          ∏ i ∈ s,
            (√(1 - u i ^ (2 : ℕ)) * Real.exp (-Real.artanh (u i))) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (sqrt_one_sub_sq_mul_exp_neg_artanh_eq_one_sub (hu i hi)).symm
      _ = (∏ i ∈ s, √(1 - u i ^ (2 : ℕ))) *
          ∏ i ∈ s, Real.exp (-Real.artanh (u i)) := Finset.prod_mul_distrib
      _ = (∏ i ∈ s, √(1 - u i ^ (2 : ℕ))) *
          Real.exp (-(∑ i ∈ s, Real.artanh (u i))) := by
        congr 1
        rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [hplus, hminus, Real.sinh_eq]
  ring

/-- Complete spectral escape occurs exactly when additive rapidity vanishes. -/
theorem prod_one_add_eq_prod_one_sub_iff_rapidity_eq_zero
    {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, u i ∈ Set.Ioo (-1) 1) :
    (∏ i ∈ s, (1 + u i)) = (∏ i ∈ s, (1 - u i)) ↔
      ∑ i ∈ s, Real.artanh (u i) = 0 := by
  have hroot :
      0 < ∏ i ∈ s, √(1 - u i ^ (2 : ℕ)) := by
    apply Finset.prod_pos
    intro i hi
    apply Real.sqrt_pos.2
    have hui := hu i hi
    have hprod : 0 < (1 + u i) * (1 - u i) :=
      mul_pos (by linarith [hui.1]) (by linarith [hui.2])
    nlinarith
  have hrapidity := prod_one_add_sub_prod_one_sub_eq_rapidity s u hu
  constructor
  · intro h
    have hzero :
        (∏ i ∈ s, (1 + u i)) - (∏ i ∈ s, (1 - u i)) = 0 := sub_eq_zero.mpr h
    rw [hrapidity] at hzero
    have hsinh : Real.sinh (∑ i ∈ s, Real.artanh (u i)) = 0 := by
      rcases mul_eq_zero.mp hzero with htwo | hrest
      · exact False.elim ((mul_ne_zero (by norm_num) hroot.ne') htwo)
      · exact hrest
    exact Real.sinh_eq_zero.mp hsinh
  · intro h
    apply sub_eq_zero.mp
    rw [hrapidity, h, Real.sinh_zero, mul_zero]

end

end RHTower.GibbsGas
