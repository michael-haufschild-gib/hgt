import GaloisForLFunctions.RHTower.XiShiftedFilteredGammaTransmutation
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeChebyshevExpansion
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCayleyDivisorLift
import GaloisForLFunctions.RHTower.XiResolventHankelLadder
import GaloisForLFunctions.RHTower.XiSquaredCompleteMonotonicityFarRay

/-!
# Cayley--Chebyshev positive-root source packet

This module constructs the exact denominator-cleared source polynomial
`Q_n(W) = (1+W)^n T_n((1-W)/(1+W))`. It proves its recurrence, explicit positive
tangent-square roots, rational-square identity on the real spectral line, and unconditional
unit-shift Gamma transmutation for the literal Xi divisor.
-/

open Polynomial Real

namespace RHTower

noncomputable section

/-- Degree-`n` Cayley--Chebyshev polynomial `T_n(2X-1)`. -/
def cayleyChebyshevPolynomial (n : ℕ) : Polynomial ℝ :=
  xiHardEdgeReciprocalPolynomial 1 (Polynomial.Chebyshev.T ℝ (n : ℤ))

theorem eval_cayleyChebyshevPolynomial (n : ℕ) (u : ℝ) :
    (cayleyChebyshevPolynomial n).eval u =
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (2 * u - 1) := by
  simp [cayleyChebyshevPolynomial, xiHardEdgeReciprocalPolynomial]

/-- Coefficient vector of `T_n`, padded to its exact degree. -/
def cayleyChebyshevSourceCoefficients (n : ℕ) : Fin (n + 1) → ℝ :=
  Polynomial.toFn (n + 1) (cayleyChebyshevPolynomial n)

/-- Denominator-cleared source polynomial
`Q_n(W) = (1+W)^n T_n((1-W)/(1+W))`. -/
def cayleyChebyshevSourcePolynomial (n : ℕ) : Polynomial ℝ :=
  xiShiftedReversedPolynomial 1 n (cayleyChebyshevSourceCoefficients n)

theorem ofFn_cayleyChebyshevSourceCoefficients (n : ℕ) :
    Polynomial.ofFn (n + 1) (cayleyChebyshevSourceCoefficients n) =
      cayleyChebyshevPolynomial n := by
  apply Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
  apply lt_of_le_of_lt
    (natDegree_xiHardEdgeReciprocalPolynomial_le 1
      (Polynomial.Chebyshev.T ℝ (n : ℤ)))
  rw [natDegree_chebyshevT]
  omega

/-- Exact source handoff away from the unique clearing pole. -/
theorem eval_cayleyChebyshevSourcePolynomial_div (n : ℕ) (W : ℝ)
    (hW : 1 + W ≠ 0) :
    (cayleyChebyshevSourcePolynomial n).eval W / (1 + W) ^ n =
      (cayleyChebyshevPolynomial n).eval (1 / (1 + W)) := by
  have hcomplex : (1 : ℂ) + (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hrev := eval_xiShiftedReversedPolynomial_eq 1 n
    (cayleyChebyshevSourceCoefficients n) (W : ℂ) hcomplex
  rw [ofFn_cayleyChebyshevSourceCoefficients] at hrev
  have hinv : ((1 : ℂ) + (W : ℂ))⁻¹ = ((1 / (1 + W) : ℝ) : ℂ) := by
    have hadd : (1 : ℂ) + (W : ℂ) = ((1 + W : ℝ) : ℂ) := by norm_num
    rw [hadd, one_div, ← Complex.ofReal_inv]
  norm_num only [Complex.ofReal_one] at hrev
  rw [evalRealPolynomial_ofReal] at hrev
  rw [hinv, evalRealPolynomial_ofReal] at hrev
  have hreal :
      (cayleyChebyshevSourcePolynomial n).eval W =
        (1 + W) ^ n *
          (cayleyChebyshevPolynomial n).eval (1 / (1 + W)) := by
    exact_mod_cast hrev
  rw [hreal]
  field_simp [hW]

theorem cayleyChebyshevSourcePolynomial_zero :
    cayleyChebyshevSourcePolynomial 0 = 1 := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.Finite.infinite_compl (Set.finite_singleton (-1 : ℝ))).mono ?_
  intro W hW
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff] at hW ⊢
  have hplus : 1 + W ≠ 0 := by
    intro hp
    apply hW
    linarith
  have h := eval_cayleyChebyshevSourcePolynomial_div 0 W hplus
  rw [eval_cayleyChebyshevPolynomial] at h
  simpa using h

theorem cayleyChebyshevSourcePolynomial_one :
    cayleyChebyshevSourcePolynomial 1 = 1 - X := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.Finite.infinite_compl (Set.finite_singleton (-1 : ℝ))).mono ?_
  intro W hW
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff] at hW ⊢
  have hplus : 1 + W ≠ 0 := by
    intro hp
    apply hW
    linarith
  have h := eval_cayleyChebyshevSourcePolynomial_div 1 W hplus
  rw [eval_cayleyChebyshevPolynomial] at h
  simp at h
  have h' := (div_eq_iff hplus).mp h
  field_simp [hplus] at h'
  rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
  nlinarith

/-- Denominator-cleared Chebyshev recurrence. -/
theorem cayleyChebyshevSourcePolynomial_succ_succ (n : ℕ) :
    cayleyChebyshevSourcePolynomial (n + 2) =
      2 * (1 - X) * cayleyChebyshevSourcePolynomial (n + 1) -
        (1 + X) ^ (2 : ℕ) * cayleyChebyshevSourcePolynomial n := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.Finite.infinite_compl (Set.finite_singleton (-1 : ℝ))).mono ?_
  intro W hW
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff] at hW ⊢
  have hplus : 1 + W ≠ 0 := by
    intro hp
    apply hW
    linarith
  have h0 := eval_cayleyChebyshevSourcePolynomial_div n W hplus
  have h1 := eval_cayleyChebyshevSourcePolynomial_div (n + 1) W hplus
  have h2 := eval_cayleyChebyshevSourcePolynomial_div (n + 2) W hplus
  have hpRec :
      (cayleyChebyshevPolynomial (n + 2)).eval (1 / (1 + W)) =
        2 * (2 * (1 / (1 + W)) - 1) *
            (cayleyChebyshevPolynomial (n + 1)).eval (1 / (1 + W)) -
          (cayleyChebyshevPolynomial n).eval (1 / (1 + W)) := by
    have hcheb : Polynomial.Chebyshev.T ℝ ((n + 2 : ℕ) : ℤ) =
        2 * X * Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ) -
          Polynomial.Chebyshev.T ℝ (n : ℤ) := by
      convert Polynomial.Chebyshev.T_add_two (R := ℝ) (n : ℤ) using 1 <;>
        norm_num
    rw [eval_cayleyChebyshevPolynomial, eval_cayleyChebyshevPolynomial,
      eval_cayleyChebyshevPolynomial, hcheb]
    simp
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_pow]
  have h0' := (div_eq_iff (pow_ne_zero n hplus)).mp h0
  have h1' := (div_eq_iff (pow_ne_zero (n + 1) hplus)).mp h1
  have h2' := (div_eq_iff (pow_ne_zero (n + 2) hplus)).mp h2
  rw [hpRec] at h2'
  have hpow1 : (1 + W) ^ (n + 1) = (1 + W) ^ n * (1 + W) := by
    rw [pow_succ]
  have hpow2 : (1 + W) ^ (n + 2) = (1 + W) ^ n * (1 + W) ^ (2 : ℕ) := by
    rw [pow_add]
  rw [hpow1] at h1'
  rw [hpow2] at h2'
  field_simp [hplus] at h2'
  rw [h0', h1', h2']
  ring

/-- Explicit positive candidate root. -/
def cayleyChebyshevSourceRoot (n k : ℕ) : ℝ :=
  Real.tan (((2 * k + 1 : ℕ) : ℝ) * Real.pi / (4 * n)) ^ (2 : ℕ)

theorem cayleyChebyshevSourceRoot_pos {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    0 < cayleyChebyshevSourceRoot n k := by
  rw [cayleyChebyshevSourceRoot]
  apply sq_pos_of_pos
  apply Real.tan_pos_of_pos_of_lt_pi_div_two
  · positivity
  · have hnR : (0 : ℝ) < n := by positivity
    have hkR : ((2 * k + 1 : ℕ) : ℝ) < 2 * n := by exact_mod_cast (by omega)
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * n)).2
    nlinarith [Real.pi_pos]

set_option maxHeartbeats 800000 in
/-- Every explicit tangent-square node is a root of `Q_n`. -/
theorem cayleyChebyshevSourcePolynomial_eval_root {n k : ℕ}
    (hn : 0 < n) (hk : k < n) :
    (cayleyChebyshevSourcePolynomial n).eval
        (cayleyChebyshevSourceRoot n k) = 0 := by
  let θ : ℝ := ((2 * k + 1 : ℕ) : ℝ) * Real.pi / (2 * n)
  have hθpos : 0 < θ := by dsimp [θ]; positivity
  have hθpi : θ < Real.pi := by
    dsimp [θ]
    have hnR : (0 : ℝ) < n := by positivity
    have hkR : ((2 * k + 1 : ℕ) : ℝ) < 2 * n := by exact_mod_cast (by omega)
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).2
    nlinarith [Real.pi_pos]
  have hcos : Real.cos θ ≠ -1 := by
    have hgt := Real.strictAntiOn_cos
      (show θ ∈ Set.Icc (0 : ℝ) Real.pi by exact ⟨hθpos.le, hθpi.le⟩)
      (show Real.pi ∈ Set.Icc (0 : ℝ) Real.pi by exact ⟨Real.pi_pos.le, le_rfl⟩)
      hθpi
    rw [Real.cos_pi] at hgt
    linarith
  have htan : 0 < Real.tan (θ / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have hrootEq : cayleyChebyshevSourceRoot n k = Real.tan (θ / 2) ^ (2 : ℕ) := by
    have harg : (((2 * k + 1 : ℕ) : ℝ) * Real.pi / (4 * n)) = θ / 2 := by
      dsimp [θ]
      ring
    rw [cayleyChebyshevSourceRoot, harg]
  have hplus : 1 + cayleyChebyshevSourceRoot n k ≠ 0 := by
    rw [hrootEq]
    positivity
  have hhalf := Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq θ hcos
  have hmobius :
      (1 - cayleyChebyshevSourceRoot n k) /
          (1 + cayleyChebyshevSourceRoot n k) = Real.cos θ := by
    rw [hrootEq]
    exact hhalf.symm
  have hnorm := eval_cayleyChebyshevSourcePolynomial_div n
    (cayleyChebyshevSourceRoot n k) hplus
  have harg : 2 * (1 / (1 + cayleyChebyshevSourceRoot n k)) - 1 = Real.cos θ := by
    rw [← hmobius]
    field_simp [hplus]
    ring
  rw [eval_cayleyChebyshevPolynomial, harg,
    Polynomial.Chebyshev.T_real_cos] at hnorm
  have hangle : (n : ℤ) * θ = ((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2 := by
    dsimp [θ]
    norm_num [Nat.cast_add, Nat.cast_mul]
    field_simp
  have hangle' : ((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2 =
      Real.pi / 2 + k * Real.pi := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  rw [hangle, hangle', Real.cos_add_nat_mul_pi, Real.cos_pi_div_two,
    mul_zero] at hnorm
  field_simp [hplus] at hnorm
  simpa using hnorm

/-- Exact real-line rational-square identity. -/
theorem cayleyChebyshev_rational_square (n : ℕ) (x : ℝ) :
    (cayleyChebyshevSourcePolynomial n).eval (x ^ (2 : ℕ)) ^ (2 : ℕ) /
        (1 + x ^ (2 : ℕ)) ^ (2 * n + 1) =
      Real.cos (2 * n * Real.arctan x) ^ (2 : ℕ) / (1 + x ^ (2 : ℕ)) := by
  have hplus : 1 + x ^ (2 : ℕ) ≠ 0 := by positivity
  have hnorm := eval_cayleyChebyshevSourcePolynomial_div n (x ^ (2 : ℕ)) hplus
  have hcos :
      (cayleyChebyshevPolynomial n).eval (1 / (1 + x ^ (2 : ℕ))) =
        Real.cos (2 * n * Real.arctan x) := by
    rw [eval_cayleyChebyshevPolynomial]
    have harctan := Real.cos_two_mul (Real.arctan x)
    rw [Real.cos_sq_arctan] at harctan
    have harg : 2 * (1 / (1 + x ^ (2 : ℕ))) - 1 =
        Real.cos (2 * Real.arctan x) := by nlinarith
    rw [harg, Polynomial.Chebyshev.T_real_cos]
    congr 1
    push_cast
    ring
  rw [hcos] at hnorm
  have hQ : (cayleyChebyshevSourcePolynomial n).eval (x ^ (2 : ℕ)) =
      (1 + x ^ (2 : ℕ)) ^ n * Real.cos (2 * n * Real.arctan x) := by
    have := (div_eq_iff (pow_ne_zero n hplus)).mp hnorm
    nlinarith
  rw [hQ]
  field_simp [hplus]
  ring

/-! ### Exact Xi source handoff -/

theorem cayleyChebyshevPolynomial_eq_rangeSum (n : ℕ) :
    cayleyChebyshevPolynomial n =
      ∑ j ∈ Finset.range (n + 1),
        Polynomial.C ((cayleyChebyshevPolynomial n).coeff j) * X ^ j := by
  have hdeg : (cayleyChebyshevPolynomial n).natDegree < n + 1 := by
    apply lt_of_le_of_lt
      (natDegree_xiHardEdgeReciprocalPolynomial_le 1
        (Polynomial.Chebyshev.T ℝ (n : ℤ)))
    rw [natDegree_chebyshevT]
    omega
  conv_lhs =>
    rw [Polynomial.as_sum_range' (cayleyChebyshevPolynomial n) (n + 1) hdeg]
  exact Finset.sum_congr rfl fun j _ =>
    Polynomial.C_mul_X_pow_eq_monomial.symm

/-- Real part of the Cayley--Chebyshev trace is its literal unit-shift Hankel quadratic. -/
theorem xiResolventTrace_cayleyChebyshevPolynomial_re_eq_hankel (n : ℕ) :
    (xiResolventTrace 1 (cayleyChebyshevPolynomial n)).re =
      xiShiftedReciprocalHankelQuadratic 1
        (cayleyChebyshevSourceCoefficients n) := by
  rw [cayleyChebyshevPolynomial_eq_rangeSum,
    xiResolventTrace_rangeSum (by norm_num)]
  rw [xiResolventHankelForm, xiShiftedReciprocalHankelQuadratic]
  change Complex.reCLM (∑ i ∈ Finset.range (n + 1),
      ∑ j ∈ Finset.range (n + 1),
        (((cayleyChebyshevPolynomial n).coeff i : ℂ) *
          ((cayleyChebyshevPolynomial n).coeff j : ℂ)) *
            xiResolventMoment (i + j) 1) = _
  rw [map_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [xiShiftedReciprocalMoment_eq_xiResolventMoment (by norm_num)]
  simp [cayleyChebyshevSourceCoefficients, Polynomial.toFn, Complex.mul_re]

/-- Exact normalized Gamma transmutation for the explicit positive-root source polynomial. -/
theorem xiResolventTrace_cayleyChebyshevPolynomial_re_eq_normalizedFilteredGamma
    (n : ℕ) :
    (xiResolventTrace 1 (cayleyChebyshevPolynomial n)).re =
      (1 / ((2 * n).factorial : ℝ)) *
        ∫ t in Set.Ioi (0 : ℝ),
          xiShiftedFilteredGammaKernelReal 1 0 n
            (cayleyChebyshevSourceCoefficients n) t := by
  rw [xiResolventTrace_cayleyChebyshevPolynomial_re_eq_hankel,
    xiShiftedReciprocalHankelQuadratic_one_eq_normalizedFilteredGamma]

end
end RHTower
