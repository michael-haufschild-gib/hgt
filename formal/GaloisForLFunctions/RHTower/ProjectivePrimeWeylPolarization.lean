import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The projective prime clock: polarizations, transverse Gram, and Weyl leakage

On a finite point set `X` of cardinality `p + 1` — the model of `P¹(F_p)` — the *point/complement
polarization* at a marked point `a` is the two-dimensional subspace

`E a = span {e_a, 1_{X \ {a}}}`

of `EuclideanSpace ℂ X`, and the *positive natural-cone vector* with marked weight `e^z` is

`u_a(z) = (e^z e_a + 1_{X \ {a}}) / √(p + e^{2z})`.

This file proves the exact finite statements attached to that clock:

* two distinct polarizations meet exactly in the uniform source line `ℂ·u⁰` (needs `p + 1 ≥ 3`);
* the unit transverse vectors satisfy `⟪v_a, v_b⟫ = -1/p`, so their Gram determinant is `1 - p⁻²`;
* the marked-weight derivative of `u_a` at `z = 0` is `(√p/(p+1)) v_a`, of squared length
  `p/(p+1)²` — the squarefree Fisher capacity;
* the marked sign reflection has source expectation `(p-1)/(p+1)`;
* the compression leakage of a foreign natural-cone vector is
  `‖(1 - Q_a) u_b(z)‖² = ((p-1)/p)(e^z - 1)²/(p + e^{2z})`, which vanishes exactly at `z = 0`;
* the same-polarization Gram coefficient is the Bernoulli Hellinger affinity.

Every point permutation acts by a unitary that carries the whole package along.
-/

open Complex Finset
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Two-valued coordinate vectors -/

/-- The vector with value `w` at the marked point `a` and value `c` at every other point. -/
def projTwoValue (a : X) (w c : ℂ) : EuclideanSpace ℂ X :=
  (EuclideanSpace.equiv X ℂ).symm (fun x => if x = a then w else c)

omit [Fintype X] in
@[simp]
theorem projTwoValue_apply (a : X) (w c : ℂ) (x : X) :
    projTwoValue a w c x = if x = a then w else c := by
  simp [projTwoValue]

/-- Residue degree of the projective clock: `p = |X| - 1`. -/
def projDeg (X : Type*) [Fintype X] : ℝ := (Fintype.card X : ℝ) - 1

omit [DecidableEq X] in
theorem projDeg_add_one (X : Type*) [Fintype X] :
    projDeg X + 1 = (Fintype.card X : ℝ) := by
  rw [projDeg]; ring

omit [DecidableEq X] in
theorem projDeg_pos (h : 2 ≤ Fintype.card X) : 0 < projDeg X := by
  rw [projDeg]
  have : (2 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast h
  linarith

/-! ## The two master inner products -/

theorem inner_projTwoValue (a b : X) (w c w' c' : ℂ) :
    ⟪projTwoValue a w c, projTwoValue b w' c'⟫_ℂ =
      ∑ x : X, conj (if x = a then w else c) * (if x = b then w' else c') := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, projTwoValue_apply]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

theorem inner_projTwoValue_same (a : X) (w c w' c' : ℂ) :
    ⟪projTwoValue a w c, projTwoValue a w' c'⟫_ℂ =
      conj w * w' + (projDeg X : ℂ) * (conj c * c') := by
  classical
  rw [inner_projTwoValue, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have hsum : ∑ x ∈ Finset.univ.erase a,
      conj (if x = a then w else c) * (if x = a then w' else c') =
      ∑ _x ∈ Finset.univ.erase a, (conj c * c' : ℂ) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [if_neg (Finset.mem_erase.mp hx).1, if_neg (Finset.mem_erase.mp hx).1]
  have hcard : ((Fintype.card X - 1 : ℕ) : ℂ) = (projDeg X : ℂ) := by
    have h1 : 1 ≤ Fintype.card X := Fintype.card_pos_iff.mpr ⟨a⟩
    have hr : ((Fintype.card X - 1 : ℕ) : ℝ) = projDeg X := by
      rw [projDeg, Nat.cast_sub h1]; norm_num
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hr
  rw [hsum, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_univ, nsmul_eq_mul, hcard]
  simp

theorem inner_projTwoValue_ne {a b : X} (hab : a ≠ b) (w c w' c' : ℂ) :
    ⟪projTwoValue a w c, projTwoValue b w' c'⟫_ℂ =
      conj w * c' + conj c * w' + ((projDeg X : ℂ) - 1) * (conj c * c') := by
  classical
  have hmemb : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
  rw [inner_projTwoValue, ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    ← Finset.add_sum_erase _ _ hmemb]
  have hsum : ∑ x ∈ (Finset.univ.erase a).erase b,
      conj (if x = a then w else c) * (if x = b then w' else c') =
      ∑ _x ∈ (Finset.univ.erase a).erase b, (conj c * c' : ℂ) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
    have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    rw [if_neg hxa, if_neg hxb]
  have h2 : 2 ≤ Fintype.card X := by
    have hle : ({a, b} : Finset X).card ≤ Fintype.card X := Finset.card_le_univ _
    rwa [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton] at hle
  have hcard : ((Fintype.card X - 1 - 1 : ℕ) : ℂ) = (projDeg X : ℂ) - 1 := by
    have h1 : 1 ≤ Fintype.card X := le_trans (by norm_num) h2
    have hr : ((Fintype.card X - 1 - 1 : ℕ) : ℝ) = projDeg X - 1 := by
      rw [projDeg, Nat.cast_sub (by omega), Nat.cast_sub h1]
      norm_num
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hr
  rw [hsum, Finset.sum_const, Finset.card_erase_of_mem hmemb,
    Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
    nsmul_eq_mul, hcard]
  simp only [if_true, if_neg hab, if_neg (Ne.symm hab)]
  ring

theorem inner_projTwoValue_same_real (a : X) (w c w' c' : ℝ) :
    ⟪projTwoValue a (w : ℂ) (c : ℂ), projTwoValue a (w' : ℂ) (c' : ℂ)⟫_ℂ =
      ((w * w' + projDeg X * (c * c') : ℝ) : ℂ) := by
  rw [inner_projTwoValue_same]
  push_cast
  simp [Complex.conj_ofReal]

theorem inner_projTwoValue_ne_real {a b : X} (hab : a ≠ b) (w c w' c' : ℝ) :
    ⟪projTwoValue a (w : ℂ) (c : ℂ), projTwoValue b (w' : ℂ) (c' : ℂ)⟫_ℂ =
      ((w * c' + c * w' + (projDeg X - 1) * (c * c') : ℝ) : ℂ) := by
  rw [inner_projTwoValue_ne hab]
  push_cast
  simp [Complex.conj_ofReal]

/-! ## Three-valued vectors and squared lengths -/

/-- The vector with value `w` at `a`, value `w'` at `b`, and value `c` at every other point. -/
def projThreeValue (a b : X) (w w' c : ℂ) : EuclideanSpace ℂ X :=
  (EuclideanSpace.equiv X ℂ).symm
    (fun x => if x = a then w else if x = b then w' else c)

omit [Fintype X] in
@[simp]
theorem projThreeValue_apply (a b : X) (w w' c : ℂ) (x : X) :
    projThreeValue a b w w' c x = if x = a then w else if x = b then w' else c := by
  simp [projThreeValue]

theorem norm_sq_projTwoValue (a : X) (w c : ℝ) :
    ‖projTwoValue a (w : ℂ) (c : ℂ)‖ ^ 2 = w ^ 2 + projDeg X * c ^ 2 := by
  have hnorm : ‖projTwoValue a (w : ℂ) (c : ℂ)‖ ^ 2 =
      RCLike.re (inner ℂ (projTwoValue a (w : ℂ) (c : ℂ)) (projTwoValue a (w : ℂ) (c : ℂ))) :=
    norm_sq_eq_re_inner _
  rw [hnorm, inner_projTwoValue_same_real]
  simp [pow_two]

theorem norm_sq_projThreeValue {a b : X} (hab : a ≠ b) (w w' c : ℝ) :
    ‖projThreeValue a b (w : ℂ) (w' : ℂ) (c : ℂ)‖ ^ 2 =
      w ^ 2 + w' ^ 2 + (projDeg X - 1) * c ^ 2 := by
  classical
  have hmemb : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
  have h2 : 2 ≤ Fintype.card X := by
    have hle : ({a, b} : Finset X).card ≤ Fintype.card X := Finset.card_le_univ _
    rwa [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton] at hle
  have hcard : ((Fintype.card X - 1 - 1 : ℕ) : ℝ) = projDeg X - 1 := by
    have h1 : 1 ≤ Fintype.card X := le_trans (by norm_num) h2
    rw [projDeg, Nat.cast_sub (by omega), Nat.cast_sub h1]
    norm_num
  have hsum : ∑ x : X, ‖projThreeValue a b (w : ℂ) (w' : ℂ) (c : ℂ) x‖ ^ 2 =
      w ^ 2 + w' ^ 2 + (projDeg X - 1) * c ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ hmemb]
    have htail : ∑ x ∈ (Finset.univ.erase a).erase b,
        ‖projThreeValue a b (w : ℂ) (w' : ℂ) (c : ℂ) x‖ ^ 2 =
        ∑ _x ∈ (Finset.univ.erase a).erase b, c ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
      have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      simp [hxa, hxb, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [htail, Finset.sum_const, Finset.card_erase_of_mem hmemb,
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, nsmul_eq_mul, hcard]
    simp only [projThreeValue_apply, if_true, if_neg hab, if_neg (Ne.symm hab)]
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun x _ => by positivity)]
  exact hsum

/-! ## The named projective vectors -/

/-- Normalization of the marked natural-cone vector. -/
def projNorm (X : Type*) [Fintype X] (z : ℝ) : ℝ := Real.sqrt (projDeg X + Real.exp (2 * z))

omit [Fintype X] [DecidableEq X] in
theorem exp_two_mul_eq (z : ℝ) : Real.exp (2 * z) = Real.exp z ^ 2 := by
  rw [two_mul, Real.exp_add, sq]

omit [DecidableEq X] in
theorem projNorm_pos (h : 2 ≤ Fintype.card X) (z : ℝ) : 0 < projNorm X z := by
  have hp := projDeg_pos (X := X) h
  exact Real.sqrt_pos.mpr (by positivity)

omit [DecidableEq X] in
theorem projNorm_sq (h : 2 ≤ Fintype.card X) (z : ℝ) :
    projNorm X z ^ 2 = projDeg X + Real.exp z ^ 2 := by
  have hp := projDeg_pos (X := X) h
  rw [projNorm, Real.sq_sqrt (by positivity), exp_two_mul_eq]

/-- Positive natural-cone vector with marked weight `e^z` at the point `a`. -/
def projNatural (a : X) (z : ℝ) : EuclideanSpace ℂ X :=
  projTwoValue a ((Real.exp z / projNorm X z : ℝ) : ℂ) ((1 / projNorm X z : ℝ) : ℂ)

/-- The constant vector. -/
def projConst (X : Type*) [Fintype X] (c : ℂ) : EuclideanSpace ℂ X :=
  (EuclideanSpace.equiv X ℂ).symm (fun _ => c)

omit [DecidableEq X] in
@[simp]
theorem projConst_apply (c : ℂ) (x : X) : projConst X c x = c := by
  simp [projConst]

theorem projTwoValue_self (a : X) (c : ℂ) : projTwoValue a c c = projConst X c := by
  refine PiLp.ext fun x => ?_
  by_cases hx : x = a <;> simp [hx]

/-- The uniform projective source vector: the critical squarefree state. -/
def projUniform (X : Type*) [Fintype X] : EuclideanSpace ℂ X :=
  projConst X ((1 / Real.sqrt (Fintype.card X) : ℝ) : ℂ)

omit [DecidableEq X] in
theorem projNorm_zero : projNorm X 0 = Real.sqrt (Fintype.card X) := by
  rw [projNorm]
  norm_num [projDeg_add_one X]

/-- **Equation (6).**  At the critical marked weight the natural-cone vector is the uniform
projective source vector, independently of the marked point. -/
theorem projNatural_zero (a : X) : projNatural a 0 = projUniform X := by
  rw [projNatural, projNorm_zero,
    show Real.exp 0 / Real.sqrt (Fintype.card X) = 1 / Real.sqrt (Fintype.card X) from by
      rw [Real.exp_zero]]
  unfold projUniform
  exact projTwoValue_self a _

/-- The unit transverse vector of the polarization at `a`, orthogonal to the source line. -/
def projTransverse (a : X) : EuclideanSpace ℂ X :=
  projTwoValue a ((Real.sqrt (projDeg X / (projDeg X + 1)) : ℝ) : ℂ)
    ((-(1 / Real.sqrt (projDeg X * (projDeg X + 1))) : ℝ) : ℂ)

/-! ## Norms and the transverse Gram seam -/

theorem norm_projNatural (h : 2 ≤ Fintype.card X) (a : X) (z : ℝ) :
    ‖projNatural a z‖ = 1 := by
  have hp := projDeg_pos (X := X) h
  have hN := projNorm_pos (X := X) h z
  have hsq := projNorm_sq (X := X) h z
  have hnorm : ‖projNatural a z‖ ^ 2 = 1 := by
    rw [projNatural, norm_sq_projTwoValue, div_pow, div_pow, hsq]
    field_simp
    ring
  have hnn : 0 ≤ ‖projNatural a z‖ := norm_nonneg _
  nlinarith [hnorm, hnn]

omit [DecidableEq X] in
theorem sq_sqrt_projDeg_div (h : 2 ≤ Fintype.card X) :
    Real.sqrt (projDeg X / (projDeg X + 1)) ^ 2 = projDeg X / (projDeg X + 1) := by
  have hp := projDeg_pos (X := X) h
  exact Real.sq_sqrt (by positivity)

omit [DecidableEq X] in
theorem sq_sqrt_projDeg_mul (h : 2 ≤ Fintype.card X) :
    Real.sqrt (projDeg X * (projDeg X + 1)) ^ 2 = projDeg X * (projDeg X + 1) := by
  have hp := projDeg_pos (X := X) h
  exact Real.sq_sqrt (by positivity)

theorem norm_projTransverse (h : 2 ≤ Fintype.card X) (a : X) :
    ‖projTransverse a‖ = 1 := by
  have hp := projDeg_pos (X := X) h
  have hnorm : ‖projTransverse a‖ ^ 2 = 1 := by
    rw [projTransverse, norm_sq_projTwoValue, sq_sqrt_projDeg_div (X := X) h,
      neg_pow, div_pow, sq_sqrt_projDeg_mul (X := X) h]
    field_simp
  have hnn : 0 ≤ ‖projTransverse a‖ := norm_nonneg _
  nlinarith [hnorm, hnn]

omit [DecidableEq X] in
theorem projTransverse_mul (h : 2 ≤ Fintype.card X) :
    Real.sqrt (projDeg X / (projDeg X + 1)) *
        (-(1 / Real.sqrt (projDeg X * (projDeg X + 1)))) = -(1 / (projDeg X + 1)) := by
  have hp := projDeg_pos (X := X) h
  have hp1 : (0 : ℝ) < projDeg X + 1 := by linarith
  set A : ℝ := Real.sqrt (projDeg X / (projDeg X + 1)) with hA
  set B : ℝ := Real.sqrt (projDeg X * (projDeg X + 1)) with hB
  have hApos : 0 < A := Real.sqrt_pos.mpr (by positivity)
  have hBpos : 0 < B := Real.sqrt_pos.mpr (by positivity)
  have hAsq : A ^ 2 = projDeg X / (projDeg X + 1) := sq_sqrt_projDeg_div (X := X) h
  have hBsq : B ^ 2 = projDeg X * (projDeg X + 1) := sq_sqrt_projDeg_mul (X := X) h
  have hprod : (A * (-(1 / B))) ^ 2 = (-(1 / (projDeg X + 1))) ^ 2 := by
    rw [mul_pow, neg_pow, div_pow, hAsq, hBsq, neg_pow]
    field_simp
  have hneg : A * (-(1 / B)) ≤ 0 := by
    have : 0 < A * (1 / B) := by positivity
    linarith
  have hfactor : (A * (-(1 / B)) + 1 / (projDeg X + 1)) *
      (A * (-(1 / B)) - 1 / (projDeg X + 1)) = 0 := by nlinarith [hprod]
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · linarith
  · exfalso
    have : 0 < 1 / (projDeg X + 1) := by positivity
    have heq : A * (-(1 / B)) = 1 / (projDeg X + 1) := by linarith
    linarith

/-- **Equation (8b).**  Two transverse projective lines overlap in the unsquared first-trace seam
`-1/p`. -/
theorem inner_projTransverse (h : 2 ≤ Fintype.card X) {a b : X} (hab : a ≠ b) :
    ⟪projTransverse a, projTransverse b⟫_ℂ = ((-(1 / projDeg X) : ℝ) : ℂ) := by
  have hp := projDeg_pos (X := X) h
  have hp1 : (0 : ℝ) < projDeg X + 1 := by linarith
  have hAC := projTransverse_mul (X := X) h
  have hCA : (-(1 / Real.sqrt (projDeg X * (projDeg X + 1)))) *
      Real.sqrt (projDeg X / (projDeg X + 1)) = -(1 / (projDeg X + 1)) := by
    rw [mul_comm]; exact hAC
  have hCC : (-(1 / Real.sqrt (projDeg X * (projDeg X + 1)))) *
      (-(1 / Real.sqrt (projDeg X * (projDeg X + 1)))) =
      1 / (projDeg X * (projDeg X + 1)) := by
    rw [neg_mul_neg, ← sq, div_pow, sq_sqrt_projDeg_mul (X := X) h]
    norm_num
  rw [projTransverse, projTransverse, inner_projTwoValue_ne_real hab]
  congr 1
  rw [hAC, hCA, hCC]
  field_simp
  ring

/-- **Equation (8c).**  The producer/reporter transverse Gram determinant is the safe squarefree
numerator `1 - p⁻²`. -/
theorem det_projTransverseGram (h : 2 ≤ Fintype.card X) {a b : X} (hab : a ≠ b) :
    (!![(1 : ℂ), ⟪projTransverse a, projTransverse b⟫_ℂ;
        ⟪projTransverse b, projTransverse a⟫_ℂ, 1]).det =
      ((1 - (projDeg X)⁻¹ ^ 2 : ℝ) : ℂ) := by
  have hp := projDeg_pos (X := X) h
  rw [Matrix.det_fin_two_of, inner_projTransverse (X := X) h hab,
    inner_projTransverse (X := X) h (Ne.symm hab)]
  push_cast
  field_simp

/-! ## The marked sign reflection and the Möbius phase -/

/-- The marked-point sign reflection `S_a = 1 - 2 |e_a⟩⟨e_a|`. -/
def projSignReflect (a : X) (v : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  (EuclideanSpace.equiv X ℂ).symm (fun x => if x = a then -(v x) else v x)

omit [Fintype X] in
@[simp]
theorem projSignReflect_apply (a : X) (v : EuclideanSpace ℂ X) (x : X) :
    projSignReflect a v x = if x = a then -(v x) else v x := by
  simp [projSignReflect]

theorem projSignReflect_projConst (a : X) (c : ℂ) :
    projSignReflect a (projConst X c) = projTwoValue a (-c) c := by
  refine PiLp.ext fun x => ?_
  by_cases hx : x = a <;> simp [hx]

theorem projUniform_eq_projTwoValue (a : X) :
    projUniform X = projTwoValue a ((1 / Real.sqrt (Fintype.card X) : ℝ) : ℂ)
      ((1 / Real.sqrt (Fintype.card X) : ℝ) : ℂ) :=
  (projTwoValue_self a _).symm

omit [DecidableEq X] in
theorem sq_inv_sqrt_card (h : 2 ≤ Fintype.card X) :
    (1 / Real.sqrt (Fintype.card X)) * (1 / Real.sqrt (Fintype.card X)) =
      1 / (projDeg X + 1) := by
  have hcard : (0 : ℝ) ≤ (Fintype.card X : ℝ) := by positivity
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hcard, projDeg_add_one]

/-- **Equation (8f).**  The critical source expectation of the marked sign reflection is the local
signed Plücker/Loschmidt factor `(p-1)/(p+1)`. -/
theorem inner_projUniform_signReflect (h : 2 ≤ Fintype.card X) (a : X) :
    ⟪projUniform X, projSignReflect a (projUniform X)⟫_ℂ =
      (((projDeg X - 1) / (projDeg X + 1) : ℝ) : ℂ) := by
  have hp := projDeg_pos (X := X) h
  have hp1 : (0 : ℝ) < projDeg X + 1 := by linarith
  have hk := sq_inv_sqrt_card (X := X) h
  rw [projUniform, projSignReflect_projConst, ← projTwoValue_self a,
    ← Complex.ofReal_neg, inner_projTwoValue_same_real]
  congr 1
  rw [show ((1 / Real.sqrt (Fintype.card X) : ℝ)) * (-(1 / Real.sqrt (Fintype.card X) : ℝ)) =
      -((1 / Real.sqrt (Fintype.card X)) * (1 / Real.sqrt (Fintype.card X))) from by ring, hk]
  field_simp
  ring

/-! ## The Hellinger affinity of two marked weights -/

/-- **Equation (11).**  The same-polarization Gram coefficient is exactly the Bernoulli Hellinger
affinity of the two marked-odds laws. -/
theorem inner_projNatural_same (h : 2 ≤ Fintype.card X) (a : X) (z y : ℝ) :
    ⟪projNatural a z, projNatural a y⟫_ℂ =
      (((projDeg X + Real.exp (z + y)) / (projNorm X z * projNorm X y) : ℝ) : ℂ) := by
  have hNz := projNorm_pos (X := X) h z
  have hNy := projNorm_pos (X := X) h y
  rw [projNatural, projNatural, inner_projTwoValue_same_real]
  congr 1
  rw [Real.exp_add]
  field_simp
  ring

/-! ## Point/complement polarizations -/

/-- The point/complement polarization at a marked projective point. -/
def projPolarization (a : X) : Submodule ℂ (EuclideanSpace ℂ X) :=
  Submodule.span ℂ {projTwoValue a 1 0, projTwoValue a 0 1}

omit [Fintype X] in
theorem mem_projPolarization_iff (a : X) (v : EuclideanSpace ℂ X) :
    v ∈ projPolarization a ↔ ∃ β : ℂ, ∀ x, x ≠ a → v x = β := by
  constructor
  · intro hv
    obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hv
    refine ⟨d, fun x hx => ?_⟩
    have := congrArg (fun w : EuclideanSpace ℂ X => w x) hcd
    simpa [hx] using this.symm
  · rintro ⟨β, hβ⟩
    have hv : v = v a • projTwoValue a 1 0 + β • projTwoValue a 0 1 := by
      refine PiLp.ext fun x => ?_
      by_cases hx : x = a
      · subst hx; simp
      · simp [hx, hβ x hx]
    rw [hv]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

omit [Fintype X] in
theorem projTwoValue_mem_projPolarization (a : X) (w c : ℂ) :
    projTwoValue a w c ∈ projPolarization a :=
  (mem_projPolarization_iff a _).mpr ⟨c, fun x hx => by simp [hx]⟩

theorem projUniform_mem_projPolarization (a : X) :
    projUniform X ∈ projPolarization a := by
  rw [projUniform_eq_projTwoValue a]
  exact projTwoValue_mem_projPolarization a _ _

theorem projNatural_mem_projPolarization (a : X) (z : ℝ) :
    projNatural a z ∈ projPolarization a :=
  projTwoValue_mem_projPolarization a _ _

theorem projTransverse_mem_projPolarization (a : X) :
    projTransverse a ∈ projPolarization a :=
  projTwoValue_mem_projPolarization a _ _

/-- **Equation (7).**  Two distinct point/complement polarizations meet exactly in the uniform
projective source line. -/
theorem projPolarization_inf (h3 : 3 ≤ Fintype.card X) {a b : X} (hab : a ≠ b) :
    projPolarization a ⊓ projPolarization b = Submodule.span ℂ {projUniform X} := by
  classical
  have hcardpos : (0 : ℕ) < Fintype.card X := lt_of_lt_of_le (by norm_num) h3
  have hkpos : (0 : ℝ) < 1 / Real.sqrt (Fintype.card X) := by
    have : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hcardpos
    positivity
  apply le_antisymm
  · rintro v ⟨hva, hvb⟩
    obtain ⟨βa, hβa⟩ := (mem_projPolarization_iff a v).mp hva
    obtain ⟨βb, hβb⟩ := (mem_projPolarization_iff b v).mp hvb
    obtain ⟨c, hc⟩ : ∃ c : X, c ≠ a ∧ c ≠ b := by
      by_contra hcon
      have hall : ∀ x : X, x = a ∨ x = b := by
        intro x
        by_cases hxa : x = a
        · exact Or.inl hxa
        · by_cases hxb : x = b
          · exact Or.inr hxb
          · exact absurd ⟨x, hxa, hxb⟩ hcon
      have hsub : (Finset.univ : Finset X) ⊆ {a, b} := by
        intro x _
        rcases hall x with hx | hx <;> simp [hx]
      have hcardle := Finset.card_le_card hsub
      rw [Finset.card_univ] at hcardle
      have hle : ({a, b} : Finset X).card ≤ 2 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        simp
      omega
    have hβ : βa = βb := by rw [← hβa c hc.1, hβb c hc.2]
    have hconst : ∀ x : X, v x = βa := by
      intro x
      rcases eq_or_ne x a with hx | hx
      · rw [hx, hβ]; exact hβb a hab
      · exact hβa x hx
    have hspos : (0 : ℝ) < Real.sqrt (Fintype.card X) := by
      have : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hcardpos
      positivity
    have hveq : v = (βa * ((Real.sqrt (Fintype.card X) : ℝ) : ℂ)) • projUniform X := by
      refine PiLp.ext fun x => ?_
      rw [hconst x]
      simp only [PiLp.smul_apply, projUniform, projConst_apply, smul_eq_mul]
      rw [mul_assoc, ← Complex.ofReal_mul,
        show Real.sqrt (Fintype.card X) * (1 / Real.sqrt (Fintype.card X)) = 1 from by
          field_simp]
      simp
    rw [hveq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨projUniform_mem_projPolarization a, projUniform_mem_projPolarization b⟩

end

end RHTower

namespace RHTower

noncomputable section

open Complex Finset
open scoped InnerProductSpace ComplexConjugate

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Point permutations act by unitaries carrying the whole package -/

/-- The unitary induced by a permutation of the projective points. -/
def projPermute (σ : Equiv.Perm X) : EuclideanSpace ℂ X ≃ₗᵢ[ℂ] EuclideanSpace ℂ X :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ

omit [DecidableEq X] in
@[simp]
theorem projPermute_apply (σ : Equiv.Perm X) (v : EuclideanSpace ℂ X) (x : X) :
    projPermute σ v x = v (σ.symm x) := rfl

theorem projPermute_projTwoValue (σ : Equiv.Perm X) (a : X) (w c : ℂ) :
    projPermute σ (projTwoValue a w c) = projTwoValue (σ a) w c := by
  refine PiLp.ext fun x => ?_
  rw [projPermute_apply, projTwoValue_apply, projTwoValue_apply]
  by_cases hx : x = σ a
  · rw [if_pos hx, if_pos (by rw [hx]; simp)]
  · have hne : σ.symm x ≠ a := fun hh => hx (by rw [← hh]; simp)
    rw [if_neg hx, if_neg hne]

omit [DecidableEq X] in
theorem projPermute_projConst (σ : Equiv.Perm X) (c : ℂ) :
    projPermute σ (projConst X c) = projConst X c := by
  refine PiLp.ext fun x => ?_
  simp

omit [DecidableEq X] in
/-- **Equation (8), source line.**  Every point permutation fixes the uniform source vector. -/
theorem projPermute_projUniform (σ : Equiv.Perm X) :
    projPermute σ (projUniform X) = projUniform X :=
  projPermute_projConst σ _

/-- **Equation (8), natural cone.** -/
theorem projPermute_projNatural (σ : Equiv.Perm X) (a : X) (z : ℝ) :
    projPermute σ (projNatural a z) = projNatural (σ a) z :=
  projPermute_projTwoValue σ a _ _

/-- **Equation (8), transverse line.** -/
theorem projPermute_projTransverse (σ : Equiv.Perm X) (a : X) :
    projPermute σ (projTransverse a) = projTransverse (σ a) :=
  projPermute_projTwoValue σ a _ _

/-- **Equation (8), polarization.** -/
theorem mem_projPolarization_permute (σ : Equiv.Perm X) (a : X) (v : EuclideanSpace ℂ X) :
    projPermute σ v ∈ projPolarization (σ a) ↔ v ∈ projPolarization a := by
  rw [mem_projPolarization_iff, mem_projPolarization_iff]
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨β, fun y hy => ?_⟩
    have hne : σ y ≠ σ a := fun hh => hy (σ.injective hh)
    simpa using hβ (σ y) hne
  · rintro ⟨β, hβ⟩
    refine ⟨β, fun x hx => ?_⟩
    have hne : σ.symm x ≠ a := fun hh => hx (by rw [← hh]; simp)
    simpa using hβ (σ.symm x) hne

/-- **Equation (8g).**  Weyl transport moves the whole marked sign-reflection package. -/
theorem projPermute_signReflect (σ : Equiv.Perm X) (a : X) (v : EuclideanSpace ℂ X) :
    projPermute σ (projSignReflect a v) = projSignReflect (σ a) (projPermute σ v) := by
  refine PiLp.ext fun x => ?_
  rw [projPermute_apply, projSignReflect_apply, projSignReflect_apply, projPermute_apply]
  by_cases hx : x = σ a
  · rw [if_pos hx, if_pos (by rw [hx]; simp)]
  · have hne : σ.symm x ≠ a := fun hh => hx (by rw [← hh]; simp)
    rw [if_neg hx, if_neg hne]

/-! ## Compression to a polarization and the exact Weyl leakage -/

/-- Compression of a vector to the polarization at `a`: keep the marked coordinate and replace
every other coordinate by their common mean. -/
def projCompress (a : X) (v : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  projTwoValue a (v a) (((projDeg X : ℂ))⁻¹ * ∑ x ∈ Finset.univ.erase a, v x)

theorem projCompress_mem (a : X) (v : EuclideanSpace ℂ X) :
    projCompress a v ∈ projPolarization a :=
  projTwoValue_mem_projPolarization a _ _

theorem card_erase_cast (h : 2 ≤ Fintype.card X) (a : X) :
    ((Finset.univ.erase a).card : ℂ) = (projDeg X : ℂ) := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
  have h1 : 1 ≤ Fintype.card X := le_trans (by norm_num) h
  have hr : ((Fintype.card X - 1 : ℕ) : ℝ) = projDeg X := by
    rw [projDeg, Nat.cast_sub h1]; norm_num
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hr

theorem sum_erase_projTwoValue {a b : X} (hab : a ≠ b) (h : 2 ≤ Fintype.card X) (w c : ℂ) :
    ∑ x ∈ Finset.univ.erase a, projTwoValue b w c x = w + ((projDeg X : ℂ) - 1) * c := by
  classical
  have hmemb : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
  have hcard : (((Finset.univ.erase a).erase b).card : ℂ) = (projDeg X : ℂ) - 1 := by
    have h1 : 1 ≤ Fintype.card X := le_trans (by norm_num) h
    have hr : ((Fintype.card X - 1 - 1 : ℕ) : ℝ) = projDeg X - 1 := by
      rw [projDeg, Nat.cast_sub (by omega), Nat.cast_sub h1]; norm_num
    rw [Finset.card_erase_of_mem hmemb, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ]
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hr
  rw [← Finset.add_sum_erase _ _ hmemb]
  have htail : ∑ x ∈ (Finset.univ.erase a).erase b, projTwoValue b w c x =
      ∑ _x ∈ (Finset.univ.erase a).erase b, c := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [projTwoValue_apply, if_neg (Finset.mem_erase.mp hx).1]
  rw [htail, Finset.sum_const, nsmul_eq_mul, hcard, projTwoValue_apply, if_pos rfl]

theorem sum_erase_sub_mean (h : 2 ≤ Fintype.card X) (a : X) (v : EuclideanSpace ℂ X) :
    ∑ x ∈ Finset.univ.erase a,
      (v x - ((projDeg X : ℂ))⁻¹ * ∑ y ∈ Finset.univ.erase a, v y) = 0 := by
  have hp : (0 : ℝ) < projDeg X := projDeg_pos (X := X) h
  have hpne : (projDeg X : ℂ) ≠ 0 := by
    simpa using (ne_of_gt hp)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, card_erase_cast (X := X) h a]
  field_simp
  ring

/-- The compression is the orthogonal projection onto the polarization. -/
theorem starProjection_projPolarization (h : 2 ≤ Fintype.card X) (a : X)
    (v : EuclideanSpace ℂ X) :
    (projPolarization a).starProjection v = projCompress a v := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (projCompress_mem a v) ?_
  intro w hw
  obtain ⟨β, hβ⟩ := (mem_projPolarization_iff a w).mp hw
  rw [PiLp.inner_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have hzero : (v - projCompress a v) a = 0 := by
    simp [projCompress]
  have hhead : (inner ℂ ((v - projCompress a v) a) (w a) : ℂ) = 0 := by
    rw [hzero]
    simp
  have htail : ∑ x ∈ Finset.univ.erase a,
      (inner ℂ ((v - projCompress a v) x) (w x) : ℂ) =
      conj (∑ x ∈ Finset.univ.erase a,
        (v x - ((projDeg X : ℂ))⁻¹ * ∑ y ∈ Finset.univ.erase a, v y)) * β := by
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxa : x ≠ a := (Finset.mem_erase.mp hx).1
    have hcx : projCompress a v x = ((projDeg X : ℂ))⁻¹ * ∑ y ∈ Finset.univ.erase a, v y := by
      simp [projCompress, hxa]
    rw [RCLike.inner_apply, hβ x hxa, PiLp.sub_apply, hcx]
    ring
  rw [hhead, htail, sum_erase_sub_mean (X := X) h a v]
  simp

/-! ## Exact Weyl leakage -/

/-- The exact compression leakage of a foreign natural-cone vector. -/
def projLeakageValue (X : Type*) [Fintype X] (z : ℝ) : ℝ :=
  (projDeg X - 1) / projDeg X * (Real.exp z - 1) ^ 2 / (projDeg X + Real.exp z ^ 2)

omit [DecidableEq X] in
@[simp]
theorem projLeakageValue_zero : projLeakageValue X 0 = 0 := by
  simp [projLeakageValue]

theorem projNatural_sub_compress (h : 2 ≤ Fintype.card X) {a b : X} (hab : a ≠ b) (z : ℝ) :
    projNatural b z - projCompress a (projNatural b z) =
      projThreeValue a b ((0 : ℝ) : ℂ)
        (((Real.exp z - 1) * (projDeg X - 1) / (projDeg X * projNorm X z) : ℝ) : ℂ)
        (((1 - Real.exp z) / (projDeg X * projNorm X z) : ℝ) : ℂ) := by
  have hp : (0 : ℝ) < projDeg X := projDeg_pos (X := X) h
  have hN : (0 : ℝ) < projNorm X z := projNorm_pos (X := X) h z
  have hpne : (projDeg X : ℂ) ≠ 0 := by simpa using (ne_of_gt hp)
  have hNne : ((projNorm X z : ℝ) : ℂ) ≠ 0 := by simpa using (ne_of_gt hN)
  have hva : projNatural b z a = ((1 / projNorm X z : ℝ) : ℂ) := by
    simp [projNatural, hab]
  have hsum : ∑ x ∈ Finset.univ.erase a, projNatural b z x =
      ((Real.exp z / projNorm X z : ℝ) : ℂ) +
        ((projDeg X : ℂ) - 1) * ((1 / projNorm X z : ℝ) : ℂ) :=
    sum_erase_projTwoValue hab h _ _
  refine PiLp.ext fun x => ?_
  simp only [PiLp.sub_apply, projCompress, projTwoValue_apply, projThreeValue_apply, hva, hsum]
  by_cases hxa : x = a
  · subst hxa
    simp [hab, projNatural]
  · rw [if_neg hxa]
    by_cases hxb : x = b
    · subst hxb
      rw [if_pos rfl, if_neg hxa]
      simp only [projNatural, projTwoValue_apply]
      push_cast
      field_simp
      ring
    · rw [if_neg hxb, if_neg hxa]
      simp only [projNatural, projTwoValue_apply, if_neg hxb]
      push_cast
      field_simp
      ring

/-- **Equation (9).**  The exact Weyl leakage of a foreign natural-cone vector through the
point/complement compression. -/
theorem projWeylLeakage (h : 2 ≤ Fintype.card X) {a b : X} (hab : a ≠ b) (z : ℝ) :
    ‖projNatural b z - projCompress a (projNatural b z)‖ ^ 2 = projLeakageValue X z := by
  have hp : (0 : ℝ) < projDeg X := projDeg_pos (X := X) h
  have hN : (0 : ℝ) < projNorm X z := projNorm_pos (X := X) h z
  have hNsq := projNorm_sq (X := X) h z
  rw [projNatural_sub_compress (X := X) h hab z, norm_sq_projThreeValue hab]
  rw [projLeakageValue, ← hNsq]
  field_simp
  ring

/-- **Equation (10).**  The compressed norm is the complementary Hellinger weight. -/
theorem projWeylCompressionNorm (h : 2 ≤ Fintype.card X) {a b : X} (hab : a ≠ b) (z : ℝ) :
    ‖projCompress a (projNatural b z)‖ ^ 2 = 1 - projLeakageValue X z := by
  have hp : (0 : ℝ) < projDeg X := projDeg_pos (X := X) h
  have hN : (0 : ℝ) < projNorm X z := projNorm_pos (X := X) h z
  have hNsq := projNorm_sq (X := X) h z
  have hva : projNatural b z a = ((1 / projNorm X z : ℝ) : ℂ) := by
    simp [projNatural, hab]
  have hsum : ∑ x ∈ Finset.univ.erase a, projNatural b z x =
      ((Real.exp z / projNorm X z : ℝ) : ℂ) +
        ((projDeg X : ℂ) - 1) * ((1 / projNorm X z : ℝ) : ℂ) :=
    sum_erase_projTwoValue hab h _ _
  have hcomp : projCompress a (projNatural b z) =
      projTwoValue a ((1 / projNorm X z : ℝ) : ℂ)
        (((Real.exp z + projDeg X - 1) / (projDeg X * projNorm X z) : ℝ) : ℂ) := by
    rw [projCompress, hva, hsum]
    congr 1
    have hpne : (projDeg X : ℂ) ≠ 0 := by simpa using (ne_of_gt hp)
    have hNne : ((projNorm X z : ℝ) : ℂ) ≠ 0 := by simpa using (ne_of_gt hN)
    push_cast
    field_simp
    ring
  rw [hcomp, norm_sq_projTwoValue, projLeakageValue, div_pow, div_pow, mul_pow, hNsq]
  field_simp
  ring

omit [DecidableEq X] in
/-- The critical state has zero leakage; every noncritical real radial state leaks. -/
theorem projLeakageValue_pos (h3 : 3 ≤ Fintype.card X) {z : ℝ} (hz : z ≠ 0) :
    0 < projLeakageValue X z := by
  have hp : (1 : ℝ) < projDeg X := by
    rw [projDeg]
    have : (3 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast h3
    linarith
  have hE : Real.exp z ≠ 1 := by
    intro hcon
    have hz0 : Real.exp z = Real.exp 0 := by rw [hcon, Real.exp_zero]
    exact hz (Real.exp_eq_exp.mp hz0)
  have hEsub : (Real.exp z - 1) ^ 2 > 0 := by positivity
  have hden : (0 : ℝ) < projDeg X + Real.exp z ^ 2 := by positivity
  rw [projLeakageValue]
  have hnum : 0 < (projDeg X - 1) / projDeg X := by
    apply div_pos <;> linarith
  positivity

/-! ## The marked-weight tangent is the squarefree Fisher direction -/

omit [Fintype X] in
theorem projTwoValue_eq_smul_add (a : X) (w c : ℂ) :
    projTwoValue a w c = w • projTwoValue a 1 0 + c • projTwoValue a 0 1 := by
  refine PiLp.ext fun x => ?_
  by_cases hx : x = a <;> simp [hx]

omit [DecidableEq X] in
theorem projNorm_zero_eq : projNorm X 0 = Real.sqrt (projDeg X + 1) := by
  rw [projNorm]
  norm_num

omit [DecidableEq X] in
theorem hasDerivAt_projNorm (h : 2 ≤ Fintype.card X) (z : ℝ) :
    HasDerivAt (fun t : ℝ => projNorm X t) (Real.exp (2 * z) / projNorm X z) z := by
  have hp := projDeg_pos (X := X) h
  have hne : projDeg X + Real.exp (2 * z) ≠ 0 := by positivity
  have hid : HasDerivAt (fun t : ℝ => (2 : ℝ) * t) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℝ)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (2 * t)) (2 * Real.exp (2 * z)) z := by
    simpa [mul_comm] using hid.exp
  have hg : HasDerivAt (fun t : ℝ => projDeg X + Real.exp (2 * t))
      (2 * Real.exp (2 * z)) z := by
    simpa using hexp.const_add (projDeg X)
  have hcomp : HasDerivAt (fun t : ℝ => Real.sqrt (projDeg X + Real.exp (2 * t)))
      (1 / (2 * Real.sqrt (projDeg X + Real.exp (2 * z))) * (2 * Real.exp (2 * z))) z := by
    simpa [Function.comp_def] using (Real.hasDerivAt_sqrt hne).comp z hg
  have hfinal : HasDerivAt (fun t : ℝ => projNorm X t)
      (1 / (2 * projNorm X z) * (2 * Real.exp (2 * z))) z := hcomp
  have hNpos : 0 < projNorm X z := projNorm_pos (X := X) h z
  refine hfinal.congr_deriv ?_
  field_simp

/-- **Equation (8d).**  The marked-weight tangent of the natural cone at the critical point. -/
theorem hasDerivAt_projNatural_zero (h : 2 ≤ Fintype.card X) (a : X) :
    HasDerivAt (fun z : ℝ => projNatural a z)
      (projTwoValue a
        ((projDeg X / ((projDeg X + 1) * Real.sqrt (projDeg X + 1)) : ℝ) : ℂ)
        ((-(1 / ((projDeg X + 1) * Real.sqrt (projDeg X + 1))) : ℝ) : ℂ)) 0 := by
  have hp := projDeg_pos (X := X) h
  have hp1 : (0 : ℝ) < projDeg X + 1 := by linarith
  have hN0 : projNorm X 0 = Real.sqrt (projDeg X + 1) := projNorm_zero_eq (X := X)
  have hspos : (0 : ℝ) < Real.sqrt (projDeg X + 1) := Real.sqrt_pos.mpr hp1
  have hssq : Real.sqrt (projDeg X + 1) ^ 2 = projDeg X + 1 := Real.sq_sqrt (le_of_lt hp1)
  have hNpos : (0 : ℝ) < projNorm X 0 := projNorm_pos (X := X) h 0
  have hNne : projNorm X 0 ≠ 0 := ne_of_gt hNpos
  have hNderiv' : HasDerivAt (fun t : ℝ => projNorm X t) (1 / Real.sqrt (projDeg X + 1)) 0 := by
    refine (hasDerivAt_projNorm (X := X) h 0).congr_deriv ?_
    rw [hN0]
    norm_num
  have hexp0 : HasDerivAt (fun t : ℝ => Real.exp t) (Real.exp 0) 0 := Real.hasDerivAt_exp 0
  have hf : HasDerivAt (fun t : ℝ => Real.exp t / projNorm X t)
      (projDeg X / ((projDeg X + 1) * Real.sqrt (projDeg X + 1))) 0 := by
    refine (hexp0.div hNderiv' hNne).congr_deriv ?_
    rw [hN0]
    field_simp
    rw [hssq]
    simp only [Real.exp_zero]
    ring
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := hasDerivAt_const 0 1
  have hg : HasDerivAt (fun t : ℝ => 1 / projNorm X t)
      (-(1 / ((projDeg X + 1) * Real.sqrt (projDeg X + 1)))) 0 := by
    refine (hconst.div hNderiv' hNne).congr_deriv ?_
    rw [hN0]
    field_simp
    rw [hssq]
    ring
  have hfC : HasDerivAt (fun t : ℝ => ((Real.exp t / projNorm X t : ℝ) : ℂ))
      (((projDeg X / ((projDeg X + 1) * Real.sqrt (projDeg X + 1)) : ℝ) : ℂ)) 0 :=
    hf.ofReal_comp
  have hgC : HasDerivAt (fun t : ℝ => ((1 / projNorm X t : ℝ) : ℂ))
      (((-(1 / ((projDeg X + 1) * Real.sqrt (projDeg X + 1))) : ℝ) : ℂ)) 0 :=
    hg.ofReal_comp
  have hsum : HasDerivAt (fun z : ℝ => projNatural a z)
      (((projDeg X / ((projDeg X + 1) * Real.sqrt (projDeg X + 1)) : ℝ) : ℂ) •
          projTwoValue a 1 0 +
        ((-(1 / ((projDeg X + 1) * Real.sqrt (projDeg X + 1))) : ℝ) : ℂ) •
          projTwoValue a 0 1) 0 := by
    have hbase := (hfC.smul_const (projTwoValue a 1 0)).add (hgC.smul_const (projTwoValue a 0 1))
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [] with z
    rw [projNatural]
    exact projTwoValue_eq_smul_add a _ _
  refine hsum.congr_deriv ?_
  exact (projTwoValue_eq_smul_add a _ _).symm

/-- The critical tangent is exactly the transverse projective direction, scaled by `√p/(p+1)`. -/
theorem projNatural_deriv_eq_transverse (h : 2 ≤ Fintype.card X) (a : X) :
    projTwoValue a
        ((projDeg X / ((projDeg X + 1) * Real.sqrt (projDeg X + 1)) : ℝ) : ℂ)
        ((-(1 / ((projDeg X + 1) * Real.sqrt (projDeg X + 1))) : ℝ) : ℂ) =
      ((Real.sqrt (projDeg X) / (projDeg X + 1) : ℝ) : ℂ) • projTransverse a := by
  have hp := projDeg_pos (X := X) h
  have hp1 : (0 : ℝ) < projDeg X + 1 := by linarith
  have hspos : (0 : ℝ) < Real.sqrt (projDeg X + 1) := Real.sqrt_pos.mpr hp1
  have hppos : (0 : ℝ) < Real.sqrt (projDeg X) := Real.sqrt_pos.mpr hp
  have hsne : Real.sqrt (projDeg X + 1) ≠ 0 := ne_of_gt hspos
  have hpne : Real.sqrt (projDeg X) ≠ 0 := ne_of_gt hppos
  have hpsq : Real.sqrt (projDeg X) * Real.sqrt (projDeg X) = projDeg X :=
    Real.mul_self_sqrt (le_of_lt hp)
  have hdiv : Real.sqrt (projDeg X / (projDeg X + 1)) =
      Real.sqrt (projDeg X) / Real.sqrt (projDeg X + 1) :=
    Real.sqrt_div (le_of_lt hp) _
  have hmul : Real.sqrt (projDeg X * (projDeg X + 1)) =
      Real.sqrt (projDeg X) * Real.sqrt (projDeg X + 1) :=
    Real.sqrt_mul (le_of_lt hp) _
  have hA : Real.sqrt (projDeg X) / (projDeg X + 1) *
      Real.sqrt (projDeg X / (projDeg X + 1)) =
      projDeg X / ((projDeg X + 1) * Real.sqrt (projDeg X + 1)) := by
    rw [hdiv, div_mul_div_comm, hpsq]
  have hC : Real.sqrt (projDeg X) / (projDeg X + 1) *
      (-(1 / Real.sqrt (projDeg X * (projDeg X + 1)))) =
      -(1 / ((projDeg X + 1) * Real.sqrt (projDeg X + 1))) := by
    rw [hmul]
    field_simp
  refine PiLp.ext fun x => ?_
  simp only [PiLp.smul_apply, projTransverse, projTwoValue_apply, smul_eq_mul]
  by_cases hx : x = a
  · rw [if_pos hx, if_pos hx, ← Complex.ofReal_mul, hA]
  · rw [if_neg hx, if_neg hx, ← Complex.ofReal_mul, hC]

/-- **Equation (8d), capacity.**  The squared length of the critical tangent is the squarefree
Fisher capacity `p/(p+1)²`. -/
theorem norm_sq_projNatural_deriv (h : 2 ≤ Fintype.card X) (a : X) :
    ‖projTwoValue a
        ((projDeg X / ((projDeg X + 1) * Real.sqrt (projDeg X + 1)) : ℝ) : ℂ)
        ((-(1 / ((projDeg X + 1) * Real.sqrt (projDeg X + 1))) : ℝ) : ℂ)‖ ^ 2 =
      projDeg X / (projDeg X + 1) ^ 2 := by
  have hp := projDeg_pos (X := X) h
  have hp1 : (0 : ℝ) < projDeg X + 1 := by linarith
  have hspos : (0 : ℝ) < Real.sqrt (projDeg X + 1) := Real.sqrt_pos.mpr hp1
  have hssq : Real.sqrt (projDeg X + 1) ^ 2 = projDeg X + 1 := Real.sq_sqrt (le_of_lt hp1)
  rw [norm_sq_projTwoValue, div_pow, mul_pow, hssq, neg_pow, div_pow, mul_pow, hssq]
  field_simp

end

end RHTower
