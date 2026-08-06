import GaloisForLFunctions.HTGeometry.TwoCylinderDifferential

/-!
# Dilated cotangent models on separated orbits

The external orbit of a double-sine defect consists of translates of the source, and in the
cylinder coordinate a translate is a dilation.  The Euler operator commutes with dilations, so the
Euler-operator combination of a dilated cotangent model is the dilate of the combination, and its
only pole sits at the dilated fixed point.

Hence a finite family of dilated cotangent models, one of whose poles lies on a multiplicative
orbit disjoint from all the others, has exactly one pole on that orbit; the multiplicative-orbit
residue obstruction then forbids the family from being a `q`-difference of a rational function.

This is the separated form of the defect obstruction: it is what distinguishes translates in
distinct classes modulo the period lattice.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

noncomputable section

/-! ### Dilation and the derivation -/

theorem polyScale_derivative (q : K) (p : Polynomial K) :
    Polynomial.derivative (polyScale q p) = C q * polyScale q (Polynomial.derivative p) := by
  rw [polyScale_eq_comp, polyScale_eq_comp, Polynomial.derivative_comp]
  have hd : Polynomial.derivative (C q * X : Polynomial K) = C q := by
    simp
  rw [hd]

theorem ratFuncScale_algebraMap (q : K) (hq : q ≠ 0) (p : Polynomial K) :
    ratFuncScale q hq (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) (polyScale q p) := by
  have h := ratFuncScale_div q hq p 1
  rw [map_one] at h
  set A : RatFunc K := algebraMap (Polynomial K) (RatFunc K) p with hA
  set B : RatFunc K := algebraMap (Polynomial K) (RatFunc K) (polyScale q p) with hB
  have h1 : A / 1 = A := div_one A
  have h2 : B / algebraMap (Polynomial K) (RatFunc K) (polyScale q 1) = B := by
    rw [map_one, map_one, div_one]
  rw [h1, h2] at h
  exact h

/-- **The derivation transforms by the chain rule under dilation.** -/
theorem ratFuncDerivative_ratFuncScale (q : K) (hq : q ≠ 0) (f : RatFunc K) :
    ratFuncDerivative K (ratFuncScale q hq f)
      = algebraMap K (RatFunc K) q * ratFuncScale q hq (ratFuncDerivative K f) := by
  classical
  have hD : ∀ x y : RatFunc K,
      ratFuncDerivative K (x * y) = x * ratFuncDerivative K y + y * ratFuncDerivative K x := by
    intro x y
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hpoly : ∀ p : Polynomial K,
      ratFuncDerivative K (ratFuncScale q hq (algebraMap (Polynomial K) (RatFunc K) p))
        = algebraMap K (RatFunc K) q *
          ratFuncScale q hq (ratFuncDerivative K (algebraMap (Polynomial K) (RatFunc K) p)) := by
    intro p
    rw [ratFuncScale_algebraMap, ratFuncDerivative_algebraMap, ratFuncDerivative_algebraMap,
      ratFuncScale_algebraMap, polyScale_derivative, map_mul, algebraMap_ratFunc_eq_polynomialC]
  refine RatFunc.induction_on (P := fun f => ratFuncDerivative K (ratFuncScale q hq f)
      = algebraMap K (RatFunc K) q * ratFuncScale q hq (ratFuncDerivative K f)) f ?_
  intro p s hs
  set A : RatFunc K := algebraMap (Polynomial K) (RatFunc K) p with hAdef
  set B : RatFunc K := algebraMap (Polynomial K) (RatFunc K) s with hBdef
  have hB : B ≠ 0 := RatFunc.algebraMap_ne_zero hs
  have hSB : ratFuncScale q hq B ≠ 0 := by
    rw [hBdef, ratFuncScale_algebraMap]
    refine RatFunc.algebraMap_ne_zero ?_
    intro hcon
    exact hs (polyScale_injective hq (by rw [hcon, map_zero]))
  have hscaledDiv : ratFuncScale q hq (A / B)
      = ratFuncScale q hq A / ratFuncScale q hq B := map_div₀ (ratFuncScale q hq) A B
  have hDA := hpoly p
  have hDB := hpoly s
  rw [← hAdef] at hDA
  rw [← hBdef] at hDB
  have hpush : ratFuncScale q hq
        ((ratFuncDerivative K A * B - A * ratFuncDerivative K B) / B ^ 2)
      = (ratFuncScale q hq (ratFuncDerivative K A) * ratFuncScale q hq B
          - ratFuncScale q hq A * ratFuncScale q hq (ratFuncDerivative K B))
        / (ratFuncScale q hq B) ^ 2 := by
    rw [map_div₀ (ratFuncScale q hq) (ratFuncDerivative K A * B - A * ratFuncDerivative K B)
      (B ^ 2), map_sub, map_mul, map_mul, map_pow]
  rw [hscaledDiv, leibniz_div (ratFuncDerivative K) hD hSB,
    leibniz_div (ratFuncDerivative K) hD hB, hDA, hDB, hpush]
  field_simp

/-- **The Euler operator commutes with dilation.** -/
theorem ratFuncEulerOp_ratFuncScale (q : K) (hq : q ≠ 0) (f : RatFunc K) :
    ratFuncEulerOp (ratFuncScale q hq f) = ratFuncScale q hq (ratFuncEulerOp f) := by
  have hX : ratFuncScale q hq (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
      = algebraMap K (RatFunc K) q * algebraMap (Polynomial K) (RatFunc K) Polynomial.X := by
    rw [ratFuncScale_algebraMap, polyScale_X, map_mul, algebraMap_ratFunc_eq_polynomialC]
  rw [ratFuncEulerOp, ratFuncEulerOp, map_mul, hX, ratFuncDerivative_ratFuncScale]
  ring

theorem ratFuncEulerOp_iterate_ratFuncScale (q : K) (hq : q ≠ 0) (n : ℕ) (f : RatFunc K) :
    ratFuncEulerOp^[n] (ratFuncScale q hq f) = ratFuncScale q hq (ratFuncEulerOp^[n] f) := by
  induction n generalizing f with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        ratFuncEulerOp_ratFuncScale, ih]

theorem eulerCombination_ratFuncScale (q : K) (hq : q ≠ 0) (a : ℕ → K) (r : ℕ) (f : RatFunc K) :
    eulerCombination a r (ratFuncScale q hq f) = ratFuncScale q hq (eulerCombination a r f) := by
  rw [eulerCombination, eulerCombination, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ratFuncEulerOp_iterate_ratFuncScale]
  congr 1
  rw [ratFuncScale_algebraMap, polyScale_eq_comp, Polynomial.C_comp]

/-! ### Regularity helpers -/

theorem regularAt_zero (c : K) : RegularAt (0 : RatFunc K) c := ⟨0, 1, by simp, by simp⟩

theorem regularAt_finsetSum {ι : Type*} [DecidableEq ι] (t : Finset ι) (F : ι → RatFunc K)
    {w : K} (h : ∀ i ∈ t, RegularAt (F i) w) : RegularAt (∑ i ∈ t, F i) w := by
  classical
  induction t using Finset.induction with
  | empty => simpa using regularAt_zero w
  | insert i t hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i t)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem not_regularAt_add_left {x y : RatFunc K} {c : K} (hx : ¬ RegularAt x c)
    (hy : RegularAt y c) : ¬ RegularAt (x + y) c := by
  intro h
  exact hx (by simpa using h.sub hy)

/-! ### The pole of a dilated combination -/

theorem not_regularAt_scaled_eulerCombination_cotModel [CharZero K] (a : ℕ → K) {s c : K}
    (hs : s ≠ 0) (hc : c ≠ 0) (r : ℕ) (har : a r ≠ 0) :
    ¬ RegularAt (ratFuncScale s hs (eulerCombination a r (cotModel c))) s⁻¹ := by
  rw [regularAt_ratFuncScale, mul_inv_cancel₀ hs]
  exact not_regularAt_one_eulerCombination_cotModel a c hc r har

theorem regularAt_scaled_eulerCombination_cotModel (a : ℕ → K) {s c : K} (hs : s ≠ 0)
    (r : ℕ) {w : K} (hw : w ≠ s⁻¹) :
    RegularAt (ratFuncScale s hs (eulerCombination a r (cotModel c))) w := by
  rw [regularAt_ratFuncScale]
  refine regularAt_of_ne_one_eulerCombination_cotModel a c r ?_
  intro hcon
  refine hw ?_
  field_simp
  linear_combination hcon

/-! ### The separated family obstruction -/

/-- **The separated defect obstruction.**  A finite family of dilated cotangent models, one of
whose poles lies on a multiplicative orbit disjoint from the poles of all the others, is not a
`q`-difference of a rational function. -/
theorem not_dilationTelescoped_separated_family [CharZero K]
    (q : K) (hq : q ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    {ι : Type*} [DecidableEq ι] (t : Finset ι) (σ : ι → K) (hσ : ∀ i, σ i ≠ 0)
    (a : ι → ℕ → K) (r : ι → ℕ) (c : ι → K)
    {i₀ : ι} (hi₀ : i₀ ∈ t) (hc₀ : c i₀ ≠ 0) (har : a i₀ (r i₀) ≠ 0)
    (hsep : ∀ j ∈ t, j ≠ i₀ → ∀ n : ℤ, (σ i₀)⁻¹ * q ^ n ≠ (σ j)⁻¹) :
    ¬ ∃ h : RatFunc K,
      (∑ i ∈ t, ratFuncScale (σ i) (hσ i)
          (eulerCombination (a i) (r i) (cotModel (c i))))
        = ratFuncScale q hq h - h := by
  classical
  set F : ι → RatFunc K := fun i =>
    ratFuncScale (σ i) (hσ i) (eulerCombination (a i) (r i) (cotModel (c i))) with hF
  have hother : ∀ (n : ℤ), ∀ j ∈ t, j ≠ i₀ → RegularAt (F j) ((σ i₀)⁻¹ * q ^ n) := by
    intro n j hj hne
    refine regularAt_scaled_eulerCombination_cotModel (a j) (hσ j) (r j) ?_
    exact hsep j hj hne n
  have hsum : ∀ n : ℤ, n ≠ 0 → RegularAt (∑ i ∈ t, F i) ((σ i₀)⁻¹ * q ^ n) := by
    intro n hn
    refine regularAt_finsetSum _ _ ?_
    intro j hj
    by_cases hje : j = i₀
    · subst hje
      refine regularAt_scaled_eulerCombination_cotModel (a j) (hσ j) (r j) ?_
      intro hcon
      have hqn : q ^ n = 1 := by
        refine mul_left_cancel₀ (inv_ne_zero (hσ j)) ?_
        rw [mul_one]
        exact hcon
      exact hqtor n hn hqn
    · exact hother n j hj hje
  have hzero : ¬ RegularAt (∑ i ∈ t, F i) ((σ i₀)⁻¹) := by
    have hsplit : ∑ i ∈ t, F i = F i₀ + ∑ i ∈ t.erase i₀, F i := by
      rw [← Finset.add_sum_erase t F hi₀]
    rw [hsplit]
    refine not_regularAt_add_left ?_ ?_
    · exact not_regularAt_scaled_eulerCombination_cotModel (a i₀) (hσ i₀) hc₀ (r i₀) har
    · refine regularAt_finsetSum _ _ ?_
      intro j hj
      have hjt : j ∈ t := Finset.mem_of_mem_erase hj
      have hjne : j ≠ i₀ := (Finset.mem_erase.mp hj).1
      simpa using hother 0 j hjt hjne
  refine not_dilationTelescoped_of_unique_multOrbit_pole q ((σ i₀)⁻¹) hq
    (inv_ne_zero (hσ i₀)) hqtor _ hzero ?_
  intro n hn
  exact hsum n hn

end

end GaloisForLFunctions.HTGeometry
