import GaloisForLFunctions.HTGeometry.ParabolicLaurentFrame

/-!
# Iterates of a parabolic germ and their formal generator

Let `r = X·(1 + a X^k + X^{k+1} w)`, `k ≥ 1`, and `C f = f(r)`.  The difference operator
`D = C − 1` raises the `X`-adic order, so `Cⁿ = Σ_m binom(n, m) D^m` and every coefficient of the
iterate `Cⁿ f` is a polynomial in `n`.

* **Flows.**  These polynomials assemble into a power series `flow f` with coefficients in `ℂ[t]`
  whose value at `t = n` is `Cⁿ f`; a power series over `ℂ[t]` vanishing at infinitely many
  integers is zero.
* **The generator.**  The coefficient of `t` of `flow f` is a derivation `L` of `ℂ⟦X⟧` (the flow
  of a product is the product of the flows), hence `L = X_g·d/dX` with `X_g = L X = a X^{k+1} + …`;
  it commutes with `C`, so `X_g(r) = r'·X_g`.
* **Lowest order.**  If one nonzero polynomial `T` vanishes on the jets `(z, Cⁿ z, (Cⁿ z)′, …)` for
  infinitely many `n`, it vanishes along the flow `z + t·H` (`H(0) = X_g`), and the lowest
  `t`-order part is a nonzero relation among the jets of `X_g`.
* **Ritt's implication.**  Then `1/X_g` is a differentially algebraic eigen-coordinate
  (`v(r) = v/r'`) in formal Laurent series, and `R` carries a rational cocycle.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k : ℕ} {a : ℂ} {w : ℂ⟦X⟧}

/-! ### The difference operator -/

/-- The difference operator `D f = f(r) − f`. -/
def parDiff (k : ℕ) (a : ℂ) (w : ℂ⟦X⟧) : Module.End ℂ ℂ⟦X⟧ := (parSubst k a w).toLinearMap - 1

theorem parDiff_apply (f : ℂ⟦X⟧) : parDiff k a w f = parSubst k a w f - f := rfl

/-- **The difference operator raises the order.** -/
theorem X_pow_succ_dvd_parDiff (hk : 1 ≤ k) {i : ℕ} {f : ℂ⟦X⟧} (hf : (X : ℂ⟦X⟧) ^ i ∣ f) :
    (X : ℂ⟦X⟧) ^ (i + 1) ∣ parDiff k a w f := by
  have h := X_pow_dvd_parSubst_sub_lead (a := a) (w := w) hk hf
  have h2 : (X : ℂ⟦X⟧) ^ (i + 1) ∣ C ((i : ℂ) * a * coeff i f) * X ^ (i + k) :=
    dvd_mul_of_dvd_right (pow_dvd_pow _ (by omega)) _
  have h3 : (X : ℂ⟦X⟧) ^ (i + 1) ∣ X ^ (i + k + 1) := pow_dvd_pow _ (by omega)
  rw [parDiff_apply]
  have := dvd_add (h3.trans h) h2
  rwa [sub_add_cancel] at this

theorem X_pow_add_dvd_parDiff_pow (hk : 1 ≤ k) {i : ℕ} {f : ℂ⟦X⟧} (hf : (X : ℂ⟦X⟧) ^ i ∣ f)
    (m : ℕ) : (X : ℂ⟦X⟧) ^ (i + m) ∣ (parDiff k a w ^ m) f := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ← add_assoc]
      exact X_pow_succ_dvd_parDiff hk ih

theorem X_pow_dvd_parDiff_pow (hk : 1 ≤ k) (m : ℕ) (f : ℂ⟦X⟧) :
    (X : ℂ⟦X⟧) ^ m ∣ (parDiff k a w ^ m) f := by
  simpa using X_pow_add_dvd_parDiff_pow (a := a) (w := w) hk (i := 0) (by simp) m

theorem coeff_parDiff_pow_eq_zero (hk : 1 ≤ k) {j m : ℕ} (hjm : j < m) (f : ℂ⟦X⟧) :
    coeff j ((parDiff k a w ^ m) f) = 0 :=
  X_pow_dvd_iff.mp (X_pow_dvd_parDiff_pow hk m f) j hjm

/-- **The binomial expansion of an iterate.** -/
theorem parSubst_iterate_eq_sum (n : ℕ) (f : ℂ⟦X⟧) :
    (parSubst k a w)^[n] f
      = ∑ m ∈ Finset.range (n + 1), ((n.choose m : ℕ) : ℂ) • (parDiff k a w ^ m) f := by
  have hC : (parSubst k a w).toLinearMap = parDiff k a w + 1 := by rw [parDiff]; abel
  have hpow := (Commute.one_right (parDiff k a w)).add_pow n
  have h1 : (parSubst k a w)^[n] f = ((parSubst k a w).toLinearMap ^ n) f := by
    rw [Module.End.pow_apply]; rfl
  rw [h1, hC, hpow, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_pow, mul_one, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul,
    Nat.cast_smul_eq_nsmul]

/-! ### Binomial polynomials -/

/-- The binomial polynomial `binom(t, m)`. -/
def binomPoly (m : ℕ) : Polynomial ℂ := Polynomial.C ((m.factorial : ℂ)⁻¹) * descPochhammer ℂ m

theorem binomPoly_eval (m n : ℕ) : (binomPoly m).eval (n : ℂ) = n.choose m := by
  rw [binomPoly, Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  field_simp

/-! ### Flows over `ℂ[t]` -/

/-- Evaluation of the parameter. -/
def flowEval (c : ℂ) : PowerSeries (Polynomial ℂ) →+* ℂ⟦X⟧ :=
  PowerSeries.map (Polynomial.evalRingHom c)

theorem coeff_flowEval (c : ℂ) (j : ℕ) (F : PowerSeries (Polynomial ℂ)) :
    coeff j (flowEval c F) = (coeff j F).eval c := by
  rw [flowEval, coeff_map, Polynomial.coe_evalRingHom]

/-- **A flow vanishing at infinitely many integers is zero.** -/
theorem eq_zero_of_flowEval_eq_zero {F : PowerSeries (Polynomial ℂ)} {S : Set ℕ} (hS : S.Infinite)
    (h : ∀ n ∈ S, flowEval n F = 0) : F = 0 := by
  refine PowerSeries.ext fun j => ?_
  rw [map_zero]
  refine Polynomial.eq_zero_of_infinite_isRoot (coeff j F) ?_
  refine Set.Infinite.mono ?_ (hS.image (Nat.cast_injective (R := ℂ)).injOn)
  rintro _ ⟨n, hn, rfl⟩
  show (coeff j F).eval (n : ℂ) = 0
  rw [← coeff_flowEval, h n hn, map_zero]

/-- The flow of a power series: the power series over `ℂ[t]` whose value at `t = n` is `Cⁿ f`. -/
def flow (k : ℕ) (a : ℂ) (w : ℂ⟦X⟧) (f : ℂ⟦X⟧) : PowerSeries (Polynomial ℂ) :=
  PowerSeries.mk fun j => ∑ m ∈ Finset.range (j + 1),
    binomPoly m * Polynomial.C (coeff j ((parDiff k a w ^ m) f))

theorem coeff_flow (j : ℕ) (f : ℂ⟦X⟧) :
    coeff j (flow k a w f) = ∑ m ∈ Finset.range (j + 1),
      binomPoly m * Polynomial.C (coeff j ((parDiff k a w ^ m) f)) := by
  rw [flow, coeff_mk]

/-- **The flow evaluates to the iterates.** -/
theorem flowEval_flow (hk : 1 ≤ k) (n : ℕ) (f : ℂ⟦X⟧) :
    flowEval n (flow k a w f) = (parSubst k a w)^[n] f := by
  refine PowerSeries.ext fun j => ?_
  rw [coeff_flowEval, coeff_flow, parSubst_iterate_eq_sum, map_sum]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, binomPoly_eval,
    map_smul, smul_eq_mul]
  have hL : ∑ m ∈ Finset.range (j + 1), ((n.choose m : ℕ) : ℂ) * coeff j ((parDiff k a w ^ m) f)
      = ∑ m ∈ Finset.range (j + n + 1), ((n.choose m : ℕ) : ℂ)
          * coeff j ((parDiff k a w ^ m) f) := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun m hm hmj => ?_
    rw [Finset.mem_range, not_lt] at hmj
    rw [coeff_parDiff_pow_eq_zero (m := m) hk (by omega), mul_zero]
  have hR : ∑ m ∈ Finset.range (n + 1), ((n.choose m : ℕ) : ℂ) * coeff j ((parDiff k a w ^ m) f)
      = ∑ m ∈ Finset.range (j + n + 1), ((n.choose m : ℕ) : ℂ)
          * coeff j ((parDiff k a w ^ m) f) := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun m hm hmn => ?_
    rw [Finset.mem_range, not_lt] at hmn
    rw [Nat.choose_eq_zero_of_lt (n := n) (k := m) (by omega), Nat.cast_zero, zero_mul]
  rw [hL, hR]

theorem flowEval_zero_flow (hk : 1 ≤ k) (f : ℂ⟦X⟧) : flowEval 0 (flow k a w f) = f := by
  have := flowEval_flow (a := a) (w := w) hk 0 f
  rwa [Nat.cast_zero, Function.iterate_zero_apply] at this

theorem parSubst_iterate_mul (n : ℕ) (f g : ℂ⟦X⟧) :
    (parSubst k a w)^[n] (f * g) = (parSubst k a w)^[n] f * (parSubst k a w)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_mul]

theorem parSubst_iterate_add (n : ℕ) (f g : ℂ⟦X⟧) :
    (parSubst k a w)^[n] (f + g) = (parSubst k a w)^[n] f + (parSubst k a w)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_add]

theorem parSubst_iterate_C (n : ℕ) (c : ℂ) : (parSubst k a w)^[n] (C c) = C c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; exact (parSubst k a w).commutes c

theorem flow_mul (hk : 1 ≤ k) (f g : ℂ⟦X⟧) :
    flow k a w (f * g) = flow k a w f * flow k a w g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_flowEval_eq_zero Set.infinite_univ fun n _ => ?_
  rw [map_sub, map_mul, flowEval_flow hk, flowEval_flow hk, flowEval_flow hk, parSubst_iterate_mul,
    sub_self]

theorem flow_add (hk : 1 ≤ k) (f g : ℂ⟦X⟧) :
    flow k a w (f + g) = flow k a w f + flow k a w g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_flowEval_eq_zero Set.infinite_univ fun n _ => ?_
  rw [map_sub, map_add, flowEval_flow hk, flowEval_flow hk, flowEval_flow hk, parSubst_iterate_add,
    sub_self]

theorem flow_C (hk : 1 ≤ k) (c : ℂ) : flow k a w (C c) = C (Polynomial.C c) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_flowEval_eq_zero Set.infinite_univ fun n _ => ?_
  rw [map_sub, flowEval_flow hk, parSubst_iterate_C, flowEval, map_C, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, sub_self]

/-! ### The linear part and the generator -/

/-- The coefficient of `t` of a flow. -/
def linPart (F : PowerSeries (Polynomial ℂ)) : ℂ⟦X⟧ := PowerSeries.mk fun j => (coeff j F).coeff 1

theorem coeff_linPart (j : ℕ) (F : PowerSeries (Polynomial ℂ)) :
    coeff j (linPart F) = (coeff j F).coeff 1 := by
  rw [linPart, coeff_mk]

theorem linPart_add (F G : PowerSeries (Polynomial ℂ)) :
    linPart (F + G) = linPart F + linPart G := by
  refine PowerSeries.ext fun j => ?_
  simp [coeff_linPart]

theorem polynomial_coeff_one_mul (P Q : Polynomial ℂ) :
    (P * Q).coeff 1 = P.coeff 1 * Q.coeff 0 + P.coeff 0 * Q.coeff 1 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton]
  simp only [zero_add]
  ring

theorem linPart_mul (F G : PowerSeries (Polynomial ℂ)) :
    linPart (F * G) = linPart F * flowEval 0 G + flowEval 0 F * linPart G := by
  refine PowerSeries.ext fun j => ?_
  rw [coeff_linPart, PowerSeries.coeff_mul, map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    Polynomial.finsetSum_coeff, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [polynomial_coeff_one_mul, coeff_linPart, coeff_linPart, coeff_flowEval, coeff_flowEval,
    ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero]

/-- **The logarithmic generator** `L f`: the coefficient of `t` of the flow of `f`. -/
def parLog (k : ℕ) (a : ℂ) (w : ℂ⟦X⟧) (f : ℂ⟦X⟧) : ℂ⟦X⟧ := linPart (flow k a w f)

theorem parLog_mul (hk : 1 ≤ k) (f g : ℂ⟦X⟧) :
    parLog k a w (f * g) = parLog k a w f * g + f * parLog k a w g := by
  rw [parLog, flow_mul hk, linPart_mul, flowEval_zero_flow hk, flowEval_zero_flow hk]
  rfl

theorem parLog_add (hk : 1 ≤ k) (f g : ℂ⟦X⟧) :
    parLog k a w (f + g) = parLog k a w f + parLog k a w g := by
  rw [parLog, flow_add hk, linPart_add]
  rfl

theorem parLog_C (hk : 1 ≤ k) (c : ℂ) : parLog k a w (C c) = 0 := by
  rw [parLog, flow_C hk]
  refine PowerSeries.ext fun j => ?_
  rw [coeff_linPart, coeff_C, map_zero]
  split_ifs <;> simp

theorem parLog_C_mul (hk : 1 ≤ k) (c : ℂ) (f : ℂ⟦X⟧) :
    parLog k a w (C c * f) = C c * parLog k a w f := by
  rw [parLog_mul hk, parLog_C hk, zero_mul, zero_add]

theorem parLog_sub (hk : 1 ≤ k) (f g : ℂ⟦X⟧) :
    parLog k a w (f - g) = parLog k a w f - parLog k a w g := by
  have h := parLog_add (a := a) (w := w) hk (f - g) g
  rw [sub_add_cancel] at h
  rw [h]; ring

theorem coeff_parLog (j : ℕ) (f : ℂ⟦X⟧) :
    coeff j (parLog k a w f) = ∑ m ∈ Finset.range (j + 1),
      (binomPoly m).coeff 1 * coeff j ((parDiff k a w ^ m) f) := by
  rw [parLog, coeff_linPart, coeff_flow, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.coeff_mul_C]

theorem coeff_parLog_eq_zero_of_X_pow_dvd (hk : 1 ≤ k) {j : ℕ} {h : ℂ⟦X⟧}
    (hh : (X : ℂ⟦X⟧) ^ (j + 1) ∣ h) : coeff j (parLog k a w h) = 0 := by
  rw [coeff_parLog]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [X_pow_dvd_iff.mp (X_pow_add_dvd_parDiff_pow hk hh m) j (by omega), mul_zero]

/-- **The formal generator** `X_g = L X`. -/
def parGen (k : ℕ) (a : ℂ) (w : ℂ⟦X⟧) : ℂ⟦X⟧ := parLog k a w X

theorem X_dvd_parGen : (X : ℂ⟦X⟧) ∣ parGen k a w := by
  refine X_dvd_iff.mpr ?_
  rw [← coeff_zero_eq_constantCoeff_apply, parGen, coeff_parLog, Finset.sum_range_one, pow_zero,
    Module.End.one_apply, coeff_zero_X, mul_zero]

theorem parLog_one (hk : 1 ≤ k) : parLog k a w 1 = 0 := by
  rw [show (1 : ℂ⟦X⟧) = C 1 from (map_one C).symm, parLog_C hk]

theorem parLog_X_pow (hk : 1 ≤ k) (i : ℕ) :
    parLog k a w (X ^ i) = parGen k a w * d⁄dX ℂ (X ^ i) := by
  induction i with
  | zero => rw [pow_zero, parLog_one hk, Derivation.map_one_eq_zero, mul_zero]
  | succ i ih =>
      rw [pow_succ, parLog_mul hk, ih, Derivation.leibniz, derivative_X, smul_eq_mul,
        smul_eq_mul]
      rw [parGen]
      ring

theorem X_pow_dvd_derivative {n : ℕ} {g : ℂ⟦X⟧} (hg : (X : ℂ⟦X⟧) ^ (n + 1) ∣ g) :
    (X : ℂ⟦X⟧) ^ n ∣ d⁄dX ℂ g := by
  refine X_pow_dvd_iff.mpr fun m hm => ?_
  rw [coeff_derivative, X_pow_dvd_iff.mp hg (m + 1) (by omega), zero_mul]

/-- **The generator is a vector field**: `L f = X_g·f'`. -/
theorem parLog_eq_parGen_mul_derivative (hk : 1 ≤ k) (f : ℂ⟦X⟧) :
    parLog k a w f = parGen k a w * d⁄dX ℂ f := by
  refine PowerSeries.ext fun j => ?_
  set P : ℂ⟦X⟧ := ∑ i ∈ Finset.range (j + 2), C (coeff i f) * X ^ i with hP
  have hfP : (X : ℂ⟦X⟧) ^ (j + 2) ∣ f - P := by
    refine X_pow_dvd_iff.mpr fun m hm => ?_
    rw [map_sub, hP, map_sum]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hm), sub_self]
  have hPlog : parLog k a w P = parGen k a w * d⁄dX ℂ P := by
    rw [hP]
    induction (Finset.range (j + 2)) using Finset.induction_on with
    | empty => rw [Finset.sum_empty, show (0 : ℂ⟦X⟧) = C 0 from (map_zero C).symm, parLog_C hk,
        map_zero, map_zero, mul_zero]
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, parLog_add hk, ih, parLog_C_mul hk, parLog_X_pow hk, map_add,
          Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul]
        ring
  have h1 : coeff j (parLog k a w f) = coeff j (parLog k a w P) := by
    have := coeff_parLog_eq_zero_of_X_pow_dvd (a := a) (w := w) hk
      ((pow_dvd_pow X (by omega : j + 1 ≤ j + 2)).trans hfP)
    rw [parLog_sub hk, map_sub] at this
    exact sub_eq_zero.mp this
  have h2 : coeff j (parGen k a w * d⁄dX ℂ f) = coeff j (parGen k a w * d⁄dX ℂ P) := by
    have hd := X_pow_dvd_derivative (n := j + 1) hfP
    rw [map_sub] at hd
    have hprod : (X : ℂ⟦X⟧) ^ (j + 1) ∣ parGen k a w * (d⁄dX ℂ f - d⁄dX ℂ P) :=
      (pow_dvd_pow X (by omega : j + 1 ≤ 1 + (j + 1))).trans
        (by rw [pow_add, pow_one]; exact mul_dvd_mul X_dvd_parGen hd)
    have := X_pow_dvd_iff.mp hprod j (by omega)
    rw [mul_sub, map_sub] at this
    exact sub_eq_zero.mp this
  rw [h1, h2, hPlog]

theorem X_pow_dvd_parSubst {n : ℕ} {h : ℂ⟦X⟧} (hh : (X : ℂ⟦X⟧) ^ n ∣ h) :
    (X : ℂ⟦X⟧) ^ n ∣ parSubst k a w h := by
  obtain ⟨q, rfl⟩ := hh
  rw [map_mul, map_pow, parSubst_X, parGerm, mul_pow, mul_assoc]
  exact dvd_mul_right _ _

theorem parSubst_parDiff_pow (m : ℕ) (f : ℂ⟦X⟧) :
    parSubst k a w ((parDiff k a w ^ m) f) = (parDiff k a w ^ m) (parSubst k a w f) := by
  have hcomm : Commute (parSubst k a w).toLinearMap (parDiff k a w) := by
    rw [parDiff]
    exact (Commute.refl _).sub_right (Commute.one_right _)
  have := congrArg (fun T : Module.End ℂ ℂ⟦X⟧ => T f) (hcomm.pow_right m).eq
  simpa [Module.End.mul_apply] using this

/-- The truncated logarithm `Σ_{m ≤ j} b_m D^m h`. -/
def parLogTrunc (k : ℕ) (a : ℂ) (w : ℂ⟦X⟧) (j : ℕ) (h : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  ∑ m ∈ Finset.range (j + 1), (binomPoly m).coeff 1 • (parDiff k a w ^ m) h

theorem X_pow_dvd_parLog_sub_trunc (hk : 1 ≤ k) (j : ℕ) (h : ℂ⟦X⟧) :
    (X : ℂ⟦X⟧) ^ (j + 1) ∣ parLog k a w h - parLogTrunc k a w j h := by
  refine X_pow_dvd_iff.mpr fun i hi => ?_
  rw [map_sub, coeff_parLog, parLogTrunc, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [sub_eq_zero]
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun m _ hm => ?_
  rw [Finset.mem_range, not_lt] at hm
  rw [coeff_parDiff_pow_eq_zero (m := m) hk (by omega), mul_zero]

/-- **The generator commutes with the substitution.** -/
theorem parSubst_parLog (hk : 1 ≤ k) (f : ℂ⟦X⟧) :
    parSubst k a w (parLog k a w f) = parLog k a w (parSubst k a w f) := by
  refine PowerSeries.ext fun j => ?_
  have h1 := X_pow_dvd_parSubst (k := k) (a := a) (w := w)
    (X_pow_dvd_parLog_sub_trunc (a := a) (w := w) hk j f)
  have h2 := X_pow_dvd_parLog_sub_trunc (a := a) (w := w) hk j (parSubst k a w f)
  have htr : parSubst k a w (parLogTrunc k a w j f) = parLogTrunc k a w j (parSubst k a w f) := by
    rw [parLogTrunc, parLogTrunc, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, parSubst_parDiff_pow]
  rw [map_sub, htr] at h1
  have e1 := X_pow_dvd_iff.mp h1 j (by omega)
  have e2 := X_pow_dvd_iff.mp h2 j (by omega)
  rw [map_sub] at e1 e2
  rw [sub_eq_zero.mp e1, sub_eq_zero.mp e2]

/-- **The generator is invariant**: `X_g(r) = r'·X_g`. -/
theorem parSubst_parGen (hk : 1 ≤ k) :
    parSubst k a w (parGen k a w) = parGen k a w * d⁄dX ℂ (parGerm k a w) := by
  rw [parGen, parSubst_parLog hk, parSubst_X, parLog_eq_parGen_mul_derivative hk]
  rfl

theorem binomPoly_one : binomPoly 1 = Polynomial.X := by
  simp [binomPoly]

/-- **The generator starts with `a X^{k+1}`.** -/
theorem coeff_parGen (hk : 1 ≤ k) : coeff (k + 1) (parGen k a w) = a := by
  rw [parGen, coeff_parLog, Finset.sum_eq_single (1 : ℕ)]
  · rw [binomPoly_one, Polynomial.coeff_X_one, one_mul, pow_one, parDiff_apply, parSubst_X,
      parGerm, parUnit]
    have : (X : ℂ⟦X⟧) * (1 + C a * X ^ k + X ^ (k + 1) * w) - X
        = C a * X ^ (k + 1) + X ^ (k + 2) * w := by ring
    rw [this, map_add, coeff_C_mul_X_pow, if_pos rfl, coeff_X_pow_mul', if_neg (by omega),
      add_zero]
  · intro m hm hm1
    rcases Nat.lt_or_ge m 1 with h | h
    · obtain rfl : m = 0 := by omega
      rw [pow_zero, Module.End.one_apply, coeff_X, if_neg (by omega), mul_zero]
    · have hD : (X : ℂ⟦X⟧) ^ (k + 1) ∣ parDiff k a w X := by
        rw [parDiff_apply, parSubst_X]
        exact X_pow_dvd_parGerm_sub_X
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hm' : 1 ≤ m' := by omega
      have := X_pow_add_dvd_parDiff_pow (a := a) (w := w) hk hD m'
      rw [pow_succ, Module.End.mul_apply, X_pow_dvd_iff.mp this (k + 1) (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem parGen_ne_zero (hk : 1 ≤ k) (ha : a ≠ 0) : parGen k a w ≠ 0 := fun h =>
  ha (by have := coeff_parGen (k := k) (a := a) (w := w) hk; rwa [h, map_zero, eq_comm] at this)

/-! ### The lowest order in the flow parameter -/

theorem map_derivative {A B : Type*} [CommSemiring A] [CommSemiring B] (f : A →+* B)
    (F : PowerSeries A) : PowerSeries.map f (d⁄dX A F) = d⁄dX B (PowerSeries.map f F) := by
  refine PowerSeries.ext fun n => ?_
  simp [coeff_derivative]

theorem map_iterate_derivative {A B : Type*} [CommSemiring A] [CommSemiring B] (f : A →+* B)
    (i : ℕ) (F : PowerSeries A) :
    PowerSeries.map f ((⇑(d⁄dX A))^[i] F) = (⇑(d⁄dX B))^[i] (PowerSeries.map f F) := by
  induction i generalizing F with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, map_derivative]

theorem iterate_derivative_C_mul_powerSeries {A : Type*} [CommSemiring A] (i : ℕ) (c : A)
    (F : PowerSeries A) :
    (⇑(d⁄dX A))^[i] (C c * F) = C c * (⇑(d⁄dX A))^[i] F := by
  induction i generalizing F with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Derivation.leibniz,
        derivative_C, smul_zero, add_zero, smul_eq_mul, ih]

theorem iterate_derivative_add_powerSeries {A : Type*} [CommSemiring A] (i : ℕ)
    (F G : PowerSeries A) :
    (⇑(d⁄dX A))^[i] (F + G) = (⇑(d⁄dX A))^[i] F + (⇑(d⁄dX A))^[i] G := by
  induction i generalizing F G with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, map_add, ih]

theorem flowEval_aeval {σ : Type*} (c : ℂ) (v : σ → PowerSeries (Polynomial ℂ))
    (T : MvPolynomial σ ℂ) :
    flowEval c (MvPolynomial.aeval v T) = MvPolynomial.aeval (fun i => flowEval c (v i)) T := by
  induction T using MvPolynomial.induction_on with
  | C x =>
      rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
      refine PowerSeries.ext fun j => ?_
      rw [coeff_flowEval, PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply, coeff_C,
        coeff_C]
      split_ifs <;> simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X]

/-- A power series over `ℂ[t]` with its value at `t = 0` removed, divided by `t`. -/
def tDiv (F : PowerSeries (Polynomial ℂ)) : PowerSeries (Polynomial ℂ) :=
  PowerSeries.mk fun j => (coeff j F).divX

theorem eq_flowEval_zero_add_tDiv (F : PowerSeries (Polynomial ℂ)) :
    F = PowerSeries.map Polynomial.C (flowEval 0 F) + C Polynomial.X * tDiv F := by
  refine PowerSeries.ext fun j => ?_
  rw [map_add, coeff_map, coeff_flowEval, coeff_C_mul, tDiv, coeff_mk, add_comm,
    ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.X_mul_divX_add]

theorem flowEval_zero_tDiv (F : PowerSeries (Polynomial ℂ)) : flowEval 0 (tDiv F) = linPart F := by
  refine PowerSeries.ext fun j => ?_
  rw [coeff_flowEval, tDiv, coeff_mk, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX,
    coeff_linPart]

/-- The jets of the coordinate: `z, 1, 0, 0, …`. -/
def coordJet {M : ℕ} : ℕ → MvPolynomial (Fin (M + 1)) ℂ
  | 0 => MvPolynomial.X 0
  | 1 => 1
  | _ + 2 => 0

theorem aeval_coordJet {M : ℕ} {A : Type*} [CommRing A] [Algebra ℂ A]
    (v : Fin (M + 1) → PowerSeries A) (hv : v 0 = X) (i : ℕ) :
    MvPolynomial.aeval v (coordJet i) = (⇑(d⁄dX A))^[i] X := by
  match i with
  | 0 => rw [coordJet, MvPolynomial.aeval_X, hv]; rfl
  | 1 => rw [coordJet, map_one]; exact (derivative_X (R := A)).symm
  | i + 2 =>
      rw [coordJet, map_zero, Function.iterate_succ_apply, Function.iterate_succ_apply,
        derivative_X, Derivation.map_one_eq_zero]
      induction i with
      | zero => rfl
      | succ i ih => rw [Function.iterate_succ_apply', ← ih, map_zero]

/-- The substitution `Y₀ ↦ z`, `Y_{i+1} ↦ (z-jet)_i + t·Y_{i+1}`. -/
def jetScale (M : ℕ) :
    MvPolynomial (Fin (M + 1)) ℂ →ₐ[ℂ] Polynomial (MvPolynomial (Fin (M + 1)) ℂ) :=
  MvPolynomial.aeval (Fin.cons (Polynomial.C (MvPolynomial.X 0)) fun i : Fin M =>
    Polynomial.C (coordJet (i : ℕ)) + Polynomial.C (MvPolynomial.X i.succ) * Polynomial.X)

/-- The inverse shift `Y₀ ↦ Y₀`, `Y_{i+1} ↦ Y_{i+1} − (z-jet)_i`. -/
def jetUnshift (M : ℕ) : MvPolynomial (Fin (M + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (M + 1)) ℂ :=
  MvPolynomial.aeval (Fin.cons (MvPolynomial.X 0) fun i : Fin M =>
    MvPolynomial.X i.succ - coordJet (i : ℕ))

theorem jetUnshift_coordJet {M : ℕ} (i : ℕ) : jetUnshift M (coordJet i) = coordJet i := by
  match i with
  | 0 => rw [coordJet, jetUnshift, MvPolynomial.aeval_X]; rfl
  | 1 => rw [coordJet, map_one]
  | _ + 2 => rw [coordJet, map_zero]

theorem jetScale_ne_zero {M : ℕ} {T : MvPolynomial (Fin (M + 1)) ℂ} (hT : T ≠ 0) :
    jetScale M T ≠ 0 := by
  set ev : Polynomial (MvPolynomial (Fin (M + 1)) ℂ) →ₐ[ℂ] MvPolynomial (Fin (M + 1)) ℂ :=
    (Polynomial.aeval (1 : MvPolynomial (Fin (M + 1)) ℂ)).restrictScalars ℂ
  have key : ((jetUnshift M).comp ev).comp (jetScale M) = AlgHom.id ℂ _ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [jetScale, ev, jetUnshift]
    · simp only [AlgHom.comp_apply, jetScale, MvPolynomial.aeval_X, Fin.cons_succ, map_add,
        map_mul, ev, AlgHom.restrictScalars_apply, Polynomial.aeval_C, Polynomial.aeval_X,
        Algebra.algebraMap_self, RingHom.id_apply, jetUnshift_coordJet, AlgHom.id_apply]
      rw [map_one, mul_one, jetUnshift, MvPolynomial.aeval_X, Fin.cons_succ]
      ring
  intro h
  apply hT
  have := AlgHom.congr_fun key T
  rw [AlgHom.comp_apply, AlgHom.comp_apply, h, map_zero, map_zero, AlgHom.id_apply] at this
  exact this.symm

/-- **One relation among infinitely many iterates gives a relation among generator jets.**  If a
nonzero `T` vanishes on `(z, Cⁿ z, (Cⁿ z)′, …)` for infinitely many `n`, then a nonzero `T'`
vanishes on `(z, X_g, X_g′, …)`: the flow of `z` is `z + t·H` with `H(0) = X_g`, and the lowest
`t`-order part of the relation along the flow survives. -/
theorem exists_relation_parGen_of_iterates (hk : 1 ≤ k) {M : ℕ}
    {T : MvPolynomial (Fin (M + 1)) ℂ} (hT : T ≠ 0) {S : Set ℕ} (hS : S.Infinite)
    (hrel : ∀ n ∈ S, MvPolynomial.aeval (Fin.cons X fun i : Fin M =>
      (⇑(d⁄dX ℂ))^[i] ((parSubst k a w)^[n] X) : Fin (M + 1) → ℂ⟦X⟧) T = 0) :
    ∃ T' : MvPolynomial (Fin (M + 1)) ℂ, T' ≠ 0 ∧ MvPolynomial.aeval (Fin.cons X fun i : Fin M =>
      (⇑(d⁄dX ℂ))^[i] (parGen k a w) : Fin (M + 1) → ℂ⟦X⟧) T' = 0 := by
  set F := flow k a w X with hF
  set H := tDiv F with hH
  have hFX : F = X + C Polynomial.X * H := by
    conv_lhs => rw [eq_flowEval_zero_add_tDiv F]
    rw [hF, flowEval_zero_flow hk, map_X]
  set jF : Fin (M + 1) → PowerSeries (Polynomial ℂ) :=
    Fin.cons X fun i : Fin M => (⇑(d⁄dX (Polynomial ℂ)))^[i] F with hjF
  -- the relation holds along the flow
  have hG : MvPolynomial.aeval jF T = 0 := by
    refine eq_zero_of_flowEval_eq_zero hS fun n hn => ?_
    have hjets : (fun i => flowEval n (jF i)) = (Fin.cons X fun i : Fin M =>
        (⇑(d⁄dX ℂ))^[i] ((parSubst k a w)^[n] X) : Fin (M + 1) → ℂ⟦X⟧) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [hjF, Fin.cons_zero, flowEval, map_X]
      · simp only [hjF, Fin.cons_succ]
        rw [flowEval, map_iterate_derivative, ← flowEval, hF, flowEval_flow hk]
    rw [flowEval_aeval, hjets, hrel n hn]
  -- the flow relation is the scaled polynomial evaluated at `t`
  set v : Fin (M + 1) → PowerSeries (Polynomial ℂ) :=
    Fin.cons X fun i : Fin M => (⇑(d⁄dX (Polynomial ℂ)))^[i] H with hv
  set E : Polynomial (MvPolynomial (Fin (M + 1)) ℂ) →+* PowerSeries (Polynomial ℂ) :=
    Polynomial.eval₂RingHom (MvPolynomial.aeval v).toRingHom (C Polynomial.X) with hE
  have hEscale : E (jetScale M T) = MvPolynomial.aeval jF T := by
    rw [jetScale, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, MvPolynomial.aeval_def]
    have halg : E.comp (algebraMap ℂ (Polynomial (MvPolynomial (Fin (M + 1)) ℂ)))
        = algebraMap ℂ (PowerSeries (Polynomial ℂ)) := by
      refine RingHom.ext fun c => ?_
      rw [RingHom.comp_apply, Polynomial.algebraMap_apply, hE, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rw [halg]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hE, hv, hjF]
    · simp only [Function.comp_apply, Fin.cons_succ, hE, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, hjF, hv]
      rw [aeval_coordJet _ (by rfl), hFX, iterate_derivative_add_powerSeries,
        iterate_derivative_C_mul_powerSeries, mul_comm]
  -- factor out the trailing power of `t`
  set P := jetScale M T with hP
  have hP0 : P ≠ 0 := jetScale_ne_zero hT
  obtain ⟨d0, hd0⟩ : ∃ d0, d0 = P.natTrailingDegree := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : Polynomial.X ^ d0 ∣ P := Polynomial.X_pow_dvd_iff.mpr fun d hd =>
    Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (hd0 ▸ hd)
  refine ⟨Q.coeff 0, ?_, ?_⟩
  · have htc : P.coeff d0 ≠ 0 := by
      rw [hd0]
      exact Polynomial.trailingCoeff_eq_zero.not.mpr hP0
    rwa [hQ, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self] at htc
  · have hEQ : E Q = 0 := by
      have h1 : E P = 0 := by rw [hP, hEscale, hG]
      rw [hQ, map_mul, map_pow, hE, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] at h1
      refine (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ ?_)
      exact fun h => Polynomial.X_ne_zero (C_injective (h.trans (map_zero C).symm))
    have h2 := congrArg (flowEval 0) hEQ
    rw [map_zero, hE, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂] at h2
    have ht0 : flowEval 0 (C Polynomial.X) = 0 := by
      rw [flowEval, map_C, Polynomial.coe_evalRingHom, Polynomial.eval_X, map_zero]
    rw [ht0, Polynomial.eval₂_at_zero, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, flowEval_aeval] at h2
    have hjets : (fun i => flowEval 0 (v i)) = (Fin.cons X fun i : Fin M =>
        (⇑(d⁄dX ℂ))^[i] (parGen k a w) : Fin (M + 1) → ℂ⟦X⟧) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [hv, Fin.cons_zero, flowEval, map_X]
      · simp only [hv, Fin.cons_succ]
        rw [flowEval, map_iterate_derivative, ← flowEval, hH, flowEval_zero_tDiv, hF]
        rfl
    rwa [hjets] at h2

/-! ### The generator is differentially algebraic -/

instance formalLaurent_charZero : CharZero FormalLaurent :=
  charZero_of_injective_ringHom (f := (algebraMap ℂ⟦X⟧ FormalLaurent).comp (C : ℂ →+* ℂ⟦X⟧))
    ((IsFractionRing.injective ℂ⟦X⟧ FormalLaurent).comp C_injective)

/-- **A formal relation with polynomial coefficients is a differential-algebraic relation over
`ℂ(z)` in formal Laurent series.** -/
theorem differentialAlgebraicOver_of_formal_relation {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P ≠ 0) {g : ℂ⟦X⟧}
    (hrel : MvPolynomial.aeval (Fin.cons X fun j : Fin (n + 1) =>
      (⇑(d⁄dX ℂ))^[j] g : Fin (n + 2) → ℂ⟦X⟧) P = 0) :
    letI := ratFuncDerivDifferential
    letI := laurentDifferential
    DifferentialAlgebraicOver (RatFunc ℂ) (algebraMap ℂ⟦X⟧ FormalLaurent g) := by
  letI := ratFuncDerivDifferential
  letI := laurentDifferential
  set ι := algebraMap ℂ⟦X⟧ FormalLaurent with hι
  set G : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) := reshapeJet n P with hG
  set Q : MvPolynomial (Fin (n + 1)) (RatFunc ℂ) :=
    MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) G with hQdef
  have hG0 : G ≠ 0 := fun hzero => hP (reshapeJet_injective n (by simpa [hG] using hzero))
  have hQ0 : Q ≠ 0 := by
    intro hzero
    apply hG0
    apply MvPolynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
    simpa [hQdef] using hzero
  set jets : Fin (n + 1) → FormalLaurent := fun j => differentialJet (j : ℕ) (ι g) with hjets
  have hjet : ∀ j : ℕ, differentialJet j (ι g) = ι ((⇑(d⁄dX ℂ))^[j] g) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [differentialJet_succ, ih, Function.iterate_succ_apply']
        exact laurentDeriv_algebraMap _
  have hcoe : (algebraMap (RatFunc ℂ) FormalLaurent).comp (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      = ι.comp (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* ℂ⟦X⟧) := by
    refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, algebraMap_ratFunc_formalLaurent, ratExpandZero_algebraMap]
    rfl
  have hhom : (MvPolynomial.eval₂Hom (ι.comp (Polynomial.coeToPowerSeries.ringHom :
        Polynomial ℂ →+* ℂ⟦X⟧)) jets).comp (reshapeJet n)
      = MvPolynomial.eval₂Hom (ι.comp (algebraMap ℂ ℂ⟦X⟧))
          (ι ∘ (Fin.cons X fun j : Fin (n + 1) => (⇑(d⁄dX ℂ))^[j] g : Fin (n + 2) → ℂ⟦X⟧)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [reshapeJet]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [reshapeJet]
      · simp [reshapeJet, hjets, hjet]
  have hfield : MvPolynomial.aeval jets Q = 0 := by
    rw [MvPolynomial.aeval_def, hQdef, MvPolynomial.eval₂_map, hcoe]
    have h1 := RingHom.congr_fun hhom P
    rw [RingHom.comp_apply] at h1
    rw [MvPolynomial.coe_eval₂Hom] at h1
    rw [hG, h1, MvPolynomial.coe_eval₂Hom, ← MvPolynomial.eval₂_comp_left,
      ← MvPolynomial.aeval_def, hrel, map_zero]
  unfold DifferentialAlgebraicOver DifferentialIndependent
  intro hindependent
  let e : Fin (n + 1) → Unit × ℕ := fun j => ((), (j : ℕ))
  have he : Function.Injective e := fun i j hij => Fin.ext (congrArg Prod.snd hij)
  have hrename : MvPolynomial.rename e Q ≠ 0 := fun hzero =>
    hQ0 (MvPolynomial.rename_injective e he hzero)
  apply hrename
  apply hindependent.eq_zero_of_aeval_eq_zero
  rw [MvPolynomial.aeval_rename]
  simpa [e, Function.comp_def, hjets] using hfield

/-- **Ritt's implication at a parabolic fixed point, from one relation among the iterates.**  If
a nonzero `T` vanishes on `(z, Rⁿ, (Rⁿ)′, …)` for infinitely many `n` (as formal power series at
the parabolic fixed point `0`), then `R` carries a rational cocycle `A(R)·R'^N = β·A`. -/
theorem ratTransport_of_iterate_relation {R : RatFunc ℂ} (hk : 1 ≤ k) (ha : a ≠ 0)
    (hR : ¬ ∃ c : ℂ, R = RatFunc.C c) (hd : 2 ≤ ratFuncDegree R)
    (hRr : ratExpandZero R = algebraMap ℂ⟦X⟧ FormalLaurent (parGerm k a w)) {n : ℕ}
    {T : MvPolynomial (Fin (n + 2)) ℂ} (hT : T ≠ 0) {S : Set ℕ} (hS : S.Infinite)
    (hrel : ∀ m ∈ S, MvPolynomial.aeval (Fin.cons X fun i : Fin (n + 1) =>
      (⇑(d⁄dX ℂ))^[i] ((parSubst k a w)^[m] X) : Fin (n + 2) → ℂ⟦X⟧) T = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ β : ℂ, β ≠ 0 ∧ ∃ A : RatFunc ℂ, A ≠ 0 ∧
      IsRatAffineTransport R hR (N : ℤ) (RatFunc.C β) 0 A := by
  letI := ratFuncDerivDifferential
  letI := laurentDifferential
  haveI := laurent_differentialAlgebra
  obtain ⟨T', hT', hrel'⟩ := exists_relation_parGen_of_iterates hk hT hS hrel
  set ι := algebraMap ℂ⟦X⟧ FormalLaurent with hι
  have hgen : ι (parGen k a w) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℂ⟦X⟧ FormalLaurent)).mpr (parGen_ne_zero hk ha)
  have hDA := differentialAlgebraicOver_inv (differentialAlgebraicOver_of_formal_relation hT' hrel')
  refine ratTransport_of_laurent_eigen hk ha hR hd hRr (inv_ne_zero hgen) ?_ hDA
  have hR' : ratExpandZero (ratFuncDeriv R) = ι (d⁄dX ℂ (parGerm k a w)) := by
    rw [← laurentDeriv_ratExpandZero, hRr, laurentDeriv_algebraMap]
  rw [map_inv₀, laurentSubst_algebraMap hk, parSubst_parGen hk, map_inv₀, hR', map_mul, mul_inv,
    mul_comm]

end

end GaloisForLFunctions.HTGeometry
