import GaloisForLFunctions.HTGeometry.MultiplicativeOrbitNonSummability
import GaloisForLFunctions.HTGeometry.RationalFunctionPartialInvariant

/-!
# The double-sine descent obstruction: `A(b)` is not a `q`-telescoped rational difference

This is the analytic core of the double-sine translation-annihilator theorem.  After the paired
telescoping reduction and the specialization of the `E₁ = ℂ(u₁)` factor, the hypothetical
differential algebraicity of the double-sine logarithmic derivative descends to a `q`-difference
equation on one multiplicative cylinder,

```text
h(qX) - h(X) = A(b)(X),        b(X) = c (X+1)/(X-1),  c ≠ 0,
```

where `h` is rational, `q = exp(2πi ω₁/ω₂)` is not a root of unity because `ω₁/ω₂` is irrational,
and `A = ∑_{i ≤ r} a_i δ^i` is a nonzero constant-coefficient polynomial in the Euler operator
`δ = X d/dX` (the coordinate form of `d/dz` on the cylinder, up to a nonzero scalar, so any
constant-coefficient differential operator becomes one of these).

The content proved here, unconditionally:

* one application of `d/dX` raises the pole order at `X = 1` by exactly one, in the exact
  polynomial-numerator form `f (X-1)^k = p  ⟹  f' (X-1)^(k+1) = p'(X-1) - k p`;
* consequently `A(b) (X-1)^(r+1)` is a polynomial whose value at `1` is `a_r` times a nonzero
  constant, so `A(b)` has a pole at `1` and is regular at every other point of `ℂ`;
* hence `A(b)` has exactly one pole on the multiplicative orbit `q^ℤ`, and the multiplicative-orbit
  residue obstruction of `MultiplicativeOrbitNonSummability` forbids the displayed equation.

`not_dilationTelescoped_eulerCombination_cotModel` is the resulting theorem, proved over an
arbitrary field of characteristic zero.  Taking that field to be `ℂ(u₁)` gives
`not_dilationTelescoped_twoCylinder`, the form the descent actually needs: the paired telescoping
theorem produces `g` in the two-cylinder field, and no specialization of the `u₁` factor is
required because every pole of `A(b)` and every orbit point lies in the constant subfield.  It has no
hypotheses beyond `q` not a root of unity, `c ≠ 0` and `a r ≠ 0`, and it uses only Lean's standard
axioms.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

noncomputable section

/-- Embedding of polynomials into rational functions. -/
abbrev toRF (p : Polynomial K) : RatFunc K := algebraMap (Polynomial K) (RatFunc K) p

/-- The linear factor at the fixed point `X = 1` of the multiplicative orbit. -/
def linFac (K : Type*) [Field K] : Polynomial K := X - C 1

theorem linFac_def : linFac K = X - C (1 : K) := rfl

@[simp] theorem derivative_linFac : Polynomial.derivative (linFac K) = 1 := by
  simp [linFac]

@[simp] theorem eval_linFac (w : K) : (linFac K).eval w = w - 1 := by
  simp [linFac]

theorem C_nat_mul_pow_pred_mul (k : ℕ) :
    C ((k : K)) * linFac K ^ (k - 1) * linFac K = C ((k : K)) * linFac K ^ k := by
  cases k with
  | zero => simp
  | succ n => rw [Nat.add_sub_cancel, mul_assoc, ← pow_succ]

/-- The Euler operator `X d/dX` on the rational function field. -/
def ratFuncEulerOp (f : RatFunc K) : RatFunc K := toRF X * ratFuncDerivative K f

/-- **One derivative raises the pole order at `1` by one.**  If `f * (X-1)^k` is the polynomial
`p`, then `f' * (X-1)^(k+1)` is the polynomial `p' (X-1) - k p`. -/
theorem ratFuncDerivative_mul_linFac_pow (f : RatFunc K) (k : ℕ) (p : Polynomial K)
    (hf : f * toRF (linFac K ^ k) = toRF p) :
    (ratFuncDerivative K f) * toRF (linFac K ^ (k + 1))
      = toRF (Polynomial.derivative p * linFac K - C ((k : K)) * p) := by
  have hD := congrArg (ratFuncDerivative K) hf
  rw [Derivation.leibniz, ratFuncDerivative_algebraMap, ratFuncDerivative_algebraMap,
    Polynomial.derivative_pow, derivative_linFac, mul_one] at hD
  simp only [smul_eq_mul] at hD
  have h1 : toRF (linFac K ^ k) * toRF (linFac K) = toRF (linFac K ^ (k + 1)) := by
    rw [← map_mul, ← pow_succ]
  have h2 : f * toRF (C ((k : K)) * linFac K ^ (k - 1)) * toRF (linFac K)
      = toRF (C ((k : K)) * p) := by
    rw [mul_assoc, ← map_mul, C_nat_mul_pow_pred_mul, map_mul, ← mul_assoc, mul_comm f,
      mul_assoc, hf, ← map_mul]
  have h3 : toRF (Polynomial.derivative p) * toRF (linFac K)
      = toRF (Polynomial.derivative p * linFac K) := (map_mul _ _ _).symm
  have h4 : toRF (Polynomial.derivative p * linFac K - C ((k : K)) * p)
      = toRF (Polynomial.derivative p * linFac K) - toRF (C ((k : K)) * p) := map_sub _ _ _
  rw [h4]
  linear_combination (toRF (linFac K)) * hD - (ratFuncDerivative K f) * h1 - h2 + h3


theorem ratFuncEulerOp_mul_linFac_pow (f : RatFunc K) (k : ℕ) (p : Polynomial K)
    (hf : f * toRF (linFac K ^ k) = toRF p) :
    ratFuncEulerOp f * toRF (linFac K ^ (k + 1))
      = toRF (X * (Polynomial.derivative p * linFac K - C ((k : K)) * p)) := by
  rw [ratFuncEulerOp, mul_assoc, ratFuncDerivative_mul_linFac_pow f k p hf, ← map_mul]

theorem linFac_ne_zero : linFac K ≠ 0 := Polynomial.X_sub_C_ne_zero 1

/-- The rational model of the cotangent term `c (X+1)/(X-1)` on the multiplicative cylinder. -/
def cotModel (c : K) : RatFunc K := toRF (C c * (X + C 1)) / toRF (linFac K)

theorem cotModel_mul (c : K) :
    cotModel c * toRF (linFac K ^ 1) = toRF (C c * (X + C 1)) := by
  rw [pow_one, cotModel, div_mul_cancel₀]
  exact RatFunc.algebraMap_ne_zero linFac_ne_zero

/-- The numerator polynomials of the Euler-operator jets of the cotangent model. -/
def eulerNum (c : K) : ℕ → Polynomial K
  | 0 => C c * (X + C 1)
  | (i + 1) => X * (Polynomial.derivative (eulerNum c i) * linFac K
      - C (((i + 1 : ℕ) : K)) * eulerNum c i)

theorem ratFuncEulerOp_iterate_cotModel (c : K) (i : ℕ) :
    ratFuncEulerOp^[i] (cotModel c) * toRF (linFac K ^ (i + 1)) = toRF (eulerNum c i) := by
  induction i with
  | zero => simpa [eulerNum] using cotModel_mul c
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have := ratFuncEulerOp_mul_linFac_pow (ratFuncEulerOp^[n] (cotModel c)) (n + 1) (eulerNum c n) ih
      rw [this, eulerNum]

theorem eval_eulerNum_ne_zero [CharZero K] (c : K) (hc : c ≠ 0) (i : ℕ) : (eulerNum c i).eval 1 ≠ 0 := by
  induction i with
  | zero =>
      have h2 : (1 : K) + 1 ≠ 0 := by norm_num
      simp only [eulerNum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
        Polynomial.eval_X]
      exact mul_ne_zero hc h2
  | succ n ih =>
      have h : (eulerNum c (n + 1)).eval 1 = -(((n : K) + 1) * (eulerNum c n).eval 1) := by
        simp [eulerNum, linFac_def]
      rw [h]
      refine neg_ne_zero.mpr (mul_ne_zero ?_ ih)
      intro hz
      have : ((n : K) + 1) = ((n + 1 : ℕ) : K) := by push_cast; ring
      rw [this] at hz
      exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) hz

/-- A constant-coefficient Euler-operator combination applied to a rational function. -/
def eulerCombination (a : ℕ → K) (r : ℕ) (f : RatFunc K) : RatFunc K :=
  ∑ i ∈ Finset.range (r + 1), toRF (C (a i)) * ratFuncEulerOp^[i] f

/-- The numerator of `A(b)` over `(X-1)^(r+1)`. -/
def eulerCombinationNum (a : ℕ → K) (c : K) (r : ℕ) : Polynomial K :=
  ∑ i ∈ Finset.range (r + 1), C (a i) * eulerNum c i * linFac K ^ (r - i)

theorem eulerCombination_cotModel_mul (a : ℕ → K) (c : K) (r : ℕ) :
    eulerCombination a r (cotModel c) * toRF (linFac K ^ (r + 1))
      = toRF (eulerCombinationNum a c r) := by
  rw [eulerCombination, eulerCombinationNum, Finset.sum_mul,
    show toRF (∑ i ∈ Finset.range (r + 1), C (a i) * eulerNum c i * linFac K ^ (r - i))
      = ∑ i ∈ Finset.range (r + 1), toRF (C (a i) * eulerNum c i * linFac K ^ (r - i)) from
      map_sum _ _ _]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsplit : (linFac K : Polynomial K) ^ (r + 1) = linFac K ^ (i + 1) * linFac K ^ (r - i) := by
    rw [← pow_add]
    congr 1
    omega
  have e1 : toRF (linFac K ^ (r + 1)) = toRF (linFac K ^ (i + 1)) * toRF (linFac K ^ (r - i)) := by
    rw [hsplit]
    exact map_mul (algebraMap (Polynomial K) (RatFunc K)) _ _
  have e2 : toRF (C (a i) * eulerNum c i * linFac K ^ (r - i))
      = toRF (C (a i)) * toRF (eulerNum c i) * toRF (linFac K ^ (r - i)) := by
    simp only [map_mul]
  rw [e1, e2, ← ratFuncEulerOp_iterate_cotModel c i]
  ring

theorem eval_eulerCombinationNum (a : ℕ → K) (c : K) (r : ℕ) :
    (eulerCombinationNum a c r).eval 1 = a r * (eulerNum c r).eval 1 := by
  rw [eulerCombinationNum, Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single r]
  · simp
  · intro i hi hir
    have hir' : i < r := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hir
    have : r - i ≠ 0 := by omega
    simp [linFac_def, zero_pow this]
  · intro h
    exact absurd (Finset.self_mem_range_succ r) h


/-! ## Reading regularity off a polynomial clearing identity -/

theorem regularAt_of_mul_polynomial (f : RatFunc K) (g Q : Polynomial K) (w : K)
    (hg : g.eval w ≠ 0) (h : f * toRF g = toRF Q) : RegularAt f w := by
  have hg0 : g ≠ 0 := fun hz => hg (by rw [hz]; simp)
  refine ⟨Q, g, hg, ?_⟩
  rw [eq_div_iff (RatFunc.algebraMap_ne_zero hg0)]
  exact h

theorem not_regularAt_of_mul_polynomial (f : RatFunc K) (g Q : Polynomial K) (w : K)
    (hg : g.eval w = 0) (hQ : Q.eval w ≠ 0) (h : f * toRF g = toRF Q) : ¬ RegularAt f w := by
  rintro ⟨p, s, hs, rfl⟩
  have hs0 : s ≠ 0 := fun hz => hs (by rw [hz]; simp)
  have hsne : toRF s ≠ 0 := RatFunc.algebraMap_ne_zero hs0
  have h2 : toRF p * toRF g = toRF Q * toRF s := by
    field_simp at h
    linear_combination h
  have h3 : p * g = Q * s := by
    refine RatFunc.algebraMap_injective K ?_
    simp only [map_mul]
    exact h2
  have h4 := congrArg (Polynomial.eval w) h3
  rw [Polynomial.eval_mul, Polynomial.eval_mul, hg, mul_zero] at h4
  exact (mul_ne_zero hQ hs) h4.symm

/-! ## The pole structure of an Euler-operator combination of the cotangent model -/

theorem not_regularAt_one_eulerCombination_cotModel [CharZero K] (a : ℕ → K) (c : K) (hc : c ≠ 0) (r : ℕ)
    (har : a r ≠ 0) : ¬ RegularAt (eulerCombination a r (cotModel c)) 1 := by
  refine not_regularAt_of_mul_polynomial _ (linFac K ^ (r + 1)) (eulerCombinationNum a c r) 1
    (by simp [linFac]) ?_ (eulerCombination_cotModel_mul a c r)
  rw [eval_eulerCombinationNum]
  exact mul_ne_zero har (eval_eulerNum_ne_zero c hc r)

theorem regularAt_of_ne_one_eulerCombination_cotModel (a : ℕ → K) (c : K) (r : ℕ) {w : K}
    (hw : w ≠ 1) : RegularAt (eulerCombination a r (cotModel c)) w := by
  refine regularAt_of_mul_polynomial _ (linFac K ^ (r + 1)) (eulerCombinationNum a c r) w ?_
    (eulerCombination_cotModel_mul a c r)
  rw [Polynomial.eval_pow, eval_linFac]
  exact pow_ne_zero _ (sub_ne_zero.mpr hw)

/-- **The double-sine descent obstruction.**  Let `q` be a non-root-of-unity, let
`b(X) = c (X+1)/(X-1)` be the rational model of the cotangent term on a multiplicative cylinder,
and let `A = ∑_{i ≤ r} a_i (X d/dX)^i` be a constant-coefficient Euler-operator polynomial with
nonzero top coefficient.  Then the `q`-difference equation

```text
A(b)(X) = h(qX) - h(X)
```

has no rational solution `h`.  This is the multiplicative-orbit residue contradiction of the
double-sine translation-annihilator theorem. -/
theorem not_dilationTelescoped_eulerCombination_cotModel [CharZero K]
    (q : K) (hq : q ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    (c : K) (hc : c ≠ 0) (a : ℕ → K) (r : ℕ) (har : a r ≠ 0) :
    ¬ ∃ h : RatFunc K, eulerCombination a r (cotModel c) = ratFuncScale q hq h - h := by
  refine not_dilationTelescoped_of_unique_multOrbit_pole q 1 hq one_ne_zero hqtor _
    (not_regularAt_one_eulerCombination_cotModel a c hc r har) ?_
  intro n hn
  rw [one_mul]
  exact regularAt_of_ne_one_eulerCombination_cotModel a c r (hqtor n hn)

/-! ## The two-cylinder form -/

/-- **The descended equation over the first cylinder's function field.**  The paired telescoping
theorem produces `g` in the two-cylinder field `ℂ(u₁, u₂)`, not in `ℂ(u₂)`.  No specialization of
the `u₁` factor is needed: all poles of `A(b)` and every point of the orbit `q^ℤ` lie in the
constant subfield `ℂ` of the base field `ℂ(u₁)`, so the orbit-balance obstruction applies verbatim
in `ℂ(u₁)(u₂) = ℂ(u₁, u₂)`. -/
theorem not_dilationTelescoped_twoCylinder
    (q : ℂ) (hq : q ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    (c : ℂ) (hc : c ≠ 0) (a : ℕ → ℂ) (r : ℕ) (har : a r ≠ 0) :
    ¬ ∃ h : RatFunc (RatFunc ℂ),
      eulerCombination (fun i => RatFunc.C (a i)) r (cotModel (RatFunc.C c))
        = ratFuncScale (RatFunc.C q) (by simpa using hq) h - h := by
  refine not_dilationTelescoped_eulerCombination_cotModel (K := RatFunc ℂ)
    (RatFunc.C q) (by simpa using hq) ?_ (RatFunc.C c) (by simpa using hc)
    (fun i => RatFunc.C (a i)) r (by simpa using har)
  intro n hn hcon
  refine hqtor n hn ((RatFunc.C : ℂ →+* RatFunc ℂ).injective ?_)
  rw [map_zpow₀, map_one]
  exact hcon

/-- **The double-sine descent obstruction in its period form.**  For an irrational period ratio
`θ = ω₁/ω₂` the multiplier `q = exp(2πi θ)` is not a root of unity, so no rational `h` solves the
descended paired telescoping equation `h(qX) - h(X) = A(b)(X)`. -/
theorem not_dilationTelescoped_irrationalPeriodRatio
    {θ : ℝ} (hθ : Irrational θ) (c : ℂ) (hc : c ≠ 0) (a : ℕ → ℂ) (r : ℕ) (har : a r ≠ 0) :
    ¬ ∃ h : RatFunc ℂ,
      eulerCombination a r (cotModel c)
        = ratFuncScale (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)))
            (Complex.exp_ne_zero _) h - h :=
  not_dilationTelescoped_eulerCombination_cotModel _ (Complex.exp_ne_zero _)
    (fun _ hn => exp_two_pi_I_zpow_ne_one hθ hn) c hc a r har

end

end GaloisForLFunctions.HTGeometry
