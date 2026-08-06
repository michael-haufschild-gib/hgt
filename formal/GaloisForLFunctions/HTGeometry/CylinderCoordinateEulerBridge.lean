import GaloisForLFunctions.HTGeometry.EulerOperatorDiagonal
import GaloisForLFunctions.HTGeometry.DoubleSineOrbitResidueObstruction

/-!
# The multiplicative cylinder coordinate: cotangent, Euler operator, and the analytic jets

The double-sine argument transports the equation

```text
(T_1 - 1) L_2 = ± (π/ω_2) cot(π z/ω_2)
```

to the multiplicative cylinder `u = exp(2πi z/ω_2)`.  Three coordinate facts are proved here,
unconditionally.

* `cos_div_sin_eq_cylinder` and `cotangentTerm_cylinder` — the cotangent is the value of the
  rational model `c (X+1)/(X-1)` with `c = iπ/ω`, whose numerator and denominator are the very
  polynomials defining `cotModel`.
* `deriv_comp_exp_mul` and `iteratedDeriv_comp_exp_mul` — differentiation in `z` is a nonzero
  scalar multiple of the Euler operator `u d/du` in the coordinate: the `n`-th `z`-derivative of a
  cylinder pullback is `a^n` times the `n`-th Euler jet.  Consequently a constant-coefficient
  differential operator of order `r` in `z` is a constant-coefficient Euler-operator polynomial of
  order `r` in the coordinate, with proportional top coefficient.
* `eulerOp_iterate_cotFun` and `eulerCombinationFun_eq` — the analytic Euler jets of the cotangent
  model are governed by exactly the polynomial recursion `eulerNum` of the rational model, so the
  analytic `A(b)` is the value of the rational `A(b)`.  This is what makes the orbit residue
  obstruction of `DoubleSineOrbitResidueObstruction` a statement about the actual cotangent term
  rather than about a formal stand-in.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem exp_mul_I_sq (w : ℂ) :
    Complex.exp (w * Complex.I) ^ 2 = Complex.exp (2 * Complex.I * w) := by
  rw [← Complex.exp_nat_mul]
  exact congrArg Complex.exp (by push_cast; ring)

theorem sin_ne_zero_of_exp_ne_one {w : ℂ} (h : Complex.exp (2 * Complex.I * w) ≠ 1) :
    Complex.sin w ≠ 0 := by
  intro hs
  apply h
  rw [← exp_mul_I_sq]
  have hE : Complex.exp (w * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hneg : Complex.exp (-w * Complex.I) = (Complex.exp (w * Complex.I))⁻¹ := by
    rw [← Complex.exp_neg]
    exact congrArg Complex.exp (by ring)
  rw [Complex.sin, hneg, div_eq_zero_iff] at hs
  rcases hs with hs | hs
  · rcases mul_eq_zero.mp hs with hs' | hs'
    · have h4 : (Complex.exp (w * Complex.I))⁻¹ = Complex.exp (w * Complex.I) :=
        sub_eq_zero.mp hs'
      have h5 : Complex.exp (w * Complex.I) ^ 2
          = Complex.exp (w * Complex.I) * (Complex.exp (w * Complex.I))⁻¹ := by
        rw [h4, sq]
      rw [h5, mul_inv_cancel₀ hE]
    · exact absurd hs' Complex.I_ne_zero
  · norm_num at hs

/-- **The cotangent in the multiplicative cylinder coordinate.** -/
theorem cos_div_sin_eq_cylinder (w : ℂ) (h : Complex.exp (2 * Complex.I * w) ≠ 1) :
    Complex.cos w / Complex.sin w
      = Complex.I * ((Complex.exp (2 * Complex.I * w) + 1)
          / (Complex.exp (2 * Complex.I * w) - 1)) := by
  have hE : Complex.exp (w * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hneg : Complex.exp (-w * Complex.I) = (Complex.exp (w * Complex.I))⁻¹ := by
    rw [← Complex.exp_neg]
    exact congrArg Complex.exp (by ring)
  have hsinne : Complex.sin w ≠ 0 := sin_ne_zero_of_exp_ne_one h
  have hden : Complex.exp (w * Complex.I) ^ 2 - 1 ≠ 0 := by
    rw [exp_mul_I_sq]
    exact sub_ne_zero.mpr h
  rw [div_eq_iff hsinne, Complex.cos, Complex.sin, hneg, ← exp_mul_I_sq]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem hasDerivAt_exp_mul (a z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (a * z)) (a * Complex.exp (a * z)) z := by
  have h := (((hasDerivAt_id z).const_mul a).cexp)
  simpa [mul_comm] using h

/-- **Differentiation in `z` is the Euler operator in the cylinder coordinate.** -/
theorem deriv_comp_exp_mul (a : ℂ) (f : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℂ f (Complex.exp (a * z))) :
    deriv (fun z => f (Complex.exp (a * z))) z = a * eulerOp f (Complex.exp (a * z)) := by
  have hcomp : HasDerivAt (fun z : ℂ => f (Complex.exp (a * z)))
      (deriv f (Complex.exp (a * z)) * (a * Complex.exp (a * z))) z :=
    hf.hasDerivAt.comp z (hasDerivAt_exp_mul a z)
  rw [hcomp.deriv, eulerOp]
  ring

theorem analyticOnNhd_eulerOp_iterate {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (n : ℕ) : AnalyticOnNhd ℂ (eulerOp^[n] f) U := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (analyticOnNhd_id (𝕜 := ℂ) (s := U)).mul (ih.deriv_of_isOpen hU)

/-- **The iterated coordinate law.**  On the region where `f` is analytic, the `n`-th derivative in
`z` of the cylinder pullback is `a^n` times the `n`-th Euler-operator jet. -/
theorem iteratedDeriv_comp_exp_mul (a : ℂ) (f : ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) :
    ∀ (n : ℕ) (z : ℂ), Complex.exp (a * z) ∈ U →
      iteratedDeriv n (fun z => f (Complex.exp (a * z))) z
        = a ^ n * (eulerOp^[n] f) (Complex.exp (a * z)) := by
  have hV : IsOpen ((fun z : ℂ => Complex.exp (a * z)) ⁻¹' U) :=
    hU.preimage (by fun_prop)
  intro n
  induction n with
  | zero => intro z _; simp
  | succ n ih =>
    intro z hz
    have hmem : z ∈ (fun z : ℂ => Complex.exp (a * z)) ⁻¹' U := hz
    have heq : (fun y => iteratedDeriv n (fun z => f (Complex.exp (a * z))) y)
        =ᶠ[nhds z] (fun y => a ^ n * (eulerOp^[n] f) (Complex.exp (a * y))) := by
      filter_upwards [hV.mem_nhds hmem] with y hy using ih y hy
    have hana := analyticOnNhd_eulerOp_iterate hU hf n
    have hdiff : DifferentiableAt ℂ (eulerOp^[n] f) (Complex.exp (a * z)) :=
      (hana _ hz).differentiableAt
    have hdiff2 : DifferentiableAt ℂ
        (fun y : ℂ => (eulerOp^[n] f) (Complex.exp (a * y))) z :=
      hdiff.comp z (hasDerivAt_exp_mul a z).differentiableAt
    rw [iteratedDeriv_succ, heq.deriv_eq, deriv_const_mul _ hdiff2,
      deriv_comp_exp_mul a _ z hdiff, Function.iterate_succ_apply']
    ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

/-- The cotangent term of the double-sine functional equation, read in the cylinder coordinate
`u = exp(2πi z/ω)`: it is the value of the rational model `c (X+1)/(X-1)` with `c = iπ/ω`. -/
theorem cotangentTerm_cylinder (ω : ℂ) (z : ℂ)
    (h : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z / ω) ≠ 1) :
    ((Real.pi : ℂ) / ω)
        * (Complex.cos ((Real.pi : ℂ) * z / ω) / Complex.sin ((Real.pi : ℂ) * z / ω))
      = Polynomial.eval (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z / ω))
            (Polynomial.C (Complex.I * (Real.pi : ℂ) / ω) * (Polynomial.X + Polynomial.C 1))
        / Polynomial.eval (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z / ω)) linFac := by
  have hexp : Complex.exp (2 * Complex.I * ((Real.pi : ℂ) * z / ω))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z / ω) :=
    congrArg Complex.exp (by ring)
  have hne : Complex.exp (2 * Complex.I * ((Real.pi : ℂ) * z / ω)) ≠ 1 := by
    rw [hexp]; exact h
  rw [cos_div_sin_eq_cylinder _ hne, hexp, eval_linFac]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X]
  ring

/-- The analytic cotangent model on the cylinder. -/
def cotFun (c : ℂ) : ℂ → ℂ := fun u => c * (u + 1) / (u - 1)

/-- **The analytic Euler-operator jets of the cotangent model have the algebraic numerators.**
The `i`-th Euler jet of `c (u+1)/(u-1)` is `eulerNum c i` over `(u-1)^(i+1)`, the same polynomial
recursion that governs the rational model. -/
theorem eulerOp_iterate_cotFun (c : ℂ) :
    ∀ (i : ℕ) (u : ℂ), u ≠ 1 →
      (eulerOp^[i] (cotFun c)) u = Polynomial.eval u (eulerNum c i) / (u - 1) ^ (i + 1) := by
  have hopen : IsOpen {u : ℂ | u ≠ 1} := isOpen_ne
  intro i
  induction i with
  | zero =>
    intro u _
    simp [cotFun, eulerNum]
  | succ n ih =>
    intro u hu
    have hu0 : u - 1 ≠ 0 := sub_ne_zero.mpr hu
    have heq : (eulerOp^[n] (cotFun c))
        =ᶠ[nhds u] (fun y => Polynomial.eval y (eulerNum c n) / (y - 1) ^ (n + 1)) := by
      filter_upwards [hopen.mem_nhds hu] with y hy using ih y hy
    have hnum : HasDerivAt (fun y : ℂ => Polynomial.eval y (eulerNum c n))
        (Polynomial.eval u (Polynomial.derivative (eulerNum c n))) u :=
      (eulerNum c n).hasDerivAt u
    have hden : HasDerivAt (fun y : ℂ => (y - 1) ^ (n + 1))
        (((n : ℂ) + 1) * (u - 1) ^ n) u := by
      have h1 : HasDerivAt (fun y : ℂ => y - 1) 1 u := (hasDerivAt_id u).sub_const 1
      have h2 : HasDerivAt (fun y : ℂ => (y - 1) ^ (n + 1))
          ((((n : ℕ) + 1 : ℕ) : ℂ) * (u - 1) ^ (n + 1 - 1) * 1) u := h1.pow (n + 1)
      simpa using h2
    have hdiv : HasDerivAt (fun y : ℂ => Polynomial.eval y (eulerNum c n) / (y - 1) ^ (n + 1))
        ((Polynomial.eval u (Polynomial.derivative (eulerNum c n)) * (u - 1) ^ (n + 1)
            - Polynomial.eval u (eulerNum c n) * (((n : ℂ) + 1) * (u - 1) ^ n))
          / ((u - 1) ^ (n + 1)) ^ 2) u :=
      hnum.div hden (pow_ne_zero _ hu0)
    rw [Function.iterate_succ_apply', eulerOp, heq.deriv_eq, hdiv.deriv, eulerNum]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
      eval_linFac]
    have hpow1 : (u - 1) ^ (n + 1) = (u - 1) ^ n * (u - 1) := pow_succ _ _
    have hpow2 : (u - 1) ^ (n + 1 + 1) = (u - 1) ^ n * (u - 1) ^ 2 := by ring
    have htn : (u - 1) ^ n ≠ 0 := pow_ne_zero _ hu0
    rw [hpow1, hpow2]
    field_simp
    push_cast
    ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

/-- The analytic Euler-operator combination of the cotangent model. -/
def eulerCombinationFun (a : ℕ → ℂ) (r : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun u => ∑ i ∈ Finset.range (r + 1), a i * (eulerOp^[i] f) u

/-- **The analytic and algebraic Euler combinations agree.**  Away from the fixed point `u = 1`,
the analytic operator applied to the cotangent model is the value of the rational model's
numerator over `(u-1)^(r+1)`. -/
theorem eulerCombinationFun_eq (a : ℕ → ℂ) (c : ℂ) (r : ℕ) (u : ℂ) (hu : u ≠ 1) :
    eulerCombinationFun a r (cotFun c) u
      = Polynomial.eval u (eulerCombinationNum a c r) / (u - 1) ^ (r + 1) := by
  have hu0 : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  rw [eulerCombinationFun, eulerCombinationNum, Polynomial.eval_finsetSum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsplit : (u - 1) ^ (r + 1) = (u - 1) ^ (i + 1) * (u - 1) ^ (r - i) := by
    rw [← pow_add]
    congr 1
    omega
  rw [eulerOp_iterate_cotFun c i u hu, hsplit]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, eval_linFac]
  field_simp

end

end GaloisForLFunctions.HTGeometry
