import GaloisForLFunctions.RHTower.EulerSourceJetJacobian
import GaloisForLFunctions.HTGeometry.SmoothNumbers
import Mathlib

/-!
# Degree-one Euler sources are finite-jet open but full-jet faithful

`RHTower/EulerSourceJetJacobian.lean` supplies the *algebraic* certificate for the card
`euler-source-finite-jet-local-openness`: the differential at the trivial degree-one Euler product
is a weighted Vandermonde map, and that map is bijective.  This file supplies the two *analytic*
halves the card still needed.

## The finite-jet map and its local openness

For distinct prime labels `p i` and a base point `s₀`, vary the degree-one local Euler factors
`(1 - a i · p i^{-s})^{-1}` near the trivial parameter `a = 0` and record the first `k`
`s`-derivatives at `s₀` of the negative logarithmic derivative

`F_a(s) = -L_a'(s)/L_a(s) = Σ_i (log p_i) · a_i p_i^{-s} / (1 - a_i p_i^{-s})`.

The `s`-derivatives are computed in closed form: writing `w = x p^{-s}`, the operator `∂_s` acts as
`-(log p)·w ∂_w`, so the `j`-th derivative of one local term is
`(log p)(-log p)^j A_j(w)/(1-w)^{j+1}` with `A_j` the Eulerian-type polynomials `eulerJetPoly`,
characterised by `A_0 = X` and `A_{j+1} = X((1-X)A_j' + (j+1)A_j)`.  Since `A_j(0) = 0` and
`A_j'(0) = 1`, the parameter derivative at the trivial product is exactly the ledgered weighted
Vandermonde entry `(log p_i) p_i^{-s₀} (-log p_i)^j`.  The holomorphic inverse-function theorem then
gives local openness and a local holomorphic inverse.

## All-prime full-jet faithfulness

For the bounded all-prime class `‖a_p‖ ≤ 1` the flux `F_a` is the Dirichlet series of the
prime-power coefficient stream `degreeOneEulerPrimeFluxCoeff a`, by geometric expansion along each
prime ray and the prime-power reindexing.  Its abscissa of absolute convergence is at most `1`, so
the flux is analytic on `Re s > 1`; equal full jets at one point of that half-plane force equal
germs, the identity theorem propagates the equality across the (convex) half-plane, and Dirichlet
uniqueness recovers every prime parameter.

## Main results

* `eulerFlux_eq_neg_logDeriv` — the flux is `-L_a'/L_a` for the finite Euler product `L_a`;
* `hasStrictFDerivAt_eulerJetMap` — the differential of the finite source-jet map at the trivial
  Euler product is the weighted Vandermonde Jacobian;
* `eulerJetMap_map_nhds_zero`, `eventually_exists_eulerJetMap` — **finite-jet local openness**:
  every sufficiently small `k`-jet is realised by a genuine finite degree-one Euler product;
* `eventuallyEq_zero_of_vanishing_on_eulerJetMap` — the finite-equation consequence: nothing
  holomorphic vanishes on all Euler-source jets without vanishing near the zero jet;
* `hasStrictFDerivAt_eulerJetLocalInverse`, `eulerJetMap_eventually_left_inverse`,
  `eulerJetMap_eventually_right_inverse` — the **local biholomorphism**;
* `lSeries_degreeOneEulerPrimeFluxCoeff_eq` — the Euler flux is the Dirichlet series of its
  prime-power coefficient stream on `Re s > 1`;
* `eventuallyEq_of_iteratedDeriv_eq` — equal full jets determine an analytic germ;
* `degreeOneEulerParameter_eq_of_iteratedDeriv_eq` — **all-prime full-jet faithfulness**.
-/

noncomputable section

namespace RHTower

open Complex Filter

/-! ### The Eulerian-type jet polynomials -/

/-- `eulerJetPoly j` is the polynomial `A_j` with `(w d/dw)^j (w/(1-w)) = A_j(w)/(1-w)^(j+1)`. -/
noncomputable def eulerJetPoly : ℕ → Polynomial ℂ
  | 0 => Polynomial.X
  | (j + 1) => Polynomial.X * ((1 - Polynomial.X) * Polynomial.derivative (eulerJetPoly j)
      + Polynomial.C ((j : ℂ) + 1) * eulerJetPoly j)

theorem eulerJetPoly_succ (j : ℕ) :
    eulerJetPoly (j + 1) = Polynomial.X * ((1 - Polynomial.X) *
      Polynomial.derivative (eulerJetPoly j) + Polynomial.C ((j : ℂ) + 1) * eulerJetPoly j) := rfl

@[simp] theorem eval_eulerJetPoly_zero (j : ℕ) : (eulerJetPoly j).eval 0 = 0 := by
  cases j with
  | zero => simp [eulerJetPoly]
  | succ j => simp [eulerJetPoly_succ]

theorem eval_derivative_eulerJetPoly_zero (j : ℕ) :
    (Polynomial.derivative (eulerJetPoly j)).eval 0 = 1 := by
  induction j with
  | zero => simp [eulerJetPoly]
  | succ j ih =>
      rw [eulerJetPoly_succ, Polynomial.derivative_mul, Polynomial.derivative_X]
      simp [ih]

/-! ### One local flux term and its `s`-derivatives -/

/-- The closed form of the `j`-th `s`-derivative of one degree-one Euler logarithmic-flux term
`(log p) x p^{-s} / (1 - x p^{-s})`. -/
noncomputable def localFluxJet (p : ℕ) (x : ℂ) (j : ℕ) (s : ℂ) : ℂ :=
  (Real.log p : ℂ) * (-(Real.log p : ℂ)) ^ j *
    (eulerJetPoly j).eval (x * (p : ℂ) ^ (-s)) / (1 - x * (p : ℂ) ^ (-s)) ^ (j + 1)

theorem localFluxJet_zero_eq (p : ℕ) (x s : ℂ) :
    localFluxJet p x 0 s =
      (Real.log p : ℂ) * (x * (p : ℂ) ^ (-s)) / (1 - x * (p : ℂ) ^ (-s)) := by
  simp [localFluxJet, eulerJetPoly]

@[simp] theorem localFluxJet_param_zero (p : ℕ) (j : ℕ) (s : ℂ) : localFluxJet p 0 j s = 0 := by
  simp [localFluxJet]

theorem hasDerivAt_const_cpow_neg {p : ℕ} (hp : 0 < p) (s : ℂ) :
    HasDerivAt (fun s : ℂ => (p : ℂ) ^ (-s))
      (-((Real.log p : ℂ) * (p : ℂ) ^ (-s))) s := by
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hlog : Complex.log ((p : ℕ) : ℂ) = ((Real.log p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p)]
  have h1 : HasDerivAt (fun s : ℂ => -s) (-1) s := (hasDerivAt_id s).neg
  have h2 := (Complex.hasStrictDerivAt_const_cpow (x := ((p : ℕ) : ℂ)) (y := -s)
    (Or.inl hp0)).hasDerivAt
  have h3 : HasDerivAt (fun s : ℂ => (p : ℂ) ^ (-s))
      ((p : ℂ) ^ (-s) * Complex.log ((p : ℕ) : ℂ) * (-1)) s := h2.comp s h1
  rw [hlog] at h3
  exact h3.congr_deriv (by ring)

theorem differentiable_const_cpow_neg {p : ℕ} (hp : 0 < p) :
    Differentiable ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) :=
  fun z => (hasDerivAt_const_cpow_neg hp z).differentiableAt

theorem isOpen_localFluxDomain (p : ℕ) (hp : 0 < p) (x : ℂ) :
    IsOpen {s : ℂ | x * (p : ℂ) ^ (-s) ≠ 1} :=
  isOpen_ne.preimage (continuous_const.mul (differentiable_const_cpow_neg hp).continuous)

/-- **The jet recursion.**  Off the polar set the closed forms are the successive `s`-derivatives
of one another. -/
theorem hasDerivAt_localFluxJet {p : ℕ} (hp : 0 < p) (x : ℂ) (j : ℕ) {s : ℂ}
    (h : x * (p : ℂ) ^ (-s) ≠ 1) :
    HasDerivAt (localFluxJet p x j) (localFluxJet p x (j + 1) s) s := by
  set c : ℂ := (Real.log p : ℂ) with hc
  set w : ℂ := x * (p : ℂ) ^ (-s) with hwdef
  have hd0 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hw : HasDerivAt (fun s : ℂ => x * (p : ℂ) ^ (-s)) (-(c * w)) s :=
    ((hasDerivAt_const_cpow_neg hp s).const_mul x).congr_deriv (by rw [hwdef]; ring)
  have hA0 := ((eulerJetPoly j).hasDerivAt w).comp s hw
  have hA : HasDerivAt (fun s : ℂ => (eulerJetPoly j).eval (x * (p : ℂ) ^ (-s)))
      ((eulerJetPoly j).derivative.eval w * -(c * w)) s := hA0
  have h1 : HasDerivAt (fun s : ℂ => 1 - x * (p : ℂ) ^ (-s)) (c * w) s :=
    (hw.const_sub 1).congr_deriv (by ring)
  have hden : HasDerivAt (fun s : ℂ => (1 - x * (p : ℂ) ^ (-s)) ^ (j + 1))
      (((j + 1 : ℕ) : ℂ) * (1 - w) ^ j * (c * w)) s := h1.pow (j + 1)
  have hnum : HasDerivAt (fun s : ℂ => c * (-c) ^ j * (eulerJetPoly j).eval (x * (p : ℂ) ^ (-s)))
      (c * (-c) ^ j * ((eulerJetPoly j).derivative.eval w * -(c * w))) s := hA.const_mul _
  have hdenne : (1 - w) ^ (j + 1) ≠ 0 := pow_ne_zero _ hd0
  have hq : HasDerivAt (localFluxJet p x j)
      ((c * (-c) ^ j * ((eulerJetPoly j).derivative.eval w * -(c * w)) * (1 - w) ^ (j + 1)
        - c * (-c) ^ j * (eulerJetPoly j).eval w
          * (((j + 1 : ℕ) : ℂ) * (1 - w) ^ j * (c * w))) / ((1 - w) ^ (j + 1)) ^ 2) s :=
    hnum.div hden hdenne
  refine hq.congr_deriv ?_
  rw [localFluxJet, eulerJetPoly_succ]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_C, ← hwdef, ← hc]
  rw [div_eq_div_iff (pow_ne_zero _ hdenne) (pow_ne_zero _ hd0)]
  simp only [pow_succ]
  push_cast
  ring

/-! ### Iterated `s`-derivatives -/

/-- Off the polar set the `j`-th iterated `s`-derivative of one flux term is the closed form. -/
theorem iteratedDeriv_localFluxJet {p : ℕ} (hp : 0 < p) (x : ℂ) (j : ℕ) :
    ∀ {s : ℂ}, x * (p : ℂ) ^ (-s) ≠ 1 →
      iteratedDeriv j (localFluxJet p x 0) s = localFluxJet p x j s := by
  induction j with
  | zero => intro s _; simp [iteratedDeriv_zero]
  | succ j ih =>
      intro s h
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv j (localFluxJet p x 0) =ᶠ[nhds s] localFluxJet p x j :=
        Filter.eventuallyEq_of_mem ((isOpen_localFluxDomain p hp x).mem_nhds h)
          (fun t ht => ih ht)
      rw [heq.deriv_eq]
      exact (hasDerivAt_localFluxJet hp x j h).deriv

/-! ### The finite Euler product and its logarithmic flux -/

/-- The `j`-th `s`-derivative of the total logarithmic flux of a finite degree-one Euler product. -/
noncomputable def eulerFluxJet {k : ℕ} (p : Fin k → ℕ) (a : Fin k → ℂ) (j : ℕ) (s : ℂ) : ℂ :=
  ∑ i, localFluxJet (p i) (a i) j s

/-- `F_a(s) = -L_a'(s)/L_a(s) = Σ_i (log p_i) a_i p_i^{-s}/(1 - a_i p_i^{-s})`, the negative
logarithmic derivative of the degree-one Euler product with parameters `a`. -/
noncomputable def eulerFlux {k : ℕ} (p : Fin k → ℕ) (a : Fin k → ℂ) (s : ℂ) : ℂ :=
  eulerFluxJet p a 0 s

theorem eulerFlux_eq {k : ℕ} (p : Fin k → ℕ) (a : Fin k → ℂ) (s : ℂ) :
    eulerFlux p a s =
      ∑ i, (Real.log (p i) : ℂ) * (a i * (p i : ℂ) ^ (-s)) / (1 - a i * (p i : ℂ) ^ (-s)) := by
  simp only [eulerFlux, eulerFluxJet]
  exact Finset.sum_congr rfl fun i _ => localFluxJet_zero_eq _ _ _

theorem hasDerivAt_one_sub_param {p : ℕ} (hp : 0 < p) (x : ℂ) (s : ℂ) :
    HasDerivAt (fun s : ℂ => 1 - x * (p : ℂ) ^ (-s))
      ((Real.log p : ℂ) * (x * (p : ℂ) ^ (-s))) s :=
  (((hasDerivAt_const_cpow_neg hp s).const_mul x).const_sub 1).congr_deriv (by ring)

/-- The finite degree-one Euler product `L_a(s) = ∏_i (1 - a_i p_i^{-s})^{-1}`. -/
noncomputable def eulerProductL {k : ℕ} (p : Fin k → ℕ) (a : Fin k → ℂ) (s : ℂ) : ℂ :=
  ∏ i, (1 - a i * (p i : ℂ) ^ (-s))⁻¹

/-- **The flux really is the negative logarithmic derivative of the Euler product**, so the jet map
below is the card's `Φ_{s₀,k}` and not merely a hand-written series. -/
theorem eulerFlux_eq_neg_logDeriv {k : ℕ} {p : Fin k → ℕ} (hp : ∀ i, 0 < p i) (a : Fin k → ℂ)
    {s : ℂ} (h : ∀ i, a i * (p i : ℂ) ^ (-s) ≠ 1) :
    eulerFlux p a s = -logDeriv (eulerProductL p a) s := by
  have hne : ∀ i, (1 : ℂ) - a i * (p i : ℂ) ^ (-s) ≠ 0 := fun i => sub_ne_zero.mpr (Ne.symm (h i))
  have hdsub : ∀ i, DifferentiableAt ℂ (fun s : ℂ => 1 - a i * (p i : ℂ) ^ (-s)) s :=
    fun i => (hasDerivAt_one_sub_param (hp i) (a i) s).differentiableAt
  have hd : ∀ i, DifferentiableAt ℂ (fun s : ℂ => (1 - a i * (p i : ℂ) ^ (-s))⁻¹) s :=
    fun i => (hdsub i).inv (hne i)
  have hL : logDeriv (eulerProductL p a) s
      = ∑ i, logDeriv (fun s : ℂ => (1 - a i * (p i : ℂ) ^ (-s))⁻¹) s :=
    logDeriv_prod (fun i _ => inv_ne_zero (hne i)) (fun i _ => hd i)
  have hterm : ∀ i, logDeriv (fun s : ℂ => (1 - a i * (p i : ℂ) ^ (-s))⁻¹) s
      = -((Real.log (p i) : ℂ) * (a i * (p i : ℂ) ^ (-s)) / (1 - a i * (p i : ℂ) ^ (-s))) := by
    intro i
    have hinv : (fun s : ℂ => (1 - a i * (p i : ℂ) ^ (-s))⁻¹)
        = fun s : ℂ => 1 / (1 - a i * (p i : ℂ) ^ (-s)) := by
      funext t; rw [one_div]
    rw [hinv, logDeriv_div s one_ne_zero (hne i) (differentiableAt_const 1) (hdsub i),
      logDeriv_const]
    simp only [Pi.zero_apply, zero_sub]
    rw [logDeriv_apply, (hasDerivAt_one_sub_param (hp i) (a i) s).deriv]
  rw [hL]
  simp only [hterm, Finset.sum_neg_distrib, neg_neg]
  exact eulerFlux_eq p a s

theorem isOpen_eulerFluxDomain {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, 0 < p i) (a : Fin k → ℂ) :
    IsOpen {s : ℂ | ∀ i, a i * (p i : ℂ) ^ (-s) ≠ 1} := by
  have hset : {s : ℂ | ∀ i, a i * (p i : ℂ) ^ (-s) ≠ 1}
      = ⋂ i, {s : ℂ | a i * (p i : ℂ) ^ (-s) ≠ 1} := by
    ext s; simp
  rw [hset]
  exact isOpen_iInter_of_finite fun i => isOpen_localFluxDomain _ (hp i) _

theorem hasDerivAt_eulerFluxJet {k : ℕ} {p : Fin k → ℕ} (hp : ∀ i, 0 < p i) (a : Fin k → ℂ)
    (j : ℕ) {s : ℂ} (h : ∀ i, a i * (p i : ℂ) ^ (-s) ≠ 1) :
    HasDerivAt (eulerFluxJet p a j) (eulerFluxJet p a (j + 1) s) s :=
  HasDerivAt.fun_sum fun i _ => hasDerivAt_localFluxJet (hp i) (a i) j (h i)

/-- **The finite jets of the Euler logarithmic flux are the closed forms.** -/
theorem iteratedDeriv_eulerFlux {k : ℕ} {p : Fin k → ℕ} (hp : ∀ i, 0 < p i) (a : Fin k → ℂ)
    (j : ℕ) : ∀ {s : ℂ}, (∀ i, a i * (p i : ℂ) ^ (-s) ≠ 1) →
      iteratedDeriv j (eulerFlux p a) s = eulerFluxJet p a j s := by
  induction j with
  | zero => intro s _; simp [iteratedDeriv_zero, eulerFlux]
  | succ j ih =>
      intro s h
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv j (eulerFlux p a) =ᶠ[nhds s] eulerFluxJet p a j :=
        Filter.eventuallyEq_of_mem ((isOpen_eulerFluxDomain p hp a).mem_nhds h)
          (fun t ht => ih ht)
      rw [heq.deriv_eq]
      exact (hasDerivAt_eulerFluxJet hp a j h).deriv

/-! ### The differential of the jet map at the trivial Euler product -/

/-- **The parameter derivative of one jet coordinate at the trivial product.**  Only the first
power of the local parameter contributes, giving the weighted Vandermonde entry. -/
theorem hasStrictDerivAt_localFluxJet_param (p : ℕ) (j : ℕ) (s₀ : ℂ) :
    HasStrictDerivAt (fun x : ℂ => localFluxJet p x j s₀)
      ((Real.log p : ℂ) * (-(Real.log p : ℂ)) ^ j * (p : ℂ) ^ (-s₀)) 0 := by
  set c : ℂ := (Real.log p : ℂ) with hc
  set u : ℂ := (p : ℂ) ^ (-s₀) with hu
  have hmul : HasStrictDerivAt (fun x : ℂ => x * u) u 0 := by
    simpa using (hasStrictDerivAt_id (0 : ℂ)).mul_const u
  have hnum : HasStrictDerivAt (fun y : ℂ => c * (-c) ^ j * (eulerJetPoly j).eval y)
      (c * (-c) ^ j * (eulerJetPoly j).derivative.eval 0) 0 :=
    ((eulerJetPoly j).hasStrictDerivAt 0).const_mul _
  have hsub : HasStrictDerivAt (fun y : ℂ => 1 - y) (-1 : ℂ) 0 := by
    simpa using (hasStrictDerivAt_id (0 : ℂ)).const_sub 1
  have hden : HasStrictDerivAt (fun y : ℂ => (1 - y) ^ (j + 1))
      (((j + 1 : ℕ) : ℂ) * ((1 : ℂ) - 0) ^ j * (-1)) 0 := hsub.pow (j + 1)
  have hd0 : ((1 : ℂ) - 0) ^ (j + 1) ≠ 0 := by norm_num
  have hG : HasStrictDerivAt
      (fun y : ℂ => c * (-c) ^ j * (eulerJetPoly j).eval y / (1 - y) ^ (j + 1))
      (c * (-c) ^ j) 0 :=
    (hnum.div hden hd0).congr_deriv (by
      simp [eval_eulerJetPoly_zero, eval_derivative_eulerJetPoly_zero])
  have hzu : (0 : ℂ) * u = 0 := zero_mul u
  have hG' : HasStrictDerivAt
      (fun y : ℂ => c * (-c) ^ j * (eulerJetPoly j).eval y / (1 - y) ^ (j + 1))
      (c * (-c) ^ j) ((0 : ℂ) * u) := by rw [hzu]; exact hG
  exact hG'.comp 0 hmul

/-- The Jacobian at the trivial Euler product, as a continuous linear map. -/
noncomputable def eulerJetJacobianCLM {k : ℕ} (p : Fin k → ℕ) (s₀ : ℂ) :
    (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) :=
  ContinuousLinearMap.pi fun j : Fin k => ∑ i : Fin k,
    ((Real.log (p i) : ℂ) * (-(Real.log (p i) : ℂ)) ^ (j : ℕ) * (p i : ℂ) ^ (-s₀)) •
      (ContinuousLinearMap.proj i : (Fin k → ℂ) →L[ℂ] ℂ)

/-- The continuous-linear Jacobian is the ledgered weighted Vandermonde map. -/
theorem eulerJetJacobianCLM_apply {k : ℕ} (p : Fin k → ℕ) (s₀ : ℂ) (a : Fin k → ℂ) :
    eulerJetJacobianCLM p s₀ a = eulerSourceJetJacobian p s₀ a := by
  funext j
  simp only [eulerJetJacobianCLM, eulerSourceJetJacobian, ContinuousLinearMap.pi_apply,
    FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The finite source-jet map -/

/-- The finite source-jet map `Φ_{s₀,k}`: the first `k` `s`-derivatives at `s₀` of the negative
logarithmic derivative of the degree-one Euler product with parameters `a`. -/
noncomputable def eulerJetMap {k : ℕ} (p : Fin k → ℕ) (s₀ : ℂ) (a : Fin k → ℂ) : Fin k → ℂ :=
  fun j => iteratedDeriv (j : ℕ) (eulerFlux p a) s₀

/-- The closed form of the jet map, valid off the polar set. -/
noncomputable def eulerJetForm {k : ℕ} (p : Fin k → ℕ) (s₀ : ℂ) (a : Fin k → ℂ) : Fin k → ℂ :=
  fun j => eulerFluxJet p a (j : ℕ) s₀

theorem isOpen_eulerParamDomain {k : ℕ} (p : Fin k → ℕ) (s₀ : ℂ) :
    IsOpen {a : Fin k → ℂ | ∀ i, a i * (p i : ℂ) ^ (-s₀) ≠ 1} := by
  have hset : {a : Fin k → ℂ | ∀ i, a i * (p i : ℂ) ^ (-s₀) ≠ 1}
      = ⋂ i, {a : Fin k → ℂ | a i * (p i : ℂ) ^ (-s₀) ≠ 1} := by
    ext a; simp
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_ne.preimage ?_
  exact (continuous_apply i).mul continuous_const

theorem eulerJetMap_eventuallyEq_form {k : ℕ} {p : Fin k → ℕ} (hp : ∀ i, 0 < p i) (s₀ : ℂ) :
    eulerJetMap p s₀ =ᶠ[nhds (0 : Fin k → ℂ)] eulerJetForm p s₀ := by
  refine Filter.eventuallyEq_of_mem
    ((isOpen_eulerParamDomain p s₀).mem_nhds (fun i => ?_)) (fun a ha => ?_)
  · simp
  · funext j
    exact iteratedDeriv_eulerFlux hp a (j : ℕ) ha

/-- **The differential of the finite source-jet map at the trivial Euler product** is the weighted
Vandermonde Jacobian.  This is the analytic half of the card's finite-jet openness theorem. -/
theorem hasStrictFDerivAt_eulerJetForm {k : ℕ} (p : Fin k → ℕ) (s₀ : ℂ) :
    HasStrictFDerivAt (eulerJetForm p s₀) (eulerJetJacobianCLM p s₀) 0 := by
  rw [hasStrictFDerivAt_pi']
  intro j
  have hi : ∀ i : Fin k, HasStrictFDerivAt
      (fun a : Fin k → ℂ => localFluxJet (p i) (a i) (j : ℕ) s₀)
      (((Real.log (p i) : ℂ) * (-(Real.log (p i) : ℂ)) ^ (j : ℕ) * (p i : ℂ) ^ (-s₀)) •
        (ContinuousLinearMap.proj i : (Fin k → ℂ) →L[ℂ] ℂ)) 0 := by
    intro i
    have hproj : HasStrictFDerivAt (⇑(ContinuousLinearMap.proj i : (Fin k → ℂ) →L[ℂ] ℂ))
        (ContinuousLinearMap.proj i : (Fin k → ℂ) →L[ℂ] ℂ) 0 :=
      (ContinuousLinearMap.proj i : (Fin k → ℂ) →L[ℂ] ℂ).hasStrictFDerivAt
    have hcomp : HasStrictFDerivAt
        ((fun x : ℂ => localFluxJet (p i) x (j : ℕ) s₀) ∘
          ⇑(ContinuousLinearMap.proj i : (Fin k → ℂ) →L[ℂ] ℂ))
        (((Real.log (p i) : ℂ) * (-(Real.log (p i) : ℂ)) ^ (j : ℕ) * (p i : ℂ) ^ (-s₀)) •
          (ContinuousLinearMap.proj i : (Fin k → ℂ) →L[ℂ] ℂ)) 0 :=
      HasStrictDerivAt.comp_hasStrictFDerivAt 0
        (hasStrictDerivAt_localFluxJet_param (p i) (j : ℕ) s₀) hproj
    exact hcomp
  have hsum := HasStrictFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin k)))
    (fun i _ => hi i)
  refine hsum.congr_fderiv ?_
  rw [eulerJetJacobianCLM, ContinuousLinearMap.proj_pi]

theorem hasStrictFDerivAt_eulerJetMap {k : ℕ} {p : Fin k → ℕ} (hp : ∀ i, 0 < p i) (s₀ : ℂ) :
    HasStrictFDerivAt (eulerJetMap p s₀) (eulerJetJacobianCLM p s₀) 0 :=
  (hasStrictFDerivAt_eulerJetForm p s₀).congr_of_eventuallyEq
    (eulerJetMap_eventuallyEq_form hp s₀).symm

/-! ### The holomorphic inverse-function theorem: finite-jet local openness -/

theorem eulerJetJacobianCLM_bijective {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) (s₀ : ℂ) :
    Function.Bijective (eulerJetJacobianCLM p s₀) := by
  have hfun : ⇑(eulerJetJacobianCLM p s₀) = eulerSourceJetJacobian p s₀ := by
    funext a
    exact eulerJetJacobianCLM_apply p s₀ a
  rw [hfun]
  exact eulerSourceJetJacobian_bijective p hp hpinj s₀

/-- The weighted Vandermonde Jacobian as a continuous linear **equivalence**. -/
noncomputable def eulerJetJacobianEquiv {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) (s₀ : ℂ) : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ) :=
  ContinuousLinearEquiv.ofBijective (eulerJetJacobianCLM p s₀)
    (LinearMap.ker_eq_bot.mpr (eulerJetJacobianCLM_bijective p hp hpinj s₀).1)
    (LinearMap.range_eq_top.mpr (eulerJetJacobianCLM_bijective p hp hpinj s₀).2)

@[simp] theorem eulerJetJacobianEquiv_coe {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) (s₀ : ℂ) :
    ((eulerJetJacobianEquiv p hp hpinj s₀ : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ)) :
        (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) = eulerJetJacobianCLM p s₀ := rfl

/-- The trivial Euler product has the zero jet. -/
@[simp] theorem eulerJetMap_zero {k : ℕ} {p : Fin k → ℕ} (hp : ∀ i, 0 < p i) (s₀ : ℂ) :
    eulerJetMap p s₀ 0 = 0 := by
  funext j
  rw [eulerJetMap, iteratedDeriv_eulerFlux hp 0 (j : ℕ) (fun i => by simp)]
  simp [eulerFluxJet]

theorem hasStrictFDerivAt_eulerJetMap_equiv {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) (s₀ : ℂ) :
    HasStrictFDerivAt (eulerJetMap p s₀)
      ((eulerJetJacobianEquiv p hp hpinj s₀ : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ)) :
        (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) 0 :=
  hasStrictFDerivAt_eulerJetMap (fun i => Nat.zero_lt_one.trans (hp i)) s₀

/-- **Finite-jet local openness.**  The finite source-jet map pushes the neighbourhood filter of the
trivial Euler product onto the neighbourhood filter of the zero jet. -/
theorem eulerJetMap_map_nhds_zero {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) (s₀ : ℂ) :
    Filter.map (eulerJetMap p s₀) (nhds 0) = nhds (0 : Fin k → ℂ) := by
  have h := (hasStrictFDerivAt_eulerJetMap_equiv p hp hpinj s₀).map_nhds_eq_of_equiv
  rwa [eulerJetMap_zero (fun i => Nat.zero_lt_one.trans (hp i)) s₀] at h

/-- The jet map is open at the trivial Euler product. -/
theorem eulerJetMap_image_mem_nhds {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) (s₀ : ℂ) {U : Set (Fin k → ℂ)}
    (hU : U ∈ nhds (0 : Fin k → ℂ)) :
    eulerJetMap p s₀ '' U ∈ nhds (0 : Fin k → ℂ) := by
  rw [← eulerJetMap_map_nhds_zero p hp hpinj s₀]
  exact Filter.image_mem_map hU

/-- **Every sufficiently small `k`-jet is the logarithmic-flux jet of a genuine finite degree-one
Euler product.**  This is the card's finite-jet fullness statement. -/
theorem eventually_exists_eulerJetMap {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) (s₀ : ℂ) :
    ∀ᶠ c in nhds (0 : Fin k → ℂ), ∃ a : Fin k → ℂ, eulerJetMap p s₀ a = c := by
  filter_upwards [eulerJetMap_image_mem_nhds p hp hpinj s₀ Filter.univ_mem] with c hc
  obtain ⟨a, -, ha⟩ := hc
  exact ⟨a, ha⟩

/-- **The finite-equation consequence.**  Any function vanishing on all finite Euler-source jets
vanishes on a whole neighbourhood of the zero jet: no finite jet carries an equation that separates
the degree-one Euler class. -/
theorem eventuallyEq_zero_of_vanishing_on_eulerJetMap {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) (s₀ : ℂ) {H : (Fin k → ℂ) → ℂ}
    (hH : ∀ a : Fin k → ℂ, H (eulerJetMap p s₀ a) = 0) :
    ∀ᶠ c in nhds (0 : Fin k → ℂ), H c = 0 := by
  filter_upwards [eventually_exists_eulerJetMap p hp hpinj s₀] with c hc
  obtain ⟨a, ha⟩ := hc
  rw [← ha]
  exact hH a

/-! ### The local biholomorphism -/

/-- The local holomorphic inverse of the finite source-jet map at the trivial Euler product. -/
noncomputable def eulerJetLocalInverse {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) (s₀ : ℂ) : (Fin k → ℂ) → (Fin k → ℂ) :=
  HasStrictFDerivAt.localInverse (eulerJetMap p s₀) (eulerJetJacobianEquiv p hp hpinj s₀) 0
    (hasStrictFDerivAt_eulerJetMap_equiv p hp hpinj s₀)

/-- **Local biholomorphism.**  The local inverse of the finite source-jet map is itself strictly
differentiable at the zero jet, with the inverse Jacobian as derivative. -/
theorem hasStrictFDerivAt_eulerJetLocalInverse {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) (s₀ : ℂ) :
    HasStrictFDerivAt (eulerJetLocalInverse p hp hpinj s₀)
      (((eulerJetJacobianEquiv p hp hpinj s₀).symm : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ)) :
        (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) (0 : Fin k → ℂ) := by
  have h := (hasStrictFDerivAt_eulerJetMap_equiv p hp hpinj s₀).to_localInverse
  rwa [eulerJetMap_zero (fun i => Nat.zero_lt_one.trans (hp i)) s₀] at h

theorem eulerJetMap_eventually_left_inverse {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) (s₀ : ℂ) :
    ∀ᶠ a in nhds (0 : Fin k → ℂ),
      eulerJetLocalInverse p hp hpinj s₀ (eulerJetMap p s₀ a) = a :=
  (hasStrictFDerivAt_eulerJetMap_equiv p hp hpinj s₀).eventually_left_inverse

theorem eulerJetMap_eventually_right_inverse {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) (s₀ : ℂ) :
    ∀ᶠ c in nhds (0 : Fin k → ℂ),
      eulerJetMap p s₀ (eulerJetLocalInverse p hp hpinj s₀ c) = c := by
  have h := (hasStrictFDerivAt_eulerJetMap_equiv p hp hpinj s₀).eventually_right_inverse
  rwa [eulerJetMap_zero (fun i => Nat.zero_lt_one.trans (hp i)) s₀] at h

/-! ### All-prime full-jet faithfulness: the analytic step -/

/-- The bounded degree-one Euler flux coefficients are dominated by von Mangoldt. -/
theorem norm_degreeOneEulerPrimeFluxCoeff_le_vonMangoldt {a : Nat.Primes → ℂ}
    (ha : ∀ p, ‖a p‖ ≤ 1) (n : ℕ) :
    ‖degreeOneEulerPrimeFluxCoeff a n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  have hbd : ∀ q : ℕ, ‖(if hq : q.Prime then a ⟨q, hq⟩ else 0)‖ ≤ 1 := by
    intro q
    by_cases hq : q.Prime
    · rw [dif_pos hq]; exact ha _
    · rw [dif_neg hq]; simp
  rw [degreeOneEulerPrimeFluxCoeff, degreeOneEulerFluxCoeff,
    ArithmeticFunction.vonMangoldt_apply]
  by_cases hn : IsPrimePow n
  · rw [if_pos hn, if_pos hn]
    have hq : (Nat.minFac n).Prime := Nat.minFac_prime hn.ne_one
    have hlog : (0 : ℝ) ≤ Real.log (Nat.minFac n) :=
      Real.log_nonneg (by exact_mod_cast hq.one_lt.le)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    have hp1 : ‖(if hq' : (Nat.minFac n).Prime then a ⟨Nat.minFac n, hq'⟩ else 0)‖ ^
        (n.factorization (Nat.minFac n)) ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (hbd _)
    simpa using mul_le_mul_of_nonneg_left hp1 hlog
  · rw [if_neg hn, if_neg hn]
    simp

/-- The Euler-flux Dirichlet series of a bounded all-prime parameter field converges absolutely on
the Euler half-plane. -/
theorem lSeriesSummable_degreeOneEulerPrimeFluxCoeff {a : Nat.Primes → ℂ}
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (degreeOneEulerPrimeFluxCoeff a) s := by
  have hΛ : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hnorm : Summable fun n =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ :=
    summable_norm_iff.mpr hΛ
  refine Summable.of_norm_bounded hnorm fun n => ?_
  refine LSeries.norm_term_le s ?_
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]
  exact norm_degreeOneEulerPrimeFluxCoeff_le_vonMangoldt ha n

theorem abscissaOfAbsConv_degreeOneEulerPrimeFluxCoeff_le {a : Nat.Primes → ℂ}
    (ha : ∀ p, ‖a p‖ ≤ 1) :
    LSeries.abscissaOfAbsConv (degreeOneEulerPrimeFluxCoeff a) ≤ ((1 : ℝ) : EReal) := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun x hx => ?_
  exact lSeriesSummable_degreeOneEulerPrimeFluxCoeff ha (by simpa using hx)

theorem abscissaOfAbsConv_degreeOneEulerPrimeFluxCoeff_lt_top {a : Nat.Primes → ℂ}
    (ha : ∀ p, ‖a p‖ ≤ 1) :
    LSeries.abscissaOfAbsConv (degreeOneEulerPrimeFluxCoeff a) < ⊤ :=
  lt_of_le_of_lt (abscissaOfAbsConv_degreeOneEulerPrimeFluxCoeff_le ha) (EReal.coe_lt_top 1)

/-- The all-prime degree-one Euler logarithmic flux
`F_a(s) = Σ_p (log p) a_p p^{-s} / (1 - a_p p^{-s})`. -/
noncomputable def primeEulerFlux (a : Nat.Primes → ℂ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes,
    (Real.log (p : ℕ) : ℂ) * (a p * ((p : ℕ) : ℂ) ^ (-s)) / (1 - a p * ((p : ℕ) : ℂ) ^ (-s))

theorem norm_prime_param_cpow_lt_one {a : Nat.Primes → ℂ} (ha : ∀ p, ‖a p‖ ≤ 1)
    (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) : ‖a p * ((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.property.two_le
  have hppos : 0 < (p : ℕ) := p.property.pos
  have hcp : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s).re :=
    Complex.norm_natCast_cpow_of_pos hppos _
  have hlt : ((p : ℕ) : ℝ) ^ (-s).re < 1 := by
    rw [Complex.neg_re]
    refine Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  calc ‖a p * ((p : ℕ) : ℂ) ^ (-s)‖ = ‖a p‖ * ‖((p : ℕ) : ℂ) ^ (-s)‖ := norm_mul _ _
    _ ≤ 1 * ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
        gcongr
        exact ha p
    _ = ((p : ℕ) : ℝ) ^ (-s).re := by rw [one_mul, hcp]
    _ < 1 := hlt

/-- **The Euler flux is the Dirichlet series of its prime-power coefficient stream.**  This is the
expansion step of the card's full-jet faithfulness argument. -/
theorem lSeries_degreeOneEulerPrimeFluxCoeff_eq {a : Nat.Primes → ℂ} (ha : ∀ p, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (degreeOneEulerPrimeFluxCoeff a) s = primeEulerFlux a s := by
  have hsum : Summable (LSeries.term (degreeOneEulerPrimeFluxCoeff a) s) :=
    lSeriesSummable_degreeOneEulerPrimeFluxCoeff ha hs
  have hsupp : Function.support (LSeries.term (degreeOneEulerPrimeFluxCoeff a) s)
      ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra hnp
    refine hn ?_
    rw [LSeries.term_def]
    split_ifs with h0
    · rfl
    · rw [degreeOneEulerPrimeFluxCoeff,
        degreeOneEulerFluxCoeff_eq_zero_of_not_isPrimePow _ hnp, zero_div]
  rw [LSeries, tsum_eq_tsum_primes_of_support_subset_prime_powers hsum hsupp, primeEulerFlux]
  refine tsum_congr fun p => ?_
  have hz : ‖a p * ((p : ℕ) : ℂ) ^ (-s)‖ < 1 := norm_prime_param_cpow_lt_one ha p hs
  have hterm : ∀ k : ℕ, LSeries.term (degreeOneEulerPrimeFluxCoeff a) s ((p : ℕ) ^ (k + 1))
      = (Real.log (p : ℕ) : ℂ) * (a p * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) := by
    intro k
    have hne : ((p : ℕ) ^ (k + 1)) ≠ 0 := pow_ne_zero _ p.property.pos.ne'
    rw [LSeries.term_of_ne_zero hne, degreeOneEulerPrimeFluxCoeff,
      degreeOneEulerFluxCoeff_prime_pow _ p.property (Nat.succ_ne_zero k)]
    rw [div_eq_mul_inv, ← Complex.cpow_neg,
      GaloisForLFunctions.cpow_nat_prime_power p (k + 1) s, mul_pow]
    simp only [dif_pos p.property, Subtype.coe_eta, Nat.succ_eq_add_one]
    ring
  simp_rw [hterm]
  have hgeom : ∑' k : ℕ, (a p * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1)
      = (a p * ((p : ℕ) : ℂ) ^ (-s)) / (1 - a p * ((p : ℕ) : ℂ) ^ (-s)) := by
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hz, div_eq_mul_inv]
  rw [tsum_mul_left, hgeom]
  ring

/-! #### The germ is determined by the full jet -/

/-- **Equal full jets determine the germ.**  Two functions analytic at a point whose iterated
derivatives agree in every order agree on a neighbourhood of that point. -/
theorem eventuallyEq_of_iteratedDeriv_eq {f g : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (h : ∀ n : ℕ, iteratedDeriv n f x = iteratedDeriv n g x) :
    f =ᶠ[nhds x] g := by
  obtain ⟨p, hp⟩ : ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesAt f p x := hf
  obtain ⟨q, hq⟩ : ∃ q : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesAt g q x := hg
  obtain ⟨rf, hrf⟩ : ∃ r, HasFPowerSeriesOnBall f p x r := hp
  obtain ⟨rg, hrg⟩ : ∃ r, HasFPowerSeriesOnBall g q x r := hq
  have hr : 0 < min rf rg := lt_min hrf.r_pos hrg.r_pos
  have hf' : HasFPowerSeriesOnBall f p x (min rf rg) := hrf.mono hr (min_le_left _ _)
  have hg' : HasFPowerSeriesOnBall g q x (min rf rg) := hrg.mono hr (min_le_right _ _)
  have hcoeff : ∀ n : ℕ, p.coeff n = q.coeff n := by
    intro n
    have hp1 := hrf.factorial_smul (1 : ℂ) n
    have hq1 := hrg.factorial_smul (1 : ℂ) n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, one_pow, one_smul] at hp1 hq1
    rw [← iteratedDeriv_eq_iteratedFDeriv] at hp1 hq1
    rw [h n] at hp1
    have hsm : (n.factorial) • p.coeff n = (n.factorial) • q.coeff n := by
      rw [hp1, hq1]
    exact nsmul_right_injective (Nat.factorial_ne_zero n) hsm
  refine Filter.eventuallyEq_of_mem (Metric.eball_mem_nhds x hr) (fun z hz => ?_)
  have hy : z - x ∈ Metric.eball (0 : ℂ) (min rf rg) := by
    have hd : edist (z - x) (0 : ℂ) = edist z x := by
      simp [edist_dist, dist_eq_norm]
    simpa [Metric.mem_eball, hd] using hz
  have h1 := hf'.hasSum hy
  have h2 := hg'.hasSum hy
  have hfun : (fun n => (p n) fun _ => (z - x)) = fun n => (q n) fun _ => (z - x) := by
    funext n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, hcoeff n]
  rw [hfun] at h1
  simpa using h1.unique h2

/-! #### All-prime full-jet faithfulness -/

theorem primeEulerFlux_eventuallyEq_lSeries {a : Nat.Primes → ℂ} (ha : ∀ p, ‖a p‖ ≤ 1)
    {s₀ : ℂ} (hs₀ : 1 < s₀.re) :
    primeEulerFlux a =ᶠ[nhds s₀] LSeries (degreeOneEulerPrimeFluxCoeff a) := by
  refine Filter.eventuallyEq_of_mem
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs₀) (fun s hs => ?_)
  exact (lSeries_degreeOneEulerPrimeFluxCoeff_eq ha hs).symm

theorem analyticOnNhd_lSeries_degreeOneEulerPrimeFluxCoeff {a : Nat.Primes → ℂ}
    (ha : ∀ p, ‖a p‖ ≤ 1) :
    AnalyticOnNhd ℂ (LSeries (degreeOneEulerPrimeFluxCoeff a)) {s : ℂ | 1 < s.re} := by
  intro s hs
  refine LSeries_analyticOnNhd (degreeOneEulerPrimeFluxCoeff a) s ?_
  refine lt_of_le_of_lt (abscissaOfAbsConv_degreeOneEulerPrimeFluxCoeff_le ha) ?_
  exact_mod_cast hs

theorem analyticAt_primeEulerFlux {a : Nat.Primes → ℂ} (ha : ∀ p, ‖a p‖ ≤ 1)
    {s₀ : ℂ} (hs₀ : 1 < s₀.re) : AnalyticAt ℂ (primeEulerFlux a) s₀ :=
  (analyticOnNhd_lSeries_degreeOneEulerPrimeFluxCoeff ha s₀ hs₀).congr
    (primeEulerFlux_eventuallyEq_lSeries ha hs₀).symm

/-- **All-prime full-jet faithfulness.**  On the closed prime polydisc `‖a_p‖ ≤ 1`, the complete
jet of the degree-one Euler logarithmic flux at a single point of the Euler half-plane recovers
every local parameter.  Combined with finite-jet openness this is the card's pro-jet dichotomy:
every finite jet projection contains an open set, yet the full jet is injective. -/
theorem degreeOneEulerParameter_eq_of_iteratedDeriv_eq {a b : Nat.Primes → ℂ}
    (ha : ∀ p, ‖a p‖ ≤ 1) (hb : ∀ p, ‖b p‖ ≤ 1) {s₀ : ℂ} (hs₀ : 1 < s₀.re)
    (h : ∀ j : ℕ, iteratedDeriv j (primeEulerFlux a) s₀ = iteratedDeriv j (primeEulerFlux b) s₀) :
    a = b := by
  have hgerm : primeEulerFlux a =ᶠ[nhds s₀] primeEulerFlux b :=
    eventuallyEq_of_iteratedDeriv_eq (analyticAt_primeEulerFlux ha hs₀)
      (analyticAt_primeEulerFlux hb hs₀) h
  have hL : LSeries (degreeOneEulerPrimeFluxCoeff a) =ᶠ[nhds s₀]
      LSeries (degreeOneEulerPrimeFluxCoeff b) :=
    ((primeEulerFlux_eventuallyEq_lSeries ha hs₀).symm.trans hgerm).trans
      (primeEulerFlux_eventuallyEq_lSeries hb hs₀)
  have heq : Set.EqOn (LSeries (degreeOneEulerPrimeFluxCoeff a))
      (LSeries (degreeOneEulerPrimeFluxCoeff b)) {s : ℂ | 1 < s.re} :=
    (analyticOnNhd_lSeries_degreeOneEulerPrimeFluxCoeff ha).eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_lSeries_degreeOneEulerPrimeFluxCoeff hb)
      ((convex_halfSpace_re_gt 1).isPreconnected) hs₀ hL
  have hreal : (fun x : ℝ => LSeries (degreeOneEulerPrimeFluxCoeff a) x)
      =ᶠ[Filter.atTop] fun x : ℝ => LSeries (degreeOneEulerPrimeFluxCoeff b) x := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact heq (by simpa using hx)
  have hcoeff : degreeOneEulerPrimeFluxCoeff a = degreeOneEulerPrimeFluxCoeff b := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [degreeOneEulerPrimeFluxCoeff, degreeOneEulerPrimeFluxCoeff,
        degreeOneEulerFluxCoeff_eq_zero_of_not_isPrimePow _ not_isPrimePow_zero,
        degreeOneEulerFluxCoeff_eq_zero_of_not_isPrimePow _ not_isPrimePow_zero]
    · exact LSeries.eq_of_LSeries_eventually_eq
        (abscissaOfAbsConv_degreeOneEulerPrimeFluxCoeff_lt_top ha)
        (abscissaOfAbsConv_degreeOneEulerPrimeFluxCoeff_lt_top hb) hreal hn
  exact degreeOneEulerPrimeFluxCoeff_injective hcoeff

end RHTower
