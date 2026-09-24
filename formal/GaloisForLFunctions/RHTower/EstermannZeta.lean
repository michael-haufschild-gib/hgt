import Mathlib.NumberTheory.LSeries.ZMod

/-!
# Estermann's zeta function and its functional equation

For `q ≥ 1` and `a` a residue mod `q`, Estermann's zeta function is

```text
D(s, a/q) = Σ_{N ≥ 1} d(N) e(aN/q) N^{-s}    (Re s > 1),
```

`d` the divisor function.  Grouping `N = mn` and then the factor `m` by its residue class `c`
modulo `q` turns this into a finite combination of Hurwitz and exponential zeta functions,

```text
D(s, a/q) = q^{-s} Σ_{c mod q} E(ac/q, s) · ζ(s, c/q),
```

because `e(amn/q)` depends on `m` only through `c = m mod q`.  The right-hand side is taken as the
definition: it is meromorphic on all of `ℂ`, and by `ZMod.LFunction_eq_LSeries` it agrees with the
Dirichlet series wherever the latter converges.

The Hurwitz and exponential zeta functions are exchanged by the `s ↔ 1 - s` reflection, so the
defining sum is formally self-dual.  Expanding both reflections, the four resulting products regroup
under the two permutations `c ↦ ac` and `c ↦ -ac` of `ZMod q` (available because `a` is a unit) into
just two Estermann values, at `a⁻¹` and at `-a⁻¹`:

```text
D(1-s, a/q) = 2 q^{2s-1} (2π)^{-2s} Γ(s)² ( D(s, a⁻¹/q) + cos(πs) · D(s, -a⁻¹/q) ).
```

The two exponential factors `e^{±iπs}` of the cross terms combine into the single `cos(πs)`.

Separating the residue `c = 0`, where both factors degenerate to `ζ`, and replacing every remaining
Hurwitz zeta by `ζ` plus an entire difference, confines all singular behaviour to one factor:

```text
D(s, a/q) = q^{-s} ( (ζ(s) + G_a(s)) ζ(s) + R_a(s) ),
```

with `G_a` and `R_a` entire whenever `a` is a unit.  So `D(·, a/q)` is holomorphic off `s = 1` and
has a double pole there whose leading Laurent coefficient is `1/q`, independent of `a`.
-/

open Complex HurwitzZeta

namespace RHTower

noncomputable section

/-- Multiplication by a unit is a permutation of `ZMod q`. -/
def unitsMulPerm {q : ℕ} (a : (ZMod q)ˣ) : ZMod q ≃ ZMod q where
  toFun x := (a : ZMod q) * x
  invFun x := ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * x
  left_inv x := by
    show ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * ((a : ZMod q) * x) = x
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  right_inv x := by
    show (a : ZMod q) * (((a⁻¹ : (ZMod q)ˣ) : ZMod q) * x) = x
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

@[simp] theorem unitsMulPerm_apply {q : ℕ} (a : (ZMod q)ˣ) (x : ZMod q) :
    unitsMulPerm a x = (a : ZMod q) * x := rfl

/-- **Estermann's zeta function.** -/
def estermannZeta (q : ℕ) [NeZero q] (a : ZMod q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-s) *
    ∑ c : ZMod q, expZeta (ZMod.toAddCircle (a * c)) s * hurwitzZeta (ZMod.toAddCircle c) s

/-- Inverse of a unit cancels a left multiplication. -/
theorem units_inv_mul_cancel {q : ℕ} (a : (ZMod q)ˣ) (c : ZMod q) :
    ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * ((a : ZMod q) * c) = c := by
  rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- `a` is a unit, so `a * c` vanishes only at `c = 0`. -/
theorem units_mul_ne_zero {q : ℕ} (a : (ZMod q)ˣ) {c : ZMod q} (hc : c ≠ 0) :
    (a : ZMod q) * c ≠ 0 := by
  intro h
  refine hc ?_
  have hcc := units_inv_mul_cancel a c
  rw [h, mul_zero] at hcc
  exact hcc.symm

variable {q : ℕ} [NeZero q]

/-- **Functional equation of Estermann's zeta function.** -/
theorem estermannZeta_one_sub (a : (ZMod q)ˣ) {s : ℂ} (hs : ∀ n : ℕ, s ≠ 1 - (n : ℂ)) :
    estermannZeta q (a : ZMod q) (1 - s)
      = 2 * (q : ℂ) ^ (2 * s - 1) * (2 * (Real.pi : ℂ)) ^ (-(2 * s)) * Complex.Gamma s ^ 2 *
        (estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s
          + Complex.cos ((Real.pi : ℂ) * s) *
            estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hsn : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hcon
    refine hs (n + 1) ?_
    rw [hcon]; push_cast; ring
  have hs1 : s ≠ 1 := by
    intro h
    exact hs 0 (by rw [h]; norm_num)
  have e1 : Complex.exp ((Real.pi : ℂ) * I * s / 2) * Complex.exp (-(Real.pi : ℂ) * I * s / 2)
      = 1 := by
    rw [← Complex.exp_add, show (Real.pi : ℂ) * I * s / 2 + -(Real.pi : ℂ) * I * s / 2 = 0 by ring,
      Complex.exp_zero]
  have e2 : Complex.exp ((Real.pi : ℂ) * I * s / 2) * Complex.exp ((Real.pi : ℂ) * I * s / 2)
      = Complex.exp ((Real.pi : ℂ) * I * s) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e3 : Complex.exp (-(Real.pi : ℂ) * I * s / 2) * Complex.exp (-(Real.pi : ℂ) * I * s / 2)
      = Complex.exp (-((Real.pi : ℂ) * I * s)) := by
    rw [← Complex.exp_add]; congr 1; ring
  -- pointwise expansion of the reflected summand
  have hexp : ∀ c : ZMod q,
      expZeta (ZMod.toAddCircle ((a : ZMod q) * c)) (1 - s) *
          hurwitzZeta (ZMod.toAddCircle c) (1 - s)
        = ((2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s) ^ 2 *
          ( hurwitzZeta (ZMod.toAddCircle ((a : ZMod q) * c)) s * expZeta (ZMod.toAddCircle c) s
            + Complex.exp ((Real.pi : ℂ) * I * s) *
                (hurwitzZeta (ZMod.toAddCircle ((a : ZMod q) * c)) s *
                  expZeta (-(ZMod.toAddCircle c)) s)
            + Complex.exp (-((Real.pi : ℂ) * I * s)) *
                (hurwitzZeta (-(ZMod.toAddCircle ((a : ZMod q) * c))) s *
                  expZeta (ZMod.toAddCircle c) s)
            + hurwitzZeta (-(ZMod.toAddCircle ((a : ZMod q) * c))) s *
                expZeta (-(ZMod.toAddCircle c)) s ) := by
    intro c
    rw [expZeta_one_sub _ hs, hurwitzZeta_one_sub _ hsn (Or.inr hs1)]
    set K0 : ℂ := (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s with hK0
    set X := hurwitzZeta (ZMod.toAddCircle ((a : ZMod q) * c)) s with hX
    set Y := hurwitzZeta (-(ZMod.toAddCircle ((a : ZMod q) * c))) s with hY
    set Z := expZeta (ZMod.toAddCircle c) s with hZ
    set W := expZeta (-(ZMod.toAddCircle c)) s with hW
    linear_combination (K0 ^ 2 * X * Z + K0 ^ 2 * Y * W) * e1 + (K0 ^ 2 * X * W) * e2 +
      (K0 ^ 2 * Y * Z) * e3
  -- the four reindexed sums
  have hS1 : (∑ c : ZMod q, hurwitzZeta (ZMod.toAddCircle ((a : ZMod q) * c)) s *
        expZeta (ZMod.toAddCircle c) s)
      = ∑ c : ZMod q, expZeta (ZMod.toAddCircle (((a⁻¹ : (ZMod q)ˣ) : ZMod q) * c)) s *
          hurwitzZeta (ZMod.toAddCircle c) s := by
    refine Fintype.sum_equiv (unitsMulPerm a) _ _ (fun c => ?_)
    rw [unitsMulPerm_apply, units_inv_mul_cancel]
    ring
  have hS2 : (∑ c : ZMod q, hurwitzZeta (ZMod.toAddCircle ((a : ZMod q) * c)) s *
        expZeta (-(ZMod.toAddCircle c)) s)
      = ∑ c : ZMod q, expZeta (ZMod.toAddCircle ((-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) * c)) s *
          hurwitzZeta (ZMod.toAddCircle c) s := by
    refine Fintype.sum_equiv (unitsMulPerm a) _ _ (fun c => ?_)
    rw [unitsMulPerm_apply, neg_mul, units_inv_mul_cancel, map_neg]
    ring
  have hS3 : (∑ c : ZMod q, hurwitzZeta (-(ZMod.toAddCircle ((a : ZMod q) * c))) s *
        expZeta (ZMod.toAddCircle c) s)
      = ∑ c : ZMod q, expZeta (ZMod.toAddCircle ((-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) * c)) s *
          hurwitzZeta (ZMod.toAddCircle c) s := by
    refine Fintype.sum_equiv ((unitsMulPerm a).trans (Equiv.neg (ZMod q))) _ _ (fun c => ?_)
    simp only [Equiv.trans_apply, unitsMulPerm_apply, Equiv.neg_apply]
    rw [neg_mul_neg, units_inv_mul_cancel, map_neg]
    ring
  have hS4 : (∑ c : ZMod q, hurwitzZeta (-(ZMod.toAddCircle ((a : ZMod q) * c))) s *
        expZeta (-(ZMod.toAddCircle c)) s)
      = ∑ c : ZMod q, expZeta (ZMod.toAddCircle (((a⁻¹ : (ZMod q)ˣ) : ZMod q) * c)) s *
          hurwitzZeta (ZMod.toAddCircle c) s := by
    refine Fintype.sum_equiv ((unitsMulPerm a).trans (Equiv.neg (ZMod q))) _ _ (fun c => ?_)
    simp only [Equiv.trans_apply, unitsMulPerm_apply, Equiv.neg_apply]
    rw [mul_neg, units_inv_mul_cancel, map_neg, map_neg]
    ring
  -- power and cosine identities
  have hpine : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨two_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero⟩
  have hqp : (q : ℂ) ^ (-(1 - s)) = (q : ℂ) ^ (2 * s - 1) * (q : ℂ) ^ (-s) := by
    rw [← Complex.cpow_add _ _ hq0]; congr 1; ring
  have hpip : ((2 * (Real.pi : ℂ)) ^ (-s)) ^ (2 : ℕ) = (2 * (Real.pi : ℂ)) ^ (-(2 * s)) := by
    rw [sq, ← Complex.cpow_add _ _ hpine]; congr 1; ring
  have hcos : Complex.exp ((Real.pi : ℂ) * I * s) + Complex.exp (-((Real.pi : ℂ) * I * s))
      = 2 * Complex.cos ((Real.pi : ℂ) * s) := by
    rw [Complex.cos, show ((Real.pi : ℂ) * s) * I = (Real.pi : ℂ) * I * s by ring,
      show -((Real.pi : ℂ) * s) * I = -((Real.pi : ℂ) * I * s) by ring]
    ring
  -- assembly
  unfold estermannZeta
  rw [Finset.sum_congr rfl (fun c _ => hexp c), ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hS1, hS2, hS3, hS4, hqp, mul_pow, hpip]
  set A : ℂ := ∑ c : ZMod q, expZeta (ZMod.toAddCircle (((a⁻¹ : (ZMod q)ˣ) : ZMod q) * c)) s *
    hurwitzZeta (ZMod.toAddCircle c) s with hA
  set B : ℂ := ∑ c : ZMod q, expZeta (ZMod.toAddCircle ((-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) * c)) s *
    hurwitzZeta (ZMod.toAddCircle c) s with hB
  linear_combination ((q : ℂ) ^ (2 * s - 1) * (q : ℂ) ^ (-s) * (2 * (Real.pi : ℂ)) ^ (-(2 * s)) *
    Complex.Gamma s ^ 2 * B) * hcos

/-- Estermann's zeta function is the `ZMod q` L-function of the exponential-zeta weights. -/
theorem estermannZeta_eq_LFunction (a : ZMod q) (s : ℂ) :
    estermannZeta q a s
      = ZMod.LFunction (fun c => expZeta (ZMod.toAddCircle (a * c)) s) s := rfl

/-- **The Dirichlet series of Estermann's zeta function.**  For `1 < Re s` it is the L-series whose
`m`-th coefficient is `expZeta (a m / q) s = Σ_n e(amn/q) n^{-s}`; expanding the inner series and
grouping by the product `mn` gives `Σ_N d(N) e(aN/q) N^{-s}`. -/
theorem estermannZeta_eq_LSeries (a : ZMod q) {s : ℂ} (hs : 1 < s.re) :
    estermannZeta q a s
      = LSeries (fun m : ℕ => expZeta (ZMod.toAddCircle (a * (m : ZMod q))) s) s := by
  rw [estermannZeta_eq_LFunction, ZMod.LFunction_eq_LSeries _ hs]

/-- A convergent L-series as a sum over positive indices. -/
theorem hasSum_lseries_succ {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    HasSum (fun n : ℕ => f (n + 1) / (((n + 1 : ℕ) : ℂ)) ^ s) (LSeries f s) := by
  have hi : Function.Injective (fun n : ℕ => n + 1) := fun m n hmn => by simpa using hmn
  have hz : ∀ x ∉ Set.range (fun n : ℕ => n + 1), LSeries.term f s x = 0 := by
    intro x hx
    have hx0 : x = 0 := by
      by_contra hne
      refine hx ⟨x - 1, ?_⟩
      show x - 1 + 1 = x
      omega
    rw [hx0, LSeries.term_zero]
  have hbase : HasSum (LSeries.term f s) (LSeries f s) := h.hasSum
  have hcomp := (Function.Injective.hasSum_iff (f := LSeries.term f s) hi hz).mpr hbase
  have heq : (LSeries.term f s ∘ fun n : ℕ => n + 1)
      = fun n : ℕ => f (n + 1) / (((n + 1 : ℕ) : ℂ)) ^ s := by
    funext n
    simp only [Function.comp_apply]
    exact LSeries.term_of_ne_zero (Nat.succ_ne_zero n) f s
  rwa [heq] at hcomp

/-- **The Estermann double series.**  For `1 < Re s` the value `estermannZeta q a s` is the sum of
`e(a m n / q) (mn)^{-s}` over all pairs of positive integers `(m, n)`; grouping by the product `mn`
turns this into `Σ_N d(N) e(aN/q) N^{-s}`. -/
theorem hasSum_estermannZeta (a : ZMod q) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : ℕ × ℕ =>
        (ZMod.stdAddChar (a * ((p.1 + 1 : ℕ) : ZMod q) * ((p.2 + 1 : ℕ) : ZMod q)) : ℂ) /
          ((((p.1 + 1 : ℕ) : ℂ)) ^ s * (((p.2 + 1 : ℕ) : ℂ)) ^ s))
      (estermannZeta q a s) := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  -- the sum over the first index
  have houter : HasSum
      (fun m : ℕ => expZeta (ZMod.toAddCircle (a * ((m + 1 : ℕ) : ZMod q))) s /
        (((m + 1 : ℕ) : ℂ)) ^ s) (estermannZeta q a s) := by
    rw [estermannZeta_eq_LSeries a hs]
    exact hasSum_lseries_succ (f := fun m : ℕ => expZeta (ZMod.toAddCircle (a * (m : ZMod q))) s)
      (ZMod.LSeriesSummable_of_one_lt_re (fun c => expZeta (ZMod.toAddCircle (a * c)) s) hs)
  -- the sum over the second index, for each value of the first
  have hrow : ∀ m : ℕ, HasSum
      (fun n : ℕ =>
        (ZMod.stdAddChar (a * ((m + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ZMod q)) : ℂ) /
          ((((m + 1 : ℕ) : ℂ)) ^ s * (((n + 1 : ℕ) : ℂ)) ^ s))
      (expZeta (ZMod.toAddCircle (a * ((m + 1 : ℕ) : ZMod q))) s /
        (((m + 1 : ℕ) : ℂ)) ^ s) := by
    intro m
    set j : ZMod q := a * ((m + 1 : ℕ) : ZMod q) with hj
    have hE : expZeta (ZMod.toAddCircle j) s
        = LSeries (fun n : ℕ => (ZMod.stdAddChar (j * (n : ZMod q)) : ℂ)) s := by
      rw [← ZMod.LFunction_stdAddChar_eq_expZeta j s (Or.inr hs1), ZMod.LFunction_eq_LSeries _ hs]
    rw [hE]
    have hsum := hasSum_lseries_succ (f := fun n : ℕ => (ZMod.stdAddChar (j * (n : ZMod q)) : ℂ))
      (ZMod.LSeriesSummable_of_one_lt_re (fun c => (ZMod.stdAddChar (j * c) : ℂ)) hs)
    have hdiv := hsum.div_const ((((m + 1 : ℕ) : ℂ)) ^ s)
    have heq : (fun n : ℕ => (ZMod.stdAddChar (j * ((n + 1 : ℕ) : ZMod q)) : ℂ) /
          (((n + 1 : ℕ) : ℂ)) ^ s / (((m + 1 : ℕ) : ℂ)) ^ s)
        = fun n : ℕ => (ZMod.stdAddChar (j * ((n + 1 : ℕ) : ZMod q)) : ℂ) /
          ((((m + 1 : ℕ) : ℂ)) ^ s * (((n + 1 : ℕ) : ℂ)) ^ s) := by
      funext n
      rw [div_div]
      ring
    rw [heq] at hdiv
    exact hdiv
  -- absolute convergence of the double family
  have hg : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ s.re) :=
    (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_rpow (p := s.re)).mpr hs)
  have hprod : Summable (fun p : ℕ × ℕ =>
      (1 / (((p.1 + 1 : ℕ) : ℝ)) ^ s.re) * (1 / (((p.2 + 1 : ℕ) : ℝ)) ^ s.re)) :=
    hg.mul_of_nonneg hg (fun n => by positivity) (fun n => by positivity)
  have hnorm : ∀ p : ℕ × ℕ,
      ‖(ZMod.stdAddChar (a * ((p.1 + 1 : ℕ) : ZMod q) * ((p.2 + 1 : ℕ) : ZMod q)) : ℂ) /
          ((((p.1 + 1 : ℕ) : ℂ)) ^ s * (((p.2 + 1 : ℕ) : ℂ)) ^ s)‖
        = (1 / (((p.1 + 1 : ℕ) : ℝ)) ^ s.re) * (1 / (((p.2 + 1 : ℕ) : ℝ)) ^ s.re) := by
    intro p
    rw [norm_div, ZMod.stdAddChar_apply, Circle.norm_coe, norm_mul,
      norm_natCast_cpow_of_pos (Nat.succ_pos _), norm_natCast_cpow_of_pos (Nat.succ_pos _)]
    simp only [one_div, mul_inv]
  have hsummable : Summable (fun p : ℕ × ℕ =>
      (ZMod.stdAddChar (a * ((p.1 + 1 : ℕ) : ZMod q) * ((p.2 + 1 : ℕ) : ZMod q)) : ℂ) /
        ((((p.1 + 1 : ℕ) : ℂ)) ^ s * (((p.2 + 1 : ℕ) : ℂ)) ^ s)) := by
    refine Summable.of_norm ?_
    simpa only [hnorm] using hprod
  have hfib := hsummable.hasSum.prod_fiberwise hrow
  have heq := hfib.unique houter
  rw [← heq]
  exact hsummable.hasSum

/-! ### The polar structure at `s = 1` -/

/-- The character sum over nonzero residues, `Σ_{c ≠ 0} E(ac/q, s)`. -/
def estermannCharSum (q : ℕ) [NeZero q] (a : ZMod q) (s : ℂ) : ℂ :=
  ∑ c ∈ Finset.univ.erase (0 : ZMod q), expZeta (ZMod.toAddCircle (a * c)) s

/-- The regular part of Estermann's zeta function, `Σ_{c ≠ 0} E(ac/q, s)(ζ(s, c/q) - ζ(s))`. -/
def estermannRegularPart (q : ℕ) [NeZero q] (a : ZMod q) (s : ℂ) : ℂ :=
  ∑ c ∈ Finset.univ.erase (0 : ZMod q),
    expZeta (ZMod.toAddCircle (a * c)) s * (hurwitzZeta (ZMod.toAddCircle c) s - riemannZeta s)

/-- **The polar decomposition.**  Separating the residue `c = 0`, where both factors degenerate to
`ζ`, and replacing every remaining Hurwitz zeta by `ζ` plus an entire difference, isolates all of
the singular behaviour of `D(s, a/q)` in the factor `(ζ(s) + G_a(s)) ζ(s)`. -/
theorem estermannZeta_eq_polar_add_regular (a : ZMod q) (s : ℂ) :
    estermannZeta q a s
      = (q : ℂ) ^ (-s) *
          ((riemannZeta s + estermannCharSum q a s) * riemannZeta s
            + estermannRegularPart q a s) := by
  classical
  unfold estermannZeta estermannCharSum estermannRegularPart
  congr 1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))]
  rw [mul_zero, map_zero, expZeta_zero, hurwitzZeta_zero]
  have hsplit : (∑ c ∈ Finset.univ.erase (0 : ZMod q),
        expZeta (ZMod.toAddCircle (a * c)) s * (hurwitzZeta (ZMod.toAddCircle c) s - riemannZeta s))
      = (∑ c ∈ Finset.univ.erase (0 : ZMod q),
          expZeta (ZMod.toAddCircle (a * c)) s * hurwitzZeta (ZMod.toAddCircle c) s)
        - (∑ c ∈ Finset.univ.erase (0 : ZMod q),
          expZeta (ZMod.toAddCircle (a * c)) s) * riemannZeta s := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit]
  ring

/-- The nonzero-residue character sum is entire. -/
theorem differentiable_estermannCharSum (a : (ZMod q)ˣ) :
    Differentiable ℂ (estermannCharSum q (a : ZMod q)) := by
  classical
  unfold estermannCharSum
  apply Differentiable.fun_sum
  intro c hc
  refine differentiable_expZeta_of_ne_zero ?_
  rw [ne_eq, ZMod.toAddCircle_eq_zero]
  exact units_mul_ne_zero a (Finset.ne_of_mem_erase hc)

/-- The regular part is entire. -/
theorem differentiable_estermannRegularPart (a : (ZMod q)ˣ) :
    Differentiable ℂ (estermannRegularPart q (a : ZMod q)) := by
  classical
  unfold estermannRegularPart
  apply Differentiable.fun_sum
  intro c hc
  refine Differentiable.mul (differentiable_expZeta_of_ne_zero ?_) ?_
  · rw [ne_eq, ZMod.toAddCircle_eq_zero]
    exact units_mul_ne_zero a (Finset.ne_of_mem_erase hc)
  · have h := differentiable_hurwitzZeta_sub_hurwitzZeta (ZMod.toAddCircle c) 0
    simpa [hurwitzZeta_zero] using h

/-- A constant raised to the negated variable is entire. -/
theorem differentiable_const_cpow_neg {x : ℂ} (hx : x ≠ 0) :
    Differentiable ℂ (fun s : ℂ => x ^ (-s)) := by
  have heq : (fun s : ℂ => x ^ (-s)) = fun s : ℂ => Complex.exp (Complex.log x * (-s)) := by
    funext s
    rw [Complex.cpow_def_of_ne_zero hx]
  rw [heq]
  exact Differentiable.cexp ((differentiable_const _).mul differentiable_id.neg)

/-- **Estermann's zeta function is holomorphic off `s = 1`.** -/
theorem differentiableAt_estermannZeta (a : (ZMod q)ˣ) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (estermannZeta q (a : ZMod q)) s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have heq : estermannZeta q (a : ZMod q) = fun z : ℂ => (q : ℂ) ^ (-z) *
      ((riemannZeta z + estermannCharSum q (a : ZMod q) z) * riemannZeta z
        + estermannRegularPart q (a : ZMod q) z) := by
    funext z
    exact estermannZeta_eq_polar_add_regular _ z
  rw [heq]
  have hz : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs
  exact ((differentiable_const_cpow_neg hq0) s).mul
    (((hz.add ((differentiable_estermannCharSum a) s)).mul hz).add
      ((differentiable_estermannRegularPart a) s))

/-- **The leading Laurent coefficient at the double pole.**  It is `1/q`, independent of `a`. -/
theorem tendsto_sq_sub_one_mul_estermannZeta (a : (ZMod q)ˣ) :
    Filter.Tendsto (fun s : ℂ => (s - 1) ^ 2 * estermannZeta q (a : ZMod q) s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds ((q : ℂ)⁻¹)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hres : Filter.Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 1) := riemannZeta_residue_one
  have hsub : Filter.Tendsto (fun s : ℂ => s - 1) (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 0) := by
    have h : Filter.Tendsto (fun s : ℂ => s - 1) (nhds (1 : ℂ)) (nhds ((1 : ℂ) - 1)) :=
      ((continuous_id (X := ℂ)).sub (continuous_const (y := (1 : ℂ)))).tendsto (1 : ℂ)
    simpa using h.mono_left nhdsWithin_le_nhds
  have hpow : Filter.Tendsto (fun s : ℂ => (q : ℂ) ^ (-s))
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds ((q : ℂ) ^ (-(1 : ℂ)))) :=
    ((differentiable_const_cpow_neg hq0) 1).continuousAt.continuousWithinAt.tendsto
  have hG : Filter.Tendsto (fun s : ℂ => estermannCharSum q (a : ZMod q) s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (estermannCharSum q (a : ZMod q) 1)) :=
    ((differentiable_estermannCharSum a) 1).continuousAt.continuousWithinAt.tendsto
  have hR : Filter.Tendsto (fun s : ℂ => estermannRegularPart q (a : ZMod q) s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (estermannRegularPart q (a : ZMod q) 1)) :=
    ((differentiable_estermannRegularPart a) 1).continuousAt.continuousWithinAt.tendsto
  have hcomb : Filter.Tendsto
      (fun s : ℂ => (q : ℂ) ^ (-s) *
        (((s - 1) * riemannZeta s) * ((s - 1) * riemannZeta s)
          + ((s - 1) * estermannCharSum q (a : ZMod q) s) * ((s - 1) * riemannZeta s)
          + (s - 1) ^ 2 * estermannRegularPart q (a : ZMod q) s))
      (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhds ((q : ℂ) ^ (-(1 : ℂ)) * (1 * 1
        + (0 * estermannCharSum q (a : ZMod q) 1) * 1
        + 0 ^ 2 * estermannRegularPart q (a : ZMod q) 1))) :=
    hpow.mul (((hres.mul hres).add ((hsub.mul hG).mul hres)).add ((hsub.pow 2).mul hR))
  have hval : (q : ℂ) ^ (-(1 : ℂ)) * (1 * 1
      + (0 * estermannCharSum q (a : ZMod q) 1) * 1
      + 0 ^ 2 * estermannRegularPart q (a : ZMod q) 1) = (q : ℂ)⁻¹ := by
    rw [Complex.cpow_neg, Complex.cpow_one]
    ring
  rw [hval] at hcomb
  refine hcomb.congr fun s => ?_
  rw [estermannZeta_eq_polar_add_regular]
  ring

end

end RHTower
