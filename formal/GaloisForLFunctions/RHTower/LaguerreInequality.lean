/-
The first Laguerre inequality and its use as a one-sided off-line-zero detector for ξ.

The first Laguerre inequality is the pointwise constraint
`(f')² ≥ f · f''` satisfied by every function with only real zeros (the Laguerre–Pólya
class).  It is a *sign* obstruction: at any point where a function locally curves the
"wrong" way relative to its slope — where `(f')² < f · f''` — the function cannot have all
its zeros real.  This module builds the inequality from the polynomial level up and turns it
into a detector for the completed Riemann ξ on the critical line.

* **§1 (unconditional).**  For a real polynomial `p` all of whose roots are real, the
  L₁ polynomial `L₁[p] := (p')² − p·p''` is pointwise nonnegative.  The proof is the linear
  peel identity
  `L₁[(X − r)·q] = q² + (X − r)²·L₁[q]`,
  which exhibits `L₁` of a one-larger factorization as a sum of two squares times the
  smaller `L₁`; nonnegativity then follows by induction over the multiset of real roots,
  the base case `L₁[const] = 0`.  No analytic input, no limiting argument.

* **§2 (limit passage).**  `LaguerrePolya f` says `f` and its first two derivatives are
  pointwise limits of a sequence of real-split polynomials.  The inequality `(f')² ≥ f·f''`
  passes to the limit at each point, since `≤` is closed and multiplication and squaring are
  continuous — nothing but §1 and order-closedness of the reals.

* **§3 (the ξ detector).**  On the critical line `ξ(½ + it)` is real: Schwarz reflection
  `ξ(s̄) = ξ(s)‾` and the functional equation `ξ(1−s) = ξ(s)` together force
  `ξ(½ + it)‾ = ξ(½ − it) = ξ(½ + it)`.  Writing `Ξ(t) := Re ξ(½ + it)`, Pólya's theorem is
  the single isolated interface `RiemannHypothesis → LaguerrePolya Ξ` (the hard analytic
  direction, taken as a hypothesis).  Contraposing §2 through it gives the detector: a single
  real `t` with a *strict* margin deficit `(Ξ'(t))² < Ξ(t)·Ξ''(t)` refutes the Riemann
  hypothesis.
-/
import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.Reflection

namespace RHTower

open Polynomial Filter Topology

/-! ### §1 The polynomial engine: real-split ⟹ `L₁ ≥ 0` (unconditional) -/

/-- The first Laguerre form of a polynomial: `L₁[p] = (p')² − p·p''`.  Its evaluation at `x`
is `(p'(x))² − p(x)·p''(x)`, the quantity the first Laguerre inequality bounds below by `0`. -/
noncomputable def laguerreL1 (p : Polynomial ℝ) : Polynomial ℝ :=
  (derivative p) ^ (2 : ℕ) - p * derivative (derivative p)

/-- **Linear peel identity.**  Attaching one monic linear factor turns `L₁` into a sum of
two squares plus the previous `L₁`:
`L₁[(X − r)·q] = q² + (X − r)²·L₁[q]`.
Mechanism: `((X − r)q)' = q + (X − r)q'` and `((X − r)q)'' = 2q' + (X − r)q''`; substituting
and expanding, the cross term `2(X − r)qq'` cancels, leaving `q²` and `(X − r)²(q'² − qq'')`. -/
lemma laguerreL1_linear_mul (r : ℝ) (q : Polynomial ℝ) :
    laguerreL1 ((X - C r) * q) = q ^ (2 : ℕ) + (X - C r) ^ (2 : ℕ) * laguerreL1 q := by
  have hu : derivative (X - C r) = 1 := by
    simp [derivative_sub, derivative_X, derivative_C]
  have e1 : derivative ((X - C r) * q) = q + (X - C r) * derivative q := by
    rw [derivative_mul, hu]; ring
  have e2 : derivative (derivative ((X - C r) * q))
      = 2 * derivative q + (X - C r) * derivative (derivative q) := by
    rw [e1, derivative_add, derivative_mul, hu]; ring
  unfold laguerreL1
  rw [e2, e1]
  ring

/-- **Constant-multiple scaling.**  `L₁` is quadratically homogeneous: `L₁[c·q] = c²·L₁[q]`,
since `(c·q)' = c·q'` and `(c·q)'' = c·q''`. -/
lemma laguerreL1_C_mul (c : ℝ) (q : Polynomial ℝ) :
    laguerreL1 (C c * q) = (C c) ^ (2 : ℕ) * laguerreL1 q := by
  have hd1 : derivative (C c * q) = C c * derivative q := by
    rw [derivative_mul, derivative_C]; ring
  have hd2 : derivative (derivative (C c * q)) = C c * derivative (derivative q) := by
    rw [hd1, derivative_mul, derivative_C]; ring
  unfold laguerreL1
  rw [hd2, hd1]; ring

/-- `L₁` of a product of monic linear factors evaluates nonnegatively.  Induction over the
multiset of factors: empty product gives `L₁[1] = 0`; the peel identity adds `q(x)² ≥ 0` and
`(x − a)²·L₁[q](x) ≥ 0` at each step. -/
lemma laguerreL1_prod_eval_nonneg (s : Multiset ℝ) (x : ℝ) :
    0 ≤ (laguerreL1 (Multiset.map (fun a => X - C a) s).prod).eval x := by
  induction s using Multiset.induction with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    unfold laguerreL1
    simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, laguerreL1_linear_mul,
        eval_add, eval_mul, eval_pow, eval_pow]
    exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) ih)

/-- **The L₁ polynomial of a real-split polynomial is pointwise nonnegative.**  Over `ℝ`,
`p.Splits` means `p` factors as a constant times monic linear factors; `L₁` scales by the
squared constant and is nonnegative on the linear-factor product. -/
theorem laguerreL1_eval_nonneg {p : Polynomial ℝ} (hsp : p.Splits) (x : ℝ) :
    0 ≤ (laguerreL1 p).eval x := by
  have hfact : p = C p.leadingCoeff * (Multiset.map (fun a => X - C a) p.roots).prod :=
    hsp.eq_prod_roots
  rw [hfact, laguerreL1_C_mul, eval_mul, eval_pow, eval_C]
  exact mul_nonneg (sq_nonneg _) (laguerreL1_prod_eval_nonneg _ _)

/-- **First Laguerre inequality (polynomial form).**  For a real polynomial all of whose
roots are real, `p(x)·p''(x) ≤ (p'(x))²` at every real `x`.  Immediate from
`laguerreL1_eval_nonneg` by expanding `L₁ = (p')² − p·p''`. -/
theorem laguerre_inequality_poly {p : Polynomial ℝ} (hsp : p.Splits) (x : ℝ) :
    p.eval x * (derivative (derivative p)).eval x ≤ ((derivative p).eval x) ^ (2 : ℕ) := by
  have h := laguerreL1_eval_nonneg hsp x
  unfold laguerreL1 at h
  rw [eval_sub, eval_pow, eval_mul] at h
  linarith

/-! ### §2 Laguerre–Pólya passage to the limit -/

/-- `f` lies in the (pointwise) Laguerre–Pólya class: there is a sequence of real polynomials,
each with only real roots (`Splits` over `ℝ`), such that the polynomials, their first
derivatives, and their second derivatives converge pointwise to `f`, `deriv f`, and
`deriv (deriv f)` respectively.  This is the exact hypothesis under which the first Laguerre
inequality survives the passage from polynomials to `f`. -/
def LaguerrePolya (f : ℝ → ℝ) : Prop :=
  ∃ p : ℕ → Polynomial ℝ,
    (∀ n, (p n).Splits) ∧
    (∀ x, Tendsto (fun n => (p n).eval x) atTop (𝓝 (f x))) ∧
    (∀ x, Tendsto (fun n => (derivative (p n)).eval x) atTop (𝓝 (deriv f x))) ∧
    (∀ x, Tendsto (fun n => (derivative (derivative (p n))).eval x) atTop
      (𝓝 (deriv (deriv f) x)))

/-- **First Laguerre inequality for the Laguerre–Pólya class.**  If `f` is a pointwise limit
of real-split polynomials together with its first two derivatives, then `(f'(x))² ≥ f(x)·f''(x)`
at every `x`.  Proof: the polynomial inequality `pₙ·pₙ'' ≤ (pₙ')²` holds for every `n`
(§1); its two sides converge to `f·f''` and `(f')²`, and `≤` is closed. -/
theorem laguerre_inequality_lp {f : ℝ → ℝ} (hf : LaguerrePolya f) :
    ∀ x, (deriv f x) ^ (2 : ℕ) ≥ f x * deriv (deriv f) x := by
  obtain ⟨p, hsplit, h0, h1, h2⟩ := hf
  intro x
  have hprod : Tendsto (fun n => (p n).eval x * (derivative (derivative (p n))).eval x)
      atTop (𝓝 (f x * deriv (deriv f) x)) := (h0 x).mul (h2 x)
  have hsq : Tendsto (fun n => ((derivative (p n)).eval x) ^ (2 : ℕ)) atTop
      (𝓝 ((deriv f x) ^ (2 : ℕ))) := (h1 x).pow 2
  exact le_of_tendsto_of_tendsto' hprod hsq (fun n => laguerre_inequality_poly (hsplit n) x)

/-! ### §3 The Ξ detector on the completed Riemann ξ -/

/-- The completed Riemann ξ restricted to the critical line, as a real function:
`Ξ(t) := Re ξ(½ + it)`.  On the line `ξ` is real (`xiHalfLine_real`), so no information is
lost in taking the real part. -/
noncomputable def Xi (t : ℝ) : ℝ := (xi (1/2 + (t : ℂ) * Complex.I)).re

/-- **ξ is real on the critical line.**  `ξ(½ + it) = Ξ(t)` as a complex number.  Schwarz
reflection gives `ξ(½ + it)‾ = ξ(½ − it)`, and the functional equation gives
`ξ(½ − it) = ξ(1 − (½ + it)) = ξ(½ + it)`; hence `ξ(½ + it)` equals its own conjugate and is
therefore real. -/
theorem xiHalfLine_real (t : ℝ) :
    xi (1/2 + (t : ℂ) * Complex.I) = (Xi t : ℂ) := by
  set s : ℂ := 1/2 + (t : ℂ) * Complex.I with hs
  have hconj : (starRingEnd ℂ) s = 1 - s := by
    rw [hs, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀, map_one,
      map_ofNat]
    ring
  have h1 : xi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (xi s) := xi_conj s
  rw [hconj, xi_one_sub] at h1
  have h2 : (starRingEnd ℂ) (xi s) = xi s := h1.symm
  rw [Complex.conj_eq_iff_re] at h2
  rw [← h2]
  rfl

/-- **The Ξ detector.**  Given Pólya's theorem as the isolated interface
`hPolya : RiemannHypothesis → LaguerrePolya Ξ` (ξ lies in the Laguerre–Pólya class iff the
Riemann hypothesis holds — the hard analytic direction taken as hypothesis), a single real `t`
at which the first Laguerre inequality *strictly fails* — `(Ξ'(t))² < Ξ(t)·Ξ''(t)` — refutes the
Riemann hypothesis.  Contrapositive of `laguerre_inequality_lp` composed with `hPolya`. -/
theorem laguerre_margin_neg_not_RH_of_polya
    (hPolya : RiemannHypothesis → LaguerrePolya Xi)
    (h : ∃ t : ℝ, (deriv Xi t) ^ (2 : ℕ) < Xi t * deriv (deriv Xi) t) :
    ¬ RiemannHypothesis := by
  intro hRH
  obtain ⟨t, ht⟩ := h
  have hlp := laguerre_inequality_lp (hPolya hRH) t
  linarith

end RHTower
