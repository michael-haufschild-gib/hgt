# Hurwitz Quadratic N=2 Density Shadow

- **ID:** hurwitz-quadratic-n2-density-shadow
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/hurwitz-in-a-weld-escape-ht.md
- **Statement:** For `Re(s)>1` and `s notin Z`, the functions `zeta(s,a)`, `zeta(s+1,a)`, and `zeta(s+2,a)` satisfy no nonzero `C(a)`-polynomial relation of total degree at most two.

## Goal

This is the first nonlinear density shadow in the Hurwitz weld model. It strengthens the simple Turan/log-convex check: the collision `Y_0Y_2-Y_1^2` cannot be repaired by rational coefficients or lower-degree terms.

The result is not full hypertranscendence. Higher-degree relations and the full `N=2` Zariski-density gate remain open in the parent card.

## Gates

- [x] 0 -> 1 in-progress: exact obstruction named inside the Hurwitz weld/escape card
- [x] 1 -> 2 fully-proven: complete paper proof below, no computation dependency
- [x] 2 -> 3 formalized: `FullyProvenNewTargets.hurwitz_quadratic_n2_density_shadow`, axiom-clean
- [ ] 3 -> 4 publication-ready: not extracted into standalone paper form

## Theorem

Fix `Re(s)>1` with `s notin Z`, and set

`F_k(a)=zeta(s+k,a)`, for `k=0,1,2`.

There is no nonzero polynomial `P in C(a)[Y_0,Y_1,Y_2]` of total `Y`-degree at most two such that

`P(a,F_0(a),F_1(a),F_2(a))=0`.

Via `partial_a^k zeta(s,a)=(-1)^k(s)_k zeta(s+k,a)`, this excludes all order-two algebraic ODEs for `zeta(s,a)` whose polynomial degree in `(y,y',y'')` is at most two.

## Proof

Clear denominators in the rational coefficients. It is enough to work near `a=-n` for all sufficiently large `n`, avoiding the finite set of coefficient poles and zeros specified below. Put `x=a+n`. On a fixed local branch,

`F_k(-n+x)=x^{-s-k}+R_{n,k}(x)`,

where `R_{n,k}` is holomorphic at `x=0` after the local singular term is removed.

Let a degree-at-most-two relation be written as

`Q_2(a;F_0,F_1,F_2)+Q_1(a;F_0,F_1,F_2)+Q_0(a)=0`.

The quadratic monomial `F_iF_j` has leading exponent `-2s-(i+j)`. Since `s` is nonintegral, these quadratic exponents do not collide with the linear or constant exponents. For quadratic weights `w=i+j`, the weights `0,1,3,4` have a unique monomial, so the corresponding coefficients vanish at infinitely many `a=-n` and hence vanish as rational functions.

At weight `w=2`, the only leading collision is `F_0F_2` with `F_1^2`. The leading condition gives `q_{02}+q_{11}=0` as a rational function. Therefore any surviving quadratic part has the form

`q(a)(F_0F_2-F_1^2)`.

A remaining relation would be

`q(a)(F_0F_2-F_1^2)+l_0(a)F_0+l_1(a)F_1+l_2(a)F_2+c(a)=0`.

The leading rational-normal term cancels in the bracket:

`x^{-s}x^{-s-2}-x^{-s-1}x^{-s-1}=0`.

The next most singular term is

`F_0F_2-F_1^2 = x^{-s-2}R_{n,0}(0)+O(x^{-s-1})`.

Thus the coefficient of `x^{-s-2}` in the remaining relation is

`q(-n)R_{n,0}(0)+l_2(-n)=0`

for all sufficiently large `n`.

If `q` were nonzero, then outside the finite zero set of `q(-n)` the values `R_{n,0}(0)` would agree with the rational function `-l_2(-n)/q(-n)`. But the regular part has the exact form

`R_{n,0}(0)=zeta(s)+eta H_n^{(s)}`,

where `eta=exp(epsilon pi i s)` for the fixed branch and `epsilon in {+1,-1}`. Hence

`R_{n,0}(0)-R_{n-1,0}(0)=eta n^{-s}`.

A finite difference of a rational function has an asymptotic expansion in integral powers of `n`; it cannot equal `eta n^{-s}` for nonintegral `s`. Therefore `q=0`. The same coefficient equation then gives `l_2(-n)=0` for infinitely many `n`, so `l_2=0`.

The remaining relation `l_0F_0+l_1F_1+c=0` is killed by the degree-one distinct-exponent argument at `a=-n`: the exponents `-s`, `-s-1`, and `0` are distinct under the stated hypotheses, so each coefficient vanishes at infinitely many negative integers and therefore vanishes as a rational function. This proves the theorem.

## Anti-Theatre Check

This theorem is not an RH-equivalent positivity restatement. It lives inside the Hurwitz weld model and names the first nonlinear obstruction produced by the monodromy-line program.

The falsification point is explicit: if the regular-part sequence `R_{n,0}(0)` were rationally interpolable, the quadratic collision could be absorbed into a lower-degree term. The finite-difference obstruction blocks exactly that repair.

## Lean formalization

The exact card statement is the Lean target

```
FullyProvenNewTargets.HurwitzN2DensityShadowTarget (s : ℂ) : Prop :=
  1 < s.re → (∀ k : ℤ, (k : ℂ) ≠ s) →
  ∀ (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ) (N : ℕ),
    (∀ n ≥ N, ∀ z in the branch strip,
        ∑_{i,j} q i j · F_i F_j + ∑_k l k · F_k + cc = 0) →
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 1 1 = 0 ∧ q 0 2 + q 2 0 = 0 ∧ l 2 = 0 ∧ l 0 = 0 ∧ l 1 = 0 ∧ cc = 0
```

discharged unconditionally by

`FullyProvenNewTargets.hurwitz_quadratic_n2_density_shadow`
(`formal/GaloisForLFunctions/FullyProvenNewTargets.lean`),

which composes `Hurwitz.N2HalfInteger.hurwitz_n2_unconditional_all_noninteger`; the earlier generic
branch `Hurwitz.N2Final.hurwitz_n2_unconditional` needed the extra side condition `2s ∉ ℤ`, and the
half-integer branch removes it, so the Lean theorem covers exactly the card's hypothesis `s ∉ ℤ`.

The relation is stated on the local branch `a = -n + e^z` used in the card's proof (`x = a + n`),
with `tailFactored` the regular part `R_{n,k}` after removing the local singular term.  The
conclusion `q 0 2 + q 2 0 = 0` together with the vanishing of all other quadratic coefficients is
exactly the card's "any surviving quadratic part has the form `q(a)(F_0F_2 - F_1^2)`", and the
remaining vanishing statements close it.

Audited with `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.

## Log

- 2026-06-24 -- created as a proven support card from the parent Hurwitz weld/escape card.

## 2026-06-24 Superseded By All-N Quadratic Theorem

This `N=2` card is now a special case of `hurwitz-quadratic-all-n-tail-independence.md`, promoted to `2-fully-proven` on the same date. It remains useful as the minimal collision example `Y_0Y_2-Y_1^2`; the stronger theorem covers every finite shift ladder at total degree `<=2`.
