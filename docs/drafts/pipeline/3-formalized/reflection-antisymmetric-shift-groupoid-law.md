# The shift groupoid of a reflection-antisymmetric value function

- **ID:** `reflection-antisymmetric-shift-groupoid-law`
- **Stage:** 3-formalized
- **Type:** SUBSUMING GENERAL LAW / VALUE-RELATION INTERFACE
- **Status:** `[PAPER-PROVED]` and `[LEAN-PROVED]`; significance: infrastructure-grade, see §5
- **Parents (corpus):**
  - `formal/GaloisForLFunctions/RHTower/XiPairwiseShiftValueReflection.lean`
  - `formal/GaloisForLFunctions/RHTower/XiTransverseShiftPrimeDefectValueReflection.lean`
  - `formal/GaloisForLFunctions/RHTower/RiemannTower.lean` (`xi_differentiable`, `xi_one_sub`)

## 1. The residue this closes

The corpus proves the pairwise-shift value relations — reversal is negation, composition
telescopes, simultaneous translation is a gauge, and each oriented pair is fixed by the reflection
about its own midpoint — for `logDeriv xi` specifically, inside RHTower.  Reading those proofs, none
of them uses zeta.  All of them use exactly one input:

```text
logDeriv xi (1 - s) = - logDeriv xi s.
```

So the whole family is a statement about an arbitrary `L : ℂ → ℂ` with `L (c - s) = -L s`, and it
was being carried as a fact about one function.

## 2. The law `[PAPER-PROVED]`

Let `L : ℂ → ℂ` and set `D_L(a,b)(s) = L (s + a) - L (s + b)`, `sigma_{a,b}(s) = c - a - b - s`.

> **LAW.**
> **(A) Groupoid, unconditional.**  `D_L(a,a) = 0`, `D_L(b,a) = -D_L(a,b)`,
> `D_L(a,c') = D_L(a,b) + D_L(b,c')`, and `D_L(a+u, b+u)(s-u) = D_L(a,b)(s)`.
> **(B) Interface discharge.**  If `f` is differentiable on `ℂ` and `f (c - s) = f s` for all `s`,
> then `L = logDeriv f` satisfies `L (c - s) = -L s`.
> **(C) Centre value relation.**  `L (c - s) = -L s` forces `L (c/2) = 0`.
> **(D) Twisted reflection law.**  If `L (c - s) = -L s + M s` then
> ```text
> D_L(a,b)(sigma_{a,b}(s)) = D_L(a,b)(s) - D_M(a,b)(s).
> ```
> **(E) Reflection invariance.**  `M = 0` gives `D_L(a,b) ∘ sigma_{a,b} = D_L(a,b)`.
> **(F) Antipodal parity.**  If `a + b = c` then `sigma_{a,b}(s) = -s`, so `D_L(a,b)` is even.

**Proof.** (A) is `ring` on the definition.  (B) is the chain rule for `logDeriv` along
`t ↦ c - t`, whose derivative is `-1`: `logDeriv f s = logDeriv f (c - s) * (-1)`.  (C) is (D) at
`s = c/2`, where `c - c/2 = c/2` gives `L(c/2) = -L(c/2)`.  (D): with `s' = sigma_{a,b}(s)` one has
`s' + a = c - (s + b)` and `s' + b = c - (s + a)`, so

```text
D_L(a,b)(s') = L(c - (s+b)) - L(c - (s+a))
             = (-L(s+b) + M(s+b)) - (-L(s+a) + M(s+a))
             = D_L(a,b)(s) - D_M(a,b)(s).
```

(E) and (F) are specialisations.  `QED`

## 3. Lean status `[LEAN-PROVED]`

Unconditional (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`);
`scripts/formal_tools.py lint --check-generated` passes.

| Statement | Declaration |
|---|---|
| Interface | `HTGeometry.IsReflectionAntisymmetric`, `IsReflectionAntisymmetricWith` |
| (B) discharge | `HTGeometry.isReflectionAntisymmetric_logDeriv` |
| (C) centre value | `HTGeometry.eq_zero_of_isReflectionAntisymmetric` |
| (A) groupoid | `shiftDifference_self`, `_swap`, `_cocycle`, `_translationGauge` |
| (D) twisted law | `HTGeometry.shiftDifference_pairReflection_with` |
| (E) invariance | `HTGeometry.shiftDifference_pairReflection` |
| (F) antipodal parity | `HTGeometry.shiftDifference_neg_of_add_eq` |
| Xi discharge | `RHTower.isReflectionAntisymmetric_logDeriv_xi` |
| Xi identification | `RHTower.xiPairwiseShiftRawLogDerivDifference_eq`, `xiPairwiseShiftReflection_eq` |
| Xi reflection, derived | `RHTower.xiPairwiseShiftRawLogDerivDifference_pairReflection` |
| Xi antipodal parity (new) | `RHTower.xiPairwiseShiftRawLogDerivDifference_neg` |

Files: `formal/GaloisForLFunctions/HTGeometry/ReflectionShiftGroupoid.lean`,
`formal/GaloisForLFunctions/RHTower/XiReflectionShiftInstance.lean`.

## 4. What is new here and what is not

- (A) is trivial algebra and (C) is one line; neither is claimed as new mathematics.  `logDeriv xi
  (1/2) = 0` is already in the corpus as `logDeriv_xi_one_half`, proved directly; the general
  statement now covers it and every other reflection-antisymmetric value function at once.  No
  duplicate was added.
- (D) is the piece with content: the reflection **defect** of a shift difference is again a shift
  difference, formed from the multiplier's value function.  That makes twisted functional equations
  (`f(c-s) = m(s) f(s)`, i.e. incomplete L-functions, Gamma quotients, elliptic gamma factors) usable
  through the same interface, where before only the untwisted `xi` case was available.
- (B) is the practical delta: the interface is discharged from `Differentiable ℂ f` plus the
  functional equation, so any entire function with a reflection equation enters the calculus with no
  further work.
- (F) is a statement the Xi file does not contain.

## 5. Hostile verdict

`BRIDGE`, honestly labelled.  This is a subsumption and an interface discharge, not a new theorem
about zeta: the mathematics was already present, distributed across one function's file.  Its value
is that every future object with a functional equation — twisted or not — now gets the whole
value-relation package for the cost of one differentiability statement, and that the twisted defect
formula (D) had no representative in the corpus at all.

## 6. Next move

The interface `IsReflectionAntisymmetricWith c L M` is exactly what a *twisted* functional equation
supplies.  The concrete next object is the incomplete Euler factor: `zeta` itself satisfies
`zeta(1-s) = chi(s) zeta(s)`, so `M = -logDeriv chi` is an explicit elementary function (Gamma and
trigonometric), and (D) then computes the reflection defect of every pairwise shift difference of
`logDeriv zeta` in closed form.  That is a value relation for the *uncompleted* zeta which the corpus
currently has only for the completed one.
