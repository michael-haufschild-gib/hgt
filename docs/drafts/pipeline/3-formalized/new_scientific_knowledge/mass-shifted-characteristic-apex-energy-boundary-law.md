# Mass-shifted characteristic-apex energy boundary law

- **ID:** `mass-shifted-characteristic-apex-energy-boundary-law`
- **Stage:** 3-formalized
- **Route:** U
- **Type:** THEOREM
- **Scientific status:** `[PROVED HERE] [CORPUS-NOVEL] [EXTERNAL NOVELTY SEARCHED] [LEAN-PROVED]`
- **Lean status:** complete in `RHTower/XiShiftedCanonicalAdmissionCharacteristicApexEnergy.lean`,
  umbrella-wired. Shell continuity law `hasDerivAt_xiShiftedCanonicalAdmissionApexEnergyShell`
  (`e_n' = b_n + f_(n-1) - f_n`), telescoped finite budget
  `hasDerivAt_xiShiftedCanonicalAdmissionApexEnergy`
  (`(sum e_n)' = sum b_n + f_0 - f_N`), skew-Jacobi averaged transport, and both nonnegativity
  laws. Module build passes (2026-08-13); axiom audit `[propext, Classical.choice, Quot.sound]`
  on all five theorems.

## Frozen theorem

Put `A_n(y)=P_n(y,1/y)`, `N_n(y)=<P_n,P_n>_y`, and, for `n>0`,

```text
e_n = A_n^2/(n N_n),
f_n = 2 A_(n+1) A_n/N_n,
b_n = alpha_n e_n.
```

Whenever the shifted-Xi Hankel block through degree `N+1` is positive definite,

```text
e_n' = b_n + f_(n-1) - f_n,

(sum_(n=1)^N e_n)' = sum_(n=1)^N b_n + f_0 - f_N.
```

Thus characteristic transport has no interior degree leakage after canonical norm normalization.
All failure of a finite global budget is concentrated in one bottom endpoint flux, one moving top
flux, and the literal Jacobi diagonal production.

## Proof

Average the already proved backward and forward characteristic equations:

```text
A_n' = (a_n-n alpha_n) A_n + n beta_n A_(n-1) - n A_(n+1).
```

The canonical norm law is

```text
N_n' = (2 a_n-(2n+1) alpha_n) N_n.
```

Differentiate `A_n^2/(n N_n)`. The `a_n` terms cancel. The remaining diagonal coefficient is
`alpha_n`. For the backward coupling, use exact Jacobi norm identity

```text
N_(n-1) beta_n = N_n.
```

This gives `e_n'=b_n+f_(n-1)-f_n`. Summing from `1` through `N` telescopes every interior flux.
No limiting argument, infinite moment representation, RH premise, computation, or added axiom is
used.

## Conjecture / failure / pivot ledger

1. **Triangular apex ODE alone controls cofinal escape.** `[FAILED]` A finite cascade has no
   top-degree boundary condition; arbitrary top data can inject sign downward.
2. **Unweighted sum of apex squares closes.** `[FAILED]` Jacobi edge coefficients do not cancel.
3. **Norm weighting alone closes.** `[FAILED]` the forward coefficient carries an extra factor
   `n`.
4. **Degree-and-norm weight `1/(n N_n)` yields conservative transport.** `[PROVED HERE]` Jacobi
   norm ratios cancel every interior adjacent-degree term exactly.

## Higher principle and remaining obstruction

Characteristic apex transport is a discrete continuity equation in admission degree. Earlier
local contact laws saw one edge of this equation; apparent uncontrolled interior coupling was a
normalization artifact. The genuine global obstruction is boundary/source orientation:
`f_0`, `f_N`, and signs of `alpha_n`. A closing Route-U theorem must control these literal terms on
the intrinsic parabolic frontier schedule. More local transversality or generic positive-moment
transport cannot replace that source theorem.

## Novelty audit

Corpus search found characteristic transport, Jacobi norm flow, and adjacent-edge action
separately, but no apex-square continuity law or telescoping finite energy. Current literature
search found general time-dependent orthogonal-polynomial/Toda evolution, but no completed-Xi
moving-apex energy with this degree/norm normalization and boundary balance. External priority
remains provisional.

