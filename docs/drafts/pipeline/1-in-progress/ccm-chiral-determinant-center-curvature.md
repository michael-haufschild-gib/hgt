# CCM chiral determinant center-curvature seed

- **ID:** `ccm-chiral-determinant-center-curvature`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** whole-corpus weld: matched oriented characteristic cocycle × chiral nodal source shear × wall-light jets × determinant curvature
- **Statement:** Every actual prime-power nodal source-shear determinant has a double spectral-center zero and strictly negative second spectral derivative, with an exact positive two-term source formula.

## Goal

Produce an unconditional, coefficient-faithful chamber seed for the determinant-line carrier. The
target must expose more than the already known signed crossing in shear time: frequency curvature at
the reflection center must be forced by actual prime-polar geometry. This is a nonterminal source
statement; it uses no Xi divisor, Weil-positivity, RH, zero placement, or assumed source sign.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, exact leaf build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Conjecture C1

For one atom `n`, write

```text
C_n(x) = ∫_0^rho A cosh(r/2) (2 - 2 cos(2πrx)) dr,
P_n(x) = ∫_0^rho 2 A sinh(r/2) sin(2πrx) dr,
S_n(x) = cos(2π log(n)x) C_n(x) + sin(2π log(n)x) P_n(x).
```

Let `D_n(x)` be the determinant at unit source shear. Then

```text
D_n(x) = -2 a_n² S_n(x),
D_n(0) = D_n'(0) = 0,
D_n''(0) = -2 a_n² (Q_n + 4π log(n) M_n),
Q_n = ∫_0^rho 8π²r² A cosh(r/2) dr,
M_n = ∫_0^rho 4πr A sinh(r/2) dr.
```

For an actual prime-power label, `a_n != 0`, `rho > 0`, `Q_n > 0`, `M_n > 0`, and
`log n > 0`; hence `D_n''(0) < 0`.

## Paper proof

Differentiate the bounded-interval cosine and sine integrals twice under the integral sign. At
`x=0`, parity kills all order-zero and first-order mixed terms. Product rule leaves exactly cosine
curvature `Q_n` plus twice anchor rate `2π log n` times odd-current first moment `M_n`. Existing
mass matching makes `rho` positive at every prime-power wall; strict positivity of both moment
integrals follows from positive integrands on the nondegenerate interval. Existing projective gauge
nonvanishing and exact determinant formula transfer positive source curvature to strict negative
determinant curvature.

## Why this changes frontier

Prior nodal-shear theorem reads arbitrary source orientation at a fixed frequency but supplies no
preferred chamber. C1 forces a preferred chamber in a punctured center germ from source geometry
itself. It is first premise-free local chamber datum on this determinant line. Remaining global
problem becomes propagation/counting of later determinant crossings, compatible with corpus
Krein/Stokes and distributional source-reconstruction mechanisms.

## Kill tests

1. Kill if derivative formula cancels or requires a sign premise.
2. Kill if strictness fails for an actual prime-power label.
3. Narrow if result merely restates existing wall-light quadratic jet rather than differentiating
   the operator-derived determinant line.
4. Do not claim global chamber propagation or RH without a separate source-native theorem.

## Log

- 2026-08-21 — created after broad search across CCM characteristic, wall-light, Route-L reconstruction, Hilbert determinant curvature, quantum metric, Stokes, and exterior-source modules.
