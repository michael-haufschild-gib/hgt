# Xi Ward zero-adapted four-unit boundary-charge law

- **ID:** `xi-ward-zero-adapted-four-unit-boundary-charge-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / THEOREM (Lean)
- **Scientific status:** `[PROVED HERE] [UNCONDITIONAL] [NOVELTY AUDIT OPEN] [NOT RH]`
- **Lean module:** `RHTower/GammaSewnMobiusXiWardCofinalBoundaryLift.lean`

## Result

Let `q` be one upper representative of a strict-right Xi Schwarz pair and put

```text
lambda = xiRightCenteredZero(q),
a = Re(lambda),             0 < a < 1/2,
w_q = conj(lambda).
```

For the absolutely convergent continued anti-causal Xi Ward response

```text
r_P(w)
 = sum_p 2[(w+lambda_p)^(-1)+(w+conj(lambda_p))^(-1)],
```

the zero-adapted node obeys the unconditional atomic charge bound

```text
Re r_P(w_q) > 1/a,
|r_P(w_q)|^2 > 2/a.                                  (1)
```

For the right-half-plane Cauchy Gram,

```text
G(w_q,w_q)=1/(2a),
```

so `(1)` is exactly

```text
|r_P(w_q)|^2 > 4 G(w_q,w_q).                         (2)
```

Thus one strict-right Xi pair makes the one-node diagonal of

```text
4G-r_P r_P^*
```

strictly negative. Equivalently, the actual augmented boundary Gram

```text
W_P = [[G,r_P],[r_P^*,4]]
```

is not positive semidefinite on that adapted singleton packet.

Lean then proves the exact endpoint classification

```text
RiemannHypothesis
  <->
for every finite right-half-plane packet P,
  W_P is positive semidefinite.                         (3)
```

The equivalent Schur-complement formulation is also formalized.

## Proof

For every right-half-plane node `w` and every strict-right Schwarz pair `p`, both denominators in

```text
2[(w+lambda_p)^(-1)+(w+conj(lambda_p))^(-1)]
```

have positive real part. Their inverses therefore have positive real part, so every pair response
has positive real part.

At `w_q=conj(lambda)`, the first term of the selected pair is

```text
2/(conj(lambda)+lambda)=1/a.
```

Its second term has strictly positive real part. Hence the selected response has real part
strictly greater than `1/a`. Absolute summability permits taking real parts termwise. Every
remaining pair is nonnegative, so the full infinite response retains the strict lower bound.

Since `a<1/2`, `a^(-1)>2`. Squaring the positive real-part lower bound and using

```text
(Re z)^2 <= |z|^2
```

gives

```text
|r_P(w_q)|^2 > a^(-2) > 2a^(-1)=4G(w_q,w_q).
```

This proves `(2)` without truncation, cancellation assumption, zero enumeration, or RH hypothesis.
The block/Schur equivalence follows from the positive definite scalar corner `4`. Under RH the
strict-right divisor is empty, so `r_P=0` and `W_P=diag(G,4)` is positive semidefinite. Conversely,
failure of RH supplies `q`, and `(2)` supplies the singleton non-PSD witness.

## New mechanism

Generic Ward estimates face cancellation from the complete Xi divisor. Zero-adapted sampling
removes that obstacle: at `w=conj(lambda_q)`, every Schwarz-pair contribution lies in the open
right half-plane. The entire infinite tail reinforces the selected atom instead of cancelling it.

The resulting boundary charge is quantized by transverse displacement:

```text
any PSD lift with scalar boundary diagonal d must have d > 2/a
```

for every strict-right zero with displacement `a`. In particular the CCM critical value `d=4`
allows no strict-right atom because `a<1/2`.

## Exact frontier

Equation `(3)` proves that constructing the requested four-unit lift is exactly an RH proof. It
does not construct that lift unconditionally. Remaining proof-bearing task is source-side:
derive positivity of this already fixed block from the singular/cofinal Möbius--Gamma source
without assuming a bounded, norm-holomorphic, finite-rank, or target-factored transport.

## Formal audit

- Direct `lake env lean` check: passed.
- No hypotheses in `(1)`--`(3)` beyond the displayed strict-right pair for the obstruction arm.
- No numerical experiment or zero computation.
- No `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration.

## Gates

- [x] 0 → 1: exact boundary object and zero-adapted attack identified
- [x] 1 → 2: dependency-closed paper proof
- [x] 2 → 3: Lean module checks directly
- [ ] 3 → 4: independent literature novelty audit and paper integration
- [ ] source-side positivity of `W_P`
- [ ] RH
