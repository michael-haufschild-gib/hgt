# Determinant-controlled squarefree projection

- **ID:** twin-prime-determinant-squarefree-transfer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / BRIDGE
- **Source:** [affine squarefree transfer](twin-prime-affine-squarefree-transfer.md).
- **Statement:** At determinant four, joint square-divisor incidence permits equal truncation cutoffs with error `9T/R + sqrtNat(F(T)) + R sqrtNat(G(T))`.

## Exact statement

Let `F(t)=at+b` and `G(t)=ct+d` be reduced primitive positive
affine rows, and let `|ad-bc|=4`. Use the actual correlations
`C_mu` and `C_lambda` defined on the affine squarefree transfer card.
For every natural `T` and positive integer cutoffs `R,S`,

```text
|C_mu(T)-C_lambda(T;R,S)|
 <= T/R + sqrtNat(F(T)) + 8T/S + R sqrtNat(G(T)).       (1)
```

Thus `S=R` gives

```text
|C_mu(T)-C_lambda(T;R,R)|
 <= 9T/R + sqrtNat(F(T)) + R sqrtNat(G(T)).             (2)
```

Only `R^2` retained pairs are needed, instead of `R^3` under
the asymmetric truncation. This improves the finite transfer;
it does not assert cancellation of its retained Liouville sum.

The same proof works at every positive determinant magnitude
`D=|ad-bc|`: replace `8T/S` by `2DT/S` in (1), and `9T/R`
by `(1+2D)T/R` in (2). The Lean domain therefore uses a
pair of primitive rows with an explicit positive determinant.
This arithmetic domain condition contains no cancellation input.

## Closed paper proof

Write `A_R(n)=lambda(n) sum_(1<=u<=R,u^2|n) mu(u)`.
The preceding transfer gives the exact tail identity and

```text
sum_(t=1..T) |mu(F(t))-A_R(F(t))|
 <= T/R + sqrtNat(F(T)).
```

Retain divisibility in the second product error rather than using
the uniform pointwise bound `|A_R|<=R`:

```text
|A_R(F(t))| |mu(G(t))-A_S(G(t))|
 <= sum_(1<=u<=R,u^2|F(t))
      sum_(S<v<=sqrtNat(G(T)),v^2|G(t)) 1.
```

For fixed positive `u,v`, set `g=gcd(u^2,v^2)` and
`q=lcm(u^2,v^2)`. If both divisibilities hold anywhere, then
`g` divides both row values and hence divides
`aG(t)-cF(t)=ad-bc`. Therefore `g<=4`.
Each primitive row selects at most one residue modulo its
square divisor. Their joint selection lies in one residue
modulo `q`, so its count in `[1,T]` is at most `T/q+1`.
The exact relation `gq=u^2v^2` then gives

```text
#{t<=T : u^2|F(t), v^2|G(t)} <= 4T/(u^2v^2)+1.
```

If the joint set is empty, the same bound holds directly.
Summing and using
`sum_(1<=u<=R) 1/u^2 <= 2` and
`sum_(S<v<=M) 1/v^2 <= 1/S`, the weighted second error is
at most `8T/S + R sqrtNat(G(T))`.
The exact product decomposition

```text
mu(F)mu(G)-A_R(F)A_S(G)
 = [mu(F)-A_R(F)]mu(G) + A_R(F)[mu(G)-A_S(G)]
```

and `|mu(G)|<=1` prove (1); elementary algebra proves (2).
Every sum is finite, and `T=0` is included.
For general positive `D`, the sole change is `g<=D`, giving
`DT/(u^2v^2)+1` for the joint count and exactly the generalized
constants above. This also proves the stronger domain statement
before formalization.

## Attack and scientific status

- The determinant is essential to this argument: it bounds the
  common square modulus. Equal rows would not satisfy this bound.
- Empty or incompatible residue intersections contribute zero;
  no CRT solution is assumed to exist.
- The error counts actual joint divisibility, so no sign estimate
  or unproved uniformity bound enters.
- Corpus search: primitive affine determinant/common square
  divisor/joint residue count. Surfaced affine-pair sieve root
  counts and the preceding transfer, but no exact matching bound.
  This is a scoped search, not an assertion of worldwide novelty.
- Verdict **BRIDGE**: an elementary determinant/CRT refinement
  of the squarefree projection. No new cancellation theorem or
  scientific-priority claim. The finite refinement is Lean-certified; the larger analytic
  cancellation argument still requires its own complete certificate.

## Gates

- [x] Exact statement, empty-set case, determinant and endpoint costs.
- [x] Closed paper proof without an analytic input.
- [x] Lean joint residue count with determinant bound.
- [x] Lean weighted tail and two-row error, including equal cutoffs.
- [x] Foreground leaf audit, transitive axiom audit and umbrella wiring.

## Log

- 2026-10-24 — Extracted the determinant-sensitive improvement
  while formalizing the unrestricted two-row transfer. The full
  analytic inputs and twin-prime infinitude remain unproved.

## Lean certificate

Module: `formal/GaloisForLFunctions/twin-prime/AffineSquarefreeTransfer.lean`.
Namespace: `TwinPrime.AffineSquarefree`.

- `Frame D`: primitive affine rows with absolute determinant `D>0`.
- `jointDivisorCount_le_lcm`: actual joint residue count.
- `Frame.dvd_determinant`: common divisors divide the determinant.
- `Frame.jointDivisorCount_le`: density at most `DT/(qr)+1`.
- `sum_square_divisor_counts_mul`: exact joint-incidence double count.
- `Frame.sum_weighted_error_le`: weighted omitted tail at most
  `2DT/S + R sqrtNat(G(T))`.
- `Frame.abs_correlation_sub_le`: generalized inequality (1).
- `Frame.abs_correlation_sub_same_cutoff_le`: generalized inequality (2).
- `abs_correlation_sub_same_cutoff_det_four_le`: coefficient nine
  at determinant four.

The foreground command
`lake --old env lean GaloisForLFunctions/twin-prime/AffineSquarefreeTransfer.lean`
exited 0 without warnings. All eight new capstone axiom audits
returned only `propext`, `Classical.choice`, and `Quot.sound`.
Audit directives were removed. The existing `twin-prime/Main.lean`
import includes the full module; no umbrella was compiled.

- 2026-10-24 — Formalized the general positive-determinant theorem
  and its determinant-four specialization. This closes the finite
  refinement, not the analytic cancellation or twin-prime goal.
