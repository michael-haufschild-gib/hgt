# Prime-coherent scale factor forces perspective-neutral external time

- **ID:** `prime-coherent-scale-factor-clock-duality`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** user scale-factor/internal-metric conjecture; infinite prime-clock superspace; separate from
  Routes A--D in `docs/reports/rhtower_status_1107.md`
- **Statement:** The one-prime coherent-state clock metric is finite exactly to the right of the
  critical line. In the open strip, both functional-equation clock perspectives require an external
  clock exactly on `Re(s)=1/2`; consequently RH is equivalent to this perspective-neutral
  double-divergence condition at every `xi` zero.

## Goal

Turn the statement "an inner metric, often its scale factor, forces the external clock" into an
exact arithmetic theorem. The target is not a Hamiltonian whose spectrum is postulated to be the
zeros. It is a source-derived metric on the infinite prime coherent superspace, followed by a
functional-equation comparison of the two clock perspectives.

The card is deliberately disjoint from the four live RHTower routes. It neither estimates a live
carrier nor imports a zero-localization hypothesis.

## Gates

- [x] 0 -> 1 in-progress: the prime coherent family, its clock generator, scale factor, reflected
  criterion, RH equivalence, and parent-theory comparisons are explicit.
- [x] 1 -> 2 fully-proven: complete paper proof independently audited, including the coherent-state
  metric identity and the thermal-metric remainder estimate.
- [x] 2 -> 3 formalized: Lean proves the summability wall, reflected double-divergence selector, and
  RH equivalence; operator/Fubini--Study semantics remain a separately audited interpretation layer.
- [ ] 3 -> 4 publication-ready: exact literature comparison against zeta statistical mechanics,
  coherent CCR representations, quantum Fisher geometry, and supersymmetric RH models.

## 1. Prime coherent superspace and its inner clock metric

Let the one-particle space be `h_P = l2(P)`, with one bosonic mode for every rational prime. For
`s = sigma + i t`, use the formal displacement

```text
alpha_s(p) = p^(-s) = p^(-sigma) exp(-i t log p).
```

At a finite prime cutoff `P <= X`, this is an ordinary coherent state. The diagonal prime-clock
Hamiltonian is

```text
H_X = sum_(p <= X) (log p) N_p,
```

and `exp(-i u H_X)` sends `alpha_(sigma,t)` to `alpha_(sigma,t+u)`. The Fubini--Study metric of a
coherent-state orbit is the squared one-particle norm of the displacement differential. Hence

```text
ds_X^2 = A_X(sigma) (d sigma^2 + d t^2),
A_X(sigma) = sum_(p <= X) (log p)^2 p^(-2 sigma).
```

Equivalently, `A_X(sigma) = Var_(alpha_s)(H_X)`, up to the conventional factor `4` in quantum
Fisher information. Thus the intrinsic scale factor of the clock direction is

```text
a_X(sigma) = sqrt(A_X(sigma)).
```

This identity is exact at every finite cutoff; it is not an analogy.

## 2. Scale-factor wall `[PROVED HERE]`

Define

```text
A(sigma) = sum_p (log p)^2 p^(-2 sigma)
```

when the series converges. Then

```text
A(sigma) < infinity  iff  sigma > 1/2.                 (1)
```

### Proof

If `sigma <= 1/2`, then for every prime `p >= 2`,

```text
p^(-2 sigma) >= p^(-1),
(log p)^2 >= (log 2)^2 > 0.
```

Therefore the summand dominates `(log 2)^2/p`, and Euler's divergence of the prime harmonic series
forces divergence.

If `sigma > 1/2`, choose `epsilon > 0` so small that
`2 sigma - 2 epsilon > 1`. The standard logarithm bound
`log x <= x^epsilon/epsilon` for `x >= 1` gives

```text
(log p)^2 p^(-2 sigma)
  <= epsilon^(-2) p^(-(2 sigma - 2 epsilon)).
```

The comparison series over all positive integers converges because its exponent exceeds one.
Hence the prime subseries converges. This proves (1). ∎

The clock orbit therefore has a finite Hilbert-space tangent exactly for `sigma>1/2`. At and to the
left of the line, the intrinsic clock scale is infinite: the parameter `t` survives only as an
external coordinate of the singular coherent chart, not as a finite Fubini--Study direction.

## 3. Perspective-neutral clock theorem `[PROVED HERE]`

Functional-equation--Schwarz reflection preserves `t` and sends

```text
tau(s) = 1 - conj(s),
Re(tau(s)) = 1 - sigma.
```

For `0 < sigma < 1`, (1) gives

```text
A(sigma) = infinity and A(1-sigma) = infinity
  iff
sigma <= 1/2 and 1-sigma <= 1/2
  iff
sigma = 1/2.                                           (2)
```

Thus the critical line is the unique point of the strip where neither reflected clock perspective
possesses a finite internal scale factor. Off the line the clock status is asymmetric: exactly one
of the two reflected perspectives has a finite clock metric. The line is selected by
**perspective-neutral externality**, not by choosing either side as preferred.

## 4. RH equivalence `[PROVED HERE]`

Because completed `xi` zeros are the nontrivial zeros, (2) yields

```text
RH
  iff
for every rho, xi(rho)=0 implies
  not Summable(p |-> (log p)^2 p^(-2 Re(rho)))
  and
  not Summable(p |-> (log p)^2 p^(-2 (1-Re(rho)))).    (3)
```

The forward implication puts every zero on the line, where both series diverge by (1). Conversely,
the two divergences force `Re(rho)<=1/2` and `1-Re(rho)<=1/2`, hence `Re(rho)=1/2`.

Equation (3) is an exact reformulation, not a proof of RH. Its new content is the source-derived
metric meaning of the selector and the necessity of imposing it in both clock perspectives.

## 5. Relation to the zeta thermal Fisher metric `[PROVED HERE]`

The bosonic prime Fock partition function at inverse temperature `x=2 sigma` is

```text
Z(x) = product_p (1-p^(-x))^(-1) = zeta(x).
```

Its thermal Fisher metric is

```text
G_th(sigma) = (log zeta)''(2 sigma)
            = sum_p (log p)^2 p^(-2 sigma) / (1-p^(-2 sigma))^2.
```

It decomposes exactly as

```text
G_th(sigma) = A(sigma) + R(sigma),
R(sigma) = sum_p (log p)^2
  * (2 p^(-4 sigma) - p^(-6 sigma)) / (1-p^(-2 sigma))^2.   (4)
```

For `sigma >= 1/2`, the denominator is uniformly bounded away from zero and the remainder is
dominated by a constant times `(log p)^2/p^2`, hence extends finitely to the critical line. Therefore
the already-known Fisher blow-up

```text
G_th(sigma) ~ 1/(2 sigma-1)^2
```

is entirely carried by the one-prime coherent scale factor:

```text
A(sigma) ~ 1/(2 sigma-1)^2,
a(sigma) ~ 1/(2 sigma-1).                                (5)
```

Higher occupation-number superpositions change the metric only by the finite remainder `R` at the
wall. This is the precise sense in which the scale factor forcing the external clock is a primitive
prime-sector effect rather than an artifact of the full thermal ensemble.

## 6. Novelty and non-circularity audit

- The existing `critical-line-fisher-signature-wall` proves the full thermal metric blow-up and is
  RH-blind. It does not isolate the one-prime coherent metric, prove the finite remainder (4), or
  compare the internal/external status of both reflected clock perspectives.
- The existing prime-clock Shale theorem compares `alpha_s-alpha_tau(s)` and selects the line by
  equivalence of two coherent sectors. The present selector instead asks whether each perspective's
  **own clock tangent** has finite metric. Neither theorem implies the other's physical
  interpretation, although both share Euler's prime-harmonic threshold.
- Bost--Connes and prime-oscillator models identify `zeta` as a partition function; supersymmetric RH
  models select the critical line by normalizability or self-adjointness. The exact
  one-prime-scale-factor decomposition (4) and the double-externality criterion (2)--(3) were not
  found in the initial search.
- `[PARENT-THEORY VERDICT]` The analytic engine of (1) is classical comparison theory, the
  coherent-state metric/variance identity is standard quantum geometry, and the reflected criterion
  is a direct two-inequality composition. The exact arithmetic formulation was not found in the
  initial search, but it is parent-routine once the prime displacement is written down. The result is
  therefore graded **BRIDGE / not new scientific knowledge**. It remains significant as a constraint
  on viable superspace models.

## 7. What remains genuinely open

The theorem identifies the only perspective-neutral external-clock wall. It does not explain why
every zero of the completed Euler--Gamma constraint must live there. A non-circular proof still needs
the source to force the double-externality condition at its zeros, for example through a derived
constraint state whose two FE-related clock reductions are both singular but mutually compatible.

## Log

- 2026-07-11 — extracted from the user's inner-metric/scale-factor conjecture. Proved the prime
  coherent scale-factor wall, the reflected double-externality characterization of the critical
  line, the RH equivalence, and the finite thermal-remainder decomposition on paper.
- 2026-07-11 — formalized the summability wall, reflected selector, and RH equivalence in
  `PrimeClockScaleFactor.lean`; focused build, formal lint, and axiom audit pass. Strict novelty audit
  grades the result BRIDGE/not-new because every mathematical step is parent-routine after the prime
  coherent family is specified.
