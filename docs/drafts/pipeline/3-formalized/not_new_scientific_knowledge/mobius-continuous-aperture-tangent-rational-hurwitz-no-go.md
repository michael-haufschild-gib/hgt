# The first continuous Möbius source germ still sees the critical strip

- **ID:** `mobius-continuous-aperture-tangent-rational-hurwitz-no-go`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (Lean) / VALUE-REFLECTION GERM LIMIT / NO-GO WITH POSITIVE SUCCESSOR
- **Scientific status:** `[PROVED] [FORMALIZED]
  [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/XiMobiusContinuousApertureTangentRationalHurwitzNoGo.lean`
- **Parents:**
  - `../needs-audit/xi-mobius-continuous-aperture-szego-metric.md`
  - `mobius-continuous-aperture-rational-hurwitz-no-go.md`
  - `prime-seam-damping-aperture-law.md`
  - `uniform-positive-multiplier-summability-transfer.md`
- **Statement:** The right-normalized zero-aperture tangent of the continuous Möbius source metric,
  applied to the normalized rational-Hurwitz reflection energy, is summable exactly in the open
  critical strip, with the critical line as the zero case.  For every point in that strip, the
  total reflected source energy divided by the aperture converges to this finite tangent energy.
  Hence first-order source-germ finiteness is unconditional on every Xi fibre and cannot imply RH.

## Exact tangent/value splice

For a prime `p`, write `q=p^(-1)` and

```text
D_p(a)=(q/(1+q))^2 (1-p^(-a))/(1+p^(-a)).               (1)
```

The formalized source theorem gives

```text
D_p(0)=0,
D_p'(0)=1/2 (q/(1+q))^2 log p.                          (2)
```

For `rho=sigma+i*t`, the normalized rational-Hurwitz reflection energy remains

```text
H_p(rho)=p/4 (p^(-sigma)-p^(-(1-sigma)))^2.             (3)
```

Define the local reflected tangent energy `T_p(rho)=D_p'(0)H_p(rho)`.  Multiplying `(2)` and `(3)`
gives the exact splice

```text
T_p(rho)
 = 1/[8(1+q)^2] * log(p) p^(-1)
     * (p^(-sigma)-p^(-(1-sigma)))^2.                   (4)
```

Since `0<q<1`,

```text
1/32 <= 1/[8(1+q)^2] <= 1.                             (5)
```

Thus the tangent energy is uniformly equivalent to the `m=1`, `theta=1` member of the general
prime-seam logarithmic-moment hierarchy.

## Exact classification and germ limit

The all-moment damping-aperture law applied to `(4)`--`(5)` yields

```text
sum_p T_p(rho)<infinity
  iff sigma=1/2 or |2sigma-1|<1.                        (6)
```

For `a>0`, the existing source estimate gives

```text
|D_p(a)/a| <= (q/(1+q))^2 log p = 2 D_p'(0).            (7)
```

On the open strip, `(6)` makes the right side of `(7)` times `H_p(rho)` summable.  Pointwise
differentiability `(2)` and dominated convergence therefore prove the actual all-prime value limit

```text
lim_(a->0+) [sum_p D_p(a) H_p(rho)]/a
  = sum_p T_p(rho).                                     (8)
```

Every Xi zero lies in the open strip unconditionally, so both tangent summability and `(8)` hold on
every Xi fibre without RH.

## No-go closure and positive successor

- **Exact killing mechanism:** source-aperture differentiation inserts only one logarithmic prime
  moment and does not reduce the reciprocal-prime damping exponent.  Finite logarithmic moments do
  not change the strict prime-zeta convergence threshold.
- **Strongest positive survivor:** the exact local splice `(4)`, exact classification `(6)`, and
  the dominated all-prime reflected germ limit `(8)`.
- **New insight:** even the first nonzero normalized source germ is a finite vector throughout the
  critical strip.  The surviving RH interface must control a contractive/sign-sensitive transfer,
  a genuinely cofinal loss in the prime-power exponent, or a higher/non-finite-order boundary
  effect; mere existence or finiteness of the aperture tangent is now retired.  The first nonlinear
  dyadic cubic effect has subsequently been classified in the same way as log moment three.
- **Status:** dependency-closed paper proof and exact Lean formalization.  The source check, exact
  Lake target build, and representative axiom audit pass.

## Novelty and parent boundary

Differentiation of the hyperbolic tangent factor, dominated convergence for summable series, and
the invariance of a power-series convergence threshold under fixed logarithmic moments are
classical.  The source/value identification and its unconditional Xi consequence are
project-internal bridge closure.  No standalone new-science claim is made.

## Gates

- [x] exact source diagonal derivative already proved in the corpus
- [x] exact rational-Hurwitz reflection value already proved in the corpus
- [x] tangent/value factorization and two-sided comparison proved on paper
- [x] exact tangent summability classification proved on paper
- [x] dominated all-prime reflected germ limit proved on paper
- [x] first-order tangent-finiteness shortcut retired with a positive survivor
- [x] formalize the splice, classification, germ limit, and unconditional Xi Props
- [x] test and retire the first nonlinear dyadic cubic refinement as an RH selector
- [ ] derive source contractivity or a genuinely exponent-changing cofinal law

## Log

- 2026-07-19 — extracted by connecting the continuous Möbius diagonal derivative and domination
  theorem to the rational-Hurwitz value-reflection law and the general log-moment damping aperture.
- 2026-07-19 — formalized the exact tangent/value factorization, uniform two-sided comparison,
  exact summability aperture, total reflected right-germ limit by dominated convergence, and two
  unconditional all-Xi Prop interfaces.  The exact leaf source check and target build pass;
  representative declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-19 — followed by `mobius-dyadic-cubic-reflection-aperture-no-go.md`, which closes the
  all-prime cubic source limit and proves that its reflected third-moment germ also sees the strip.
