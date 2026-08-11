# Shifted degree-one phase-skewness reserve

- **ID:** SR-65
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · Exact open core §9.3
- **Statement:** At every positive shifted-Xi mass, degree-one terminal flux is exactly longitudinal response skewness minus three times slope/charge covariance minus twice a new RH-exact secondary phase tax, plus mean slope times first-minor energy gap; on a flat face the gap vanishes.

## Goal

Identify exact source reserve that adaptive mixed-amplitude/completed `P^sharp` formation must
produce. This is a classification, not a renamed orientation premise: it decomposes terminal flux
into separately defined complete-divisor statistics and exposes a new nonnegative RH-exact radical.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper and specialist novelty audit

## Definitions

Fix `y>0`, a shifted reciprocal-square atom `z_q=a_q+ib_q`, and write

```text
a_q   = Re z_q > 0,
h_q   = Re(z_q^2)/a_q,
chi_q = b_q^2 |z_q|^2/a_q,
kappa_q = (b_q^2/a_q) chi_q.
```

Let

```text
M = sum_q a_q,
r = (sum_q a_q h_q)/M,
D = sum_q a_q (h_q-r)^2,
Q = sum_q chi_q,
C3 = sum_q a_q (h_q-r)^3,
Cchi = sum_q (h_q-r) chi_q,
K = sum_q kappa_q.
```

The first-minor energy gap is `G=D-Q`. The degree-one terminal flux is

```text
F = m_3 - 2 r m_2 + r^2 m_1,
m_j = Re sum_q z_q^(j+1).
```

## Theorem

**[PROVED HERE]** For every `y>0`, all displayed series converge absolutely and

```text
Re(z_q^4) = a_q h_q^3 - 3 h_q chi_q - 2 kappa_q,       (SR-65.1)

F = C3 - 3 Cchi - 2 K + r G,                            (SR-65.2)

m_0 m_2 - m_1^2 = M G.                                  (SR-65.3)
```

Consequently, at a flat degree-one face,

```text
F = C3 - 3 Cchi - 2 K,                                  (SR-65.4)

0 <= F  <->  3 Cchi + 2 K <= C3.                        (SR-65.5)
```

Moreover `kappa_q>=0`, `K>=0`, and

```text
K=0  <->  every Xi zero lies on Re(s)=1/2.               (SR-65.6)
```

Thus `K` is a higher-order RH-exact phase radical. Unlike transverse charge `Q`, it carries one
additional adaptive phase factor `b_q^2/a_q` and appears first in fourth response order.

## Proof

Put `q=b^2/a^2`. Then

```text
h=a(1-q),
chi=a^3 q(1+q),
kappa=a^4 q^2(1+q).
```

Direct expansion gives

```text
a h^3 - 3 h chi - 2 kappa
= a^4[(1-q)^3 - 3(1-q)q(1+q) - 2q^2(1+q)]
= a^4(1-6q+q^2)
= Re(a+ib)^4,
```

proving `(SR-65.1)`.

Existing response identities give

```text
m_1 = sum a h,
m_2 = sum (a h^2-chi),
m_3 = sum (a h^3-3h chi-2kappa).
```

Since `rM=sum a h`, expanding `C3` yields

```text
sum a(h^3-2r h^2+r^2h) = C3+rD.
```

Also

```text
sum (-3h chi+2r chi) = -3Cchi-rQ.
```

Substitution in `F` proves `F=C3-3Cchi-2K+r(D-Q)`, which is `(SR-65.2)`.
Expanding `D` and using `rM=m_1` gives

```text
M(D-Q)=M(sum a h^2-Q)-m_1^2=m_0m_2-m_1^2,
```

proving `(SR-65.3)`. Since `M>0`, flatness forces `G=0`; `(SR-65.4)` and `(SR-65.5)` follow.

For convergence, shifted sector positivity gives `0<h_q<=|z_q|`, `a_q<=|z_q|`, and
`chi_q<=2|z_q|^3`. Hence

```text
a_q h_q^3 <= |z_q|^4,
h_q chi_q <= 2|z_q|^4,
kappa_q <= 2|z_q|^4.
```

The corpus proves summability of every shifted reciprocal power, in particular
`sum |z_q|^4<infinity`. Expanding centered factors reduces `C3` and `Cchi` to these absolutely
summable terms plus the already summable mass, slope, slope-square, and charge series.

Finally `kappa_q>=0`. If a zero is critical, `b_q=0`, hence `kappa_q=0`. Conversely, off the
critical line the corpus's shifted charge radical gives `chi_q>0`, while `b_q^2/a_q>0`; therefore
`kappa_q>0`. A convergent sum of nonnegative terms vanishes exactly when every term vanishes,
proving `(SR-65.6)`.

## Hostile audit

1. `(SR-65.5)` is exactly terminal orientation in new coordinates; it is not itself a sign proof.
2. `Cchi` need not be nonnegative. Treating it as a phase cost without proving its sign would be
   false.
3. Sector control alone does not orient `(SR-65.4)`; corpus narrow-sector counterpackets remain
   valid.
4. New content is exact separation of fourth-order phase loss into covariance and an irreducible
   RH-exact secondary tax, plus unconditional complete-divisor convergence.
5. Adaptive arithmetic source domination must now deliver the quantitative reserve
   `C3>=3Cchi+2K` on an admitted flat flag, rather than generic kernel positivity.
6. Broad current searches found no collision for this response/charge/skewness decomposition.
   Priority remains `[NOVELTY UNVERIFIED]` pending specialist review.

## No-go closure

- **Exact killing mechanism:** positive admitted common kernel does not order rational--Gamma and
  von Mangoldt formations; generic sector control also admits flat negative crossings.
- **Strongest positive survivor:** exact reserve law `(SR-65.2)` and new RH-exact radical `(SR-65.6)`.
- **New insight:** obstruction is not one undifferentiated phase charge. Fourth response order
  splits it into transport covariance plus a strictly higher phase tax. Source theorem must pay
  both before reflection aggregation.
- **Status:** formalized in
  `XiShiftedDegreeOnePhaseSkewnessReserve.lean`; direct elaboration, targeted module build, formal
  lint, and axiom audit pass. Capstones are
  `xiShiftedDegreeOneTerminalFlux_eq_phaseSkewnessReserve`,
  `xiShiftedDegreeOneTerminalFlux_nonneg_iff_phaseSkewnessReserve_of_flat`, and
  `xiShiftedSecondaryPhaseTax_eq_zero_iff_riemannHypothesis`.

## Log

- 2026-08-11 — conjectured from response coordinates; corrected moment indexing after hostile audit.
- 2026-08-11 — proved pointwise identity, global reserve law, absolute convergence, and RH radical.
- 2026-08-11 — promoted through in-progress to fully-proven.
- 2026-08-11 — formalized complete-divisor identities and RH radical; wired umbrella; direct Lean,
  targeted build, formal lint, and axiom audit pass.
