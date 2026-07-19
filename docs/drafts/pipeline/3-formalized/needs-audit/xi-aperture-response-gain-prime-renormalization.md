# Xi aperture response-gain prime renormalization

- **ID:** `xi-aperture-response-gain-prime-renormalization`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM (Lean) / positive survivor from a trace-class no-go
- **Source:** `XiAperturePoissonUnitApertureHilbertTransport.lean`,
  `XiMobiusContinuousApertureSzegoMetric.lean`, and the HTGeometry Hilbert--Schmidt/Fredholm layer
- **Scientific status:** `[PROVED HERE ON PAPER] [LEAN-PROVED]`
  `[CANDIDATE NEW RH-PROOF-SHAPE KNOWLEDGE] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`

## Exact statement

For a prime `p`, put `q_p=p^{-1}`.  The already formalized squared gain from the true
aperture-one Szegő ray to the completely valuation-fused Poisson response is

```text
g_p=((1+q_p)/(1-q_p))^3.                                (RG1)
```

Then:

```text
g_p - 1 - 6q_p
  = 2q_p^2(9-8q_p+3q_p^2)/(1-q_p)^3.                   (RG2)
```

Since `0<q_p<=1/2`, the remainder `r_p` in `(RG2)` satisfies

```text
0 < r_p <= 144q_p^2.                                   (RG3)
```

Consequently `sum_p r_p` converges.  In contrast,

```text
g_p-1 >= 6q_p,
```

so `sum_p(g_p-1)` diverges by Euler's divergence of the reciprocal-prime series.  Moreover
`g_p-1=O(q_p)`, hence `sum_p(g_p-1)^2` converges.

On the prime-coordinate Hilbert carrier this classifies the diagonal gain correction:

```text
G-I = 6 P^(-1) + R,
```

where `G-I` is Hilbert--Schmidt but not trace class, while the positive remainder `R` is trace
class.  Thus `6/p` is the unique first-order non-trace-class counterterm exposed by the exact
aperture transport.

## Paper proof

Expanding the numerator gives

```text
(1+q)^3-(1-q)^3-6q(1-q)^3
  = 18q^2-16q^3+6q^4
  = 2q^2(9-8q+3q^2),
```

which proves `(RG2)`.  On `0<q<=1/2`, the quadratic factor is positive and at most `9`, while
`(1-q)^(-3)<=8`; this proves `(RG3)`.  Prime-square summability gives `sum_p r_p<infinity`.
Also `(1-q)^3<=1`, so `(g_p-1)>=(6q+2q^3)>=6q`; reciprocal-prime divergence proves the
trace-class no-go.  The same formula and `q<=1/2` give `g_p-1<=52q`, hence square summability.

## Why this matters for the RH route

The sharp bound `g_p<=27` proves bounded raywise transport but does not make the all-prime gain
correction trace class.  The obstruction is not an uncontrolled tail: it has the exact universal
form `6/p`.  Removing that one channel leaves a positive trace-class correction, which is the
correct determinant-compatible object for the HTGeometry Fredholm machinery.  Any completed
aperture response operator should therefore be renormalized by `I+6P^(-1)`, not by the identity
alone.

This does not continue the operator through the critical strip or prove its required indefinite
sign.  It identifies the precise renormalization class that such a continuation must preserve.

## Hostile audit

1. The rational expansion and prime harmonic divergence are classical ingredients.  Candidate
   novelty is the exact `1+6/p+trace-class` classification forced by the actual Xi aperture--Poisson
   gain.
2. A diagonal sequence classification is not yet a constructed completed response operator.
3. The factor `6` is forced by the derivative of `(1+q)^3/(1-q)^3` at `q=0`; changing it leaves a
   non-summable reciprocal-prime tail.
4. External specialist novelty review remains open.

## No-go closure

- **Killed route:** treat the bounded true-aperture gain as a trace-class perturbation of the
  identity and feed it directly to an ordinary Fredholm determinant.
- **Killing mechanism:** `g_p-1>=6/p`, hence the diagonal correction is not trace class.
- **Strongest positive survivor:** subtract the exact marginal channel `6/p`; the remaining
  positive diagonal is dominated by `144/p^2` and is trace class.
- **New invariant:** the universal prime-harmonic counterterm coefficient `6`.

## Lean status

`RHTower/XiApertureResponseGainPrimeRenormalization.lean` formalizes:

1. the exact rational decomposition `(RG2)`;
2. strict positivity and the `144/p^2` majorant `(RG3)`;
3. divergence of `sum_p(g_p-1)` from reciprocal-prime divergence;
4. summability of the positive renormalized remainder; and
5. square-summability of `g_p-1`, giving the sequence-level Hilbert--Schmidt/not-trace-class
   dichotomy.

The exact scratch leaf check passes.  `#print axioms` for the decomposition, divergence,
renormalized summability, and square-summability theorems reports only `propext`,
`Classical.choice`, and `Quot.sound`.  No umbrella or full project build was used.

## Gates

- [x] 0 -> 1: exact obstruction and positive survivor derived
- [x] dependency-closed paper proof
- [ ] external novelty audit
- [x] Lean exact decomposition, sign, divergence, and summability
- [x] splice to the HTGeometry regularized Fredholm determinant carrier

## Log

- 2026-07-19 — the sharp gain theorem was hostile-tested against all-prime trace-class transport;
  the failure has the exact positive survivor `G-I=6P^(-1)+R` with `R` positive trace class.
- 2026-07-19 — formalized the exact decomposition, non-trace-class obstruction,
  Hilbert--Schmidt square summability, and positive trace-class remainder; targeted leaf and axiom
  audits pass.
- 2026-07-19 — determinant splice completed in
  `XiApertureResponseCorrelationDet2.lean`: the coefficient `6` is uniquely characterized by
  trace-class renormalizability; the det2 logarithmic response cancels the linear channel exactly
  and exposes the positive summable survivor `36/p^2+c_p`.  The diagonal determinant is zero-free,
  so this also closes it as a divisor/Morse-crossing route and forces an off-diagonal completed
  prime--Gamma/cross-aperture coupling.
