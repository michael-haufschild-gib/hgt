# Kapustin power gauges have infinite two-sided Krein index

- **ID:** `kapustin-power-gauge-infinite-krein-index`
- **Stage:** 2-fully-proven/new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** V. V. Kapustin, *Hilbert--Pólya Operators in Krein Spaces*, Siberian
  Mathematical Journal 65 (2024), 72--75
- **Statement:** Every explicit power gauge `phi_beta(s)=s^(-beta)` in Kapustin's theorem gives a
  critical-line weight with infinitely many positive and negative sign intervals.  The associated
  symmetric Krein space has positive and negative indices `(infinity,infinity)`, and no finite-rank
  correction of its metric can make it positive.

## Goal

Kapustin constructs exact spectral carriers for the nontrivial zeta zeros.  For an admissible
analytic gauge `phi`, put

```text
q(s)=(2pi)^(s-2) phi(s)/Gamma(s),
p(s)=(q(s)+q(1-s))/2=Re q(s)       on Re s=1/2.
```

On the symmetric subspace `f(1-s)=f(s)` of `L2(|p|)`, the operator

```text
T f = f/(s(1-s)) - [f,u]u,
u(s)=pi^(-s/2)Gamma(s/2)zeta(s),
```

is self-adjoint for the Krein metric `[f,g]=integral f conjugate(g) p`, and every nontrivial zero
`rho` gives the eigenvalue `1/(rho(1-rho))`.

The missing Hilbert--Polya step is not the spectrum but the metric.  This card determines the metric
inertia for the entire explicit family singled out in Kapustin's paper and tests whether its
indefiniteness is a finite defect that could be removed by a finite-rank polarization.

## Theorem

Fix real `beta>0` and use the principal branch of `s^(-beta)` on `Re s>1/2`.  For `t in R`, define

```text
q_beta(t)
  =(2pi)^(-3/2+it)
    / (Gamma(1/2+it)(1/2+it)^beta),

p_beta(t)=Re q_beta(t).
```

Then `p_beta` has infinitely many positive open intervals and infinitely many negative open
intervals as `t->+infinity`.  It is even, so the same holds at negative heights.

Let

```text
K_beta={f in L2(R,|p_beta(t)|dt): f(-t)=f(t)}
```

with indefinite form

```text
[f,g]_beta=integral_R f(t)conjugate(g(t))p_beta(t)dt.
```

Both the positive and negative indices of `K_beta` are infinite.  If `B` is any bounded finite-rank
Hermitian form on the Hilbert majorant `L2(|p_beta|)`, then `[.,.]_beta+B` still has infinite negative
index and therefore is not a Hilbert inner product.

In particular the conclusion holds for every `beta>17/21`, the explicit admissible power family in
Kapustin's theorem, including `beta=1`.

## Proof

### 1. Exact phase and Stirling asymptotics

For `t>0`, the function `q_beta(t)` is nonzero.  Choose its continuous argument
`Theta_beta(t)` on a positive half-line.  The logarithmic Stirling expansion, differentiable on every
closed subsector of the right half-plane, gives

```text
log Gamma(1/2+it)
 = (1/2)log(2pi) - (pi/2)t
   + i(t log t-t) + O(1/t),

arg(1/2+it)=pi/2-1/(2t)+O(1/t^3).
```

Consequently

```text
|q_beta(t)|
 =(2pi)^(-2)e^((pi/2)t)t^(-beta)(1+O(1/t^2)),              (1)

Theta_beta(t)
 =t log(2pi e/t)-(beta pi)/2+O(1/t),                       (2)

Theta_beta'(t)
 =log(2pi/t)+O(1/t^2).                                     (3)
```

The constant ambiguity in the continuous argument only adds an integral multiple of `2pi` and is
irrelevant.

Equation `(3)` shows that `Theta_beta` is strictly decreasing for all sufficiently large `t`, while
`(2)` shows that `Theta_beta(t)->-infinity`.  It therefore crosses every sufficiently negative
integer multiple of `pi`.  At successive crossings of even and odd multiples,

```text
p_beta(t)=|q_beta(t)|cos(Theta_beta(t))
```

has alternating signs.  Continuity supplies a nonempty open interval of the same sign around each
crossing.  This proves the infinite sign alternation.  Schwarz symmetry of `Gamma` and the principal
power gives `q_beta(-t)=conjugate(q_beta(t))`, hence `p_beta(-t)=p_beta(t)`.

### 2. The symmetric sector has index `(infinity,infinity)`

Let `I` be any positive interval on which `p_beta>0`.  Even functions supported on
`I union (-I)` form an infinite-dimensional positive-definite subspace of `K_beta`.  Repeating the
same construction with a negative interval gives an infinite-dimensional negative-definite
subspace.  Thus both Krein indices are infinite even after Kapustin's symmetry restriction.

### 3. Finite-rank metric corrections cannot Hilbertize

Let `N` be an infinite-dimensional negative-definite subspace constructed above.  A bounded
finite-rank Hermitian form `B` is represented by a finite-rank self-adjoint operator in the Hilbert
majorant.  The subspace

```text
N intersect ker(B)
```

has finite codimension in `N` and is therefore infinite-dimensional.  On it the corrected form
`[.,.]_beta+B` equals `[.,.]_beta` and remains strictly negative.  Hence every finite-rank metric
correction leaves infinite negative index.

This completes the proof.

## Hilbert--Polya consequence

Kapustin's power-gauge operators are exact global spectral realizations, but their displayed Krein
metric is not a Pontryagin metric with finitely many negative directions.  Its inertia is
`(infinity,infinity)` independently of the zeta divisor and remains so even if RH is assumed.  Thus:

1. the metric index cannot count off-line zeros;
2. the rank-one nature of the operator perturbation does not make the polarization defect rank one;
3. no finite-rank change of metric can turn these gauges into Hilbert--Polya operators; and
4. a successful repair must replace the metric by an infinite-rank, source-selected positive
   polarization, not merely adjust finitely many spectral modes.

This distinguishes Kapustin's carrier from the shifted-`Xi` generalized de Branges kernel in
`../not_new_scientific_knowledge/shifted-xi-kernel-transverse-index-filtration.md`, whose negative
index faithfully equals the number of zeros beyond the shifted line.

## Scope and non-implications

- The theorem closes only the explicit power gauges `phi_beta=s^(-beta)` and their finite-rank metric
  repairs.  It does not prove that every analytic gauge allowed by Kapustin has sign-changing weight.
- It does not dispute the exact eigenvalue theorem.  The operators remain valid Krein-self-adjoint
  carriers of `1/(rho(1-rho))`.
- It does not constrain CCM, Suzuki, Sonin, prolate, or finite-Weil constructions.
- It does not constrain finite-prime approximants that carry the `Xi` divisor locally uniformly and
  satisfy the sub-log-square reflected-energy condition on their zero fibres.  That cofinal transfer
  mechanism is recorded separately in
  `../../3-formalized/not_new_scientific_knowledge/finite-prime-logarithmic-boundary-transfer.md`.

## Novelty and significance audit

- **Exact parent comparison.** Kapustin proves that the weights define Krein spaces and that the
  associated rank-one perturbations contain all transformed zeta zeros in their point spectra.  The
  paper calls the metric indefinite but does not compute its positive or negative index, prove
  infinite sign alternation for the advertised power gauges, or analyze finite-rank Hilbertization.
- **Literature search.** Searches through July 2026 located Kapustin's 2021/2022 precursor and 2024
  Krein-space paper, but no source stating this weight asymptotic or the resulting two-sided infinite
  index.
- **Novelty.** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` The analytic ingredients are classical Stirling
  asymptotics and elementary Krein geometry.  The source-specific inertia theorem and its
  finite-rank-polarization consequence were not located in the parent literature.
- **Significance.** The theorem separates an exact zeta spectral carrier from a faithful RH defect
  carrier and closes the entire explicit gauge family offered in the 2024 paper as a finite-defect
  route to Hilbert--Polya.

## Gates

- [x] 0 -> 1: exact source operator, gauge family, and falsifiable inertia claim isolated.
- [x] 1 -> 2: complete Stirling, sign-alternation, symmetric-index, and finite-rank obstruction proof.
- [ ] 2 -> 3: no Lean formalization selected; the current tree lacks complex Stirling asymptotics and
  weighted Krein-space infrastructure, and a partial finite-dimensional wrapper would not formalize
  the theorem.
- [ ] 3 -> 4: independent expert check and broader admissible-gauge classification remain.

## Open core

`[CONJECTURE]` Every admissible Kapustin gauge has either a sign-changing weight of infinite negative
index or else contains, in its inner/outer factorization, an infinite-rank boundary phase whose
construction is already an RH-strength positive polarization.  The power-gauge theorem proves the
first branch only for the explicit family and does not establish this universal dichotomy.

## References

1. V. V. Kapustin, *Hilbert--Polya Operators in Krein Spaces*, Siberian Math. J. 65 (2024),
   72--75, DOI `10.1134/S0037446624010087`.
2. V. V. Kapustin, *The set of zeros of the Riemann zeta function as the point spectrum of an
   operator*, St. Petersburg Math. J. 33 (2022), 661--673, DOI `10.1090/spmj/1720`.
3. N. N. Lebedev, *Special Functions and Their Applications*, for the uniform complex Stirling
   expansion used in `(1)`--`(3)`.

## Log

- 2026-07-11 -- parent paper and project pipeline audited; power-gauge phase asymptotic isolated.
- 2026-07-11 -- infinite sign alternation, symmetric two-sided infinite index, and finite-rank
  non-Hilbertization proved on paper.
