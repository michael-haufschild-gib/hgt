# Kapustin power gauges require a noncompact full-sector polarization

- **ID:** `kapustin-power-gauge-infinite-krein-index`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** V. V. Kapustin, *Hilbert--Pólya Operators in Krein Spaces*, Siberian
  Mathematical Journal 65 (2024), 72--75
- **Statement:** Every explicit power gauge `phi_beta(s)=s^(-beta)` in Kapustin's theorem gives a
  critical-line weight with infinitely many positive and negative sign intervals.  The associated
  symmetric Krein space has indices `(infinity,infinity)`.  More positively: every bounded metric
  correction that Hilbertizes this carrier must dominate the identity on the complete negative
  sector, and is therefore necessarily infinite-rank, noncompact, outside every finite Schatten
  class, and of essential norm at least one.

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
inertia for the entire explicit family singled out in Kapustin's paper and gives a necessary operator
profile for every successful polarization.  The conclusion is a construction requirement, not only
an exclusion: the new metric must act coercively on an infinite-dimensional, explicitly located
negative sector.

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

Both the positive and negative indices of `K_beta` are infinite.  Let `J_beta` be the fundamental
symmetry `multiplication by sign(p_beta)`, and let `P_-` be the Hilbert-majorant projection onto the
negative sector.  If a bounded self-adjoint operator `G` corrects the metric so that

```text
J_beta+G >= 0,
```

then necessarily

```text
P_- G P_- >= P_-.                                             (4)
```

Consequently `G` has infinite rank, is noncompact, belongs to no finite Schatten class, and satisfies
`essentialNorm(G)>=1`.  If `J_beta+G>=epsilon I` for some `epsilon>0`, then the stronger bound

```text
P_- G P_- >= (1+epsilon)P_-                                  (5)
```

holds.

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

### 3. Every Hilbertization must dominate the full negative sector

In the Hilbert majorant, the original Krein form is

```text
[f,g]_beta=<J_beta f,g>.
```

For `f` in the range of `P_-`, one has `J_beta f=-f`.  Positivity of the corrected metric gives

```text
0 <= <(J_beta+G)f,f>
   =-||f||^2+<Gf,f>.
```

Therefore `<Gf,f>>=||f||^2` on the whole negative sector, which is exactly `(4)`.  Uniform positivity
with lower bound `epsilon` gives `(5)` in the same way.

Since the range of `P_-` is infinite-dimensional, `(4)` rules out compactness: if `G` were compact,
its compression `P_-GP_-` would be compact and could not dominate the identity on an
infinite-dimensional Hilbert space.  The same argument excludes every finite Schatten class.  The
image of `G` contains infinitely many independent negative-sector directions, so `G` has infinite
rank.  Finally, the image of `G` in the Calkin algebra has norm at least one because every compact
perturbation still has compression with lower essential spectral edge at least one.  Hence
`essentialNorm(G)>=1`.

The earlier finite-rank obstruction is now a corollary of the stronger positive requirement `(4)`.

This completes the proof.

## Hilbert--Polya consequence

Kapustin's power-gauge operators are exact global spectral realizations, but their displayed Krein
metric is not a Pontryagin metric with finitely many negative directions.  Its inertia is
`(infinity,infinity)` independently of the zeta divisor and remains so even if RH is assumed.  Thus:

1. the metric index cannot count off-line zeros;
2. the rank-one nature of the operator perturbation does not make the polarization defect rank one;
3. every successful metric must supply a noncompact full-sector correction satisfying `(4)`; and
4. a viable construction must therefore produce an infinite-rank, source-selected polarization with
   an essential lower bound, not merely adjust finitely many spectral modes.

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
- **Novelty.** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` The analytic ingredients are classical
  Stirling asymptotics and elementary Krein geometry.  More decisively, the universal bridge
  `kapustin-carrier-bilateral-polarization-law.md` derives two-sided infinite index for every bounded
  analytic gauge from established Toeplitz-kernel theory.  The
  power-gauge calculation is therefore a useful explicit specialization, not a separate scientific
  discovery.
- **Significance.** The theorem separates an exact zeta spectral carrier from a faithful RH defect
  carrier and gives the exact operator inequality every Hilbertization of the explicit 2024 gauge
  family must satisfy.  It replaces a finite-defect search by a noncompact full-sector polarization
  target.

## Gates

- [x] 0 -> 1: exact source operator, gauge family, and falsifiable inertia claim isolated.
- [x] 1 -> 2: complete Stirling, sign-alternation, symmetric-index, and full-sector polarization proof.
- [ ] 2 -> 3: no Lean formalization selected; the current tree lacks complex Stirling asymptotics and
  weighted Krein-space infrastructure, and a partial finite-dimensional wrapper would not formalize
  the theorem.
- [ ] 3 -> 4: independent expert check and broader admissible-gauge classification remain.

## Route disposition

The universal sign theorem in `kapustin-carrier-bilateral-polarization-law.md` closes the gauge
classification: every nonzero bounded analytic Kapustin gauge lies in the sign-changing branch.
The remaining target is no longer another gauge.  The attempted pointed global incidence metric
built from the weighted all-prime coefficient tail, archimedean completion, and distinguished
divisor/trace moments is classified and retired in
`../../5-failed/kapustin-source-incidence-polarization.md`: regular-germ continuous readings are
orbit-blind, `M_0` weighted-tail readings decouple, and divisor-faithful metric positivity is exactly
RH.  Reopening requires a new pre-divisor quantized source incidence that obeys `(4)` and canonically
produces the Hilbert metric before the Xi divisor is reconstructed.

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
- 2026-07-11 -- no-go recast as the positive full-sector requirement `P_-GP_->=P_-`; every successful
  Hilbertization must be noncompact, infinite-rank, and have essential norm at least one.

## Formalization progress (2026-08-24)

`GaloisForLFunctions.HTGeometry.FullSectorPolarizationLaw` now proves `(4)` and `(5)` as exact
quadratic-form inequalities, plus the induced unit norm floor, infinite algebraic rank,
noncompactness, and distance at least one from every compact perturbation.
`GaloisForLFunctions.RHTower.FullSectorPolarizationEssentialNorm` proves
`essentialNorm G ≥ 1` and exclusion from every positive Schatten class.  Both leaves pass direct
Lean checking and targeted leaf builds; new declarations use only standard Lean
`propext`/choice/quotient axioms.

Card remains Stage 2.  Exact phase/Stirling asymptotics `(1)`--`(3)`, infinite alternating sign
intervals, and the literal even weighted-`L²` Krein-index construction are still unformalized.
