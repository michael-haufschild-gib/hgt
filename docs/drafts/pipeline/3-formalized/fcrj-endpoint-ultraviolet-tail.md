# FCRJ endpoint ultraviolet tail

- **ID:** FCRJ-UVT
- **Stage:** 3-formalized
- **Type:** THEOREM `[PAPER-PROVED] [LEAN-PROVED]`
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md` · Conjecture loop 58 survivor
- **Statement:** Physical FCRJ character-energy tail has exact `1/N` coefficient equal to signed endpoint jump-square mass.

## Goal

Replace vague “retain high frequencies” warning by exact source law.  For finite active physical
prime packet `P`, aperture `A>0`, and signed endpoint moment

```text
U_n = sum_x j(x) fourier_1(x)^n,
J   = sum_x |j(x)|^2,
```

prove

```text
lim_(N->infinity) N sum_(n>N) |U_n|^2/n^2 = J.         (UV1)
```

Using exact endpoint differentiation

```text
U_n = (2 pi i n/A) A_n,
```

deduce exact physical tail law

```text
lim_(N->infinity) N sum_(n>N) |A_n|^2
  = A^2/(4 pi^2) J.                                    (UV2)
```

For nonempty active packet, right side is positive.  Hence physical character tail is exactly
order `1/N`, never `o(1/N)`.  This is source-pure and does not assume RH or response saturation.

## Gates

- [x] 0 → 1 in-progress: exact source-pure statement, corpus basis, hostile audit, proof plan
- [x] 1 → 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency
- [x] 2 → 3 formalized: exact Lean theorem, targeted build, axiom and lint gates
- [ ] 3 → 4 publication-ready: independent expert priority review

## Corpus frontier `[CORPUS]`

1. `sum_endpointCircleJump_mul_fourier` identifies `U_n` with aperture-character rate times exact
   physical FCRJ amplitude for every nonzero integer frequency.
2. `tendsto_finiteExponentialPencil_cesaro_norm_sq` and
   `tendsto_xiPhysicalPrimeLogEndpointCircleMoment_cesaro_norm_sq` prove
   `N^-1 sum_(n<N)|U_n|^2 -> J`.
3. `sum_normSq_xiPhysicalPrimeLogEndpointCircleJump_pos` proves `J>0` for every nonempty active
   packet of raw width in `(0,A)`.
4. `tsum_normSq_xiPhysicalPrimeLogCharacterAmplitude` gives total Parseval energy but no tail
   asymptotic.
5. Corpus search found reciprocal-square tail bounds and finite Abel summation, but no theorem
   converting a Cesàro limit into exact scaled inverse-square tail, and no physical FCRJ law
   `(UV1)--(UV2)`.

## External frontier `[LITERATURE]`

Periodic Bernoulli/Green kernels and Fourier reconstruction of piecewise-smooth functions make
`1/n` jump asymptotics classical.  Abelian partial summation makes the abstract implication

```text
(1/N) sum_(n<N) a_n -> L
  ==> N sum_(n>N) a_n/n^2 -> L                         (UV0)
```

classical for nonnegative `a_n`.  Literature on logarithmic prime intervals controls prime counts
or moments, not this signed clipped prime-log aperture carrier.  Targeted search found no primary
source stating `(UV1)` or `(UV2)` for the physical FCRJ packet.  Novelty claim is restricted to
the source-specific specialization and its route consequence; `(UV0)` and Fourier jump theory are
not claimed new.

## Conjecture loop A — abstract tail principle

`[CONJECTURE]` `(UV0)` holds for every nonnegative real sequence whose Cesàro mean converges.

Hostile verdict: `REDISCOVERED`.  It is an Abelian partial-summation consequence and is not new
scientific knowledge.  Killing mechanism: statement contains no arithmetic source and belongs to
classical summability theory.

Failure-driven replacement: retain exact endpoint differentiation and positive physical jump mass.
The generic theorem becomes infrastructure; scientific claim is `(UV1)--(UV2)` and its sharp
classification of the FCRJ ultraviolet tail.

## Conjecture loop B — physical endpoint tail

`[CONJECTURE] [FROZEN 2026-08-27]` Equations `(UV1)--(UV2)` hold with no error hypothesis.  For a
nonempty active packet their common coefficient is positive, so

```text
not (sum_(n>N)|A_n|^2 = o(1/N)).                       (UV3)
```

### Hostile audit

- Not circular: definitions use finite prime packet, clipped aperture intervals, endpoint jumps,
  and Fourier characters only.
- Not a total-energy upper bound: it controls `N -> infinity` for each fixed packet.  It does not
  provide uniformity when packet and endpoint separations move with the arithmetic scale `M`.
- Not implied by pointwise nondecay alone: `(UV1)` gives exact tail coefficient, not merely a
  subsequence with nonzero differentiated amplitude.
- Classical parent survives unchanged, but source identification and strict physical coefficient
  require corpus endpoint differentiation and noncancellation.

Verdict: `SURVIVES PRELIMINARY ATTACK` as source-specific theorem.  Significance is exact boundary
on the proposed FCRJ survivor: any `O(M^-1 polylog M)` proof must be uniform in the moving packet
and must control endpoint phase collisions; it cannot obtain extra ultraviolet decay.

## Approach

Let `a_n=|U_n|^2` and `S_N=sum_(n<N)a_n`.  Wiener gives `S_N/N -> J`.  Write
`S_N=JN+r_N`, where `r_N=o(N)`.  Finite Abel summation for `M<=n<=R` gives

```text
sum_(n=M)^R a_n/n^2
 = S_(R+1)/R^2 - S_M/M^2
   + sum_(n=M+1)^R S_n(1/(n-1)^2-1/n^2).              (UV4)
```

The terminal term tends to zero.  Substituting `S_n=Jn+r_n`, exact telescoping leaves

```text
J sum_(n=M)^infinity 1/n^2.
```

Since `M sum_(n>=M)n^-2 -> 1`, this contributes `J`.  For every `epsilon>0`, eventually
`|r_n|<=epsilon n`; the error in `M` times `(UV4)` is bounded by a fixed multiple of `epsilon`,
so it tends to zero.  This proves `(UV0)` and `(UV1)`.

For `n>0`, endpoint differentiation and
`|2 pi i n/A|^2=4 pi^2 n^2/A^2` give termwise

```text
|A_n|^2 = A^2/(4 pi^2) |U_n|^2/n^2.                  (UV5)
```

Absolute convergence permits summing `(UV5)` over `n>N`, proving `(UV2)`.  Strict jump-mass
positivity gives positive limit and `(UV3)`.

### Dependency-closed form

Put `g_n=S_n/n` for `n>0` (and any value at `n=0`).  Then `g_n -> J`.  With `M=N+1`, infinite
Abel summation is justified directly from `g_n=O(1)` and the summable inverse-square kernel, and
gives

```text
sum_(n>=M) a_n/n^2
 = -g_M/M
   + sum_(j>=M) g_(j+1)/j^2
   + sum_(j>=M) [g_(j+1) j/(j+1)]/j^2.               (UV6)
```

Both bracketed weights converge to `J`.  Corpus theorem `tendsto_weightedTail_rpow` at `p=0`
therefore makes the two scaled tails converge to `J`, while
`N g_(N+1)/(N+1) -> J`.  Hence `(UV6)` has scaled limit `-J+J+J=J`.  This proves `(UV0)` with no
extra boundedness or summability premise: both follow inside Abel summation from convergence of
`g`.  Equations `(UV5)` and source Parseval then give `(UV2)`; strict jump mass gives `(UV3)`.

Every dependency is already proved in corpus: finite endpoint Wiener law, endpoint
differentiation, weighted inverse-square tail asymptotic, character Parseval, and strict endpoint
jump mass.  No analytic hypothesis remains.

`[LEAN-PROVED]` Module `XiPhysicalPrimeEndpointUltravioletTail.lean` formalizes the two-kernel
Abel transfer, exact moment law `(UV1)`, exact character law `(UV2)`, and strict nonzero scaled-tail
obstruction `(UV3)`.  Generic Lean transfer exposes weighted-tail summability as a premise; exact
physical Parseval discharges it unconditionally.  Next conjecture must quantify convergence
uniformly in moving prime packet through endpoint phase-separation data.

## No-go closure

- **Exact killing theorem/mechanism:** Any FCRJ claim asserting `o(1/N)` high-character energy is
  killed by positive endpoint jump-square mass and `(UV2)`.
- **Strongest positive survivor:** Exact `1/N` law `(UV2)`; coefficient is physical endpoint charge.
- **New insight:** Fixed-packet ultraviolet tail is fully determined.  Remaining analytic burden is
  two-parameter uniformity under moving endpoint collisions, not another Fourier decay estimate.
- **Status:** `[PAPER-PROVED] [LEAN-PROVED]`; fixed-packet ultraviolet tail closed.

## Log

- 2026-08-27 — created in Stage 1 after corpus and primary-literature audit; loop A marked
  `REDISCOVERED`, loop B frozen.
- 2026-08-27 — promoted to Stage 2 after exact two-kernel Abel decomposition `(UV6)` closed all
  summability and limit dependencies from existing corpus theorems.
- 2026-08-27 — formalized in `XiPhysicalPrimeEndpointUltravioletTail.lean`; direct Lean check,
  targeted module build, axiom audit, and formal lint passed.  Promoted to Stage 3.
