# Route L: cofinal Green source limits with a retained Xi coefficient

- **ID:** L-C40
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM; original-source compact escape and retained physical readout
- **Depends on:** [C38 finite Green source](../3-formalized/route-l-complete-green-domain-comparison.md) and [C39 full Xi/Sonin transport](../3-formalized/route-l-paired-source-sonin-reader.md)
- **RH status:** unproved

Chain: complete original Green/BV source → fixed physical-reader agreement
→ conormal vanishing → RH. C39 proves that finite paired depletion preserves
the original fixed physical image up to a source-derived nonzero multiplier.
The next attack is the actual infinite-prime limit and its source domain.

## Proven source-limit law

Let `P_n` be finite ordered prime lists such that each original prime
belongs to every sufficiently late list. Let `h_n` be C38's paired Gaussian
source for `P_n`, in the original topologized Meyer source space. For any
complex scalar sequence `c_n`, every convergent sequence `c_n h_n` has
limit zero. For each fixed prime `p`, its sufficiently late terms belong
to `ker Per_log(p)`; that kernel is closed, so the limit belongs to it.
Cofinal prime tomography forces the entire limit source to vanish.

The positive survivor is a sharp limit classification: even arbitrary scalar
renormalization cannot produce a nonzero limit in that original source
topology. This does not assert convergence to zero or boundedness of the
family; it classifies limits if they exist.

Fix one actual Xi coordinate `rho` and normalize each source by
`M(h_n)(rho)^(-1)`. C38 proves every denominator nonzero. The literal
reading is exactly one at every finite stage. Its continuity in the original
Meyer topology excludes convergence, because the only possible source limit
is zero. The functional is constructed by the exact Fourier bridge below.
No stronger half-density norm or unproved topology identification is used.

## Corpus anchors already read

- `DeningerCircleSeparating.lean`: `deningerPeriodizationLM_isClosed_ker`.
- `DeningerTomographyProduct.lean`: `deningerPeriodizationLM_eq_zero_iff`;
  whole prime tomography infrastructure.
- `DeningerTomographyInjective.lean`: `deningerCofinalPrimeTomography`.
- `DeningerFinitePrimeGreenDomainXiJets.lean`: actual paired source in every
  selected original Green domain and its nonzero Xi evaluation.
- `DeningerMeyerSeminorm.lean`: literal weight `exp(A*|t|)` times the norm
  of the original derivative.
- `DeningerMeyerStrongLogMellinContinuity.lean`: evaluation continuity in
  the separate explicit strong-log topology.

A 150-second deep/method search inspected all 20 candidates and 20 source
arguments, including periodization continuity and source topology. Generation
874732; semantic coverage 2352649/2353293; partial because of deadline,
filter/judge and source refresh. No hypothesis supplied by a generated
ingredient group was adopted. The C40 scratch subsequently verified the exact original-Meyer bridge
and source-limit statements below.


## Exact original-Meyer continuity

The verified bridge is `deningerExpMulSchwartzLM_continuous(sigma)` maps the ORIGINAL
Meyer source continuously to the Schwartz function `t -> exp(sigma*t)h(t)`.
Compose with the Schwartz Fourier transform and evaluation at
`-Im(s)/(2*pi)`. Expanding the Fourier kernel identifies this continuous
linear functional exactly with `M(h)(s)` for every complex `s`. This avoids
any identification of the separate strong-log topology and preserves the
original source function and exact Fourier normalization. Lean verifies both this literal equality and the closed-kernel limit argument.


## Stronger survivor forced by the limit proof

Coefficient-preserving sources escape every compact subset of the original
Meyer space. If a compact set contained infinitely many terms, first
countability and compactness would give a convergent subsequence. The prime
lists remain cofinal along every increasing subsequence; the zero-limit
classification and fixed Xi evaluation one contradict that convergence.
Thus the result is an actual compact-escape law, not only failure to converge
along one chosen sequence.

The physical coefficient is retained during this escape. C39 gives the
physical image `A_P(rho)*oldImage(q)`, whereas the scalar used to normalize
the source is `1/[A_P(rho)*oldGaussianGrade(q)]`. Consequently every finite
normalized prime/depth chain has exactly
`oldGaussianGrade(q)^(-1)*oldImage(q)` as its fixed Sonin operator image.
Both cancellations are justified by nonvanishing theorems. This does not
prove that the retained image vanishes; it identifies precisely the source
escape that any infinite-domain comparison must account for.


## Research and novelty checks

Four 150-second deep/method searches inspected all 20 candidate lemmas and
20 source arguments in each report, plus generated ingredients and coverage.
All were partial; no missing-result claim is treated as exhaustive.

| Mechanism | Generation | Semantic ready/expected |
|---|---:|---:|
| original Meyer Mellin continuity | 874781 | 2352738/2353405 |
| closed kernel / compact subsequence method | 874796 | 2352770/2353445 |
| Fourier weighting / tightness | 874828 | 2352929/2353562 |
| damped paired Euler residual | 874835 | 2352929/2353624 |

Actual source checks supply the weighted Schwartz continuity, closed
periodization kernels and literal source-to-reader formulas. Broad arXiv
queries used compactness, condensation, boundary, escape and tightness,
including June–September 2026 filters. They returned no applicable recent
paper; direct arXiv search pages failed to fetch. Older results were not
represented as recent.

[Dörfler–Feichtinger–Gröchenig, Compactness Criteria in Function Spaces](https://arxiv.org/pdf/math/0201161),
Theorem 2 and its proof, characterize compactness of closed bounded L2
families by tightness of the short-time Fourier transform. The proof splits
compact-region convergence from the uniformly controlled tail. This suggests
investigating which weighted source components escape. It does not imply
compactness in the stronger Meyer topology and is not a Lean premise.

## Exact boundary of the result

The explicit family uses all original primes up to the cutoff, normalizes
one literal Xi evaluation and keeps every prime/depth label in its physical
transport. General cofinal lists also retain repetitions. No premise assumes
RH, a critical-line root, source balance or a reader identity.
The compact-escape theorem applies to the original Meyer topology, not to
all weaker distribution topologies. It covers exact prime-kernel sources;
Abel-damped sources require control of their actual periodization residual.
The fixed normalized physical image is retained, not proved zero.

## Verification

Scratch: `/tmp/route_l_cofinal_c40.lean`. The final clean 12-theorem proof
passed `lake env lean` with no errors or warnings. The new module is
`formal/GaloisForLFunctions/RHTower/DeningerCofinalPrimeMeyerEscape.lean`
(201 lines, 12 theorems, three definitions), with exactly one umbrella import.
Targeted leaf audit passed: only the new leaf was built (193 seconds;
11942 dependency-graph jobs). Index refresh passed and the new module
appears in `LEAN_API.md`. Duplicate audit found 15 declarations and zero
collisions; scratch and module are byte-identical. `git diff --check` passed.
Global lint reported one unrelated shared-tree error: the concurrently added
`ThetaCuspHawkingBMSourceDensityDual` module was not yet reachable from its
umbrella. C40 itself is wired exactly once. No umbrella build, numerical
experiment or axiom-print command was used. All C40 Lean and research
processes finished.

Next attack: [damped prime Green residual](../1-in-progress/route-l-damped-prime-green-residual.md).
