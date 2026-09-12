# RH alternatives under the strict exclusions

**Result: no qualifying triple found. The requested discovery remains unresolved.**

This search did not identify three mechanisms that are both independent of the current frontier and free of positivity, scalar sign criteria, rigidity, and spectral methods. The closest proposals fail identifiable tests below. They are not being promoted as alternatives, and this is not a theorem that qualifying alternatives cannot exist.

The task allows open research. A candidate need not already prove RH. It does need a concrete source construction, a specified missing theorem, and a chain explaining how that theorem would imply RH without an excluded step. A new name for an existing endpoint, or an unspecified connection from a general mathematical tool to zeta, is insufficient.

The [working log](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/rh-three-alternatives-working-log.md) records the evolving audit and exact source-read scope. Raw results, comparison snapshots, and search metadata are retained in this directory.

## Scope and evidence

- Ran **36 corpus searches** using `scripts/formal_tools.py research`: 20 deep and 16 lexical. Sixteen deep responses report partial retrieval; four report complete retrieval. Lexical responses do not expose the same completeness metadata. Queries, results, unfinished stages, and freshness are preserved in [search-summary.json](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/rh-alternatives-search-2026-09-12/search-summary.json).
- Screened the frontier's **25 live labels and 36 candidate labels**. The [inventory](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/rh-alternatives-search-2026-09-12/route-label-inventory.json) also records 265 terminal table entries. Read the primitive gates and shared mechanism families, then investigated the nearest relevant sources. This is mechanism screening, not a full proof audit of every long progress row.
- The initial search reported 57,250 indexed files and 739,746 declarations. Those numbers describe index scope, **not the number reviewed**. Much compiler metadata was pending/source-only; semantic completeness was not measured. Generated ingredient sets and proof ideas were treated as suggestions, never proofs.
- A final comparison found no change between the initial frontier snapshot and the checked working copy. Hashes and time are in [frontier-delta-audit.json](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/rh-alternatives-search-2026-09-12/frontier-delta-audit.json).

## Three closest mechanisms, and why they do not qualify

### 1. Scalar vertical self-recurrence of zeta

**Proposed chain.** Start with the actual Dirichlet coefficients of zeta. Construct sufficiently many shifts for which `ζ(s+iτ)` approximates `ζ(s)` uniformly on a compact set strictly inside `1/2 < Re(s) < 1`. If that compact set encloses a hypothetical zero, uniform boundary control transfers it to the shifts. Enough distinct translated zeros would contradict a sublinear zero count in a fixed strict-right strip.

This is the classical Bagchi endpoint. Its return set must have **positive lower density**, so it does not meet this task's strict exclusion of scalar sign criteria. Ordinary universality does not remove the obstruction: its admissible targets are nonvanishing. Generalized self-approximation is known for every nonzero dilation parameter `d`; the `d=0` case remains the RH criterion. These statements are set out in [Pańkowski's paper](https://arxiv.org/html/1503.06931v1).

**Corpus evidence.** [RecurrenceZeroDensity.lean](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/RecurrenceZeroDensity.lean:68) already contains this scalar mechanism. Its formal receiver assumes, for abstract real numbers,

```text
0 < T,  δ*T ≤ N,  N ≤ ε*T,  ε < δ.
```

The contradiction follows immediately. The declaration does not construct return times, prove a zeta zero-density estimate, or supply the bound `δ*T ≤ N`. Its prose describes a larger mathematical program than its formal theorem proves.

The [Bohr return theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/HTGeometry/AlmostPeriodicHull.lean:129) assumes a compact translation orbit for a bounded continuous function. The [unimodular rounding theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/HTGeometry/UnimodularRounding.lean:282) is finite-dimensional. Neither constructs the missing arithmetic self-recurrence premise.

Weakening the approximation topology also fails to supply the needed zero transfer. Falcó–Gauthier prove broad approximation-in-measure results, including positive-density versions; these do not assert compact-uniform control on a zero-enclosing boundary. The loss of that boundary control is the reason these theorems do not close the proposed chain. [Primary paper, Theorems 12–14](https://www.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=9033&what=fullteng).

**Verdict:** a known conditional endpoint with an excluded density-sign step; no qualifying new arithmetic producer found. It is distinct from operator recurrence, but removing the spectral language is insufficient.

### 2. Exact arithmetic pairing or sign-reversing involution

**Proposed chain.** Pair opposite Möbius signs by a relation defined from prime factorization. Bound the unmatched contribution sufficiently sharply, then apply the Möbius cancellation implication to RH.

**Exact overlap.** This is already Route E's source-incidence problem. The corpus proves that a row-stochastic kernel whose supported edges reverse the sign satisfies

```text
2 * Σᵢ sign(i) = Σⱼ sign(j) * (1 - columnLoad(j)).
```

Thus declaring such a kernel does not establish cancellation: the signed column defect retains the original signed sum. The specified all-strict-half-power bound on the total column defect already implies RH. See [the exact identity](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/RouteEParityColumnLoadCircularityNoGo.lean:32) and [the RH implication](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/RouteEParityColumnLoadCircularityNoGo.lean:176).

The frontier explicitly includes signed column-load, Hall/load, nested-incidence, and chronological Euler-deletion mechanisms. Relabelling these as an involution, transport, or cancellation algorithm does not create an independent route. The final all-scale scalar bound would also require scrutiny under the user's sign exclusion.

**Verdict:** not independent. This rejection concerns this proposed reformulation, not a proof that every possible combinatorial construction must fail.

### 3. Topological divisibility through analytic root towers

**Proposed chain.** Construct analytic `2^k`-th roots of the actual completed zeta function, for every `k`, on a connected zero-exclusion region. The order of a hypothetical zero would be divisible by every `2^k`, contradicting its finite positive multiplicity.

**Exact overlap and forbidden step.** The [existing theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CoherentTower.lean:119) proves precisely this, assuming an open preconnected region, analyticity, a nonzero anchor, and global analytic roots of every order `2^k`. Coherence between successive roots is not even needed for this implication.

The selection step is multiplicity rigidity: all-power divisibility forces the zero order to vanish. Root ladders and finite-root passports are already covered by the frontier. Replacing “roots” with covering lifts or divisibility data does not change that step.

**Verdict:** existing route and explicitly excluded rigidity. No independent construction of those roots was found.

## Other mechanisms screened

| Mechanism | Why it was not counted |
|---|---|
| Speiser derivative zeros / inverse-branch topology | The checked critical-line result is a scalar negative logarithmic-derivative law and is already a terminal/nonselective map entry. A global critical-point exclusion was not constructed. Exponential gauges preserve the divisor while changing the logarithmic derivative; retaining a growth passport imposes further restrictions. |
| Riemann–Siegel, Turing, Rouché, all-height certificates | Return to existing census/winding mechanisms. A finite certificate covers a finite window. No source-derived all-height certification law was found; one-root disks combined with reflection introduce uniqueness forcing. |
| Robin / Nicolas / Lagarias arithmetic bounds | Excluded directly by the user's clarification about scalar sign criteria. |
| Nyman–Beurling, Báez-Duarte, Hilbert-space approximation | Existing Hilbert/norm mechanisms; not a route outside the positivity and spectral exclusions. |
| One-ended graph coherence | Existing SEC/F10a reconstruction mechanism. No literal arithmetic-to-Xi identification found; promoting eventual reconstruction to zero exclusion also reintroduces rigidity. |
| Noetherian or well-founded descent | Search found valid abstract termination/stratification ingredients. It did not find a source-defined operation taking a hypothetical off-line zeta zero to a strictly smaller arithmetic obstruction. That missing operation cannot be replaced by the word “descent.” |
| Chevalley–Warning / polynomial method | Finite-field divisibility and finite-grid nonvanishing are present in mathlib. No integral model or specialization theorem connecting them to the actual complex zeta divisor was found. |
| Hindman / monochromatic finite-products structure | The partition-regularity ingredient is present. It supplies neither zeta self-approximation on a zero-enclosing boundary nor an arithmetic zero-exclusion operation. |
| Spectral determinants, eigenvalue or operator recurrence, scattering variants | Excluded by the user's last instruction and already represented throughout the frontier. |

The map's shared families explain the overlaps: Ward/boundary selection, Weil/paired-kernel selection, cofinal/Hankel/Sonin selection, Green/Stokes/completion descent, prime/Wold signed incidence, operator/determinant occurrence, and nonlinear scattering. Sharing a downstream implication to RH alone would not make a new source construction redundant. Here, the investigated proposals either reuse the actual existing mechanism or have no specified new source bridge.

## Verification boundaries

Two scratch Lean audits succeeded for **twelve existing declarations**, including the root-divisibility receiver, Route E identity and RH implication, Speiser sign and gauge law, bounded-clock RH equivalence, Bohr returns, finite-dimensional rounding, scalar recurrence contradiction, Chevalley–Warning, combinatorial Nullstellensatz, and Hindman partition regularity. Their reported axioms are only `propext`, `Classical.choice`, and `Quot.sound`. Commands, scratch source and exact output are in [lean-verification.md](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/rh-alternatives-search-2026-09-12/lean-verification.md).

The mathlib ingredients also exposed a retrieval limitation: conventional names and module-filtered searches returned no eligible hits even though direct file reads and Lean checks confirmed the declarations. Negative search results therefore cannot establish corpus absence.

No new Lean theorem, paper proof, or frontier route was added. Scratch checks validate names and declarations in installed compiled imports; they do not rebuild every imported source or prove the open premises. Partial retrieval and the possibility of unsearched mechanisms remain material limitations.

This is a search assessment, not a mathematical retirement of these research areas. The requested three alternatives remain unfound.
