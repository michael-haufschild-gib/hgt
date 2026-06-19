# The Manifest — Census of the Wall

**The official register of what is inside the wall (NATIVE) and what is not.** Every draft and Lean module is
graded by the Door (`00-charter-wall-and-door.md`, Part III). The grade is the verdict; the one-liner is the
Door justification (almost always Door-2: *strip the new vocabulary — does a parent still prove it?*).

*Confidence: **[C]** = graded from a full read or from the repo's authoritative per-file description
(`docs/architecture.md`) where Door-2 is unambiguous; **[T]** = tentative, graded from title/role, to be
confirmed when its grade-banner is added in the pruning pass. No grade is fabricated; tentatives are marked.*

Grades: **NATIVE** (through the door) · **CONJECTURE** (native aim, unproven) · **BRIDGE** (doorway, P5 border)
· **IMPORT** (classical, formalized/reframed — fails Door-2) · **EMBASSY** (metaphor, not mathematics) ·
**META** (index/vision/charter).

---

## Headline result (read this first)

After applying the Door to the whole body:

> **NATIVE (proven, irreducible) items: 0.** No draft and no Lean module proves a theorem that survives Door-2
> — i.e. that a parent discipline could not prove with the multi-`q` vocabulary stripped out. This is the C5
> gap of the charter (Part IV), now confirmed item-by-item.
>
> **The field's genuine content is:** native **definitions** (the multi-`q` module, corank, difference-trdeg),
> native **conjectures** (difference Siegel–Shidlovsky and its scaffolding), and a set of **BRIDGE** items at
> the single-prime / finite borders. Everything else is **IMPORT** (classical mathematics reframed) or
> **EMBASSY** (metaphor). The Lean ledger is, by the Door, an **Imports Annex**: elementary classical facts,
> honestly machine-checked, but not native theorems.

This is the measurement the cleanup exists to make visible. It is not a verdict that the work is worthless —
imports and bridges and even embassies have their uses — but it is the verdict that **the wall currently
encloses no proven native theorem**, and that earning one (task: "the decades") is the whole game.

---

## A. Lean modules (`formal/GaloisForLFunctions/`) — graded [C] from `docs/architecture.md`

The Lean tree is Tier-A by design (the charter's P5/elementary border). By Door-2 it is the **Imports Annex**:
classical facts, formalized. Grades below.

| Module | What it proves | Door-2 (parent that proves it) | Grade |
|---|---|---|---|
| Core | σ-involution, cpow critical-line, ℚ-LI of {log p} | complex analysis + FTA | IMPORT (foundation stone) |
| OrbitFreeness | additive corollaries of ℚ-LI | FTA | IMPORT |
| EulerProduct | Euler product ⟺ Bohr factorization; mod-5 fake | classical Dirichlet-series theory | IMPORT (the firewall) |
| MultiQDifference | first-order `q`-difference eqn of one Euler factor | single-`q`/elementary (Door-4 fails: one base) | **BRIDGE** (single-prime border) |
| Resonance | resonance lattices; prime-log annihilator Λ=0 | FTA + linear algebra | BRIDGE (corank defined, classical content) |
| FlatConnection | cocycle/curvature, finite integrability, co-extension flatness | classical flat-connection/Frobenius (finite) | **BRIDGE** (multi-op structure, finite) |
| DSSDeterminant | nontrivial kernel ⟺ det = 0 | linear algebra | CONJECTURE-scaffold (DSS) |
| MultiplicityEstimate | auxiliary-vanishing determinant for `N^{z_j}` | Siegel-lemma / linear algebra | CONJECTURE-scaffold (DSS) |
| SpectrumGenericity | DSS spectral-genericity skeleton | linear algebra | CONJECTURE-scaffold [T] |
| RankOneCohomology | rank-one cocycles/coboundaries/Picard quotient | group cohomology (rank-one difference) | BRIDGE |
| KoszulCohomology | Koszul differentials + Euler-characteristic count | homological algebra | IMPORT |
| EHKoszulDuality | Euler–Koszul duality skeleton | homological algebra | IMPORT [T] |
| HolonomyAbelian | holonomy type / abelian case | holonomy is native invariant; content classical | BRIDGE [T] |
| difference-galois-cohomology (module/draft) | H¹ of rank-one difference modules | classical difference cohomology | BRIDGE |
| SecularMoments / SecularNewton / MultisetNewton / MomentReconstruction | Newton identities, power sums ↔ elementary symm. | classical symmetric-function theory | IMPORT |
| SpectralTorelli / PowerSumTorelli | finite power-sum/poly faithfulness, Vieta | classical algebra | IMPORT |
| SmoothNumbers | prime-exponent ↔ smooth-frequency bijection | FTA | IMPORT |
| DiagonalCharacter | Bohr characters = Dirichlet monomials | classical Bohr/harmonic analysis | IMPORT |
| BoundaryModulus | Re=½ unit-norm criterion | classical complex analysis (Lemma 1) | IMPORT |
| SatakeTensor / SatakeInterval / ExteriorSatake / LocalFactorDuality / CompleteHomogeneous / AdamsOperations / SymPowerPlethysm / SatakeReality / SatakeSymPower | Satake / λ-ring / symmetric-function identities | classical representation theory | IMPORT |
| WCoordinate / ArakelovW / SigmaOrbit / BerryKeating | coordinate identities, FE involution, `s(1−s)` | classical complex analysis | IMPORT |
| CarrierPickKernel / CarrierCauchy / SecularHankel / KreinLangerInertia / MeasureCarrier / CayleySchur / FECarrier | Pick/Herglotz/Hankel/Krein–Langer/de Branges/Cauchy | classical moment & complex-analysis theory | IMPORT |
| MultiplierScaling | real substitution preserves real-rootedness | classical | IMPORT |
| OscillatorAlgebra | `[X,Y]=−4H` etc. | Lie algebra | IMPORT |
| ExteriorParity / FunctionalEquationParity | parity bookkeeping | classical | IMPORT |
| SuperzetaResolvent | superzeta resolvent identities | classical analysis | IMPORT [T] |
| ArchimedeanLane | archimedean wing structure | archimedean analysis | IMPORT/BRIDGE [T] |
| FieldConjectures | statement-level DSS/realization Props | — (statements only) | CONJECTURE (native) |

**Lean tally (Door verdict):** NATIVE 0 · BRIDGE ~5 · CONJECTURE-scaffold ~4 · IMPORT ~35. The Lean ledger is
an honest **Imports Annex** with a few BRIDGE stones at the single-prime/finite border. No native theorem.

## B. Drafts — graded ([C] read / authoritative, [T] tentative pending banner-pass)

| Draft | Role | Door verdict | Grade |
|---|---|---|---|
| 00-core-vision | the vision | — | META (vision) [C] |
| 00-charter-wall-and-door | this charter | — | META (charter) [C] |
| 00-manifest-wall-census | this file | — | META (census) [C] |
| 00-manuscript-outline / 00-planetary-atlas / proven-core / formalization-queue / formalization-roadmap-finite-to-apex | indices/roadmaps | — | META [C] |
| infinite-base-difference-galois-for-L-functions | the founding draft | native DEFINITIONS (P2, §18) + much IMPORT (Bohr, explicit formula) + EMBASSY (wings) | FOUNDING (mixed; re-grade internally) [C] |
| hypertranscendental_galois_field_foundations | foundations | native defs + DSS conjecture + IMPORT | FOUNDING/CONJECTURE [C] |
| hypertranscendental_galois_program | programme statement | native problem + plan | CONJECTURE/META [T] |
| multi-q-difference-galois-foundations (5526 lines) | the big foundations | §43–84 structure = largely Bohr/Kronecker + Langlands **relabeled**; native defs + conjectures interleaved | mostly IMPORT/CONJECTURE; heavy re-grade [C-partial] |
| transcendence-theory-nonholonomic-functions | District D4 | the native problem (difference S–S for non-holonomic values) | CONJECTURE (native) [T] |
| dss-multiplicity-estimate-spectral-genericity | DSS engine | difference-S–S scaffolding; proven parts classical | CONJECTURE-scaffold / BRIDGE [T] |
| dss-across-the-period-nonperiod-divide / spectral-torelli-inverse-problem / difference-galois-cohomology | DSS / cohomology | native apparatus touched; content classical | BRIDGE/CONJECTURE [T] |
| automorphic-continent-rankin-selberg-ramanujan | District D3 | Langlands reframed (Ramanujan=Deligne, etc.) | IMPORT (reframed) [T] |
| dynamics-continent-lyapunov-avila-morales-ramis | District D5 | Avila/Morales–Ramis reframed | IMPORT (reframed) [T] |
| geometric-rosetta-function-field-continent | District D6 | Deligne/Weil-II reframed; the P5 function-field border | BRIDGE (P5 border) [T] |
| secular-positivity-hierarchy (756) / rh-byproduct-secular-hankel-overdetermination / spectral-functoriality-operations-calculus / spectral-torelli-inverse-problem / superzeta-tower-resolution-B23 | secular/positivity analysis | classical moment/positivity theory reframed | IMPORT (reframed) [T] |
| arakelov-height-of-zeros / absolute-zeta-archimedean-frobenius / the-archimedean-lane / the-shoreline-and-the-archimedean-lane / edge-value-transcendence-baker-wing | archimedean/Arakelov | classical Arakelov/archimedean + Baker reframed | IMPORT/BRIDGE [T] |
| carrier-unifies-dss-and-rh-faces / prime-zero-period-comparison / period-comparison-primes-zeros-the-planet / seam-is-the-period-nonperiod-divide / moduli-prime-systems / wild-cells-B24-B27-adjudication | unification/period/seam | reframings; period comparison touches native aim | IMPORT/CONJECTURE [T] |
| speculative-proofs-grand-conjectures | speculative attacks | conjectural; mostly classical attack ideas | CONJECTURE/EMBASSY [T] |
| **arithmetic-cosmology-causality-inflaton** | this session | physics metaphor on explicit formula / dBN | **EMBASSY** [C] |
| **arithmetic-cosmology-II-pt-symmetry-horizons-time-loops** | this session | physics metaphor on PT-QM / quantum chaos | **EMBASSY** [C] |
| **time-emergence-scale-clock-wheeler-dewitt** | this session | WDW metaphor; "DeWitt pairing" = Weil form | **EMBASSY** (Brick #1 = IMPORT) [C] |
| rh-holographic-pseudorandom-boundary | the embassy (explicit) | holographic metaphor | EMBASSY [C] |

**Draft tally (Door verdict):** NATIVE 0 · FOUNDING (native defs) ~3 · CONJECTURE (native aim) ~5 · BRIDGE ~4
· IMPORT (reframed classical) ~12 · EMBASSY ~5 · META ~7. (Tentatives confirmed in the pruning pass.)

---

## C. What the census commands

1. **The Embassy is real and large.** The three cosmology drafts of this session + the holographic draft are
   EMBASSY — inspiration, not mathematics. They get the embassy banner and are excluded from any claim about
   the field's content. (They are not deleted: metaphor has seeded real questions before, and the record
   stands.)
2. **The Lean ledger is the Imports Annex.** Honest, elementary, classical-provable. It is *not* evidence of a
   new branch; it is evidence of careful formalization of classical facts plus a few border bridges.
3. **The native content is definitions + conjectures + bridges — and zero proven native theorems.** The
   manifest makes the C5 gap concrete and unhideable.
4. **The reframed "continents" (D3, D5, D6, secular hierarchy) are IMPORT-reframed**, valuable as a *map* of
   where classical results sit relative to the field's borders, but they are classical mathematics and must be
   labeled so — not cited as the field's own theorems.
5. **The only path to a NATIVE entry on this manifest is the irreducible theorem** (task "the decades"). Until
   then the wall encloses an honest, well-mapped, empty plaza — with a clearly marked construction site at its
   centre.

*Pruning (banners + relocation, reversible) executes against this manifest next. Tentative [T] grades are
confirmed by reading each draft as its banner is written.*
