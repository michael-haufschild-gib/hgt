# Route L: arithmetic current in the fixed singular trace

- **ID:** RH-L-C63
- **Stage:** 1-in-progress
- **Target:** Full-source fixed physical-reader agreement.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.

C62 verified the original-anchor correction and the admitted transform `(A(w)-A(v)) Xi^(k)(w)` of the complete raw modulation current. The source's original arithmetic labels and native internal jet remain intact. Its ordinary Fourier reader does not yet identify its fixed Gamma/BV value.

## Tested attack

Test whether the actual arithmetic coefficients, together with their native prime/depth incidence, determine a map into the existing Gamma singular graph and its trace. A chosen graph coordinate cannot supply the comparison. Also test whether the original anchor correction is the modular correction required by the fixed physical trace, using the existing paracyclic source differential rather than replacing the boundary by a new one.

## Source identity proved in Lean

Let `s(v)=1/2+i*v`, `a_n(v)=mu(n)n^(-m*s(v))`, and `g_d(s)=exp((2 Re s-1)log d)`, the existing Deninger mate gain. Directly retaining the original translation gives

```
exp(-i*(conj(v)-v)*m*log n) = g_{n^m}(s(v))
a_n(conj(v)) = g_{n^m}(s(v)) a_n(v).
```

Consequently, C62's raw current at reflection has the admitted integral

```
sum_{n>=p} (g_{n^m}(s(v))-1) a_n(v) Xi^(k)(conj(v)).
```

Each summand is the existing canonical cofinal-relative readout of the literal ordinary-prime cycle atom, weighted by `a_n(v)`, at degree `n^m`. The Tate quotient stage remains an independent parameter. This does not place the arithmetic index in the cofinal-depth coordinate or define a desired graph trace.

The candidate agreement is with these degree-labelled cofinal readouts. It is not yet the fixed degree-six physical reader. Replacing `g_{n^m}` by `g_6` leaves the complete correction

```
sum_{n>=p} (g_{n^m}(s(v))-g_6(s(v))) a_n(v) Xi^(k)(conj(v)).
```

Both reflected coefficient families must be absolutely admitted before summing. This correction, and its actual Gamma/BV transport, remain required. It cannot be declared zero by choosing a graph coordinate.


The exact complete correction is now also proved:

```
sum_{n>=p} (nativeReadout(n^m) - fixedReadout(d))
  = (A_{p,m}(conj(v)) - g_d(s(v))*A_{p,m}(v)) Xi^(k)(conj(v)).
```

Both the native readout series and this difference series are absolutely summable. The original raw-current integral is integrable and equals the complete native readout sum. The domains remain `m!=0`, `Re s(v)>1/m`, `Re s(conj(v))>1/m`; the integral also requires `|Im conj(v)|<1`. The selected prime `p` is unchanged, every label `n=p+j` is retained, and internal jet order `k` remains arbitrary. Thus the theorem can be specialized at native nonzero Xi jets without replacing them by vanishing lower derivatives.

Implementation: `formal/GaloisForLFunctions/RHTower/MobiusThetaRawReflectionCofinalReadout.lean`.

The proof starts with the existing raw coefficient/translation theorem, proves the exact reflection phase, applies the existing canonical cofinal-relative readout to the weighted literal ordinary-prime cycle, and then sums the reflected and original absolutely admitted coefficient families. The arithmetic cycle has trace one by an existing source theorem; no new trace or graph coordinate is chosen. The arithmetic label `n`, power depth `m`, and Tate quotient stage `r` remain separate.

Public results:

- `mobiusThetaRawReflectionPhase_eq_mateGain`
- `mobiusThetaPrimeRawAmplitude_star`
- `mobiusThetaRawCofinalReadout_nativeDegree_eq`
- `mobiusThetaRawCofinalReadout_nativeDegree_data`
- `mobiusThetaRawReflectionCurrent_eq_tsum_cofinalReadout`
- `mobiusThetaRawCofinalReadout_fixedDegreeCorrection_data`

## What the attempts settle

1. **Direct arithmetic labels into the cofinal singular graph.** Not established. The existing graph coordinate indexes cofinal Tate stages, whereas the complete raw source has arithmetic labels at a fixed native depth. Assigning those labels to graph basis indices would not derive the required native incidence. No such map was added.
2. **Modular phase matching.** Proved exactly, but the degree is `n^m`. The fixed degree-six gain cannot replace it termwise. The positive result is the admitted complete native readout and its explicit correction to any fixed degree.
3. **Weighted cyclicity or a total derivative.** Neither erases the correction. The existing modular-trace identity retains `(sigma(y)-y)*x`; the previously formalized ordinary-integer Gibbs exchange law retains its mate gain. The new sum theorem supplies the concrete complete coefficient to be compared, not a reason for its zero value.
4. **Boundary-square cancellation.** A second boundary can vanish while a first boundary remains visible. Existing source/Gamma natural-reporter results still require naturality on the original selected boundaries; their structures do not supply that premise.

At `d=6`, the fixed cofinal readout carries `g_6-1`. It is not by itself the normalized BV scalar. The existing physical Gibbs continuation carries `(g_6-1)/(6*g_6)`, and the reflected BV boundary carries `g_6-g_6^(-1)`. These calibration and orientation factors remain part of the actual physical comparison. This turn does not assert that the new correction is the sole missing term of that comparison.

**Next mathematical target:** derive the image of the complete correction in the original Gamma/BV pairing, together with the original horizontal boundary, and establish their required cancellation. Neither deleting the correction nor fitting a singular trace to the Fourier value is a producer. Full-source fixed-reader agreement and RH remain **UNPROVED**.

## Whole-corpus search audit

Four direct deep searches used `--any --budget-seconds 120 --no-refresh --json`:

| Search file | Index generation | Coverage snapshot/current | Files / Lean files / declarations |
| --- | --- | --- | --- |
| `route-l-arithmetic-singular-trace-search.json` | 880693 | 880709 / 880709 | 57099 / 47470 / 735772 |
| `route-l-modular-raw-current-method-search.json` | 880700 | 880709 / 880709 | 57099 / 47470 / 735772 |
| `route-l-reflection-cofinal-coefficients-search.json` | 880742 | 880749 / 880750 | 57100 / 47471 / 735785 |
| `route-l-fixed-degree-reflection-correction-search.json` | 880808 | 880815 / 880816 | 57100 / 47471 / 735788 |

All 80 candidate statements and 80 source-method arguments were inspected, including their assumptions. All four runs were partial; text/source retrieval was interrupted and some ranking/query stages remained unfinished. Inventory coverage was complete, compiler enrichment predominantly pending/source-only. Partial retrieval is not proof that a producer is absent.

All four runs returned zero proof ideas. The first returned no ingredient groups. The second's group repackages the already known ordinary/corner trace distinction, leaving product matching unresolved. The third combines weighted-sum identities with a defined reflection multiplier on a different carrier. The fourth pairs scalar reflection-parameter bounds with unrelated correction estimates. None is a verified full-source physical comparison.

Source inspection additionally checked the existing raw amplitude and centered-coordinate definitions; cofinal relative quotient and native source landing; ordinary-prime cyclic atom and trace; the completed Hellinger/Gamma local incidence bridge; source/Gamma shared-ghost naturality structure; and the earlier C16 ordinary-integer Gibbs operator-domain proof. In particular, the local incidence bridge uses the nonzero source coefficient on a canonical incidence vector and explicitly leaves global graph separation open. The shared-ghost structure contains source naturality as a premise, so it cannot be used to produce that naturality.

## Broad recent-paper tests

The newest-first single-word arXiv search was `transgression`. Web search-page fetches failed with cache misses; a direct bounded `curl` fetch succeeded. Search results from June–September 2026 included higher anomalies, higher Chern–Simons theory, Goldstone dynamics, ordinary-corner AKSZ descent, fluid anomaly inflow, and shifted contact structures. The following two primary papers were inspected beyond the abstract:

- [Anghel, *AKSZ Descent on Manifolds with Ordinary Corners*, arXiv:2608.02928v1](https://arxiv.org/html/2608.02928v1), posted August 3, 2026: introductory theorem, standing mapping-space hypothesis, and face-descent statements inspected. The proposed mechanism uses compatible restrictions and signed face incidence. It requires the relevant integration/Stokes operations; it does not supply them for the arithmetic singular graph. Its twice-iterated defect cancellation does not establish vanishing of the selected first boundary. No paper theorem was imported into Lean.
- [Zheng–Huang, *Schwinger–Keldysh effective field theory of type-B Goldstone*, arXiv:2608.09776v2](https://arxiv.org/html/2608.09776v2), August 15, 2026: introduction, stated limitations and Appendix B inspected. Version 1 was already screened in C16; this is not counted as a new mechanism. The exact interpolation formula retains endpoint contractions. Its reduction to a total derivative assumes local Hamiltonian exactness and retains a boundary term. No corresponding exactness or endpoint cancellation was derived for the original Gamma/BV source, and no paper result was used in Lean.

These are limited applicability audits, not reviews of the entire papers or proofs of their claims.

## Validation

- Helper-name scratch: `lake env lean /tmp/RouteLReflectionReadoutCheck.lean` — exit 0.
- Final scratch: `lake env lean /tmp/MobiusThetaRawReflectionCofinalReadout.lean` — exit 0, no warnings. An initial sum-scope error was corrected by explicitly parenthesizing the difference inside the infinite sum; `autoImplicit false` prevents accidental free parameters. An unused simplification argument was removed.
- Final audit: `lake build GaloisForLFunctions.RHTower.MobiusThetaRawReflectionCofinalReadout` — exit 0. Only the new leaf was built, in 5.3 seconds; the 11245-job dependency graph was replayed. No full or umbrella build was run.
- `scripts/formal_tools.py lint` — exit 0, `formal lint passed`; existing large-file warnings remain.
- Tracked whitespace check passed. New-file checks emitted no whitespace diagnostics; their `git diff --no-index` exit 1 denotes file differences.
- New 156-line leaf is wired into `GaloisForLFunctions.RHTower`, with the existing `MainTheorems` and root umbrella chain verified.
- Every owned scratch, search and build process completed. No owned Lean process remains. No commit or push was made.

No heartbeat/recursion-limit increases, computations, added axioms or axiom-printing commands were used.

The universal `universal-law-field/STATUS.md` ledger is unchanged: its existing source-preservation, original-reader and complete-admission requirements cover this result. The degree-labelled formulas are route-specific and do not belong there.
