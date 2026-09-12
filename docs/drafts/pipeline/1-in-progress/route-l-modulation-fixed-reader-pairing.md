# Route L: modulation current in the fixed physical pairing

- **ID:** RH-L-C62
- **Stage:** 1-in-progress
- **Target:** Full-source fixed physical-reader agreement.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.

C61 kernel-checked the complete modulation-current integral, with the retained multiplier difference and native Xi jet. This turn tests its image in the already fixed Gamma/BV or Burnol/Sonin pairing. No ordinary Fourier evaluation, chosen cyclic functional, or vanishing lower Xi jet may replace that pairing.

## In progress

Conjecture to test: the actual complete modulation current has a source-derived transport into the fixed physical reader whose paired value closes the boundary comparison. Transport, domain admission, coefficient retention and cancellation must each be derived from the original source.

## Source correction: proved in Lean

The prime-normal source in C61 is complete for every arithmetic label `n = p + j`, but its coordinate is recentered. External modulation depends on that anchor. Write

- `L = m log p`, `h = p^(m/2)`, `E_u(x) = exp(-i u x)`;
- `R_k(x) = sum_{j>=0} rawHead(k,p+j,m,x)`;
- `Lraw_delta(x) = sum_{j>=0} E_delta(x-m log(p+j)) rawHead(k,p+j,m,x)`;
- `Craw_delta = E_delta R_k - Lraw_delta`.

These are literal source sums. The raw head is the existing source definition, with its original Möbius coefficient, translation and internal jet. No evaluation defines the source.

The exact identities are

```
Snorm_k(x) = h R_k(x+L)
Lnorm_delta(x) = h Lraw_delta(x+L)
h Craw_delta(x+L)
  = E_delta(L) Cnorm_delta(x)
    + (E_delta(L)-1) Lnorm_delta(x).
```

The last term is a complete source term, including its leading arithmetic packet. It cannot be dropped when using C61 to represent variation at the original anchor. C61's normalized identity remains correct.

Define the original arithmetic multiplier

```
A_{p,m}(u) = sum_{j>=0} LSeries.term(mu, m*(1/2+i*u), p+j).
```

Then the normalization cancels exactly, with its phase retained:

```
A_{p,m}(u) = h^(-1) E_u(L) M_{p,m}(u).
```

For `w = v + delta`, the complete admitted integrals are

```
integral E_v(x) Lraw_delta(x) dx = A_{p,m}(v) Xi^(k)(w)
integral E_v(x) Craw_delta(x) dx
  = (A_{p,m}(w)-A_{p,m}(v)) Xi^(k)(w).
```

The first requires `p>0`, `m!=0`, `|Im w|<1`, and `Re(1/2+i*v)>1/m`. The second also requires `Re(1/2+i*w)>1/m`. Integrability is proved, rather than relying on the default value of an unadmitted integral. Translation transfers C61's absolute admission; the source is not differentiated under an infinite sum. The internal jet order `k` is unchanged. No vanishing lower jet, RH premise, reader-equality premise or stationarity premise enters these results.

Implementation: `formal/GaloisForLFunctions/RHTower/MobiusThetaRawSourceModulation.lean`.

Public results:

- `mobiusThetaRawResidualMultiplier_eq`
- `mobiusThetaInternalJetRawResidualSource_recenter`
- `mobiusThetaRawSourceModulationCommutator_recenter`
- `mobiusThetaRawLocalModulationSource_fourierLaplace_data`
- `mobiusThetaRawSourceModulationCommutator_fourierLaplace_data`

## Physical pairing attack and remaining obligation

1. **Conjecture: the C61 current transfers unchanged to the original source reader.** The source calculation exposes the omitted anchor contribution. A transfer must transport both terms of the exact recentering identity. This rejects that shortcut, not Route L.
2. **Replacement: derive the complete raw current and its admitted arithmetic coefficient.** Proved above in Lean. This is the positive source result; it preserves every residual coefficient and its native jet.
3. **Conjecture: existing cofinal Gamma transport completes the comparison from Fourier integrability.** Applicability is not established. `DeningerGammaSixCofinalSingularGraphSoninTransport` constructs a graph `ell2 direct-sum C`; the fixed physical map is its second coordinate times the fixed Sonin receiver. Finite actual Gamma assembly agrees with this map, and the singular vector has graph trace one while its ambient projection is zero. The source identities above do not supply a coefficient-faithful map from the raw arithmetic packets into that graph, nor identify the required singular trace. Choosing the trace to be a desired Fourier value would assume the missing comparison.
4. **Burnol alternative.** The existing critical-line kernel and contour theorems provide actual L2 admission and horizontal estimates for their specified quotient source. The co-Poisson pairing uses a compact multiplicative-window seed. No equality between those inputs and the complete raw modulation source was obtained. Their admission results therefore do not establish this fixed-reader pairing.

The exact next obligation is original-source transport into the fixed Gamma/Sonin or Burnol pairing, including the anchor correction, its domain and Gamma calibration. Then its paired value must be derived at every native depth and multiplicity copy with the nonzero Xi coefficient retained. Neither the ordinary Fourier integral nor a chosen cyclic trace is that producer. Full-source reader agreement and RH remain **UNPROVED**.

## Corpus audit

Four direct whole-corpus deep searches were run, each with a 120-second request budget, `--any --no-refresh --json`:

| Saved search | Index generation | Coverage snapshot/current | Files / Lean files / declarations |
| --- | --- | --- | --- |
| `route-l-modulation-fixed-reader-search.json` | 880480 | 880489 / 880490 | 57089 / 47462 / 735680 |
| `route-l-burnol-modulation-pairing-search.json` | 880480 | 880489 / 880490 | 57089 / 47462 / 735680 |
| `route-l-raw-source-anchor-modulation-search.json` | 880490 | 880500 / 880500 | 57090 / 47463 / 735694 |
| `route-l-raw-modulation-physical-transport-search.json` | 880564 | 880584 / 880585 | 57091 / 47464 / 735713 |

All inventories report complete; all search runs report **partial** retrieval, including interrupted text/source passes. Compiler enrichment is predominantly pending/source-only. This is not evidence that a producer is absent from the corpus.

All 20 candidate statements and all 20 source arguments in each run were inspected, including assumptions and proposed groups: 80 candidates and 80 source arguments. The fourth run had no generated method descriptions; its proof excerpts and statements were inspected directly. No group was treated as a proof. The first phase-orbit group gives Fourier/unitary translation, not the physical pairing. The third half-density group combines definitions from different carriers and leaves matching their masses unresolved. The second and fourth runs returned no ingredient groups; all four returned no proof ideas. Retrieved C61 declarations were recognized as prior work, not independent confirmation.

Additional source inspection covered the raw-head and normalized residual definitions; fixed reflected BV comparison; actual Gibbs continuation; Burnol kernel factorization, L2 contour admission and co-Poisson pairing; cofinal Mobius/Gamma/Xi Sonin incidence; and the actual singular graph transport and Meyer–Tate boundary construction. The latter explicitly retains a nonzero vertical receiver and does not assert boundary annihilation.

## Broad recent-paper screen

Newest-first arXiv search used the single broad word [duality](https://arxiv.org/search/?query=duality&searchtype=all&abstracts=show&order=-announced_date_first&size=50).

- [Chen et al., *The Local Embedding Problem for Hardy Spaces of Dirichlet Series*, arXiv:2609.11560](https://arxiv.org/html/2609.11560), September 10, 2026: abstract, contents and introductory theorem discussion screened. The preprint claims local critical-line Lp bounds for Dirichlet polynomials with p>2 using duality and common-prime covariance. Such a bound is not a point-jet bound or a vanishing theorem. Applying it here would still require admission of the actual coefficient family in its Hardy norm and identification with the fixed physical reader. No result from this preprint was used in Lean; its full proof was not audited.
- [Lo Biundo–Tripaldi, *Spectral Complexes and Currents on the Engel Group*, arXiv:2609.11625](https://arxiv.org/html/2609.11625), September 10, 2026: abstract screen only. Its current-complex transport suggested checking domains before transferring a current. No source-derived map from the arithmetic/Gamma carrier to the Engel-group complex was obtained, and no theorem was imported.

These papers supplied questions to test, not mathematical premises.

## Validation

- Helper-name scratch: `lake env lean /tmp/RouteLRawModulationCheck.lean` — exit 0.
- Final scratch: `lake env lean /tmp/MobiusThetaRawSourceModulation.lean` — exit 0, no warnings. An initial cast mismatch was corrected with explicit `Nat.cast_add`; phase cancellation uses a direct exponential rewrite.
- Final named leaf: `lake build GaloisForLFunctions.RHTower.MobiusThetaRawSourceModulation` — exit 0; new leaf built in 5.1 seconds. The 9482-job dependency graph was replayed; no full or umbrella build was run.
- `scripts/formal_tools.py lint` — exit 1 for a separate concurrent module: `GaloisForLFunctions.HTGeometry.CoordinateEinsteinDiagonalCollapse` is unreachable from its theorem-area umbrella. Large-file warnings also remain. The new Route L module is not reported by lint. This is not a clean global lint result.
- Tracked whitespace check passed. New-file `git diff --no-index --check` checks emitted no whitespace diagnostics; exit 1 denotes file differences.
- All owned scratch/build processes completed; no owned Lean process remains.

No heartbeat/recursion-limit changes, computations, added axioms, or axiom-printing commands were used. The new 214-line leaf is wired into `GaloisForLFunctions.RHTower`; the existing parent chain reaches the root umbrella. No commit or push was made.

The universal `universal-law-field/STATUS.md` ledger is unchanged: its existing source-preservation, anchor, domain-admission and fixed-reader requirements already cover this result. No route-specific formula belongs in that ledger.
