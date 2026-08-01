# Route E literal OPEN-SOURCE-001 pursuit (2026-08-01)

Status: OPEN. Do not reuse the earlier false “terminal closure” framing as Route E completion.

Exact hard source:
- Critical schedule (z^2x/\log z\to1).
- Need (|A_z(x)-\sum_{p>z}A_z(px)|\ll_\epsilon x^{-1/2-\epsilon}).
- Finite renewal identity and two-large-prime remainder are proved; this source implies strict-half Möbius Laplace decay and RH.
- At (T=z^2), zero-plus-one boundary coefficient equals literal Möbius coefficient for every (n\le T); Lean theorem `mobiusZero_add_oneLargePrimeCoefficient_eq_mobius_of_le_sq`.

Current surviving mechanism:
- Explicit factor-replacement graph: cross-sector (p\leftrightarrow q_1q_2q_3q_4), same-sector (q\leftrightarrow rs).
- Existential low-defect matching alone is source repackaging.
- New exact fractional-flow reduction: symmetric conductance on parity-flipping edges cancels signed row mass; signed Gibbs mass is bounded by unused capacity.
- Canonical (c(m,n)=1_{m\sim n}\min(w(m)/d(m),w(n)/d(n))) reduces source to isolated Gibbs mass plus normalized-degree edge variation.
- Lean module `MobiusBoundaryOppositeSignTransport.lean` proves Hall selection, exponential transport, fractional cancellation, generic minimum-endpoint defect, and fully canonical degree-normalized defect.
- Umbrella import already present.

Hostile audits:
- Cross p↔two-small products has logarithmic supply deficit.
- Cross four-small alone cannot cover zero/one sector density imbalance.
- General spectator transport cost sees (a|Q-p|), not (|Q-p|).
- At (p\asymp z,a\asymp z), required token window is polylogarithmic. Existing almost-all exact-almost-prime theorems do not control prime centers or spectator exclusions.
- For (a=1), extracting Matomäki–Teräväinen’s all-interval E3 factor ranges at (p/2) gives a squarefree four-small (Q) with (|Q-p|\ll z(\log z)^{1.55}); prime-only atoms are pointwise non-isolated. This does not give capacity balance.

Current named hard lemma:
`SPECTATOR-COPRIME-E3-ALL-INTERVAL`: uniformly (a\le z^2/p), find enough coprime four-small replacements with (a|Q-p|\le z^{1+o(1)}), then prove combined cross/same-sector canonical defect (O_\epsilon(x^{-1/2-\epsilon})). Still unproved.

Files modified:
- `docs/drafts/pipeline/1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`
- `formal/GaloisForLFunctions/RHTower/MobiusExponentialGibbsBoundary.lean`
- `formal/GaloisForLFunctions/RHTower/MobiusBoundaryOppositeSignTransport.lean`
- `formal/GaloisForLFunctions/RHTower.lean`

Lean discipline: direct `lake env lean <file>` passed for the two edited source modules. No full build. Targeted build only when missing olean.