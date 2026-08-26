# RH frontier map snapshot — 2026-08-26 12:30

Target: `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`

Evidence method:
- Lean working tree only; used `scripts/formal_tools.py research`.
- No cards or papers used as evidence.
- No Lean builds or computations.
- Only frontier map edited by this agent; all other dirty files belong to concurrent agents.

Current topology:
- 779 lines.
- 24 live branch labels.
- 34 candidate interface labels.
- No new live branch or candidate label justified by this delta.

Material frontier changes folded:
- Smooth AFE/Barban–Vehov: classical two-fifths scale `L=N^5, M=N^2` has normalized full base/cross/derivative limits `1,-3,113/12`; detector polynomial `1-6r+(113/12)r²=(113/12)(r-36/113)²+5/113` has positive floor. Omitted-head complementary-divisor reorientation, exact three-moment quadratic, common lower endpoint `L*max(q,r)`, uniform errors under `8M²≤L`, and exact max-endpoint Selberg continuous mains are closed. Open: normalized asymptotics of three max-endpoint forms and actual full-minus-omitted interference, plus growing sigma, cutoff, off-diagonal, detector-zero, T1 transfer.
- S6F: ordinary sixth score has exact point-plus-ray decomposition, dominant atom and stable tower bounds; actual theta fifth/sixth jets and order-6 reflected Hankel curvature are exact. Separate reciprocal-trace theorem: `normalizedPrimeArchMoment 2 < 3/10^7` excludes centered order-24 residual annulus, forces positive reciprocal-square 24th powers and moment 23 positivity. Cap reduces to five explicit first-atom enclosures. Their cellwise Taylor bounds exist; enclosures, Fock/reciprocal identification, and all-order/cofinal landing remain open. S6F stays candidate.
- HB: complete gauge-fixed causal direct/mixed/doubled BM convolution shares one target denominator and exact total shifted Schur numerator. Under numerator regularity, simple-QNM residue/inverse-Laplace excitation vanish iff total shifted angular cokernel section vanishes. Open: actual source tensors, numerator regularity/nonvanishing, complex Xi-momentum jump and reciprocity, moving horizon/residual, global law. HB stays live.
- KPG: one-sided Toeplitz symbol is real trace of explicit nonvanishing local analytic square; prescribed nonzero root fixes measurable analytic local branch; H1 product arc gluing requires only a.e. trace equality. Arithmetic trace equality, Xi occurrence, and source sign remain absent. KPG stays interface/no-go.
- AEC/SCH: algebraic coset representative can simultaneously retain Kähler vanishing and put translated point in subgroup zero locus. Mixed invariant point pullback is a group homomorphism; a vanishing point set generates a subgroup in its kernel. Missing bridge is identifying that generated subgroup with enough algebraic-coset subgroup to force quotient co-Lie vanishing. Still finite transcendence/coset rigidity, not RH route.
- Arbitrary finite functional-equation/passport gauges and elliptic-Gamma differential matroid strengthen terminal finite-data no-go.
- Generic measurable analytic germ representative is reusable plumbing only; no route consequence.

Validation:
- `git diff --check` clean.
- No conflict markers or diary markers latest/recent/newly/today/yesterday.
- Counts verified from tables.
- HEAD at audit start/end: `04fd28ed8b1b4dee74cab3d58ab7be800c2cf14f`.
