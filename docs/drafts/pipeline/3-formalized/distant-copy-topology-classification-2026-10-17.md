# Distant-copy amplitudes, compactness and polar continuity

- **ID:** distant-copy-topology-classification-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** Infinite-Grid Tail Rigidity Beyond Trap 5; general signed correlations.
- **Status:** Certified package 12 of 100; counted once.
- **Paper:** `docs/reports/BiScaleUncertainty/DistantCopyTopologyClassification.md`
- **Guide:** `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (read-only).

## Exact classification

For actual compact C² positive-mass f with correlation radius D>0 and T>D,
let g=f-a f(.-T), H=h_f/h_f(0), and b=a/(1+a²). Then

    H_g(x)-H(x)=-b(H(x-T)+H(x+T)),
    ||H_g-H||_infinity=|b|, H_g(T)=-b, |b|<=1/2.

For T_n>=D+1 tending to infinity, arbitrary amplitudes share one explicit
energy ceiling and E(g_n)->E(f). Local correlations eventually equal H on every
fixed window. Global uniform correlation convergence, compact correlation closure,
and uniform signed-grid tail decay each hold exactly when b_n->0.

The normalized polar density is integrable and its actual integral satisfies

    P(g)=(1-2b cosh(T/2))P(f).

If P(f)!=0, polar continuity holds exactly when b_n cosh(T_n/2)->0. The concrete
nonnegative smooth bump construction supplies positive mass and positive P(f).

## No-go closure and positive survivors

- **Pointwise sampling obstruction:** Actual smooth unit-amplitude copies have
  eventually zero samples at each fixed logarithmic node and convergent energy,
  but their global correlations are not relatively compact.
- **Polar obstruction:** Actual smooth polar-attenuated copies have zero polar
  moment and converge both globally in correlation and in energy to a seed with
  positive polar moment. Their correlation closure is compact and their signed
  grid traces decay uniformly. Exact full-grid blindness is not asserted.
- **Strongest positive survivors:** The exact unweighted mixing criterion for
  correlation compactness and exact weighted mixing criterion for polar continuity.
  Both have dependency-closed paper proofs and exact Lean certificates.
- **New insight:** Uniform trace control and energy convergence do not supply the
  exponentially weighted control required by the polar functional.

## Gates and certificates

- [x] Corpus audit: deep discovery completed in 64.92 seconds; source-only candidates.
  Lexical fallback and direct reads verified the actual source moment multipliers,
  correlation expansion, translated energy envelope and full-line cosh product.
- [x] Dependency-closed paper proof preceded new Lean code; actual witnesses audited.
- [x] Five direct `lake --old env lean` leaves pass without diagnostics:
  `DistantCopyCorrelationTopology`, `DistantCopyEnergyTopology`,
  `DistantCopyPolarTopology`, `DistantCopyCompactness`, `DistantCopySharpness`.
- [x] All 43 public declarations (35 theorems, 8 definitions) axiom-audited:
  only `propext`, `Classical.choice`, `Quot.sound`. Private seed helper covered
  transitively. Scratch: `/tmp/distant_copy_topology_axioms.lean`.
- [x] All five umbrella imports and all 43 API name/module pairs verified;
  index refresh passed. No umbrella build ran.
- [x] Formal lint run; no owned error. Global gate remains blocked by five foreign
  unwired modules: `CausalExponentialResponseAndLaplaceEnergy`, `FiniteGridRunLength`,
  `FoldFreeKernelGramAndFranelGcdCancellation`, `RealizedCoherentCancellation`,
  `SuccessorSequenceHilbert`. Repository-wide green is not claimed.
- [x] Ledger and parent card updated to 12 certified connected packages.

Leaf logs: `/tmp/distant-copy-{correlation,energy,polar,compactness,sharpness}-leaf.log`.
Audit logs: `/tmp/distant-copy-topology-{axioms,index,lint}.log`.
Corpus logs: `/tmp/distant-copy-topology-research.txt`,
`/tmp/distant-copy-polar-lexical.txt`, `/tmp/distant-copy-moment-lexical.txt`.
No exhaustive external priority claim. Existing copy algebra and moment products
are reused inputs, not additional counted contributions.

## Next frontier

Growing finite trains may have vanishing normalized active coefficients through
mass diffusion over many comparable packets. Candidate and corpus evidence:
`../1-in-progress/finite-train-topology-and-diffuse-escape-2026-10-17.md`.
The sqrt(n)-weighted polar-copy sample defect is already in package 1.
