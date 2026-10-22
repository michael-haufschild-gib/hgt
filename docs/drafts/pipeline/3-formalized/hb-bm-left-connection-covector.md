# BM canonical left connection covectors

- **ID:** HB-BM-LCC
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `HB-BM3-PPC` conjugate-frequency endpoint and left-normalization open core
- **Statement:** `[LEAN-PROVED] [NEW] [BRIDGE]` On every Xi fibre, inverse rows of exact BM horizon-to-AdS connection matrix are canonical unit-normalized left covectors; every outer coefficient vector has unique horizon coordinates, and AdS boundary symplectic concomitant is exactly `-lambda` times alternating determinant of those coordinates.

## Goal

Remove radial left-functional normalization ambiguity from augmented Peierls incidence. Freeze
remaining problem as time-oriented source incidence, not arbitrary choice of a left QNM covector.

This does not prove RH and does not construct global retarded/advanced Einstein propagator.

## Gates

- [x] 0 → 1 in-progress: conjecture frozen from exact nonzero connection determinant
- [x] 1 → 2 fully-proven: dependency-closed algebraic proof and hostile audit
- [x] 2 → 3 formalized: exact Lean theorem, targeted build, umbrella wiring, axiom audit
- [ ] 3 → 4 publication-ready: external priority review beyond corpus-specific specialization

## Exact frozen claim

On Xi fibre `q`, write exact connection matrix

`M = [[A_R,A_C],[B_R,B_C]]`

with `D = A_R B_C - B_R A_C = -2 lambda != 0`. For arbitrary AdS outer data
`u=(s,r)`, define

`ell_R(u) = (s B_C-r A_C)/D`,

`ell_C(u) = (A_R r-B_R s)/D`.

Then

- `ell_R(R)=1`, `ell_R(C)=0`, `ell_C(R)=0`, `ell_C(C)=1`;
- every `u` has unique decomposition `u=ell_R(u)R+ell_C(u)C`;
- for `++` outer vector `u` and Schwarz `--` vector `v`, with holomorphic partner
  `v_hol=(conj(v.source),conj(v.response))`,

`J_AdS(u,v) = -lambda * (ell_R(u) ell_C(v_hol)-ell_C(u) ell_R(v_hol))`.

All statements quantify over arbitrary coefficient vectors and require no theorem premise after Xi
specialization.

## Complete paper proof

Exact corpus connection determinant gives `D=-2 lambda` and `D != 0` on every Xi fibre. Direct
matrix multiplication proves two inverse-row normalization laws. Cramer's rule then reconstructs
both source and response coordinates. If two coordinate pairs reconstructed same vector, subtract
their two equations. Multiplication by `B_C,-A_C` isolates first difference times `D`; multiplication
by `-B_R,A_R` isolates second. Nonzero `D` forces both differences to vanish, proving uniqueness.

For vectors `u=M x`, `v_hol=M y`, determinant covariance in dimension two gives

`u_source v_response-u_response v_source = D (x_R y_C-x_C y_R)`.

Corpus boundary concomitant is half left side. Substituting `D=-2 lambda` yields exact transport
law.

## Hostile review and priority verdict

- No inverse or nonzero determinant is assumed: Xi-fibre nondegeneracy is already premise-free.
- Conjugation is applied only converting Schwarz `--` outer data to holomorphic partner; resulting
  determinant matches exact corpus concomitant convention.
- Result does not rename covectors as full augmented left QNM states. They are exact radial
  connection covectors. Gauge, constraint, corner, and time-support components remain open.
- Inverse-matrix and two-dimensional symplectic covariance mechanisms are classical linear
  algebra. Exact BM hypergeometric connection specialization and its use to remove Peierls
  left-normalization ambiguity were not found in corpus or audited primary HB/Peierls literature.

Verdict: `[NEW] [BRIDGE] [PAPER-PROVED] [LEAN-PROVED]`; external priority provisional. Scientific
significance is precise proof-burden reduction, not a standalone RH proof.

## No-go closure

- **Killed ambiguity:** no free radial left normalization remains on Xi fibres.
- **Strongest positive survivor:** unique canonical pair `(ell_R,ell_C)` and exact alternating
  determinant formula.
- **New insight:** actual Peierls incidence must prove literal augmented source maps acquire these
  canonical horizon coordinates. Any different radial left functional contradicts uniqueness.
- **Remaining core:** construct one boundary-stationary global retarded/advanced propagator and
  prove its augmented source projections equal canonical coordinate determinant, including
  time-support and counterterm reciprocity; then prove pre-specialization FE-odd source covariance.

## Lean formalization

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSecondHarmonicLeftConnectionCovector.lean`
- Canonical covectors:
  `d4BMXiPlusPlusRegularLeftConnectionCovector`,
  `d4BMXiPlusPlusComplementaryLeftConnectionCovector`
- Unique decomposition: `d4BMXi_existsUnique_plusPlusHorizonCoordinates`
- Symplectic transport:
  `d4BMXiAdSBoundaryPolarizedConcomitant_eq_horizonCoordinates`
- Direct `lake env lean` check passed.
- Targeted build
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicLeftConnectionCovector`
  passed (`11161/11161`).
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.
- Formal lint currently blocked by two unrelated concurrent sieve modules not yet wired into
  umbrella: `Sieve.MatomakiTeravainenC3PaperScale`, `Sieve.PrimeWindowRelaxedPaperScale`.

## Log

- 2026-08-27 — conjectured from corpus exact connection determinant after same-frequency and
  same-projective-response no-gos were found already closed.
- 2026-08-27 — paper proof and Lean formalization completed; radial left-normalization sub-burden
  removed.
