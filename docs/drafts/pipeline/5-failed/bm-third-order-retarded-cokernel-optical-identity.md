# BM third-order bare retarded-cokernel optical identity

- **ID:** HB-BM3-OPT
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · HB; corrected by current Lean source and 2026-08-26 corpus audit
- **Statement:** `[FALSIFIED]` Bare imaginary part of complete gauge-fixed Einstein--Teukolsky `++-` cokernel section cannot equal positive phase-invariant radiation flux for every nonzero complex theta seed.

## Goal

Test whether unit-Wronskian left projection of complete Birmingham--Mokhtari `++-` Schur source
could itself be identified with positive horizon-plus-boundary radiation loss.

## Gates

- [x] 0 → 1 in-progress: exact normalized statement, source-pure attack, internal/external frontier audited
- [ ] 1 → 2 fully-proven: impossible; frozen statement falsified
- [ ] 2 → 3 formalized: no false statement formalized
- [ ] 3 → 4 publication-ready: retired

## Frozen claim

Let `L` be gauge-fixed linearized Einstein--Teukolsky operator on massless `d=4` topological-AdS
Birmingham--Mokhtari background. Let `p,m` be FE-reflected and Schwarz-conjugated fundamental
modes, `B,C` second and third variations, `Rpm,Rpp` retarded inverses, and `ell` a fixed
unit-Wronskian left target-QNM functional. Define

\[
S^{(3)}_{++-}
=B(p,R_{+-}B(p,m))+B(m,R_{++}(B(p,p)/2))+C(p,p,m)/2.
\]

For every nonzero complex seed `A`, frozen claim asserted

\[
\operatorname{Im}\,\ell(S^{(3)}_{++-}(A))
=\mathcal F_{\mathrm{hor}+\partial\mathrm{AdS}}(A)>0.
\]

## Internal and external frontier

- `[CORPUS]` `ThetaCuspHawkingAIMEThirdOrderSourceCohomology.lean` gives exact complete `++-` decomposition and left-cokernel invariance under exact remainders.
- `[CORPUS]` `ThetaCuspHawkingAIMECrossBranchTeukolskyResidue.lean` exhibits physical cubic amplitude law `A * normSq(A) * c`.
- `[CORPUS]` `ThetaCuspHawkingTotalThirdOrderCausalCut.lean` removes common direct third jet from retarded-minus-advanced cut.
- `[CORPUS]` `ThetaCuspHawkingBMMixedHorizonCausalOpticalProducer.lean` proves desired total-cut/optical conclusion only under mixed-response, `++`-cut, and Einstein--Green reciprocity hypotheses.
- `[CORPUS]` `ThetaCuspHawkingBMProjectiveCausalResponse.lean` warns that common Frobenius normalization poles cancel from physical projective boundary response.
- `[CORPUS]` `ThetaCuspHawkingTeukolskySemigroupTerminalValue.lean` leaves only target-co-resonant atom after contractive Cesàro evolution.
- `[LITERATURE]` audited BM linear QNM, QNM bilinear, AIME, second-order Teukolsky-source, and third-order Schwarzschild-Hamiltonian papers do not derive complete topological-AdS BM cubic optical projection.

## Hostile attack

Time-translation/U(1) charge forces every physical `++-` coefficient to have form

\[
\Sigma(A)=A|A|^2c.
\]

Hence `Sigma(-A)=-Sigma(A)`, while radiation flux obeys `F(-A)=F(A)`. If bare identity held at
both `A` and `-A`, then

\[
\operatorname{Im}\Sigma(A)=F(A)>0,
\qquad
-\operatorname{Im}\Sigma(A)=F(A)>0,
\]

contradiction. Failure precedes every BM radial normalization, counterterm, or positivity issue.

## No-go closure

- **Exact killing theorem/mechanism:** U(1) charge mismatch. Cubic `++-` section is charge-one equivariant; positive radiation flux is charge-zero invariant. Half-turn `A ↦ -A` reverses bare imaginary part and preserves flux.
- **Strongest positive survivor:** Hermitian modal work `conj(A) * Sigma(A)=|A|^4 c` is exactly U(1)-invariant. For `A ≠ 0`, `Im(conj(A) * Sigma(A))>0` iff `Im(c)>0`. This is sharp: it removes exactly one unit of cubic phase charge.
- **New insight:** Physical Einstein--Green reciprocity must pair cubic source with conjugate target amplitude, divide by seed amplitude, or explicitly phase-fix target mode. Corpus hypothesis `ell(B p u)=normSq(projection)` hides this normalization and cannot be discharged with a seed-independent bare `ell`.
- **Status:** `[FALSIFIED] [POSITIVE SURVIVOR PAPER-PROVED] [POSITIVE SURVIVOR LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]`. Formalized in `ThetaCuspHawkingCubicPhaseCovarianceOpticalNoGo.lean`; targeted build, axiom audit, and formal lint pass.

## Log

- 2026-08-26 — created in Stage 1 after corpus and current primary-literature audit.
- 2026-08-27 — hostile U(1) attack falsified frozen claim; phase-invariant modal-work survivor proved and formalized; route retired.
