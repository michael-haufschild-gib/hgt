# FZZ-P full Hermitian Riesz stability hypersurface

- **ID:** FZZ-P-HC36
- **Stage:** 3-formalized
- **Type:** THEOREM / exact four-parameter classification and no-go
- **Source:** HC1--HC3 Hermitian reporter coordinates + HC34--HC35 Riesz stability laws
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityFullHermitianRieszStabilityHypersurface`
- **Frontier map:** read-only; no edit permitted

## Frozen conjecture

Let `G_beta=[[P,Q],[Q,R]]`, `E=Q^2-PR>0`, and let `A_beta` be the canonical
source-Krein generator. For every Hermitian reporter

`H(a,b,c,d)=[[a,b+i c],[b-i c,d]]`,

its literal source-metric Riesz representative is

`B=E^-1 [[-Ra+Qb-iQc, -Rb+Qd-iRc],`

`          [ Qa-Pb+iPc,  Qb-Pd+iQc]]`.

For `M=A+B`, define

`T=(-Ra+2Qb-Pd)/E`,

`D=((b^2+c^2)-(a-PE/R)(d+E))/E`,

`Delta=T^2-4D`.

Theorem package:

1. `B` Riesz-represents `H` and `M` is formally `G_beta`-self-adjoint;
2. every eigenvalue of `M` satisfies `lambda^2-T lambda+D=0`;
3. actual spectral reality of `M` is equivalent to `Delta>=0`;
4. `Delta<0` carries an explicit nonreal neutral eigenpair;
5. source-defined reporter `(a,b,c,d)=(PE/R,0,0,-E)` is unique reporter with `M=0`;
6. this annihilating reporter lies strictly inside existing reflection-detector cone because
   `d=-E!=0` and `b^2+c^2=0<d^2`.

Items 5--6 show that even a universal RH-strength radial-reflection detector can annihilate
the canonical local generator unconditionally. Hence no spectral-stability or stationary-kernel
principle on complete local Hermitian Riesz family can supply missing FZZ/GFZZ divisor matching.

## Paper derivation

`det G=PR-Q^2=-E`, so direct inversion gives displayed `B=G^-1 H`. Moreover

`G A = diag(-PE/R,E)`.

Therefore

`G M = [[a-PE/R,b+i c],[b-i c,d+E]]`.

Taking trace after multiplication by `G^-1` gives `T`; multiplicativity of two-by-two determinant
gives

`det M = det(GM)/det G = ((b^2+c^2)-(a-PE/R)(d+E))/E=D`.

Characteristic polynomial has real coefficients. Its roots are real exactly for `Delta>=0`; for
`Delta<0`, `T/2+i sqrt(-Delta)/2` is a nonreal root and a two-case explicit kernel vector of
`M-lambda I` supplies eigenpair. Formal self-adjointness makes every nonreal eigenvector neutral.
Finally `M=0` iff `GM=0`, which forces four displayed coefficients, and cone claim follows from
`E>0`.

## Corpus audit

Mandatory searches on 2026-08-28:

- `scripts/formal_tools.py research "FZZ nonlinear Riesz feedback state dependent coupling parity stability"`
- `scripts/formal_tools.py research "FZZ Hermitian quadratic observable Riesz representative general coefficients"`
- `scripts/formal_tools.py research "FZZ full Hermitian reporter spectral stability source metric"`

Corpus contains four reporter coordinates and two-coordinate Riesz slice, but no complete
four-parameter Riesz representative, stability hypersurface, or detector-annihilator theorem.

## Literature boundary

Current primary-source search found generic pseudo-Hermitian/Krein spectral theory and FZZ
duality papers, but no source-specific four-parameter stability hypersurface or detector-annihilator
law:

- Feinberg--Riser, pseudo-Hermitian matrices and indefinite metrics, arXiv:2109.09221:
  https://arxiv.org/abs/2109.09221
- Creutzig--Hikida, higher-rank FZZ dualities, arXiv:2010.14681:
  https://arxiv.org/abs/2010.14681
- Mukherjee--Mukhi--Pakman, FZZ algebra and interacting dressings, arXiv:hep-th/0606037:
  https://arxiv.org/abs/hep-th/0606037

Generic two-by-two discriminant and Riesz inversion are standard; novelty claim is limited to
literal FZZ source synthesis and resulting route closure. Status is “no collision located,” not an
absolute priority claim.

## New route knowledge

- HC35 did not exhaust local Hermitian interactions: first-diagonal and real-cross coordinates
  enlarge its two-parameter slice to a complete four-real-dimensional Riesz chart.
- Complete actual spectrum is nevertheless controlled by one explicit real quadratic
  hypersurface `Delta=0`; negative side contains a constructed nonreal neutral eigenpair.
- Unique reporter cancelling canonical generator is
  `diag(PE/R,-E)=-G A`; uniqueness is proved from Riesz-pairing injectivity, not coefficient guess.
- This reporter lies strictly inside RH-strength reflection-detector cone, so it is simultaneously
  an exact critical-line detector and identically zero local dynamics.
- Therefore no principle using only local Hermitian Riesz stationarity, spectral reality, or kernel
  selection can derive missing global parity-Mellin matching. Surviving FZZ-P interaction must add
  nonlinear, nonlocal/infinite, singular, or genuine divisor-incidence data.

## Lean closure

Main declarations:

- `fzzCigarParityDilatedFullHermitianRieszOperator_represents`
- `fzzCigarParityDilatedFullHermitianRiesz_determinant_eq`
- `fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator_formallySelfAdjoint`
- `fzzCigarParityDilatedFullHermitianRiesz_eigenvalue_characteristic`
- `fzzCigarParityDilatedFullHermitianRieszSpectrallyReal_iff_discriminant_nonneg`
- `fzzCigarParityDilatedFullHermitianRieszInstabilityEigenpair`
- `fzzCigarParityDilatedFullHermitianRieszInstabilityEigenvector_null`
- `fzzCigarParityDilatedFullHermitianRieszPerturbedKreinOperator_all_zero_iff`
- `fzzCigarParityDilatedFullHermitianRieszAnnihilatorMellinReading_eq_reflection_iff`
- `fzzCigarParityDilatedFullHermitianRiesz_detectorAnnihilatorNoGo`

Verification on 2026-08-28:

- direct `lake env lean` passed;
- targeted `lake build GaloisForLFunctions.RHTower.FZZCigarParityFullHermitianRieszStabilityHypersurface`
  passed with 9763 jobs;
- 13 exported endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`;
- formal lint reports no finding for HC36; existing unrelated unreachable-module errors remain;
- module wired into `GaloisForLFunctions.RHTower`; no umbrella build run;
- frontier map untouched.

## Gates

- [x] 0 -> 1 in-progress: corpus-led conjecture frozen
- [x] 1 -> 2 fully-proven: dependency-closed paper derivation
- [x] 2 -> 3 formalized: unconditional Lean theorem package and audit
- [ ] 3 -> 4 publication-ready: independent specialist priority/physics audit

## Log

- 2026-08-28 — Complete four-coordinate conjecture derived from HC1--HC3 and HC35.
- 2026-08-28 — Exact hypersurface, explicit neutral mode, unique detector-annihilator, and Mellin
  pointwise detector law formalized and audited.
