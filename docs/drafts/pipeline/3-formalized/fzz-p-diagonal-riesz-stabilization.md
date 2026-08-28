# FZZ-P diagonal Riesz stabilization and stability-selection separation

- **ID:** FZZ-P-HC5
- **Stage:** 3-formalized
- **Type:** THEOREM / source-native stability-versus-selection classifier
- **Source:** FZZ-P-HC3 detector cone + HC4 source-metric Riesz interaction calculus
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityDiagonalRieszStabilization`
- **Statement:** The unit diagonal cone reporter has a canonical negative source-gap coupling that
  makes the local FZZ Krein spectrum real at every positive scale, while reflected equality of the
  same energy remains exactly the critical-line condition.

## Main theorem

At positive scale `beta`, write

`P=P(beta)`, `Q=P(2 beta)`, `R=P(4 beta)`, `E=Q^2-PR>0`.

For the literal source metric `G=[[P,Q],[Q,R]]`, the HC3 unit second-coordinate reporter

`D=[[0,0],[0,1]]`

has exact Riesz representative

`B_D=G^-1 D=E^-1 [[0,Q],[0,-P]]`.

The family `A_gamma=A+gamma B_D` remains formally `G`-self-adjoint and has matrix

`[[P,Q(1+gamma/E)],[-PQ/R,-P(1+gamma/E)]]`.

Its real trace, determinant, and characteristic discriminant are

- `tr(A_gamma)=-gamma P/E`;
- `det(A_gamma)=Delta_0(1+gamma/E)`;
- `disc(A_gamma)=gamma^2 P^2/E^2-4 Delta_0(1+gamma/E)`.

At the source-gap coupling

`gamma_*=-E<0`,

the second column vanishes:

`A_gamma*=[[P,0],[-PQ/R,0]]`.

Consequently

`A_gamma*^2=P A_gamma*`, `det(A_gamma*)=0`, `disc(A_gamma*)=P^2`,

and every eigenvalue is real.  The two explicit eigenpairs have eigenvalues `0` and `P`.

Independently, the generating unit diagonal energy on the centered FZZ Mellin carrier satisfies

`H_D(M(rho))=H_D(M(reflect rho)) <-> rho.re=1/2`.

Thus every positive source scale has unconditional local spectral stabilization, but reflected
energy matching remains a pointwise critical-line detector and universal divisor-mode matching
remains RH-strength.

## Paper proof

Multiplying `G` by `E^-1[[0,Q],[0,-P]]` gives `D`: the first column is zero, while the second is
`E^-1(Q^2-PR)(0,1)`.  Hence `G(u,B_Dv)=conj(u_2)v_2`, proving the Riesz identity and formal
self-adjointness.  Adding `gamma B_D` to the canonical matrix gives the displayed family.

Direct `2x2` expansion yields the trace and determinant.  Substituting them into
`tr^2-4 det` gives the discriminant formula.  At `gamma=-E`, the common factor `1+gamma/E`
vanishes because `E>0`; this gives the triangular matrix and the polynomial identity
`A^2=P A`.

If `A v=lambda v` with `v!=0`, the first coordinate shows either `v_1=0` or `lambda=P`.  In the
first case the second coordinate and `v!=0` force `lambda=0`.  Therefore every eigenvalue equals
one of the real source coefficients `0,P`.  Explicit vectors `(0,1)` and `(R,-Q)` realize both.

Finally HC3's sharp detector theorem applies to coefficients `(a,b,c,d)=(0,0,0,1)`, since
`d!=0` and `b^2+c^2<=d^2`.  This proves the critical-line equivalence without using spectral
stability or any zero-location premise.

## New route knowledge

- the same unit diagonal energy is both a cone-valued reflection detector and a canonical
  source-metric interaction;
- unlike chiral HC4 coupling, diagonal coupling can restore local spectral reality;
- stabilization needs no Mellin mode, Xi zero, or target fitting: `gamma_*=-E` is source-only;
- therefore spectral reality of a finite local FZZ block is not itself an orientation law;
- the surviving producer must force reflected energy matching, not merely a real local spectrum.

This closes local finite-block spectral stability as the missing FZZ-P selector.  It does not prove
matching on divisor modes or RH.

## Corpus audit

Mandatory searches on 2026-08-28:

- `scripts/formal_tools.py research "FZZ diagonal Hermitian reporter Riesz interaction Krein stabilization triangular source gap"`
- `scripts/formal_tools.py research "FZZ parity unit diagonal G inverse perturbation real spectrum critical coupling"`
- `scripts/formal_tools.py research "two scale indefinite Hankel diagonal Riesz perturbation exceptional point spectral reality"`
- `scripts/formal_tools.py research "Krein self adjoint 2x2 diagonal energy perturbation discriminant stabilization chamber"`

Corpus contained diagonal KMS and positive-Hankel no-gos, HC3's reporter cone, and HC4's chiral
Riesz instability, but no diagonal Riesz interaction, source-gap collapse, or exact
stability-selection separation.

## Literature boundary

Primary neighbors checked:

- Hikida--Schomerus, FZZ duality and correlation matching, arXiv:0805.3931:
  https://arxiv.org/abs/0805.3931
- Kapitula--Kevrekidis--Yan, Krein matrix and signature theory, arXiv:1212.2951:
  https://arxiv.org/abs/1212.2951
- Guenther--Stefani, spectral branch points in Krein-space settings, arXiv:math-ph/0506021:
  https://arxiv.org/abs/math-ph/0506021
- Poltoratski, Krein spectral shift and rank-one perturbations, arXiv:math/9601206:
  https://arxiv.org/abs/math/9601206

Exact-object searches found no source-specific FZZ diagonal Riesz coupling, source-gap
triangularization, or stability-versus-reflection theorem.  Status is “no collision located,” not
an absolute priority claim.

## Lean closure

Main declarations:

- `fzzCigarParityDilatedSecondDiagonalRieszOperator_represents`
- `fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_formallySelfAdjoint`
- `fzzCigarParityDilatedSecondDiagonalPerturbed_determinant_eq`
- `fzzCigarParityDilatedSecondDiagonalPerturbedCharacteristicDiscriminant_eq`
- `fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_stabilizingCoupling`
- `fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_sq`
- `fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_stabilizingCoupling`
- `fzzCigarParity_allPositiveScales_exists_negative_diagonalStabilizingCoupling`
- `fzzCigarParityMellinCharacterUnitSecondDiagonalReading_eq_reflection_iff`
- `fzzCigarParity_allPositiveScales_diagonalStability_and_reflectionDetector`

Verification on 2026-08-28:

- direct `lake env lean` passed;
- targeted module build passed;
- axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`;
- scoped banned-token and `git diff --check` audits passed;
- module wired into `GaloisForLFunctions.RHTower` umbrella;
- frontier map untouched.

## Gates

- [x] 0 -> 1 in-progress: source-pure conjecture frozen after corpus search
- [x] 1 -> 2 fully-proven: Riesz, characteristic, collapse, and spectral proof complete
- [x] 2 -> 3 formalized: unconditional Lean theorem package and audit
- [ ] 3 -> 4 publication-ready: independent specialist priority/physics audit

## Log

- 2026-08-28 — Conjectured after HC4 closed chiral Riesz stabilization.
- 2026-08-28 — Exact source-gap stabilization and stability-selection separation proved and
  formalized.
