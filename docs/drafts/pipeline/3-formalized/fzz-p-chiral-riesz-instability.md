# FZZ-P chiral Riesz instability

- **ID:** FZZ-P-HC4
- **Stage:** 3-formalized
- **Type:** THEOREM / source-native interaction stability classification
- **Source:** FZZ-P-HC2 chiral grade reporter + literal FZZ two-scale Krein metric/operator
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityChiralRieszInstability`
- **Statement:** Riesz-representing the unique source-native chiral reporter through the literal
  indefinite FZZ metric preserves formal Krein self-adjointness but increases the nonreal spectral
  gap by the exact positive square `gamma^2/E`.

## Main theorem

At positive scale `beta`, write

`P=P(beta)`, `Q=P(2 beta)`, `R=P(4 beta)`, `E=Q^2-PR`.

The strict negative Fermi--Hankel minor gives `E>0`.  Let

`G=[[P,Q],[Q,R]]`, `Y=[[0,i],[-i,0]]`.

The source-metric Riesz representative of the HC2 unit chiral reporter is

`B=G^-1 Y=E^-1 [[-iQ,-iR],[iP,iQ]]`.

For the canonical traceless source-Krein generator `A`, define

`A_gamma=A+gamma B`, `gamma in R`.

Then:

1. `G(u,Bv)=u*Yv`, so `B` is formally `G`-self-adjoint;
2. `A_gamma` is formally `G`-self-adjoint and specializes exactly to `A` at `gamma=0`;
3. its exact instability discriminant is
   `Delta_gamma=Delta_0+gamma^2/E>0`;
4. it has an explicit nonzero eigenvector with eigenvalue
   `lambda_gamma=i sqrt(Delta_gamma)`;
5. that eigenvalue is nonreal and its eigenvector is `G`-neutral for every real `gamma`;
6. if `gamma!=0`, then `Im(lambda_0)<Im(lambda_gamma)`.

Consequently no real chiral Riesz coupling restores spectral reality at any positive source scale.

## Paper proof

Matrix multiplication gives `GB=Y`; the four entries reduce to `0,i,-i,0` using
`E=Q^2-PR`.  Since `Y` is Hermitian, `G(Bu,v)=G(u,Bv)`.  Adding this identity to formal
self-adjointness of `A` proves the same property for `A_gamma`.

Write

`A_gamma=[[a,b],[c,-a]]`,

where

- `a=P-i gamma Q/E`,
- `b=Q-i gamma R/E`,
- `c=-PQ/R+i gamma P/E`.

Direct expansion cancels both terms linear in `gamma` and yields

`a^2+bc=-(Delta_0+gamma^2/E)`.

Thus the characteristic equation is `lambda^2=-Delta_gamma`.  Since `Delta_0>0` and `E>0`,
`Delta_gamma>0` for every real coupling, and it is strictly larger than `Delta_0` when
`gamma!=0`.  The vector `(b,lambda_gamma-a)` is an eigenvector; it is nonzero because `Re b=Q>0`.
The square-root formula gives `Im lambda_gamma=sqrt(Delta_gamma)>0`, hence nonreality and strict
gap growth.

Finally formal self-adjointness on this eigenvector gives

`(conj(lambda_gamma)-lambda_gamma) G(v_gamma,v_gamma)=0`.

The first factor is nonzero, so `G(v_gamma,v_gamma)=0`.  Every perturbed nonreal mode therefore
remains neutral.  No premise or unproved dependency remains.

## New route knowledge

HC2 showed that the literal grade crossing already contains the unique chiral Hermitian reporter.
This theorem now evaluates its canonical dynamical realization rather than treating it only as a
readout:

- source-metric Riesz representation is exact and coefficient-faithful;
- chiral coupling is not merely insufficient for stability—it is strictly anti-stabilizing;
- formal Krein self-adjointness and eigenvector neutrality persist at every coupling;
- increasing chiral strength moves the pair farther from spectral reality;
- a viable FZZ/GFZZ stability law must add a diagonally dominating cone component, nonlocal
  channel, nonlinear state dependence, or singular/infinite completion before divisor selection.

This closes one direct interacting producer, but does not prove RH or derive Hermitian reflection
matching on parity-Mellin divisor modes.

## Corpus audit

Mandatory searches on 2026-08-28:

- `scripts/formal_tools.py research "FZZ chiral Hermitian reporter Riesz representative Krein operator spectral stabilization interaction"`
- `scripts/formal_tools.py research "indefinite metric G inverse sigma y perturbation eigenvalue discriminant Krein stability"`
- `scripts/formal_tools.py research "FZZ parity source chiral coupling formally self adjoint perturbed operator real spectrum"`
- `scripts/formal_tools.py research "Krein collision chiral energy perturbation imaginary eigenvalue gap monotonicity"`

Corpus contained the unperturbed FZZ Krein pair and HC2's reporter identity, but no chiral Riesz
operator, perturbative discriminant, or all-coupling stability classification.

## Literature boundary

Primary neighbors checked:

- Hikida--Schomerus, FZZ duality and correlation matching, arXiv:0805.3931:
  https://arxiv.org/abs/0805.3931
- Kapitula--Kevrekidis--Yan, Krein matrix and signature theory, arXiv:1212.2951:
  https://arxiv.org/abs/1212.2951
- Kollar--Miller, graphical Krein signatures and Evans--Krein functions, arXiv:1209.3185:
  https://arxiv.org/abs/1209.3185
- Chernyavsky--Kevrekidis--Pelinovsky, real Krein quantities in Hamiltonian and PT-symmetric
  systems, arXiv:1711.02191: https://arxiv.org/abs/1711.02191

Exact-object searches found no source-specific FZZ chiral Riesz perturbation or the discriminant
law above.  Status is “no collision located,” not an absolute priority claim.

## Lean closure

Main declarations:

- `fzzCigarParityDilatedTwoScaleKreinGap_pos`
- `fzzCigarParityDilatedChiralRieszOperator_represents`
- `fzzCigarParityDilatedChiralRieszOperator_formallySelfAdjoint`
- `fzzCigarParityDilatedChiralPerturbedKreinOperator_formallySelfAdjoint`
- `fzzCigarParityDilatedChiralPerturbed_characteristic`
- `fzzCigarParityDilatedChiralPerturbedEigenpair`
- `fzzCigarParityDilatedChiralPerturbedEigenvector_null`
- `not_fzzCigarParityDilatedChiralPerturbedSpectrallyReal`
- `fzzCigarParityDilatedChiralPerturbedEigenvalue_im_gt`

Verification on 2026-08-28:

- direct `lake env lean` passed;
- targeted module build passed;
- axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`;
- scoped banned-token and `git diff --check` audits passed;
- module wired into `GaloisForLFunctions.RHTower` umbrella;
- frontier map untouched.

## Gates

- [x] 0 -> 1 in-progress: source-pure conjecture frozen after corpus search
- [x] 1 -> 2 fully-proven: exact Riesz, discriminant, eigenpair, and neutrality proof
- [x] 2 -> 3 formalized: unconditional Lean theorem package and audit
- [ ] 3 -> 4 publication-ready: independent specialist priority/physics audit

## Log

- 2026-08-28 — Conjectured from HC2's source-native chiral reporter.
- 2026-08-28 — Exact anti-stabilization law and all-real-coupling no-go proved and formalized.
