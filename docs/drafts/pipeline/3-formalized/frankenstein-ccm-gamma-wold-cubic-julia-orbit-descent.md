# CCM--Gamma Wold-cubic Julia-orbit descent

- **ID:** P-G208--P-G210
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Cross-corpus Route P / CCM / Wold / Julia--Krein synthesis
- **Statement:** A literal multiplicity-normalized CCM/Gamma two-fibre source current descends to
  the Wold cubic horizontal response; after Route-P conormal regularization and complete shared-pivot
  orientation symmetrization, every retained strict-right Xi copy has limiting short
  `16/3 * ||c||^2`, strictly above normalized primitive source budget for `c != 0`.

## Goal

Close four concrete obstructions without assuming RH: rank-one environment erasure,
inverse-cubic conormal blow-up, nonholomorphic insertion of `Re rho`, and analytic-multiplicity
loss. Keep exact remaining global completed-source order law visible rather than naming it as
positivity.

## Gates

- [x] 0 -> 1 in-progress: source-pure definitions, exact Xi/prime/Gamma labels, hostile alternatives
- [x] 1 -> 2 fully-proven: dependency-closed algebraic and limit proofs
- [x] 2 -> 3 formalized: three Lean modules compile; audited declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`
- [ ] 3 -> 4 publication-ready: external novelty audit and standalone exposition pending

## Conjecture / fail / pivot log

1. **Single Julia environment block gives positive short.** Fails exactly: rank-one block
   `[[|c|^2, conj c],[c,1]]` has Schur short zero.
2. **One-variable completed residue transports the Wold cubic rate.** Fails structurally:
   `(2 Re (rho-1/2))^3` is nonholomorphic, matching corpus sesquiholomorphic-landing no-go.
3. **Complete FE--Schwarz--Krein orbit over one shared pivot.** Proved. Summing
   `c, star c, -star c, -c` cancels cross terms and gives `diag(4||c||^2,4)`, hence short
   `4||c||^2`.
4. **Two independently holomorphic CCM/Gamma pole gauges recover horizontal cubic rate.** Proved.
   Normalize signed residue `I m` by `-I/m`; selected gauges tend to `rho-1/2` and its Schwarz mate.
   Add them before cubing. Successive residues land exactly on finite Wold response.
5. **Wold cubic neutralizes conormal distance scale.** Proved. On strict-right copy,
   `-(2/3)(2a)^3 * 1/(4a^3) = 4/3`; complete orbit tends to
   `16/3||c||^2`, independent of horizontal distance and ordinate.
6. **Primitive budget controls completed orbit.** Not proved and not assumed. Literal normalized
   budget is strictly smaller than one nonzero orbit quantum. Universal copywise order statement is
   Lean-equivalent to RH, so it is receiver, not producer.

## Paper proof

Let `B(c)=[[|c|^2,conj c],[c,1]]`. Direct expansion gives

`B(c)+B(star c)+B(-star c)+B(-c)=diag(4|c|^2,4)`.

Its Schur short through environment corner `4` is `4|c|^2`.

For Xi support `rho`, let `T(u)` be literal signed primitive-depth completed Gamma trace and
`p_rho=rho-1`. Define

`G_rho(u)=((u-p_rho)(-i T(u))(u+1-1/2))/m_rho`.

The proved source residue `(u-p_rho)T(u) -> i m_rho` gives
`G_rho(u) -> rho-1/2` without simple-zero assumption. For strict-right copy `q`, take independent
variables at `rho` and Schwarz-conjugate support. Then

`(G_rho(u)+G_conj(rho)(v))^3 -> ((rho-1/2)+conj(rho-1/2))^3
 = (2 Re(rho-1/2))^3`.

Multiplying by finite Wold prime-clock coefficient gives exact finite Wold response. Taking the
prime-clock limit gives coefficient `-2/3`. Multiplication by negative Route-P diagonal
`1/(4a^3)` and four-orientation short yields `16/3|c|^2`.

## Lean certificate

- `formal/GaloisForLFunctions/RHTower/FrankensteinCCMGammaWoldCubicSourcePolarization.lean`
  proves centered source gauge, both selected source limits, and exact finite Wold landing.
- `formal/GaloisForLFunctions/RHTower/FrankensteinWoldCubicJuliaOrbitBudget.lean` proves shared-pivot
  orbit diagonalization, nonzero short, Wold regularization, quantum, strict budget gap, and hostile
  RH-equivalence.
- `formal/GaloisForLFunctions/RHTower/FrankensteinCCMGammaWoldCubicJuliaOrbitDescent.lean` composes
  literal source landing with finite regularized Julia-orbit response.

Direct `lake env lean` checks and exact leaf `lake build` checks pass. Umbrella imports are wired;
no umbrella build was run. `scripts/formal_tools.py lint` reaches these modules but currently fails
on unrelated pre-existing unwired HTGeometry modules.

## Exact open core

Construct an independent pre-divisor completed-source order or conservation law bounding this
literal operator-valued orbit current by the primitive Euler budget. It must act before Xi residue
selection and preserve prime/depth coefficients, Gamma/polar countercurrent, Schwarz pairing, and
linear analytic multiplicity. Ordinary source nonexpansiveness, compression-monotone Ward budget,
rank-one shorting, scalar counterterms, and one-variable holomorphic descent do not supply it.

## Novelty status

`[CORPUS-DERIVED] [PROVED HERE] [NOVELTY UNVERIFIED]`. No external literature audit has yet been
performed for the exact two-fibre source polarization plus shared-pivot Wold--Julia composition.

## Log

- 2026-08-18 -- Three-module unconditional Lean chain completed, leaf-built, axiom-audited, and
  wired into `RHTower.lean`.
