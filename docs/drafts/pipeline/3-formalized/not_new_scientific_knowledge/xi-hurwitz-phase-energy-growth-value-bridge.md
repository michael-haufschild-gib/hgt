# Xi--Hurwitz phase, energy, and rectangular-growth value bridge

- **ID:** xi-hurwitz-phase-energy-growth-value-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / VALUE BRIDGE
- **Scientific status:** `[PROVED] [NOT CLAIMED NEW]`
- **Statement:** Every right-half Xi Hurwitz principal phase is simultaneously a transverse displacement, a rectangular growth exponent, and a strictly positive summand controlling the negative limit of finite continued prime--Gamma source values.

## Exact value relation

For every multiplicity copy `q` of a right-half Xi zero, put

\[
  \phi_q=\frac{|\arg(-e^{-2\pi i\rho_q})|}{2\pi}.
\]

The open critical strip removes phase aliasing, and Lean proves

\[
  0<\phi_q<\frac12,
  \qquad
  \phi_q=\Re\rho_q-\frac12.
\]

Its orientation defect is exactly

\[
  d_q=\sin^2(2\pi\phi_q).
\]

Consequently the multiplicity-exact weighted witness

\[
  e_q=w_q\sin^2(2\pi\phi_q)
\]

is strictly positive and satisfies `e_q <= E_Xi`.

## Source consequence

The unconditional continued-Cauchy reconstruction gives finite algebraic source vectors `V_n`
with

\[
  \mathcal W(V_n)\longrightarrow-\mathcal E_\Xi.
\]

For every right-half copy `q`, the same sequence is therefore eventually bounded by

\[
  \mathcal W(V_n)<-\frac{e_q}{2}<0.
\]

Independently, the supremum of the phases `phi_q` is already proved to be the sharp power-growth
exponent of every fixed-width logarithmically sampled rectangular Weil sequence.  This is a direct
cross-route value identification, not a new proof of the missing source sign.

## Research use

The bridge gives a precise falsification test for any proposed unconditional source positivity:
under one hypothetical right-half zero it must fail cofinally by at least the displayed phase
witness.  Conversely, a source proof of eventual nonnegativity along the reconstructed sequence
annihilates every sharp rectangular growth phase at once.

The remaining gap is still source-side.  The current closure theorem produces algebraic-span
vectors, but does not yet expose each `V_n` as a collision-free finite Cauchy packet with its
continued prime--Gamma divided-difference value written term by term.

## Lean certificate

- `formal/GaloisForLFunctions/RHTower/XiHurwitzPhaseEnergyGrowth.lean`
- `xiHurwitzOrientationDefect_eq_sin_sq_rightPrincipalPhase`
- `xiHurwitzRightPrincipalPhase_witness_le_orientationEnergy`
- `sin_two_pi_xiHurwitzRightPrincipalPhase_pos`
- `exists_continuedCauchyCore_eventually_lt_neg_half_phaseWitness`

## Gates

- [x] pointwise phase--defect identity
- [x] strict open-strip phase range
- [x] phase witness bounded by global orientation energy
- [x] phase-to-eventual-negative-source-value theorem
- [x] exact Lean build and axiom audit
- [ ] explicit collision-free packet extraction and termwise continued-source formula
