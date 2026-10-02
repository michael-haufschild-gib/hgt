# Timelike bilinear phase flattening

- **ID:** tt-timelike-bilinear-flattening
- **Stage:** 5-failed
- **Type:** FALSIFIED mechanism; positive survivor formalized
- **Route:** TT/T1, signed nonlocal centered-source covariance
- **Statement:** Interior timelike logarithmic blocks retain a coherent rank-one component after removing two tangent phases; the complete coefficient-weighted remainder has an explicit vanishing relative bound.

## Goal and scope

Test whether a generic bilinear estimate for the actual reduced mass phase
can supply the missing arithmetic cancellation. The phase is
S(u,h)=sqrt(u^2-h^2), already identified from the literal rapidity saddle.
This concerns that phase, not a replacement by the corpus Vaughan phase.
It does not assert an upper bound for the actual centered arithmetic sum.

## Paper proof

For h^2,k^2<=u^2 the exact identity is

    2 S(u,h)(S(u,h)-S(u,k))-2h(k-h)
      = (k-h)^2+(S(u,h)-S(u,k))^2.

When u>0 and |h|,|k|<=3u/4, both shells exceed u/2. Rationalizing
their difference gives |S(u,h)-S(u,k)|<=2|k-h|. Consequently

    |S(u,k)-S(u,h)+(h/S(u,h))(k-h)| <= 5(k-h)^2/u.

Put k=h+x+y. Removing the constant phase a*S(u,h), and the separate
tangent phases -(a*h/S(u,h))*x and -(a*h/S(u,h))*y, leaves a unit
complex kernel K with |K-1|<=5|a|L^2/u whenever |x+y|<=L and the
block remains inside the stated cone. Thus the full finite bilinear
packet is its product of one-variable sums plus an error bounded by
(5|a|L^2/u) times the product of the two coefficient l1 norms.
Unit coefficients retain real part at least (1-5|a|L^2/u) times the
number of ordered pairs. Multiplicative integer blocks correspond to
x=log(m/M), y=log(n/N), h=log(MN).

## No-go closure

- **Proposed mechanism under test:** cancellation uniform over arbitrary
  coefficient vectors from the mass phase alone on interior logarithmic
  blocks, including growing widths L with L^2/u tending to zero.
- **Obstruction:** the two removable tangent phases leave a kernel tending
  uniformly to 1. Coherent coefficient vectors therefore survive.
- **Positive survivor:** the exact tangent energy and complete coefficient-
  preserving bilinear decomposition, including the controlled remainder.
  For actual coefficients, the one-variable twisted sums remain, rather
  than disappearing in an unsigned norm estimate.
- **Status:** the positive survivor has the dependency-closed paper proof
  above and seven audited public theorems in
  `XiMassTimelikeBilinearFlattening.lean`. Only the coefficient-blind
  cancellation mechanism is retired; TT remains open.

This obstruction applies to genuinely growing factor blocks, not just
single entries. For example, m,n in [M,2M], u=4 log M, h=2 log M,
and L=2 log 2 satisfy the cone conditions for sufficiently large M.
Removing the two unit tangent phases preserves the matrix operator norm;
the all-ones test vectors then give a lower bound tending to the maximal
square root of the product of the two block sizes. This application follows
on paper from the finite theorem; an asymptotic operator-norm theorem is
not claimed as a separate Lean declaration.

Actual centered Lambda and Mobius coefficients need not be the coherent
vectors. The finite packet theorem retains their two twisted sums and the
complete remainder. It proves neither cross-block cancellation nor a bound
for the full mass propagator. Its l1 remainder alone can remain exponential.

## Formal certificate

- Exact identity: `xiMassTimelikeAction_tangent_energy`.
- Uniform geometry: `xiMassTimelikeAction_block_chord`,
  `xiMassTimelikeAction_block_tangent`.
- Literal phase factorization: `xiMassTimelikeBilinearFlatKernel_eq`.
- Entry error: `norm_xiMassTimelikeBilinearFlatKernel_sub_one_le`.
- Coefficient-preserving survivor:
  `xiMassTimelikeBilinearFlatKernel_packet_error`.
- Coherent obstruction: `xiMassTimelikeBilinearFlatKernel_coherent_lower`.

Targeted `lake build --old +GaloisForLFunctions.RHTower.XiMassTimelikeBilinearFlattening`
passed. Final `lake env lean GaloisForLFunctions/RHTower/XiMassTimelikeBilinearFlattening.lean`
passed without warnings. A separate `/tmp` audit printed exactly
`[propext, Classical.choice, Quot.sound]` for each of the seven public
theorems. No new axioms, proof holes, heartbeat changes, or numerical
experiments. The leaf is imported by `RHTower.lean`; no umbrella build ran.
Generated indexes refreshed. Repository lint result is recorded in the
working log because unrelated shared modules also affect that gate.

## Log

- 2026-10-02 — source search and exact phase definitions checked; implementation begun.
- 2026-10-02 — exact survivor and obstruction audited; phase-only mechanism retired.
