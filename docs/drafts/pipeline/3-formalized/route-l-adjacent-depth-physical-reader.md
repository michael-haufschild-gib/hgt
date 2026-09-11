# Route L: adjacent-depth nonlinear physical reader

- **ID:** L-C30
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** LEAN-CLOSED; source-derived physical readout and exact collapse boundary
- **Depends on:** [C29 actual regulator/depth crossover](../3-formalized/route-l-regulator-depth-crossover.md)
- **RH status:** unproved; physical-reader vanishing remains separate

## Target and source provenance

Let `T_M` be C29's original admitted complete integral tail operator at
unchanged spectral point `w` and internal orders `k,l`. Keep ordinary
dilation six. For the same positive regulator `epsilon_M` at adjacent
depths, take the literal quotient

`Q_M=AbelDefect(epsilon_M,6,T_(M+1))/AbelDefect(epsilon_M,6,T_M)`.

Proved: whenever `epsilon_M -> 0` and the original internal jet
product is nonzero, `Q_M -> q(w)`, the original successor ratio.
No convergence or increment assumption on `M*epsilon_M` is imposed.
Using the same regulator in numerator and denominator is essential.
Every original multiplicity-top Xi source supplies the nonzero product.

Put `beta=successor(6)/6>1` and `kappa=2*log(6)/log(beta)`.
Define the fixed nonlinear scalar reader, independently of `w` and its
zero label, by

`F(z)=1/6-||z||^kappa`.

Since `||q(w)||=beta^(-Re(s(w)))`, the proved limit is

`F(Q_M) -> 1/6-6^(-2*Re(s(w))) = B_6(s(w))`,

where `B_6` is the already fixed ordinary-integer BV Green--Stokes
boundary evaluation. This constructs an actual source-derived
nonlinear physical readout at the original anchor, including from paths
where the individual normalized measurements vanish.

The complete sequence remains the input, with its original prime,
depth, multiplicity, nonzero jet and spectral point. The decoder uses
only the adjacent actual defect values and the intrinsic degree-six
successor base. It does not feed the desired physical value or the
spectral parameter into the decoder. Finite diagonal repairs
preserve the quotient at all sufficiently late original depths.

This identifies a physical value; it does not prove it zero or identify it
with the cyclic endpoint reader. Its zero condition must not be assumed
as an RH input. Reflection must retain its actual source and separately
recover the paired physical radial defect.

## Proof

C29 gives the exact factorization

`Defect(epsilon,6,T_M)=epsilon^2*N_M^(-1)*6^(-M*epsilon)*H_M(epsilon)`,

with `H_M(epsilon_M)->K!=0` for every eventually positive
`epsilon_M->0`. The same theorem applied to the predecessor-shifted
regulator path and then composed with `M->M+1` gives
`H_(M+1)(epsilon_M)->K`. Both defects are eventually nonzero.

Exact adjacent normalizer cancellation gives

`Q_M=q(w)*6^(-epsilon_M)*H_(M+1)(epsilon_M)/H_M(epsilon_M)`.

Thus `Q_M->q(w)` independently of the size of `M*epsilon_M`.
Real-power and logarithm identities give the fixed decoder identity;
continuity at nonzero `q(w)` then gives the physical readout limit.
All operator/source identities come from the audited C29 complete
integrand bridge. No new admission or source-action identity is assumed.

## Failed transfers and remaining checks

The first two deep/method searches (20 candidates and 20 source-method
arguments each) were inspected. They returned parameter differentiation,
relative transgression and nonlinear-covariance interfaces, with partial
coverage and generation `823350`. The inspected Peierls stationary
elimination needs cyclic variational incidence and causal skewness;
those have not been constructed for this source. The existing adiabatic
Green--Stokes theorem retains the transgression difference rather than
forcing absolute vanishing. Neither supplies the missing fixed-reader
agreement. The present theorem instead derives a concrete nonlinear
reader from actual adjacent measurements.

The third whole-corpus deep/method search returned an applicable proof
mechanism: `tendsto_shellAdjacentTransfer` in
`HighExponentShellLeastAtomAsymptotic.lean` divides adjacent normalized
shells converging to the same nonzero limit. Its source proof was read.
C29 supplies that mechanism for the actual complete-source defects with a
common moving regulator. All 20 candidates and 20 source arguments were
inspected; one proposed ingredient set repeats this ratio mechanism.
Coverage remained partial: source generation `823350`, 552 pending/stale
files reported, semantic coverage 2,196,271/2,337,170; candidate
applicability was checked in the complete scratch and final audits.

The fourth deep/method search for projective boundary balance returned
20 candidates and 20 source arguments, all inspected. Coverage was partial
(deadline, filter/judge and source refresh; same generation and semantic
counts), with no proof ideas or ingredient sets. The inspected
`asymptotic_conjOp_iff` requires symmetric operators and zero trace
difference; it transfers an asymptotic relation rather than producing it.
The inspected Davies detailed-balance theorem constructs Gibbs populations
using the prescribed Boltzmann ratio, so stationarity does not force equal
populations or the critical spectral rate. The fifth same-source swapped-port search also returned 20 candidates and
20 source arguments, all inspected, with the same partial coverage and no
new proof ideas/ingredient sets. Source-zero Hedenmalm equivariance was
read: it transports the actual causal flow to the reflected parameter;
fixedness of that flow is separately equivalent to the critical line.
The mixed-horizon optical comparison explicitly assumes its response
incidence and reciprocity identities. These transfers do not provide a
common symmetric response realization for the two Route-L readers.
Search hits from dependency test files declaring axioms were rejected;
none is imported or used. Broad arXiv searches for transmutation,
isomonodromy, gluing, subordination, resurgence and intertwining have so
far returned older papers despite June--September 2026 preferences;
no recent result or external hypothesis is being presumed.

The actual quotient, fixed decoder, all-divisor specialization and finite
diagonal repairs are formalized. The remaining task is to derive a
whole-source law forcing this physical readout to vanish; the construction
itself is not an RH proof.


## External transfer audit and collapse test

- [Patie--Savov--Zhao, arXiv:1706.08995](https://arxiv.org/abs/1706.08995):
  abstract inspected. Boundary extension starts with an existing Markov
  semigroup intertwining and suitable normalization; it does not produce
  the missing source/physical intertwining here.
- [Amar, arXiv:1105.1932](https://arxiv.org/abs/1105.1932): abstract
  inspected. Hardy/Bergman subordination transfers established properties
  between specified domains; no Route-L physical comparison follows.
- Broad additional single-word searches: tomography, projective,
  reciprocity. These found [Vu et al., arXiv:2609.04169v2, September 6,
  2026](https://arxiv.org/html/2609.04169v2). Theorem 1 and Theorem 4 proofs
  were inspected. Inverting a symmetric operator preserves symmetry, so
  swapped drive/read ports give equal response entries. This mechanism
  requires an actual common symmetric response operator and exact port
  identification. It does not equate arbitrary diagonal responses or
  nonlinear decay readings. Neither requirement has been established for
  the two physical readers. No numerical experiment from the paper is
  used or run.

Additional theorem forced by the exact C29 factorization: each raw
actual defect tends to zero, at both adjacent depths with the same
regulator, because `|q|<1`, `epsilon->0`, `0<6^(-M*epsilon)<=1`, and the
deattenuated factor converges. Nevertheless the fixed quotient decoder
converges to `B_6(s)`, whereas its value at the collapsed zero pair is
`F(0)=1/6`. Since `6^(-2 Re(s))>0`, these values differ at every finite
source parameter. Lean proves, using the actual Xi source, that
the literal totalized quotient decoder is discontinuous at the zero
pair. This concerns its fixed value `F(0)`, not every possible endpoint
assignment on a restricted source family. The positive survivor is the already constructed relative-decay
physical readout; zero raw measurements do not supply its vanishing.


## Completed Lean audit

[Module](../../../../formal/GaloisForLFunctions/RHTower/DeningerGammaSixAdjacentDepthPhysicalReader.lean):
22 theorems and 5 definitions; wired into `RHTower`.

- Complete scratch: `lake env lean /tmp/route_l_adjacent_depth_physical_reader.lean`,
  exit 0, empty log. Repository proof bodies match this successful scratch.
- Targeted final build:
  `lake build GaloisForLFunctions.RHTower.DeningerGammaSixAdjacentDepthPhysicalReader`,
  exit 0; new module built successfully. Log:
  `/tmp/route_l_adjacent_depth_build.log`. No full or umbrella build.
- All 22 theorem dependencies:
  `lake env lean /tmp/route_l_adjacent_depth_axioms.lean`, exit 0.
  Exact theorem-name coverage checked; every report contains only
  `propext`, `Classical.choice`, `Quot.sound`. No added axioms or proof gaps.
  Log: `/tmp/route_l_adjacent_depth_axioms.log`.
- Required `scripts/formal_tools.py lint`: exit 0, `formal lint passed`.
  Log: `/tmp/route_l_adjacent_depth_lint.log`; repository warnings remain.
- Foreground Lean checks were sequential; all owned Lean processes exited.
  No numerical experiments or computations were used.

Key conclusions are
`tendsto_deningerGammaSixAdjacentDefectQuotient`,
`tendsto_deningerGammaSixAdjacentDefect_physicalBV`,
`tendsto_deningerGammaSixXiAdjacentPhysicalReadout`,
`tendsto_deningerGammaSixXiAdjacentPhysicalReadout_reflected`,
`tendsto_deningerGammaSixAdjacentDefect_finite_repair_physicalBV`,
`tendsto_deningerGammaSixIntegralTailOperator_defect_pair_zero`, and
`deningerGammaSixAdjacentPhysicalDecoder_not_continuousAt_zero`.

The decoder is nonlinear and cancels the common amplitude; its inputs
remain the original complete defects with their nonzero internal Xi jet.
It is not an injective encoding of source energy and is not a cyclic
linear reader. Neither property may be inferred from recovery of the
physical value. The next RH-bearing obligation is an independently
proved whole-source law identifying this physical value with the fixed
zero/cyclic boundary reading, retaining native arithmetic action and
original anchor. All-zero raw limits, reflected equivariance, generic
Gibbs stationarity and reciprocal-port terminology do not supply that
law.
