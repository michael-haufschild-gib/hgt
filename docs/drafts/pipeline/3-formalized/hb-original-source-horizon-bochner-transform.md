# HB original source: horizon decay and joint Bochner transform

- **Stage:** 3-formalized; targeted leaf and new-declaration audits passed.
- **Type:** THEOREM (Lean).
- **RH status:** open.
- **Frontier map:** read-only.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

## Exact advance

The actual native square-remainder source is one strongly continuous, causal
family in the original spatial Hilbert space. Its Bochner Laplace integral
converges in norm for every `Re(w)>-2` and equals the exact derived frequency
source, with the physical amplitude, fixed smooth onset transform, original
radial measure and native angular remainder retained.

This closes the joint integral/completion interchange for the native
square-remainder channel. The complete cusp residual additionally contains
three cutoff-principal Green-response channels; their common causal time
construction and full-source transform remain open.

## Horizon cancellation and time decay

Let `t<0` be tortoise radius, `tau` static time, `u(t)=-tanh(t)`, and s the
physical source rate at a Xi occurrence. Write H(v) for the fixed smooth onset
`chi(v) exp(2s v)`. The previous source identity is

`R(tau,t)=C0(t) H(tau+t)+C1(t) H'(tau+t)`,

where C0 is the original zero-frequency reduced coefficient and C1 is twice
the actual radial derivative of its explicit lift.

Both literal coefficients have a horizon zero. Lean proves the exact identities

`1-u(t)=exp(2t)(1+u(t))`,
`Ci(t)=exp(2t) Pi(u(t))`,

with the actual compact profiles Pi continuous on `[0,1]`. No coefficient is
replaced by a scalar proxy. The current-rate theorem gives `Re(2s)<-2` without
RH. For each real `c<2`, the onset and its retained derivative have a bound
`|H(v)|+|H'(v)| <= Bc exp(-cv)`. Hence

`|R(tau,t)| <= Cc exp(-c tau) exp((2-c)t)`.

The last radial factor belongs to L² because `2-c>0`. It follows that the
radial and full spatial source vectors satisfy

`||S(tau)|| <= Dc exp(-c tau)`.

Taking c=0 supplies a fixed L² majorant for all times. Dominated convergence
of squared distances, together with actual pointwise time continuity, proves
strong continuity in the L² quotient. The spatial source is exactly the
continuous separated-product map applied to the radial vector and the
already admitted native angular remainder.

## Independent frequency and genuine interchange

The affine-frequency identity and the two horizon zeros yield

`reducedCoefficient(s,w,a,T,t)`
`  = exp((w+2)t) T (P0(u(t))+w P1(u(t)))`.

Consequently the literal reduced frequency source has radial L² admission
for `Re(w)>-2`. This is a sufficient source-transform chamber; no maximality
claim is made.

For any w in that chamber, choose `c=1-Re(w)/2`. Then `c<2` and
`Re(w)+c>0`. The vector decay estimate proves norm convergence of the weighted
Bochner time integral.

For every original radial L² test g, Cauchy–Schwarz makes
`|g(t)| exp((2-c)t)` integrable in radius. Its product with the integrable time
majorant bounds the full time-space pairing. Absolute Fubini is therefore
valid. Applying the previously proved scalar delayed-source transform inside
that pairing and testing against every g identifies the radial Bochner
integral in the Hilbert quotient. The fixed angular tensor map commutes with
that integral, proving

`integral_(tau>0) exp(-w tau) • timeCuspMainVector(q,branch,a,tau)`
`  = cuspMainLaplaceVector(q,branch,a,w)`.

The right side agrees almost everywhere with

`reducedCoefficient(s,w,a,onsetTransform(2s,w),t)`
`  * squareResidual(q,coordinates(z))`.

The proof does not infer vector interchange from pointwise transforms or
slice admission alone.

## Lean surface and audit

Route namespace `RHTower.D4BMJointSource`; module prefix
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSource`.

| Suffix | Public theorems | Content |
|---|---:|---|
| HorizonFactor | 6 | Exact horizon polynomial factors and compact profiles |
| TimeDecay | 3 | Actual onset-pair and delayed radial source bounds |
| VectorDecay | 9 | Radial/joint L² decay, continuity and native tensor identity |
| TransformChamber | 5 | Frequency source admission and genuine Bochner integrability |
| TransformPairing | 2 | Absolute time-space pairing and all-test Fubini identity |
| VectorLaplace | 4 | Actual radial and joint Bochner source-transform identities |

Generic `GaloisForLFunctions.HTGeometry.L2DominatedContinuity` adds one theorem
in that namespace: pointwise continuity with a fixed L² majorant gives strong
continuity of the actual L² classes.

Total: seven leaves, thirty public theorems, 567 source lines.

All seven canonical leaves passed individual `lake build <module>` audits in
an isolated package backed by existing dependency caches. The audit logs show
only the requested new module compiled in each command, with no warnings.
No dependency or umbrella module was compiled. All seven installed sources
and fourteen `.olean`/`.ilean` artifacts match the audited copies. Each new
leaf is imported exactly once by its area umbrella; no umbrella was built.

A scratch `lake env lean` audit checked all thirty new public theorem axioms,
and only those declarations. Every result contains exactly `propext`,
`Classical.choice`, and `Quot.sound`; no added axiom or computational certificate
occurs. Scoped source-debt, whitespace, artifact and wiring checks passed.

The generated source indexes were refreshed. Repository-wide
`scripts/formal_tools.py lint --check-generated` failed on thirteen concurrent,
unwired modules outside this change: `CoppoFockRotation`,
`CoppoJosephsonPotential`, `CoppoKerrPhaseGeometry`, `CoppoNonlocalNoise`,
`CoppoPartnerEigenspaces`, `CoppoSSH`, `QNMAnchorNormalization`,
`QNMHyperboloidalPolynomial`, `QNMLorentzAuxiliary`, `QNMQuadraticPencil`,
`QNMBackwardError`, `QNMMatrixBackwardError`, and `QNMModalResidue`.
It also reported 141 existing large-file warnings. None of the seven new HB
leaves was flagged. Concurrent modules and their wiring were preserved.

## Remaining hard obligations

The source transform's enlarged chamber does not continue the original
response inverse there. The three cutoff-principal causal responses and their
commutators, complete-source vector transform and convolution with the original
causal response still need construction. Original time equations, propagation,
endpoint traces, constrained Einstein sectors, left-QNM continuation and
multiplicity-matched spin-two/AIME pairing remain separate obligations.
Independent Hawking-clock extinction remains unproved. These theorems impose
no restriction on Xi-zero locations and do not prove RH.

No numerical experiment or computational certificate was used. The existing
route-independent ledger already requires physical-domain identification and
retention of onset terms; no additional universal-law entry is needed. The
frontier map was not edited.
