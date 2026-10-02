# TG cofinal escape of the confluent counterterm

- **ID:** TG-C6-CONFLUENT-ESCAPE
- **Stage:** 3-formalized
- **Route:** TG
- **Module:** `RHTower.PrimeBurnolCofinalCountertermEscape`
- **Parent:** `../1-in-progress/tg-confluent-cofinal-counterterm.md`

## Exact source results

For every finite injective prime-depth packet, let `f_i` be its actual zero-clock Burnol
columns and `h_i=r f_i` its radial jets. Let `H=Gram(f,h)`, `G=Gram(f)`,
`K=M_2-M_1 G^-1 M_1`, and `D=H^-1 [0;G]`. The physical dual family
`z_j=sum_i D_ij (f,h)_i` satisfies

```
<f_i,z_j>=0,     <h_i,z_j>=G_ij,
Gram(z)=G K^-1 G.
```

Fix any prime p and grow its packet through depths 0,...,N. For the ground dual `z_N=z_0`,
the energy `E_N=Re Tr(G K^-1 G)`, and the positive operator `B_N=sum_j |z_j><z_j|`,
Lean proves

```
||z_N|| -> infinity,
E_N=sum_j ||z_j||² -> infinity,
||B_N|| >= ||z_N||²,     ||B_N|| -> infinity.
```

The actual cubic principal coefficient from `PrimeBurnolMixedCubicPrincipal` is exactly

```
coefficient_N(a) = -v(a,p)(u(a,p)-1/2) E_N,
u=visibility²,    v=visibility*contrast.
```

The unconditional dichotomy includes every real grade: if that theta factor is zero, all
these second-order coefficients are zero; otherwise their norms tend to infinity. No claim
that the first-order pole vanishes in the exceptional grades is made.

## Dependency-closed paper proof

Finite confluent independence gives invertibility of H. Multiplying `H D=[0;G]` proves both
dual pairing identities. Since H and G are Hermitian, the dual Gram equals
`[0,G] H^-1 [0;G]=G K^-1 G` by the already checked Schur inverse identity.

Every fixed finite original-column combination y is orthogonal to `z_N` eventually, while
`<h_0,z_N>=||f_0||²>0`. The corpus's literal single-prime depth density approximates h_0
arbitrarily closely by such y. Cauchy–Schwarz gives
`||f_0||²<=||h_0-y|| ||z_N||`, forcing norm divergence. The Gram trace is the sum of all
squared dual norms. The quadratic form of B_N is the sum of squared dual pairings; testing
on z_N gives `||z_N||^4<=||B_N|| ||z_N||²`, hence the stronger operator-norm conclusion.
For a fixed prime, actual theta U and V are scalar matrices, giving the coefficient formula.

## Strongest positive survivor

Normalize the actual ground dual: `e_N=z_N/||z_N||`. Its norm is one. The same density
argument, now applied to an arbitrary fixed physical vector, proves `<x,e_N>->0`.
The rank-one operator `Q_N=|e_N><e_N|` is self-adjoint, idempotent, fixes e_N, has range
`span(e_N)`, rank one, and norm one, while `Q_N x->0` for every fixed x.

This is an explicit source-native finite-rank escape law, with its positive survivor proved
alongside the obstruction. No infinite-dimensional trace interface or Hardy index is inferred
from the rank statement.

## Frontier contribution and limits

Finite inverse-Gram cancellation cannot be followed by a uniform bound for this uncompensated
counterterm. Its divergence already occurs in operator norm at a single prime, so it is not
merely an increasing-rank trace effect. A joint prime–Gamma construction must control the
moving dual directions before completion. The theorem does not rule out that joint cancellation.

The mixed first-order pole, bounded remainder, arithmetic Gamma matching, Hardy-index transfer,
and final sub-unit estimate remain open. RH remains unproved and unfalsified.

## Audit

- Production `lake --old env lean -o ... PrimeBurnolCofinalCountertermEscape.lean`: exit 0,
  no warnings; default heartbeats.
- Leaf wired into the RHTower umbrella; no full or umbrella build.
- Separate `lake --old env lean /tmp/...` import audit of all 25 public theorem axiom sets:
  exit 0; only `propext`, `Classical.choice`, and `Quot.sound`.
- Corpus index refreshed. Authoritative lint exits 1 on eleven unrelated unwired RHTower leaves:
  CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
  CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
  CCMRetainedChainKernelLower, MobiusDivisorCriticalSourceSimpleJet,
  MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
  ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving. No new TG error.
- C6 scratch files and search/diagnostic outputs cleaned after recording their outcomes.
