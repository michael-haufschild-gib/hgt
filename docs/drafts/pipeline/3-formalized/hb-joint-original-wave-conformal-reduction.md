# HB original joint-wave conformal reduction

- **Stage:** 3-formalized.
- **RH status:** open. This proves an exact differential reduction, not regularity
  or causality of the completed response.
- **Frontier map:** read-only.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

The [admitted original residual](hb-full-original-source-admission.md) has a
completed joint energy/operator-domain response. The results here give an exact
local Euclidean equation to which that response must be transferred. All
identities use actual derivatives and the corpus's original metric wave.

## Exact coordinate and field identities

Write original coordinates as p=(t,x,y), y>0, and define

`u(t)=-sinh(t)/cosh(t)`, `a(t)=1/cosh(t)`,
`Phi(p)=(X,Y,Z)=(yu,ya,x)`, `m(p)=sqrt(y)*sqrt(cosh(t))`.

The verified relations are `u²+a²=1`, `u'=-a²`, `a'=au`, and `m≠0`.
With derivative index i=(t,x,y), the actual chart derivatives are

| i | partial_i Phi | partial_i² Phi |
|---|---|---|
| t | (-ya²,yau,0) | (-2ya²u,ya(2u²-1),0) |
| x | (0,0,1) | (0,0,0) |
| y | (u,a,0) | (0,0,0) |

Set `A=(1,a²y²,a²y²)`. The actual weight jets have ratios

`alpha=(m_i/m)=(-u/2,0,1/(2y))`,
`beta=(m_ii/m)=(a²/2+u²/4,0,-1/(4y²))`.

The exact contraction identities are

`sum_i A_i Phi_i,j Phi_i,k = Y² delta_jk`,
`sum_i A_i (Phi_ii,j+2 alpha_i Phi_i,j)=0`,
`sum_i A_i beta_i=1/4`.

The second derivative chain and product rules, applied to these actual jets,
therefore prove for every actual C² complex field V near Phi(p):

`L[m*(V o Phi)] = m*[Y²*(Delta_E V) o Phi+(V o Phi)/4]`,

where `L=partial_t²+a²y²(partial_x²+partial_y²)`. The intermediate coordinate
operator is explicitly identified with the corpus's original `fieldWave`,
including its original angular `scalarLaplacian`. The resulting theorem is

`fieldWave_w[m*(V o Phi)]`
`=m*[(w²-1/4)*(V o Phi)-Y²*(Delta_E V) o Phi]`.

No field derivatives are assigned by compatibility. The proof uses their
Frechet Hessians and actual coordinate derivatives. The complex parameter w is
arbitrary; y>0 and C² regularity are the explicit local analytic conditions.
These conditions are not supplied by the completed energy response yet.

## Inverse and density

The actual inverse is

`Psi(X,Y,Z)=(-arsinh(X/Y),Z,sqrt(X²+Y²))`.

Lean proves `Psi(Phi(p))=p` for y>0, `Phi(Psi(q))=q` for Y>0, and smoothness of
the inverse on Y>0. The original t<0,y>0 coordinate domain corresponds to
X>0,Y>0. This describes the coordinate domain; modular quotient identification
still needs its own transfer.

The determinant of the actual Frechet Jacobian, with columns given by the
coordinate basis, is `det D Phi=ya=Y>0`. The actual complex weight satisfies
`norm(m)²=y/a`. Hence the exact density coefficient is

`norm(m)²/(y² det D Phi)=1/Y²`.

This is the coefficient required for transforming the native scalar mass
integral. The module proves this algebraic identity, not a measure pushforward
or a weak-test change-of-variables theorem.

## Sobolev gain

The existing planar Fourier proof extends to every finite-dimensional real
Euclidean space E. For its actual tempered distributions,

`BesselPotential_2(v)=v-(2*pi)^(-2)*Delta(v)`.

Thus `v in H^s` and `Delta(v) in H^s` imply `v in H^(s+2)`.
This includes dimension three, with the corpus's Fourier normalization. The
chart calculus uses `Fin 3 -> R`; a distributional application must identify
its coordinate Laplacian with the Euclidean-space Laplacian under the standard
continuous linear coordinate equivalence. That identification and application
to the completed response remain open.

## Lean surface

Namespace: `RHTower.D4BMJointConformal`. Canonical prefix:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointConformal`.

| Suffix | Public theorems | Content |
|---|---:|---|
| CurveJets | 1 | Actual weighted curve second derivative |
| CoordinateLines | 4 | Actual coordinate-line derivatives and Hessian slots |
| WarpJets | 13 | Actual hyperbolic and weight-root derivatives |
| ChartJets | 4 | Smooth chart and actual first/second jets |
| WeightJets | 5 | Nonzero smooth weight and actual first/second jets |
| Coefficients | 5 | Exact principal, drift, and potential coefficients |
| JetContraction | 4 | Linear and bilinear basis contractions |
| Conjugation | 5 | Actual coordinate-wave conjugation |
| OriginalWave | 5 | Identification with original metric wave |
| InverseChart | 7 | Smooth inverse and physical coordinate domains |
| ChartDensity | 5 | Actual Jacobian and mass-density coefficient |

The twelfth leaf is
`GaloisForLFunctions.HTGeometry.EuclideanSobolevLaplacianGain`, containing two
public theorems in namespace `GaloisForLFunctions.HTGeometry`. Total: twelve
leaves and sixty public theorems.

Key endpoints: `originalWave_conjugation`, `inverseChart_chart`,
`chart_inverseChart`, `chart_jacobian`, `chart_weighted_mass_density`, and
`euclidean_sobolev_gain_two`.

## Audit

Every development module passed its foreground scratch `lake env lean` check.
All twelve exact canonical `lake build <module>` audits passed, each compiling
only its new leaf plus bookkeeping (two jobs). All twelve source pairs and
twenty-four installed olean/ilean pairs match the audited bytes. Each leaf is
wired once into its area umbrella; no dependency or umbrella build was run.

One scratch axiom audit of only the sixty new public theorems found only
`propext`, `Classical.choice`, and `Quot.sound`. Source indexing, scoped
whitespace checks, and `lint --check-generated` passed. Lint reported 141
existing large-file warnings. The new Lean sources total 840 lines.

No numerical computation or computational certificate was used. No new
route-independent law was established, so universal-law STATUS was not edited.
The frontier map was not edited.
All owned Lean/Lake processes exited; the owned scratch and isolated audit
directories were removed after verification.

## Remaining hard obligations

Transfer the actual completed joint response, measure, and weak tests through
Phi and m. Establish the distributional Euclidean equation with its original
source and localization derivatives. The current joint graph uses separated
radial/angular tests; extending its equation to arbitrary compact joint tests
requires proof in the appropriate derivative topology. L² density of test
values alone does not supply this step.

Then apply Euclidean Sobolev gain and bootstrap to the actual response, prove
modular patching and radial boundary transfer, and construct frequency-dependent
time-causal inversion. Constrained Einstein reconstruction, the left-QNM action
pairing, and independent Hawking-clock extinction remain necessary. These
coordinate identities alone impose no Xi-zero restriction.
