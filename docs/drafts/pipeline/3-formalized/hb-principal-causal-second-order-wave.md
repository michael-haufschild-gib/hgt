# HB principal causal response: second time derivative and spatial range

- **Stage:** formalized in Lean 4.
- **RH goal:** open.
- **Frontier map:** read-only.

## Exact result

Every actual principal causal response `U_i`, with its original amplitude,
physical source rate and complex potential retained, has a continuous second
time derivative in the original whole-line L² norm. Write
`A=2*pi*<D>`, `F_i` for the actual odd-extended source, and `W_i` for the
original bounded potential. The proved identity is

```
U_i(tau) = A^(-2) [F_i(tau) + W_i U_i(tau) - U_i''(tau)].
```

Here `A^(-2)` is the actual bounded Fourier multiplier
`(2*pi)^(-2)*kgFreqInvOp*kgFreqInvOp`. Thus the constructed response lies in
the twice-regularized spatial range. The proof applies to all three principal
channels without assuming differentiability of the forcing or of the response.
Those properties are derived from their actual definitions.

This closes the time regularity and twice-regularized wave identity needed
for the original radial equation. Identification with the classical radial
differential expression, its endpoint trace and the original Green solution
is still required. No left-QNM continuation or Hawking-clock extinction is
proved here.

## Dependency-closed proof

Let `chi` be the fixed smooth transition and
`H_v(u)=chi(u)*exp(v*u)`. Both derivatives are retained:

```
H_v'  = (chi' + v*chi)*exp(v*u),
H_v'' = (chi'' + 2*v*chi' + v^2*chi)*exp(v*u).
```

The second transition derivative is continuous and vanishes off `[0,1]`.
Compactness gives its global bound. Together with the already proved bound
on `chi'`, this bounds `|H_v'|+|H_v''|` uniformly when `Re(v)<=0`; both vanish
before arrival. The physical rate supplies this inequality unconditionally.

For the literal reduced radial source,

```
R(tau,t) = C0(t)*H_(2s)(tau+t) + 2*B1(t)*H_(2s)'(tau+t),
d_tau R = C0(t)*H_(2s)'(tau+t) + 2*B1(t)*H_(2s)''(tau+t).
```

The established horizon factorizations of `C0` and `2*B1` retain their exact
`exp(2t)` factor and compact profile bounds. Consequently
`|d_tau R(tau,t)| <= C*exp(2t)` for all time and `t<0`. This is an L²
majorant on the original infinite negative ray.

A norm-differentiation lemma supplies the required passage from pointwise
derivatives to actual L² classes. The mean value inequality bounds every
pointwise difference quotient by the derivative majorant. Squared errors are
dominated by four times its square. Dominated convergence and the exact L²
norm formula then prove convergence of slopes in the Hilbert norm. The same
majorant and continuity of the onset jets prove continuity of the derivative.

Odd extension and multiplication by the actual principal amplitudes are
bounded linear maps. They transport this C¹ property to `F_i`. The existing
C¹ response and bounded potential give `G_i=F_i+W_i U_i` a continuous norm
derivative. Established source causality and response initial data give
`G_i(0)=0`.

Write `D(t)=sin(A*t)/A`. Integration by parts retains the boundary term:

```
integral_0^tau cos(A*(tau-sigma))*G(sigma) d_sigma
  = D(tau)*G(0) + integral_0^tau D(tau-sigma)*G'(sigma) d_sigma.
```

The zero initial value therefore identifies `U'` with the retarded
convolution of `G'`. The already proved first-derivative theorem for that
convolution yields `U''` and its continuity.

A second integration by parts uses the bounded operator
`A^(-2)*cos(A*(tau-sigma))`. Its derivative in `sigma` is `D(tau-sigma)`.
The resulting exact identity is

```
U(tau) = A^(-2) [G(tau) - cos(A*tau)*G(0)
  - integral_0^tau cos(A*(tau-sigma))*G'(sigma) d_sigma].
```

Substituting the proved zero initial value and second derivative gives the
stated wave identity. All integrations are Bochner integrals; continuity
supplies interval integrability and the bounded linear maps commute with
them. No pointwise differentiation of an arbitrary L² representative is used.

## Lean audit

Six new canonical leaves, 22 public theorems, 513 source lines:

| Module suffix | Public theorems |
|---|---:|
| `HTGeometry.L2DominatedDerivative` | 1 |
| `RHTower.ThetaCuspHawkingBMJointSourceOnsetDerivativeBound` | 3 |
| `RHTower.ThetaCuspHawkingBMJointSourceTimeDerivative` | 6 |
| `HTGeometry.UnitWaveTimeIntegration` | 3 |
| `HTGeometry.UnitWaveEllipticRange` | 2 |
| `RHTower.ThetaCuspHawkingBMJointSourcePrincipalTimeSecondDerivative` | 7 |

Every final canonical leaf passed its own `lake build <module>` audit in an
isolated package backed by existing caches. Each command compiled exactly
the requested new leaf, without warnings. No existing dependency or umbrella
was built. Twelve installed `.olean`/`.ilean` artifacts match the audited
copies; each new leaf is wired once into its area umbrella.

A scratch `lake env lean` audit checked exactly the 22 new public theorems.
Every result depends only on `propext`, `Classical.choice`, and `Quot.sound`.
No axioms, proof holes or computational certificates were added. No numerical
experiment was run. The onset bound uses direct inequalities in place of a
slow broad arithmetic tactic.

Generated source indexes were refreshed. Repository-wide
`scripts/formal_tools.py lint --check-generated` passed, with 141 existing
large-file warnings and no new-leaf warning. Installed source, artifact,
whitespace and unique umbrella-import checks passed. The frontier map was
unchanged. Owned scratch and isolated audit directories were removed; no
owned Lean or Lake process remained. Concurrent work was preserved.

## Remaining hard obligation

Use the actual Fourier multiplier to identify the spatial differential
expression and construct a continuous representative with the original
endpoint trace. Then prove that the negative-ray restriction of
`principalTimeLaplace` equals `principalDifference` at the actual onset
transform. The corpus identity
`weightSchwartz_fourierSCLM` supplies the matching normalization
`(1+xi^2)*Fourier(f)=Fourier(f-f''/(4*pi^2))` for Schwartz tests.

Only after the endpoint Green comparison is closed can the assembled causal
source transform be identified with `cuspResidualVector`. The response
continuation, retained spin-two pairing and independent Hawking-clock
extinction remain open. The present result supplies no Xi-zero selection.
