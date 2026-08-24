# A one-dimensional first-order connection carries only boundary holonomy

- **ID:** `one-dimensional-first-order-connection-hp-gauge-law`
- **Stage:** 3-formalized (Lean 4; promoted 2026-08-24)
- **Type:** DIRECT HILBERT--PÓLYA GAUGE CLASSIFICATION / POSITIVE PRINCIPAL-SYMBOL LAW
- **Scientific status:** `[PROVED] [SEARCH] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Let

  ```text
  H=-ic I_m d/du+V(u),                                      (1)
  ```

  where `c!=0` is real and `V(u)` is a locally integrable Hermitian `m x m` matrix potential. On
  the line, `H` is unitarily gauge-equivalent to free momentum with multiplicity `m`; on a finite
  interval, `V` survives only through one unitary boundary holonomy and the spectrum is a union of
  at most `m` arithmetic progressions. Hence no finite-channel first-order connection with scalar
  principal symbol can be a zeta-zero Hilbert--Pólya operator. A viable local realization must use
  a non-scalar principal symbol, an infinite fibre, or genuinely nonlocal/singular incidence.

## 1. Gauge trivialization on the line

Let `V:R->Herm(m)` be locally integrable. Let `G:R->U(m)` be the absolutely continuous fundamental
solution of

```text
G'(u)=-(i/c)V(u)G(u),
G(0)=I.                                                      (2)
```

Existence and uniqueness are the standard linear Caratheodory theorem. Since `V=V^*`,

```text
(G^*G)'=G'^*G+G^*G'
       =(i/c)G^*VG-(i/c)G^*VG
       =0.                                                   (3)
```

Thus `G(u)` is unitary for every `u`. Let `M_G` be pointwise multiplication by `G`. On the natural
Sobolev domain,

```text
H(Gf)
 =-ic(G'f+Gf')+VGf
 =G(-ic f'),                                                (4)
```

because `(2)` makes `-icG'+VG=0`. Therefore

```text
M_G^* H M_G=-ic I_m d/du.                                   (5)
```

On `L2(R,C^m)`, the Fourier transform sends `(5)` to multiplication by `c t I_m`. Consequently `H`
has purely absolutely continuous spectrum `R` of multiplicity `m` and empty point spectrum.

The argument permits noncommuting values `V(u_1),V(u_2)`: the path-ordered fundamental solution in
`(2)` performs the full nonabelian gauge. Noncommutativity of the matrix coefficients alone does not
create one-dimensional curvature or spectral confinement.

## 2. Finite-interval classification

Put the operator on `[0,L]`, `L>0`, with a self-adjoint boundary condition

```text
f(L)=W f(0),   W in U(m).                                   (6)
```

Under `f=Gg`, `(6)` becomes

```text
g(L)=W_eff g(0),
W_eff=G(L)^* W G(0).                                       (7)
```

Thus every local potential enters only through the effective holonomy `W_eff`. Let its eigenvalues
be `exp(i theta_j)`, `1<=j<=m`. A free eigenfunction is `g(u)=exp(i lambda u/c)v`, and `(7)` gives

```text
exp(i lambda L/c)v=W_eff v.                                 (8)
```

Hence

```text
spec(H)=union_(j=1)^m
  { (c/L)(theta_j+2 pi k):k in Z },                         (9)
```

up to the harmless sign convention for the derivative. The spectrum is a finite union of equally
spaced lattices.

An energy-independent boundary unitary therefore cannot produce the Riemann--von Mangoldt density
`T log T`, let alone the exact zeta ordinates. Allowing an energy-dependent `W(lambda)` writes a
secular equation into the boundary data; it is not the domain of one fixed self-adjoint operator
unless it is realized by an additional boundary Hilbert space or a genuine boundary relation.

## 3. Hilbert--Pólya consequences

The theorem exhausts all finite-channel local repairs of the BBM/Berry--Keating clock with scalar
principal symbol.

1. **Scalar potential:** pure gauge, even if unbounded locally subject to the ODE/domain hypotheses.
2. **Finite matrix potential:** still pure nonabelian gauge; only endpoint holonomy remains.
3. **Finite prime phases in the connection:** they may make `G(L)` arithmetically complicated, but
   produce only the `m` offsets in `(9)`.
4. **Growing cutoff channels:** to retain all prime phases one needs at least `m_N>pi(N)` real state
   dimension in the regular autonomous category, but each finite stage remains a union of lattices
   unless its principal symbol or boundary category changes.

Thus a successful local first-order operator must have a principal symbol `J` with at least two
spectral sectors,

```text
H=-i J d/du+V(u),   [J,V(u)] not identically zero,           (10)
```

so the gauge group preserving `J` cannot remove the transverse part of `V`. Alternatively it must
use a nonlocal integral/translation kernel, an infinite-dimensional fibre, or a singular source
boundary module.

Equation `(10)` is a necessary shape, not a sufficient RH mechanism. The source still has to select
`J,V`, the closed domain, and the determinant without using the Xi divisor.

## 4. Constraint reading

The completed flat `(sigma_p,partial_s)` generator is a one-dimensional connection when represented
with scalar principal symbol. This theorem shows why its local connection coefficients cannot be
the Hilbert--Pólya spectrum producer: on a simply connected one-dimensional base, they are gauge.

The positive carrier must therefore be one of:

```text
graded curvature/incidence across distinct principal-symbol sectors,
global boundary holonomy in a growing or infinite fibre,
nonlocal prime--archimedean kernel,
singular extension class with a nonliftable determinant boundary.             (11)
```

This is the operator version of “constraint, not flow”: a flat one-dimensional connection can
transport phase, but its local coefficients cannot quantize the zeta divisor.

## 5. Boundaries

- Matrix Dirac and canonical systems with non-scalar `J` are outside the theorem.
- Second-order Sturm--Liouville operators are outside the theorem; their scalar potential is not
  pure gauge.
- Infinite-dimensional holonomy can have non-lattice spectral structure, but must satisfy its own
  compactness and determinant theorems.
- Singular measures and point interactions require a separate extension analysis. Purely chiral
  unitary jumps are still holonomy; sector-mixing singularities with non-scalar principal symbol
  may survive.
- Finite determinant families converging locally uniformly to `Xi` are outside the global
  point-operator classification.

## Scientific status

After removing the RH vocabulary, this is the elementary gauge triviality of a connection on a
one-dimensional simply connected base and the standard self-adjoint boundary classification of
first-order momentum on an interval. It is `[SEARCH]`/`[BRIDGE]`, not new scientific knowledge.

## Lean formalization certificate

- `formal/GaloisForLFunctions/HTGeometry/LocallyIntegrableLinearEvolution.lean` constructs the
  global Peano--Baker/Carathéodory evolution for locally integrable Banach-algebra coefficients,
  with continuity, compact-interval absolute continuity, the ODE almost everywhere, factorial
  Volterra estimates, and global uniqueness. Supporting absolute-continuity infrastructure is in
  `BanachIntervalIntegralAbsoluteContinuity.lean`.
- `formal/GaloisForLFunctions/HTGeometry/FirstOrderConnectionGauge.lean` specializes the evolution
  to `G' = -(i/c)VG`, proves pointwise norm preservation and finite-dimensional unitarity, and
  proves the exact almost-everywhere derivative/product cancellation on the natural first-order
  representative domain in `ae_caratheodoryGauge_trivializes_connection`.
- `formal/GaloisForLFunctions/HTGeometry/L2OperatorFamilyIsometry.lean` and
  `FirstOrderConnectionL2Gauge.lean` lift the pointwise gauge and adjoint inverse to a genuine
  unitary multiplication operator on vector-valued `L²(R)`.
- `formal/GaloisForLFunctions/HTGeometry/FreeMomentumSpectralClassification.lean` proves the
  vector Plancherel multiplier law with the project convention `2*pi*c*xi`, absolute continuity
  of the pushforward spectral measure, full real essential range, empty point spectrum, and
  constant finite-channel multiplicity `m`; capstone
  `finiteChannel_freeMomentum_spectral_classification`.
- `formal/GaloisForLFunctions/HTGeometry/FirstOrderConnectionIntervalClassification.lean` proves
  the endpoint holonomy formula, characteristic-polynomial eigenphase census, exact union of at
  most `m` arithmetic lattices, explicit linear finite-window count, and impossibility of every
  eventual positive `T*log T` lower density; capstone
  `finiteChannel_connection_interval_classification`.
- Every listed leaf passed direct `lake env lean` checking and targeted `lake build`; all new
  modules are wired into `HTGeometry.lean` without an umbrella build. `scripts/formal_tools.py
  lint` passed.
- `#print axioms` for the new capstones reports only `propext`, `Classical.choice`, and
  `Quot.sound`; no project axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration is used.

## Formalization gates

- [x] nonabelian Carathéodory unitary gauge constructed and unique.
- [x] natural-domain gauge cancellation and genuine `L²` unitary proved.
- [x] full-line spectral type classified.
- [x] finite-interval spectrum computed from holonomy as at most `m` lattices.
- [x] linear counting law and `T log T` obstruction proved.
- [x] finite-channel scalar-principal-symbol Hilbert--Pólya class closed.

Follow-up outside this card: investigate the minimal graded principal symbol `(10)` with a
source-derived transverse prime--archimedean potential.
