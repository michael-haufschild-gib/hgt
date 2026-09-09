# HB: actual physical response radial equation

Status: formalized in seven individually audited leaves, with 18 new public
theorems. RH remains open. Frontier map is read-only.

Chain: theta cusp → Xi occurrence → complete native source → original
outgoing response and physical adjoint residue → independent Hawking-clock
extinction → RH.

## Closed equation

Let U be the original causal response to the complete four-channel cusp
source F. For a physical Xi target r, put u=(r-1)/2, E=scalar(u),
lambda=u^2-1/4, and R=P_r(yU). On `3/2 < Re w < 2`, `Im w != 0`,
the actual projected response satisfies, for every original radial core
test f,

```text
<f'',R> + lambda <sech(t)^2 f,R> - w^2 <f,R>
  = -<f,continuedAngularSourceL2>.
```

The source on the right is the original complete projected source, with
the same parameters and all four channels retained. The inner product is
conjugate linear in its first argument. The theorem constructs weighted
response admission, the differentiated noncompact-test limit, and source
identification internally. It assumes no new response equation or
outgoing inverse.

## Physical vertical derivative

The actual Fourier family's vertical derivative is a finite combination
of three shifted families whose weighted bounds are already proved.
Thus the full Fourier tail has a bounded vertical derivative on every
positive lower-height half-plane. At the physical parameter, the exact
remaining principal term gives

```text
E_y = reflectedCompletedLambda(r-1) (1-r/2) y^(-r/2)
      + (full Fourier tail)_y.
```

Since `0 < Re r < 1`, the displayed power is bounded above the cusp
threshold. Smoothness on the compact remainder and finite cusp measure
then give E_y in the original angular L2 space. This is admission of the
ordinary vertical derivative; admission of E/y was proved earlier.
No admission of E itself in angular L2 is asserted.

## Both cutoff terms and their integral limit

For the previously constructed modular core fields
`g_n=chi_(n+1) conjugate(E)`, real coordinate differentiation and the
full chart product rule give exactly

```text
Delta_H g_n = chi_N conjugate(lambda E)
  + 2 (y chi_N') y conjugate(E_y)
  + (y^2 chi_N'') conjugate(E),       N=n+1.
```

The quotient germ construction transports this equality to the original
modular cell, including its full native chart Laplacian. Both scaled
profile derivatives have a common uniform bound C, hence

```text
|Delta_H g_n| <= (|lambda|+C)|E| + 2 C y |E_y|.
```

For every radial Hilbert test h and joint vector U with yU in L2,
`conjugate(h) E U` is integrable by the reciprocal-weight pairing.
The product `h E_y (yU)` is integrable by the separated L2 product and
Cauchy–Schwarz. These two functions supply an integrable majorant for
the differentiated pairing, uniformly in n. Eventual equality of the
complete test germs supplies pointwise convergence. Dominated convergence
therefore proves

```text
lim_n <h tensor Delta_H g_n,U> = lambda <h,P_r(yU)>.
```

This is the missing integral limit, with the original operator and both
commutator terms controlled. Combining it with the earlier compact-test
equation and mass-pairing limits gives the closed equation above.
Height multiplication of the actual source representative is also proved
equal to the already constructed complete weighted source class; its
physical projection is exactly `continuedAngularSourceL2`.

## Scope still open

The projected radial equation and original radial L2 membership are
proved. Its actual Dirichlet endpoint is now also proved by transporting
the original closed radial graph and deriving the zero-extension Sobolev
trace; see the [endpoint proof](hb-physical-response-dirichlet-endpoint.md).
Equality to the original radial Green response on the overlap and
continuation of that same observable to QNMs remain open. The equation
alone does not establish an endpoint condition. Physical adjoint residue, complete-source
pole survival, spin-two/AIME reconstruction, and independent extinction
also remain open. No unconditional RH proof follows from these leaves.

## Lean leaves and verification

All seven modules are under `GaloisForLFunctions.RHTower`, prefixed
`ThetaCuspHawkingBM`:

- `AngularVerticalBounds`: actual Fourier-family and full-tail derivatives.
- `PhysicalVerticalAdmission`: original physical derivative formula and L2 admission.
- `AngularCutoffCalculus`: exact conjugation and full height-product Laplacian.
- `PhysicalCutoffLaplacian`: original physical field and modular cutoff formula.
- `PhysicalCutoffDomination`: uniform Laplacian bound and derivative pairing admission.
- `PhysicalLaplacianPairingLimit`: exact differentiated pairing and its integral limit.
- `PhysicalResponseRadialEquation`: complete source identity and actual radial equation.

Each leaf passed `lake env lean` in scratch and an individual
`lake build <module>` final audit without warnings, using existing
dependency caches. Only the 18 new public theorems were checked with
`#print axioms`; each uses only `propext`, `Classical.choice`, and
`Quot.sound`. No numerical proof result, new axiom, or placeholder was
used. All seven sources and fourteen audited olean/ilean artifacts were
hash-verified during installation. The seven leaves total 523 lines and
are wired into `RHTower.lean`; no umbrella or full build ran.
The corpus index was refreshed once. `scripts/formal_tools.py lint
--check-generated` passed with existing large-file warnings only;
`git diff --check` passed for the edited tracked documentation and umbrella.
