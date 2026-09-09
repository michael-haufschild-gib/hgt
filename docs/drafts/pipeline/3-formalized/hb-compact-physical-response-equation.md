# HB: compact physical response equation

Status: formalized in seven individually audited leaves, with 36 new
public theorems and eight definitions. RH remains open. Frontier map is
read-only.

Chain: theta cusp → Xi occurrence → complete native source → original
outgoing response and physical adjoint residue → independent Hawking-clock
extinction → RH.

## Original compact-test equation

Let J be the original scalar embedding of the completed joint energy
graph. Its remaining components are the radial derivative and the two
modular derivatives multiplied by sech(t). For every original compact
radial test f and full smooth compact modular core field g, the native
modular Green identity extends to every element of that completed graph.
The proof uses the existing constructed planar periodization of g;
neither an interior-only test nor a new condition at a modular seam is
substituted for the full core.

The radial derivative test f' stays in the original radial core.
Multiplication of f by sech(t) also preserves that core. The resulting
identities transfer both derivatives onto the tests and give, for the
actual causal response U=J jointWaveResponse(w,F),

```text
<f'' tensor g,U> + <sech(t)^2 f tensor Delta_H g,U>
  - w^2 <f tensor g,U> = -<f tensor g,F>.
```

All inner products use the test-first convention, conjugate linear in
their first argument. The theorem retains the complete source F. Its
response specialization supplies the weak equation from the existing
inverse's proved specification, rather than assuming a new PDE premise.

The same transposition identifies the original unbounded Friedrichs
operator on these core fields. Its action is exactly

```text
f tensor g - f'' tensor g - sech(t)^2 f tensor Delta_H g.
```

To prove domain membership, pair this expression with every completed
energy field. The result is the original energy inner product with the
core graph vector. The embedding adjoint therefore returns that vector;
the already constructed covariance/inverse relation supplies membership
and the literal operator action.

## Constructed compact physical tests

Use theta(y)=1-smoothTransition(y-2) and chi_N(y)=theta(y/N).
For N>=1, chi_N is one below 2N, zero above 3N, and between zero and one.
Its profile is constant across the low nonparabolic overlaps of the
modular fundamental cell. Translation preserves height, so its full
cell germs are compatible under every modular element. Cell-germ
extension constructs a smooth invariant cutoff on the actual quotient,
with support in the compact truncated cell y<=3N.

Both profile derivatives obey a bound independent of N:

```text
|y chi_N'(y)| <= C,       |y^2 chi_N''(y)| <= C.
```

The exact derivative formulas reduce these quantities to
`|(y/N) theta'(y/N)|` and `|(y/N)^2 theta''(y/N)|`. The unscaled
derivatives vanish outside [2,3]; continuity on that compact interval
supplies C. No numerical bound or numerical experiment is used.

For each Xi target r, use its actual physical angular parameter
u=(r-1)/2. The corpus's full-field inversion theorem and literal
periodicity imply invariance under S and T, hence the entire modular
group. Smoothness comes from the proved full scalar series, including
all Fourier modes. Thus

```text
g_n = chi_(n+1) conjugate(E_r)
```

is a constructed original CoreField. The conjugation ensures its Hilbert
pairing contains E_r, as required by the original physical projection.
For each fixed cell point, the complete germ of g_n eventually equals
conjugate(E_r), so its native Laplacian eventually equals that field's
native Laplacian at the point.

## Actual response pairing limit

For any original joint vector U with yU in L2 and any radial Hilbert
test h, the earlier reciprocal-weight construction proves integrability
of `conjugate(h) E_r U`. The compact test's inner product is exactly
its integral multiplied by chi_(n+1). Cutoff modulus is at most one,
and the cutoff is eventually one at every fixed cell point. Dominated
convergence therefore gives

```text
lim_n <h tensor g_n,U> = <h,P_r(yU)>.
```

For the actual complete cusp response, weighted admission is instantiated
internally on `3/2 < Re w < 2`, `Im w != 0`. No weighted-response
assumption is supplied at this specialization. The compact equation
above is also instantiated for these exact g_n and the full original
four-channel source.

## Current continuation and remaining obligation

The differentiated angular integral limit and actual complete-source
projected radial equation are now proved in seven further leaves. Their
proof admits the physical vertical derivative, transports the full cutoff
product rule through the native chart, and dominates both commutator
terms. See the [radial equation proof and scope](hb-physical-response-radial-equation.md).

The actual Dirichlet endpoint is also proved from the original completed
radial graph; see the [endpoint proof](hb-physical-response-dirichlet-endpoint.md).
Equality to the original radial Green solution remains to be proved. Meromorphic
continuation of that same observable, physical adjoint residue,
complete-source pole survival, spin-two/AIME reconstruction, and
independent Hawking-clock extinction also remain open.

## Lean leaves

All seven modules are under `GaloisForLFunctions.RHTower`, prefixed
`ThetaCuspHawkingBM`:

- `JointCoreTestData`: full modular Green identity and actual radial tests.
- `JointCoreTransposition`: original completed-domain and response equations.
- `JointCoreOperator`: original unbounded operator domain and action.
- `CuspCutoffProfile`: exact scaled derivatives and uniform bounds.
- `ModularCuspCutoff`: quotient support, smoothness, full germs, stabilization.
- `PhysicalCoreCutoff`: actual physical modular field and compact tests.
- `PhysicalCorePairingLimit`: literal pairings, actual response limit, complete compact equation.

## Verification

Each leaf passed a scratch `lake env lean` check and its individual
`lake build <module>` final audit, without warnings. The final audits
used existing dependency caches; no umbrella or full build ran.
`#print axioms` checked only the 44 new public declarations: each uses
only `propext`, `Classical.choice`, and `Quot.sound`. No numerical proof
result, added axiom, or proof placeholder is present. All seven source
files and their checked olean/ilean artifacts were hash-verified during
installation; the seven leaves are wired into `RHTower.lean`.
The corpus index was refreshed once. `scripts/formal_tools.py lint
--check-generated` passed, with existing large-file warnings only;
the seven new leaves total 623 lines. `git diff --check` passed for the
edited tracked documentation and umbrella.
