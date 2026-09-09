# HB: original physical response Dirichlet endpoint

Status: formalized in eight individually audited leaves: 23 public
theorems, six definitions, and one carrier abbreviation. RH remains open.
Frontier map is read-only.

Chain: theta cusp → Xi occurrence → complete native source → original
outgoing response and physical adjoint residue → independent Hawking-clock
extinction → RH.

## Closed endpoint

For the original complete cusp response U and physical angular target r,
the already constructed radial value is R=P_r(yU). On
`3/2 < Re w < 2`, `Im w != 0`, its actual radial derivative component
also admits multiplication by y. Set D=P_r(y U_t). The pair (R,D)
belongs to the closure of the original pairs (f,f'), where f is smooth
and compactly supported strictly inside the negative tortoise half-line.

Consequently R has a continuous representative `physicalCuspProfile`
with value zero at t=0 and

```text
lim_(t -> 0 from below) physicalCuspProfile(t) = 0.
```

It equals the original physical response almost everywhere in the
original radial measure. The value is derived from the original domain;
no endpoint, derivative-admission, or replacement-solution premise is
supplied to the actual-response theorem.

## Weighted graph estimate

Write a=Re w, b=Im w, M_N for the original bounded cusp multipliers,
M_infinity for their limiting weight, and

```text
K = a |w| / ((a^2+b^2)(a^2-9/4)),
B = ||M_infinity F||,       V = K B,
X_N = ||jointCuspWeight_N U||.
```

The original weighted mass estimate gives `||M_N U||<=V`. The full
rotated energy identity retains X_N, its vertical component d_N, and
the logarithmic-slope term r_N. Their bounds are
`||r_N||<=(3/2)V` and `||d_N||<=X_N`. Since a>3/2, the nonnegative
mass term in that identity may be discarded, leaving

```text
a X_N^2 <= |w| V B + (9/4) a V^2 + 3 |b| V X_N.
```

The square `(a X_N-3 |b| V)^2>=0` absorbs the mixed term. It supplies a
uniform bound for the whole original weighted graph. In particular the
radial component `M_N U_t` is uniformly L2 bounded. The actual multiplier
limit and Fatou estimate admit `M_infinity U_t`; the existing height
comparison then admits `y U_t`.

B is the norm of the full limiting cusp weight, including its constant
part. It is not replaced by `||yF||`. The already proved height admission
of the complete source supplies finiteness of this B internally.

## Transporting the original boundary domain

For every angular L2 vector g, tensor insertion h↦h tensor g is bounded.
Its adjoint contracts the first two components of the original joint
energy graph to a radial value/derivative pair. On each joint core, that
pair is exactly a scalar multiple of an original (f,f') pair. Continuity
and closedness therefore put every such contraction in the closed radial
Dirichlet graph.

Apply this to the previously constructed compact angular fields
`g_n=chi_(n+1) conjugate(E_r)`. The earlier physical pairing limit applies
both to U and to its now admitted radial derivative U_t. Thus the two
contracted components converge weakly to R and D. The original closed
radial subspace is the orthogonal complement of its orthogonal complement;
testing that equality proves the limit pair remains in it. No boundary
information is inferred from the interior equation alone.

## Literal trace from the completed graph

Zero extension of an original compact radial core equals its original
whole-line function, and the same holds for its derivative. Hence its
distributional derivative is the zero extension of f'. The corresponding
continuous linear constraint remains zero on the completed radial graph:

```text
partial_t ZR = ZD
```

as actual tempered distributions. In particular no boundary delta appears.
Both ZR and ZD are L2 classes. A reusable real-line Sobolev theorem now
proves that u and its first derivative in H^s imply u in H^(s+1): the
second derivative lies in H^(s-1), and the existing Laplacian gain supplies
the remaining two orders. Applied at s=0, this gives ZR in H^1.

The corpus's Sobolev representative theorem supplies a continuous
whole-line representative. Its zero extension vanishes almost everywhere
on [0,infinity); continuity makes that equality pointwise, including t=0.
Restriction to the original half-line gives the literal physical trace.

## Exact remaining scope

The original physical response now has its radial L2 value, admitted
radial derivative, complete distribution equation, original Dirichlet
graph membership, and actual zero endpoint trace. Equality with the
original complete-source endpoint Green integral is now proved on the
positive-frequency overlap; see the [endpoint identification](hb-physical-response-endpoint-green-identification.md).
For the same source and target copy, [continuation to both fundamental QNMs](hb-physical-self-response-continuation.md) is also proved. Physical
adjoint residue, complete-source pole survival, spin-two/AIME reconstruction,
and independent Hawking-clock extinction remain open. This result does
not prove RH.

## Lean leaves and verification

Seven modules are under `GaloisForLFunctions.RHTower`, prefixed
`ThetaCuspHawkingBM`:

- `CuspWeightGraphBound`: full original weighted graph estimate.
- `PhysicalRadialAdmission`: actual radial derivative height admission.
- `RadialDirichletGraph`: original closed radial domain, contraction, weak closure.
- `PhysicalRadialDirichletDomain`: actual physical value/derivative pair in that domain.
- `RadialDirichletZeroExtension`: original distributional derivative of the zero extension.
- `RadialDirichletTrace`: Sobolev admission and literal boundary trace.
- `PhysicalResponseEndpoint`: continuous actual physical representative and endpoint limit.

`GaloisForLFunctions.HTGeometry.RealSobolevDerivativeGain` supplies the
reusable real-line Sobolev gain. The eight leaves total 465 lines.
Each passed a scratch `lake env lean` check and an individual
`lake build <module>` final audit without warnings, using existing
dependency caches. The axiom check covered only the 30 new public
declarations; each uses standard Lean axioms or none. No numerical
experiment, numerical proof certificate, new axiom, or placeholder was
used. All eight sources and sixteen audited olean/ilean artifacts were
hash-verified during installation. Both area umbrellas are wired;
neither an umbrella build nor a full build ran.
One corpus index refresh completed. `scripts/formal_tools.py lint
--check-generated` passed with existing large-file warnings only.
`git diff --check` passed for the edited tracked documentation and umbrellas.
