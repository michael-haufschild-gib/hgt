# CCM Euler--essential boundary-layer correspondence

- **ID:** `ccm-euler-essential-boundary-layer-correspondence`
- **Stage:** 1-in-progress
- **Type:** THEOREM / FRONTIER CORRECTION
- **Scientific status:** `[PAPER PROOF CLOSED] [LEAN-FORMALIZED] [TARGET BUILD PASSED] [CORPUS-NEW] [EXTERNAL NOVELTY OPEN] [NOT RH]`
- **Parents:**
  - `ccm-affine-euler-cutoff-fisher-transport.md`
  - `../3-formalized/needs-audit/ccm-essential-cusp-boundary-layer-sharpness.md`

## Exact law

Let

```text
B_u(t)=2 sqrt(2) exp(-t/u),       0<t<=1,
E(u)=integral_(0,1] B_u(t)^2 dt.
```

Normalize `B_u(t)^2 dt` by `E(u)` and use the source coordinate

```text
x=2t/u.
```

For `u>0` and `0<=x<=2/u`, the normalized head energy is exactly

```text
Prob_u(X<=x)
 = [integral_(0,ux/2] B_u(t)^2 dt]/E(u)
 = (1-exp(-x))/(1-exp(-2/u)).                            (EB1)
```

Thus `X` has the unit exponential law conditioned on `0<X<=2/u`.  As `u->0+`,

```text
Prob_u(X<=x) -> 1-exp(-x),       x>=0.                   (EB2)
```

The physical all-integer affine Euler clock already satisfies, as `sigma->1+`,

```text
Prob(X_sigma<=x) -> 1-exp(-x),   x>=0,                   (EB3)
```

and its projective Fisher energy tends to `4`.  The essential cusp energy density also tends to
`4`.  Hence physical affine Euler source and essential Hilbert cusp select same exponential clock
and same four-unit Fisher normalization under canonical scale `x=2t/u`.

The same law is proved directly for actual positive von Mangoldt fixed current.  Put

```text
A(s)=-zeta'(s)/zeta(s),
s_(sigma,t)=sigma-i t(sigma-1).
```

On `sigma>1`, `A` is literally convergent positive prime-power current, and

```text
A(s_(sigma,t))/A(sigma)
 = [sum Lambda(n)n^(-s_(sigma,t))]/
   [sum Lambda(n)n^(-sigma)]
 ->(1-it)^(-1).                                         (EB4)
```

Thus actual CCM prime-power current, affine all-integer source, and essential Hilbert cusp all
select same unit exponential clock.

Taking imaginary parts gives the universal Abel sine law

```text
Im A(s_(sigma,t))/A(sigma) -> t/(1+t^2)>0,   t>0.        (EB5)
```

In particular actual positive von Mangoldt current is eventually aligned at first CCM phase
`t=2*pi`.  Remaining first-clock problem is now sharply a positive de-Abelization problem:
transport `(EB5)` across the invariant half-weight seam from Gibbs/Abel weighting to literal
`Lambda(n)/sqrt(n)` hard aperture while retaining Gamma--polar reflection budget.  This singular
half-weight hard de-Abelization is RH-complete by `(HW6)`; `(EB5)` does not assume it.

The full complex essential boundary-layer response is

```text
H_u(t)
 =[1-exp(-(1-it)2/u)]/
  [(1-it)(1-exp(-2/u))].                                 (EB6)
```

It is the characteristic function of `Exp(1)` conditioned on `x<=2/u`, hence

```text
H_u(t)->(1-it)^(-1),
A(s_(sigma,t))/A(sigma)-H_u(t)->0                        (EB7)
```

under independent limits `sigma->1+`, `u->0+`.  This is full complex response correspondence, not
only equality of scalar mass, CDF, or Fisher energy.

## Proof

Existing exact integration gives

```text
E(u)=4u(1-exp(-2/u)).
```

Subtract tail energy from `ux/2` to `1`:

```text
E(u)-E_tail(ux/2,u)
 =4u[(1-exp(-2/u))-(exp(-x)-exp(-2/u))]
 =4u(1-exp(-x)).
```

Division proves `(EB1)`.  Since `exp(-2/u)->0`, `(EB2)` follows.  `(EB3)` and both four-unit limits
are already unconditional Lean theorems; new theorem connects their exact normalizations.

## Frontier consequence

C39's essential category is not merely an abstract Hilbert-space counterexample.  At clock and
Fisher level it is canonical physical Euler boundary layer.  Therefore no CCM argument using only

```text
critical clock law + first two moments + four-unit Fisher/Ward normalization
```

can exclude essential source transport.  Remaining RH-complete datum is microscopic
von-Mangoldt--Gamma phase, concretely first-clock half-wave inequality `(HW6)`.  Any successful
transport must retain that phase before critical exponential collapse.

This does not prove RH and does not kill CCM.  It closes source-relevance question for essential
survivor and prevents treating essential cusp as unrelated pathology.

## Hostile audit

1. C39 proves cusp existence and endpoint concentration, but does not identify normalized
   boundary energy law.
2. Affine Euler card proves physical clock/Fisher limits, but does not connect them to essential
   cusp.
3. Common appearance of `Exp(1)` is insufficient: `(EB1)` proves exact finite-`u` conditional law
   under canonical geometric coordinate.
4. The theorem contains no source-phase claim.  It cannot orient `(HW6)` and is not presented as
   RH progress beyond frontier localization.

## Gates

- [x] exact paper proof of conditional exponential law
- [x] collision audit against C39 and affine Euler theorem
- [x] formalize `(EB1)` and `(EB2)` in Lean
- [x] formalize actual von Mangoldt current ratio and limit `(EB4)`
- [x] prove universal positive Abel sine response `(EB5)`
- [x] formalize full complex source/cusp response correspondence `(EB6)`--`(EB7)`
- [x] connect physical Euler CDF and both four-unit limits
- [x] wire into `RHTower.lean`
- [x] direct Lean, targeted build, lint, and axiom audit

Audit:

- `lake env lean GaloisForLFunctions/RHTower/CCMEulerEssentialBoundaryLayerCorrespondence.lean`
  passed with no diagnostics.
- `lake build GaloisForLFunctions.RHTower.CCMEulerEssentialBoundaryLayerCorrespondence` passed.
- `scripts/formal_tools.py lint` passed; only pre-existing large-file warnings.
- Capstone declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
