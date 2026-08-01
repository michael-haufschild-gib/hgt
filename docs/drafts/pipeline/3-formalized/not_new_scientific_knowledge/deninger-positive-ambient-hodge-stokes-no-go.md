# Deninger positive ambient Hodge--Stokes no-go

- **ID:** `deninger-positive-ambient-hodge-stokes-no-go`
- **Stage:** 3-formalized
- **Type:** STANDARD CHAIN-LEVEL OBSTRUCTION; NEW ROUTE-L SCOPE CONSEQUENCE
- **Label:** `DAC_POSITIVE_AMBIENT_HODGE_STOKES_NO_GO`
- **Route:** L
- **Parent:** `deninger-gamma-rank-regular-representation`

## Theorem

Let

\[
 E^0\xrightarrow{d_0}E^1\xrightarrow{d_1}E^2,
 \qquad d_1d_0=0,
\]

be an additive three-term complex. Let (J:E^1\to E^1) preserve cocycles, and let
\(\Psi:E^1\times E^1\to\mathbf C\) satisfy strict ambient cup--Hodge positivity

\[
 x\ne0\quad\Longrightarrow\quad
 \operatorname{Re}\Psi(x,Jx)>0.                              \tag{1}
\]

If exacts are in the left Stokes radical against all cocycles,

\[
 d_1z=0\quad\Longrightarrow\quad
 \Psi(d_0a,z)=0,                                             \tag{2}
\]

then

\[
 d_0=0.                                                       \tag{3}
\]

Equivalently, if (d_0a\ne0), then (z=Jd_0a) is a cocycle and

\[
 \Psi(d_0a,z)\ne0.                                           \tag{4}
\]

Thus a strictly positive ambient cup--Hodge form whose Hodge operator preserves cocycles cannot
descend unchanged through any nonzero incoming boundary subspace.

## Proof

For (b=d_0a), the complex identity gives (d_1b=0). Cocycles are (J)-stable, so
(d_1Jb=0). Applying `(2)` with (z=Jb) gives

\[
 \Psi(b,Jb)=0.
\]

If (b\ne0), this contradicts `(1)`. Hence every (d_0a) is zero, proving `(3)`. Conversely, a
nonzero (b=d_0a) makes (Jb) the closed witness in `(4)` by `(1)`.

## Route-L consequence

The positive Gamma-rank regular coefficient has an ambient antiunitary (J), positive coefficient
pairing, and (J)-commuting bar differentials. Those facts do **not** make the ambient coefficient
pairing a cohomological pairing. If the arithmetic incidence differential is nonzero, the theorem
forbids exacts from being the radical of that unchanged positive form.

Required order is therefore:

1. construct nontrivial Rost--Schmid/Milnor incidence in the nuclear source complex;
2. construct adjoint/Green data and harmonic projection (P);
3. define cohomological Hodge on harmonic representatives, for example (PJP), and prove it is an
   odd isometry there;
4. transport cup through harmonic representatives or prove a relative Green form has radical
   exactly the boundary closure;
5. only then complete the positive cohomology quotient.

This is precisely why `DAC_GLOBAL_GREEN_ENERGY_RADICAL` and the conservative full-Cauchy boundary
classification cannot be replaced by Gamma-rank coefficient positivity.

## Positive survivor

There is no obstruction to (J) commuting with the Hodge Laplacian or preserving the harmonic
subspace. Standard Hodge theory uses positivity after harmonic reduction: Hodge star need not
preserve every cocycle in the way assumed above, and the positive inner product is not the raw cup
form on arbitrary cochains. Route L survives only in this harmonic/relative form.

## Hostile audit

- No claim that the Gamma-rank differential is nonzero has been smuggled in; `(3)` is an exact
  conditional classification.
- No quotient is declared positive by choosing representatives.
- No spectral divisor, Xi zero, RH premise, or numerical computation occurs.
- The theorem does not prove the global Green radical law; it proves that law is indispensable.

## Novelty audit

The algebraic argument is standard and is not claimed as new scientific knowledge. Corpus search
found the global Green-radical program and several quotient-positivity warnings, but not this exact
three-term incompatibility stated against the Gamma-rank commuting-Hodge construction. Novelty is
only the Route-L dependency correction.

## Lean formalization

Module:
`formal/GaloisForLFunctions/RHTower/DeningerPositiveAmbientHodgeStokesNoGo.lean`.

Kernel-checked declarations:

- `deningerPositiveAmbientHodge_stokes_forces_boundary_zero` formalizes `(3)`;
- `deningerPositiveAmbientHodge_exists_stokes_defect` formalizes witness `(4)`.

Both theorems are unconditional.  They use arbitrary additive groups and additive differentials;
no analytic, topological, spectral, or RH hypotheses occur.
