# Before There Was Time: the finite-rank no-interaction theorem

- **ID:** `before-time-finite-rank-no-interaction`
- **Stage:** 1-in-progress
- **Type:** THEOREM / HYPERTRANSCENDENCE / MATRIX PRINCIPAL SYMBOLS / CAUSAL GEOMETRY
- **Scientific status:** `[LEAN-PROVEN SYMBOL THEOREM] [ACTUAL SELECTED-JET INTERPRETATION WITHDRAWN] [GAMMA DETERMINANT NO-GO ONLY]`
- **Paper lane:** *Before There Was Time: Hypertranscendence, Quantum Curvature, and the Holographic Horizon*
- **Statement:** Every regular exact-flat finite-rank matrix-symbol tower is a
  static commutative observable algebra up to gauge. If its first symbol is linear, its geometric
  determinant horizon is a finite hyperplane arrangement. Noncommutative or irreducibly curved
  horizons require principal curvature or infinite rank.

> **Anti-theatre correction.** For an actual selected-derivation jet tower over one common
> algebraically independent source, the zeroth jet is law-independent. This forces the zeroth
> symbol to be constant; regular coefficient flatness then forces every symbol to be
> law-independent and the dependence horizon to be empty. A law-linear zeroth symbol is already
> incompatible with regularity. Thus the finite-hyperplane result below remains a correct
> symbol-classification theorem but is vacuous under its earlier actual-jet hypotheses. The
> corrected theorem and curvature consequence are isolated in
> `before-time-hypertranscendence-discriminant-forces-curvature.md`.

## 1. Exact abelian-gauge classification `[LEAN SOURCE-CHECKED]`

Let

```text
S_n(A) : K^r -> K^r
```

be the coefficient-oriented principal symbols of a varying-derivation lower law. Assume

```text
S_n(B) S_(n+1)(A) = S_n(A) S_(n+1)(B)                 (F)
```

and one reference law `e` with `det S_n(e) != 0` for every `n`. Define

```text
T_n(A) = S_n(e)^(-1) S_n(A).
```

Then `(F)` implies

```text
[T_n(A), T_n(B)] = 0                                    (A)
```

for every `n,A,B`, and

```text
T_(n+1)(A) = S_(n+1)(e)^(-1) T_n(A) S_(n+1)(e).        (G)
```

Conversely, a static commuting family `T_0(A)` and an arbitrary sequence of invertible gauge
matrices generate a flat tower by `(G)`. Hence

```text
regular coefficient-flat tower
  iff
static abelian matrix family + invertible gauge sequence. (C)
```

The unconditional theorem `regular_matrixCoefficientPrincipalSymbolFlat_iff_abelianGauge` and
its transport, commutation, reconstruction, and curvature-obstruction lemmas are in
`formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolAbelianRigidity.lean`.

## 2. The law of the external source `[LEAN SOURCE-CHECKED]`

The source packet in the principal-symbol theorem is not a hidden generator. If every `S_n(A)` is
nonsingular, every finite lower-law transformation is invertible, so

```text
target complete jet packet is algebraically independent
  iff
ancestral source packet is algebraically independent.   (H)
```

Thus regular finite-rank evolution cannot create hypertranscendence. It transports ancestral
independence; a singular horizon may destroy it. This is the exact constraint on the datum that
had previously been supplied externally.

`matrixPrincipalPacket_ancestral_independence_iff` and
`matrixPrincipalLowerLaw_ancestral_independence_iff` are unconditional in
`formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolAncestralConservation.lean`.

## 3. Hyperplane collapse `[LEAN-PROVEN]`

Assume `K` is algebraically closed and the first symbol `A |-> S_0(A)` is linear. By `(A)`, the
normalized family `T_0(A)` is commuting and therefore simultaneously upper triangular. Its
diagonal entries are linear characters `lambda_j : g -> K`. Consequently

```text
det S_0(A) = det S_0(e) product_j lambda_j(A),
```

with multiplicity, and the complete hypertranscendence horizon is

```text
H = union_j ker lambda_j.                                (P)
```

The basis-free theorem is formalized in
`formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolAbelianSpectrum.lean`: every ordinary
generalized eigenspace is exactly the sum of the joint sectors over the matching character fiber,
the joint sectors span and are independent, and there are at most `r` nonzero joint characters.
Every supported character is then proved linear on law space.

`regularFlatLinearPrincipalSymbol_hyperplaneHorizon` in
`formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolHyperplaneHorizon.lean` gives the exact
basis-free form of `(P)`:

```text
det S_n(A) = 0
  iff
some supported joint linear character vanishes at A,

number of supported characters <= r.
```

The same file proves the horizon-capacity bound: a finite set of singular laws on which no one
supported character can vanish twice has cardinality at most `r`.

This corrects the unrestricted determinantal picture. A nonlinear determinant polynomial can be
written before flatness, but a regular exact-flat linear pencil cannot retain an irreducible
nonlinear geometric horizon.

## 4. Causal chamber `[LEAN SOURCE-CHECKED]`

Over `R`, let the first symbol be a real-linear matrix pencil and define

```text
C = {A | S_0(A) is positive definite}.
```

Then `C` is convex, every `A` in `C` has `det S_0(A) != 0`, and the exact varying-derivation
horizon theorem gives

```text
C is contained in the hypertranscendental law phase.     (T)
```

These results are unconditional in
`formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolCausalChamber.lean`.

Under the symmetric definite hypotheses of `(P)`, `C` is the chamber

```text
lambda_j(A) > 0 for every j.
```

Selection of a time orientation is therefore selection of one chamber of the pretemporal
hypertranscendence phase.

## 5. Physical content `[ACTUAL GAMMA NO-GO LEAN-PROVEN] [CHERN--SIMONS EXTENSION OPEN]`

The finite-rank theorem is a no-interaction result. If reflection positivity supplies a positive
reference pencil, `(T)` selects a causal chamber. Exact flatness forces its normalized observables
to commute. A genuinely quantum realization with noncommuting observables must therefore have
nonzero principal curvature or pass to an infinite-rank completion.

There is now an unconditional natural special-function realization of the obstruction. The entire
reciprocal Gamma function has zeros at every nonpositive integer. Homogenize them as the laws

```text
g_m = (1,-m) in C^2.
```

A nonzero linear functional on `C^2` vanishes on at most one `g_m`. The horizon-capacity theorem
therefore implies

```text
no finite-rank regular coefficient-flat linear principal tower
can have determinant zero set equal to the reciprocal-Gamma boundary.       (Q)
```

`not_matrixCoefficientPrincipalSymbolFlat_of_reciprocalGamma_horizon` proves `(Q)` for the actual
mathlib Euler Gamma function in
`formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolGammaInfiniteRank.lean`.

The Chern--Simons target is concrete. Mkrtchyan--Veselov identify the analytic continuation of the
Cartan--Killing volume of `SU(N)` with the Barnes `G`-function, and universal Chern--Simons theory
identifies its nonperturbative sector essentially with inverse gauge-group volume. Barnes `G` has
the same infinite negative-integer divisor ladder, with growing multiplicities. Thus the paper
corollary should say that an exact principal-symbol realization of the analytically continued
nonperturbative `SU(N)` Chern--Simons sector is curved or infinite-rank. This application remains
open until the Barnes `G` divisor and the precise normalization/zero-versus-pole orientation are
formalized in Lean; it is not yet promoted as a theorem about QFT.

## 6. Many-worlds topology `[CONJECTURE BEYOND THE FINITE THEOREM]`

At finite rank, `(P)` cuts law space into finitely many sign/argument chambers. These are the only
possible world sectors of an exact-flat model. Curvature can replace the arrangement by an
irreducible determinantal hypersurface with nonabelian monodromy; infinite rank can produce an
infinite arrangement or a completed spectral boundary. The proposed quantum superverse is the
curved or completed branch, not the abelian finite truncation.

## 7. Anti-theatre and novelty gate

Flat connections being locally pure gauge, simultaneous triangularization of commuting matrices,
positive-definite convex cones, and invariance of algebraic independence under invertible linear
changes are established mathematics. None is claimed as new.

The candidate new result is their forced conjunction for the **ordinary differential-algebraic
dependence spectrum as the derivation law varies**:

```text
exact lower law + regular finite rank + flatness
  => ancestral conservation + abelian gauge classification
  => finite hyperplane hypertranscendence horizon.
```

Searches in parametrized differential Galois theory, hypertranscendence of difference equations,
Spencer integrability, matrix-pencil theory, simultaneous diagonalization, and discrete
zero-curvature systems found the ingredients but no theorem with this dependence-spectrum
conclusion. This is an absence-of-hit verdict, not a priority claim. The actual reciprocal-Gamma
obstruction supplies a natural infinite-divisor carrier. Scientific significance now depends on
completing the topological-QFT application rather than on finding a carrier in principle.

## 8. RH impact

Any exact-flat finite-rank completed-`L`-function law model can encode only a finite arrangement of
linear law walls and cannot create its algebraically independent source by regular transport. A
model intended to encode individual zero geometry must therefore supply an external independent
source, nonzero curvature, or infinite rank. This is a route constraint, not an RH proof.

## 9. Gates

- [x] prove normalized abelian rigidity and noncommutativity-forces-curvature
- [x] prove the full abelian-gauge classification and converse construction
- [x] prove ancestral hypertranscendence conservation
- [x] prove convexity and hypertranscendence of the positive causal chamber
- [x] formalize joint generalized-eigenspace spanning and finite character bound
- [x] formalize fiberwise joint spectral decomposition and linear character extraction
- [x] formalize the exact finite hyperplane horizon and horizon-capacity bound
- [x] prove the actual reciprocal-Gamma finite-rank flatness no-go
- [ ] derive coefficient curvature from higher-rank commutator closure
- [ ] formalize the Barnes `G` divisor and the universal `SU(N)` Chern--Simons application
- [ ] complete targeted builds, terminal axiom audit, and lint
- [ ] clear the literature priority gate with a systematic expert-level audit
