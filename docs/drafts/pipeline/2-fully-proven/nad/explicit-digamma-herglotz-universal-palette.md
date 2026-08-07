# Explicit digamma Herglotz universal palette

- **ID:** `explicit-digamma-herglotz-universal-palette`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM / EXPLICIT REALIZATION
- **Scientific status:** `[EXPLICIT HERGLOTZ CONSTRUCTION FORMALIZED; JOINT GAMMA-SHIFT INDEPENDENCE NOT YET FORMALIZED] [NOVELTY UNVERIFIED]`
- **Target paper:**
  `../4-publication-ready/universal-constraint-orientation-product-law/main.tex`

## Constraint

The residual prime-log Cauchy phase proves existence of a universal Herglotz translation palette,
but does not exhibit one point of that phase.  The objective is to remove the residual choice
inside the Herglotz realization itself, without claiming novelty for classical Gamma-shift
hypertranscendence.

## Explicit source and palette

Let `c : script-U -> N` be the explicit injective code already used by the prime--Dirichlet
realization, with `c(emptyset,0)=0`, and put

```text
alpha_q = 1 / (c(q) + 2),
alpha_0 = 1/2,
s(q) = alpha_q - 1/2.
```

Then the `alpha_q` are distinct points of `(0,1)`, hence distinct modulo `Z`.  Define

```text
g_star(z) = digamma(z+1/2) + EulerGamma.
```

Its explicit palette is

```text
g_star(z+s(q)) = digamma(z+alpha_q) + EulerGamma.
```

## Classical input

Hardouin, Compositio Math. 144 (2008), Corollary 4.4, proves hyperalgebraic independence of finite
families of Gamma translates whose periodic divisors are integer-linearly independent.  Distinct
classes `alpha_q mod Z` give independent point divisors.  Passing to logarithmic derivatives is a
triangular rational jet substitution, so every finite family

```text
digamma(z+alpha_q)
```

is differentially algebraically independent over `C(z)`.  Dependence is finitary, hence the entire
countable palette is independent.  This is an application of an established parent theorem, not
an original hypertranscendence claim.

## Herglotz law

Gauss's series gives, locally normally off the pole lattice,

```text
g_star(z) = sum_(n>=0) [1/(n+1) - 1/(n+z+1/2)].
```

For `Im z>0`, every nonconstant summand has positive imaginary part

```text
Im(-1/(n+z+1/2)) = Im(z) / |n+z+1/2|^2 > 0.
```

Thus `g_star` is Herglotz.  Its poles are `lambda_n=-n-1/2`, each with residue `-1`.

Choose a bijection `nu : Primes -> N`.  For a finite reversed set `J`, put

```text
g_(star,J)(z)
  = g_star(z) + 2 sum_(p in J) 1/(z + nu(p) + 1/2).
```

This is a rational gauge.  Therefore every translated chamber palette remains differentially
independent and generates the same embedded field as the all-positive palette.  The source is
Herglotz exactly for `J=emptyset`: at a reversed pole the residue changes from `-1` to `+1`, and
the imaginary part tends to `-infinity` on vertical approach.

## Infinite orientation

For an arbitrary sign sequence `epsilon : Primes -> {+1,-1}`, define

```text
g_epsilon(z)
  = sum_(n>=0) epsilon(n)
      [1/(n+1) - 1/(n+z+1/2)].
```

The summands are locally uniformly `O(n^-2)`, so the series is canonical and independent of
exhaustion.  Its residue at `-n-1/2` is `-epsilon(n)`, and it is Herglotz exactly at the all-positive
orientation.  Finite chamber truncations converge locally normally to `g_epsilon`.

The infinite boundary has an exact two-scale law.  The summable-residue completion theorem makes
the compact-open common-atom Cauchy algebra independent of every source and every finite or
infinite orientation.  At the stricter raw level, the separate prime--Dirichlet tail theorem says
that two complete palette fields coincide exactly under eventual equality or eventual opposition;
all other tail directions are transverse.  Thus arbitrary infinite `epsilon` is classified rather
than left outside the theorem, without conflating raw fields with their analytic completion.

## Scientific geometry

The classical ingredients are:

- Gamma-shift hyperalgebraic independence;
- the Gauss digamma series;
- rational-gauge field invariance;
- local residue detection of Herglotz failure.

The candidate new contribution is their product geometry: one explicit Herglotz source supports
every finite Stanley--Reisner differential matroid in every finite orientation chamber, the full
orientation inverse limit has explicit signed digamma representatives, and a second arithmetic
realization exactly stratifies its infinite field coordinate.

## Gates

- [x] explicit source and injective real palette isolated
- [x] classical joint-independence parent located precisely
- [x] paper proof of Herglotz and finite rational-gauge laws
- [x] paper proof of normally convergent arbitrary orientation representatives
- [x] exact infinite signed Herglotz law, including normally convergent deleted-pole backgrounds
- [x] formalize the new source-specific positivity and finite/cofinal sign cores from the classical
  Gamma-shift input boundary
- [x] integrate into the journal manuscript and rebuild the PDF
- [ ] complete novelty/significance audit of the combined geometry

## Internal proof surface

`formal/GaloisForLFunctions/HTGeometry/ExplicitDigammaHerglotzPalette.lean` proves the strict
upper-half-plane positivity of the closed-form source, injectivity and integer incongruence of the
palette points, the exact finite Herglotz chamber law, absolute summability of every bounded signed
Gauss completion, and convergence of its canonical finite partial sums.  Joint differential
independence begins at the stated classical Hardouin theorem boundary.

`formal/GaloisForLFunctions/HTGeometry/ExplicitDigammaOrientationLimit.lean` proves local normal
convergence and holomorphy of every deleted-pole background, exact atom--regular splitting for
arbitrary Boolean tails, and the unconditional equivalence

```text
signed Gauss completion is Herglotz <-> every orientation coordinate is positive.
```

## Literature boundary

- Charlotte Hardouin, *Hypertranscendance des systemes aux differences diagonaux*, Compositio
  Math. 144 (2008), 565--581, especially Theorem 4.2 and Corollary 4.4.
- Hardouin--Singer, *Differential Galois Theory of Linear Difference Equations*, Math. Ann. 342
  (2008), 333--377, for the parameterized difference-Galois framework.

## Authoritative Lean audit

The source-specific theorem surface is axiom-clean.

- `ExplicitDigammaHerglotzPalette.lean` proves strict upper-half-plane positivity, injectivity and
  integer incongruence of the explicit palette, exact finite-orientation Herglotz classification,
  pointwise absolute convergence, the off-pole Gauss-series identity on the full plane, and exact
  identification of the all-positive completion with the shifted-digamma source. It also proves
  `explicitDigammaPalette_collisionMatroid_eq_free`: the actual mathlib collision matroid of the
  closed-form palette is the free matroid.
- `ExplicitDigammaOrientationLimit.lean` proves global compact-local normal convergence of every
  bounded signed completion, upper-half-plane holomorphy, deleted-pole regularity and atom splitting,
  and the exact infinite Boolean Herglotz equivalence.
- The finite rational-gauge differential-field and Stanley--Reisner consequences are formalized in
  `UniversalConstraintOrientation.lean` and `UniversalOrientedConstraintProduct.lean`. The
  Hardouin joint Gamma-shift independence result remains the explicitly cited classical parent
  boundary; no project axiom is introduced for it.

Targeted builds of both explicit digamma modules, `#print axioms` on the finite, infinite,
normal-convergence, source-identification, and Herglotz capstones, and the repository formal lint
pass. No full build was run.
