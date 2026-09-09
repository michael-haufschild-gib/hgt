# Original Maass slice rigidity and strict slice mass

Status: dependency-closed paper proof and complete Lean audit passed.
RH remains open. Frontier map is read-only.

## Exact original-source statements

Let f be the original nonzero principal-congruence Maass cusp eigenform,
with real eigenvalue λ and period w=N+1. Let aₙ(y) be its actual Fourier
coefficient, M(y) its normalized squared slice mass, and Φ(y) its outgoing
vertical flux. No independent coefficients or boundary data are supplied.

For every real λ:

1. Zero value and first height derivative of one aₙ at a positive height
   force that coefficient and derivative to vanish at every positive height.
2. M(y)=0 if and only if f vanishes on the whole horizontal line at height y.
3. Every positive height has a nonzero original modal Cauchy pair.
4. Every nonempty open positive-height band contains a nonzero source
   value and a slice with M(y)>0.

For 0<λ<1/4:

5. Every cusp tail has strictly positive hyperbolic mass:

       ∫_Y^∞ M(y)/y² dy > 0,  for every Y>0.

6. Every horizontal slice has M(y)>0. In particular, a whole zero slice is
   impossible even without assuming its normal derivative vanishes.
7. Every compact positive-height band has a source-dependent d>0 with
   M(y)≥d throughout the band.
8. The full congruence trace D has a positive point in every unit period at
   every positive height. Original zero means then give two positive-density
   directions at that height whose squared normalized chord exceeds two.

Statements about an exceptional source retain its actual eigenform data;
they do not assert that such an eigenform exists.

## Complete proof

The defining Maass PDE already gives the actual modal equation

    aₙ''(y) = (kₙ² − λ/y²) aₙ(y),   kₙ=2πn/(N+1).

The coefficient is continuous on y>0. To propagate zero Cauchy data from Y
to any y>0, parameterize the segment by p(t)=Y+t(y−Y), 0≤t≤1, and use
the state W(t)=(aₙ(p(t)),aₙ'(p(t))). Compactness supplies a bound C on the
scalar coefficient. With the product norm,

    ||W'(t)|| ≤ |y−Y|(1+|C|) ||W(t)||.

Actual derivative composition and Grönwall give W=0 from W(0)=0. The affine
path handles both height directions without any assumed ODE solution
formula.

Actual Parseval identifies M with Σ|aₙ|². If all coefficients vanish at a
height, M=0. Conversely, continuity and nonnegativity of |f|² show that zero
mass forces zero values on the closed fundamental period; actual
periodicity extends this to the full line. If all modal Cauchy pairs
vanished at one height, their propagated coefficients would vanish at all
heights, so Parseval would make the original nonzero eigenform zero. Thus
every height has a nonzero Cauchy pair. If the physical source vanished on
an open height band, every coefficient would vanish on that band; at its
midpoint both coefficient and derivative would vanish. This is impossible.

For an exceptional source, the existing source estimates give integrability
of M(y)/y² on each cusp tail. If its nonnegative tail integral were zero,
the function would vanish almost everywhere there. Continuity upgrades
this to vanishing at every height of the open tail. The preceding band
nonvanishing theorem gives a contradiction. Therefore the tail mass is
strictly positive for every lower height.

Now suppose one entire horizontal slice at height Y is zero. Its original
Fourier coefficients are all zero, so the actual Bessel boundary form B(Y)
is zero. The outgoing flux Φ(Y) is zero as well: every Hermitian product
contains the zero source value, irrespective of its normal derivative.
The already proved full source boundary-square identity is

    −Φ(Y) + (λ−1/4) ∫_Y^∞ M(y)/y² dy = B(Y) + Σₙ Rₙ(Y),
    Rₙ(Y) ≥ 0.

The left side is strictly negative and the right side nonnegative, a
contradiction. This proves M(Y)>0 at every positive height. Continuity and
compactness give a positive minimum on each fixed compact height band.

Finally, the identity coset gives |f(z)|²≤D(z). Nonzero original values on
each height therefore give a positive trace point. Unit periodicity of D
moves it into [0,1]. The existing original-source negative-correlation
theorem, now with this produced positive base point at each height, gives
the separated positive-density directions.

## Consequences and remaining distinction

The source cannot disappear completely on a line or a cusp tail in the
exceptional case. The positive compact floor controls integrated squared
mass, not the minimum of D along a horizontal line. Common zeros and the
common flat-node alternative from zero current remain unexcluded. A band
of zero current is therefore still not contradicted by these results.

No generic elliptic unique continuation, analyticity, explicit Bessel
solution representation, positive boundary form on arbitrary traces,
numerical certificate or conjectural spectral premise was used. The
uniform quotient-area quarter comparison and independent full-Xi
occurrence remain open; the full SQB candidate is retained.

## Broad corpus discovery

All searches used the repository research tool with OR matching, no
per-module cap and complete declaration-result retrieval:

- PDE rigidity, unique continuation, elliptic, nodal and maximum-principle
  terms: 3,217 rows in 390 modules.
- Maass, spectral gap, Hardy inequality, ground state and quarter:
  2,772 rows in 685 modules.
- Harnack, Hopf lemma, Kato, mode uniqueness, decaying solution and Bessel
  positivity: 64 rows in 25 modules.
- Slice nonzero/positive, zero trace, Cauchy, height rigidity, vanishing
  slice and Dirichlet: 10,191 rows in 2,571 modules.

These are metadata counts, not claims that every proof was inspected.
Selected source reads covered actual Maass Fourier/Parseval, flux, tail
energy and Bessel boundary identities, complex source nonvanishing, finite
trace positivity and direction separation. The arithmetic exponential-mode
and wave Cauchy results did not supply a Maass PDE uniqueness theorem.
Mathlib Grönwall, derivative composition and equality of continuous
functions from almost-everywhere equality supplied the needed general
tools. Outputs: `/tmp/sqb21_{pde,coercivity,uniqueness,slice}_broad.json`.

## Lean audit

Module: `GaloisForLFunctions.RHTower.SelbergMaassSliceRigidity`.
It contains 20 public declarations: 19 theorems and one scalar-potential
definition. Main results:

- `maassCoefficient_cauchy_zero`
- `exists_nonzero_in_height_band`
- `hyperbolic_tail_mass_pos`
- `exceptional_not_zero_slice`
- `exceptional_slice_mass_pos`
- `exceptional_compact_slice_mass_floor`
- `exceptional_separated_directions_every_height`

Scratch passed without warnings: `/tmp/sqb21_slice.lean`,
`/tmp/sqb21_slice.log`. Canonical source check
`lake env lean GaloisForLFunctions/RHTower/SelbergMaassSliceRigidity.lean`
also passed without warnings (`/tmp/sqb21_slice_source.log`).

Preflight found only the intended leaf stale. Final audit
`lake build GaloisForLFunctions.RHTower.SelbergMaassSliceRigidity` passed,
compiling only that module in 3.6 seconds. Other jobs in the 8,821-job
dependency graph were cached. No umbrella or full build ran. Logs:
`/tmp/sqb21_slice_preflight.log`, `/tmp/sqb21_slice_build.log`.

All 20 declarations were individually checked in `/tmp/sqb21_axioms.lean`;
all axiom inventories contain only `propext`, `Classical.choice`, and
`Quot.sound` (`/tmp/sqb21_axioms.log`). No proof hole, added axiom, unsafe
declaration or external computation was introduced. The module is wired
once into `RHTower.lean`, and all 20 declarations are indexed exactly once
in `/tmp/sqb21_indexed_declarations.json`. Index and formal lint passed
(`/tmp/sqb21_index.log`, `/tmp/sqb21_lint.log`), with existing unrelated
large-file warnings. Whitespace checks passed; no owned Lean/Lake process
remains. This work made no edits to the read-only frontier map.
