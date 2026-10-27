# Corner flux of smooth modular boundary data

- **ID:** leftovers-twisted-corner-flux
- **Stage:** 1-in-progress
- **Type:** FALSIFIED ancillary estimate; explicit boundary-jet classification
- **Source:** [twisted minimum principle](../2-fully-proven/leftovers/twisted-minimum-principle.md), input (C1).
- **Statement:** Smooth boundary data do not force the Dirichlet extension's flux to vanish at the modular corner.

## Exact obstruction

Let `y₀=√3/2`, `P=(1/2,y₀)`, `k=4π` and
`W(u,y)=K₀(ky) cos(ku)`. This is an even, one-periodic,
bounded solution of `div(y∇W)=0` on the fundamental strip, smooth in an
open neighborhood of its closure at every finite height. Its trace is
admissible smooth even boundary data. Uniqueness in (C1) therefore makes
its bounded Dirichlet extension exactly `W`.

The radial normal derivative on the unit arc is

`F(u)=-k u K₀(k y(u)) sin(ku)-k y(u) K₁(k y(u)) cos(ku)`,
where `y(u)=√(1-u²)`. It extends continuously to the corner and

`F(1/2)=-4π y₀ K₁(4π y₀)<0`.

Multiplying by the positive conormal weight `y(u)`, or reversing normal
orientation, cannot make this limit zero. Hence the assertion in (C1)
that every smooth datum has flux `O(r^(1/2))` is false. Here `r` can be
Euclidean distance to `P` or any equivalent corner coordinate. The
nonzero limit is incompatible with every positive power of `r`.

## Positive survivor and exact correction

The obstruction identifies the missing boundary jet. Every finite
Whittaker sum has the exact endpoint flux

`-y₀ Σ_m a_m (2πm) K₁(2πm y₀) (-1)^m`.

Thus vanishing corner flux is a specific linear constraint on coefficients,
not a consequence of smoothness. The precise identity, its continuity,
and the single-mode strict sign will be formalized against the actual
`kMoment` Bessel integral and actual radial derivative. No assumed
Dirichlet producer is needed for these identities.

There is also a general geometric classification. For any smooth even
periodic extension, `W_u(P)=0`. Its trace derivative is
`g'(1/2)=-(1/(2y₀))W_y(P)`, whereas its radial derivative is
`F(P)=y₀W_y(P)`. Hence `F(P)=-(3/2)g'(1/2)`. Corner flux vanishes
exactly when the trace has zero endpoint derivative. Here smoothness
means ordinary smoothness on the closed arc, as for the actual growing
trace `J|A`; imposing a periodically matched trace derivative at the
glued corner would be an additional boundary-jet restriction.

For the main potential construction the appropriate regular remainder is
`J-D_(J|A)`, which has zero boundary trace. The homogeneous corner law
(C3), rather than the false flux statement for `D_g` itself, gives its
`O(r^(1/2))` flux. This preserves the intended main theorem. Proving the
global Dirichlet/ Martin producers, the homogeneous corner expansion,
Green regularization and uniqueness remains part of the full programme.

## Proof dependencies and status

Corpus search and source inspection locate `WhittakerStreamFunction`
(`hasDerivAt_kMoment_comp_mul`, `kMoment_two_eq`),
`WhittakerStreamCorner` (actual corner height), and the underlying
positive Bessel integral. The elementary derivative and finite-sum
identities above are dependency-closed paper calculations. Lean audit
is pending. The counterexample is not yet a promoted no-go, and the
original card is not retired or marked fully formalized.

The full strip admissibility proof must additionally certify actual
boundedness, periodicity, evenness and the equation for `W`; it must not
replace those with assumption fields. The final failure of the (C1)
estimate is a consequence of the explicit admissible witness and its
nonzero continuous flux limit.

The scratch draft `/tmp/leftovers_whittaker_corner_flux.lean` contains
29 declarations: smoothness of all actual Bessel moments, actual mode
smoothness/evenness/periodicity, literal first and second derivatives and
the axisymmetric equation, a bound on the whole modular strip, exact
the general even-periodic corner-jet identity, exact single/finite-mode identities, and failure of the square-root
distance estimate for the literal radial derivative. The draft is not
certified. Its first source/axiom check (session 9319) found three
elaboration errors in a reflected derivative, a product curve and a
continuity composition. Smoothness, boundedness, the literal PDE, trace
derivatives and all finite-mode endpoint identities already had standard
axioms. Explicit compositions and conversions address these errors; the
revised full audit was cancelled after the user cleared the goal
(session 61715, exit 143). Fixes remain unchecked. The draft is preserved
in [the checkpoint](leftovers-formalization-checkpoint/WhittakerCornerFlux.lean.draft). This is a classical
calculus correction, with no claim of scientific novelty.
