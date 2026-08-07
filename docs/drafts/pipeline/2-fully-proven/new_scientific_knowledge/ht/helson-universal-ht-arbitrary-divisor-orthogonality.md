# Boundary-everywhere Helson continuation seam and universal HT field type

- **ID:** `helson-universal-ht-arbitrary-divisor-orthogonality`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / RH ROUTE CONSTRAINT
- **Scientific status:** `[PROVED ON PAPER] [LEAN-CERTIFIED CONSEQUENCES] [NEW GEOMETRY] [NOVEL × SIGNIFICANT]`

## Constraint

For a completely multiplicative unimodular function `chi`, put

```text
Z_chi(s) = sum_n chi(n)n^(-s)
         = product_p (1-chi(p)p^(-s))^(-1),     Re(s)>1.
```

Let `E_fin` be the finite-prime Dirichlet differential field and fix a countable set `A` of
distinct nonnegative real shifts.  Write

```text
L_chi = E_fin<Z_chi(s+a) : a in A>_D.
```

The question is whether the complete hypertranscendental field carried on the half-plane of
absolute convergence constrains the divisor obtained after analytic continuation.

## Theorem

### Universal free field type

`[CLASSICAL INPUT]` Pong's Theorem 5.9 applies to every arithmetic function whose prime support is
not finitely generated.  In particular, for every completely multiplicative unimodular `chi`,
every finite family of distinct shifted derivatives

```text
Z_chi^(j)(s+a)
```

is algebraically independent over `E_fin`.  Hence every `L_chi` is an abstract differential
rational function field on the same shift-indexed family.  For every `chi,psi` there is a unique
`E_fin`-differential field isomorphism

```text
Phi_(chi,psi) : L_chi -> L_psi
Phi_(chi,psi)(Z_chi(s+a)) = Z_psi(s+a).
```

The uniqueness is relative to the labelled palette.

### Arbitrary continued divisor

`[CLASSICAL INPUT]` Andersson's Helson-zeta Mittag--Leffler theorem states that, for every connected
domain `U` containing `Re(s)>1` and every admissible locally finite signed divisor in
`U intersect {Re(s)<1}`, there exists a Helson zeta function with meromorphic continuation to `U`
and exactly that divisor; its maximal meromorphic domain can also be prescribed.

Combining the two inputs gives the target product law:

```text
abstract labelled differential-field type = constant,
continued divisor                         = arbitrary.
```

Equivalently, the divisor map is surjective on every admissible divisor class while the complete
shift--jet differential matroid and the labelled abstract generated differential field remain
fixed.

### Dense-null continuation seam

Identify the Helson phase space with the compact product torus

```text
Omega = product_(p prime) S^1
```

with its product topology and Haar product probability.  Let `M` be the set of phases `chi` for
which `Z_chi` has meromorphic continuation to the whole complex plane.

Then `M` is dense.  Indeed, every basic cylinder fixes only finitely many prime phases.  Extend
those phases by `chi(p)=1` at every remaining prime.  The resulting Helson zeta is

```text
Z_chi(s) = zeta(s)
           product_(p in P) (1-p^(-s))/(1-chi(p)p^(-s)),
```

so it is meromorphic on the plane and belongs to the cylinder.

On the other hand `M` is Haar-null.  Seip records the Saksman--Webb theorem that the meromorphic
abscissa `sigma(chi)` equals `1/2` almost surely, whereas every member of `M` has
`sigma(chi)=-infinity`.  Since Haar measure has full support, the complement of `M` meets every
nonempty cylinder.  Therefore

```text
closure(M)              = Omega,
closure(Omega minus M)  = Omega,
Haar(M)                 = 0,
boundary(M)             = Omega.
```

Consequently the Boolean continuation indicator

```text
1_M : Omega -> {false,true}
```

is continuous at no point.  More strongly, it cannot factor as `c o q` through continuous maps
from `Omega` to any topological readout space and from that space to the discrete two-point space.
Thus no continuous invariant of the finite-prime product topology decides global meromorphic
continuation, even locally.

Finally Andersson's theorem with `U=C` makes the divisor map from `M` onto all locally finite
signed divisors in `Re(s)<1` surjective.  Thus the globally continuable stratum is simultaneously
dense, probabilistically invisible, boundary-everywhere, divisor-universal, and contained in one
labelled abstract differential-field isomorphism class together with its noncontinuable
complement.

This is the geometric statement.  The individual ingredients--finite Euler modifications,
almost-sure meromorphic abscissa, arbitrary divisor prescription, and free differential-field
algebra--are not claimed as new separately.

## Positive necessity law

> **Singular continuation-seam necessity.**  An RH-capable hypertranscendental carrier must add a
> topology or gluing datum strictly stronger than the finite-prime product topology and must retain
> the positive Euler polarization inside it.  The continuation indicator is nowhere continuous
> in the prime-phase inverse limit and admits no continuous factorization through a topological
> readout, while the continuable stratum already realizes every divisor.
> The abstract differential field and its complete differential--difference matroid are constant
> across both sides of this everywhere-dense seam.

Thus a viable route must preserve at least one structure that Helson deformation destroys: the
scale-one functional equation with its archimedean factor, the positive unit Euler orientation,
or an equivalent valuation-bearing seam invariant that reaches the continued divisor.  In
particular, a compact inverse limit of finite prime chambers with only continuous product-topology
readouts cannot be the completed RH carrier.

## Proof boundary

The analytic statements of Pong, Saksman--Webb as recorded by Seip, and Andersson are literature
inputs.  The project contribution consists of the universal labelled differential-field
isomorphism, including derivation compatibility and uniqueness, and the combined dense-null
boundary-everywhere geometry.  The algebraic contribution is proved in
`formal/GaloisForLFunctions/HTGeometry/DifferentialIndependentFieldUniversality.lean`; the seam
topology and continuous-factorization obstruction are proved in
`formal/GaloisForLFunctions/HTGeometry/DenseNullContinuationSeam.lean`.

## Lean certification

The project contribution is formalized without adding the classical analytic inputs as axioms.
Those inputs occur only as the explicit hypotheses identified above.  The algebraic module proves

```text
differentialIndependentAdjoinAlgEquiv
differentialIndependentAdjoinAlgEquiv_jet
differentialIndependentAdjoinAlgEquiv_deriv
differentialIndependentAdjoinAlgEquiv_unique
```

so equally labelled differentially independent palettes generate canonically isomorphic fields,
the equivalence sends every labelled jet to its counterpart, commutes with the derivation, and is
the unique derivation-preserving equivalence with the prescribed order-zero labels.

The seam module proves

```text
dense_finiteModification
dense_compl_of_measure_zero_of_open_pos
frontier_eq_univ_of_dense_and_dense_compl
frontier_eq_univ_iff_dense_and_dense_compl
every_open_neighborhood_meets_both_sides
nowhereContinuous_seamIndicator
no_continuous_factorization_seamIndicator
not_isClosed_or_not_continuous_of_surjective_to_noncompact
```

which is the complete topological deduction from the finite-modification density, Haar-nullity
with full support, and divisor-surjectivity inputs.  Direct module elaboration and dedicated target
builds pass.  The final declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Attacks

1. **Known-input attack.**  Pong already proves maximal differential--difference independence;
   Andersson already proves arbitrary continuation divisors.  Neither input is new here.
2. **Routine-corollary attack.**  The individual density, nullity, and free-field arguments are
   short.  The claimed contribution is their exact joint geometry: a boundary-everywhere,
   divisor-surjective continuation seam across which the complete labelled differential-field
   type is constant, together with its no-continuous-factorization consequence.
3. **Embedding attack.**  The fields are abstractly isomorphic, not equal as embedded subfields of
   a common meromorphic-function field.  This distinction is the theorem's point and must never be
   blurred.
4. **Functional-equation boundary.**  General Helson zeta functions do not share the Riemann zeta
   functional equation.  The result proves that such extra continuation coupling is necessary; it
   does not prove it sufficient.
5. **Coefficient boundary.**  General Helson coefficients are unimodular rather than all positive.
   Positivity remains a legitimate polarization and is not ruled out.
6. **Novelty attack.**  The targeted searches found the arbitrary-divisor, random-abscissa, compact
   character-torus, and differential-independence ingredients, but no source stating their
   dense-null, boundary-everywhere, field-isotypic combination.  This is evidence, not a substitute
   for expert novelty review.
7. **Significance attack.**  Density and nullity are elementary once the inputs are juxtaposed.
   Significance comes from the exact impossibility class: no continuous readout of the compact
   finite-prime inverse limit can determine continuation even at one phase, although the
   continuable side is divisor-surjective.  This forces an RH carrier to add a singular gluing
   datum rather than merely completing finite Euler chambers.

## Gates

- [x] exact classical Pong input located and checked
- [x] exact classical Andersson arbitrary-divisor input located and checked
- [x] exact compact phase-torus and almost-sure `sigma(chi)=1/2` input located in Seip
- [x] route consequence stated positively as continuation-seam necessity
- [x] universal labelled differential-field isomorphism proved on paper
- [x] universal labelled differential-field isomorphism formalized unconditionally
- [x] density, nullity, codensity, and boundary-everywhere proof completed on paper
- [x] targeted literature audit found no statement of the combined geometry
- [x] abstract dense/codense seam consequences formalized from the classical hypotheses
- [x] nowhere-continuous continuation classifier proved
- [x] no-continuous-factorization theorem proved
- [x] significance gate: exact continuous-carrier impossibility class identified
- [x] novelty gate: targeted searches found no prior statement of the joint law
- [ ] 2 -> 3: the labelled-field universality and every abstract dense-null seam consequence are
  formalized axiom-clean; the concrete Pong, Andersson, and Saksman--Webb/Seip Helson inputs and
  their joint instantiation remain to be formalized

## Primary literature

- W. Y. Pong, *Applications of differential algebra to algebraic independence of arithmetic
  functions*, Acta Arith. 172 (2016), Theorem 5.9 and its formal-to-analytic discussion.
- J. Andersson, *Mittag-Leffler type theorems for Helson zeta-functions*, arXiv:2408.15713,
  especially Theorem 5.
- K. Seip, *Universality and distribution of zeros and poles of some zeta functions*, J. Anal.
  Math. 141 (2020), especially Section 1.1 and its citation of the Saksman--Webb almost-sure
  meromorphic-abscissa theorem.

## Lean plan — the three classical inputs, separated by cost

The card's open `2 → 3` gate names three concrete external theorems.  They are not equally
expensive, and the abstract layer they feed is already formal.

- **Pong's Theorem 5.9** (finite families of distinct shifted derivatives of a Dirichlet series
  with non-finitely-generated prime support are algebraically independent over the finite-prime
  differential field).  The corpus already owns the differential-independence machinery this
  produces (`DifferentialIndependence`, `DifferentialIndependentFieldUniversality`,
  `PrimeDirichletDifferentialField`), so the missing content is the *arithmetic* input: a prime
  support that is not finitely generated forces independence.  This is the piece to attack first.
- **Andersson's arbitrary-divisor theorem** — an analytic continuation statement about
  `Z_χ`; needs Dirichlet-series continuation machinery the corpus partly owns via `PNTPlus`.
- **Saksman--Webb/Seip almost-sure `σ(χ) = 1/2`** — a probabilistic statement on the character
  torus; the corpus owns the compact phase torus (`completed-time-torus` layer) but not the
  almost-sure abscissa.

The universality and dense/codense seam consequences are already formalized axiom-clean; what these
three add is the *instantiation*, i.e. that the hypothesis class is inhabited by the actual
`Z_χ` family.  Until then the formal statements are conditional on their hypotheses being met, and
the card should not claim the joint law is formal.
