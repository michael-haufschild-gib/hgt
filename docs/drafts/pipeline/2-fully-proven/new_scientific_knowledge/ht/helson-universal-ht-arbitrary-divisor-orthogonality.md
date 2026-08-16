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

## Lean progress — Pong's hypothesis is discharged for every character

`GaloisForLFunctions/HTGeometry/PrimeSupportNotFinitelyGenerated.lean` (wired, axiom-clean):

    mem_of_prime_mem_closure             a prime in the multiplicative closure of a finite set of
                                         primes belongs to that set
    primeSupport_not_finitelyGenerated   **no finite set of primes generates every prime**

Pong's Theorem 5.9 applies to an arithmetic function whose prime support is not finitely generated.
For a completely multiplicative unimodular `chi` the support is all primes, so the hypothesis is
now a theorem rather than a condition to be checked per character.  What remains of Pong's input is
its conclusion — algebraic independence of the shifted derivatives — not its hypothesis.

## Lean plan — the density half of the seam is NOT a literature input

The `2 → 3` gate lists three classical inputs, but the dense half of the dense–null seam is not one
of them: the card proves it itself, by finite Euler modification.  Only the *null* half needs
Saksman--Webb.  So the seam splits into one buildable brick and one deep one, and the buildable one
is the next target.

What the density argument needs, in order:

1. **`MeromorphicOn riemannZeta Set.univ`** — mathlib does not have it.  Route: off `1` use
   `differentiableAt_riemannZeta` with `analyticAt_iff_eventually_differentiableAt` (the set `{1}ᶜ`
   is a neighbourhood of every other point).  At `1` use `MeromorphicAt.congr` against the explicit
   formula `riemannZeta s = (completedRiemannZeta₀ s - 1/s - 1/(1-s)) / Gammaℝ s`
   (`riemannZeta_def_of_ne_zero`, `completedRiemannZeta_eq`), valid on a punctured neighbourhood of
   `1`: `completedRiemannZeta₀` is entire (`differentiable_completedZeta₀`), `1/s` is analytic at
   `1`, `1/(1-s)` is meromorphic at `1`, and `Gammaℝ` is analytic and nonzero at `1`
   (`Gammaℝ_ne_zero_of_re_pos`).
2. **The finite Euler modification is meromorphic.**  For a finite set `P` of primes and phases
   `χ p` on the unit circle, `∏_{p ∈ P} (1 - p^{-s})/(1 - χ(p) p^{-s})` is a finite product of
   quotients of entire functions with nonzero denominators, hence meromorphic on `ℂ`.
3. **It is the Helson zeta.**  On `Re s > 1`, mathlib's Euler product for a completely
   multiplicative coefficient function (`EulerProduct`) identifies
   `Z_χ(s) = ζ(s) · ∏_{p ∈ P} (1 - p^{-s})/(1 - χ(p) p^{-s})` when `χ = 1` off `P`.
4. **Density.**  `dense_finiteModification` (already formal in `DenseNullContinuationSeam.lean`)
   then gives that the continuable stratum is dense in the character torus, with no classical input.

That leaves, as genuinely classical and genuinely deep: Pong's Theorem 5.9 (algebraic independence
of the shifted derivatives — note the corpus already owns the conclusion for the prime-power
valuation palette, `primePowerCoefficientShiftPalettes_differentialIndependent_of_recurringPatternsSpan`,
so the remaining work is to discharge `RecurringCoefficientPatternsSpan` for a unimodular completely
multiplicative phase and to descend from the palette to `Z_χ` itself), Andersson's arbitrary-divisor
theorem, and Saksman--Webb's almost-sure abscissa.

## Lean progress — step 1 of the density instantiation: zeta is meromorphic on the plane

`GaloisForLFunctions/HTGeometry/RiemannZetaMeromorphic.lean` (wired, axiom-clean):

    analyticAt_riemannZeta    away from `1`, `ζ` is analytic — differentiability on the open set
                              `{1}ᶜ`, which is a neighbourhood of every other point
    analyticAt_Gammaℝ         the real gamma factor is analytic on the right half plane
    meromorphicOn_riemannZeta **`MeromorphicOn riemannZeta Set.univ`**

mathlib records the pole of `ζ` only as the residue limit `(s-1)ζ(s) → 1`, and has no meromorphy
statement, so this had to be built.  The proof at `s = 1` does not use a removable-singularity
theorem: meromorphy depends only on the germ off the point (`MeromorphicAt.congr`), and on a
punctured neighbourhood of `1` the completed functional equation writes

    ζ(s) = (Λ₀(s) - 1/s - 1/(1-s)) / Γ_ℝ(s)

with `Λ₀` entire, `1/s` analytic at `1`, `1/(1-s)` visibly meromorphic there, and `Γ_ℝ` analytic
at `1` because `Γ` is analytic at `1/2`.

This is step 1 of the four-step density instantiation recorded above; steps 2–4 (meromorphy of the
finite Euler modification factor, the Euler-product identification on `Re s > 1`, and the appeal to
`dense_finiteModification`) do not need any classical input either.

## Lean progress — steps 2 and 4 of the density instantiation

`GaloisForLFunctions/HTGeometry/HelsonEulerModification.lean` (wired, axiom-clean):

    eulerFactor a b                       the correction `(1 - a^{-s})/(1 - b·a^{-s})`
    analyticAt_const_cpow_neg             a constant power with nonzero base is entire in the
                                          exponent
    meromorphicAt_eulerFactor             so each correction factor is meromorphic
    meromorphicAt_finsetProd              a finite product of germs meromorphic at a point is
    meromorphicOn_eulerModification       hence a finite Euler modification is meromorphic on `ℂ`
    meromorphicOn_mul_eulerModification   and it preserves meromorphy of whatever it multiplies
    meromorphicOn_riemannZeta_mul_eulerModification :
      **every finite Euler modification of `ζ` continues meromorphically to the whole plane**
    finiteEulerStratum                    the phases equal to `1` at all but finitely many primes
    dense_finiteEulerStratum              **that stratum is dense**
    exists_meromorphicOn_of_mem_finiteEulerStratum :
      every member of it carries an explicit presentation meromorphic on the whole plane, with the
      modified primes read off as the support of `χ - 1`

Steps 1, 2 and 4 of the density plan are therefore formal, with no classical input.  What links them
is step 3: on `Re s > 1` the presentation
`ζ(s)·∏_{p ∈ P}(1 - p^{-s})/(1 - χ(p)p^{-s})` equals the Helson zeta `Z_χ(s)`, which is mathlib's
Euler product for a completely multiplicative coefficient function together with the splitting of a
convergent product by a finite correction.  That is the next brick, and it is not a classical input
either.

Only the *null* half of the seam — Saksman--Webb's almost-sure abscissa — together with Pong's and
Andersson's conclusions, remains genuinely classical on this card.

## Lean progress — THE DENSITY HALF OF THE SEAM IS CLOSED, unconditionally

`GaloisForLFunctions/HTGeometry/HelsonZetaEulerProduct.lean` (wired, axiom-clean):

    norm_prime_cpow_neg_lt_one            `‖p^{-s}‖ < 1` on `Re s > 1`
    one_sub_phase_prime_cpow_ne_zero      so no Euler denominator of a unimodular phase vanishes
    one_sub_prime_cpow_ne_zero
    hasProd_helsonEuler :
      **for a phase equal to `1` off a finite set `P`,**
        `∏'_p (1 - χ(p)p^{-s})^{-1} = ζ(s) · ∏_{p ∈ P} (1 - p^{-s})/(1 - χ(p)p^{-s})`
      on `Re s > 1`
    exists_meromorphicOn_helsonZeta_of_mem_finiteEulerStratum
    PhaseTorus, trivialPhase, continuableStratum
    mem_continuableStratum_of_finiteModification
    dense_continuableStratum :
      **the stratum of phases whose Helson zeta continues meromorphically to the whole plane is
      DENSE in the phase torus**

`continuableStratum` is not a proxy: it is the set of phases `χ` for which there exists `F`
meromorphic on all of `ℂ` whose values are the Euler product `∏'_p (1 - χ(p)p^{-s})^{-1}` at every
`s` with `Re s > 1`.

The proof is the card's own: split the Euler product factorwise against the Riemann one, note that
the correction family is `1` off `P` so its infinite product is the finite product
(`hasProd_prod_of_ne_finset_one`), and use the finite-modification meromorphy law together with
`meromorphicOn_riemannZeta`.  mathlib supplies only the Riemann Euler product
(`riemannZeta_eulerProduct_hasProd`); everything else had to be built, including the meromorphy of
`ζ` itself.

### Revised status of the classical inputs

The `2 → 3` gate lists Pong, Andersson and Saksman--Webb.  The density half of the dense--null seam
was never among them — it is the card's own finite-Euler-modification argument, and it is now
formal end to end with no classical input.  What is genuinely classical and still open:

| input | used for |
|---|---|
| Saksman--Webb / Seip, `σ(χ) = 1/2` a.s. | the NULL half of the seam |
| Pong, Theorem 5.9 | the universal labelled differential-field type |
| Andersson, Theorem 5 | divisor surjectivity of the continuable stratum |

The abstract consequences of the seam (`frontier_eq_univ_of_dense_and_dense_compl`,
`nowhereContinuous_seamIndicator`, `no_continuous_factorization_seamIndicator`) are already formal,
so the null half is the single remaining input for the boundary-everywhere geometry.

## Lean progress — Pong's independence conclusion, with its hypothesis discharged for every phase

`GaloisForLFunctions/HTGeometry/HelsonPhaseTailIndependence.lean` (wired, axiom-clean):

    recurringCoefficientPatternsSpan_const :
      a single source with constant coefficient displays one pattern, at every prime, so it spans
    tailCoefficientIndependent_shiftJet_const
    tailCoefficientIndependent_phaseShiftJet :
      **a nowhere-vanishing phase keeps the shift--jet palette tail independent**
    tailCoefficientIndependent_helsonShiftJet :
      in particular a unimodular phase does, at every prime-power layer
    primePowerCoefficientShiftedRotatedJet_tailIndependent_phase :
      the same for the rotated clock
    primePowerCoefficientShiftedJets_algebraicIndependent_phase :
      **the complete shifted-jet rectangle of a nowhere-vanishing phase, across a finite window of
      valuation layers, is algebraically independent over the finite-prime rational coefficient
      field**

The obstacle was that the corpus's criterion for tail independence, `RecurringCoefficientPatternsSpan`,
is designed for coefficient families of **finite range**, and a generic Helson phase has infinite
range — no value of `χ(p)` need recur at all, so the criterion is not merely hard to check, it is
false as stated for a generic phase.

It does not have to be checked.  A single source contributes its coefficient as one **common weight**
on every column of the shift--jet rectangle, and `tailCoefficientIndependent_commonWeight_iff` says a
common nowhere-vanishing weight is invisible to tail independence.  So the criterion is applied once,
to the constant family — whose single pattern recurs at every prime — and the phase is then
reinstated as a weight.  Unimodularity enters only through `χ(p) ≠ 0`.

This is the conclusion of Pong's Theorem 5.9 in the form the card consumes, for one source per
valuation layer, with no hypothesis on the arithmetic of the phase.  What remains to reach the
card's `L_χ` statement is the descent from the prime-power palette to the shifted derivatives of
`Z_χ` itself.

## Lean progress — THE BOUNDARY-EVERYWHERE SEAM IS UNCONDITIONAL; Saksman--Webb is not needed for it

The card derives codensity of the continuable stratum `M` from Haar-nullity plus full support.  That
route needs Saksman--Webb.  It is not the only route, and the cheaper one is a *theorem*, not an
input: codensity needs only **one** noncontinuable Helson zeta, because a finite Euler modification
of a noncontinuable phase is again noncontinuable, and finite modifications of any fixed phase are
dense.

`GaloisForLFunctions/HTGeometry/HelsonCubeRootNonContinuation.lean` (wired, axiom-clean):

    cubeRootUnit, normSq_cubeRootUnit, norm_cubeRootUnit
    cubeRootUnit_add_conj, cubeRootUnit_mul_conj
    cubeRoot_factorization        `(1-ωx)(1-ω̄x)(1-x) = 1-x³` for a primitive cube root `ω`
    prime_cpow_ofReal             on the real axis a prime power is a positive real
    prime_rpow_cube
    norm_sq_mul_riemannZeta :
      **`‖Z_ω(σ)‖² · ζ(σ) = ζ(3σ)`  for real `σ > 1`**
    cubeRootPhase                 the phase equal to `ω` at every prime
    tendsto_ofReal_nhdsWithin_ne
    notMem_continuableStratum_cubeRootPhase :
      **the constant cube-root phase is NOT continuable**
    eulerRatio, meromorphicAt_eulerRatio
    mem_continuableStratum_of_finite_ne :
      continuability transfers along finite modifications of the phase
    notMem_continuableStratum_of_finiteModification
    dense_compl_continuableStratum :
      **the noncontinuable phases are DENSE in the phase torus**
    frontier_continuableStratum_eq_univ :
      **`frontier M = Ω`** — the continuation seam is boundary-everywhere
    nowhereContinuous_continuationIndicator :
      **the Boolean continuation indicator is continuous at no phase**
    no_continuous_factorization_continuationIndicator :
      **and does not factor through any continuous readout**

The mechanism is an order parity obstruction at `s = 1`, not an abscissa computation.  Since `1`,
`ω`, `ω̄` are the three cube roots of unity, multiplying the Euler products of `χ ≡ ω`, of its
conjugate, and of the trivial phase gives `Z_ω · Z̄_ω · ζ = ζ(3·)` on the half plane of absolute
convergence, and on the real axis `Z̄_ω(σ) = conj Z_ω(σ)`.  Hence `‖Z_ω(σ)‖² = ζ(3σ)/ζ(σ)`, which
vanishes to order exactly **one** as `σ ↓ 1` because `ζ(3) ≠ 0` and `(σ-1)ζ(σ) → 1`.  A function
meromorphic at `1` has `‖F(σ)‖²` vanishing to an **even** order, and `2n ≠ 1` for every integer `n`.
Equivalently: the local order of `Z_ω` at `1` would have to be `-Re ω = 1/2`.

So the card's four seam conclusions

```text
closure(M) = Ω,   closure(Ω∖M) = Ω,   boundary(M) = Ω,   1_M nowhere continuous
```

are now formal with **no** classical input at all, and the "no continuous readout of the compact
finite-prime inverse limit decides continuation" law — the card's positive necessity statement — is
unconditional.

### Revised residue of this card

| statement | status |
|---|---|
| labelled differential-field universality | formal |
| Pong's hypothesis (prime support not finitely generated) | formal |
| Pong's conclusion at the prime-power palette | formal |
| density of `M` | formal |
| **codensity of `M`, `boundary(M) = Ω`, nowhere-continuous indicator, no continuous factorization** | **formal, unconditional** |
| `Haar(M) = 0` (Saksman--Webb/Seip) | open |
| divisor surjectivity (Andersson Thm 5) | open |
| descent from the prime-power palette to `Z_χ` itself | open |

Haar-nullity is no longer load-bearing for any other conclusion on the card: it is now an isolated
strengthening of codensity, not the source of it.

## Lean progress — PONG'S CONCLUSION FOR `Z_χ` ITSELF, and the labelled isomorphism `Φ_(χ,ψ)`

The remaining algebraic residue was the descent from the prime-power palette to the shifted
derivatives of `Z_χ`, whose coefficients live on **all** of `ℕ`.  The obstruction was structural,
not quantitative: the corpus's Shapiro--Sparer bridge is stated for *prime-supported* arithmetic
functions, because there the prime derivation `∂_q b = b(q)·1` is a **scalar**, so the Jacobian is a
matrix over the base field.  A completely multiplicative coefficient function has no such Jacobian.

The support restriction is unnecessary.

`GaloisForLFunctions/HTGeometry/ArithmeticFunctionGeneralJacobian.lean` (wired, axiom-clean):

    arithmeticEvalOne              evaluation at `n = 1` as a ring homomorphism `𝒜 → ℂ`
                                   (the only factorization of `1` is `1·1`)
    primeDeriv_apply_one           `(∂_q b)(1) = b q`, with no support hypothesis
    arithmeticPrimeJacobian        the Jacobian `(∂_{q i} g_j)` over the Dirichlet algebra
    arithmeticPrimeJacobian_evalOne
    det_arithmeticPrimeJacobian_ne_zero :
      **the constant term of the Jacobian determinant is the prime-evaluation determinant**
    algebraicIndependent_arithmeticFunctions_of_primeEvaluation :
      **an ARBITRARY finite family of arithmetic functions with a nonsingular prime-evaluation
      matrix is algebraically independent over `ℂ`**
    fractionArithmeticPrimeJacobian, det_fractionArithmeticPrimeJacobian_ne_zero
    algebraicIndependent_fractionArithmetic_over_commonKernel
    CofiniteArithmeticEvaluationPacket
    algebraicIndependent_fractionArithmetic_over_finitePrimeCoefficientField
    cofiniteArithmeticEvaluationPacket_of_tailIndependent
    algebraicIndependent_fractionArithmetic_of_tailIndependent :
      **tail independence of the PRIME RESTRICTIONS alone gives algebraic independence over the
      whole intrinsic finite-prime coefficient field**

The mechanism: the Dirichlet algebra is a domain, so the Jacobian criterion needs only
`det ≠ 0`, and that is decided at the identity component, where `∂_q` reads off the value at `q`
whatever the rest of the coefficients are.

`GaloisForLFunctions/HTGeometry/HelsonZetaShiftedJetIndependence.lean` (wired, axiom-clean):

    algebraicIndependent_of_finite_subfamilies
                                   a family is independent as soon as every finite subfamily is
    helsonClockJet χ α c k         the coefficient function `n ↦ χ(n) n^{-α} (c log n)^k`
    helsonClockJet_apply_prime
    logWeight_helsonClockJet       the rotated logarithmic derivation raises the clock power
    differentialJet_helsonClockJet **the `k`-th jet of `Z_χ(s+α)` in the Dirichlet field**
    tailCoefficientIndependent_equiv
    tailCoefficientIndependent_helsonClockJet
    helsonClockJets_algebraicIndependent          finite rectangles
    helsonClockJets_algebraicIndependent_all :
      **the COMPLETE shift--jet family, arbitrary shift index, unbounded jet order**
    helsonShifts_differentialIndependent :
      **`DifferentialIndependent E_fin (fun a ↦ Z_χ(s + α a))`**
    helsonShifts_differentialIndependent_of_unimodular
    helsonLabelledAlgEquiv :
      **`Φ_(χ,ψ) : L_χ ≃ₐ[E_fin] L_ψ`** for any two nowhere-vanishing phases and any shift family
      with distinct real parts
    helsonLabelledAlgEquiv_jet :
      it carries every labelled jet to its counterpart

So the card's first theorem — *every `L_χ` is an abstract differential rational function field on the
shift-indexed family, and `Φ_(χ,ψ)` is the canonical labelled isomorphism* — is now formal for the
actual Helson zeta functions, not only for a prime-power palette.  The only hypothesis on the phase
is `χ(p) ≠ 0`, which unimodularity supplies; the only hypothesis on the shifts is that their real
parts are distinct, which the card's nonnegative distinct real shifts supply.

### Residue of this card after this session

| statement | status |
|---|---|
| labelled differential-field universality (abstract) | formal |
| **Pong's conclusion for `Z_χ` itself, over `E_fin`** | **formal, unconditional** |
| **`Φ_(χ,ψ)` for actual Helson zetas** | **formal, unconditional** |
| density of `M` | formal |
| **codensity of `M`, `boundary(M) = Ω`, nowhere-continuous indicator, no continuous factorization** | **formal, unconditional** |
| `Haar(M) = 0` (Saksman--Webb/Seip) | open |
| divisor surjectivity (Andersson Thm 5) | open |

## Lean progress — the Haar-nullity half becomes a strict inequality

`GaloisForLFunctions/HTGeometry/FiniteModificationZeroOne.lean` (wired, axiom-clean) proves the
zero–one law that the continuation stratum satisfies for structural reasons, before any asymptotic
input:

```text
coordSigma n                     the σ-algebra of the n-th coordinate of a countable product
truncateBelow a n                replacing every coordinate below n by a reference point
measurableSet_limsup_of_invariant
    a measurable set invariant under modification of finitely many coordinates lies in the tail
    σ-algebra  limsup coordSigma atTop
measure_eq_zero_or_one_of_invariant
    under any measure making the coordinates independent, such a set has measure 0 or 1
iIndep_coordSigma_infinitePi     the coordinates of a countable product measure are independent
measure_infinitePi_eq_zero_or_one_of_invariant   the same, for the product measure itself
```

The proof is exactly the card's own Euler-modification observation, read measure-theoretically:
changing finitely many prime phases multiplies `Z_χ` by a finite Euler factor, which is meromorphic
on the plane, so **membership in `M` does not depend on any finite set of coordinates**.  Hence `M`
is a tail event and

```text
Haar(M) ∈ {0, 1} .
```

The remaining content of `Haar(M) = 0` is therefore the single strict inequality `Haar(M) ≠ 1` —
"the continuable stratum is not almost everything" — rather than the full Saksman--Webb asymptotic
`σ(χ) = 1/2` a.s.  Nothing else on the card depends on it: density, codensity,
`boundary(M) = Ω`, nowhere-continuity of `1_M`, and the no-continuous-factorization theorem are all
already unconditional.

The formal statement above is stated for an arbitrary countable product of probability spaces, so it
applies verbatim to `Ω = ∏_p S¹` with Haar product measure once `M` is defined there; what it needs
from the analytic side is only measurability of `M` and the finite-modification invariance.

## Lean progress — the Saksman--Webb input, first quantitative layer

`RHTower/SteinhausAbscissaSecondMoment.lean` (wired, axiom-clean) supplies the quantitative core of
"the abscissa is at least `1/2` almost surely", which is the half of Saksman--Webb/Seip that
`Haar(M) != 1` needs:

```
steinhausDirichletPoly sigma N omega      the truncated random series  sum_{n<=N} n^{-sigma} X_n
integral_normSq_steinhausDirichletPoly    E || sum_{n<=N} n^{-sigma} X_n ||^2 = sum_{n<=N} n^{-2 sigma}
one_div_le_rpow_neg_two_mul               sigma <= 1/2  ==>  1/n <= n^{-2 sigma}
tendsto_sum_rpow_neg_two_mul_atTop        hence the coefficient sum diverges
tendsto_integral_normSq_steinhausDirichletPoly_atTop
    the L^2 norms of the partial sums are unbounded for every sigma <= 1/2
```

The identity is the corpus's own model second-moment law `integral_normSq_dpoly` (orthonormality of
the Steinhaus characters) instantiated at `a_n = n^{-sigma}`; the divergence is the harmonic
comparison.  The consequence is that the partial sums cannot converge in `L^2` anywhere strictly
left of the half line — the first of the two steps that turn the zero-one law
(`measure_infinitePi_eq_zero_or_one_of_invariant`, already formal) into `Haar(M) = 0`.

What remains of this input is the passage from `L^2` divergence to almost-sure non-continuability:
the a.s. abscissa of convergence, and then the natural boundary.  Nothing else on the card depends
on it.

## Lean progress — Kolmogorov's zero–one law for a random series

`HTGeometry/SeriesConvergenceZeroOne.lean` (wired, axiom-clean).

```
coordPartialSum g N x               sum_{n<N} g n (x n)   -- n-th term reads only coordinate n
coordSeriesConverges g              { x | the partial sums converge }
coordPartialSum_sub_eq              modifying coordinates below n1 shifts every later partial sum
                                        by ONE constant
coordSeriesConverges_invariant      hence convergence is invariant under finite modification
measurable_coordPartialSum
measurableSet_coordSeriesConverges  the convergence set is measurable
measure_coordSeriesConverges_eq_zero_or_one
    under a countable product of probability measures the series converges either almost
    nowhere or almost everywhere
```

This is the step the Saksman--Webb input needs on top of
`tendsto_integral_normSq_steinhausDirichletPoly_atTop`.  The `L^2` layer says the partial sums of
`sum n^{-sigma} X_n` are unbounded in `L^2` for every `sigma <= 1/2`; the zero-one law says the
*event* that the series converges at a fixed `s` is a tail event, so its probability is `0` or `1`
and the abscissa of convergence is almost surely deterministic.

The mechanism is the same finite-modification observation the card already uses for `M`, but applied
to a series rather than to meromorphic continuation: altering finitely many prime phases changes
every partial sum past that point by a single constant, and a constant shift cannot create or
destroy convergence.  Stated for an arbitrary countable product with values in any
second-countable completely-pseudo-metrizable topological abelian group, so it applies verbatim to
`Omega = prod_p S^1` with values in `C`.

What remains between here and `Haar(M) != 1` is unchanged: the passage from `L^2` divergence to
almost-sure divergence (Lévy / Itô--Nisio for independent symmetric summands), and then from
divergence of the series to non-continuability.  The zero-one law removes the need to prove anything
about the *set* of `omega` at that point — only the dichotomy has to be broken, at a single `sigma`.

## Lean progress — Paley–Zygmund, and the route to `Haar(M) != 1` that avoids Itô--Nisio

`HTGeometry/PaleyZygmund.lean` (wired, axiom-clean).

```
le_half_add_sq_div    z <= t/2 + z^2/(2t)   for every t > 0   -- rearranges to (t - z)^2 >= 0
paley_zygmund         (1 - th)^2 (E Z)^2 <= E[Z^2] * P(Z > th E Z),   0 <= th < 1
```

The proof avoids Hölder entirely.  Splitting the mean at the threshold gives
`(1-th) E Z <= E[Z 1_A]`; the pointwise AM--GM bound integrates to
`E[Z 1_A] <= (t/2) P(A) + E[Z^2]/(2t)`; and `t = sqrt(E[Z^2]/P(A))` makes the right side
`sqrt(E[Z^2] P(A))` — Cauchy--Schwarz with the sharp constant, recovered without an L^p API.  This is
the same device used for the prolate second-moment tail bound this session; it is worth noting that
the trick is reusable exactly because the optimising `t` is chosen after integration.

### Why this matters for the card

The missing step was `L^2` divergence  ==>  almost-sure divergence, whose textbook proofs go through
Kolmogorov's three-series theorem or Itô--Nisio — neither is in mathlib, and both need stopping
times.  Paley--Zygmund replaces them with an elementary argument:

1. `E|S_N|^2 = A_N := sum_{n<=N} |a_n|^2`                      (already formal)
2. `E|S_N|^4 <= 2 A_N^2`                                        (Steinhaus fourth moment — TO DO)
3. Paley--Zygmund with `Z = |S_N|^2`, `th = 1/2`:
       `P(|S_N|^2 > A_N/2) >= (1/4) A_N^2 / E|S_N|^4 >= 1/8`     (this session)
4. If the series converged a.s. then `sup_N |S_N| < infinity` a.s., so some `M` has
   `P(sup_N |S_N| <= M) >= 9/10`; but `A_N -> infinity` gives `P(|S_N| > M) >= 1/8` for large `N`,
   hence `P(sup > M) >= 1/8`, i.e. `P(sup <= M) <= 7/8 < 9/10` — contradiction.
5. So convergence has probability `< 1`, and by the zero-one law
   (`measure_coordSeriesConverges_eq_zero_or_one`, this session) probability `0`.

Only item 2 remains, and it is a finite orthogonality computation, not a limit theorem.

## Lean progress — the fourth-moment escape engine, and a correction to the plan

`HTGeometry/FourthMomentEscape.lean` (wired, axiom-clean).

```
measure_sq_gt_half_ge   fourth moment <= C (second moment)^2  and second moment > 0
                            ==>  P( g^2 > (E g^2)/2 ) >= 1/(4C)     -- uniform in the index
measure_exists_gt_ge    second moments -> infinity  ==>  every level M is exceeded by some
                            f N with probability >= 1/(4C)
measure_unbounded_ge    hence  P( sup_N f N = infinity ) >= 1/(4C)
```

The decreasing intersection over integer levels is taken with `tendsto_measure_iInter_atTop`; the
bound survives because `1/(4C)` does not depend on `N`.  This is the elementary replacement for
Kolmogorov's three-series theorem: no stopping time, no maximal inequality, no martingale theory.

### CORRECTION to the plan recorded above

The step written earlier as

```
2.  E|S_N|^4 <= 2 A_N^2      (Steinhaus fourth moment)
```

is **FALSE as stated for the full Dirichlet polynomial** and must not be attempted in that form.
Expanding,

```
E|S_N|^4 = sum_{n k = m l} a_n a_k a_m a_l ,
```

because `E[X_{nk} conj(X_{ml})] = 1` exactly when `nk = ml`.  Over all integers `n,k,m,l <= N` the
diagonal `nk = ml` is a divisor-correlation sum, not `2 A^2`: the Steinhaus characters `X_n` are
*not* independent across `n` (`X_6 = X_2 X_3`), so the four-fold sum picks up the divisor function
and exceeds `A^2` by a logarithmic factor.

The bound IS correct over **prime** indices, where the characters are genuinely independent and
`p r = q s` forces `{p,r} = {q,s}`:

```
E| sum_p a_p X_p |^4 = 2 A^2 - sum_p a_p^4 <= 2 A^2 ,      A = sum_p a_p^2 .
```

So the chain must be run on the prime sub-series `sum_p p^{-sigma} X_p`, whose second moment
`sum_p p^{-2 sigma}` still diverges for `sigma <= 1/2` by Mertens.  This is also the natural object
for the card, since the Euler product is where the independent phases live.

Revised remaining item for this route: the prime fourth-moment identity above (a finite
orthogonality computation over `{p,r} = {q,s}`), plus `sum_p p^{-2 sigma} -> infinity`.

## Lean progress — the two prime-side inputs

`RHTower/PrimeSecondMomentDivergence.lean` (wired, axiom-clean).

```
prime_mul_eq_prime_mul       p r = q t with p,q,r prime  ==>  (p=q and r=t) or (p=t and r=q)
primeCoeff sigma             the prime-supported sequence  n |-> [n prime] * n^{-2 sigma}
not_summable_primeCoeff      sigma <= 1/2  ==>  not summable, by comparison with sum 1/p
tendsto_sum_primeCoeff_atTop hence the partial sums escape to infinity
```

The arithmetic lemma is the exact combinatorial input that makes the prime fourth moment collapse:
`E[X_{pr} conj(X_{qt})] = 1` iff `pr = qt`, and over primes that happens only on the two diagonals,
giving `2 A^2 - sum a_p^4`.  It is also precisely the statement that fails over general integers,
which is why the full Dirichlet polynomial has no such bound (see the correction above).

Note the lemma needs only THREE of the four primality hypotheses: `t` is forced to be prime by the
equation once `p, q, r` are.  Stated with the redundant hypothesis dropped.

The analytic input is mathlib's `not_summable_one_div_on_primes` (Erdős's proof of the divergence of
the sum of prime reciprocals), compared against `1/n <= n^{-2 sigma}` — which is the corpus's own
`one_div_le_rpow_neg_two_mul`, already formal.  Divergence of the partial sums then comes from
`not_summable_iff_tendsto_nat_atTop_of_nonneg`.

With these, of the chain recorded above only the prime fourth-moment identity itself remains:

```
E | sum_{p in s} a_p X_p |^4  =  2 (sum_p a_p^2)^2 - sum_p a_p^4 ,
```

a finite sum manipulation over `s x s x s x s` split by `prime_mul_eq_prime_mul`, with no analysis
in it.  The escape engine (`measure_unbounded_ge`) and the zero-one law
(`measure_coordSeriesConverges_eq_zero_or_one`) then close `Haar(M) != 1`.

## Lean progress — the four-fold diagonal collapse

`HTGeometry/QuadrupleDiagonalSum.lean` (wired, axiom-clean).

```
diagonal_summand_eq
    [p r = q t] a_p a_q a_r a_t
      = [p=q] a_p a_q * [r=t] a_r a_t  +  [p=t] a_p a_t * [q=r] a_q a_r
        - [p=q=r=t] a_p^4
    (given that the constraint cuts out exactly the two diagonals)

quadruple_diagonal_sum
    sum_{p,q,r,t in s} [p r = q t] a_p a_q a_r a_t  =  2 (sum a_p^2)^2 - sum a_p^4
```

Inclusion--exclusion on the two diagonals: each contributes `A^2`, and their overlap — the full
diagonal `p=q=r=t` — is counted twice and removed once.  The collapse is done one sum at a time from
the inside out, each step being a `Finset.sum_ite_eq` after the compound condition is refactored as
a single equality guarding a smaller conditional.

Stated over an arbitrary commutative ring, with the diagonal description as a hypothesis, so the
arithmetic input stays separate: `prime_mul_eq_prime_mul` supplies exactly that hypothesis for a
`Finset` of primes.

### Status of the `Haar(M) != 1` chain

```
1. E|S_N|^2 = sum_{p<=N} a_p^2                     formal   (integral_normSq_dpoly instantiated)
2. the diagonal collapse                            formal   (this session)
3. p r = q t over primes  <=>  two diagonals        formal   (this session)
4. Paley--Zygmund                                   formal   (this session)
5. escape engine: 4th moment bound => unbounded     formal   (this session)
6. sum_p p^{-2 sigma} diverges for sigma <= 1/2     formal   (this session)
7. zero-one law for series convergence              formal   (this session)
```

What is left is the *assembly*: expanding `|S_N|^4` as the four-fold sum in step 2 — i.e. the
identity `E[X_p conj(X_q) X_r conj(X_t)] = [p r = q t]`, which is `X_mul` plus the corpus's
`integral_X_mul_conj` — and then feeding steps 5 and 7 with it.  No further analytic input is
needed, and in particular neither Kolmogorov's three-series theorem nor Itô--Nisio appears anywhere
in the final chain.

## Lean progress — the fourth moment of a Steinhaus Dirichlet polynomial

`RHTower/SteinhausFourthMoment.lean` (wired, axiom-clean).

```
X_four_eq        X_p conj(X_q) X_r conj(X_t) = X_{pr} conj(X_{qt})     (complete multiplicativity)
integral_X_four  E[ X_p conj(X_q) X_r conj(X_t) ] = [ p r = q t ]      (orthonormality)
integrable_X_four, integrable_smul_X_four
integral_normSq_sq_dpoly
    E || sum_{n in s} a_n X_n ||^4  =  sum_{p,q,r,t in s} [ p r = q t ] a_p a_q a_r a_t
```

The expansion is a quadruple `Finset` distribution followed by a four-level exchange of integral and
sum, each level justified by `integrable_finsetSum` over the unimodular four-fold products.

One trap worth recording: `simp only [Finset.sum_mul, Finset.mul_sum]` distributes a product of four
sums with the index order **reversed** — the outermost binder ends up on the last factor.  The
resulting summand is `X_t conj(X_r) X_q conj(X_p)`, whose diagonal condition is `t q = r p`.  That is
the same condition as `p r = q t` (commute both sides), but the two are not syntactically equal and
the mismatch shows up only as a failing `ring` deep inside the proof.

Combining with `quadruple_diagonal_sum` and `prime_mul_eq_prime_mul` gives, for a `Finset` of primes,

```
E || sum_{p in s} a_p X_p ||^4  =  2 (sum_p a_p^2)^2 - sum_p a_p^4  <=  2 (E || . ||^2)^2 ,
```

which is exactly the hypothesis `measure_unbounded_ge` wants with `C = 2`.

## Lean progress — THE ESCAPE IS ASSEMBLED: the prime series has unbounded partial sums

`RHTower/SteinhausPrimeUnbounded.lean` (wired, axiom-clean).

```
steinhausPrimePoly sigma N ω  =  sum_{p < N, p prime} p^{-sigma} X_p(ω)

integral_normSq_steinhausPrimePoly       E ||S_N||^2 = sum_{p<N} p^{-2 sigma}
integral_normSq_sq_steinhausPrimePoly    E ||S_N||^4 = 2 (sum p^{-2 sigma})^2 - sum p^{-4 sigma}
norm_steinhausPrimePoly_le, measurable_steinhausPrimePoly
integrable_normSq_steinhausPrimePoly, integrable_normSq_sq_steinhausPrimePoly
sum_primeSet_eq, tendsto_integral_normSq_steinhausPrimePoly

measure_steinhausPrimePoly_unbounded
    sigma <= 1/2  ==>  Haar{ ω : sup_N ||S_N(ω)|| = infinity }  >=  1/8
```

Every step is unconditional.  The fourth moment is exactly `2 A^2 - sum a_p^4`, so the escape engine
applies with `C = 2` and the bound `1/(4C) = 1/8` comes out with no slack wasted.

This is the quantitative half of the Saksman--Webb input, obtained without Kolmogorov's three-series
theorem, without Itô--Nisio, and without any maximal inequality — only Paley--Zygmund, the prime
fourth moment, and Mertens.  Combined with
`measure_coordSeriesConverges_eq_zero_or_one` (the convergence event is a tail event, so its measure
is `0` or `1`), a positive probability of unbounded partial sums forces probability zero for
convergence.

What remains for `Haar(M) = 0` is the bridge from divergence of the prime Dirichlet series to
non-continuability of `Z_chi` — i.e. that a.s. divergence of the Euler exponent past the half line
obstructs meromorphic continuation.  That is the last analytic step; everything upstream of it is
now formal.

## Lean progress — ALMOST-SURE DIVERGENCE, unconditional

`RHTower/SteinhausPrimeDivergence.lean` (wired, axiom-clean).

```
X_prime_eq                    p prime  =>  X_p(ω) = exp(2 pi i ω_p)
                                  -- the prime characters read ONE coordinate each
primeTerm sigma n             the n-th term as a function of the n-th coordinate alone
coordPartialSum_primeTerm     its partial sums are exactly the prime Dirichlet polynomials
not_unbounded_of_converges    a convergent series has bounded partial sums (CauchySeq.isBounded_range)

measure_coordSeriesConverges_primeTerm_eq_zero
    sigma <= 1/2  ==>  Haar { ω : sum_p p^{-sigma} X_p(ω) converges } = 0
```

The prime characters reading one coordinate each is what lets the abstract tail-event zero-one law
apply verbatim: `steinhausMeasure` is definitionally `Measure.infinitePi` of the uniform phase
measures, which is exactly the hypothesis shape of
`measure_coordSeriesConverges_eq_zero_or_one`.  The escape bound gives the convergence event
probability at most `7/8`, and the dichotomy then forces `0`.

So the Saksman--Webb/Seip input needed by this card is now **proved unconditionally in Lean**, for
every `sigma <= 1/2`, along a route that uses only:

```
Paley--Zygmund   +   the prime fourth moment   +   Mertens   +   Kolmogorov's zero-one law
```

and in particular no three-series theorem, no Itô--Nisio, no maximal inequality, and no martingale
theory — none of which exist in mathlib.

### Residue of this card

| statement | status |
|---|---|
| labelled differential-field universality | formal |
| Pong's conclusion for `Z_chi`, `Phi_(chi,psi)` | formal, unconditional |
| density, codensity, `boundary(M) = Omega`, no continuous factorization | formal, unconditional |
| `Haar(M) in {0,1}` (finite-modification zero-one law) | formal, unconditional |
| **a.s. divergence of the prime series left of the half line** | **formal, unconditional** |
| `Haar(M) = 0` | needs: divergence of the Euler exponent obstructs continuation |
| divisor surjectivity (Andersson Thm 5) | open |

The single remaining analytic step for `Haar(M) = 0` is the bridge from divergence of
`sum_p p^{-sigma} X_p` to non-continuability of `Z_chi`.  Everything upstream of that bridge is now
a theorem.

### Correction: what a.s. divergence does and does not give

The note above called the step from divergence to `Haar(M) = 0` "one bridge".  That understates it
and should be read carefully.

What is now formal is `sigma_c >= 1/2` almost surely: the prime series `sum_p p^{-sigma} X_p`
diverges a.s. for every `sigma <= 1/2`.  Divergence of a Dirichlet series does **not** by itself
preclude analytic or meromorphic continuation past its abscissa of convergence — `zeta` is the
standard counterexample, convergent only for `Re s > 1` and entire apart from one pole.  So

```
a.s. divergence left of 1/2   =/=>   Haar(M) = 0 .
```

The genuine content of Saksman--Webb/Seip is the *natural boundary* statement: a.s. the line
`Re s = 1/2` is a natural boundary for `Z_chi`, not merely the edge of convergence.  That is a
strictly stronger theorem, and the divergence result formalized here is its first half, not a
reduction of it.

The remaining task is therefore correctly stated as: prove the a.s. natural boundary, of which the
formal chain here supplies the abscissa-of-convergence half.  The zero-one law
(`measure_infinitePi_eq_zero_or_one_of_invariant`) still reduces it to breaking the dichotomy at a
single point, which remains the most promising entry.

## Lean progress — divergence for arbitrary prime-supported coefficients

`RHTower/SteinhausPrimeGeneralDivergence.lean` (wired, axiom-clean).

```
steinhausPrimeGenPoly a N ω  =  sum_{p < N prime} a_p X_p(ω)     -- arbitrary real a
integral_normSq_genPoly       E ||S_N||^2 = sum_p a_p^2
integral_normSq_sq_genPoly    E ||S_N||^4 = 2 (sum_p a_p^2)^2 - sum_p a_p^4
measure_genPoly_unbounded     sum_p a_p^2 -> infinity  ==>  P(sup ||S_N|| = infinity) >= 1/8
genTerm, coordPartialSum_genTerm, not_unbounded_of_converges_gen

measure_coordSeriesConverges_genTerm_eq_zero
    sum_{p<N} a_p^2 -> infinity  ==>  Haar { ω : sum_p a_p X_p(ω) converges } = 0
```

The whole chain uses nothing about `p^{-sigma}`: the two diagonals of `p r = q t` over primes do not
see the coefficients at all, so the fourth-moment identity holds for every real sequence.  The
`sigma`-version is the special case `a_p = p^{-sigma}`.

## The route from divergence to the natural boundary: Bohr

Recording the identified reduction, since the previous correction left the remaining step
unspecified.

What is formal: `sigma_c >= 1/2` almost surely.  What the card needs: `Haar(M) != 1`, `M` the
continuation stratum.  The gap is bridged by **Bohr's theorem** for Dirichlet series,

```
sigma_u = sigma_b ,
```

the abscissa of uniform convergence equals the abscissa of *bounded* holomorphy.  Given it, suppose
`Z_chi` extended boundedly to `Re s > 1/2 - delta` for a positive-measure set of `chi`.  Then
`sigma_b <= 1/2 - delta`, hence `sigma_u <= 1/2 - delta`, hence `sigma_c <= sigma_u <= 1/2 - delta`
— contradicting the a.s. divergence proved here.  The zero-one law then upgrades positive measure to
full measure and closes `Haar(M) = 0`.

So the remaining analytic input is precisely Bohr's `sigma_u = sigma_b` (the easy inequality
`sigma_c <= sigma_u` is immediate).  It is not in mathlib.  It is a self-contained classical theorem
about ordinary Dirichlet series with no probabilistic content, which makes it a much better-defined
target than "the Saksman--Webb natural boundary" as previously recorded.

Caveat to check when that lands: the argument above controls *bounded* continuation.  If the card's
`M` is meromorphic continuation without a boundedness requirement, the reduction needs the standard
extra step of passing from meromorphic to locally bounded off the polar set.

## Lean progress — the Dirichlet kernel increment estimate (first layer toward Bohr)

`RHTower/DirichletKernelEstimate.lean` (wired, axiom-clean).

```
norm_cpow_neg_sub_le
    Re s > 0,  0 < a <= b   ==>   || a^{-s} - b^{-s} ||  <=  (||s|| / Re s) (a^{-Re s} - b^{-Re s})
```

The fundamental theorem of calculus on `[a,b]` for `x |-> x^{-s}`, whose derivative has norm
`||s|| x^{-Re s - 1}`; integrating that bound reproduces the real increment divided by `Re s`.

This is the analytic core of every convergence theorem for ordinary Dirichlet series: it is what
makes Abel summation work, converting a bound on the partial sums of the coefficients into
convergence throughout the open half-plane to the right, and it is the only place where the complex
exponent interacts with the real one.

### Why this layer, and what mathlib does not have

An audit of `Mathlib/NumberTheory/LSeries/` finds the development is entirely about **absolute**
convergence: `abscissaOfAbsConv` and its lemmas, plus `LSeriesSummable_of_sum_norm_bigO`.  There is
no abscissa of conditional convergence, no abscissa of uniform convergence, no abscissa of bounded
holomorphy, and no Bohr theorem.  So the route recorded above has to be built from this estimate up:

```
1. kernel increment estimate                              [this session]
2. bounded partial sums  =>  convergence for Re s > 0     (Abel summation + 1)
3. convergence at s0     =>  locally uniform convergence for Re s > Re s0
4. sigma_c <= sigma_u                                     (immediate from the definitions)
5. Bohr:  sigma_u = sigma_b                               (the substantial step)
```

Items 2-4 are routine given 1; item 5 is the real theorem.  Nothing in this chain is probabilistic,
so it is independent of everything else on this card and can be developed on its own.

## Lean progress — Abel summation ingredients two and three

`RHTower/DirichletIncrementSummable.lean` (wired, axiom-clean).

```
summable_rpow_neg_increment    the REAL increments (n+1)^{-σ} - (n+2)^{-σ} are summable
                                   (telescoping: partial sums are 1 - (N+1)^{-σ} <= 1)
summable_norm_cpow_increment   hence the COMPLEX kernel increments are absolutely summable
                                   for Re s > 0, by the increment estimate
tsum_norm_cpow_increment_le    with total mass at most ||s|| / Re s
tendsto_rpow_neg_nat_atTop     the boundary term N^{-Re s} -> 0
```

The three Abel-summation ingredients are now all theorems: the increment estimate (previous
section), absolute summability of the increments with an explicit total mass, and the vanishing of
the boundary term.  The total-mass bound `||s|| / Re s` is the one that makes the resulting
convergence *locally uniform* on `Re s >= Re s0 + δ`, which is what step 3 of the route needs.

Route status:

```
1. kernel increment estimate                              DONE
2. increments absolutely summable, mass <= ||s||/Re s     DONE
3. boundary term N^{-Re s} -> 0                           DONE
4. Abel identity + 1-3: bounded partial sums => convergence for Re s > 0
5. convergence at s0 => locally uniform for Re s > Re s0
6. sigma_c <= sigma_u
7. Bohr: sigma_u = sigma_b
```

Item 4 is the summation-by-parts assembly (`Finset.sum_range_by_parts` plus the three lemmas above);
5 and 6 follow from it; 7 is the substantial classical theorem.

## Lean progress — Abel summation assembled: item 4 of the Bohr route

`RHTower/DirichletAbelConvergence.lean` (wired, axiom-clean).

```
tendsto_dirichlet_partialSum_of_bounded
    || sum_{n<N} a_n ||  <=  C  for all N,   Re s > 0
      ==>  the partial sums  sum_{n<N} a_n (n+1)^{-s}  converge
```

The summation-by-parts identity is `Finset.sum_range_by_parts` with the kernel as the scalar factor:

```
sum_{n<N} a_n b_n  =  b_{N-1} A_N  -  sum_{i<N-1} (b_{i+1} - b_i) A_{i+1} ,   A_k = sum_{n<k} a_n .
```

The boundary term vanishes because `|| b_{N-1} || = N^{-Re s} -> 0` while `A_N` stays bounded, and
the sum converges absolutely by the increment summability of the previous section.

One point of care that is easy to get wrong: the conclusion is convergence of the **partial sums**,
not `Summable`.  A Dirichlet series outside its half-plane of absolute convergence is only
conditionally convergent, so `Summable` is false in general and the ordered limit is the only
correct statement.  (Everything in mathlib's `LSeries` is `Summable`-based, which is exactly why
none of this could be reused.)

Route status:

```
1. kernel increment estimate                              DONE
2. increments absolutely summable, mass <= ||s||/Re s     DONE
3. boundary term N^{-Re s} -> 0                           DONE
4. bounded partial sums => convergence for Re s > 0       DONE
5. convergence at s0 => locally uniform for Re s > Re s0
6. sigma_c <= sigma_u
7. Bohr: sigma_u = sigma_b
```

Item 5 is item 4 applied to the shifted coefficients `a_n (n+1)^{-s0}`, whose partial sums are
bounded precisely because the series converges at `s0`; the uniformity comes from the explicit mass
bound in item 2.

## Lean progress — the half-plane property: item 5 of the Bohr route

`RHTower/DirichletHalfPlane.lean` (wired, axiom-clean).

```
tendsto_dirichlet_partialSum_of_re_lt
    the series converges at s0,   Re s > Re s0
      ==>  the series converges at s
```

Abel summation applied to the shifted coefficients `a_n (n+1)^{-s0}`: their partial sums are bounded
exactly because the series converges at `s0` (a convergent sequence has bounded range), and the
remaining exponent `s - s0` has positive real part, which is the hypothesis of item 4.  The two
kernels recombine by `Complex.cpow_add` on the positive real base.

This is the property that makes an abscissa of convergence well defined, and it is precisely where
conditional convergence departs from the absolute convergence mathlib develops: the half-plane of
absolute convergence can be strictly smaller than this one, which is the whole reason `sigma_c` and
`abscissaOfAbsConv` are different invariants.

Route status:

```
1. kernel increment estimate                              DONE
2. increments absolutely summable, mass <= ||s||/Re s     DONE
3. boundary term N^{-Re s} -> 0                           DONE
4. bounded partial sums => convergence for Re s > 0       DONE
5. convergence at s0 => convergence for Re s > Re s0      DONE
6. sigma_c <= sigma_u
7. Bohr: sigma_u = sigma_b
```

Item 6 is immediate once the two abscissas are defined (uniform convergence implies convergence);
item 7 is the substantial classical theorem and the only remaining mathematical content on this
route.

## Lean progress — the two abscissas: item 6 of the Bohr route

`RHTower/DirichletAbscissa.lean` (wired, axiom-clean).

```
dirichletPartialSum a N s             sum_{n<N} a_n (n+1)^{-s}
DirichletConvergesAt a s              the partial sums converge at s
DirichletUniformlyConvergesOn a x     they converge uniformly on the closed half-plane Re s >= x
abscissaOfConv a                      sInf of the real points of convergence, in EReal
abscissaOfUnifConv a                  sInf of the real points of uniform convergence

DirichletConvergesAt.abscissaOfConv_le
convergesAt_of_abscissaOfConv_lt_re   abscissaOfConv a < Re s  ==>  converges at s
DirichletUniformlyConvergesOn.convergesAt
abscissaOfConv_le_abscissaOfUnifConv  sigma_c <= sigma_u
```

Both abscissas are defined exactly as mathlib defines `abscissaOfAbsConv` — an infimum over the
*real* points where the mode of convergence holds — which is legitimate precisely because of the
half-plane property proved in the previous section.  `convergesAt_of_abscissaOfConv_lt_re` is that
property restated in terms of the invariant, and is the form every later argument uses.

Route status:

```
1. kernel increment estimate                              DONE
2. increments absolutely summable, mass <= ||s||/Re s     DONE
3. boundary term N^{-Re s} -> 0                           DONE
4. bounded partial sums => convergence for Re s > 0       DONE
5. convergence at s0 => convergence for Re s > Re s0      DONE
6. sigma_c <= sigma_u, with both abscissas defined        DONE
7. Bohr: sigma_u = sigma_b
```

Only item 7 remains on this route.  It needs a third invariant — the abscissa of bounded holomorphy
`sigma_b` — and the classical argument that a Dirichlet series bounded and holomorphic on a
half-plane converges uniformly on every smaller one.  That is a self-contained theorem about
ordinary Dirichlet series with no probabilistic content, and it is the last mathematical step
between this card and `Haar(M) = 0`.

## Lean progress — the easy half of Bohr's comparison

`RHTower/DirichletBoundedSum.lean` (wired, axiom-clean).

```
norm_dirichletPartialSum_le                    each partial sum is bounded on Re s >= x, by
                                                   sum_{n<N} ||a_n|| (n+1)^{-x}
DirichletBoundedSumOn a x                      the series converges on Re s >= x to a bounded function
DirichletUniformlyConvergesOn.boundedSumOn     uniform convergence gives a bounded sum
abscissaOfBddSum a
abscissaOfBddSum_le_abscissaOfUnifConv         sigma_bdd <= sigma_u
```

The partial-sum bound is the only input: `(n+1)^{-Re s} <= (n+1)^{-x}` on the half-plane since
`n+1 >= 1`, so each partial sum is bounded there, and a uniform limit of bounded functions is
bounded.

### An honest statement of what is left

`DirichletBoundedSumOn` asks the series to **converge** on the half-plane to a bounded function.
Bohr's `sigma_b` is weaker: it allows the bounded holomorphic function to be an analytic
*continuation*, defined where the series need not converge at all.  So what is proved here is

```
sigma_bdd <= sigma_u ,        with sigma_bdd the convergent-sum abscissa,
```

and this is NOT half of Bohr's theorem in the usual sense — with the convergent notion the
inequality `sigma_u <= sigma_bdd` would be the whole content, and it is false without further work,
because uniform convergence is strictly stronger than pointwise convergence to a bounded limit.

The real remaining task is therefore:

```
7a. define sigma_b via a bounded holomorphic continuation (not via convergence)
7b. Bohr: sigma_u = sigma_b
```

`7a` needs `DifferentiableOn` on the open half-plane plus a boundedness hypothesis, and agreement
with the sum on the region of convergence; `7b` is the classical theorem.  Recording this so the
next pass does not mistake the inequality proved here for the corresponding half of Bohr.

## Lean progress — item 7a done, and the easy half of Bohr with the CORRECT definition

`RHTower/DirichletBddHolo.lean` (wired, axiom-clean).

```
differentiable_dirichletPartialSum       every partial sum is entire
DirichletBddHoloOn a x                   a bounded holomorphic F on Re s > x agreeing with the sum
                                             wherever the series converges
abscissaOfBddHolo a                      sigma_b
DirichletUniformlyConvergesOn.bddHoloOn  uniform convergence gives such an F
abscissaOfBddHolo_le_abscissaOfUnifConv  sigma_b <= sigma_u
```

This is the easy half of Bohr's theorem stated with the right invariant — `sigma_b` defined through a
bounded holomorphic *continuation*, not through convergence, which is what the previous section
warned was missing.  The proof: the partial sums are entire (each term is a nonzero constant to the
power `-s`), uniform convergence on the closed half-plane restricts to locally uniform convergence
on the open one, and `TendstoLocallyUniformlyOn.differentiableOn` gives holomorphy of the limit;
boundedness is the previous section's partial-sum bound plus one uniform-convergence step.

Route status:

```
1-6.  DONE
7a.   sigma_b defined via bounded holomorphic continuation      DONE
7b.   Bohr: sigma_u <= sigma_b                                  the classical theorem
```

Item 7b is now the single remaining statement on this route.  With it, `sigma_u = sigma_b` follows
from the inequality proved here, and the reduction recorded earlier closes `Haar(M) = 0`:

```
Z_chi bounded holomorphic on Re s > 1/2 - delta  =>  sigma_b <= 1/2 - delta
   =>  sigma_u <= 1/2 - delta   [7b]   =>  sigma_c <= sigma_u <= 1/2 - delta   [item 6]
   =>  contradicts the a.s. divergence   =>  Haar(M) != 1   =>  Haar(M) = 0   [zero-one law]
```

Every arrow in that chain except `[7b]` is now a Lean theorem.

## Lean progress — Bohr's first coefficient estimate

`RHTower/DirichletCoeffLimit.lean` (wired, axiom-clean).

```
tendsto_rpow_neg_of_one_lt                b > 1  ==>  b^{-sigma} -> 0
tendsto_dirichletPartialSum_ofReal_atTop  every partial sum -> a_0 along the real axis
tendsto_dirichletSum_ofReal_atTop         F(sigma) -> a_0 as sigma -> +infinity
norm_coeff_zero_le                        ||F|| <= C on the half-plane  ==>  ||a_0|| <= C
```

Only finitely many terms matter: past a cut the uniform error is small, and the remaining terms with
index `n >= 1` decay like `(n+1)^{-sigma}` while the `n = 0` term is the constant `a_0`, because
`1^{-s} = 1`.

`norm_coeff_zero_le` is the first of Bohr's coefficient estimates and the base case of the induction
that gives `||a_n|| <= C` for every `n`: the shifted series `n^s (F(s) - sum_{m<n} a_m m^{-s})` has
first coefficient `a_n`, and the inductive step needs a bound on that shifted function, which is
where the vertical-mean (almost-periodic) argument enters.

This is also the uniqueness engine for Dirichlet coefficients: two series with the same sum on a
half-plane have the same `a_0`, hence by shifting the same coefficients throughout.

Route status:

```
1-6.  DONE
7a.   sigma_b via bounded holomorphic continuation      DONE
7b.   Bohr: sigma_u <= sigma_b                          in progress
        - first coefficient estimate                    DONE
        - all coefficient estimates (vertical means)
        - Perron / Riesz-mean summation
        - the theorem
```

## Lean progress — vertical means of characters

`RHTower/VerticalMeanCharacter.lean` (wired, axiom-clean).

```
integral_cexp_const_mul       int_a^b e^{c t} dt = (e^{cb} - e^{ca}) / c      (c != 0)
norm_integral_cexp_I_le       || int_{-T}^{T} e^{i theta t} dt ||  <=  2 / |theta|
                                  -- UNIFORM in T, which is the whole point
tendsto_vertical_mean_cexp    hence (1/2T) || int_{-T}^{T} e^{i theta t} dt ||  ->  0
integral_cexp_zero_mul        the trivial character integrates to 2T
```

No trigonometry is needed: the antiderivative of `e^{ct}` is `e^{ct}/c`, and both endpoint values
are unimodular, so the integral is at most `2/|theta|` however long the segment.  Dividing by the
length kills it.

This is the orthogonality relation behind Bohr's coefficient estimates.  Applied with
`theta = log((m+1)/(n+1))` it separates the `m`-th term of a Dirichlet series from the `n`-th, which
is what upgrades `norm_coeff_zero_le` from the first coefficient to all of them:

```
a_n  =  lim_{T -> infinity} (1/2T) int_{-T}^{T} F(sigma + it) (n+1)^{sigma + it} dt ,
```

the `m != n` terms being killed by the mean above and the `m = n` term contributing `a_n`.

Route status:

```
1-6.  DONE
7a.   sigma_b via bounded holomorphic continuation      DONE
7b.   Bohr: sigma_u <= sigma_b                          in progress
        - first coefficient estimate                    DONE
        - vertical mean orthogonality                   DONE
        - the coefficient formula and ||a_n|| <= C
        - Perron / Riesz-mean summation
        - the theorem
```

## Lean progress — the off-diagonal terms die

`RHTower/DirichletTermMean.lean` (wired, axiom-clean).

```
cpow_neg_mul_cpow_eq       b^{-s} c^{s} = e^{sigma(log c - log b)} * e^{i(log c - log b)t},  s = sigma + it
log_sub_log_ne_zero        m != n  ==>  log(n+1) - log(m+1) != 0
tendsto_vertical_mean_term m != n  ==>  the vertical mean of the m-th term against
                                            (n+1)^{s} tends to zero
```

The first lemma is the whole point: the conjugate kernel `b^{-s} c^{s}` separates into a factor
depending only on `sigma` and a pure character `e^{i theta t}` whose frequency is
`theta = log c - log b`.  The frequency vanishes exactly when `b = c`, which for `b = m+1`,
`c = n+1` means `m = n`.  So off the diagonal the previous section's uniform bound applies and the
mean vanishes; on the diagonal `theta = 0` and the kernel is the constant `1`.

That is the orthogonality needed for

```
a_n  =  lim_T (1/2T) int_{-T}^{T} F(sigma + it) (n+1)^{sigma+it} dt .
```

Route status:

```
1-6.  DONE
7a.   sigma_b via bounded holomorphic continuation      DONE
7b.   Bohr: sigma_u <= sigma_b                          in progress
        - first coefficient estimate                    DONE
        - vertical mean orthogonality (characters)      DONE
        - off-diagonal Dirichlet terms vanish           DONE
        - interchange of the sum and the mean, giving ||a_n|| <= C
        - Perron / Riesz-mean summation
        - the theorem
```

The remaining interchange is the one genuinely infinite step: uniform convergence on the half-plane
lets the mean pass through the series, after which the diagonal term contributes `a_n` and every
other term contributes zero by the theorem above.

## Lean progress — the coefficient formula, exactly, for finite sums

`RHTower/DirichletCoeffFormula.lean` (wired, axiom-clean).

```
cpow_neg_mul_cpow_self          b^{-s} b^{s} = 1
continuous_kernel_term          each conjugate-kernel term is continuous in t
tendsto_vertical_mean_diagonal  the diagonal term has vertical mean equal to its coefficient
tendsto_vertical_mean_term_zero off-diagonal terms have vertical mean zero
tendsto_vertical_mean_partialSum
    lim_T (1/2T) int_{-T}^{T} S_N(sigma+it) (n+1)^{sigma+it} dt  =  a_n        (n < N)
```

For a **finite** sum there is no interchange to justify: the integral of a finite sum is the sum of
the integrals, so the coefficient formula is exact with no analytic hypotheses at all — no
convergence, no boundedness, nothing about `a`.  The diagonal term integrates to the constant `a_n`
because `b^{-s} b^{s} = 1`, and every other term is a nontrivial character killed by the uniform
bound of two sections ago.

This reroutes the remaining step.  The plan recorded earlier was to pass the vertical mean through
the infinite series; that is not needed.  Instead:

```
given eps, uniform convergence gives N with ||F - S_N|| <= eps on the half-plane,
so ||S_N|| <= C + eps there;  the mean above extracts a_n from S_N exactly;
and the trivial bound on the mean gives  ||a_n|| <= (C + eps) (n+1)^sigma ;
let eps -> 0.
```

Only the finite coefficient formula and a trivial integral bound are involved, and the infinite
interchange disappears entirely.

Route status:

```
1-6.  DONE
7a.   sigma_b via bounded holomorphic continuation      DONE
7b.   Bohr: sigma_u <= sigma_b                          in progress
        - first coefficient estimate                    DONE
        - vertical mean orthogonality (characters)      DONE
        - off-diagonal Dirichlet terms vanish           DONE
        - coefficient formula for finite sums           DONE
        - ||a_n|| <= C (n+1)^sigma  (eps-argument above)
        - Perron / Riesz-mean summation
        - the theorem
```

## Lean progress — Bohr's coefficient estimate, all coefficients

`RHTower/DirichletCoeffBound.lean` (wired, axiom-clean).

```
norm_coeff_le
    uniform convergence on Re s >= x,  ||F|| <= C there,  sigma >= x
      ==>  ||a_n||  <=  C (n+1)^sigma       for every n
```

The epsilon-argument sketched in the previous section, carried out: uniform convergence gives a cut
`N` past which `||S_N|| <= C + eps` on the half-plane; the exact coefficient formula for the finite
sum extracts `a_n` as a vertical mean; the trivial bound on a mean gives
`||a_n|| <= (C + eps)(n+1)^sigma`; and `eps -> 0` closes it.  No interchange of limits appears
anywhere in the proof.

This is Bohr's coefficient estimate in full, generalising `norm_coeff_zero_le` from the first
coefficient (the case `n = 0`, `sigma` arbitrary, where `(n+1)^sigma = 1`) to all of them.

Route status:

```
1-6.  DONE
7a.   sigma_b via bounded holomorphic continuation      DONE
7b.   Bohr: sigma_u <= sigma_b                          in progress
        - first coefficient estimate                    DONE
        - vertical mean orthogonality (characters)      DONE
        - off-diagonal Dirichlet terms vanish           DONE
        - coefficient formula for finite sums           DONE
        - ||a_n|| <= C (n+1)^sigma                      DONE
        - Perron / Riesz-mean summation
        - the theorem
```

What remains is the summation half: given the coefficient bounds, recover uniform convergence.  The
classical device is a Riesz (or Cesaro) mean of the Dirichlet series, whose uniform convergence
follows from the coefficient bounds by an elementary Abel argument, plus a Tauberian step returning
to ordinary convergence.  That is the last piece of Bohr's theorem, and the last mathematical step
between this card and `Haar(M) = 0`.

## Lean progress — the absolute-convergence comparisons

`RHTower/DirichletAbsoluteAbscissa.lean` (wired, axiom-clean).

```
norm_dirichletTerm_le                each term is bounded by its majorant on Re s >= x
uniformlyConvergesOn_of_summable     a summable majorant gives uniform convergence
abscissaOfUnifConv_le_of_summable    sigma_u <= sigma_a
exists_norm_coeff_le_of_convergesAt  convergence at s0  ==>  ||a_n|| <= C (n+1)^{Re s0}
```

The first three are the Weierstrass test for Dirichlet series, giving the upper comparison
`sigma_c <= sigma_u <= sigma_a` (the lower half being `abscissaOfConv_le_abscissaOfUnifConv`).

The last is the coefficient bound in the *other* direction from Bohr's estimate: it comes from
nothing but the vanishing of the terms of a convergent series, read against the kernel, and it is
the ingredient of Bohr's width-one inequality

```
sigma_a  <=  sigma_c + 1 ,
```

since `sum ||a_n|| (n+1)^{-x} <= C sum (n+1)^{Re s0 - x}` converges once `x > Re s0 + 1`.

Note the pair of coefficient estimates now available runs in both directions:

```
convergence at s0        =>  ||a_n|| <= C (n+1)^{Re s0}        (this section)
uniform convergence
  + boundedness by C     =>  ||a_n|| <= C (n+1)^{sigma}        (Bohr, previous section)
```

The second is the sharp one — the constant is the sup norm itself, with no loss.

## Lean progress — Bohr's width-one inequality; the abscissa chain is closed

`RHTower/DirichletWidthOne.lean` (wired, axiom-clean).

```
DirichletAbsConvAt a x, abscissaOfAbsConvShift a
summable_shift_rpow_neg                  a shifted p-series converges for p > 1
absConvAt_of_convergesAt                 convergence at s0  ==>  absolute convergence for
                                             x > Re s0 + 1
abscissaOfAbsConvShift_le_of_convergesAt the same as an abscissa bound
abscissaOfUnifConv_le_abscissaOfAbsConvShift    sigma_u <= sigma_a
```

With the earlier `abscissaOfConv_le_abscissaOfUnifConv` this closes the classical chain

```
sigma_c  <=  sigma_u  <=  sigma_a  <=  sigma_c + 1 ,
```

every inequality now a Lean theorem.  The width-one bound is elementary: convergence at `s0` bounds
the coefficients by `C (n+1)^{Re s0}` (previous section), and the majorant
`sum (n+1)^{Re s0 - x}` converges once `x > Re s0 + 1`.

For the card this is the quantitative frame the Helson zeta lives in: `sigma_c = 1/2` almost surely
(the divergence half is formal), `sigma_a = 1` always, and the whole question of the natural boundary
is where `sigma_b` sits between them.  What Bohr's theorem supplies — and what remains — is that
`sigma_b = sigma_u`, which by the chain above forces `sigma_b >= sigma_c = 1/2` and closes
`Haar(M) = 0`.

Route status:

```
1-6.  DONE
7a.   sigma_b via bounded holomorphic continuation      DONE
7b.   Bohr: sigma_u <= sigma_b                          in progress
        - first coefficient estimate                    DONE
        - vertical mean orthogonality (characters)      DONE
        - off-diagonal Dirichlet terms vanish           DONE
        - coefficient formula for finite sums           DONE
        - ||a_n|| <= C (n+1)^sigma                      DONE
        - abscissa chain sigma_c <= sigma_u <= sigma_a <= sigma_c + 1   DONE
        - Perron / Riesz-mean summation
        - the theorem
```
