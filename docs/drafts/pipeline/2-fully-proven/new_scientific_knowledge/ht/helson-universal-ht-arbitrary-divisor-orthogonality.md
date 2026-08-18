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

## Lean progress — uniqueness of Dirichlet coefficients

`RHTower/DirichletUniqueness.lean` (wired, axiom-clean).

```
coeff_eq_zero_of_tendstoUniformlyOn_zero   sum = 0 uniformly on a half-plane  ==>  every a_n = 0
dirichletPartialSum_sub
coeff_eq_of_tendstoUniformlyOn             two series with the same sum have the same coefficients
```

This is Bohr's coefficient estimate at `C = 0`: the bound `||a_n|| <= C (n+1)^sigma` degenerates to
`||a_n|| <= 0`.  No separate argument is needed — in particular no analytic continuation and no
identity theorem for holomorphic functions, both of which the textbook proofs use.

It matters for the card because the Euler-product manipulations on `Z_chi` all presuppose that a
Dirichlet expansion determines its coefficients; that is now a theorem in the conditionally
convergent setting, where mathlib's `LSeries` uniqueness (absolutely convergent) does not reach.

### Note on the size of what remains

The remaining item, Perron/Riesz-mean summation, is the one genuinely heavy analytic step: it needs
a contour representation of the Riesz mean

```
R_lambda(s)  =  (1/2 pi i) int_{(c)} F(s+w) e^{lambda w} / w^2 dw ,
```

hence residue calculus on vertical lines, none of which exists in mathlib in usable form.  This is
correctly described as a multi-session build in its own right, not a final assembly.  Everything
around it — the abscissa theory, both coefficient estimates, uniqueness, the two easy halves of the
Bohr comparison — is now formal and independent of it.

## CORRECTION — the Perron engine already exists in the corpus

A corpus search (`formal_tools.py research "Perron formula vertical line integral contour Mellin"`)
finds the Perron machinery is already built and unconditional.  The previous section's claim that
Perron summation is "a multi-session build in its own right" was made without searching and is
WRONG.  What exists:

```
RHTower/QuietCrossingRigidity.lean
  perronKernelG                         the weight u |-> max(1-u, 0)
  perronKernel_mellin                   mellin perronKernelG s = 1/(s(s+1))  for Re s > 0
  perronKernel_mellinConvergent
  perronKernel_verticalIntegrable       absolute convergence on Re s = c > 0
  perronKernel_inversion                (1/2 pi) int y^{c+it}/((c+it)(c+it+1)) dt = max(1 - 1/y, 0)
  smoothed_perron_sum                   sum_n a_n max(x-n, 0)
                                          = (1/2 pi) int L(c+it) x^{(c+it)+1}/((c+it)((c+it)+1)) dt
  perronE, perronKink_second_difference, perronSecondDiff_integral, quiet_crossing_rigidity

HTGeometry/PerronKernelSegments.lean
  norm_integral_horizontal_le, norm_integral_vertical_edge_cpow_le   (contour segment bounds)
HTGeometry/VerticalStripContourShift.lean
  integral_vertical_line_eq_of_horizontal_tendsto                    (contour shift)
HTGeometry/SmoothWeightShift.lean
  integral_mul_mellin_smoothWeight_shift    the Perron contour shift for F holomorphic and
                                                polynomially bounded on a strip
HTGeometry/integrable_inv_sq_add_sq                                  (already present)
```

`smoothed_perron_sum` is exactly the Riesz/Cesaro-mean representation Bohr's theorem needs, and the
strip shift is exactly the step that moves the contour left toward the boundedness abscissa.  So the
remaining assembly is: apply `smoothed_perron_sum` at an abscissa of absolute convergence (which
exists by the width-one bound), shift the contour to `theta + eps` using
`integral_mul_mellin_smoothWeight_shift`, bound the shifted integral by the sup norm of `F` times the
kernel mass, and run the Tauberian step from `A_1(x) = O(x^{theta+eps+1})` back to convergence.

## Lean progress — the bridge to the `LSeries` indexing

`RHTower/DirichletLSeriesBridge.lean` (wired, axiom-clean).

```
term_succ_eq                             LSeries.term b s (n+1) = b (n+1) (n+1)^{-s}
dirichletPartialSum_eq_sum_term          the two conventions have identical partial sums
convergesAt_iff_tendsto_sum_term
tendstoUniformlyOn_sum_term_of_uniformlyConvergesOn
```

The conditional-convergence development here indexes from zero (`sum a_n (n+1)^{-s}`), while
mathlib's `LSeries` and the corpus's Perron engine index from one.  This bridge identifies the two,
so the abscissa theory, both coefficient estimates and the uniqueness theorem apply directly to
objects stated in the `LSeries` convention — in particular to `smoothed_perron_sum`.

## AUDIT — the corpus already has a Bohr almost-periodic theory; what I duplicated

A second search (`research "bohrCoefficient mean value almost periodic bound sup norm"`) shows the
corpus carries a substantial Bohr theory that overlaps some of this session's work:

```
HTGeometry/BohrMeanValue.lean            exists_bound_of_isBohrAlmostPeriodic
HTGeometry/BohrMeanInvariance.lean       norm_bohrCoefficient_sub_le   (coefficients 1-Lipschitz
                                              for the uniform distance)
HTGeometry/BohrParsevalIdentity.lean     tsum_normSq_bohrCoefficient
HTGeometry/BohrUniqueness.lean           eq_of_bohrCoefficient_eq, exists_bohrCoefficient_ne_zero
HTGeometry/BohrMeanTriangle.lean, BohrMeanMonotone.lean
HTGeometry/StripAlmostPeriodicBounds.lean  exists_bound_of_isStripAlmostPeriodicOn,
                                              exists_deriv_bound, exists_lipschitzOnWith_closedStrip
HTGeometry/DirichletStripAlmostPeriodic.lean  isStripAlmostPeriodic_dirichlet
HTGeometry/DirichletBohrSpectrum.lean    bohrCoefficient_dirichlet_line, isBohrHullFrequency_dirichlet
```

**What this means for the modules built earlier this session.**  `norm_bohrCoefficient_sub_le` with
`g = 0` gives `||bohrCoefficient f lambda|| <= sup ||f||`, and `bohrCoefficient_dirichlet_line`
identifies that coefficient with `a_m e^{-lambda_m sigma}`.  Together they give

```
||a_m|| <= C e^{lambda_m sigma} = C (m+1)^sigma ,
```

which is exactly `DirichletCoeffBound.norm_coeff_le`.  So that theorem — and the vertical-mean
chain leading to it (`VerticalMeanCharacter`, `DirichletTermMean`, `DirichletCoeffFormula`) — was
**derivable from the corpus** and should have been obtained that way.  The proofs written here are
independent and self-contained (they use no almost-periodic theory at all), but they are not new
capability, and the correct entry point for future work is the Bohr modules above.

Not duplicated, and still the missing content:

```
Bohr's theorem  sigma_u <= sigma_b       -- absent from the corpus and from mathlib
```

plus the abscissa scaffolding built this session (`abscissaOfConv`, `abscissaOfUnifConv`,
`abscissaOfBddHolo`, `abscissaOfAbsConvShift` and the chain
`sigma_c <= sigma_u <= sigma_a <= sigma_c + 1`), which the corpus did not have.

## Lean progress — the bridge to general Dirichlet exponents

`RHTower/DirichletExponentBridge.lean` (wired, axiom-clean).

```
ordinaryExponent n  =  log(n+1)
cpow_neg_eq_exp_neg_log        (n+1)^{-s} = exp(-log(n+1) s)
dirichletPartialSum_eq_expSum  the partial sums are general Dirichlet partial sums
ordinaryExponent_strictMono, ordinaryExponent_injective
```

This is the second bridge (after the `LSeries` one) and the one that matters for the audit above: it
puts the ordinary series into the exact shape `sum a_n e^{-lambda_n s}` that
`isStripAlmostPeriodic_dirichlet` and `bohrCoefficient_dirichlet_line` consume, with the injectivity
of the exponents that the frequency-separation argument requires.  With it, the corpus's Bohr
spectrum theory applies directly to the objects of this development.

## Lean progress — the inverse of the smoothing

`RHTower/SmoothedInverseMellin.lean` (wired, axiom-clean).  Searched first: not in the corpus.

```
aestronglyMeasurable_cpow_Ioi   measurability of x |-> x^w on a positive ray
integral_Ioi_cpow_neg_succ      int_a^infty x^{-s-1} dx = a^{-s}/s          (Re s > 0)
integral_Ioi_smoothed_kernel    int_n^infty (x - n) x^{-s-2} dx = n^{-s}/(s(s+1))
```

This is the exact inverse of `smoothed_perron_sum`: that theorem turns the Dirichlet series into
`A_1(x) = sum a_n max(x-n, 0)`, and this one turns `A_1` back into the series, term by term, since

```
s(s+1) int_1^infty A_1(x) x^{-s-2} dx  =  sum_n a_n n^{-s} .
```

The proof is the improper fundamental theorem of calculus twice, with the antiderivative
`-x^{-s}/s`, plus the identity `1/s - 1/(s+1) = 1/(s(s+1))` that gives the kernel its name.

Why this is the operative step for Bohr: a growth bound `A_1(x) = O(x^alpha)` makes the integral
above absolutely convergent for `Re s > alpha - 1`, which is how the contour-shifted Perron bound
turns into a statement about the series.  The chain is now

```
smoothed_perron_sum       series  ->  A_1                       (corpus)
contour shift             A_1(x) = O(x^{theta+eps+1})           (corpus: strip shift + sup bound)
integral_Ioi_smoothed_kernel   A_1  ->  series, convergent for Re s > theta+eps   (this section)
```

with the third arrow's *absolute convergence* now available; what remains is the Tauberian passage
from that to uniform convergence of the partial sums, and then `sigma_u <= sigma_b`.

## Lean progress — the discrete side of the smoothing

`RHTower/SmoothedPartialSumIdentity.lean` (wired, axiom-clean).  Searched: the corpus has discrete
Abel summation (`HTGeometry/DiscreteAbelIcc.sum_mul_eq_partial_mul_diff`, real-valued) and a
specialised discrete Fubini (`WeightedSigmaFubini.weighted_sigma_eq`), but not this identity.

```
sum_sub_mul_eq_sum_partialSum          sum_{n<N} (N-n) a_n  =  sum_{k<N} sum_{n<=k} a_n
smoothedPartialSum a N                 the smoothed sum at an integer point
smoothedPartialSum_succ                A_1(N+1) = A_1(N) + A(N+1)
smoothedPartialSum_second_difference   A_1(N+2) - 2 A_1(N+1) + A_1(N) = a_{N+1}
```

Both sides of the first identity count the pairs `(n,k)` with `n <= k < N`, weighted by `a_n`; it is
the discrete form of `A_1(x) = int_1^x A(u) du`.

The second difference is the discrete inversion: **the smoothing can be undone exactly**, one
coefficient at a time, with no analysis.  That is the discrete counterpart of the corpus's
`perronKink_second_difference` (which does the same for the continuous kink at half-integers) and it
is what makes a growth bound on `A_1` usable: bounding `A_1` bounds every second difference, hence
every coefficient, and — via the first identity — every ordinary partial sum in terms of the
smoothed ones.

This is the Tauberian side of Bohr's theorem in its discrete form.  What remains on that side is the
quantitative step: from `A_1(N) = O(N^alpha)` to uniform convergence of `sum a_n n^{-s}` for
`Re s > alpha - 1`.

## Lean progress — the unit first difference

`RHTower/DirichletFirstDifference.lean` (wired, axiom-clean).

```
rpow_sub_rpow_succ_le            x^{-p} - (x+1)^{-p}  <=  p x^{-p-1}                (p > 0, x > 0)
norm_cpow_neg_succ_sub_succ_le   || x^{-(s+1)} - (x+1)^{-(s+1)} ||  <=  ||s+1|| x^{-Re s - 2}
```

The real bound is the fundamental theorem of calculus on `[x, x+1]` with the integrand `p y^{-p-1}`
bounded by its left-endpoint value.  Feeding it into the increment estimate of the kernel section at
exponent `s+1` makes the factor `Re s + 1` **cancel exactly**, leaving a clean derivative-scale
bound: one unit step costs one power of `x` and one factor of the exponent.

This is the second rung of the estimate ladder:

```
||x^{-s} - y^{-s}||            <= (||s||/Re s)(x^{-Re s} - y^{-Re s})     kernel estimate
||x^{-(s+1)} - (x+1)^{-(s+1)}|| <= ||s+1|| x^{-Re s - 2}                   this section
||second difference of (n+1)^{-s}|| <= ||s|| ||s+1|| (n+1)^{-Re s - 2}     next
```

The third is what a doubly Abel-summed Dirichlet series needs: with the smoothed partial sums
`A_1(j)` bounded by `C j^alpha`, the sum `sum_j ||A_1(j)|| ||Delta^2 b_j||` is dominated by
`C ||s|| ||s+1|| sum_j j^{alpha - Re s - 2}`, convergent exactly when `Re s > alpha - 1` — which is
the Tauberian conclusion needed for Bohr.

## Lean progress — the second difference: the estimate ladder is complete

`RHTower/DirichletSecondDifference.lean` (wired, axiom-clean).

```
cpow_neg_sub_eq_integral         a^{-s} - b^{-s} = int_a^b s x^{-s-1} dx        (Re s > 0)
norm_second_difference_cpow_le   || x^{-s} - 2(x+1)^{-s} + (x+2)^{-s} ||
                                     <=  ||s|| ||s+1|| x^{-Re s - 2}
```

The first difference is an integral of the derivative; subtracting the shifted copy collapses the
second difference into a *single* integral of a first difference at exponent `s+1`, which the
previous section bounds.  Two unit steps cost two powers of the exponent and two powers of `x`, with
no constant left over.

The estimate ladder is now complete:

```
||x^{-s} - y^{-s}||                  <= (||s||/Re s)(x^{-Re s} - y^{-Re s})
||x^{-(s+1)} - (x+1)^{-(s+1)}||      <= ||s+1|| x^{-Re s - 2}
||Delta^2 (n+1)^{-s}||               <= ||s|| ||s+1|| (n+1)^{-Re s - 2}
```

Together with `sum_sub_mul_eq_sum_partialSum` and `smoothedPartialSum_second_difference`, the
Tauberian step is now a finite assembly: double Abel summation expresses the partial sums of
`sum a_n (n+1)^{-s}` through `A_1(j)` and `Delta^2 b_j`, and the two bounds

```
||A_1(j)|| <= C j^alpha ,      ||Delta^2 b_j|| <= ||s|| ||s+1|| (j+1)^{-Re s - 2}
```

make the resulting series dominated by `C ||s|| ||s+1|| sum_j j^{alpha - Re s - 2}`, absolutely
convergent precisely when `Re s > alpha - 1`, and locally uniformly so in `s`.  That is
`sigma_c <= alpha - 1` with uniformity, which is the Tauberian half of Bohr.

## CORRECTION — the Tauberian implication I stated is FALSE

The previous section claimed that the double Abel identity plus the bounds

```
||A_1(j)|| <= C j^alpha ,      ||Delta^2 b_j|| <= ||s|| ||s+1|| (j+1)^{-Re s - 2}
```

give `sigma_c <= alpha - 1`.  **That implication is false.**  The absolutely convergent part of the
double Abel identity does converge for `Re s > alpha - 1`, but the two boundary terms do not: the
term `b(N-1) A(N)` needs a bound on the *ordinary* partial sums, which `A_1 = O(N^alpha)` does not
supply.

Explicit counterexample: let the ordinary partial sums be `A(k) = (-1)^k k^alpha`.  Then
`A_1(N) = sum_{k<N} A(k) = O(N^alpha)` (alternating), while `a_n = A(n) - A(n-1) ~ 2(-1)^n n^alpha`,
so the series is `sum (-1)^n n^{alpha - s}`, whose abscissa of convergence is exactly `alpha`, not
`alpha - 1`.

So a growth bound on the *smoothed* sums alone loses a full unit relative to the naive count, and
recovering it is precisely the genuine Tauberian content of Bohr's theorem — it is not a bookkeeping
step.  Recorded here so the next pass does not attempt the false route.

## Lean progress — the correct statement: polynomially bounded partial sums

`RHTower/DirichletPolyBoundedAbel.lean` (wired, axiom-clean).

```
norm_cpow_unit_diff_le      || x^{-w} - (x+1)^{-w} ||  <=  ||w|| x^{-Re w - 1}   (Re w > 0)
tendsto_dirichlet_partialSum_of_poly_bounded
    || sum_{n<N} a_n ||  <=  C (N+1)^alpha      ==>   the series converges for Re s > alpha
```

This is the true theorem in the neighbourhood of the false one, and the counterexample above shows
its exponent is **sharp**: with `A(k) = (-1)^k k^alpha` the abscissa is exactly `alpha`.  The bounded
case `alpha = 0` is the earlier `tendsto_dirichlet_partialSum_of_bounded`.

The first lemma generalises the unit-difference bound from exponent `s+1` to any exponent with
positive real part, which is what the boundary-term analysis needs.

## Lean progress — the Riesz-mean method: kernel size, Mellin pair, and the discrete average

Three modules, all wired into `GaloisForLFunctions.RHTower` and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

```
RHTower/RieszMeanKernelBound.lean
  rieszKernel lam c t          e^{lam w} / w^2  at  w = c + i t
  norm_rieszKernel             ‖e^{lam w}/w^2‖ = e^{lam c} / (c^2 + t^2)
  integrable_norm_rieszKernel
  integral_norm_rieszKernel    (2 pi)^{-1} ∫ ‖...‖ dt = e^{lam c} / (2 c)
  rieszKernel_bound_at_optimum at c = 1/lam the value is  e lam / 2
  rieszKernel_bound_min        e lam / 2 <= e^{lam c}/(2c)  for every c > 0
  integral_norm_rieszKernel_optimum

RHTower/RieszMellinPair.lean
  log_le_rpow_div              log x <= (2/a) x^{a/2}      (x >= 1, a > 0)
  tendsto_log_mul_rpow_neg     log x . x^{-a} -> 0
  rieszMellinAntideriv         -(log y) y^{-w}/w - y^{-w}/w^2
  hasDerivAt_rieszMellinAntideriv
  tendsto_rieszMellinAntideriv
  integrableOn_log_cpow_neg_succ
  integral_Ioi_log_cpow_neg_succ    ∫_1^∞ (log x) x^{-w-1} dx = 1/w^2   (Re w > 0)

RHTower/RieszLogPartialSum.lean
  sum_log_increment            ∑_{m<N} (log(m+1) - log m) = log N
  log_increment_nonneg
  rieszLogSum_eq_sum_partialSum
        ∑_{n<N} a_n (log N - log(n+1)) = ∑_{m<N} (log(m+1) - log m) . ∑_{n<m} a_n
  norm_rieszLogSum_le          partial sums bounded by B  =>  Riesz mean bounded by B log N
```

### Why these three

The Riesz-mean method replaces the truncated Perron kernel `x^w/w` — whose vertical-line integral
diverges, forcing a truncation and an error analysis — by `x^w/w^2`, which is absolutely integrable
on every vertical line in the right half-plane.  `integral_norm_rieszKernel` computes that integral
*exactly*, as a Poisson normalisation, and `rieszKernel_bound_min` shows the optimal abscissa is
`c = 1/lam`, where the bound is `e lam / 2` — linear in `lam`, which is the source of the
logarithmic bound on partial sums.  A corpus search supplied `HTGeometry.integral_inv_sq_add_sq`,
so the Poisson normalisation itself was not rebuilt.

`integral_Ioi_log_cpow_neg_succ` is the transform identity that makes `1/w^2` the right kernel: it
is the Mellin transform of the truncated logarithm, so the vertical-line representation of a Riesz
mean is a Dirichlet series with the weights `log(N/n)`.  Nothing of this exists in mathlib; the
antiderivative, its vanishing at infinity, and the domination `log x <= (2/a) x^{a/2}` are all built
here.

`rieszLogSum_eq_sum_partialSum` is the discrete half, and needs no analysis at all: telescoping the
weight `log N - log n` and exchanging two finite sums expresses the Riesz mean as a *nonnegatively*
weighted average of the partial sums, with total weight `log N`.

### What remains on the Bohr route

The direction still missing is the Tauberian one: from a bound on the Riesz means recover a bound on
the partial sums.  The classical step compares `R` at `lam` and at `lam + h`,

```
R_{lam+h} - R_lam = h . A(N) + (tail over N < n <= N e^h) ,
```

and the tail is controlled by the coefficient bound `norm_coeff_le`, which is already formal in this
tree.  After that, `tendsto_dirichlet_partialSum_of_poly_bounded` converts the resulting
`O(log N)` partial-sum bound into convergence, and the uniformity in `s` is what upgrades
`sigma_c <= sigma_b` to `sigma_u <= sigma_b`.

## Lean progress — the Tauberian step for Riesz means

`RHTower/RieszTauberian.lean` (wired, axiom-clean).

```
sum_log_increment_Ico       ∑_{N<=m<M} (log(m+1) - log m) = log M - log N
rieszLogSum_sub             R(M) - R(N) = ∑_{N<=m<M} (log(m+1) - log m) . A(m)
norm_partialSum_le_of_rieszLogSum_bound
        ‖R(M)‖ <= B ,  ‖R(N)‖ <= B ,  ‖A(m) - A(N)‖ <= eps  on  [N, M)
          ==>   ‖A(N)‖ <= 2 B / (log M - log N) + eps
```

The block form is exact and costs nothing: two Riesz means differ by precisely the tail of the
logarithmic average, because `R(K) = ∑_{m<K} w_m A(m)` and the ranges are nested.  Splitting
`A(m) = A(N) + (A(m) - A(N))` and using that the block weights sum to `log M - log N` isolates
`A(N)`, and the two Riesz bounds plus the increment bound give the displayed estimate.

This is the Tauberian direction the previous section identified.  Note what it does and does not
say: bounded Riesz means alone say nothing about an individual partial sum — the statement needs the
increment control `eps` over a block, and the bound trades `2B/h` against `eps` as the block length
`h` grows.

### What the assembly still has to choose

Instantiating this at a Dirichlet series bounded by `M` on a half-plane needs the block and the
increment bound chosen together.  The naive choice — block `[N, N(1+delta)]`, increments bounded
coefficientwise by `norm_coeff_le` — gives `‖A(N)‖ = O(sqrt(N^{1-sigma} log N))`, which is *not*
the classical `O(log N)`; recorded so the next pass does not spend the effort rediscovering that the
coefficientwise tail bound is too lossy.  The classical argument uses the analyticity of the sum on
the half-plane rather than a termwise bound on the block, and that is the remaining choice.

## Lean progress — the continuation stratum is a TAIL EVENT

`HTGeometry/ContinuableStratumInvariant.lean` (wired, axiom-clean).

```
eulerRatio a b b'            (1 - b a^{-s}) / (1 - b' a^{-s})
meromorphicAt_eulerRatio     meromorphic at every point, for a != 0
meromorphicOn_mul_eulerRatio a meromorphic function times a finite product of ratios stays
                                 meromorphic on the plane
continuableStratum_invariant
    {p | chi p != psi p} finite  and  chi in continuableStratum
      ==>  psi in continuableStratum
```

The corpus already had `continuableStratum` and the fact that every *finite modification of the
trivial phase* lies in it.  This is the strictly stronger statement: continuability is preserved by
finite modification starting from **any** continuable phase, not only from `1`.  That is exactly the
tail-event property `M` needs — the stratum cannot be distinguished by any finitely many prime
phases.

The proof multiplies the Euler product by the finite correction `∏_{p in S} (1 - chi_p p^{-s}) /
(1 - psi_p p^{-s})`: each ratio is a quotient of entire functions, hence meromorphic on the plane,
and on `Re s > 1` the corrected product is the modified Euler product because the unmodified factors
never vanish there.

### What the zero-one law still needs

`FiniteModificationZeroOne.measure_eq_zero_or_one_of_invariant` consumes exactly two inputs: the
invariance just proved, and `MeasurableSet continuableStratum`.  The measurability is the open point,
and it is not cosmetic: the stratum is defined by an existential over meromorphic functions on `ℂ`,
so it is not measurable by inspection — it needs a countable reduction (for instance, exhausting `ℂ`
by discs and the continuation by rational-coefficient approximations).  Recorded so the next pass
does not assume it.

Note also the index type: the corpus law is stated for products indexed by `ℕ`, while the phase
torus is indexed by `Nat.Primes`; the transfer along a countable equivalence is routine but not yet
written.

## Lean progress — the zero-one law now applies to products indexed by the primes

`HTGeometry/FiniteModificationZeroOneEquiv.lean` (wired, axiom-clean).

```
measure_infinitePi_eq_zero_or_one_of_invariant_equiv
    an equivalence e : ℕ ≃ iota transports the finite-modification zero-one law to products
    indexed by iota

natEquivPrimes : ℕ ≃ Nat.Primes

measure_infinitePi_primes_eq_zero_or_one_of_invariant
    the law, stated directly for products indexed by the primes
```

This closes the index-type mismatch recorded earlier: the corpus law is proved for products over
`ℕ`, the phase torus is a product over `Nat.Primes`, and the transport is now a theorem rather than
a remark.

The transport is exactly what one expects and nothing more.  `MeasurableEquiv.piCongrLeft` is a
measurable equivalence between the two products, mathlib's `Measure.infinitePi_map_piCongrLeft`
says it carries the product measure to the product measure, and finite-modification invariance
crosses because a finite set of coordinates has finite image.  The one technical point worth
recording: the invariance transfer must be phrased at indices of the form `e m`, never at a general
`i` — writing `x (e.symm i)` produces a term of type `Y (e (e.symm i))` rather than `Y i`, and the
resulting rewrite is not type-correct.

With this and `continuableStratum_invariant`, the zero-one law for the continuation stratum needs
exactly one input: `MeasurableSet continuableStratum`.

## Lean progress — the Helson zeta is defined on ALL of the phase torus

`HTGeometry/HelsonEulerMultipliable.lean` (wired, axiom-clean).

```
summable_prime_rpow_neg        ∑_p p^{-sigma} converges for sigma > 1
norm_eulerFactor_sub_one_le    ‖ (1 - chi_p p^{-s})^{-1} - 1 ‖ <= 2 p^{-Re s}
multipliable_helsonEuler       the Euler product is multipliable for EVERY unimodular phase,
                                   on Re s > 1
```

The corpus previously had the Euler product only for phases equal to `1` off a finite set
(`hasProd_helsonEuler`), which is enough for the dense half of the seam but not to *define* `Z_chi`
on the whole torus.  This closes that: the Euler factors differ from `1` by
`chi_p p^{-s} / (1 - chi_p p^{-s})`, whose norm is at most `2 p^{-Re s}` because
`‖chi_p p^{-s}‖ <= p^{-Re s} <= 2^{-Re s} < 1/2`, and the prime sum of `p^{-Re s}` converges above the
abscissa one.

So `Z_chi(s) = ∏_p (1 - chi_p p^{-s})^{-1}` is a well-defined function of `chi` on the whole phase
torus for `Re s > 1`, which is what any measurability argument for `continuableStratum` has to start
from — the stratum is `{chi | the germ of Z_chi at Re s > 1 continues meromorphically}`, and until
now the germ itself was only known to exist on a dense subset.

## Lean progress — the continuation stratum is BOREL, and obeys a zero-one law

`HTGeometry/HelsonStratumMeasurable.lean` and `HTGeometry/HelsonStratumZeroOne.lean` (wired,
axiom-clean), on top of four new supporting modules.

```
measurableSet_continuableStratum          MeasurableSet continuableStratum
measure_infinitePi_continuableStratum_eq_zero_or_one
      for every product probability measure on the phase torus,
      measure(M) = 0  or  measure(M) = 1
continuableStratum_dense_codense_measurable_zeroOne
      M is dense, has dense complement, is Borel, and has measure 0 or 1
```

This closes the open point recorded above: the zero-one law consumed exactly two inputs, the
finite-modification invariance (already owned) and the measurability of the stratum, and the second
was *not* cosmetic — membership is an existential over meromorphic functions on the plane.

### The descriptive-set-theoretic content

The stratum is not merely measurable, it is `F_sigma-delta`.  The reduction is:

```text
chi in M   <=>   for every level N there are  d, B  in N,
                 root positions  u : Fin d -> {|u| <= rho_N + 1, Re u <= -1},
                 coefficients   c : N -> C  with  ‖c n‖ rho_N^n <= B,
                 such that      prod_i (s - 2 - u_i) . Z_chi(s) = sum_n c_n (s-2)^n
                 for all s with |s - 2| < rho_N and Re s > 1,      rho_N = N + 3.
```

Both parameters range over *compact* sets — a closed polydisc of root positions and a product of
closed balls of coefficients — and the identity is a closed condition.  A projection along a compact
factor is a closed map, so each level-and-size stratum is closed; the stratum is the countable
intersection over `N` of the countable union over `(B, d)`.

Why the encoding is the right one:

- **Meromorphic continuation to the plane is not a countable condition on one disc**, because a
  meromorphic function on `C` can have infinitely many poles, so no single polynomial clears them.
  Exhausting `C` by discs and clearing the poles of each disc separately is what makes the pole data
  finite, hence compact.
- **The pole positions may be confined to `Re s <= 1`**: on `Re s > 1` a continuation agrees with the
  Euler product, which is holomorphic there.  This is what forces the constructed continuation to
  agree with `Z_chi` on the *whole* half plane rather than off a discrete set — the polynomial
  cannot vanish where the identity is asserted.
- **Coefficient bounds replace Montel's theorem.**  The alternative encoding — the continuation
  itself, as a holomorphic function bounded on the disc — has a compact parameter space only by
  normal families.  Geometric bounds on Taylor coefficients give the same compactness by Tychonoff,
  and the radius-of-convergence estimate `‖c_n‖ r^n` bounded is exactly what a holomorphic function
  on a larger disc supplies.

### The two directions

`exists_levelData_of_mem_continuableStratum` (necessity) takes the divisor of the continuation on
the disc, which has finite support because the disc is relatively compact, and clears the poles with
the factorized rational function of the divisor's negative part.  The product is put into
meromorphic normal form — necessary, because a meromorphic function may carry arbitrary junk values
at its poles — and the normal form is analytic exactly because its divisor is non-negative.

`mem_continuableStratum_of_continuationCriterion` (sufficiency) assembles the levels.  Two level
models agree wherever both denominators are non-zero: the two products of one series with the
other's polynomial are holomorphic on the smaller disc and agree near `s = 2`, so the identity
theorem equates them.  Hence all models have a common germ at every point once the finitely many
roots are removed, and the value of the meromorphic normal form at a point does not depend on the
level.  That common value is the continuation.

### Supporting modules

```
HTGeometry/PowerSeriesDiscBridge.lean
  seriesSum                                sum_n c_n w^n
  analyticOnNhd_seriesSum                  geometric coefficient bounds => holomorphic on the disc
  exists_seriesSum_of_differentiableOn     holomorphic on a closed disc => bounded coefficients

HTGeometry/HelsonZetaAnalytic.lean
  instance : CompactSpace PhaseTorus
  hasProdLocallyUniformlyOn_helsonEuler    the Euler product converges locally uniformly in s
  differentiableOn_helsonZetaValue         Z(chi, .) is holomorphic on Re s > 1
  continuous_helsonZetaValue               Z(., s) is continuous on the phase torus
  helsonZetaValue_ne_zero                  Z(chi, s) != 0

HTGeometry/HelsonContinuationData.lean    levelRadius, rootPoly, rootBox, LevelData,
                                          ContinuationCriterion, exists_root_vector
HTGeometry/HelsonCriterionNecessary.lean
HTGeometry/HelsonCriterionSufficient.lean
```

`continuous_helsonZetaValue` and `differentiableOn_helsonZetaValue` both come from mathlib's
`Summable.hasProdUniformlyOn_one_add` / `...LocallyUniformlyOn...`: the same bound
`‖(1 - chi_p p^{-s})^{-1} - 1‖ <= 2 p^{-sigma}` is uniform in `s` on a closed half plane and uniform
in `chi` on the whole torus, so one lemma gives holomorphy in `s` and continuity in `chi`.
Non-vanishing is the observation that the Euler factors and their inverses are both multipliable and
their termwise product is `1`.

### Correction to an earlier entry

The module `HTGeometry/ContinuableStratumInvariant.lean` recorded above **duplicated** corpus content:
`mem_continuableStratum_of_finite_ne` in `HTGeometry/HelsonCubeRootNonContinuation.lean` already
proved finite-modification invariance, and the duplicated names `eulerRatio` /
`meromorphicAt_eulerRatio` made the two modules mutually un-importable.  The duplicate has been
deleted and the zero-one law now uses the corpus theorem.  The invariance is *not* a contribution of
this line of work.

### What the zero-one law does and does not decide

It gives `measure(M) in {0, 1}` for every product probability measure, in particular for Haar.  It
does **not** give `measure(M) = 0`, and the gap cannot be closed by the tools here:

- `M` is invariant under changing one coordinate, so every fibre of the projection that forgets one
  prime phase is all-or-nothing.  No Fubini or one-coordinate argument can see the difference.
- The complement is dense (the constant primitive cube root of unity and its finite modifications
  are noncontinuable, already formal), but a dense complement is compatible with full measure.
- The cube-root obstruction `Z_chi . Z_{omega chi} . Z_{omega^2 chi} = Z_{chi^3}(3s)` is homogeneous
  in the three rotated phases; the contradiction at `chi = 1` uses the *pole* of `zeta` and does not
  survive rotation to a generic phase.

So `measure(M) = 0` remains exactly the Saksman--Webb input the card names: it is equivalent, given
the above, to `measure(M) != 1`, i.e. to the noncontinuable phases having positive measure.

## Lean progress — Pong's conclusion in ANALYTIC form for an arbitrary phase

`HTGeometry/HelsonPhaseAnalyticJets.lean` (wired, axiom-clean).

```
phasePrimeArithmeticFunction / phasePrimeFiniteAbscissa / phasePrimeShiftedRotatedJet
    the prime carrier of a unimodular phase, its finite-abscissa membership, and its
    shifted rotated jets

phasePrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn
    a shifted jet is the corresponding prime column of the shift-jet palette

phasePrimeShiftedRotatedJet_tailIndependent
    the palette of a nowhere-vanishing phase has full coefficient-tail rank

phasePrimeShiftedRotatedJets_algebraicIndependent
phasePrimeShiftedUpperEndGerm_jets_algebraicIndependent
    ** the rectangle is algebraically independent as actual analytic upper-end germs **
phasePrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeCoefficientField
phasePrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeRationalCoefficientField
    ** and over the card's E_fin(s) **
```

The corpus already owned two halves that had never been joined: `PrimeDirichletAnalyticTransfer`
carried the whole chain from tail independence of prime columns to algebraic independence of
*analytic germs*, but only for signed (`+-1`) carriers, whose finite coefficient range the
tail-rigidity theorem used; and `HelsonPhaseTailIndependence` proved tail independence for an
arbitrary nowhere-vanishing phase, but stayed inside the arithmetic-function fraction field.  Every
step of the transfer uses only *boundedness* of the coefficients, so the signed chain applies
verbatim to a unimodular phase once the tail input is taken from the phase theorem.  The only new
lemma needed was reindexing a coefficient family along an equivalence
(`tailCoefficientIndependent_comp_equiv`), because the phase tail theorem is indexed by a singleton
source type.

### Scope, stated exactly

This is Pong's conclusion **for the prime carrier** `sum_p chi(p) p^{-s}` of the phase — one source
per valuation layer — not yet for the full multiplicative `Z_chi = sum_n chi(n) n^{-s}`.  The
passage to `Z_chi` is a definite next step and the corpus already has its shape: with

```text
log Z_chi(s) = sum_{r >= 0} (1/(r+1)) sum_p chi(p)^{r+1} p^{-(r+1)s} ,
```

the layers are exactly the prime-power sigma tower for which
`algebraicIndependent_primePowerSigmaTower_over_finitePrimeCoefficientField` and
`primePowerCoefficientShiftedJets_algebraicIndependent_phase` are already proved, with the phase at
layer `r` being `chi^{r+1}` — which is nowhere vanishing whenever `chi` is.  What that step needs is
the analytic assembly of the tower into `Z_chi` itself, and the trade between the jets of `Z` and
the jets of `Z'/Z` (the layer sum), which shifts the derivative order by one per shift.

## Lean progress — Pong's conclusion for `Z_chi` ITSELF, from the prime values alone

`HTGeometry/PrimeValueJacobianCriterion.lean` and `HTGeometry/HelsonZetaJetIndependence.lean`
(wired, axiom-clean).

```
PrimeValueIndependent g          no nontrivial constant combination vanishes at every prime
primeValueIndependent_of_tailIndependent
algebraicIndependent_of_primeValueIndependent
      ** a finite family of arithmetic functions whose PRIME VALUES are linearly independent is
         algebraically independent over C — with no restriction on the support **

arithmeticShiftedRotatedJet f a k          the coefficient stream of (d/ds)^k Z(s+a)
algebraicIndependent_arithmeticShiftedRotatedJets
      nowhere-vanishing prime coefficients + distinct shift real parts
        ==> the whole shifted derivative rectangle is algebraically independent
algebraicIndependent_helsonZetaShiftedJets
      ** the same for a unimodular completely multiplicative coefficient stream **
```

### Why this is the step the card needed

The corpus's independence criteria were all support-restricted: the Jacobian bridge
(`algebraicIndependent_of_evaluation_packet`) needs *prime-supported* functions, because only then
is `∂_q b = b(q) • 1` a scalar, and the prime-power packet machinery needs each function to live on
one exponent layer.  `Z_chi = sum_n chi(n) n^{-s}` is supported on **all** integers, so neither
applies, and that gap is why the card recorded Pong's conclusion as an outstanding input even though
its hypothesis was already discharged.

The gap closes by dropping the scalar requirement and paying one induction.  For *every* arithmetic
function, `(∂_q b)(1) = b(q)`.  Applying the chain rule to a minimal-degree relation `P(g) = 0`
gives `sum_j (∂_j P)(g) . ∂_q g_j = 0`, and evaluating that identity at `n` in the Dirichlet
convolution kills every divisor pair except `(n, 1)`, by strong induction on `n` — because a proper
divisor is strictly smaller.  What survives is `sum_j (∂_j P)(g)(n) . g_j(q) = 0` for every prime
`q`, so linear independence of the prime values forces `(∂_j P)(g)(n) = 0` for every `n`, i.e. every
partial derivative of `P` annihilates the family.  Minimality of the degree is contradicted.

The criterion is strictly more general than the two it replaces and is stated for any finite family;
the Helson application only has to check that the prime coefficients of a unimodular phase are
nonzero, and that the shift–jet palette has full tail rank — which is
`phasePrimeShiftedRotatedJet_tailIndependent` from the previous section.

### What is still open in Pong's input

The statement above is over `C`.  The card's `L_chi` is generated over `E_fin`, so the remaining
step is the same independence over the finite-prime coefficient field — the corpus has that upgrade
for prime columns (`algebraicIndependent_fractionPrimeColumns_over_finitePrimeCoefficientField`)
and the argument should transfer, since a coefficient in `E_fin` involves only finitely many primes
and the criterion may use any cofinite set of primes `q`.

## Lean progress — PONG'S INPUT IS CLOSED: conclusion over `E_fin(s)`, in analytic form

`HTGeometry/PrimeValueJacobianCoefficientField.lean` and the new section of
`HTGeometry/HelsonZetaJetIndependence.lean` (wired, axiom-clean).

```
eq_zero_of_sum_mul_primeDeriv_eq_zero
      the criterion's induction, with a FINITE set of primes excluded
algebraicIndependent_over_primeCommonKernelField_compl
      independence over the common kernel field of all primes outside a finite set
algebraicIndependent_over_finitePrimeCoefficientField_of_tailIndependent
      ** tail-independent prime values  ==>  algebraically independent over E_fin **

algebraicIndependent_helsonZetaShiftedJets_over_finitePrimeCoefficientField
algebraicIndependent_helsonZetaShiftedJets_over_finitePrimeRationalCoefficientField
      ** the shifted derivative rectangle of Z_chi is independent over E_fin and over E_fin(s) **
boundedFiniteAbscissa / boundedShiftedRotatedJet / boundedShiftedRotatedJet_coe
algebraicIndependent_helsonZetaShiftedUpperEndGerms
      ** and as a family of actual analytic upper-end germs **
```

### Why the upgrade works

The prime-value criterion uses the prime derivations at *every* prime, and a coefficient in
`E_fin` is not killed by all of them.  But a polynomial relation over `E_fin` exposes only finitely
many prime directions (`polynomialPrimeActivity_finite`), so every derivation outside that finite
set annihilates all its coefficients — and the criterion's induction only ever needs the relation at
primes outside a finite set, because tail independence tolerates exactly that.  Concretely: lift the
relation to the common kernel field of the primes outside the activity, clear denominators once with
a single non-zero-divisor, run the divisor-pair induction in the ring, and conclude that every
partial derivative annihilates the family.

### What this closes on the card

The `2 -> 3` gate names three classical inputs.  **Pong's is now formal in both halves**: the
hypothesis (`primeSupport_not_finitelyGenerated`, earlier) and the conclusion — for the actual
`Z_chi` coefficient stream, over the card's own `E_fin(s)`, and realized as analytic germs.  Nothing
about Pong's theorem remains as an assumption in this tree.

Remaining on the card: **Andersson's** arbitrary-divisor continuation theorem, and
**Saksman--Webb's** almost-sure meromorphic abscissa (equivalently, by the zero-one law already
proved here, that the noncontinuable phases have positive measure).  Both are analytic existence
statements about the continuation of `Z_chi` past `Re s = 1`, and neither is reachable from the
algebraic and descriptive-set-theoretic layers now in place.

## THE ROUTE THAT CLOSES `Haar(M) = 0` WITHOUT BOHR'S THEOREM

The Bohr programme recorded above (`sigma_u <= sigma_b`) is still open at its Tauberian step, and the
previous section correctly flagged that a.s. divergence alone does not give non-continuability.
There is a different route, and it is *shorter*, *unconditional*, and does not need Bohr's theorem,
the Riesz-mean Tauberian step, Itô--Nisio, or the natural-boundary theorem.  It is recorded here in
full because it is the plan the remaining sessions execute.

### The mechanism

Write the Euler logarithm as its prime layer plus its prime-power tail:

```text
log Z_chi(s)  =  G_chi(s) + H_chi(s) ,
G_chi(s) = sum_p chi(p) p^{-s} ,
H_chi(s) = sum_p sum_{k >= 2} chi(p)^k / (k p^{ks}) .
```

`H` converges **absolutely** on `Re s > 1/2` for every phase, and its second moment is bounded there
by a constant (`E|H(sigma)|^2 <= sum_{p,k>=2} p^{-2k sigma} <= 2`), uniformly as `sigma` decreases to
`1/2`.  `G` is a random Dirichlet series with genuinely **independent** coefficients, whose second
moment `A(sigma) = sum_p p^{-2 sigma}` diverges as `sigma -> 1/2+`.

If `chi` is continuable, `Z_chi = exp(G + H)` on `Re s > 1/2` (identity theorem, both sides
meromorphic there and equal on `Re s > 1`), so `Z_chi` has no zero or pole in the open half plane
and

```text
log |Z_chi(sigma)|  =  Re G_chi(sigma) + Re H_chi(sigma) ,     sigma in (1/2, 1) .
```

Meromorphy of `Z_chi` at the boundary point `1/2` gives an integer `m` (the local order) and
constants `delta, B` with

```text
| Re G_chi(sigma) + Re H_chi(sigma) - m log(sigma - 1/2) |  <=  B      on (1/2, 1/2+delta).   (*)
```

`(*)` is invariant under modifying finitely many prime phases (a finite Euler correction is
holomorphic and nonvanishing at `1/2`, since its zeros and poles sit on `Re s = 0`), so for each `m`
the event `(*)` is a **tail event**; by the zero--one law exactly one `m0` has probability one.

**`m0 = 0` by the cube-root identity.**  For a primitive cube root `w`,

```text
(G+H)_chi + (G+H)_{w chi} + (G+H)_{w^2 chi}
   =  sum_p sum_{k >= 2, 3 | k} 3 chi(p)^k/(k p^{ks})
   =  sum_p -Log(1 - chi(p)^3 p^{-3s}) ,
```

because `1 + w^k + w^{2k}` is `3` when `3 | k` and `0` otherwise — in particular the `k = 1` layer
cancels **identically**.  The right side converges absolutely on `Re(3s) > 1`, i.e. on
`Re s > 1/3`, so it is bounded near `sigma = 1/2`.  Adding three copies of `(*)` therefore forces
`3 m0 log(sigma - 1/2)` to be bounded, i.e. `m0 = 0`.  (The rotation `chi -> w chi` is a translation
of the compact phase group, so it preserves the measure and the a.s. value of `m`.)

**The contradiction.**  With `m0 = 0`, `(*)` says `|Re G(sigma) + Re H(sigma)| <= B` on a set of
measure `> 1 - 1/128`.  But the prime series is a Steinhaus sum with independent coefficients, so

```text
E[(Re G(sigma))^2] = A(sigma)/2 ,        E[(Re G(sigma))^4] <= E|G|^4 <= 2 A(sigma)^2 ,
```

and Paley--Zygmund (already formal) gives `P( (Re G)^2 > A/4 ) >= 1/32`, while Chebyshev on the
uniformly bounded `H` gives `P(|Re H| > lambda) <= 2/lambda^2`.  Choosing `lambda` and then
`sigma` with `A(sigma) > 4(B+lambda)^2` makes the three events meet, contradicting `|Re G + Re H|
<= B`.  Hence `Haar(M) != 1`, and by the zero--one law `Haar(M) = 0`.

Nothing in this chain is a classical input: it uses Kolmogorov's maximal inequality, Paley--Zygmund,
the prime fourth moment, the divergence of `sum 1/p`, the identity theorem, and the cube-root
factorisation.

## Lean progress — Kolmogorov's maximal inequality and the convergence criterion

Searched first (`research "Kolmogorov maximal inequality almost sure convergence independent random
series partial sums"`): the corpus owns the zero--one law for a coordinatewise series and the
divergence half, but no maximal inequality and no a.s. convergence.  Both are new.

`HTGeometry/KolmogorovMaximalInequality.lean` (wired, axiom-clean):

```text
blockExtend a s y                     rebuild a product point from its restriction to a finite set
indepFun_of_blockDependence           two functions reading disjoint finite coordinate blocks are
                                          independent under any product probability measure
firstPassage g lam n                  the first index at which the partial sums reach lam
integral_crossTerm_eq_zero            the Abel cross term of the first-passage decomposition dies
kolmogorov_maximal_inequality
    lam^2 . P( max_{n <= N} ||S n|| >= lam )  <=  E ||S N||^2
```

`HTGeometry/IndependentCoordSeriesConvergence.lean` (wired, axiom-clean):

```text
integral_coordTerm_mul_conj           distinct centred coordinate terms are uncorrelated
integral_normSq_coordPartialSum       E||S N||^2 = sum_{n<N} E||g n||^2
shiftTerms g M                        the series with its first M terms deleted
measure_tail_oscillation_le           P( the tail past M ever moves by lam ) <= lam^{-2} . tail
measure_coordSeriesConverges_eq_one
    **centred + bounded + mean-square summable  ==>  the series converges ALMOST EVERYWHERE**
```

The `blockExtend` device is what makes the independence input painless: "`U` reads only the block
`s`" is the equation `U (blockExtend a s (s.restrict x)) = U x`, and `IndepFun.comp` then transports
mathlib's coordinate independence through it.  No filtration, no conditional expectation, no
stopping time appears anywhere.

## Lean progress — Abel summation is uniform, so the sum is holomorphic

`RHTower/DirichletUniformAbel.lean` (wired, axiom-clean).  The corpus had the *pointwise* Abel
theorem only; the analytic use needs the uniform form, because a locally uniform limit of
holomorphic functions is holomorphic while a pointwise limit need not be.

```text
norm_dirichletPartialSum_sub_le
    || sum_{M <= n < N} a_n (n+1)^{-s} ||  <=  2C (1 + ||s||/Re s) (M+1)^{-Re s}
dirichletSum a                        the sum, as a function
tendsto_dirichletSum
norm_dirichletSum_sub_partialSum_le   the same estimate after a shift to the point of convergence
tendstoLocallyUniformlyOn_dirichletPartialSum
differentiableOn_dirichletSum
    **convergence at s0  ==>  the sum is holomorphic on Re s > Re s0**
```

Uniform convergence on a *whole* closed half plane is false in this generality — the factor `||s||`
is unbounded — which is exactly why `sigma_u` is a strictly finer invariant than `sigma_c`, and why
the bounded-part version is the right statement.

## Lean progress — the prime series is almost surely holomorphic past the half line

`RHTower/SteinhausPrimeHolomorphic.lean` (wired, axiom-clean).

```text
primeTermBound, norm_primeTerm_eq, integral_primeTerm
summable_integral_normSq_primeTerm       sum_p p^{-2 sigma} < infinity for sigma > 1/2
measure_coordSeriesConverges_primeTerm_eq_one
    **sigma > 1/2  ==>  Haar { omega : sum_p p^{-sigma} X_p converges } = 1**
primePhaseCoeff omega                    the same series in the dirichletPartialSum indexing
dirichletPartialSum_primePhaseCoeff, convergesAt_primePhaseCoeff
primeHolomorphicEvent                    convergence at every cut 1/2 + 1/(j+1)
measure_primeHolomorphicEvent            it has full measure
differentiableOn_dirichletSum_primePhaseCoeff
    **almost surely G_chi is holomorphic on the whole half plane Re s > 1/2**
primeShift, primeShift_injective, notMem_range_primeShift
hasSum_primePhase_dirichletSum
    **and on Re s > 1 it is the prime Euler sum  sum_p chi(p) p^{-s}**
```

With `SteinhausPrimeDivergence` this pins the almost-sure abscissa of convergence of the prime
series at exactly `1/2`: divergence at every `sigma <= 1/2`, convergence at every `sigma > 1/2`.

Remaining bricks on this route: the prime-power tail `H` with its uniform second-moment bound, the
Euler logarithm identity `Z_chi = exp(G+H)` on `Re s > 1`, its extension to `Re s > 1/2` by the
identity theorem, the singularity statement `(*)`, the cube-root cancellation, the rotation
invariance of the phase measure, the limit moments of `G`, and the final Paley--Zygmund assembly.

## Lean progress — the Euler logarithm splits, and the tail layer is bounded in probability

`HTGeometry/EulerLogTail.lean` (wired, axiom-clean).

```text
logTail z = -log(1-z) - z          the quadratic tail of the Euler logarithm
hasSum_logTail                     logTail z = sum_{k >= 2} z^k / k
norm_logTail_le                    ||logTail z|| <= ||z||^2 / (2(1-||z||))
cubeRootUnit_sq, cubeRootUnit_pow_three, one_add_cubeRootUnit_add_sq
cubeRootUnit_pow_sum               1 + w^n + (w^2)^n  =  3 if 3 | n, else 0
neg_log_cube_sum                   the three rotated logarithms reassemble log(1 - z^3)
logTail_cube_sum                   **logTail z + logTail(wz) + logTail(w^2 z) = -log(1 - z^3)**
```

`HTGeometry/HelsonLogTailSum.lean` (wired, axiom-clean).

```text
rpow_two_neg_half_le               2^{-1/2} <= 3/4
norm_prime_cpow_le_three_quarters  so ||p^{-s}|| <= 3/4 on Re s >= 1/2
norm_logTail_prime_le              ||logTail(chi_p p^{-s})|| <= 2 p^{-2 Re s}
helsonLogTail chi s                the absolutely convergent layer sum_p logTail(chi_p p^{-s})
summable_helsonLogTail, differentiableOn_logTail_prime
differentiableOn_helsonLogTail     **holomorphic on Re s > 1/2, for EVERY phase**
norm_neg_log_le, helsonCubeLog, norm_cube_prime_le, summable_helsonCubeLog
norm_helsonCubeLog_le              the cube remainder is bounded on Re s >= 1/2
helsonLogTail_cube                 **the three rotated tail layers sum to the cube remainder**
summable_prime_layer
hasProd_helsonEuler_exp            **the Euler product is exp(prime layer + tail layer)**
```

`RHTower/SteinhausLogTailMoment.lean` (wired, axiom-clean).

```text
X_pow_eq, integral_X_eq_zero       a nontrivial Steinhaus character averages to zero
tailTerm a t                       the tail contribution of one prime, as a coordinate function
integral_tailTerm                  **each tail term is CENTRED** — every layer of logTail carries
                                       a nontrivial character p^k with k >= 2
helsonPhaseOf, logTailCoordTerm, logTailBound, tailMomentBound
integral_normSq_logTailPartial     E ||tail partial sum||^2 <= 4 sum_n n^{-2}, uniformly in sigma
hasSum_logTailCoordTerm, tendsto_logTailPartial, measurable_logTailSum
measure_re_logTail_gt              **P( |Re H(sigma)| > lambda ) <= 4 C / lambda^2, uniformly**
```

The point of the last line is exactly the separation the whole argument rests on: the tail layer is
*pointwise* of size `sum_p p^{-2 sigma}`, which diverges at the half line, but its *second moment*
is bounded there, because its terms sit on distinct coordinates and are centred.  All the divergence
lives in the linear prime layer.

## Lean progress — the boundary logarithmic envelope, and the rotation

`HTGeometry/MeromorphicBoundaryLog.lean` (wired, axiom-clean).

```text
convex_halfPlane_re_gt, isOpen_halfPlane_re_gt, isConnected_halfPlane_re_gt
eventuallyEq_of_eq_on_abscissa
    the identity theorem: a function meromorphic on the plane which equals a nonvanishing
    holomorphic function on Re s > 1 equals it on a punctured neighbourhood of every point of
    Re s > 1/2
exists_boundary_log_bound
    **F meromorphic on C, E holomorphic on Re s > 1/2, F = exp E on Re s > 1
      ==>  there are m in Z and delta, B > 0 with
           | Re E(sigma) - m log(sigma - 1/2) | <= B     on (1/2, 1/2 + delta)**
```

The proof compares two local models of `F` — the exponential model, valid on a punctured
neighbourhood of every interior point, and the meromorphic normal form `(s-1/2)^m g(s)` at the
boundary point — and observes that both are continuous on the open half disc, so they agree there,
not merely off a discrete set.

`RHTower/SteinhausPhaseRotation.lean` (wired, axiom-clean).

```text
rot3, map_rot3                     t |-> t + 1/3 (mod 1) preserves Lebesgue measure on [0,1]
cexp_two_pi_I_div_three            e^{2 pi i/3} = cubeRootUnit
rotOmega, map_rotOmega             **the coordinatewise rotation preserves the Steinhaus measure**
measure_preimage_rotOmega
X_rotOmega                         **and multiplies every prime character by the cube root**
```

## Lean progress — anti-concentration of the real part

`RHTower/SteinhausPrimeRealMoment.lean` (wired, axiom-clean).

```text
integral_dpoly_sq                  **isotropy: E[S^2] = 0 for indices above one**
integral_re_sq_steinhausPrimePoly  hence E[(Re S_N)^2] = (1/2) sum_{p<N} p^{-2 sigma}
integral_re_pow_four_le            E[(Re S_N)^4] <= 2 (sum_{p<N} p^{-2 sigma})^2
measure_re_steinhausPrimePoly_gt
    **P( (Re S_N)^2 > A_N / 4 ) >= 1/32**            (Paley--Zygmund with C = 8)
exists_sigma_primeSum_gt, exists_primeSum_gt_nhds
    A_N(sigma) exceeds any level for a suitable cut, uniformly on a right neighbourhood of 1/2
```

Isotropy is the new ingredient: `E[X_n X_m] = E[X_{nm}] = 0` whenever `n, m >= 2`, so the
*unconjugated* second moment vanishes and the real part carries exactly half the energy.  Without it
the Paley--Zygmund bound would control `|S_N|`, which the boundary estimate does not see — the
boundary estimate constrains only `Re(G + H)`.

## Lean progress — `Haar(M) = 0` IS PROVED, UNCONDITIONALLY

`RHTower/HelsonEulerExponent.lean` and `RHTower/HelsonStratumNull.lean` (wired, axiom-clean:
`[propext, Classical.choice, Quot.sound]`).

```text
phaseTorusOf omega                  the random phase as a point of the phase torus
helsonExponent omega s              E_omega(s) = prime layer + tail layer
differentiableOn_helsonExponent     holomorphic on Re s > 1/2, almost surely
hasProd_helsonExponent              the Euler product is exp(E_omega) on Re s > 1
contEvent                           the event that the phase is continuable
exists_boundary_bound
    ** continuable  ==>  | Re E_omega(sigma) - m log(sigma - 1/2) | <= B  near the half line **
eulerExponentRe                     a measurable version of Re E_omega, via limsup
exists_bound_eulerExponentRe_sub    finite modification changes it by a bounded amount
measurableSet_contEvent, contEvent_invariant

cutSeq k = 1/2 + 1/(k+1)
negEvent, posEvent                  bounded above / below along the cut sequence
measure_negEvent_eq_zero_or_one     both are TAIL EVENTS
measure_posEvent_eq_zero_or_one
contEvent_inter_subset              ** the envelope covers the continuation stratum:
                                         m >= 0 gives the upper half, m <= 0 the lower **
primeRe, tendsto_steinhausPrimePoly, eulerExponentRe_split
contradiction_of_envelope           ** no fixed one-sided envelope holds with probability
                                         above 1 - 1/256 **
measure_contEvent_eq_zero           ** Haar { omega : Z_chi continues } = 0 **
circlePhase, circleUniform, primeRestrict, map_phaseTorusOf
measure_continuableStratum_eq_zero
    ** the same statement on the phase torus itself:
         (prod_p uniform)(continuableStratum) = 0 **
```

### The mechanism, exactly

Continuation is only visible at the boundary through a *logarithmic envelope*: if `Z_chi` continues
meromorphically past `Re s = 1/2` then, `Z_chi = exp(E_chi)` there by the identity theorem, so
`Z_chi` has no zero or pole in the open half plane, and its meromorphic normal form at the boundary
point gives an integer `m` with

```text
Re E_chi(sigma) = m log(sigma - 1/2) + O(1) .
```

The integer `m` is unknown and cannot be eliminated by any linear combination of nearby values —
the second difference in `log(sigma - 1/2)` kills the `m` term but also kills the divergence of the
variance, because the increment of the prime series over a bounded logarithmic scale has bounded
second moment.  The resolution is to *split the envelope by sign*: `m >= 0` makes `Re E` bounded
**above** along the cut sequence, `m <= 0` bounded **below**, and each of those two conditions is a
tail event — finite modification changes `Re E` by a bounded amount, uniformly on `Re s >= 1/2`.  So
one of the two has probability one, and the corresponding **one-sided** anti-concentration bound for
the prime layer contradicts it.  The one-sided bound is the half-turn phase symmetry
`X_p -> -X_p`, which is measure preserving and exchanges the two sides of the escape event.

### What this closes

| statement | status |
|---|---|
| labelled differential-field universality | formal |
| Pong's conclusion for `Z_chi`, `Phi_(chi,psi)` | formal, unconditional |
| density, codensity, `boundary(M) = Omega`, no continuous factorization | formal, unconditional |
| `Haar(M) in {0,1}` | formal, unconditional |
| a.s. divergence of the prime series left of the half line | formal, unconditional |
| **`Haar(M) = 0`  (Saksman--Webb/Seip input)** | **formal, unconditional** |
| divisor surjectivity (Andersson Thm 5) | open |

Two of the card's three named classical inputs are therefore no longer inputs: Pong's theorem and
Saksman--Webb's almost-sure meromorphic abscissa are both Lean theorems in this tree, proved from
scratch.  Only Andersson's arbitrary-divisor construction remains.

The route used none of the machinery the earlier plan expected: no Bohr theorem, no Riesz-mean
Tauberian step, no Perron contour, no three-series theorem, no Itô--Nisio, no natural-boundary
theorem, no Mertens-type upper bound on `sum_p p^{-2 sigma}`.  What it used instead: Kolmogorov's
maximal inequality (built here), Kolmogorov's convergence criterion (built here), uniform Abel
summation (built here), the identity theorem for meromorphic functions, Paley--Zygmund, the prime
fourth moment, and two measure-preserving phase rotations.

## THE ANDERSSON INPUT — exact statement, exact proof chain, exact corpus audit

Read from the source (arXiv:2408.15713v1, 12 pages).  Recording it in full because it is the only
input left on this card and it is a multi-session build.

### What is actually needed

The card consumes Theorem 5 with `U = C`:

> **Theorem 5 (Andersson).**  Let `U ⊆ C` be open connected containing `Re s > 1`, and let
> `Z ⊂ U ∩ {Re s < 1}` be any signed multiset without limit points on `U ∪ (1+iR)`.  Then there is a
> completely multiplicative unimodular `chi` such that `zeta_chi` continues meromorphically from
> `Re s > 1` to `U` with prescribed poles and zeros with the given multiplicities from `Z`.

"Admissible" therefore means exactly: **no limit points in `U ∪ (1+iR)`** — for `U = C` this is
"locally finite in the plane", which is what the card says.  There is no density or Blaschke
condition.

For the card only the `U = C` case is needed, and only through the following weaker route, which
avoids Andersson's Theorem 3 (maximal domains, Mittag-Leffler with essential singularities) entirely:

```text
Theorem 1  ==>  Theorem 2  ==>  divisor surjectivity.
```

`Theorem 2`: if `f` is analytic and zero-free on `Re s > 1` and `f'/f` extends continuously to
`Re s >= 1`, then `f = zeta_chi . g` for some Helson `chi` and some entire zero-free `g`.  Given the
target divisor `D`, realize it by a meromorphic `F` on the plane (the corpus already owns this, see
below); `F` is analytic and zero-free on a neighbourhood of `Re s >= 1` because `D` has no limit
point on `1+iR`; Theorem 2 gives `F = zeta_chi . g`, so `zeta_chi = F/g` is meromorphic on the plane
with divisor exactly `D`, because `g` is entire and zero-free.  That is the surjectivity statement.

### The proof chain of Theorem 1

```text
f(s) = zeta'_chi(s)/zeta_chi(s) + g(s)   on Re s > 1,   g entire,
   for every f continuous on Re s >= 1 and analytic on Re s > 1.
```

with `r_1(x) = int_1^x q + sum_{n<=x} chi(n) Lambda(n)` and `r_{j+1}(x) = int_1^x r_j`:

| step | content | status |
|---|---|---|
| Lemma 1 | `f = int_1^inf q(x) x^{-s} dx + g`, `q = o(1)`, `g` entire | **Arakelyan + Paley--Wiener** |
| Lemma 2 | `pi(x+bx^th) - pi(x+ax^th) >= c(b-a-delta(x)) x^th / log x` | Hoheisel, counting form |
| Lemma 3 | rounding: `\|\|sum b_j x_j - sum a_j x_j\|\| <= d max\|\|x_j\|\|` with `\|b_j\|=1` | Bagchi Lemma 4.1 |
| Lemma 4 | Vandermonde/Cramer solution of a `J x J` system over primes in `[x, x+x^th)` | uses Lemma 2 |
| Lemma 5 | Lemma 3 + Lemma 4: unimodular phases realizing prescribed moments | |
| Lemma 6 | one recursion step keeping `\|r_j(x_k)\| <= ((J+1)/(j-1)!) x_k^{(j-1)th} log x_k` | |
| Lemma 7 | the full recursion: `\|r_j(x)\| <<_j x^{j th}` for every `j` | |
| Theorem 1 | integrate `f_0 - zeta'/zeta = s int_1^inf r_1 x^{-s-1}` by parts `j` times | |

The one genuinely external analytic input is **Arakelyan's uniform approximation theorem** on the
closed half plane `Re s >= 1` (Lemma 1), used to subtract an entire function so that the remainder
is `O(\|s\|^{-2})` there; after that the Mellin representation is a Hardy-class/Paley--Wiener step
(Bochkov--Romanov, Lemma 2 of J. Funct. Anal. 282 (2022) 109398).

### Corpus audit for this chain

Already owned, verified by `formal_tools.py research`:

```text
HTGeometry/WeierstrassFactorizationTheorem.lean
    weierstrassGenusProduct, differentiable_weierstrassGenusProduct,
    weierstrassGenusProduct_eq_zero_iff       -- Weierstrass with INCREASING genus, arbitrary zeros
HTGeometry/PrescribedDivisorRealization.lean
    divisorFunction a b, meromorphicOn_divisorFunction,
    meromorphicOrderAt_divisorFunction        -- a meromorphic function with a prescribed divisor
RHTower/Sieve/PrimeWindowBrunTitchmarsh.lean  -- the upper bound needed for prime-power sparsity
RHTower/Sieve/RouteTFixedShortIntervalPrimeSupply.lean
    exists_threshold_routeT_prime_in_fixed_window
        -- unconditional: a prime in EVERY (x, x + x^{71/100}]
RHTower/Sieve/InghamUniformDetectorMellinQuantitativeThetaMass.lean
    eventually_inghamRouteTBuffered_theta_window_gt_quarter_width
        -- theta(x+2H) - theta(x) > H/4, but only along the detector centres
```

So the Weierstrass/divisor end of the argument is **already formal**, and the short-interval
prime supply exists unconditionally in the *existence* form.  What Lemma 2 needs is the *counting*
form `pi(x+h) - pi(x) >> h/log x` for `h = x^theta`, uniformly in the base point.  The corpus's
quantitative theta-mass bound is of exactly the right shape but is stated along a sequence of
detector centres; extending it to every base point is the first concrete gap.

Missing entirely from mathlib and from the corpus:

```text
Arakelyan's approximation theorem on a closed half plane          -- the hard core
the Paley--Wiener/Hardy representation f = int_1^inf q x^{-s} dx  -- moderate
Bagchi's rounding lemma (Lemma 3)                                 -- self-contained, tractable
the recursion of Lemmas 4-7                                       -- long but elementary
```

### Order of attack

1. Lemma 3 (rounding) — self-contained finite-dimensional convexity, no analytic input.
2. The divisor-surjectivity consumer, from a *hypothesis* shaped exactly like Theorem 2, so that the
   two ends of the argument are formal and only the middle remains.
3. Lemma 2 in the counting form, from the corpus's Ingham/Mellin detector chain.
4. Lemmas 4-7, the recursion.
5. Lemma 1: the Paley--Wiener step, then Arakelyan.

Nothing here is conditional on an unproved conjecture; the whole chain is classical mathematics with
a long formalization cost, and the working mode is to build it.

## Lean progress — the consumer end of the Andersson chain

`HTGeometry/HelsonPrescribedDivisor.lean` (wired, axiom-clean).

```text
HelsonFactorizationProperty
    Andersson's Theorem 2, recorded as a named property:
      F analytic and zero free on a neighbourhood of Re s >= 1
        ==>  F = zeta_chi . g  on Re s > 1, with g entire and zero free
divisorFunction_analyticAt_of_re_le      the realized divisor function is analytic on Re s >= 1
divisorFunction_ne_zero_of_re_le         and nonvanishing there, because the divisor is to the left
exists_continuable_phase_with_prescribed_divisor
    ** given Andersson's factorization, EVERY prescribed divisor is realized:
       there is a phase chi in continuableStratum whose continuation has exactly that divisor **
```

So the divisor half of the card is now a single named classical property away from being formal.
Both ends are unconditional: the Weierstrass realization of an arbitrary divisor
(`PrescribedDivisorRealization`, already in the corpus) and the passage from the factorization to
membership in `continuableStratum` with the right order at every point.  What remains is Andersson's
Theorem 2 itself, i.e. Theorem 1, i.e. Lemmas 1-7 of the plan above.

## Lean progress — two Andersson bricks: the rounding lemma and half-plane pole approximation

`HTGeometry/UnimodularRounding.lean` (wired, axiom-clean).

```text
exists_first_hit_one       moving from inside the disc along a nonzero direction, there is a FIRST
                               time at which the unit circle is reached
exists_reduce_free         with more free coefficients than the dimension, the coefficient vector
                               moves along the kernel until one more coefficient reaches the circle
exists_rounding_of_card_le radial rounding of at most `d` interior coefficients
exists_unimodular_rounding **Bagchi's Lemma 4.1 / Andersson's Lemma 3:**
                               ||sum b_j x_j - sum a_j x_j|| <= (dim) . max ||x_j||,  |b_j| = 1
```

`HTGeometry/HalfPlanePoleApproximation.lean` (wired, axiom-clean).

```text
truncPole a T              the truncated Laplace transform (1 - e^{-T(s-a)})/(s-a)
differentiable_truncPole   it is ENTIRE — the apparent singularity at `a` is removable
norm_pole_sub_truncPole_le ||1/(s-a) - truncPole a T s|| <= e^{-T(1 - Re a)}/(1 - Re a)
                               uniformly on the CLOSED half plane Re s >= 1
exists_truncPole_approx
exists_entire_approx_finite_poles
    ** a finite sum of simple poles lying strictly left of Re s = 1 is uniformly approximable, on
       the whole closed half plane, by an entire function **
```

This last statement is Arakelyan's theorem in the case the corpus can reach elementarily, and it
identifies the mechanism: a simple pole to the left of the line is the Laplace transform
`int_0^inf e^{-t(s-a)} dt` there, and truncating the integral leaves an entire function with an
exponentially small error on the half plane.  Uniform approximation on the *closed unbounded* half
plane is what separates this from the corpus's compact-open Runge results
(`HalfPlaneRungeClosure`), and it is exactly the shape Andersson's Lemma 1 consumes.

### Why the elementary route does not yet reach the full Lemma 1 — recorded so it is not retried

Three shortcuts were checked and each fails for a precise reason:

1. **Termwise Mellin.**  `1/(s-a) = int_1^inf x^{a-1} x^{-s} dx` with `Re a < 1`, so each polar term
   *is* a Mellin transform of an `o(1)` function.  But the Mittag-Leffler corrections needed to make
   `sum_a m_a/(s-a)` converge are polynomials in `s`, and a polynomial is not the Mellin transform of
   an `o(1)` function (it does not vanish as `Re s -> +inf`).  Grouping the corrections into the
   entire remainder does not help: their sum diverges.
2. **Corrections by other poles.**  Replacing the polynomial corrections by combinations of poles at
   auxiliary points `a + i h` (which *are* Mellin transforms) works analytically — the `k`-th
   difference gives `u_a(x) = x^{a-1}(1-x^h)^k` with `sup_x |u_a| <= 2^{-k}` for `|h| <= e delta/(2k)`
   — but it pollutes the divisor with the auxiliary poles, and the residues there do not cancel.
3. **A cut-off kernel.**  `u_a(x) = x^{a-1} 1_{x >= X_a}` has Mellin transform `X_a^{a-s}/(s-a)`,
   with **no** auxiliary poles and `sup |u_a| = X_a^{-(1 - Re a)}` arbitrarily small.  The resulting
   `q` is `o(1)` and the series converges on `Re s > 1`; but its continuation to the left diverges
   term by term, so it does not exhibit the required entire remainder.

So the polynomial corrections are unavoidable and the entire function that removes them is exactly
what Arakelyan's theorem supplies.  The finite-pole case above shows the mechanism; the remaining
content is the passage to infinitely many poles, uniformly on the closed half plane.

### Sharpened statement of the irreducible core

Two further routes were worked out in detail and both terminate at the same theorem.

**Smooth-cutoff Laplace approximants.**  Replacing the hard truncation by a smooth cutoff `w`
supported in `[0, 2T]` and equal to `1` on `[0,T]`, the approximant
`g_a(s) = int_0^{2T} w(t) e^{-t(s-a)} dt` is entire and, after `k` integrations by parts, the error
obeys `|1/(s-a) - g_a(s)| <= C_k e^{-T(1-Re a)} / |s-a|^k` on `Re s >= 1`.  With `k = 2` the error
family is not merely small but **`L^1` on the line `Re s = 1`**, since
`int_R dt/|1+it-a|^2 = pi/(1-Re a)`.  That is exactly the hypothesis under which the Mellin
representation of Lemma 1 is elementary — Riemann--Lebesgue plus the half-plane Cauchy formula, no
Arakelyan.

**Why that still does not close it.**  Writing `A_a` for the primitive of the error vanishing at
`+infinity`, the product `prod_a exp(m_a A_a)` has divisor `D` and converges on `Re s >= 1`, and its
logarithmic derivative is the small `L^1` remainder.  But each factor is
`(s-a)^{m_a} exp(-m_a G_a(s))` with `G_a` an entire primitive of `g_a`, and `G_a` grows like
`e^{2T|s|}` to the left, so the product does not converge off the half plane and the realized
function does not continue.  Making the product converge globally forces `G_a` to be close to the
Taylor polynomial of `log(s-a)` on compacts, while making the error `L^1` forces `G_a` to be close
to the truncated-Laplace primitive on the half plane.  **One entire `G_a` doing both is precisely
uniform approximation on a set of the form `K union {Re s >= 1}`** — Arakelyan's theorem.

So the irreducible core of this card is:

> **Arakelyan's approximation theorem** for closed sets `E ⊆ C` whose complement in the sphere is
> connected and locally connected — at minimum for `E = {Re s >= 1}` and for
> `E = K ∪ {Re s >= 1}` with `K` compact: every function continuous on `E` and analytic on its
> interior is a uniform limit on `E` of entire functions.

Neither mathlib nor this corpus has Arakelyan, Mergelyan, or a general Runge theorem for unbounded
closed sets; the corpus's `HalfPlaneRungeClosure` is compact-open only.  Formalizing Arakelyan is
therefore the single remaining task on this card, and it is a first-of-its-kind formalization in its
own right.  The pieces already built here — the entire truncated-Laplace approximant with its
exponential half-plane error, and the finite-pole case — are its elementary core.

## An elementary proof architecture for Arakelyan on the closed half plane

The source was re-read to fix the exact shape of the missing input.

> **Andersson, Theorem 1.**  Let `f` be continuous on `Re s >= 1` and analytic for `Re s > 1`.
> Then there are an entire `g` and a Helson zeta function with `f = zeta_chi'/zeta_chi + g` on
> `Re s > 1`.
>
> **Andersson, Theorem 2.**  Let `f` be analytic and zero free on `Re s > 1` with `f'/f` extending
> continuously to `Re s >= 1`.  Then `f = zeta_chi . g` on `Re s > 1` for some entire zero-free `g`.
>
> **Andersson, Lemma 1.**  Same hypothesis as Theorem 1; then `f = int_1^inf q(x)x^{-s}dx + g` with
> `q = o(1)` and `g` entire.
>
> Its proof "applies the Arakelyan approximation theorem to the function `s^2 f(s)` on the half
> plane `Re s >= 1`".

So Lemma 1 = Arakelyan + an elementary Mellin step: with `G` entire and `|s^2 f - G| <= eps` on the
half plane, write `G(s) = G(0) + G'(0)s + s^2 H(s)` with `H` entire; then

```text
f = H + G(0)/s^2 + G'(0)/s + (s^2 f - G)/s^2,
```

`1/s = int_1^inf x^{-1} x^{-s} dx` and `1/s^2 = int_1^inf (log x / x) x^{-s} dx` have `o(1)`
densities, and the last term is `O(|s|^{-2})` on the half plane, hence `L^1` on the line and a
Mellin transform of a bounded `o(1)` density by Mellin inversion plus Riemann--Lebesgue.

For the divisor application the *analytic* case of Arakelyan suffices: the divisor is locally finite
in `C`, so `F'/F` is analytic on an open horn neighbourhood of `Re s >= 1`, not merely continuous
on it.

### The architecture

Write `E = {Re s >= 1}`.

**Step 1 (cutoff).**  Choose a horn neighbourhood `Om'` of `E` with `Om' ⊆ Om`, bounded in the real
direction, and a smooth `chi` with `chi = 1` on a neighbourhood of `E` and `supp chi ⊆ Om'`.  Then
`u := f . dbar chi` is smooth, carried in a strip `{1 - 1 <= Re w <= 1}` disjoint from a
neighbourhood of `E`, and `dbar(chi f) = u`.

**Step 2 (cut the strip).**  With a smooth partition of unity in the imaginary variable, write
`u = sum_n u_n` with `u_n` smooth, `supp u_n ⊆ K_n` compact and `K_n ⊆ {n <= |Im w| <= n+1}`.  Put
`v_n := C(u_n)`, the Cauchy transform; `dbar v_n = u_n`, `v_n` is analytic off `K_n`, and `v_n` is
the Cauchy transform of a *finite* measure carried in `{Re w < 1}`.

**Step 3 (approximate each piece on `E` and on a growing disc).**  For each `n` produce an entire
`p_n` with

```text
|v_n - p_n| <= eps 2^{-n}      on   E ∪ closedBall 0 (n/2).
```

**Step 4 (sum).**  `v := sum_n (v_n - p_n)` converges uniformly on `E` and uniformly on every
compact subset of `C` (a fixed compact lies inside `closedBall 0 (n/2)` for all large `n`), hence
locally uniformly on `C`; near any point only finitely many `u_n` are nonzero and the tail is a
locally uniform limit of analytic functions, so `dbar v = u`.  Therefore

```text
h := chi f - v
```

is entire, and on `E` (where `chi = 1`) `|f - h| = |v| <= 2 eps`.

### Step 3 is elementary

The only nontrivial step is the simultaneous approximation on the *unbounded* `E` together with a
*disc* on the other side.  It is elementary because of two facts.

**(a) A far-left pole is handled by the truncated Laplace kernel on both sets at once.**  For
`Re z < -rho` one has, for every `s` in `E ∪ closedBall 0 rho`,

```text
| 1/(s-z) - truncPole z T s |  =  |exp(-T(s-z))| / |s-z|  =  e^{-T Re(s-z)} / |s-z| ,
```

and `Re(s - z) >= min(1 - Re z, -rho - Re z) > 0` on both pieces, so the error is exponentially
small in `T`, uniformly.  (`truncPole` and this estimate are already Lean theorems here:
`HalfPlanePoleApproximation`, and the measure-superposition form in
`HalfPlaneCauchyTransformApproximation`.)

**(b) Any pole in `K_n` can be pushed far left in two uniform steps.**  For `z in K_n` one has
`|Im z| >= n`, so `dist(z - L, closedBall 0 (n/2)) >= |Im z| - n/2 >= n/2` for every `L`, while
`dist(z - L, E) = 1 - Re z + L > L`.  Hence a shift `L = n/2 - delta` satisfies
`|z - (z-L)| < dist(z-L, E ∪ closedBall 0 (n/2))`, so the geometric expansion

```text
1/(s-z) = sum_k (z-z')^k / (s-z')^{k+1},        z' = z - L,
```

converges uniformly on `E ∪ closedBall 0 (n/2)` with ratio `<= (n/2-delta)/(n/2) < 1`, uniformly in
`z in K_n`.  Two such steps put the pole at `Re z'' <= Re z - (n - 2delta) < -n/2`, i.e. in the
regime of (a).  Poles of higher order are handled the same way, or by differentiating the kernel.

Composing finitely many arbitrary-accuracy steps gives arbitrary accuracy, so Step 3 follows.

### Consequences

Nothing in this route uses Mergelyan, Runge for unbounded sets, Roth's fusion lemma, or Hörmander
estimates.  The pieces needed in Lean are:

| Piece | State |
|---|---|
| `truncPole` and its half-plane error bound | **done** |
| entire approximation of a Cauchy transform on `E` | **done** |
| the same on `E ∪ closedBall 0 rho` for far-left poles | small extension of the above |
| geometric pole pushing, uniform in the pole over a compact | new, elementary |
| smooth cutoff `chi` for a closed set inside an open set | mathlib |
| Cauchy transform `dbarSolution` and `dbar (dbarSolution g) = g` | **corpus** (`DbarSolve`) |
| sup bound `|C g| <= 3 r ||g||_inf` for `g` carried in a disc of radius `r` | corpus `lintegral_ball_norm_inv` gives it |
| partition of unity in the imaginary variable | mathlib |
| locally uniform limits: `dbar` of the sum | corpus `analyticOnNhd_of_dzbarAt_eq_zero` + Weierstrass |

This replaces the earlier assessment that Arakelyan is a Mergelyan-scale obstruction.  It is not:
for a *half plane*, with an *analytic* datum, the theorem is within reach of the machinery already
in this tree.

### Step 3 of the Arakelyan architecture is now Lean-proved

Three modules were added, all axiom-clean (`propext`, `Classical.choice`, `Quot.sound`) and wired
into `GaloisForLFunctions.HTGeometry`.

**`HTGeometry/HalfPlaneCauchyTransformApproximation.lean`**

- `truncPole_eq_shift`, `truncPole_zero_eq_intervalIntegral` — the truncated Laplace kernel as
  `∫_0^T e^{-t z} dt`.
- `norm_truncPole_zero_le`, `hasDerivAt_truncPole_zero`, `deriv_truncPole_zero`,
  `norm_deriv_truncPole_zero_le`, `hasDerivAt_truncPole` — kernel and derivative bounds
  `T e^{T max(0,-Re z)}` and `T^2 e^{T max(0,-Re z)}`.
- `differentiable_truncCauchyTransform` — `s ↦ ∫ φ(x) truncPole (w x) T s dμ(x)` is entire whenever
  the carrier's real parts are bounded above.
- `norm_pole_sub_truncPole_le_of_re` — the error `e^{-T d}/d` from a lower bound `d` for
  `Re (s - a)` alone.
- `exists_entire_approx_cauchyTransform`, `exists_entire_approx_cauchyTransform_of_re_ge`,
  `exists_entire_approx_cauchyTransform_halfPlane_union_ball` — entire approximation of a Cauchy
  transform, on the closed half plane, on any set to the right of the carrier, and on
  `{Re s ≥ 1} ∪ {‖s‖ ≤ ρ}` for a far-left carrier.

**`HTGeometry/HalfPlanePolePushing.lean`**

- `pushedKernel z z' N T` — the `N`-term geometric expansion of `1/(s-z)` about `z'`, each power of
  the moved Cauchy kernel replaced by the same power of the truncated Laplace kernel; entire.
- `norm_pow_sub_pow_le`, `inv_sub_sub_geomSum` (the exact remainder `(a/b)^N/(b-a)`).
- `norm_inv_sub_pushedKernel_le` — the error bound

```text
  (M/d₂)^N / (d₂ - M)  +  N^2 (max 1 (2M/d₁))^N e^{-T d₁} / d₁ ,      M = |z - z'| ,
```

  with `d₁` a lower bound for `Re (s - z')` and `d₂` one for `|s - z'|`.  Separating the two is
  what allows the moved pole to be far to the left of a disc while still close to it in norm.

**`HTGeometry/HalfPlaneGapApproximation.lean`**

- `differentiable_integral_kernel` — a reusable parametric-integral entirety criterion: uniformly
  bounded entire kernels with uniformly bounded derivatives integrate to an entire function.
- `hasDerivAt_pushedKernel`, `norm_pushedKernel_le`, `norm_deriv_pushedKernel_le`.
- **`exists_entire_approx_cauchyTransform_gap`** — the two-piece theorem.  If

```text
  Re (w x) ≤ 1 - delta ,     rho + L + delta ≤ |Im (w x)| ,     1 + rho < L ,
```

  then for every `eps > 0` there is an entire `g` with

```text
  || ∫ φ(x)/(s - w x) dμ(x) - g(s) ||  ≤  eps      for every  s  with  Re s ≥ 1  or  ||s|| ≤ rho .
```

This is exactly Step 3 of the architecture above, with the carrier hypotheses satisfied by every
piece `K_n` of the `∂̄` source (`rho = n/4`, `L = n/2`, `|Im| ≥ n`).  What remains for Arakelyan on
the closed half plane is Steps 1, 2 and 4: the smooth cutoff and `dbar (chi f) = f dbar chi`, the
imaginary-direction partition of unity producing the compactly supported pieces, and the summation
argument (locally uniform convergence, `dbar v = u`, `h = chi f - v` entire).

### The Arakelyan step is closed for the data the card actually consumes

The `∂̄` route of the previous section turned out to be unnecessary.  Andersson applies Arakelyan to
`s^2 f(s)` where `f = F'/F` and `F` realizes the divisor; such an `f` is not an arbitrary function
analytic near the half plane, it is a **Mittag-Leffler series with simple poles**, and for that data
the approximation is termwise and elementary.

Writing `s^2 = (s-a)(s+a) + a^2`,

```text
s^2 ( m/(s-a) - Q(s) )  =  m a^2/(s-a)  +  ( m (s+a) - s^2 Q(s) ) ,
```

the second bracket is already entire, and the single Cauchy kernel `m a^2/(s-a)` is handled by the
truncated Laplace kernel — pushed left first when its pole is not already left of the disc used to
control convergence.  Because the `n`-th approximation is good *both* on `Re s >= 1` and on a disc
of radius `(‖a n‖ - 16)/8`, which grows without bound, the corrected series converges locally
uniformly on the whole plane, so its sum is entire, while on the half plane the accumulated error is
geometric.

New Lean, on top of the three modules above:

- `HalfPlaneGapApproximation.exists_entire_approx_single_kernel` — a single Cauchy kernel with pole
  in `{Re < 1}` is entirely approximable on `{Re s >= 1} ∪ {‖s‖ <= rho}` whenever
  `8 rho + 16 <= ‖a‖`.  The proof splits on whether the pole is already left of the disc (truncated
  Laplace kernel directly) or has large imaginary part (pushed kernel), and the arithmetic
  `|Re a| <= ‖a‖/8  ==>  |Im a| >= ‖a‖/2 >= rho + L + delta` closes the second case.
- `HalfPlaneGapApproximation.exists_entire_approx_single_kernel_halfPlane` — the same on the half
  plane alone, with no condition on the pole beyond `Re a < 1`.
- **`MittagLefflerHalfPlaneApproximation.exists_entire_approx_sq_mittagLeffler`** — for poles
  `a n -> infinity` with `Re (a n) < 1`, entire corrections `Q n` with the standard
  `‖m n/(z - a n) - Q n z‖ <= 2^{-n}` bound on `ball 0 (‖a n‖/2)`, and every `eps > 0`, there is an
  entire `G` with

```text
    || s^2 * ( sum_n ( m n/(s - a n) - Q n s ) ) - G(s) ||  <=  eps      for all  Re s >= 1 .
```

The corpus's own `MittagLefflerConstruction` supplies exactly this data for an arbitrary sequence of
poles tending to infinity, and `MittagLefflerConvergence` supplies the head–tail machinery used for
the local uniform convergence.

What remains of Lemma 1 is the elementary Mellin step: from `|s^2 f - G| <= eps` on the closed half
plane to `f = int_1^inf q(x) x^{-s} dx + entire` with `q = o(1)`, via the half-plane Cauchy
representation and Riemann--Lebesgue.  What remains of Theorem 2 is the identification of `F'/F`
with a Mittag-Leffler series up to an entire function, and what remains of Theorem 1 is the prime
construction, Lemmas 2 and 4-7.

### Exact remaining bricks, with the corpus assets for each

**(A) `logDeriv` of the divisor realization is a Mittag-Leffler series.**

`GaloisForLFunctions.weierstrassGenusFactorAt a n z = weierstrassE n (z / a n)` and
`logDeriv (weierstrassE g) z = -z^g/(1-z)` (`WeierstrassFactorGenus.logDeriv_weierstrassE`), so

```text
logDeriv (fun z => weierstrassE n (z / a n)) z = (z / a n)^n / (z - a n)
                                               = 1/(z - a n) + p_n(z) ,
p_n(z) = ((z/a n)^n - 1)/(z - a n) = (1/(a n)^n) * sum_{j<n} z^j (a n)^{n-1-j}   (a polynomial).
```

So the factor's logarithmic derivative is exactly a Mittag-Leffler term with `m n = 1` and
`Q n = -p_n`, and on `ball 0 (‖a n‖/2)` it is bounded by `2^{-n} * 2/‖a n‖`, which is the bound
`exists_entire_approx_sq_mittagLeffler` consumes.

The missing step is termwise differentiation of the product:

```text
logDeriv (weierstrassGenusProduct a) z = sum_n logDeriv (weierstrassGenusFactorAt a n) z ,
```

for `z` off the zeros.  The corpus already proves this shape twice —
`PowerCanonicalProductLogDeriv.logDeriv_powerCanonicalProduct_eq_tsum` and
`EllipticGammaConeSource.logDeriv_coneProduct_eq_tsum` — and
`WeierstrassFactorizationTheorem.hasProdLocallyUniformlyOn_weierstrassGenusFactorAt` supplies the
locally uniform convergence.  Then
`logDeriv (divisorFunction a b) = logDeriv (product a) - logDeriv (product b)`.

Note this also means the property recorded as `HelsonFactorizationProperty` should be narrowed to
the divisor realizations the card actually feeds it: for a *general* `F` analytic and zero free near
the closed half plane, `F'/F` has no global structure and Andersson's proof needs Arakelyan in full;
for `F = divisorFunction a b` the Mittag-Leffler route above replaces it.

**(B) The Mellin step of Lemma 1.**  From `|s^2 f - G| <= eps` on `Re s >= 1` with `G` entire, write
`G(s) = G(0) + G'(0) s + s^2 H(s)` with `H` entire; then

```text
f = H + G(0)/s^2 + G'(0)/s + (s^2 f - G)/s^2 ,
```

`1/s = int_1^inf x^{-1} x^{-s} dx`, `1/s^2 = int_1^inf (log x / x) x^{-s} dx`, both with `o(1)`
densities, and `phi := (s^2 f - G)/s^2` satisfies `|phi| <= eps/|s|^2` on the closed half plane.  For
such a `phi`:

```text
q(x) := (1/2pi) int_R phi(1+it) x^{it} dt
```

is bounded by `(1/2pi) int |phi(1+it)| dt <= eps/2`, tends to `0` by Riemann--Lebesgue, and
`int_1^inf q(x) x^{-s} dx = (1/2pi) int_R phi(1+it)/(s-1-it) dt = phi(s)` by Fubini plus the
half-plane Cauchy representation.  The last is the only nonelementary input: prove it by the
rectangle Cauchy formula (`RHTower.RectangleLocalCauchyFormula.rectIntegral_cauchyFormula_of_analyticOnNhd`)
on `[1+eta, M] x [-R, R]`, letting `M -> infinity` (right edge dies by `|phi| <= C/|s|^2`), then
`R -> infinity` (horizontal edges die by `int dx/(x^2+R^2) <= pi/(2R)`), then `eta -> 0` by
continuity up to the line.

**(C) Andersson's Theorem 1**, i.e. Lemmas 2 and 4-7: the short-interval prime supply in counting
form and the Vandermonde/Cramer recursion.  This is the remaining large project and is independent
of (A) and (B).

### Brick (A) is closed

`HTGeometry/WeierstrassLogDerivMittagLeffler.lean` (axiom-clean, wired into the umbrella):

- `hasDerivAt_weierstrassGenusFactorAt`, `logDeriv_weierstrassGenusFactorAt` —
  `logDeriv (fun z => weierstrassFactor n (z / a n)) z = (z/a n)^n/(z - a n)`.
- `weierstrassMittagLefflerCorrection a n z = -(sum_{j<n} z^j (a n)^{n-1-j})/(a n)^n`, entire, and
  `logDeriv_weierstrassGenusFactorAt_eq` : `logDeriv (factor n) z = 1/(z - a n) - Q n z`.
- `weierstrassMittagLefflerBound a n = 2^{-n} (2/‖a n‖)`, summable, and
  `norm_weierstrassMittagLefflerTerm_le` on `ball 0 (‖a n‖/2)`.
- `logDeriv_weierstrassGenusProduct_eq_tsum` — termwise logarithmic differentiation, via mathlib's
  `logDeriv_tprod_eq_tsum` and the corpus's
  `hasProdLocallyUniformlyOn_weierstrassGenusFactorAt`.
- **`exists_entire_approx_sq_logDeriv_weierstrassGenusProduct`** and
  **`exists_entire_approx_sq_logDeriv_divisorFunction`** — for every `eps > 0` there is an entire
  `G` with

```text
    || s^2 * logDeriv (divisorFunction a b) s - G(s) ||  <=  eps      for all  Re s >= 1 ,
```

whenever both zero and pole sequences tend to infinity, are nonzero, and lie in `{Re < 1}`.

`exists_entire_approx_sq_mittagLeffler` was generalized on the way: its bound hypothesis is now an
arbitrary summable `u n` rather than `2^{-n}`.

**This is Arakelyan's contribution to Andersson's Lemma 1, for exactly the data the card feeds it,
proved unconditionally.**  What is left of Lemma 1 is brick (B), the Mellin step; what is left of
Theorem 1 is brick (C), the prime construction.

### Brick (B), first half: the half-plane Cauchy representation is closed

`HTGeometry/HalfPlaneCauchyRepresentation.lean` (axiom-clean, wired):

- `lineKernel φ s y = φ (1 + i y) / ((1 + i y) - s)`, `norm_lineKernel_le`, `integrable_lineKernel`
  (envelope `C/(1+y^2)/(Re s - 1)` against `integrable_inv_one_add_sq`).
- `norm_horizontal_edge_le`, `norm_vertical_edge_le` — the three moving edges of the square
  `[1,R] x [-R,R]` are `O(1/R^2)` and `O(1/R)` respectively, from `‖φ‖ <= C/‖z‖^2`.
- `tendsto_edgeBound` — `C/R^2/(R-a) * (k R) -> 0`.
- **`halfPlane_cauchy_representation`** —

```text
  int_R  φ(1 + i y)/((1 + i y) - s)  dy  =  -2π φ(s)         (Re s > 1),
```

for `φ` analytic on `{Re s >= 1}` with `‖φ z‖ <= C/‖z‖^2` there.  The left edge of the square sits
exactly on the line — legitimate because `φ` is analytic *on* the closed half plane, which is what
`RHTower.rectIntegral_cauchyFormula_of_analyticOnNhd` needs — so no `eta -> 0` limit is required,
and the single parameter `R -> infinity` suffices.

Formalization note: a multi-line `calc` whose first line is `‖∫ y in a..b, f y` parses the integral
across the line break and swallows the closing `‖`; write the step as a term
(`exact le_trans this (le_of_eq (by ring))`) instead.

What remains of brick (B) is the Mellin half: with

```text
  q(x) := (1/2π) int_R φ(1 + i t) x^{i t} dt ,
```

Fubini gives `int_1^inf q(x) x^{-s} dx = (1/2π) int_R φ(1+it)/(s - 1 - it) dt = φ(s)` by the
representation above, `‖q‖ <= C/2` by the envelope, and `q(x) -> 0` by Riemann--Lebesgue
(`MeasureTheory.Integrable.tendsto_integral_exp_smul_cocompact`).
