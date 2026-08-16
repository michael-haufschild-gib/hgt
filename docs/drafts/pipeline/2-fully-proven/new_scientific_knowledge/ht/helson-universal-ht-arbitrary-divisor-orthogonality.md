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
