# Eight remaining `new_scientific_knowledge/other` cards — Stage-3 closure ledger

- **ID:** `other-nsk-eight-card-stage3-ledger`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAM
- **Scope:** the eight cards left in `2-fully-proven/new_scientific_knowledge/other`
- **Completion criterion:** every card has its own theorems as unconditional Lean theorems
  (no hypotheses replacing content, no `sorry`/`axiom`/`opaque`/`unsafe`), umbrella-wired,
  and is moved to `3-formalized/new_scientific_knowledge/other`.

## Card status

| # | Card | Exact remaining Lean obligation |
|---|---|---|
| 1 | `all-depth-compatible-pair-face-differential-matroid` | arbitrary-**coset** (arbitrary complex translation) extension of the multiple elliptic-gamma face-packet independence chain, then the operator-row matroid/rank law for it |
| 2 | `all-depth-pair-face-signature-completeness` | depth-two triptic DA-completeness (`U ∈ Q_2` DA ⟺ `R_2(U)=0`), the compatible pair-divisor module `Comp_d`, and the realization isomorphism |
| 3 | `bessel-order-intensity-hypertranscendence` | the Dreyfus DA→periodic-exponential special case; the parameterized difference-Galois programme is far advanced (see the card's own long Lean log) |
| 4 | `differential-variational-building-balance-law` | (i) σ-semilinear action on `M_K = Ω/Tor` as a matrix in `GL_r(R_K)`; (ii) `μ_n` = Cartan prefix invariants; (iii) bounded/linear dichotomy (affine-building semisimplicity) |
| 5 | `irrational-triptic-source-effectivity-character` | global analytic-subring packaging of the source boundary; FHRZ gerbe / differential-character comparison |
| 6 | `isogeny-tail-maurer-cartan-holography` | five scheme/jet instantiations listed in the card's Lean status |
| 7 | `torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness` | `HasAbeDampingFamily` (Abe Prop. 8.2) and `IsAbePositiveTorusless` |
| 8 | `universal-first-order-entire-cascade-unit-cost` | item 3: general `helim` — A2 `AlgebraicBorderShape`, A3 `AlgebraicPeelInduction`, A4 Wiman supply, A5 extension transfer |

## Working order

1. Card 1 (coset extension) — machinery exists, no conceptual obstruction.
2. Card 7 — two concrete analytic constructions.
3. Card 8 — fully designed module plan A2–A5.
4. Card 4 — algebraic links first, dichotomy last.
5. Cards 2, 5, 6, 3.

## Log

- 2026-08-20 — ledger opened; architecture of the elliptic-gamma face chain audited.
- 2026-08-20 — **card 1 core closed**: the arbitrary-complex-translation (coset) extension of the
  multiple elliptic-gamma face-packet chain is Lean-certified, axiom-clean, umbrella-wired
  (14 new modules, capstones `cosetProperFacePackets_diffIndepOn`,
  `cosetCompleteDifferentialMatroid`, `cosetCompleteDifferentialRank`,
  `arbitraryTranslate_eq_deepSpan_add_differentialAlgebraic`).  See Serena memory
  `nsk-other/coset-face-packet-chain-built-2026-08-20`.
- 2026-08-20 — **card 2 blocker dissolved**: the depth-two triptic DA-completeness theorem that
  cards 1 and 2 both assume is already unconditional in the tree, as
  `HTGeometry.differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero`
  (`TripticCompleteness`), axiom-clean.  Both cards' remaining mathematics is now the *all-depth
  induction*: `Q_d`, `ρ_d`, `PairFace_d`, the inductive step, and the realization half.
- 2026-08-20 — all-depth programme opened (closes cards 1 and 2 together).  Two modules landed,
  built and axiom-clean: `HTGeometry/AllDepthMixedConstraintClass.lean` (the difference cube
  `diffCube`, the class `MixedConstGermSet`, and `mixedConstGermSet_pair_iff` identifying the
  depth-two case with the corpus's `MixedConstGerm`) and `HTGeometry/AllDepthMeroClass.lean`
  (the class inside `meroField ℂ`, `exists_realizesMero`, `diffCubeMero_insert`,
  `differentialAlgebraicOver_pairFaceWitnessMero`, `realizesMero_translate`,
  `realizesMero_congr`, `periodicOneGerm_of_realizesMero`).  Full design and the remaining step
  list are in Serena memory `nsk-other/all-depth-pair-face-programme-2026-08-20`.

## Card audit against the tree (2026-08-20)

Several cards' "Lean does not yet formalize …" notes are stale.  Verified findings:

- **Card 2** — the assumed depth-two triptic DA-completeness theorem is already unconditional:
  `HTGeometry.differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero` (`TripticCompleteness`).
- **Card 5** (`irrational-triptic-source-effectivity-character`) — the card says the FHRZ group–Čech
  complex and the differential gamma gerbe are absent.  The tree already owns
  `GroupCechBicomplex` (the total complex of a group–Čech bicomplex, `totalD2_totalD1`,
  `totalD3_totalD2`, sector restrictions), `GammaGerbeDixmierDouadyGenerator` (the DD cocycle
  `gammaGerbeDD`, `coboundary₃_gammaGerbeDD = 0`, the alternation obstruction) and
  `GammaGerbeThetaCocycle` (FHRZ's `thetaProd_cocycle`, `thetaProd_defect_eq_gammaGerbeExponent`,
  and **`coboundary_gammaGerbeExponent_not_coboundary`** — the gamma gerbe has no holomorphic
  trivialisation), plus `CechLowDegreeComplex`, `CechFineAcyclicModule`.
  Its two Lean gates are therefore (i) *global analytic-subring packaging of the source boundary*
  and (ii) the *differential-character comparison*.  For (i) the corpus already packages the gamma
  products themselves (`MeromorphicEllipticGamma`: `ellipticGammaForwardAnalytic`,
  `ellipticGammaBackwardAnalytic`, `ellipticGammaMero`, both nonzero); what is missing is the
  same packaging for the two theta boundaries
  `ellipticGammaMultiplicativeThetaBoundary(Tau)` — i.e. locally uniform convergence of the two
  single q-Pochhammer products, hence entirety — and then the three source equations restated as
  identities in `meroField ℂ` (which removes the pointwise nonvanishing hypothesis of
  `ellipticGammaProduct_add_sigma` / `_add_tau`).
- **Card 7** — `QuasiAbelianDampedExtensionBasis` (2026-08-19) adds `IsAbePositiveToruslessBasis`;
  the two open obligations of the card (`HasAbeDampingFamily`, `IsAbePositiveTorusless`) are still
  open.
- **Card 8** — `AlgebraicBorderShape` (item A2) still absent; `PlaceGrading` (A1) present.

## Landed 2026-08-20 (second stretch)

**Card 5, gate (i) closed.**  `HTGeometry/EllipticGammaThetaBoundaryAnalytic.lean` — locally
uniform convergence of both single q-Pochhammer boundary products, entirety of both structural
boundaries, their packaging in `analyticSubring ℂ` / `meroField ℂ`, and the three source equations
`ellipticGammaMero_add_sigma / _add_tau / _add_one` as **unconditional** identities in the
meromorphic germ field (no regular-locus hypothesis).  Axiom-clean, wired, built.

**All-depth programme (cards 1 and 2).**  Four modules, all axiom-clean, wired, built:

- `HTGeometry/AllDepthMixedConstraintClass.lean` — difference cube `diffCube`, the class
  `MixedConstGermSet`, `mixedConstGermSet_pair_iff`, `diffCube_union`.
- `HTGeometry/AllDepthMeroClass.lean` — the class inside `meroField ℂ`, `exists_realizesMero`,
  `realizesMero_translate/_congr/_diffCubeMero`, `periodicOneGerm_of_realizesMero`,
  `differentialAlgebraicOver_pairFaceWitnessMero`.
- `HTGeometry/AllDepthPairFaceSignature.lean` — **the forward half of the all-depth pair-face
  theorem**: `pairFaceSignature_eq_zero_of_differentialAlgebraicOver`.
- `HTGeometry/AllDepthBottomCharge.lean` — the bottom charge: the pair-face signature *is* the
  orbit sum of the bottom charge (`additiveOrbitalDivisorAt_pairFaceWitnessFun`), the charge is
  `Λ_k`-invariant and finitely supported on the elliptic quotient, and
  **`exists_mixedConstGermSet_erase_of_bottomCharge_eq_zero`** — the kernel of the bottom charge
  is the next class `Q_(d−1)`.
- `HTGeometry/AllDepthTelescope.lean` — **`exists_telescopeCube`**: a finitely supported divisor on
  an abelian group whose line sums vanish in every direction of a finite family of pairwise free
  infinite-order directions is the full difference cube of a finitely supported divisor.  (Also
  `lineTail`, `lineTail_sub`, `exists_finset_support_lineTail`, `finsum_lineTail_eq_zero`.)

Remaining for cards 1–2: the theta realization (`Z = C·λ_k` with `ρ_k(Z) = ρ_k(F)`, `Z` DA) and
the descent itself.

## Landed 2026-08-20 (third stretch)

Two further all-depth modules, both wired, built and axiom-clean:

- `HTGeometry/AllDepthAtomRealization.lean` — `atomRealization σ j R c`, the finite combination of
  line-atom jets realizing a prescribed divisor at one order:
  `laurentCoeff_atomRealization_line` (prescribed coefficient on each prescribed line),
  `laurentCoeff_atomRealization_off`, `laurentCoeff_atomRealization_of_ne_order`,
  `atomRealization_periodic`, `realizedDA_atomRealization` and
  `differentiallyAlgebraic_toMeromorphicNFOn_atomRealization`.
- `HTGeometry/AllDepthSignatureDescent.lean` — `pairFaceWitnessFun_eq_shiftDiffFun` (the depth-`d`
  witness is the `τ k`-difference of the depth-`(d−1)` one),
  `additiveOrbitalDivisorAt_comp_add` (translation covariance of the orbital divisor) and
  **`additiveOrbitalDivisorAt_shiftDiffFun`** — the displacement formula
  `S^(d)_(ij)(F)(p,ℓ) = R(p + τ k, ℓ) − R(p, ℓ)`.

`AllDepthTelescope` also gained the two vanishing lemmas
`eq_zero_of_invariant_of_finite_support` and **`eq_zero_of_invariant_of_finite_classes`**
(a divisor with finitely many nonzero classes modulo a subgroup, invariant under a translation of
infinite order modulo it, vanishes) — the second is the exact tool that turns a vanishing depth-`d`
signature into a vanishing depth-`(d−1)` one.

Next: finiteness of the nonzero classes of the depth-two orbital divisor modulo `H_(ij)`
(from `TripticLineFiniteness.exists_finset_pole_classes` plus
`TripticOrbitalDivisorLinearity.laurentCoeff_boundary_periodic_one/_tau`), which closes the
signature descent; then the assembly of the realization `Z` and the induction.

## Landed 2026-08-20 (fourth stretch) — the all-depth main theorem is CLOSED

`GaloisForLFunctions.HTGeometry.AllDepthCompleteness` now proves, unconditionally and axiom-clean
(`[propext, Classical.choice, Quot.sound]`), the main theorem of
`all-depth-pair-face-signature-completeness`:

```text
differentialAlgebraicOver_of_pairFace_eq_zero        -- the converse half, by induction on |s|
differentialAlgebraicOver_iff_pairFace_eq_zero       -- F is DA  ⟺  every pair-face signature is 0
differentialAlgebraicOver_iff_pairFace_univ          -- the same on the full parameter family
```

The card assumed the depth-two theorem as a hypothesis.  It is **not** a hypothesis here: the base
case is the corpus's unconditional
`TripticCompleteness.differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero`.

Supporting modules added in this stretch (all wired, built, axiom-clean):

- `HTGeometry/AllDepthBottomRealization.lean` — `lineLattice` (the lattice `ℤ + ℤσ` as an
  `AddSubgroup`), `multiAtomRealization` (a finite atom sum carrying prescribed coefficients at
  every order `-(j+1)`, `j < N`) with its exact Laurent data, `laurentCoeff_diffCube` (the
  difference cube acts on Laurent coefficients as the translated cube), and the capstone
  **`exists_multiAtomRealization_of_bottomCharge`**: every prescribed divisor on the elliptic
  quotient with vanishing transverse line sums and bounded order is the full difference cube of the
  principal-part data of an explicit finite atom sum.  The proof descends the divisor to
  `ℂ ⧸ (ℤ + ℤσ)`, applies `exists_telescopeCube` there, and lifts through `Quotient.out`.
- `HTGeometry/AllDepthAtomClass.lean` — the atom sum is itself a member of the class:
  `shiftConstGerm_jetAtom` (a jet atom drops by `-2πi` at order zero and is unchanged above it),
  `shiftConstGerm_multiAtomRealization`, `eventually_zero_diffCube`,
  `mixedConstGermSet_zero_of_shiftConstGerm` and
  **`mixedConstGermSet_multiAtomRealization`** — with `k` and one further direction present, the
  full cube of an atom sum is germ-zero.
- `HTGeometry/AllDepthCompletenessCore.lean` — `laurentCoeff_lineLattice_of_periods`,
  **`exists_order_bound_of_lineLattice_invariant`** (finitely many pole classes + class-function
  order ⟹ bounded pole order), and the three freeness laws `lineLattice_free_single`,
  `lineLattice_free_pair`, `tripticPeriodGroup_free`.

Structural change: `pairFaceWitnessFun`, `pairFaceWitnessMero`, `bottomWitnessFun`,
`bottomWitnessMero` and every theorem about them now take an explicit `Finset ι` of active
directions instead of `Finset.univ`, and the class hypotheses are function-level
(`PeriodicOneGerm f`, `MixedConstGermSet τ s f Cst`) instead of germ-level.  Both changes are what
make the induction on `s.card` run inside one fixed index type.

Remaining for card 2: the exact-image half — the group algebra `A_S = ℂ[δ][ℂ/H_S]`, the
pushforwards `p_(S,T)`, the compatible-pair space `Comp_d`, the simultaneous finite-divisor lifting
lemma, and the isomorphism `Q_d/(Q_d ∩ Mer_DA) ≅ Comp_d`.
Remaining for card 1: the matroid statement over the all-depth class (the coset chain is already
closed).

## Landed 2026-08-20 (fifth stretch) — the simultaneous finite-divisor lifting lemma

`GaloisForLFunctions.HTGeometry.AllDepthSimultaneousLift` (wired, built, axiom-clean) proves the
second `[PROVED HERE]` lemma of `all-depth-pair-face-signature-completeness`, abstractly on any
abelian group:

```text
orbitSum w B p = ∑ᶠ n : ℤ, B (p + n • w)          the orbit-sum pushforward
orbitSum_invariant, orbitSum_finite_classes, orbitSum_add, orbitSum_sub
orbitSum_comm                       orbit sums in two free directions commute
finite_line_support_of_finite_classes
                                    a divisor with finitely many classes along one direction meets
                                    every transverse line finitely
orbitSum_step_eq_zero, finite_support_telescopeCube
orbitSum_telescopeCube_eq_zero      a full difference cube has no orbit sum in its own directions
transversalLift, exists_support_transversalLift
orbitSum_transversalLift            the orbit sum of the canonical transversal lift is the original
exists_simultaneous_lift            **the lemma**: divisors D_i, each invariant along w_i and
                                    finitely supported modulo it, with pairwise agreeing orbit sums,
                                    are the orbit-sum pushforwards of one finitely supported divisor
```

The proof is the card's: lift all but the last component by induction, subtract, note the error has
vanishing orbit sums in every earlier direction, telescope it on the quotient by the last direction
(`exists_telescopeCube`), and lift the telescoping datum through the canonical transversal — the
lift disturbs no earlier component because a full difference cube has vanishing orbit sums in its
own directions.

This is the ideal-theoretic content the card phrases as `⋂_i ker q_i = (∏_i x_i)A_d` plus exactness
at the middle of `A_d → ⊕_i A_d/(x_i) → ⊕_(i<j) A_d/(x_i,x_j)`, proved directly on divisors rather
than through the Laurent-ring UFD.

Still open for the exact-image theorem: bottom-charge surjectivity (`ρ_d(B·Ψ_(d−1)) = B`), which
needs the multiple-elliptic-gamma hierarchy's difference law, and the packaging of the signature as
an element of `A_S = ℂ[δ][ℂ/H_S]`.

## Landed 2026-08-20 (sixth stretch) — the universal carrier is in the class

`GaloisForLFunctions.HTGeometry.AllDepthUniversalCarrier` (wired, built, axiom-clean) identifies the
card's `Ψ_(d−1)` inside the Lean class:

```text
diffCubeMero_face                 the difference cube of a face coordinate deletes exactly its own
                                  directions:  □_t (Face J) = Face (J ∪ t)   for t disjoint from J
universalCarrierMero τ hτ s       = Face (univ \ s):  the multiple elliptic gamma logarithmic
                                  derivative whose parameters are exactly the directions of s
diffCubeMero_universalCarrier     □_s Ψ_s = -2πi, the terminal constant
addTranslationMeroEquiv_one_universalCarrier
periodicOneGerm_universalCarrier
mixedConstGermSet_universalCarrier        **Ψ_s ∈ Q_s**
bottomWitnessMero_universalCarrier        ρ-witness of Ψ_s = Face (univ \ {k})
exists_bottomWitnessMero_universalCarrier_theta
    = a translated theta logarithmic derivative plus a constant, so the bottom charge of Ψ_s is the
    unit divisor of the surviving direction
```

This is the card's "`ρ_d(B Ψ_(d−1)) = B`" carrier, now a Lean object with its two class properties
and its bottom identification proved.  What still separates it from bottom-charge surjectivity is
the jet layer: realizing an arbitrary finite divisor needs the finite combination
`∑_(j,q) c_(j,q) δ^j T_q Ψ_s`, i.e. Laurent data for jets of translates of the carrier, transported
from the corpus's `jetAtom` laws through the theta identification above.

## Landed 2026-08-21 (seventh stretch) — bottom-charge surjectivity

`GaloisForLFunctions.HTGeometry.AllDepthCarrierJets` (wired, built, axiom-clean) closes the card's
"the bottom-charge map `ρ_d` is surjective, `ρ_d(B Ψ_(d−1)) = B`":

```text
realizesMero_thetaLogDerivMero        the theta germ is realized by `thetaSource`
diffCubeMero_add, _finsetSum, _algebraMap_mul, _differentialJet
    the difference cube is a constant-coefficient differential operator, so it commutes with jets,
    with translations and with ℂ-linear combinations
carrierAtomCombination τ hτ s k N R c
    ∑_(j<N) ∑_(q∈R) (c j q / ((-1)^j j!)) · δ^j T_((1+τ_k)−q) Ψ_s
diffCubeMero_carrierAtomCombination, addTranslationMeroEquiv_one_carrierAtomCombination
exists_mixedConst_carrierAtomCombination      **the combination is in Q_s**
atomSumMero, realizesMero_atomSumMero         the atom-sum germ is realized by multiAtomRealization
exists_bottomWitnessMero_carrierAtomCombination
    its bottom witness is the atom sum up to an additive constant
exists_class_member_with_prescribed_bottomCharge
    **every atom-sum divisor is the bottom charge of a member of the class**
```

Combined with `AllDepthBottomRealization.laurentCoeff_multiAtomRealization_line/_off/_of_lt`, this
realizes an arbitrary finite divisor of bounded order on `ℂ/(ℤ+ℤτ_k)`.

Remaining for the exact-image theorem: the packaging of the pair-face signature as an element of
`A_S = ℂ[δ][ℂ/H_S]` with the pushforwards `p_(S,T)` and the compatible space `Comp_d`, triple
compatibility of actual signatures (for triples through the distinguished direction this is
`orbitSum_comm` plus `additiveOrbitalDivisorAt_pairFaceWitnessFun`), and the induction assembling
`Q_d/(Q_d ∩ Mer_DA) ≅ Comp_d` from the simultaneous lifting lemma, the surjectivity above and the
completeness theorem.

## Landed 2026-08-21 (eighth stretch) — the universal cyclic normal form

`GaloisForLFunctions.HTGeometry.AllDepthCarrierSpan` and `...AllDepthNormalForm` (wired, built,
axiom-clean) close the card's universal cyclic reduction `(3)`–`(4)`:

```text
carrierSpan τ hτ s            the ℂ-span of all jets of all translates of Ψ_s
carrierAtomCombination_mem_carrierSpan
carrierSpan_erase_le          deleting a direction keeps the span (the coface law exhibits
                              Ψ_(s\{k}) as the translation defect of Ψ_s)
exists_multiAtomRealization_matching
                              every lattice-invariant divisor of bounded order with finitely many
                              classes is the exact Laurent datum of an atom sum
universalCarrierMero_pair, jet_ellipticGamma_mem_carrierSpan
exists_carrierSpan_normal_form_pair    depth two, from the corpus's triptic normal form
exists_carrierSpan_normal_form
    **every member of Q_s differs from an element of carrierSpan τ hτ s by a differentially
    algebraic germ**
```

The induction is: realize the bottom charge by a carrier jet combination (surjectivity), subtract,
land in `Q_(s\{k})` (the kernel theorem), recurse, and push the smaller carrier's span into the
larger one.  The depth-two base is the corpus's
`TripticNormalForm.exists_gammaCorrection_differentiallyAlgebraic` together with
`MultipleEllipticGammaBottomFace.multipleEllipticGammaLogDerivFaceMero_two_surviving`, which
identifies `Ψ_({i,j})` with a translate of the order-one elliptic gamma logarithmic derivative.

This is the statement `all-depth-compatible-pair-face-differential-matroid` calls
"every `F ∈ Q_d` is congruent modulo DA functions to `P Ψ_(d−1)` for some finite
arbitrary-translation operator `P`", i.e. the cyclic form `Comp_d = B·PairFace_d(Ψ_(d−1))`.

## Landed 2026-08-21 (ninth stretch) — the signature is a compatible finite divisor family

Three further modules (wired, built, axiom-clean) supply the "image ⊆ Comp_d" half of the
exact-image theorem and the divisor algebra the realization half needs:

```text
HTGeometry/AllDepthClassDivisor.lean
  DivInvariant, DivFiniteClasses and their closure under ± ;
  divQuotient, divQuotient_mk, exists_finset_support_divQuotient
  exists_antidifference_of_orbitSum_zero  a divisor with vanishing line sums in an
                                          infinite-order direction is a one-step difference
  eq_zero_of_shiftDiff_eq_zero            and that difference operator is injective
HTGeometry/AllDepthSignatureProperties.lean
  pairSig τ s f i j ℓ p                   the pair-face signature at an ordered pair
  divInvariant_pairSig                    it is a class function modulo H_(ij)
  divFiniteClasses_pairSig                with finitely many nonzero classes
  exists_order_bound_pairSig              and bounded order
  pairSig_eq_zero_of_mixedConstGermSet_erase
      a member of Q_(s\{k}) has trivial signature at every pair through k
HTGeometry/AllDepthTripleCompat.lean
  finite_grid_support_of_finite_classes, finsum_comm_grid, mixedConstGerm_comm
  pairSig_triple_compat                   **the three pair-face signatures of a triple have one
                                          common pushforward**
```

`pairSig_triple_compat` is the card's "higher face reciprocity": each signature is computed by
`triptic_orbit_residue_reciprocity` in the *other* direction of its own pair, and then both
pushforwards are the same double sum of `laurentCoeff (Δ_j Δ_k W)` over the `(τ_j, τ_k)` grid,
where `W = □_(s\{i,j,k}) F`; Fubini on that grid (finite because the grid meets each
`ℤ + ℤτ_i`-class at most once) finishes.

This closes `PairFace_d(Q_d) ⊆ Comp_d`.  What is left of the exact-image theorem is the converse
inclusion: the induction realizing an arbitrary compatible family, for which every ingredient is
now in place (`exists_simultaneous_lift`, `exists_class_member_with_prescribed_bottomCharge`,
`exists_antidifference_of_orbitSum_zero`, `eq_zero_of_shiftDiff_eq_zero`,
`pairSig_eq_zero_of_mixedConstGermSet_erase`, `additiveOrbitalDivisorAt_shiftDiffFun`).

## Landed 2026-08-21 (tenth stretch) — the realization ingredients

`GaloisForLFunctions.HTGeometry.AllDepthPeriodSpan` and `...AllDepthRealization` (wired, built,
axiom-clean):

```text
periodSpan τ t = ℤ + ∑_(i ∈ t) ℤ τ_i, periodSpan_free, tripticPeriodGroup_le_periodSpan
lineLattice_free_triple                 (in AllDepthCompletenessCore)
tripticPeriodGroup_comm
pairSig_symm                            the signature is symmetric in its pair (reciprocity)
pairSig_descent                         the depth-d signature is the τ_k-displacement of the
                                        depth-(d−1) one
pairSig_add                             the signature is additive
exists_depthTwo_member_with_prescribed_divisor
    **depth-two realization**: every finite class divisor of bounded order is the orbital divisor of
    a member of the depth-two class (the corpus's `exists_mem_class_with_prescribed_divisor`
    together with a transversal of the classes)
exists_bottom_realizer
    **the components of a compatible family through one distinguished direction are realized**:
    the simultaneous lifting lemma on `ℂ ⧸ (ℤ + ℤτ_k)` produces one bottom charge, and
    `exists_class_member_with_prescribed_bottomCharge` realizes it
```

What is left of the exact-image theorem is exactly the induction that glues these: at depth `d ≥ 3`
take `F₀` from `exists_bottom_realizer`, form the errors `E_ij = D_ij − S_ij(F₀)` on the pairs below
`k`, antidifference them along `τ_k` (`exists_antidifference_of_orbitSum_zero`), check that the
antiderivatives are again a compatible family (`eq_zero_of_shiftDiff_eq_zero` for uniqueness and
`periodSpan` for the invariance bookkeeping), realize them by the inductive hypothesis on `s \ {k}`,
and add — the sum's signature is `D` by `pairSig_add`, `pairSig_descent` and
`pairSig_eq_zero_of_mixedConstGermSet_erase`.

## Landed 2026-08-21 (eleventh stretch) — THE EXACT-IMAGE THEOREM IS CLOSED

`GaloisForLFunctions.HTGeometry.AllDepthExactImage` (wired, built, axiom-clean) closes the
`Exact image and universal pair-face normal form` section of
`all-depth-pair-face-signature-completeness`:

```text
finite_line_support_of_divFiniteClasses, mixedConstGermSet_of_erase
exists_class_member_with_prescribed_pairSig
    **every compatible family of finite class divisors is the pair-face signature of a member of
    the all-depth class**
exists_class_member_with_prescribed_pairSig_iff
    the two-way form: a family is a pair-face signature exactly when each component is a finite
    class divisor of bounded order, the family is symmetric, and every triple has one common
    pushforward
```

Together with `AllDepthCompleteness.differentialAlgebraicOver_iff_pairFace_eq_zero` (injectivity)
and `AllDepthTripleCompat.pairSig_triple_compat` (image ⊆ Comp_d) this is the card's isomorphism
`Q_d/(Q_d ∩ Mer_DA) ≅ Comp_d`, in the concrete divisor description.

The induction is the card's: realize the components through one distinguished direction with
`exists_bottom_realizer`, antidifference the residual errors along `τ_k`
(`exists_antidifference_of_orbitSum_zero`), check that the antiderivatives are again symmetric
(`eq_zero_of_shiftDiff_eq_zero`) and triple-compatible (`periodSpan_free` plus
`eq_zero_of_invariant_of_finite_classes`), realize them by the inductive hypothesis on `s \ {k}`,
and add (`pairSig_add`, `pairSig_descent`, `pairSig_eq_zero_of_mixedConstGermSet_erase`).

**Card status.**  Of the card's five `[PROVED HERE]` sections, three are now fully Lean: the main
theorem, the exact image / universal normal form, and the multi-telescoping lemma.  Two remain:
`Complete differential-translation module consequences` (the criterion `P·F` is DA iff
`π_(ij)(P)·S_(ij)(F) = 0`, with the annihilator and DA translation spectrum) and the
`Multiplicative theorem`.  The card therefore stays at stage 2 until those are formalized.

## Landed 2026-08-21 (twelfth stretch) — the differential-translation module consequences

`GaloisForLFunctions.HTGeometry.AllDepthOperatorCriterion` (wired, built, axiom-clean) closes the
fourth `[PROVED HERE]` section of `all-depth-pair-face-signature-completeness`:

```text
diffCube_comp_add, pairSig_translate          translation equivariance
pairSig_deriv, pairSig_iteratedDeriv          δ becomes the order shift with the jet factor
                                              ∏_(t<n)(ℓ+t+1)
pairSig_const_mul, pairSig_finsetSum          ℂ-linearity
mixedConstGermSet_comp_add/_const_mul/_add/_finsetSum, mixedConstGermSet_deriv,
periodicOneGerm_deriv                          closure of the class under the generators
transOpFun, transOpMero, transOpDiv           a finite constant-coefficient
                                              differential-translation operator, on functions,
                                              germs and divisors
pairSig_transOp                               **the signature of an operator output is the operator
                                              applied to the signature**
differentialAlgebraicOver_transOp_iff          **`P·F` is DA ⟺ `π_(ij)(P)·S_(ij)(F) = 0` for every
                                              pair**
```

Only the card's `Multiplicative theorem` section is now missing for stage 3.

## 2026-08-21 — CARD PROMOTED: `all-depth-pair-face-signature-completeness` → stage 3

All five `[PROVED HERE]` sections of the card are unconditional, axiom-clean Lean, in twenty-four
`AllDepth*` modules wired into `GaloisForLFunctions.HTGeometry`:

1. main theorem — `AllDepthCompleteness.differentialAlgebraicOver_iff_pairFace_eq_zero`;
2. exact image / universal normal form — `AllDepthExactImage.exists_class_member_with_prescribed_pairSig_iff`;
3. multi-telescoping lemma — `AllDepthTelescope.exists_telescopeCube`;
4. differential-translation module consequences — `AllDepthOperatorCriterion.differentialAlgebraicOver_transOp_iff`;
5. multiplicative theorem — `AllDepthMultiplicative.differentialAlgebraicOver_iff_pairFace_logDeriv`.

plus the simultaneous lifting lemma (`AllDepthSimultaneousLift.exists_simultaneous_lift`) and the
bottom-charge kernel (`AllDepthBottomCharge.exists_mixedConstGermSet_erase_of_bottomCharge_eq_zero`).
The card's depth-two hypothesis is discharged — the base case is the corpus's own unconditional
triptic completeness theorem.

The card now lives at `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/other/`.

**Seven cards remain in the stage-2 `other` folder.**  Next is
`all-depth-compatible-pair-face-differential-matroid`, whose own Lean note says its single
remaining input was exactly the theorem just closed; what is left there is the Lean chaining of
formula `(1)`: `AllDepthNormalForm.exists_carrierSpan_normal_form` (every `F ∈ Q_d` is an operator
on `Ψ_(d−1)` modulo DA) into `MultipleEllipticGammaCosetSpanDecomposition.
arbitraryTranslate_eq_deepSpan_add_differentialAlgebraic` and
`MultipleEllipticGammaCosetCompleteDifferentialMatroid.cosetCompleteDifferentialMatroid_rationalBase`,
together with invariance of the differential matroid under a differentially algebraic perturbation.

## 2026-08-21 — CARD PROMOTED: `all-depth-compatible-pair-face-differential-matroid` → stage 3

`GaloisForLFunctions.HTGeometry.AllDepthMatroidChain` (wired, built, axiom-clean) supplies the
card's last open item — the concrete hierarchy-to-row identification — and with it the rank formula
for an **arbitrary** finite family in `Q_d`:

```text
exists_transOp_of_mem_carrierSpan, exists_deepCombination_of_jet_translate,
exists_deepRow_of_class, exists_operatorRow_of_class_family,
allDepth_completeDifferentialRank, allDepth_completeDifferentialRank_rationalBase
```

Chain: `AllDepthNormalForm.exists_carrierSpan_normal_form` → coset span decomposition →
row assembly → `differentialFamilyMatroid_congr_of_sub_differentialAlgebraic` →
`cosetCompleteDifferentialRank(_rationalBase)`.

**Six cards remain** in `2-fully-proven/new_scientific_knowledge/other`:
`bessel-order-intensity-hypertranscendence`, `differential-variational-building-balance-law`,
`irrational-triptic-source-effectivity-character`, `isogeny-tail-maurer-cartan-holography`,
`torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness`,
`universal-first-order-entire-cascade-unit-cost`.

## 2026-08-21 — `bessel-order-intensity-hypertranscendence`: the endgame's hypothesis, in two halves

Two new modules, both wired, built and axiom-clean:

* `GaloisForLFunctions.HTGeometry.DifferentialGaloisScalarZeroSet` —
  `deriv_eq_zero_of_scalarSpan_of_zeroSet`, `jet_relation_of_scalarSpan_of_zeroSet`,
  `isomonodromy_of_no_riccati_of_zeroSet`, `linearJetSolutions`, `matrixLinearJetSolutions`,
  `linearJetPolynomial(_ne_zero)`, `eval_linearJetPolynomial_eq_zero_of_scalarSpan`,
  `deriv_eq_zero_of_scalarSpan_of_linear`, **`isomonodromy_of_no_riccati_of_linearRelation`**.
* `GaloisForLFunctions.HTGeometry.DifferentialConstantRelationDescent` —
  `exists_descend_of_coeff_mem_range`, **`exists_constantCoeff_relation_of_sigmaFixed`**,
  `differentialPolynomialEvalOver_eq_zero_of_point`.

These split the single remaining arrow of the card ("differential algebraicity forces a compatible
derivation") into two, and close the second one outright:

1. DA over `ℂ(ν)` ⟹ a **differential** relation on the Galois matrices.  The comparison matrix has
   `σ`-invariant entries, so a relation over the base descends to the constants
   (`exists_constantCoeff_relation_of_sigmaFixed`) and evaluates at every differential point
   (`differentialPolynomialEvalOver_eq_zero_of_point`).
2. A **linear** differential relation on the Galois matrices ⟹ isomonodromy over the base
   (`isomonodromy_of_no_riccati_of_linearRelation`), unconditionally.

The gap between them is exactly linearity, and the card's own counterexample shows it is real: for
`Z = {x : δ(δx/x) = 0}` the group `{diag(a,a⁻¹)} ∪ {antidiag(b,-b⁻¹)}` has all entries in a proper
differential algebraic set, spans `M₂`, and yet its scalar stabiliser contains the unbounded family
`a + a⁻¹`.  A *linear* operator has a solution set that is a subspace over the differential
constants, which is what makes the span of the group inherit the relation.

**Remaining obligation of the card, in one sentence:** the Galois matrices of a Zariski-dense
differential algebraic subgroup of `SL₂` with a proper defining ideal satisfy one nonzero *linear*
differential operator over the constants.  Classically this is the tangent-space linearisation
(the Lie algebra of a differential algebraic group is cut out by the linearisations of the defining
differential polynomials), so the layer it needs is the Hopf/group-scheme structure of the
parameterized Galois group — which the corpus deliberately avoids today
(`galoisMonoid` is the *submonoid closure* of the set of Galois matrices, not a group).

A second, equivalent reformulation found while proving the above, worth recording:
from `(Y ⊗ 1) Z = (1 ⊗ Y)` and `δY = B Y` one gets
`δZ · Z⁻¹ = (Y ⊗ 1)⁻¹ ((1 ⊗ B) − (B ⊗ 1)) (Y ⊗ 1)`,
so **`δZ = 0` if and only if `B = ℓδ Y` has entries in the base** — the whole endgame is the single
statement that the comparison matrix becomes differentially constant after one conjugation.

## 2026-08-21 — CARD PROMOTED: `irrational-triptic-source-effectivity-character` → stage 3

Its two Lean gates are closed.

* *global analytic-subring packaging of the source boundary* — already in the tree and wired:
  `EllipticGammaThetaBoundaryAnalytic` (`ellipticGammaThetaBoundaryAnalytic(Tau)`, `…Mero(Tau)`,
  `ellipticGammaMero_add_sigma`, `_add_tau`, `_add_one`).  The card's own audit had recorded this;
  the checkbox was stale.
* *FHRZ/differential-character comparison* — new module
  `GaloisForLFunctions.HTGeometry.TripticGerbeDifferentialCharacter` (wired, built, axiom-clean).

The new module computes the flat-character group of the triptic quotient and proves the comparison:

```text
cocycleCommutator, cocycleCommutator_add_left, cocycleCommutator_eq_zero_of_basis
IsSymmNormalCocycle, CocycleExt (+ Add/Zero/Neg/AddCommGroup), split, base_split
exists_coboundary₁_of_symm_cocycle      a symmetric 2-cocycle on ℤ³ is a coboundary
exists_coboundary₁_iff_basis            H²(ℤ³, M) is detected by the three basis commutators
twistedCoboundary₁/₂, exists_twistedCoboundary₁_of_flat_of_basis
eq_add_twistedCoboundary₁_of_curvature_of_flat_of_holonomy   **the comparison**
eq_add_twistedCoboundary₁_of_gammaGerbeDD                    the same with curvature = gammaGerbeDD
```

Mechanism: the commutator pairing `B(a,b) = c a b − c b a` of a 2-cocycle is bi-additive (it is the
commutator of the central extension), hence determined by the three basis pairs; when it vanishes
the cocycle is symmetric, the extension is abelian, and the lattice being free the extension splits,
so the cocycle is a coboundary.  On invariant (flat) coefficients the twisted complex is the
untwisted one, which transports the statement to a gerbe cochain with the translation action.

The card's remaining unchecked gate, *independent specialist proof and novelty audit*, is a
3 → 4 item in this pipeline's vocabulary, not a formalization gate.

**Five cards remain** in `2-fully-proven/new_scientific_knowledge/other`:
`bessel-order-intensity-hypertranscendence`, `differential-variational-building-balance-law`,
`isogeny-tail-maurer-cartan-holography`,
`torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness`,
`universal-first-order-entire-cascade-unit-cost`.

## 2026-08-21 — Bessel card: the linearisation layer (new module)

`GaloisForLFunctions.HTGeometry.DifferentialTangentLinearization` (wired, built, axiom-clean):
the dual numbers as a differential ring, the linearisation formula
`F(p + εX) = F(p) + ε ∑_v (∂_v F)(p) δ^{v.2} X_{v.1}`, its scalar operator form, and
`exists_nonzero_linear_relation_of_tangent` — a set of tangent directions lies in the solution set
of one nonzero scalar linear differential operator, which is exactly the hypothesis of
`isomonodromy_of_no_riccati_of_linearRelation`.

This is the mechanism half of the linearity gap.  Remaining on this card: the geometry half —
Cassidy's structure theorem for Zariski-dense differential algebraic subgroups of `SL₂` (the Galois
matrices are controlled by the tangent space of the Kolchin closure at the identity), plus the
exclusion of the imprimitive case via the symmetric square.

Corpus assets found while doing this and worth reusing: the tree already owns a substantial
differential-Hopf layer — `DifferentialHopfIdeal`, `DifferentialHopfPrimitive`
(`nonzero_additiveHopfIdeal_exists_finite_jet_linear_relation`), `AdditivePolynomialHopfIdeal`,
`SymmetricHopfIdealLinear`, `GroupAlgebraHopfIdealClassification`, `HopfIdealKernel`,
`AffineExponentialGroupHopf`, `KolchinAdditiveClosure`, `DifferentialKolchinClosure` —
so the additive half of Cassidy is already available in Hopf-ideal form.

## 2026-08-21 — `torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness`: analysis of the last item

The card's sole remaining obligation is Abe's Proposition 8.2, stated in Lean as
`QuasiAbelianDampedLiftConstruction.HasAbeDampingFamily`.  Two findings from working on it:

1. **The `majorant` field is satisfiable with `C = 0`.**  Its content is a bound on the *packet
   jets* of the complement Poincaré terms, so a seed vanishing to order `m_i + 1` at every
   translated packet point `w_i + comp z` (`z ≠ 0`) satisfies it exactly, with no `B` dependence.
   The `B`-family then collapses, and the whole obligation becomes: lower-automorphic seeds with the
   prescribed packet jets, vanishing at the translated packet points, whose Poincaré series still
   converges locally uniformly.  A finite version of this — vanishing only for `0 < |z| ≤ Z(B)` with
   `Z(B) ~ √(δB/σ)` and the Gaussian tail supplying `e^{-δB}` beyond — is a *finite* interpolation
   problem, i.e. exactly the induction hypothesis (jet ampleness of the lower factor at a finite
   packet), provided the interpolant's norm grows at most polynomially in `B`.
2. **The multiplier route as literally described cannot work.**  A `ΓH`-invariant entire multiplier
   is a holomorphic function on `ℂ^d/ΓH`; when that quotient is a toroidal group it is constant, and
   in the remaining cases the only nonconstant candidates are characters `exp(λ(x))` with
   `λ(ΓH) ⊆ 2πiℤ`, whose modulus is `exp(B Re λ(x))` — linear in the complement index, hence
   *positive* on half the complement lattice.  Since the automorphy factor contributes only a
   Gaussian `exp(-σ|z|²)`, and for fixed `z` with `Re λ(comp z) > 0` the product grows like
   `e^{cB}` while the required bound decays like `e^{-δB}`, no character can damp a full complement
   lattice.  So the damping in Abe's proof is not a `ΓH`-invariant multiplier on the seed, and the
   route to the Lean interface has to go through the vanishing-order form in (1) or through a
   restatement of the interface.

## 2026-08-21 — `differential-variational-building-balance-law`: `(2)` is now Lean

New module `GaloisForLFunctions.HTGeometry.KaehlerConnection` (wired, built, axiom-clean):
the canonical connection `∇(a db) = δ(a) db + a d(δb)` on `Ω[K⁄C]`, built from the universal
property via the twisted first-jet module `KaehlerJet`, together with the resulting module
structure over the Ore ring `DiffOp K = K[∂;δ]` (`kaehlerDiffOpModule`).

Chain: `kaehlerJetDerivation` (a genuine `C`-derivation into the twisted module) →
`kaehlerLift` → `base_kaehlerLift` (it is a section) → `kaehlerConnection` with
`kaehlerConnection_D` and `kaehlerConnection_smul` → `diffOpSMul_dpartial` → `diffOpSMul_mul` →
`kaehlerDiffOpModule`.

Remaining on that card: `M_K = Ω/Tor` free over `R_K` with rank = differential transcendence
degree; the semilinear action `T_σ ∈ GL_r(R_K)`; the identification of `μ_n` with the Cartan
prefix invariants of `OperatorCartanComparison`; and the building dichotomy.

## 2026-08-21 — `bessel-order-intensity-hypertranscendence`: item (a) reduced

The imprimitivity system `(E) σe = e/p + 2b`, `(P) p σp = 1 + be + b²p` implies the **discriminant
identity** `σΔ · p² = Δ` for `Δ = e² − 4p` (and conversely `(E) ∧ (D) ⟹ (P)`).  Since the shift
preserves both the degree at infinity and the leading coefficient, this forces `intDegree p = 0`
and `ℓ(p)² = 1`; feeding that back into `(E)` and `(P)` pins the branch to
`ℓ(p) = −1`, `intDegree e = 1`, `ℓ(e) = c`, and kills `ℓ(p) = +1` outright.  `Δ ≠ 0` because
`Δ = 0` gives a rational Riccati solution, which `BesselOrderRiccati` refutes.
The surviving branch has a formal solution at infinity (the asymptotic expansions of the two Bessel
ratios), so it cannot be closed by any further degree count at infinity; the remaining argument has
to be global, of the denominator type used in `orderBesselRiccatiPolynomial_no_solution`.

## 2026-08-21 — `differential-variational-building-balance-law`: `(7)`–`(10)` basis-free

New module `GaloisForLFunctions.HTGeometry.KaehlerSemilinearAction` (wired, built, axiom-clean):
`TwistedKaehler`, `twistedKaehlerDerivation`, `kaehlerSemilinear` with `_D`, `_smul`,
`symm_fixes`, `kaehlerSemilinear_symm_kaehlerSemilinear` (it is an automorphism) and
`kaehlerSemilinear_kaehlerConnection` (it commutes with the connection).

With `KaehlerConnection` this gives the card's `(2)` and the basis-free half of `(7)`–`(10)`.
The remaining links on that card are: `M_K = Ω/Tor` free over `R_K` of rank = differential
transcendence degree (`(4)`), which converts `σ_*` into a matrix in `GL_r(R_K)`; the identification
of `μ_n` with the Cartan prefix invariants of `OperatorCartanComparison`; and the building
dichotomy of Theorem B.

## 2026-08-21 — `differential-variational-building-balance-law`: freeness over `K[∂;δ]`

New module `GaloisForLFunctions.HTGeometry.DifferentialOperatorSubmoduleFree` (wired, built,
axiom-clean): `exists_basis_card_le`, `exists_basis_of_submodule`, `free_submodule` — every
submodule of `K[∂;δ]^ι` with `ι` finite is free of rank at most `card ι`.  This upgrades the
corpus's existing generation statement (`DifferentialOperatorSubmoduleSplitting.
exists_generators_card_le`) to a basis, using that the previous stage lies in the kernel of the
coordinate projection while the new generator does not.

`KaehlerConnection` gained `kaehlerConnection_unique`, which identifies it with the corpus's
pre-existing `HypertranscendentalKaehlerClockSymbol.kaehlerConnectionDifferential` (found on a later
search; the new construction is kept because it is import-light and is what the operator-ring module
structure needs).

Card `(4)` now needs only: `M_K = Ω/Tor` embeds into a finite free module (clearing denominators in
`Q_K ⊗ M_K`, on top of `OperatorLattice`), and `rank M_K = differential-trdeg_C K`.

## 2026-08-21 — `differential-variational-building-balance-law`: the structure theorem

New module `GaloisForLFunctions.HTGeometry.DifferentialOperatorTorsionFreeQuotient` (wired, built,
axiom-clean): `rowSpanR` and its behaviour under elementary operations, `exists_equiv_of_rowColEquiv`,
`isUnit_of_torsionFree_quotient`, `rowSpanR_eq_coordSupport`, `free_quotient_coordSupport`, and
**`free_of_torsionFree_quotient`** — a torsion-free quotient of `K[∂;δ]^κ` is free.

With `DifferentialOperatorSubmoduleFree` this closes the module theory behind `(3)`–`(4)`:
`Ω[K⁄C]` is an `R_K`-module (`kaehlerDiffOpModule`), a quotient of a finite free module when `K/C`
is finitely differentially generated, and `M_K = Ω/Tor` is torsion-free, hence free.

Card 4's remaining items: (i) the rank identity `rank M_K = differential-trdeg` — not needed for the
balance law itself, only for the card's `(4)` as stated; (ii) reading `σ_*` off in a basis as a
matrix in `GL_r(R_K)`; (iii) the building dichotomy of Theorem B.

## 2026-08-21 — `differential-variational-building-balance-law`: `(7)`–`(10)` complete

New module `GaloisForLFunctions.HTGeometry.DifferentialOperatorSemilinearMatrix` (wired, built,
axiom-clean): `map_dpartial`, `map_mul'`, `mapRingHom`, **`mapRingEquiv`** (a differential
automorphism of the coefficients acts on `K[∂;δ]`), and **`isUnit_matrix_of_semilinear_equiv`** (a
`σ`-semilinear automorphism of a finite free module has an invertible matrix, `A · σ(A') = 1 =
σ(A') · A`).

With `KaehlerConnection`, `KaehlerSemilinearAction`, `DifferentialOperatorSubmoduleFree` and
`DifferentialOperatorTorsionFreeQuotient`, the card's `(2)`, `(3)`, the freeness half of `(4)` and
all of `(7)`–`(10)` are now Lean.  Remaining: the rank identity `rank M_K = differential-trdeg`, and
the building dichotomy of Theorem B.

## 2026-08-21 — `differential-variational-building-balance-law`: `(3)` finite generation

New module `GaloisForLFunctions.HTGeometry.KaehlerDifferentialGeneration` (wired, built,
axiom-clean): `kaehlerMembershipField`, **`eq_top_of_connection_stable`**, `connectionOrbit`,
**`span_connectionOrbit_eq_top`**.  A `K`-submodule of `Ω[K⁄C]` stable under the connection and
containing the differentials of a differential generating set is everything; hence `Ω[K⁄C]` is
generated over `K[∂;δ]` by the differentials of any differential generating set.

Card 4 now has `(2)`, `(3)`, `(7)`–`(10)` and the freeness half of `(4)` in Lean.  Remaining: the
rank identity `rank M_K = differential-trdeg`, and the building dichotomy of Theorem B (Bruhat–Tits
semisimplicity — the deepest remaining item on this card; the transcript records that a degree
argument at infinity cannot replace it, since over the skew field `K((∂⁻¹))` there is no eigenvalue
theory to make the subadditive sequence `μ(A^n)` eventually exactly linear).

## 2026-08-21 — `differential-variational-building-balance-law`: `(4)` freeness assembled

New module `GaloisForLFunctions.HTGeometry.KaehlerModuleFree` (wired, built, axiom-clean):
`span_diffOp_D_eq_top` and **`free_quotient_kaehler_of_torsionFree`** — for a finitely
differentially generated `K/C`, every torsion-free quotient of `Ω[K⁄C]` (in particular
`M_K = Ω/Tor`) is a *free* `K[∂;δ]`-module.  `KaehlerConnection` gained the `IsConstantBase` class,
the `Module (DiffOp K) Ω[K⁄C]` and `IsScalarTower K (DiffOp K) Ω[K⁄C]` instances, and
`partial_smul_eq_connection`; `DifferentialOperatorTorsionFreeQuotient` gained
`free_of_torsionFree_of_fg`.

Card 4 now has `(2)`, `(3)`, the freeness of `(4)`, and `(7)`–`(10)` in Lean.  Two items remain:
the rank identity `r = differential-trdeg`, and the building dichotomy (semisimplicity), for which
the transcript records why the nonarchimedean Jordan argument cannot be transplanted to the skew
field `K((∂⁻¹))` and that the remaining route is the CAT(0) geometry of the discrete affine
building.

## 2026-08-21 — `differential-variational-building-balance-law`: the rank identity

New module `GaloisForLFunctions.HTGeometry.KaehlerDifferentialIndependence` (wired, built,
axiom-clean): `kaehlerConnection_iterate_D`,
**`linearIndependent_diffOp_D_of_differentialIndependent`** (differentially independent elements
have `K[∂;δ]`-independent differentials, via
`algebraicIndependent_iff_kaehlerD_linearIndependent`), and `linearIndependent_mkQ_of_torsion`.
`KaehlerConnection` gained `diffOpSMul_eq_sum`.

Together with `span_diffOp_D_eq_top` this gives both halves of `(4)`.  **The only remaining item on
card 4 is the building dichotomy of Theorem B.**

## 2026-08-21 — `torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness`: first Lean

New module `GaloisForLFunctions.HTGeometry.QuasiAbelianVanishingDampingFamily` (wired, built,
axiom-clean): `abeDampingMajorant_of_jet_vanishing` and `AbeDampingPacketData.ofVanishing`.
The `majorant` field of `AbeDampingPacketData` constrains only the *packet jets* of the complement
Poincaré terms, so it holds with constant `0` as soon as those jets vanish.  The card's remaining
obligation is therefore an interpolation-with-vanishing problem, not a damping-multiplier problem —
and the transcript records the proof that the multiplier route is impossible (an invariant entire
multiplier on the toroidal quotient is constant, and a character's modulus is linear in the
complement index, hence positive on half the lattice).

## 2026-08-21 — two further assemblies

* `DifferentialConstantRelationDescent.exists_constantCoeff_relation_eval` (Bessel card, step 1 of
  the split, in one statement).
* Card 4's dichotomy reduced, in the card, to a precise statement about twisted products
  `A_n = A σ(A) ⋯ σ^{n-1}(A)` in `GL_r(K[∂;δ])` measured against `O^r`, `O = K[[∂^{-1}]]`, with the
  three elementary facts `μ_n = 0 ⟺ A_n ∈ GL_r(K)`, `∑ μ_i(n) = 0`, and subadditivity, and the two
  remaining routes named (CAT(0) geometry of the lattice complex — a tree when `r = 2`, where
  Serre's dichotomy is elementary — or a formal slope classification of difference modules over
  `K((∂⁻¹))`).  The associated graded of the valuation filtration is the *commutative*
  `K[ξ,ξ⁻¹]`, so the obstruction is degree cancellation in the twisted product, not
  noncommutativity.

## 2026-08-21 — `isogeny-tail-maurer-cartan-holography`: first Lean

New module `GaloisForLFunctions.HTGeometry.FixedFieldDegreeCriterion` (wired, built, axiom-clean):
**`eq_fixedPoints_subfield_of_finrank`** — a subfield inside the fixed field of a finite faithful
action, over which the whole field already has degree the order of the group, *is* the fixed field
(Artin's degree computation plus the tower).

This is the field-theoretic half of the card's `(1)`, `α^{n*}K = K^{Γ_n}`.  The remaining input for
`(1)` is a single geometric statement: `[K : α^{n*}K] = deg(α^n) = |Γ_n|` at the level of the jet
function field.  `(2)` and `(3)` are already Lean.

## 2026-08-21 — card 4 dichotomy: the first structural step is Lean

New module `GaloisForLFunctions.HTGeometry.DifferentialOperatorTopCoefficientMatrix` (wired, built,
axiom-clean): `coeff_mul_of_degree_le`, `topCoeffMatrix`, **`topCoeffMatrix_mul`** (the leading
matrix is multiplicative) and **`not_isUnit_topCoeffMatrix`** (a matrix invertible over `K[∂;δ]`
with an entry of positive degree has a singular leading matrix).

Recorded in the card: `μ₁(n) = deg(Aₙ)` and `−μ_r(n) = deg(Aₙ⁻¹)` exactly, so the dichotomy is
*"sublinear degree growth of a twisted product implies bounded"*, and the degree can drop only along
the kernel of the leading matrix — the entry point of the slope filtration.

## 2026-08-21 — card 4 dichotomy: the degree-zero case is closed

New module `GaloisForLFunctions.HTGeometry.DifferentialOperatorConstantMatrix` (wired, built,
axiom-clean): `CRingHom`, `CRingHom_injective`, **`isUnit_det_of_map_C_mul_eq_one`** (a constant
matrix invertible over the operator ring is invertible over the field — so `deg A = 0` forces
`A ∈ GL_r(K)`, hence `μ_n = 0` for all `n`), and
**`exists_degree_eq_of_topCoeffMatrix_mul_ne_zero`** (degrees are exactly additive when the leading
matrices do not annihilate).

Card 4's dichotomy now has: the degree-zero case closed, exact additivity off the kernel of the
leading matrix, and singularity of that leading matrix whenever the degree is positive.  The
remaining work is the induction on the kernel filtration.

## 2026-08-21 — card 4 dichotomy: the generic branch is Lean

New module `GaloisForLFunctions.HTGeometry.DifferentialOperatorChainDegree` (wired, built,
axiom-clean): `chainProd`, `chainProdK`, `degree_matrix_mul_le`,
**`topCoeffMatrix_chainProd`** (the leading matrix of an ordered product is the ordered product of
the leading matrices, with the degree bound `∑ eₖ`) and **`exists_degree_chainProd_eq`** (the bound
is attained exactly when that product is nonzero).

The dichotomy is now reduced to one sequence of matrices over the coefficient field — the
accumulated leading matrices.  While it is nonzero the degree is exactly `∑ eₖ`; a drop happens
exactly when it is annihilated; and the all-degrees-zero case is already closed.  What remains is
the induction on the kernel filtration.

## 2026-08-21 — card 4 dichotomy: both branches are now arithmetic

New module `GaloisForLFunctions.HTGeometry.SubadditiveDegreeDichotomy` (wired, built, axiom-clean):
`le_mul_of_subadditive`, `eq_zero_of_mul_of_eq_zero`,
**`le_sup_of_subadditive_of_eq_zero`** (bounded branch) and
**`mul_le_of_subadditive_of_exact`** (linear branch, `n·d N ≤ N·(d n + N·d 1)`).

The dichotomy of Theorem B now follows from one remaining input: the existence of an `N ≥ 1` whose
`N`-step chain has non-vanishing accumulated leading matrices (equivalently, `deg` exactly additive
along multiples of `N`).  Given that `N`, both phases are proved — `deg A_N = 0` gives
`A_N ∈ GL_r(K)` and a bounded orbit; `deg A_N > 0` gives `λ = deg A_N / N > 0`.  The open point is
the termination of the kernel filtration, where the rank bound enters.

## 2026-08-21 — card 4: the generic branch closed in the card's own form

`DiffOp.matDeg_chainProd_eq` (in `DifferentialOperatorChainDegree`): for a chain of factors of
degree at most `e` whose accumulated leading matrices never vanish, the matrix degree of the
`n`-fold product is exactly `n·e`.  With `SubadditiveDegreeDichotomy` this gives the full dichotomy
under the single hypothesis "the accumulated leading matrices never vanish".

Recorded: `P_{n+1} = C₀·σ(P_n)`, so `rank P_n` is non-increasing and the accumulated leading
matrices either never vanish or vanish from some index on.  The remaining gap is the bound on the
number of restarts after a vanishing (the rank bound, from splitting off a sub-object at each drop).

## 2026-08-21 — card 4: the leading-chain dichotomy is Lean

`chainProdK_eq_zero_of_le`, `rank_chainProdK_antitone`, **`chainProdK_dichotomy`** added to
`DifferentialOperatorChainDegree`: the accumulated leading matrices either never vanish or vanish
from some index on.  In the first regime the dichotomy of Theorem B is proved.  The card's single
open point is now: after a vanishing, the restarted chain reaches the non-vanishing regime after
finitely many restarts (classically the rank bound `r`).

## 2026-08-21 — consolidated state of the six `other` cards, with the next brick for each

**Promoted this session:** `irrational-triptic-source-effectivity-character` → stage 3.

**`differential-variational-building-balance-law`** — Lean: `(2)` the canonical connection and the
`K[∂;δ]`-module structure; `(3)` finite generation; `(4)` freeness *and* both halves of the rank
identity; `(7)`–`(10)` the semilinear action and its invertible matrix; the balance law; and for
Theorem B: `μ₁(n) = deg Aₙ`, multiplicativity of the leading matrix, singularity of the leading
matrix in positive degree, exact degree growth of a chain with non-vanishing leading products, the
regime dichotomy for the leading chain, and both arithmetic branches of the phase dichotomy.
*Next brick:* the rank bound on the number of restarts — split off a proper sub-object at each
vanishing of the accumulated leading matrix, i.e. the slope filtration of the `σ`-module.

**`bessel-order-intensity-hypertranscendence`** — Lean: the isomonodromy endgame from a *linear*
differential relation; the `σ`-descent of a differential relation to the constants and its
evaluation at every differential point; the dual-number linearisation with the tangent-space linear
relation.  *Next brick:* the linearity itself — Cassidy's structure theorem for Zariski-dense
differential algebraic subgroups of `SL₂`, plus the exclusion of the imprimitive case (the explicit
symmetric-square system is written in the card, with `ℓ(p) = +1` already excluded).

**`torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness`** — Lean: the damping majorant from
exact vanishing, and the packet datum built from it.  Recorded: the multiplier route is impossible.
*Next brick:* the finite version — vanishing for `0 < |z| ≤ Z(B) ≍ √(δB/σ)` plus the Gaussian tail,
with the interpolant's majorant constant polynomial in `B`.

**`isogeny-tail-maurer-cartan-holography`** — Lean: the fixed-field degree criterion, the
field-theoretic half of `(1)`.  *Next brick:* `[K : α^{n*}K] = deg αⁿ` on the jet function field.

**`universal-first-order-entire-cascade-unit-cost`** — the whole Wiman–Valiron layer, the Bell
reductions and the cascade induction are already in the tree.  *Next brick:* `helim` for an algebraic
derivative law; the bridge "nonzero output-jet Jacobian ⟹ `helim`" appears not to exist yet and is
formalizable on its own, leaving the Wiman nested initial law as the analytic input.

## Stretch — algebraic generators and the restart algebra

Three new modules, all wired into `GaloisForLFunctions.HTGeometry`, all `lake build`-green and
axiom-clean (`[propext, Classical.choice, Quot.sound]`).

`HTGeometry.DifferentialAlgebraicAdjoin` — **an algebraic element carries no new jets**.
`derivPart`, `deriv_mem_adjoin_of_isAlgebraic`, `derivationClosed_adjoin_of_isAlgebraic`,
`differentialAdjoin_singleton_eq_adjoin`, `finrank_differentialAdjoin_singleton`,
`finrank_eq_of_differentialAdjoin_singleton_eq_top`,
`finiteDimensional_of_differentialAdjoin_singleton_eq_top`, `subfieldDifferential`,
`subfield_differentialAlgebra`, `derivationClosed_differentialAlgebra`.
Mechanism: implicit differentiation of the minimal equation via the corpus's `deriv_eval`
(total derivative of a polynomial value), plus the observation that the elements whose derivative
stays inside a field form an intermediate field.

`HTGeometry.DeckFixedFieldSimpleGenerator` — **one generator identifies the invariants**.
`eq_fixedPoints_of_adjoin_simple_eq_top`, `eq_fixedPoints_of_differentialAdjoin_eq_top`
(`MulSemiringAction` form); `finrank_le_of_differentialAdjoin_eq_top`,
`finiteDimensional_of_differentialAdjoin_eq_top`, `eq_fixedField_of_differentialAdjoin_eq_top`,
`adjoin_differentialJetSet_eq_top_of_base`, `eq_fixedField_of_algebraic_generator`
(automorphism-subgroup form, composing with the pre-existing
`DeckDegreeUpperBound.eq_fixedField_of_finrank_le`).

Effect on **card 6** (`isogeny-tail-maurer-cartan-holography`): item `(1)`,
`alpha^{n*}K = K^{Gamma_n}`, is now proved from four inputs, three of them formal for an isogeny
pullback; the only geometric one is that the generic point is algebraic over the pullback of degree
at most `|Gamma_n|` — an *order-zero* statement.  The jet/prolongation layer that the card's Lean
status listed as item 1 is no longer needed for `(1)` at all.  Items 2–5 (quotient sheaf/atlas for
`G/H`, the DCF generic-point bridge for the logarithmic derivative, the reduced presentation, the
finite-action quotient) still gate the card.

`HTGeometry.TwistedMatrixChain` — **the restart recursion, as an identity**.
`iterHom`, `iterHom_add`, `iterHom_iterHom`, `twistedFamily`, `twistedChain`, `twistedChain_left`
(`P_{n+1} = C σ(P_n)`), `twistedChain_add` (`P_{m+n} = P_m σ^m(P_n)`), `twistedChain_restart`
(`P_{kN}` is the `k`-th term of the twisted chain of `P_N` with twist `σ^N`),
`twistedChain_eq_zero_restart_iff`, and the two bridges to `DiffOp.chainProdK` / `DiffOp.chainProd`.
Stated for an arbitrary ring and endomorphism, so it serves both the coefficient and the operator
chain.

Effect on **card 4** (`differential-variational-building-balance-law`): the last open point was
stated as a claim about restarts; that claim is now the identity `twistedChain_restart`.  What is
left is *termination* of the restart recursion, which needs the lattice-level slope filtration
(CAT(0) semisimplicity of the affine building, or Dieudonné–Manin for `σ`-modules over `Qhat_K`) —
and explicitly **not** a statement about the accumulated leading matrices, which at a restart are
generated by `P_N = 0` while the restarted leading matrix lives at the new lower degree.

Next bricks, unchanged for the other three cards: card 3 Cassidy for Zariski-dense δ-subgroups of
`SL₂` plus the imprimitive exclusion; card 7 the finite interpolation-with-vanishing; card 8 the
Wiman nested initial law (the algebraic Jacobian bridge it needed already exists in the corpus —
`JacobianAlgebraicIndependence`, `JacobianDomainCriterion`, `ArithmeticFunctionJacobianCriterion` —
and `CascadeExactOrderUnconditional` already reduces the card to that single analytic input).

## Stretch — the value at a place (card 8, item 3a)

`HTGeometry.PlaceLimit` (wired, built, axiom-clean).  The peel's value-at-infinity layer,
reproduced at a place of an algebraic extension: `PlaceLim`, its algebra (`add`, `neg`, `sub`,
`mul`, `placeLim_sum`, `placeLim_prod`), `placeLim_det`, and uniqueness against a trivially valued
subfield (`PlaceTrivialOn`, `eq_zero_of_mem_of_placeDegLE_lt`, `placeLim_unique`).  Plus the
transport theorem the card's own frontier note asked for: `one_le_valuation_of_isIntegral` and
`placeFree_of_isIntegral` — **a place trivial on a subfield is trivial on every element algebraic
over it**, proved from the strict-maximum principle on the minimal equation (constant term a unit,
every other term strictly small).

So card 8's item 3a now has all three of its supporting layers — grading (`PlaceGrading`),
derivation drop (`PlaceDerivationValuationDrop`, `AlgebraicCascadeDifferentDrop`), and limits
(`PlaceLimit`).  What remains of 3a is transcribing the border-shape and peel-step inductions from
`(TopDegLE, TopFree, TopLim)` to `(PlaceDegLE, PlaceFree, PlaceLim)` — 36 files currently mention
the coordinate triple.  Item 3b (Reduction I: Goldberg + Strelitz, the analytic branch selection)
is untouched.

## Stretch — card 7's obligation reduced to finite interpolation

`HTGeometry.MultivariateEntireJetVanishingProduct` and
`HTGeometry.QuasiAbelianFiniteVanishingDamping` (both wired, built, axiom-clean).

The first proves that vanishing jets survive multiplication (Leibniz induction) and translation,
hence `allJetsVanish_poincareTermEntire`: a Poincaré summand `ψ(γ,·)⁻¹·G(·+γ)` inherits the
vanishing of `G` at `p + γ`.  So the damping interface's `hvanish` is a condition on the *seed's*
jets at the translated packet points — the automorphy factor cannot resurrect a jet.

The second replaces vanishing at *every* nonzero complement translate by vanishing on a disc of
squared radius `Z B`, with the Gaussian tail supplying `exp(−δB)` outside as soon as
`δ·B ≤ (σ₀−σ₁)·Z B`, and a polynomial-in-`B` bound on the seed.

Card 7's analytic obligation is therefore now a finite interpolation statement — prescribed jets at
the packet, zero jets at finitely many translates — which is jet ampleness of the lower factor at
the enlarged packet, i.e. the card's own induction hypothesis, plus a growth bound.  The remaining
structural input is that the enlarged packet is pairwise distinct modulo `ΓH`.

## Stretch — card 3 item (a): the imprimitive branch, proved on paper and half in Lean

**New mathematics.**  The card had item (a) pinned to `ν(p) = 0`, `ℓ(p) = −1`, `ν(e) = 1`,
`ℓ(e) = c` and recorded that no further degree count at infinity could close it.  It is now closed
on paper by a *global* argument: the discriminant identity `σΔ·p² = Δ` forces every order of `Δ` to
be even along each integer orbit (descend from where `Δ` has no zeros or poles), hence `Δ` is a
square, hence the two Riccati ratios `r₁, r₂ = (e ± k)/2` are rational; the pair `{σr₁, σr₂}` equals
`{b + 1/r₁, b + 1/r₂}` because the two monic quadratics agree; the swap assignment is excluded
because `1/r₂` cancels the leading term of `b` while the shift preserves the degree at infinity; and
the identity assignment makes `r₁` a rational solution of the Bessel order Riccati equation, which
the corpus already refutes.

**Lean.**  `HTGeometry.RatFuncOrderSquare` (`ratOrd`, `ratOrd_of_rep`, `ratOrd_mul`,
`exists_sq_of_even_rootMultiplicity`, `isSquare_of_even_ratOrd`) and
`HTGeometry.RatFuncShiftSquareOrbit` (`rootMultiplicity_comp_X_add_one`, `ratOrd_ratShift`,
`finite_ratOrd_support`, `even_ratOrd_of_ratShift_mul_sq`, `isSquare_of_ratShift_mul_sq`) prove the
global step in full generality: over any characteristic-zero field, `σf·g² = f` makes the order of
`f` even everywhere, and over an algebraically closed one it makes `f` a square.  Also new:
`HTGeometry.QuasiAbelianEnlargedPacket` (`enlargedPacketPoints`,
`pairwiseDistinctModulo_enlargedPacketPoints`, `PairwiseDistinctModulo.comp`) closes the structural
input card 7's finite version needed — the enlarged packet is a packet for the lower lattice
precisely because the base points are distinct modulo the full lattice.

## Card 3 item (a): CLOSED, in Lean

`HTGeometry.BesselOrderImprimitivity.no_imprimitive_pair` — **no `e, p ∈ ℂ(X)` with `p ≠ 0` satisfy
`σe = e/p + 2b` and `p·σp = 1 + be + b²p`** for `b = c(X+1)`, `c ≠ 0`.  Unconditional, axiom-clean,
wired.  Supporting: `intDegree_add_eq_of_lt` (strict ultrametric equality for the degree at
infinity) and `ratShift_eq_fieldShiftRatShift`.

So the imprimitive branch of the Bessel order Galois classification is eliminated in Lean, and item
(a) of the card is finished.  The card's remaining open core is item (b) — the linearity of the
differential relation — which is unchanged.

## Card 3 item (b): the unipotent route is Lean, down to one nonvanishing

`HTGeometry.UnipotentParameterSubgroup` (wired, built, axiom-clean): `unipotentParams` (the
parameters of the upper unipotents in a matrix group form an additive subgroup),
`unipotentSubstHom` / `evalOver_unipotentSubst` (substituting `u(X)` into a differential polynomial
in the four entries computes its value at the unipotent — the entries `1`, `0` are differential
constants), and `exists_nonzero_linear_jet_relation_of_unipotentParams`, which delivers exactly the
nonzero **linear** differential relation that `isomonodromy_of_no_riccati_of_linearRelation`
consumes.

Its only hypothesis is `unipotentSubst P ≠ 0` — the defining differential polynomial of the group
does not vanish identically along the unipotent line.  That is the residue of the card's item (2),
in a sharper form than "the group contains a unipotent".

## Card 3 item (b): the tangent space is a constants-module

`HTGeometry.DifferentialTangentSubmodule` (wired, built, axiom-clean): `differentialJet_const_mul`
(jets are linear over the differential constants), `linearisationForm` with additivity and
constant-homogeneity, and `tangentSpace p F s : Submodule (differentialConstants C) (ι → C)` with
`mem_tangentSpace_iff_snd_eq_zero` identifying it with the vanishing locus of the `ε`-part at the
dual point.

This supplies, for free and with no group hypothesis, the `C`-submodule structure that
`cassidy_sl2` asks of its input `L`.  The residue of item (b) is now bracket-closure of the tangent
space, the line-stabiliser condition, and the Zariski-density transfer.

## Card 3 item (b): `Ad`-stability of the tangent space

`HTGeometry.DifferentialTangentAdjoint` (wired, built, axiom-clean): `dualMatrix` with the
first-order product rule `(p + εX)(q + εY) = pq + ε(pY + Xq)`, `evalOver_inl` (the base embeds
through the differential evaluation, because `inl` commutes with every jet), `matrixZeroSet`, and
`adjoint_mem_tangent_of_zeroSet` — **the adjoint action preserves the tangent directions at the
identity** whenever the dual-number zero set is closed under multiplication.

Next step on item (b): differentiate `Ad` along `g = 1 + ηX` over `DualNumber C` to get the
bracket; then the line-stabiliser condition and the Zariski-density transfer, which are the other
two hypotheses of `cassidy_sl2`.

## Card 3 item (b): the layer-transfer lemma

`HTGeometry.DifferentialEvalTransfer` (wired, built, axiom-clean): `differentialJet_algHom`,
`evalOver_algHom` (**the differential evaluation commutes with any differential algebra map**),
`matrixZeroSet_algHom`, and `evalOver_inl'` recovered from it.

This is the general form of the hand-proved `evalOver_inl` of the adjoint module, and it is what the
three-layer bracket argument needs: each move between `C`, `DualNumber C` and
`DualNumber (DualNumber C)` is a differential algebra map, so the zero set transfers along it.

## Card 3 item (b): ring-map transfer landed; iterated dual numbers ruled out

`HTGeometry.DifferentialEvalTransfer` now also carries `evalOver_ringHom` and
`matrixZeroSet_ringHom` — the transfer for a plain ring map that is compatible with the derivation
and with the constants, which needs no algebra structure of the target over the source.

**Finding (dead route).**  The bracket cannot be obtained over `DualNumber (DualNumber C)`:
`Differential.deriv` is inapplicable to elements of that type because its `Derivation ℤ R R` is
built over `CommRing.toCommSemiring` while the elaborator resolves the `CommSemiring` of
`TrivSqZeroExt (DualNumber C) (DualNumber C)` through `TrivSqZeroExt.commSemiring` — an instance
diamond that no form of the application escapes.  Next brick: a direct four-dimensional model of
`C[ε, η]/(ε², η²)` with explicit `CommRing` and `Differential` instances; the rest of the bracket
argument is unchanged and already reduced to `dualMatrix_mul` plus two transfers.

## Card 3 item (b): the two-infinitesimal ring, built

`HTGeometry.BiDualNumbers` (wired, built, axiom-clean): `BiDual C` = `C[ε, η]/(ε², η²)` by four
coefficients, with `CommRing`, `Algebra C`, `Differential` and `DifferentialAlgebra C` instances all
constructed here, plus the two layer inclusions `epsHom`, `etaHom` of the dual numbers and their
derivation- and constant-compatibility.

This clears the dead route recorded last stretch: `z′`, `differentialJet` and
`differentialPolynomialEvalOver` all elaborate on `BiDual C`, none of which they do on
`DualNumber (DualNumber C)`.  Construction note: build the derivation from
`(AddMonoidHom.mk' derivFun _).toIntLinearMap`, not from a `toFun` with `map_smul'`, or the `ℤ`-smul
forces a `zsmulRec` computation on the coefficients.

Next: the adjoint-derivative identity in `BiDual` plus two `matrixZeroSet_ringHom` transports.

## Card 3 item (b): the adjoint derivative is proved

`HTGeometry.BiDualAdjointDerivative` (wired, built, axiom-clean): `biMatrix`, `biMatrix_mul` (the
two-parameter first-order product rule), `etaMatrix_eq`/`epsMatrix_eq`, and
`adjointDerivative_mem_zeroSet` — **`1 + εY + εη(XY − YX)` lies in the zero set** whenever
`1 ± ηX` and `1 + ηY` do and the zero set is closed under multiplication over `C[ε,η]/(ε²,η²)`.

The commutator is now a coefficient of a member of the zero set.  Remaining on item (b): extract the
`εη`-coefficient (a three-case induction, same pattern as `snd_differentialPolynomialEvalOver_dual`,
using that the `η`-component of the point vanishes), then the line-stabiliser condition and the
Zariski-density transfer.

## Card 3 item (b): BRACKET CLOSURE PROVED

`HTGeometry.BiDualBracketExtraction` (wired, built, axiom-clean): `BiDual.jet_*`,
`evalOver_biDual_of_et_zero` (at an `η`-free point the `(1, εη)` pair of the value is a dual-number
evaluation), `mem_zeroSet_of_biMatrix_et_zero`, and **`bracket_mem_zeroSet`** — the Lie algebra of a
differential algebraic group is closed under the bracket.

So the tangent space at the identity is now: a module over the differential constants
(`DifferentialTangentSubmodule`), `Ad`-stable (`DifferentialTangentAdjoint`), and bracket-closed
(here).  Those are `cassidy_sl2`'s `hbr` plus its module hypothesis; `htr` is immediate for `SL₂`.
Item (b)'s remaining gates are `hline` (line stabilisers) and `hdense` (Zariski-density transfer).

## Card 3 item (b): tangent space packaged as a constants-submodule

`HTGeometry.IdentityTangentSubmodule` (wired, built, axiom-clean): `matrixTangent` (the tangent
directions at the identity as a `Submodule (differentialConstants C)`), `mem_matrixTangent_iff`
(**`X` is tangent exactly when `1 + εX` is in the zero set**), `dualMatrix_neg_mem_zeroSet`, and
`bracket_mem_zeroSet_of_one` — bracket closure with the `−X` hypothesis removed.

`cassidy_sl2` now has three of its four hypotheses supplied for the tangent space of a differential
algebraic subgroup of `SL₂`: the submodule structure, `htr` (immediate for `SL₂`) and `hbr`.  The
open two are `hdense` (Zariski-density transfer) and `hline` (line stabilisers).

## Card 3 item (b): `hline` reduced to a nonvanishing

`HTGeometry.ScalarStabiliserRelation` (wired, built, axiom-clean): `exists_monic_relation_of_linear`
(a nonzero linear jet relation becomes monic, by induction down the index), `scalarStabiliser` (the
scalars `c` with `c·Y` again tangent form an additive subgroup), and
`exists_monic_relation_scalarStabiliser` — the `hsol` hypothesis of
`cassidy_sl2_of_differentialSolution`, modulo one nonvanishing.

Four of the five hypotheses of `cassidy_sl2_of_differentialSolution` are now supplied for the
tangent space of a differential algebraic subgroup of `SL₂`: the submodule structure, `htr`, `hbr`,
and `hsol`.  The single open one is `hdense` — the Zariski-density transfer.

## Card 3 item (b): `sl₂` adjoint irreducibility proved

`HTGeometry.Sl2AdjointIrreducible` (wired, built, axiom-clean): `unipotentLower`, `upperConj`,
`lowerConj`, their entry formulas, `raising_mem_of_adStable`, and **`sl2_of_adStable`** — a nonzero
subspace of traceless matrices stable under conjugation by both unipotent lines is all of `sl₂`.

Finite computation: conjugation by `u(t)` is quadratic in `t`, so `t = ±1` isolates its coefficients
`−2A₁₀·e` and `2A₁₀·h − 4A₀₀·e`; every nonzero traceless `A` yields `e`, and conjugating `e` by the
lower unipotents yields `f` and `h`.

This is `hdense`'s irreducibility half.  Left on `hdense`: the Zariski-closure step (stability of the
span under the unipotents of `SL₂(U)`, not just under group elements) and nonvanishing of the Lie
algebra.

## Card 3 item (b): `hdense`'s Zariski-closure step proved

`HTGeometry.AdjointStableZariskiClosure` (wired, built, axiom-clean): `adjugate_two`,
`det_unipotentUpper/Lower`, `adjugate_unipotentUpper/Lower`, `conj_mem_of_dense` (adjoint stability
passes from `G` to every determinant-one matrix), `upperConj_mem_of_dense`,
`lowerConj_mem_of_dense`, and `sl2_of_dense`.

Mechanism: for determinant one the inverse is the adjugate, a polynomial in the entries, so
`g ↦ φ(g·A·adj g)` is polynomial; density extends its vanishing from `G` to all determinant-one
matrices; and a subspace over a field is the common kernel of the functionals killing it
(`Submodule.exists_dual_map_eq_bot_of_notMem`).  The density hypothesis is stated where it is used,
so no Zariski topology is needed.

Card 3 item (b) now has all five hypotheses of `cassidy_sl2_of_differentialSolution` supplied, each
modulo one explicit nondegeneracy: `hsol` modulo its nonvanishing, `hdense` modulo `L ≠ 0`.

## Card 3 item (b): `htr` proved outright

`HTGeometry.Sl2TangentTraceless` (wired, built, axiom-clean): `detPoly`, `evalOver_detPoly`, and
`trace_eq_zero_of_mem_zeroSet` — linearising `det = 1` at the identity gives the trace exactly,
because `ε² = 0`, so tangent directions are traceless with no nondegeneracy hypothesis.

Four structural hypotheses of `cassidy_sl2_of_differentialSolution` are now unconditional for the
tangent space of a family containing `detPoly`; the two residues (`hsol`'s nonvanishing and
`hdense`'s `L ≠ 0`) are the content of "proper" in Cassidy's theorem and fail exactly when the
differential Galois group is everything.  Next: the dichotomy that turns that failure into the
card's conclusion directly.

## Card 3 item (b): CAPSTONE — Cassidy for the tangent space, assembled

`HTGeometry.DifferentialSubgroupCassidy` (wired, built, axiom-clean): `matrixTangentM`,
`span_conj_stable`, `mem_scalarStabiliser_iff_smul_mem`, and **`cassidy_of_matrixTangent`** — one
theorem applying `cassidy_sl2_of_differentialSolution` to the tangent space of a differential
algebraic subgroup of `SL₂`, with all four structural hypotheses discharged from the eight modules
built this session.

Remaining hypotheses of the capstone: the two properness nondegeneracies (`hLne : L ≠ 0` and
`hsolres`), plus the group data (dual-number closure under multiplication, adjoint stability, and
the polynomial form of Zariski density).

Item (b) is therefore reduced from "Cassidy's structure theorem" — a multi-module project — to one
named theorem plus the properness dichotomy.

## Card 3 item (b): line-stabiliser hypothesis eliminated

`HTGeometry.BoundedLineStabiliserFinite` (wired, built, axiom-clean):
`boundedOverBase_smul_of_finiteDimensional` and `cassidy_sl2_of_finiteDimensional` — if the Lie
algebra is finite dimensional over the base, the line-stabiliser hypothesis of Cassidy's
classification is automatic, because `c ↦ c·Y` embeds the stabiliser into `L`.

So `hsolres` is gone as a residue: the classification now needs traceless, bracket-closed, spanning,
and finite dimensionality.  Card 3 item (b)'s only remaining residues are `FiniteDimensional` of the
Lie algebra and `L ≠ 0` — both of which are dimension statements about the differential algebraic
group rather than hypotheses about its equations.

## Card 3 item (b): the capstone in final form

`DifferentialSubgroupCassidy.cassidy_of_matrixTangent_finite` (wired, built, axiom-clean) —
Cassidy's classification for the tangent space of a differential algebraic subgroup of `SL₂` with
the line-stabiliser hypothesis replaced by finite dimensionality.  Hypotheses: `hone`, `hdet`,
`hmulBi` (the family defines a group in `SL₂`), `hGstable`, `hdensePoly` (adjoint stability and
Zariski density), and the two dimension statements `hLne`, `hfin`.

Item (b) is therefore exactly the properness dichotomy: either the parameterised Galois group is all
of `SL₂` — and then the output satisfies no differential relation and the card's conclusion is
immediate — or it is proper, and the capstone conjugates its Lie algebra into the constants.  That
dichotomy is the parameterised Picard–Vessiot input the card already lists as outstanding; every
other step of the classification is now a Lean theorem.

## Card 3 item (b): finite groups are not Zariski dense

`HTGeometry.FiniteNotZariskiDense` (wired, built, axiom-clean): `unipotentUpper_entry`,
`unipotentUpper_injective`, and `exists_separating_poly_of_finite` — a finite set of matrices is
separated from `SL₂` by one polynomial in the `(0,1)` entry, because the unipotent line runs that
entry over the whole (infinite) field.

This is the elementary half of `hLne`: zero Lie algebra ⟹ finite ⟹ not Zariski dense, contradicting
the density that Burnside supplies from irreducibility plus `no_imprimitive_pair`.  The remaining
link is "zero Lie algebra ⟹ finite" — the Kolchin dimension statement — which with finite
dimensionality is now the single outstanding input of item (b).

## Card 3 item (b): the constant part of the Lie algebra

`HTGeometry.ConstantTangentDirections` (wired, built, axiom-clean):
`differentialJet_eq_zero_of_deriv_eq_zero` and `linearisationForm_const` — at a perturbation with
constant entries the linearisation collapses to the algebraic differential, since constants have no
jets above order zero.

This reroutes `hLne` away from Kolchin dimension theory: the constant part of the Lie algebra is the
tangent space of the underlying algebraic variety, which for a group with Zariski closure `SL₂` is
`sl₂` — nonzero.  What remains is identifying the order-zero differential with the algebraic one for
the specific family, which is bookkeeping.

## Card 3 item (b): `hLne` reduced to the algebraic differential

`HTGeometry.ConstantLieAlgebraNonzero` (wired, built, axiom-clean): `const_mem_matrixTangentM` and
`matrixTangentM_ne_bot_of_const` — a constant matrix annihilated by the order-zero differentials of
the family at the identity is a tangent direction, so the Lie algebra is nonzero as soon as one such
nonzero constant matrix exists.  No differential content: constants have no jets above order zero.

Item (b) now has exactly one open hypothesis in `cassidy_of_matrixTangent_finite`: `hfin`, finite
dimensionality of the Lie algebra over the constants — the statement that the group is proper.

## Card 3 item (b): the properness dichotomy is Lean

`DifferentialSubgroupCassidy.cassidy_dichotomy` (wired, built, axiom-clean) — either the Lie algebra
is infinite dimensional over the constants, or one conjugation carries it onto the constant span of
`h`, `e`, `f`.  Unconditional: no dimension hypothesis remains in the statement, and all six
structural hypotheses are discharged elsewhere in the tree.

Item (b)'s single outstanding input is now the parameterised Picard–Vessiot implication
"differential algebraicity of the output rules out the infinite-dimensional branch".  Everything on
either side of it is proved.

## Card 6: `(1)` from one annihilating polynomial

`HTGeometry.IsogenyDegreeFixedField.eq_fixedField_of_annihilating_poly` (wired, built, axiom-clean)
— `E = K^Γ` from: `E` derivation-closed inside the invariants, `g` differentially generating `K`,
and one nonzero `q ∈ E[X]` with `q(g) = 0` and `deg q ≤ |Γ|`.

Card 6's `(1)` therefore needs from geometry only the annihilating polynomial `alpha^n(X) −
alpha^n(g)`, of degree `deg alpha^n = |Gamma_n|` — the definition of the degree of a finite
morphism, with no jet or prolongation content.  Items 2–5 of that card's Lean status are untouched.

## Card 6: the deck-closure step

`HTGeometry.FixedFieldSupremum` (wired, built, axiom-clean): `iInf_fixedField` (the infimum of fixed
fields is the fixed field of the supremum, by `Subgroup.iSup_induction`) and
`iInf_eq_fixedField_iSup_of_eq`.

Card 6's Theorem A is now assembled from three Lean theorems — `(1)` per level from
`eq_fixedField_of_annihilating_poly`, `(2)` from `iInf_eq_fixedField_iSup_of_eq`, `(3)` from the
existing `DifferentialKolchinClosure` — plus the single order-zero geometric input (the annihilating
polynomial of the covering degree).  Items 2–5 of the card's Lean status still gate Theorems B–D.

## Card 8 item 3a: the dominant-term lemma at a place

`HTGeometry.PlaceLimit` gained `valuation_sum_of_lt` (wired, built, axiom-clean) — a finite sum with
one strictly dominant term has that term's valuation, with the degenerate zero case handled (no term
can be strictly below zero, so the index set collapses to a singleton).

That completes the place-level toolkit the peel's border-shape inductions call: grading
(`PlaceGrading`), derivation drop (`PlaceDerivationValuationDrop`), values and determinants
(`PlaceLimit`), and now the dominant term.  What is left of item 3a is transcribing the inductions
themselves.

## Card 7: finite interpolation with vanishing, solved

`HTGeometry.EnlargedPacketInterpolant.exists_mvPolynomial_packet_and_vanishing` (wired, built,
axiom-clean) — one multivariable polynomial with prescribed jets at the packet and vanishing jets at
the translates, from the corpus's packet surjectivity applied to the enlarged packet (whose points
are distinct by `pairwiseDistinctModulo_enlargedPacketPoints`).

So the interpolation half of card 7's analytic obligation is closed constructively.  The residue is
the growth estimate for a *lower-automorphic* interpolant, which with
`AbeDampingPacketData.ofFiniteVanishing` closes the damping datum, plus `IsAbePositiveTorusless`.

## Card 4: stable rank of the accumulated leading matrices

`HTGeometry.ChainRankStabilization` (wired, built, axiom-clean): `rank_chainProdK_antitone_le` and
`exists_rank_chainProdK_stabilize` — the ranks of an ordered product are non-increasing and attain
their minimum at some index, beyond which they are constant.

This refines `chainProdK_dichotomy` into a case distinction on the stable rank, and is the natural
candidate invariant for the restart bound: a restart that lowers the stable rank can happen at most
`r` times.  The positive-rank regime is already settled by `matDeg_chainProd_eq`.

## Card 4: the stable image

`HTGeometry.ChainStableImage` (wired, built, axiom-clean): `range_chainProdK_antitone`,
`range_chainProdK_antitone_le`, `exists_range_chainProdK_stabilize` — the images of an ordered
product decrease and stabilise beyond the index of minimal rank.

With `twistedChain_left` (`P_{n+1} = C·σ(P_n)`) this is the sub-object of the slope filtration: on
the stable image the twisted operator is a bijection.  Card 4's open point still needs the restart
bound.

## Card 8 item 3a: the place toolkit is complete; one design constraint recorded

`PlaceLimit` gained `PlaceLim.mul_of_mem`, `placeLim_prod_of_mem`, `placeLim_det_of_mem` — the limit
API with values in a trivially valued subfield.

**Design constraint (found by auditing `TopCoordinateDegree`'s exports against the place toolkit):**
`TopFree` is closed under addition but `PlaceFree` is not — coordinate-freeness is a subfield
condition, being a unit at a place is not (`1`, `−1` are units, `1 + (−1)` is not).  The
transcription must translate `TopFree` as `PlaceTrivialOn F`, not as `PlaceFree`.  With that, every
general lemma of the coordinate model has its place-level counterpart; what is left of item 3a is
the model-specific layer (`fact`, `logFactor`, `univFactor` over the algebraic extension) and the
inductions.

## Card 4: the stable rank decides the dichotomy

`ChainRankStabilization` gained `rank_eq_zero_iff` (a mathlib gap: a matrix has rank zero exactly
when it vanishes) and `chainProdK_ne_zero_iff_rank_pos` — the accumulated chain never vanishes
exactly when its stable rank is positive.  `chainProdK_dichotomy` is now a numerical criterion.

## Card 6: translation invariance at arbitrary shift

`HTGeometry.PolynomialShiftInvariant.comp_X_add_C_eq_self` (wired, built, axiom-clean) — a
polynomial invariant under one nonzero translation is constant, by rescaling the variable to reduce
to the corpus's unit-shift version.  A single translation suffices; characteristic zero already
rules out a nonconstant periodic polynomial.

With `shift_invariant_rational_constant_gen` this owns both halves of the one-dimensional case of
Corollary C's `(6)`; the passage to a general connected commutative group is part of item 2.

## Card 6: translation invariance in several variables is a linear condition

`HTGeometry.MvPolynomialTranslationSpan` (wired, built, axiom-clean).  Over any characteristic-zero
field the translation directions fixing a multivariate polynomial form a **linear subspace**
(`translationSubmodule`), not merely a subgroup: restricting to the affine line `x + t·v` gives a
one-variable polynomial with the same value at every nonnegative integer, hence constant, hence
invariance under `c·v` for every scalar `c` (`mvShift_smul_of_mvShift`).

Consequences: `eq_C_of_span_translations_eq_top` — a spanning set of invariance directions forces
constancy; and `eq_C_of_coordinate_shift_invariant` — **one nonzero translation per coordinate
already forces constancy**, with no density hypothesis.

This is the multivariate half of Corollary C's `(6)`.  The corpus previously owned only the
ℂ-specific `Hurwitz.PowerOrbitAdditiveSaturation.translationInvariantSubmodule`; the general-field
version now lives in the reusable area with the constancy corollaries stated.

`PolynomialShiftInvariant` also gained `comp_X_add_one_eq_self_domain` and
`comp_X_add_C_eq_self_domain` — the one-variable rigidity over an arbitrary characteristic-zero
integral domain, which is what a coefficient ring of remaining variables is.

## Card 8 item 3a: the univariate factor at a place

`HTGeometry.PlaceUnivFactor` (wired, built, axiom-clean) is the first model-specific layer of the
algebraic model: `valuation_eval_eq` (`v(p(x)) = v(x)^{deg p}` exactly for `v(x) > 1`),
`placeDegLE_logFactor`, and `placeLim_mul_logFactor` — the place-level counterparts of
`topDegLE_logFactor` and `topLim_fx_mul_logFactor`.

The only hypothesis is that the coefficients lie in a subfield on which the place is trivial, which
`placeFree_of_isIntegral` makes automatic after any algebraic extension.  The accuracy is `(v x)⁻¹`
rather than the coordinate model's fixed `−1`, which is exactly the ramification bookkeeping
`PlaceLimit`'s parametrised accuracy was built for.

## Card 8 item 3a: the derivation drop and the peel column at a place

`HTGeometry.PlaceRationalDerivationDrop` (wired, built, axiom-clean): `valuation_derivation_mul_le`
— `v(D f)·v(x) ≤ v(f)` for a rational function `f = p(x)/q(x)` of a large element, the place-level
form of `TopDegLE.fpderiv_top`.  Proved from the Wronskian identity plus the exact valuations of
part 17; the constant/constant case is handled separately because the quotient then lies in the
trivially valued subfield.

`HTGeometry.PlaceShiftIterate` (wired, built, axiom-clean): `placeShift`,
`placeDegLE_placeShift`, `placeDegLE_iterate_placeShift`, `placeDegLE_placeShift_of_split`,
`placeLim_mul_of_split`, `placeLim_mul_zero_of_placeDegLE` — the peel's operator does not raise the
place degree, every iterate keeps it, and the scaled column has value `(deg Q_m, 0, …, 0)`.

Remaining on item 3a: instantiate the abstract column at the cascade's own derivation and response
over the algebraic extension — the closed class `S` (the analogue of `lowSub`) and the bound
`v(c) ≤ 1` have to come from the model rather than be assumed.

## Card 8 item 3a: the peel column at a place, assembled

`HTGeometry.PlaceRationalClass` — `RatIn F x` (the place-level `lowSub`), its closure under the
field operations and under a derivation killing `F`, and the drop `v(D f)·v(x) ≤ v(f)` on the whole
class.  `HTGeometry.PlacePeelColumn` — `placeDegLE_placeShift_of_borderShape`,
`placeLim_border_of_borderShape`, `placeLim_below_of_borderShape`: the scaled newest column of a
border-shaped vector has value `(deg p, 0, …, 0)` at the place.  Both wired, built, axiom-clean.

The only law-specific input left at this level is the Wronskian fact that `E` sends the logarithmic
factor two place-degrees down.

`PlacePeelColumn` also gained `placeDegLE_placeShift_logFactor`: a response one place-degree down
already sends the logarithmic factor two degrees down, discharging the leading hypothesis of the
border-shape lemmas.  When the response is only of unit size the same conclusion is the law's
Wronskian cancellation, which is the one law-specific input still outstanding at this level.

## Card 7: the growth estimate is now two sup bounds

`HTGeometry.PoincareTermJetGrowth` (wired, built, axiom-clean):
`norm_multiIndexJetEvalCLM_poincareTermEntire_le_gaussian` produces exactly `hbound` of
`abeDampingMajorant_of_finite_vanishing` from a Gaussian sup bound on the inverse automorphy factor
and a polynomial sup bound on the seed, both over one fixed ball.  Cauchy's inequality does the rest,
so no jet estimate on the seed is required.

Card 7's residue is therefore two pointwise statements on a compact set: the Riemann-form positivity
`IsAbePositiveTorusless` for the factor, and the induction hypothesis's growth bound for the
interpolant.

## Card 7: the positive automorphic factor is built, with its Gaussian decay

`HTGeometry.AppellHumbertGaussianBound` — Cauchy–Schwarz for a positive semidefinite Hermitian form
(`IsHermitianForm.norm_sq_le`, proved from scratch) and `norm_inv_appellHumbertFactor_le`:
`‖e(γ,z)⁻¹‖ ≤ exp(πC²)·exp(−(π/4)(H γ γ).re)` for base points with `(H z z).re ≤ C²`.

`HTGeometry.AppellHumbertAutomorphicFactor` — `appellHumbertAutomorphicFactor`: the expression *is*
an `AutomorphicFactor` for every period group (normalised, cocycle, nowhere zero, line-entire,
continuous), and `norm_inv_appellHumbertAutomorphicFactor_le` states the decay in that language.

Both wired, built, axiom-clean.  Card 7's damping hypothesis now needs only the seed's own sup bound.

## Card 7: the damping hypothesis is proved against a fixed ball

`HTGeometry.PoincareTermAppellHumbertDecay` (wired, built, axiom-clean).  For a lower-automorphic
seed the lattice dependence of the Poincaré term collapses to the Appell–Humbert expression of the
difference form `D = H_u − H_l`, so Abe positivity `D ⪰ 0` gives
`‖jet‖ ≤ (exp(πC²)·M_s/ρⁿ)·exp(−(π/4)·D(γ,γ))` with `M_s` the seed's sup on ONE fixed ball.

That is `hbound` of `abeDampingMajorant_of_finite_vanishing`, no longer an assumption.

## Card 4: the shear invariant

`HTGeometry.ShiftedMatrixDegree` (wired, built, axiom-clean): `ShiftDegLE k P c` — the shifted
matrix degree as a predicate, with submultiplicativity, map-invariance, `matDeg_le`, and the two
chain theorems `matDeg_twistedChain_le_of_shiftDegLE` (every shear bounds the growth rate) and
`matDeg_twistedChain_le_of_shiftDegLE_zero` (**the bounded branch**, with the explicit bound
`spread(k)` uniform in `n`).  Nothing leaves the operator ring: no completion and no `∂⁻¹`.

Two recorded counterexamples pin the remaining gap: `[[0,1],[∂,0]]` shows integer shears cannot see
a slope of denominator 2 (so the restart `N` is unavoidable), and `I + ∂M` with `M` nilpotent
constant shows a constant base change is also unavoidable.  The invariant is therefore
`min over (N, S) of matDeg(S⁻¹A_N S)/N`, and the missing half is that this min is attained.

## Card 6 item 1: iterates of a rational map

`HTGeometry.RationalMapComposition` (wired, built, axiom-clean): `ratComp`, `aeval_ratComp`,
`ratMapEval_ratComp` (the composite of two rational maps is a rational map), `ratIter`,
`natDegree_ratIter_le` (`deg αⁿ ≤ dⁿ`), `ratMapEval_ratIter` (it computes the `n`-fold iterate).

With `RationalPrefixDeckDescent.differentialAdjoin_ratMapEval_eq_fixedField` — which the tree already
owned — item 1 for a one-dimensional isogeny now needs only `dⁿ ≤ |Γₙ|` and the noncriticality of the
iterate.

Card 6 item 1 is now closed for a one-dimensional isogeny:
`RationalMapComposition.differentialAdjoin_ratIter_eq_fixedField` gives `C⟨αⁿ(g)⟩ = K^{Γ}` for every
`n`, with noncriticality of the iterate proved from the chain rule rather than computed.  The only
remaining input is `dⁿ ≤ |ker αⁿ|`.

## Card 4: the shifted leading matrix

`HTGeometry.ShiftedTopMatrix` (wired, built, axiom-clean): `coeffZ` (coefficients at integer
indices), `shiftTopMatrix`, `shiftTopMatrix_mul` (multiplicativity), `shiftTopMatrix_chainProd`, and
the two growth theorems `matDeg_chainProd_sub_le` and `matDeg_twistedChain_sub_le`:

> `|matDeg A_n − n·c| ≤ spread(k)` uniformly in `n`, whenever the accumulated shifted leading
> matrices of the twisted chain never vanish.

So relative to any shear the phase is completely decided — `c = 0` bounded, `c ≥ 1` exactly linear
with rate `c` — and the residue is the single statement that some `(N, S)` attains the minimum of
`matDeg(S⁻¹A_N S)/N`.

## Card 7: the majorant is closed from Abe positivity in coordinates

`HTGeometry.AbePositiveGaussianMajorant` (wired, built, axiom-clean): `abeGram`,
`re_hermitian_latticeSum`, `exists_gaussian_of_posDef`, and
`norm_multiIndexJetEvalCLM_le_gaussianLatticeWeight` — the `majorant` field of
`AbeDampingPacketData`, proved for Appell–Humbert data from `Matrix.PosDef (abeGram (H_u − H_l) v)`
plus the seed's sup bound on one fixed ball.  Coercivity reuses the corpus's `posDef_coercive`.

Remaining for a full damping datum: `normal` (summability), `seed`/`seed_jet` (induction hypothesis
plus `EnlargedPacketInterpolant`), and the bookkeeping fields `compat`, `decomp`.

## Card 7: the `normal` field is closed too

`HTGeometry.AbePoincareLocalNormal` (wired, built, axiom-clean):
`summableLocallyUniformlyOn_poincareTerm_appellHumbert` — the complement Poincaré series converges
locally normally, by the M-test through the corpus's
`summableLocallyUniformlyOn_of_polynomialGaussianLattice_bound`.  Both compact bounds are free:
`continuous_hermitian_self_re` (new) and continuity of the seed.

Of `AbeDampingPacketData`'s fields, `majorant` and `normal` are now both proved for Appell–Humbert
data; what remains is the group bookkeeping (`le`, `compat`, `comp`, `decomp`) and the seeds, which
are the induction hypothesis.

## Card 7: `hbound` in the shape the finite-vanishing majorant consumes

`HTGeometry.AbeDampingBoundBridge.abeDampingBound_of_appellHumbert` (wired, built, axiom-clean):
`‖jet‖ ≤ C₀·B^r·exp(−σ₀∑z_k²)` uniformly in packet index, seed index, lattice point and `B`, from
(1) Appell–Humbert factors with a lower-automorphic seed family, (2) `Matrix.PosDef (abeGram ...)`,
(3) two sup bounds on one ball.  The Cauchy estimate is at unit radius, so the constant does not
depend on the jet order.

This feeds `abeDampingMajorant_of_finite_vanishing`, so both analytic fields of
`AbeDampingPacketData` — `majorant` and `normal` — are now proved.

`AbeDampingBoundBridge` also gained `appellHumbertAutomorphicFactor_compat` — the `compat` field of
the damping datum: the upper factor restricts to the lower one along `ΓH` exactly when the two forms
and the two semicharacters agree there.  Of `AbeDampingPacketData`'s ten fields, only `le`, `comp`,
`comp_mem`, `decomp` (pure lattice data) and `seed`/`seed_mem`/`seed_jet` (the induction hypothesis)
are not yet supplied by a theorem.

## Card 7: CORRECTION — the seed hypothesis

The earlier Poincaré-decay entries used `seed(x+γ) = e_l(γ,x)·seed(x)` for `γ ∈ Γ`.  That is
unsatisfiable for a seed of the induction: the seed is automorphic only for `ΓH`, and the complement
translates are exactly the elements outside `ΓH`.  Corrected across
`PoincareTermAppellHumbertDecay`, `AbePositiveGaussianMajorant`, `AbePoincareLocalNormal`,
`AbeDampingBoundBridge` (all rebuilt, axiom-clean): the hypothesis is now the bounded **normalised
modulus** `‖seed y‖ ≤ M·exp((π/2)·Re H_l(y,y))`, which is the `ΓH`-periodic invariant.  All
conclusions are unchanged; the new ingredient is `IsHermitianForm.re_add_self`, and the bound on
`Re H_l` over a ball is free by `continuous_hermitian_self_re`.

## Card 4: constant changes of basis

`HTGeometry.ConstantConjugationDegree` (wired, built, axiom-clean): `twistedChain_conj`
(`(S⁻¹Aσ(S))_n = S⁻¹A_nσⁿ(S)`) and `matDeg_twistedChain_le_of_conj_shiftDegLE_zero` — the bounded
phase from a *pair* (constant basis, shear), which covers the `I + ∂M` counterexample that no shear
alone can.  Constant conjugation stays inside `K[∂;δ]`, unlike a shear.

Still open: whether the criterion is necessary.  General lattices are `U·diag(∂^k)·O^r` with
`U ∈ GL_r(O)`, and constant `S ∈ GL_r(K)` is a proper subgroup; closing that gap needs the degree
valuation on `Frac(K[∂;δ])`, which the tree does not yet have.

## Card 7: the damping datum is constructible

`HTGeometry.AbeDampingPacketConstruction.abeDampingPacketDataAppellHumbert` (wired, built,
axiom-clean) assembles **every field** of `AbeDampingPacketData` for a pair of Appell–Humbert
factors.  `normal` and `majorant` are discharged by the theorems of the previous entries; the
remaining fields are the induction step's own data — the two period groups with their complement
(`le`, `comp`, `comp_mem`, `decomp`), and the seed family with prescribed jets, bounded normalised
modulus `C_s·B^r`, and vanishing on a disc of squared radius `≥ κB`.

With it, `HasAbeDampingFamily` is exactly "the induction hypothesis supplies such a seed family for
every finite jet packet", and `jetAmpleEveryFiniteOrder_of_hasAbeDampingFamily` (already in the
tree) closes the induction step.

## Card 4: the degree valuation on the Ore field

`HTGeometry.PseudoDiffOpDegree` (wired, built, axiom-clean): `ordQ` on `PseudoDiffOp K = Frac(K[∂;δ])`
with `ordQ_mul` (additive on nonzero elements — the convention `deg 0 = 0` makes it false at zero)
and `ordQ_inv`.  Well-definedness is the Ore-expansion condition; additivity comes from `ore_eq`.

Recorded alongside: the slope-`1/2` example `[[0,1],[∂,0]]` is **not** invertible over `K[∂;δ]`
(inverting forces `∂·B₁₂ = 1`).  So whether a matrix invertible over the operator ring can have
non-integral slopes is now a sharp isolated question — if it cannot, integer shears suffice and the
restart bound follows.

## Card 4: the restart is unavoidable — a proved counterexample

`HTGeometry.InvertibleLeadingChainVanishes` (wired, built, axiom-clean): the companion matrix of
`t³ + ∂t + 1` is invertible over `K[∂;δ]` (explicit inverse given and both products proved to be the
identity), has matrix degree one, and its leading matrix is the single matrix unit `E₂₃`, whose
square is zero — so the accumulated leading chain dies at step two.

Its Newton polygon gives root valuations `1, −1/2, −1/2`: a denominator-two slope, invisible to every
integer shear.  So the sharp question raised in the previous entry is answered **negatively**: no
pair (constant basis, integer shear) can put every invertible matrix in the exact-degree branch, and
the restart is a real feature.  What is left is exactly the bound on the number of restarts, i.e.
that the slopes have denominator at most `r`.

## Card 7: the corpus's own majorant hypothesis is discharged

`HTGeometry.AppellHumbertLatticeGrowth.hasLatticeExponentialGrowth_appellHumbert` (wired, built,
axiom-clean) proves `AutomorphicFactor.HasLatticeExponentialGrowth` for every Appell–Humbert factor
of a positive semidefinite Hermitian form — with growth rate zero, since the reciprocal factor is
bounded on compacta.  That is the single hypothesis of the tree's own
`gaussianMajorant_of_hasLatticeExponentialGrowth`, so the corpus's majorant chain no longer has an
unverified analytic field for this class.
