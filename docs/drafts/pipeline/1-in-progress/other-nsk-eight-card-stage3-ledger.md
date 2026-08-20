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
