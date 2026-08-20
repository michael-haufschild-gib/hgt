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
