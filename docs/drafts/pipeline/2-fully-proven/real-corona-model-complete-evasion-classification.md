# Real-corona model-complete evasion classification

- **ID:** `real-corona-model-complete-evasion-classification`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), with falsified universal no-go and dependency-closed positive survivor
- **Parent:** `../4-publication-ready/real-corona-isotropy-clifford-transgression-law.md`
- **Statement:** Across arbitrary invariant-domain operator models and arbitrary unital function
  subalgebras, the Real-corona idempotent is locally admissible exactly by parity decoupling on the
  operator side and independent sector patching on the coefficient-algebra side.

## Goal

Replace the false claim that every conceivable model is obstructed by exhaustive equivalences
which classify every model in two declared universes.  Then combine those equivalences with the
already exact Real-cyclic parity and fixed-sector support--multiplicity laws, so every escape from
P1--P4 has a named necessary and sufficient mechanism.

## Gates

- [x] 0 → 1 in-progress: well-posed universes, falsifiers, exact survivor, literature collision
  search, and proof routes identified
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: unconditional Lean theorems, targeted module build, axiom and lint audit
- [ ] 3 → 4 publication-ready: manuscript rebuilt and hostile review passed

## Falsified universal no-go

`[FALSIFIED]` No universal impossibility theorem can quantify over all conceivable models.  Given
the Real-corona splitting, an unbounded block-diagonal operator commutes with its projector.  Given
any coefficient algebra, adjoining the characteristic projector makes that projector algebraically
smooth.  These are genuine countermodels, not technical gaps.

## Strongest positive survivor

`[CANDIDATE] [MODEL_COMPLETE_EVASION_CLASSIFICATION]`

1. Let `D` be any complex-linear partially defined operator on a normed space and let `m` be any
   domain-preserving isometric involution.  Write

   ```text
   D_even = (D + m D m)/2,       D_odd = (D - m D m)/2.
   ```

   Then the commutator with the Real orientation is bounded on the exact domain if and only if
   `D_odd` is bounded there.  For genuinely unbounded `D`, this is equivalent to all unboundedness
   being carried by `D_even` while `D_odd` remains bounded.  Thus every operator-model evasion is
   exactly parity decoupling; no third operator channel exists.

2. Let `X` be any set, `S ⊆ X`, and `A ⊆ ℂ^X` any unital complex subalgebra.  Let `χ_S` be the
   sector idempotent.  Then `χ_S ∈ A` if and only if `A` has independent sector patching:

   ```text
   for every f,g in A, some h in A equals f on S and g on X \ S.
   ```

   Thus every coefficient-algebra evasion is exactly sector splitting.  For any smooth dense
   function algebra represented as a unital subalgebra of `ℂ^X`, smoothness of the Real-corona
   projector is equivalent to this patching property.

3. The previously proved Real-cyclic parity law and fixed-sector
   `multiplicity = support + excess` law classify the two remaining orbit channels.  Consequently
   model changes can relocate information among parity, patching, and multiplicity enrichment,
   but cannot create an unnamed channel inside these universes.

## Complete paper proof

`[PROVED HERE]`

Put `e=(1+m)/2`.  Since `m` preserves `Dom D`, so does `e`.  Direct expansion on this exact
domain gives

```text
[D,e] = (1/2)[D,m].
```

The parity decomposition gives `[D,m]=2 D_odd m`.  Since `m²=1`, replacing `x` by `mx` proves
`D_odd m=-mD_odd`; isometry then gives, pointwise,

```text
||[D,e]x|| = ||D_odd x||.                                  (A)
```

Therefore `[D,e]` is bounded on `Dom D` if and only if `D_odd` is bounded there.  If `D` is
genuinely unbounded and (A) is bounded, boundedness conservation

```text
D bounded  iff  D_even and D_odd are both bounded
```

forces `D_even` to be genuinely unbounded.  Conversely, bounded `D_odd` alone implies bounded
`[D,e]` by (A).  This proves the operator classification, including both directions and the exact
norm constant.

For the algebra theorem, assume first `χ_S ∈ A`.  Given `f,g∈A`, closure under multiplication,
addition, and constants puts

```text
h = χ_S f + (1-χ_S)g
```

in `A`; pointwise, `h=f` on `S` and `h=g` on its complement.  Conversely, apply independent
sector patching to the two members `1,0∈A`.  The resulting `h` is pointwise one on `S` and zero on
its complement, hence equals `χ_S` by extensionality and belongs to `A`.  This proves the second
iff.

No topological, spectral, summability, or choice-dependent assertion is used.  Exhaustiveness is
literal after declaring the two universes: every invariant-domain operator has exactly one odd
parity component, and every unital function subalgebra either contains `χ_S` or does not.  The two
iff theorems name the necessary and sufficient escape mechanism in each case.

## Hostile proof audit

- Domain issue: both `m` and `(1+m)/2` preserve the exact supplied domain; no everywhere-defined
  surrogate for `D` is used.
- Constant issue: the norm identity is exact, not merely a one-way estimate.
- Algebra issue: unitality is necessary for the reverse patch with `1`; it is stated explicitly.
- Smoothness issue: for a chosen smooth function algebra, “smooth projector” means membership in
  that algebra.  The theorem classifies all such choices; it does not confuse this with a topology
  on the ambient set of all functions.
- Universality issue: “all conceivable mathematical objects” remains ill-typed.  The theorem is
  universal over the two maximal typed categories relevant to the paper, and explicit
  countermodels prevent any stronger impossibility claim.

## Novelty and collision audit

- Parity decomposition is standard operator theory and already present in the internal corpus.
- Idempotent-induced sector splitting is a commutative instance of classical Peirce decomposition.
- Candidate novelty is not either lemma alone.  It is the simultaneous exact classification of
  all Real-corona evasions and its coupling to cyclic parity and multiplicity excess.  This must be
  presented as a synthesis/classification theorem, not as invention of Peirce decomposition.
- Primary-parent audit: unbounded KK theory, Peirce decompositions, and cyclic homology of crossed
  products contain the separate mechanisms; no source found states this Real-corona four-channel
  classification.

## No-go closure

- **Exact killing theorem/mechanism:** block-diagonal unbounded `D` gives bounded (indeed zero)
  projector commutator; adjoining `χ_S` to a function algebra gives sector patching.
- **Strongest positive survivor:** the two necessary-and-sufficient classifications above.
- **New insight:** changing models does not defeat the obstruction mysteriously; it pays an exact
  price—loss of odd spectral detectability or gain of independent sector patching.
- **Status:** operator half exists in
  `RealCoronaLocalDetectabilityFracture.lean`; generic coefficient-algebra theorem and integrated
  facade remain to be formalized; paper proof is dependency-closed.

## Falsifiers

1. An invariant-domain isometric involution for which the orientation commutator is bounded but
   the odd part is genuinely unbounded, or conversely.
2. A unital function subalgebra containing `χ_S` but unable to patch arbitrary member functions
   across `S`, or having patching without containing `χ_S`.
3. A claimed additional channel that is not a change of operator parity, coefficient patching,
   Real-cyclic parity, or fixed multiplicity enrichment within the declared categories.

## Log

- 2026-08-04 — created in `1-in-progress`.  Literal all-conceivable-model impossibility rejected by
  explicit countermodels; exact evasion classification selected as positive survivor.
- 2026-08-04 — exact projector norm identity and arbitrary unital function-algebra patching
  equivalence proved on paper; hostile domain, constant, algebra, and universality checks passed;
  advanced to `2-fully-proven`.
