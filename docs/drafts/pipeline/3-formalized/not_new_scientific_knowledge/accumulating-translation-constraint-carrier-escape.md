# Accumulating translation constraints must escape every fixed DA carrier

- **ID:** `accumulating-translation-constraint-carrier-escape`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** GENERAL HT THEOREM / CONSTRAINT-COMPLEXITY ESCAPE / BRIDGE
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED SCHWARTZ REALIZATION]
  [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/SchwartzTranslation.lean`
- **Parents:**
  - `../../2-fully-proven/not_new_scientific_knowledge/ht-exact-da-translation-stabilizer.md`
  - `../../2-fully-proven/not_new_scientific_knowledge/mertens-logarithmic-corona-differential-tower.md`
- **Statement:** If translation defects of an analytic source at nonzero steps accumulating at zero
  all lie in one fixed closed linear carrier, then the infinitesimal derivative lies in that
  carrier.  Consequently an entire hypertranscendental function may have dense or accumulating DA
  translation defects only if their DA carrier complexity escapes every fixed finite-dimensional
  model.

## 1. General analytic theorem `[PROVED]`

Let `Hol(C)` carry the compact-open topology.  Let `f` be entire, let `h_n!=0` with `h_n->0`, and
let `V subset Hol(C)` be a closed complex-linear subspace.  If

```text
f(.+h_n)-f(.) in V                                      (1)
```

eventually, then

```text
f' in V.                                                (2)
```

Indeed, linearity gives

```text
(f(.+h_n)-f(.))/h_n in V.                               (3)
```

Taylor's theorem, uniformly on every compact set, makes `(3)` converge to `f'` in the compact-open
topology.  Closedness of `V` gives `(2)`.

### HT carrier-escape corollary

Suppose `f` is hypertranscendental over `C(z)`.  There cannot exist a nonzero sequence `h_n->0`
and one fixed finite-dimensional space `V` of differentially algebraic meromorphic functions such
that every defect in `(1)` belongs to `V`.

Finite-dimensional subspaces of a Hausdorff topological vector space are closed, so the theorem
would give `f' in V`.  The DA functions form a differential field and are closed under finite
linear combinations, hence `f'` would be DA.  Then `f` would also be DA: any algebraic differential
equation for `f'` becomes one for `f` after shifting every derivative index by one.  This
contradicts hypertranscendence.

Thus a dense DA translation stabilizer is compatible with HT only through complexity escape.  The
constraints may accumulate, but their carriers cannot remain uniformly finite.

## 2. Lean-formalized Schwartz source theorem

The existing HTGeometry translation module proves strong differentiability of the full Schwartz
translation orbit:

```text
(T_(a+h)f-T_a f)/h -> T_a(f')                           (4)
```

in every Schwartz seminorm.  The new declarations are:

- `SchwartzMap.translatedDeriv_mem_of_eventually_increment_mem`;
- `SchwartzMap.translatedDeriv_mem_of_accumulating_increment_mem`.

They prove that if the increments in `(4)` lie eventually in one fixed closed real-linear
Schwartz submodule `W`, either for all sufficiently small nonzero `h` or along one nonzero sequence
`h_n->0`, then

```text
T_a(f') in W.                                           (5)
```

This is not an abstract wrapper: it consumes the already formalized `O(|h|)` control in every
Schwartz seminorm and its strong-orbit limit.

## 3. Meaning for the nature of constrained HT functions

This theorem separates two notions which the RH attacks repeatedly conflated:

```text
many exact constraints
  !=
one bounded-complexity generative rule.                 (6)
```

An HT function may have:

- a nontrivial or even dense DA translation stabilizer;
- exact difference equations at arbitrarily small steps; and
- source relations of low generator rank.

What it cannot have along an accumulating family is one fixed closed finite-dimensional DA carrier
containing every defect.  The positive invariant is therefore not merely the set of admissible
shifts.  It must record how the constraint carrier grows as the shift approaches the identity.

This supports the following research object:

```text
[CONJECTURE -- OPERATOR-GROWTH PROFILE]
```

For a source-minimal constrained HT function, attach to every source operator or translation step
the smallest closed DA carrier containing its defect, together with the induced boundary-symbol
filtration.  Hypertranscendence is reflected by cofinal nontermination of this profile: no
source-faithful gauge makes all sufficiently fine constraints land in one fixed finite carrier.

The Mertens differential-corona tower supplies one exact model: multiplication by `log p` raises
the Marcinkiewicz grade forever.  The Gamma conormal supplies a second: one cyclic source relation
has a nonzero rank-one boundary symbol at every jet clock.  The factorial-frequency entire example
in the first parent supplies a third: DA defects occur at rational steps tending to zero, but their
minimal exponential-polynomial order diverges.

## 4. RH-route consequence and positive salvage

The failed idea was to repair positive-shift corona blindness by putting every finite
differential-translation defect into one fixed completion.

The theorem shows why that is structurally wrong beyond this one RH route: an accumulating
source-operator family in a fixed closed carrier collapses to an infinitesimal relation.  For a
genuinely HT source, a viable Euler--Gamma comparison must therefore be projective/graded or
singular, with complexity escaping through the boundary.  This is a positive general-HT theorem,
not merely a negative statement about RH.

It still does not supply zero localization.  Complexity escape explains the required type of
comparison object; it does not force the FE and Schwarz support points to coincide.

## 5. Parent-theory and novelty verdict

Difference quotients converging to derivatives in compact-open or Schwartz topology, closure of
finite-dimensional subspaces, and closure properties of DA functions are established analysis and
differential algebra.  The exact synthesis is useful, but it is a direct parent consequence.
Therefore the theorem is `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

The potentially new content is the operator-growth profile as a source invariant, especially if
one proves source-equivalence invariance, a minimality theorem, and a nontermination criterion for
a nontrivial class beyond the present examples.

## 6. Verification

Targeted verification only:

```text
lake env lean GaloisForLFunctions/HTGeometry/SchwartzTranslation.lean
lake build +GaloisForLFunctions.HTGeometry.SchwartzTranslation
```

Both passed.  A scratch `#print axioms` audit reports only
`[propext, Classical.choice, Quot.sound]` for both new declarations.

## Gates

- [x] compact-open analytic theorem proved
- [x] HT finite-carrier escape corollary proved
- [x] Schwartz strong-orbit realization formalized in Lean
- [x] accumulating-sequence form formalized in Lean
- [x] every no-go supplied a positive general-HT statement
- [x] parent-theory gate run conservatively
- [ ] define a source-equivalence-invariant operator-growth profile
- [ ] prove minimality for Gamma, Mertens, or a non-affine HT source
- [ ] test whether DA sources are exactly the eventually terminating profiles in a regular class

