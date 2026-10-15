# Global equivariant source splitting and coherent resolvents

Status: formalized. Four direct leaf audits, 18 principal axiom audits, local
mathlib name audit, and final repository lint passed.

## Objective

Remove the global extension obstruction between literal Meyer cohomology and its
observable comparison image, without assuming global spectral synthesis. Seek a
generator-equivariant projector that preserves every finite causal Xi packet and
whose kernel is exactly the invisible comparison kernel. Use it to lift arbitrary
observable operators, with their algebraic relations, to actual source classes.

## Corpus inputs

- `DeningerMeyerInvisibleSourceDivisibility`: every shifted invisible generator is
  surjective, including all finite products.
- `DeningerMeyerHedenmalmSourceRealization` and
  `DeningerMeyerFiniteXiCausalSplitting`: actual sources realize Hedenmalm divided
  chains; finite full-jet sections are invariant, faithful, and supported only on
  their prescribed Xi blocks.
- `DeningerDynSysDivisibleExtension`: the arithmetic dynamics route uses Baer
  extension to split divisible subobjects. The needed polynomial-module version
  will be proved, not assumed.
- Installed `Mathlib.Algebra.Module.Injective`, polynomial `Module.AEval`, and
  algebraic closure of the actual scalar field.

## Conjecture loop

1. Ordinary vector-space complement: rejected as insufficient. It need not
   commute with the generator or retain the actual causal chain representatives.
2. Polynomial injectivity: factor every nonzero complex polynomial into linear
   factors. Invisible shift divisibility makes every nonzero polynomial action
   surjective. Each polynomial ideal is principal, so a map from an ideal extends
   by dividing the image of its generator. Baer's theorem gives injectivity.
3. Compatible global splitting: let F be the union of all finite causal ranges.
   Finite source independence and full-jet evaluation give F intersect K = 0,
   where K is the invisible kernel. Both are generator-invariant. Therefore K
   embeds into Q/F as a complex-polynomial module. Extend its identity to Q/F by
   injectivity; pull back to obtain r:Q -> K, with r|K = id and r|F = 0.
   Then P = id - inclusion*r is idempotent, commutes with the generator, has
   kernel K, and fixes every finite causal packet.
4. New solution class: the actual comparison image has a single global section
   supplied by P. Sandwiching any observable endomorphism between this section
   and the comparison map preserves addition, composition, and faithfulness.
   Generator-intertwining operators lift as generator-intertwining actual source
   operators, including operators involving infinitely many observable blocks.
5. Stronger consequence exposed by the construction: on the actual projected
   source subspace, every homogeneous finite-word solution is exactly a finite
   causal Xi packet. At a Xi point outside the word's roots, every linear factor
   is a local analytic unit, so a homogeneous solution has zero jets there.
   Subtract its finite causal projection; the remainder has every Xi jet zero
   and lies in the projected space, hence is zero. Off-divisor shifts are also
   surjective by projecting existing actual causal solutions. Thus all
   off-divisor shifts are bijective on this global actual source subspace, with
   no invisible homogeneous ambiguity. This is an exact spectral construction,
   not a bound or an RH equivalence.
   Their inverses satisfy the exact resolvent identity simultaneously, opening
   a coherent rational operator calculus for all admitted source data.
6. Non-finite witness: the corpus's actual log-Gaussian has nonzero zeroth jet
   at every Xi point. Xi has infinitely many divisor points, while each finite
   causal range vanishes outside finite support. Its global projection therefore
   lies outside every finite causal range.

## Hostile audit and limits

- No claim that K vanishes, that comparison is surjective onto the entire proxy,
  or that the chosen splitting is canonical, continuous, or positive.
- Infinite observable operators must act on the actual comparison image. This
  theorem does not manufacture arbitrary entire-function source admission.
- No continuous dilation action, positive metric, or trace comparison is deduced
  from this algebraic splitting.
- All final source statements must be unconditional. Polynomial factorization,
  divisibility, finite-mode disjointness, and extension are proof obligations.
- No numerical experiments, web searches, new axioms, heartbeat changes, full
  builds, or umbrella builds.

## Verification plan

Check local names in a scratch Lean file, formalize polynomial injectivity and
the compatible splitting, then actual observable operator lifting. Audit each
leaf directly with `lake --old env lean`; audit axioms in scratch; wire leaves
into RHTower; run formal lint; remove only owned scratch artifacts.

## Verified progress

- `DeningerMeyerInvisiblePolynomialInjectivity.lean`: direct leaf audit passed.
  Every nonzero complex polynomial acts surjectively on the actual invisible
  sector; the polynomial action satisfies Baer's criterion and is injective.
- `DeningerMeyerGlobalCausalSplitting.lean`: direct leaf audit passed. A single
  generator-equivariant retraction kills the entire finite causal span. Its
  complementary projector has exactly the invisible kernel and absorbs every
  finite causal projector on both sides.
- Initial formalization failures were elaboration issues (polynomial actions,
  dependent rewriting, explicit quotient parameters); no mathematical premise
  was added to repair them.
- Both audited leaves are wired into RHTower without building the umbrella.
- `DeningerMeyerGlobalObservableSource.lean`: direct leaf audit passed and wired.
  Comparison is bijective on the actual invariant projected subspace. The whole
  observable endomorphism algebra lifts faithfully, preserving composition and
  exact generator commutators, and recovers all old finite source lifts.
  The projected actual log-Gaussian lies outside the union of finite causal
  ranges, so this is not just a finite-mode algebraic model.
- Local mathlib name audit passed against the installed toolchain.
- `DeningerMeyerObservableSourceSpectrum.lean`: direct leaf audit passed without
  warnings. Every finite-word kernel is exactly its finite resonant packet.
  All off-divisor shifts on the actual global source space are bijective, their
  inverses satisfy the exact resolvent identity, and the algebraic spectrum is
  exactly `{rho | xi rho = 0}`. All four leaves are wired into RHTower.

## Contribution and changed frontier

The unknown global invisible sector need not be proved zero before constructing
a faithful, generator-compatible actual source model for every admitted
observable datum. Its causal divisibility makes it an injective complex-polynomial
module. Applying extension after quotienting out the finite causal span splits
off that sector while preserving every original Hedenmalm causal packet.

The resulting source subspace is genuinely global: the projected log-Gaussian
is outside every finite causal range. Its full algebraic spectrum is the actual
Xi zero set. Every homogeneous finite-product equation has precisely its finite
resonant packet of solutions; off-divisor equations have unique solutions, and
the solution operators satisfy the resolvent identity. The whole endomorphism
algebra of the actual comparison image now acts faithfully on this invariant
actual source subspace. This removes the algebraic global extension obstruction;
the remaining questions concern topology, symmetry-compatible choices, metric,
and trace, rather than existence of an equivariant global source section.

## Final audit record

For each of the four leaves, the final direct command was
`lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<leaf>.olean GaloisForLFunctions/RHTower/<leaf>.lean`.
Every command exited 0 with no warnings. No full or umbrella build was run.

A separate scratch audit imported the final spectrum leaf, checked the main
statements, and printed axioms of 18 principal results. Every result used only
`propext`, `Classical.choice`, and `Quot.sound`; no new axiom or admitted proof.
The scratch name audit also exited 0. `git diff --check` passed.

The first repository lint output reported three concurrently created HTGeometry
modules missing umbrella imports. Capturing the complete lint output again after
those external changes settled exited 0, with no errors or diagnostics on the
new leaves. Existing large-file warnings remain. No unrelated module was edited.

Search used the actual Lean corpus and installed dependencies. The main deep
search had complete inventory coverage; compiler metadata was often source-only.
The Gaussian search returned useful hits with a partial local-judge diagnostic.
All used mathematical inputs were inspected in source and checked by Lean.
No numerical experiments, web search, or external novelty audit was used.

Owned scratch audits, search outputs, and lint capture are removed at completion;
the four current compiled leaf artifacts remain for downstream imports.
