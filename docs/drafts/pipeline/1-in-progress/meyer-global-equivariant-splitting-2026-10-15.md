# Global equivariant source splitting

Status: conjecture and dependency-closed paper proof; Lean audit pending.

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

## Hostile audit and limits

- No claim that K vanishes, that comparison is surjective onto the entire proxy,
  or that the chosen splitting is canonical, continuous, or positive.
- Infinite observable operators must act on the actual comparison image. This
  theorem does not manufacture arbitrary entire-function source admission.
- All final source statements must be unconditional. Polynomial factorization,
  divisibility, finite-mode disjointness, and extension are proof obligations.
- No numerical experiments, web searches, new axioms, heartbeat changes, full
  builds, or umbrella builds.

## Verification plan

Check local names in a scratch Lean file, formalize polynomial injectivity and
the compatible splitting, then actual observable operator lifting. Audit each
leaf directly with `lake --old env lean`; audit axioms in scratch; wire leaves
into RHTower; run formal lint; remove only owned scratch artifacts.
