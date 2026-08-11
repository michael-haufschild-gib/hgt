# Deninger rational-Witt sheaves literature-to-Lean parity

- **ID:** `deninger-rational-witt-sheaves-literature-to-lean-parity`
- **Stage:** 1-in-progress
- **Type:** PRIMARY-LITERATURE COVERAGE AUDIT
- **Route:** L — rational-Witt source foundation
- **Primary source:** Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  arXiv:2508.05329v1 (7 August 2025).

## Why this is on Route L

The paper is newer than the rational-Witt implementation used by Route L and proves structural
facts about the exact source functor: localization, Galois descent, sheafification, the
Hazewinkel ind-ring scheme, and finite-correspondence interpretation.  These are source
theorems, not optional analogies.

## Primary-source theorem inventory

The v1 source contains thirty theorem-level declarations:

- §1: three propositions, six theorems, three corollaries, and one lemma, including Proposition
  1.1 and Theorem 1.2.
- §2: two propositions, two lemmas, one theorem, and one corollary.
- §3: two propositions and two theorems, including Theorems 3.3 and 3.4.
- §4: six propositions, three corollaries, and one theorem/corollary chain for sheafified reduced
  monoid algebras and rational Witt vectors.
- §5: one theorem and one proposition identifying rational Witt vectors of a normal domain with
  universally integral finite correspondences.

Exact numbering/statements are being transcribed from arXiv source.  Each result will receive a
closed arithmetic specialization before Route L returns to conjectural frontier work.

## Confirmed corpus gap

`DeningerRationalWittFiniteEvaluationBridge.lean` defines
`DeningerPrimeComplexifiedRationalWittPresentation` to be the complex monoid algebra of
algebraic-closure units and cites the published identification with `W_rat`.  It does not define
the rational Witt ring or prove that identification.  Therefore the 2025 source theorems are not
formalized by the existing `Presentation` abbreviation.

## Newly closed presentation theorem

`DeningerRationalWittCyclotomicExhaustion.lean` proves two global facts that the previous finite
packet modules did not provide:

- every unit of `AlgebraicClosure (ZMod p)` has finite order prime to `p`, hence lies in one of the
  chosen finite cyclotomic root embeddings;
- every element of the full complexified monoid-algebra presentation, and every
  arithmetic-Frobenius-fixed element, descends to one finite cyclotomic stage (fixed at that stage
  in the latter case).

These are closed arithmetic theorems about the concrete presentation and remove a real gap between
the finite packet tower and its global union.  They do **not** identify that presentation with
literal `W_rat(AlgebraicClosure (F_p))`, so they do not count as Proposition 1.1, Theorem 1.2, or
any other 2025 rational-Witt theorem.

`DeningerRationalWittGaloisFixedDescent.lean` now closes the next presentation-level gap.  It proves
that every absolute Galois automorphism agrees with one arithmetic Frobenius power on any finite
cyclotomic stage, using restriction to a finite intermediate field.  Combining this with global
cyclotomic exhaustion gives the unconditional equivalence

`Frobenius(w) = w ↔ ∀ g ∈ Gal(AlgebraicClosure(F_p)/F_p), g(w) = w`.

This is the perfect-prime-field Galois fixed-point theorem on the concrete complexified
monoid-algebra presentation.  It is not yet the paper's literal equality with `W_rat(F_p)` because
the missing rational-Witt comparison is logically prior.

## Formalization order

1. Define the big rational-Witt subring using localized polynomials/power series and its Teichmüller
   map.
2. Prove the closed `Spec ℤ` localization instance of Proposition 1.1.
3. Construct the literal rational-Witt comparison and transport the now-proved presentation-level
   absolute-Galois fixed-point equality across it.
4. Replace presentation-only claims in finite packet modules by comparison maps to the constructed
   rational-Witt ring.
5. Formalize the sheaf and correspondence theorems in source order.

## Log

- 2026-08-11 — primary arXiv search located this 2025 paper; existing Route-L map did not cite it.
  Initial audit found that the corpus names a rational-Witt presentation but does not construct
  `W_rat` or prove the new paper's comparison theorems.
- 2026-08-11 — proved global finite-stage exhaustion and fixed finite-stage descent for the
  complexified arithmetic-closure monoid-algebra presentation.  Literal rational-Witt comparison
  remains the source-level blocker.
- 2026-08-11 — proved that arithmetic-Frobenius invariants in the full presentation are exactly
  absolute-Galois invariants.  Proof passes through finite intermediate fields and uses no descent
  hypothesis; transport to literal `W_rat` remains open.
