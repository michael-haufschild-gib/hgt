# Euler--Wick sign-gauge interaction cohomology

- **ID:** euler-wick-sign-gauge-interaction-cohomology
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` question 28; corpus bridge from raw Euler Wick defect to finite-quotient interaction cohomology
- **Statement:** The two-leg sign-gauge orbit of the raw four-factor Euler Wick defect canonically generates the full `Fin 2 × Fin 2` joint-observable quotient modulo row and column marginals, is invariant under every marginal counterterm, and vanishes exactly on the four local coordinate hyperplanes.

## Goal

Answer frontier question 28 with a coefficient-faithful source invariant that survives the collapse of nonlinear and tangent higher grades to grade one.  The target is not a renamed scalar obstruction: the raw Euler coefficient packet itself must induce the quotient class, and the class must exhaust the unique mixed direction without any Xi-divisor, RH, zero-location, positivity, or source-order premise.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, exact leaf `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact conjecture `[EWIC-1]`

Let `D(a)` be the raw squarefree Euler four-point Wick defect, so the existing corpus proves

`D(a) = -2 a₀ a₁ a₂ a₃`.

Let `ε : Fin 2 → ℂ` equal `1` at the distinguished anchor `1` and `-1` at `0`.  Define the actual two-leg gauge orbit

`G_a(x,y) = D(a) ε(x) ε(y)`

and take its canonical anchored mixed part

`I_a(x,y) = G_a(x,y) - G_a(x,1) - G_a(1,y) + G_a(1,1)`.

Conjecture:

1. `I_a(x,y) = D(a)(ε(x)-1)(ε(y)-1)`.
2. `I_a` lies in the anchored interaction complement and its quotient class is unchanged after adding any row-plus-column observable.
3. `[I_a] = 0 ↔ D(a)=0 ↔ a₀a₁a₂a₃=0`.
4. If all four Euler coefficients are nonzero, `[I_a]` spans the entire `Fin 2 × Fin 2` interaction cohomology, whose complex dimension is exactly one.

## Why this attacks a frontier obstruction

AGC collapse says scalarization through grade-one or marginal data erases nonlinear/tangent higher grades.  The joint-observable quotient is designed to erase exactly the two marginal spaces while retaining their mixed incidence.  `[EWIC-1]` would identify a natural raw Euler observable—not an arbitrary complement vector—whose surviving class is both coefficient-faithful and complete in the first nontrivial quotient.  This supplies an exact detector class for the mixed-incidence and higher-grade-survival obligations shared by AGC, Q, HC, PLAC, and EPC.  It does not yet prove the global order or receiver-landing theorem.

## Anti-theatre / kill criteria

Kill this bridge if any of the following occurs:

- the class is defined by inserting `D(a)` into a preselected basis rather than by the gauge orbit and canonical mixed-part operation;
- nonvanishing needs any hypothesis beyond the already classified local degeneracy locus;
- marginal neutrality is merely asserted for one chosen counterterm instead of the full marginal submodule;
- the spanning result does not identify the whole one-dimensional quotient;
- the construction factors through either single gauge leg, in which case it is grade-one data in disguise.

## Approach

Use `EulerSquarefreeWickDefect` for the literal source scalar and `CoprimePrimeResidueInteraction` for the canonical row/column/anchored decomposition.  Package the anchored observable inside `ClassInvariantRestricted (productFstSetoid ⊓ productSndSetoid)`, map it to `FiniteQuotientInteractionCohomology`, prove its exact kernel by the marginal/anchored disjointness theorem, then combine nonvanishing with the existing dimension-one formula to prove generation.

## Conjecture loop

- **C1:** Hall visible-kernel recovery solves Route E neighbor expansion. **FAIL/PIVOT.** Generic quotient injectivity is Hall's missing condition in another form; no automatic graph expansion follows from the QEC theorem.
- **C2:** Chern--Simons/Wilson secondary holonomy solves PCS zero-index blindness. **FAIL/PIVOT.** Wilson holonomy supplies a homological detector, but no corpus theorem forces its completed Euler-source class to vanish precisely in the right strip.
- **C3:** Rainich square reconstruction linearizes Route O determinant positivity. **FAIL/PIVOT.** Corpus has forward Rainich identities but no inverse source reconstruction; Route O is also inside the excluded classical operator family.
- **C4:** Raw Euler Wick defect becomes a canonical sign-gauge interaction class solving AGC's detector problem. **ACTIVE.** Strong anti-theatre target is `[EWIC-1]` above.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** active

## Log

- 2026-08-21 — Created directly in stage 1 after whole-corpus search and three explicit bridge kill tests. Scratch formalization started; frontier map remains read-only.
