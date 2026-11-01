# Hodge theory without varieties over ℤ (HWV) — programme card

- **ID:** hwv-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0111/obstacles-summary.md §2.7
- **Statement:** Build the arithmetic Kähler package on the divisibility–successor complex: links,
  Lefschetz operator, base point, local HR, transport, selection, calibration; prove each part or
  its exact boundary.

## Goal
A fourth producer type (exact local-to-global positivity with nondegeneracy) for Weil's form on
`v₁^⊥`. Lean folder `formal/GaloisForLFunctions/HodgeTheoryWithoutVarieties/`, umbrella
`HodgeTheoryWithoutVarieties.lean`, README there.

## Gates
- [x] 0 → 1  in-progress: README first draft, questions fixed
- [ ] 1 → 2  fully-proven: paper proofs of the pillars below
- [ ] 2 → 3  formalized: every pillar in Lean, module checks clean

## Work plan (modules, in order)
1. `TheKahlerPackage` — HR/strict HR/HL, strictness, deformation on connected spaces, Lefschetz step.
2. `StarsAreLowerHorizons` — prime kernel ratio invariance; prime form on star(d) = horizon ⌊N/d⌋.
3. `TheCountertermIsTheBoundaryFlux` — flux `(λ∗1)(dm) − (λ∗1)(m)`; = log d for Λ; renormalized
   star law; selection: self-similar flux ⇔ λ∗1 completely additive ⇔ tower-constant; twists ⇒ trivial.
4. `StarsOfTheCompleteWeilFamily` — translation invariance ⇒ star(d) at (c,N) = (c⌊N/d⌋/N, ⌊N/d⌋).
5. `TheLinksSplitIntoTowers` — link components = primes; connected over curves.
6. `TheNerveOfTheStarCover` — squarefree complex, reduced Euler characteristic −M(N).
7. `TheLiouvilleProperty` — dilation Liouville; Liouville at edge ⇔ RH; quantitative survivor.
8. `TheLefschetzCandidates` — dilation / overlap flow / coupling Laplacian trichotomy.
9. Deep stars are positive (universal regime transfer through 4).
10. Q2b attempts: shell degree on conductor packets.

## Open mathematical questions (research log of ideas, not results)
- Gluing identity for the star cover.
- Joint shell–pole Poincaré inequality.
- Perron sign structure of zero modes in the Metzler regime.

## Log
- 2026-11-01 — created; README first draft written.
