# The Tensor-Power Programme Ω (TPP) — programme card

- **ID:** TPP
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-1511/obstacles-summary.md §2.22 (best-shot proof route: the tensor-power programme Ω)
- **Statement:** carry Deligne's tensor-power argument to `Spec ℤ`: dissect the pole law (step iii), prove
  where it is missing, price every substitute frame, decide the pencil candidates, write the axioms of N1.

## Goal
Answer README §6 questions Q1–Q9 by Lean theorems; build the tools of README §7. Folder
`formal/GaloisForLFunctions/TensorPowerProgramme/`, umbrella `TensorPowerProgramme.lean`, README there.

## Corpus already owns (do not redo)
- Rankin/global-trace step over `𝔽_q`: AKT `tensor_moment_bound_iff`, `tensor_norm_pow_le_of_global_trace`.
- SL₂ invariants have det weight; golden Frobenius has a split SL₂ lift (AKT).
- Receiver-level tensor loss: linear loss = strip, fixed loss = RH (ACP `TheBaseIsAFixedLoss`); prime-trace
  moments ⇔ RH (SurfaceOfSpecZ `riemannHypothesis_iff_moments_primeTraces`).
- Family moments and fixed parts (IRP `member_norm_le_of_family_moments`).
- Frames, towers, walls, sign line, Stickelberger prices (FCT, EDCS); cubic correction = rung at 6s−3 (EDCS).

## Lean modules [L]
TheTensorMomentsOfAFlowDatumHaveBaseLossExactlyOne, AnAbelianBaseIsARuler,
APolarizedBaseWhoseAdamsSquaresContinueIsPure, TemperedIsTheUniformTopBound,
TheAxiomsOfAPencilThroughZeta, TheThreeLinesOfFrames.

## Status
- Flow data over Spec ℤ: k-th tensor moment converges iff σ > 1 + 2kW (base loss exactly 1); coinvariant
  expansion into shifted −ζ'/ζ; edge residue = sum of squares > 0; pole law ⇔ W ≤ w₀.
- Abelian bases (IsAbelianBase: characters + PNT package + independence): same exact law; Dirichlet
  twists of any modulus instantiate it (Q4b verdict: twist family is a ruler).
- Polarized base: continuation of Rankin–Selberg squares of Adams powers to Re s > 1 ⇒ purity (Landau +
  power-sum rigidity); rank two: p_m² = p_{2m} + 2 reduces to the Adams package (Langlands–Serre form).
- Tempered ⇔ top bound 1 for every Adams power (Q7 first clause).
- PencilThroughZeta (N1 axiom list): pencil ⇒ RH (Landau + one-cycle law at a prime); ∃ pencil ⇔ RH,
  so N1's content is a parameter-blind source of the pole law.
- Three lines: half unit; one Deligne lever ⇒ RH; sign levers at all large periods ⇒ RH; completion
  centres ↑ 2/3.

## Open
Q1 Kummer in this language; Q4c Hecke (ℚ(ω), infinity type) abelian base; Q5 A₂ Stickelberger price,
sign-line completion k ≥ 7; Q6 dual series of the cubic probe; Q7 conductor growth; Q9 in general.

## Conjecture loop (ledger)
| # | Conjecture | Test | Status |
|---|---|---|---|
| C1 | Flow data: moment abscissa exactly 1 + 2kW (no cancellation at the edge) | −ζ'/ζ pole + residue = Σ‖·‖² | **[L]** summable_flowMomentTerm_iff |
| C2 | Abelian bases (characters with PNT) are rulers with the same law | linear independence of characters | **[L]** summable_twistMomentTerm_iff |
| C3 | Polarized base + continuation of Adams squares ⇒ purity | Landau (HTGeometry) + power sums | **[L]** norm_eq_one_of_adamsPoleLaw |
| C4 | Tempered ⇔ uniform top bound 1 of Adams powers | converse via base convergence | **[L]** adamsPoleLaw_iff |
| C5 | Pencil axioms ⇒ RH; axioms ⇔ RH (trivial one-point pencil) | one-cycle law zeta_exists_universal_lefschetz_growth | **[L]** riemannHypothesis_iff_nonempty_pencil |
| C6 | One Deligne lever ⇒ RH; sign levers at all periods ⇒ RH | covering levers | **[L]** riemannHypothesis_of_deligneLever |

## Log
- 2026-11-15 — created; README; modules C1–C6 formalized.
