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
TheAxiomsOfAPencilThroughZeta, TheThreeLinesOfFrames, TheCalibrationCurvesArePureByTheirPairing,
ThePrimeNumberTheoremOfTheCharactersGivesTheirIndependence,
TheEulerLogarithmDifferentiatesToThePrimePowerSeries, TheAnglesOfTheEisensteinFieldAreAnAbelianBase,
TheGaussPairingsMeetTheSignLineOnlyAtTheEuclideanSignatures, ThePrimeTraceMomentsOfZetaReadTheWidthWithBaseLossAtMostOne,
FiniteMonodromyIsARuler.

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
- Calibration curves: ‖J(χ,φ)‖² = q by identity of the two pairings; Gauss triples priced k/2 (sign line).
- PNT of the characters ⇒ their independence; −L'/L of a number-field Euler product = prime-power series;
  angle characters ψ₆^j of ℚ(ω) form an abelian base (ζ_K = ζ·L(χ₋₃) at j = 0, Grössencharacter
  L-functions at j ≠ 0) ⇒ ruler.
- Gauss pairings vs sign line: c ≥ k/2; c = k/2 ⇒ k ∈ {3,4,6} (Euclidean signatures (3,3,3), (2,3,6),
  (2,4,4)); signature weight ∈ {1/2} ∪ [7/10, ∞), gap sharp at (2,5,10) on ZMod 11. Stage 2 in the Gauss
  family fails: no Gauss sign lever at k = 5 or k ≥ 7.

## Open
Q5 A₂ Stickelberger price, sign-line completion k ≥ 7 outside the Gauss family; Q6 dual series of the
Q6 answered by the corpus (correctionAbscissa_eq: exact transport is a ruler); Q7 conductor growth; Q9:
sources with infinite non-abelian monodromy on the parameters. Peer module AWallAboveOneHalfIsAWorldOffTheLine
(not mine, unwired) has isLever_signLever_iff.

## Conjecture loop (ledger)
| # | Conjecture | Test | Status |
|---|---|---|---|
| C1 | Flow data: moment abscissa exactly 1 + 2kW (no cancellation at the edge) | −ζ'/ζ pole + residue = Σ‖·‖² | **[L]** summable_flowMomentTerm_iff |
| C2 | Abelian bases (characters with PNT) are rulers with the same law | linear independence of characters | **[L]** summable_twistMomentTerm_iff |
| C3 | Polarized base + continuation of Adams squares ⇒ purity | Landau (HTGeometry) + power sums | **[L]** norm_eq_one_of_adamsPoleLaw |
| C4 | Tempered ⇔ uniform top bound 1 of Adams powers | converse via base convergence | **[L]** adamsPoleLaw_iff |
| C5 | Pencil axioms ⇒ RH; axioms ⇔ RH (trivial one-point pencil) | one-cycle law zeta_exists_universal_lefschetz_growth | **[L]** riemannHypothesis_iff_nonempty_pencil |
| C6 | One Deligne lever ⇒ RH; sign levers at all periods ⇒ RH | covering levers | **[L]** riemannHypothesis_of_deligneLever |
| C7 | Calibration eigenvalues pure by the pairing identity; Gauss triple on the sign line | Jacobi-sum identities, Stickelberger | **[L]** norm_jacobiSum_sq, stickelbergerPrice_jacobiTriple |
| C8 | PNT of the characters ⇒ linear independence | residues as s ↓ 1 | **[L]** linearIndependent_of_pnt |
| C9 | −L'/L of a number-field Euler product is the prime-power series | termwise derivative of Σ −log(1 − c N^{−w}) | **[L]** neg_deriv_div_eq_primePowerSeries |
| C10 | Angle characters of ℚ(ω) form an abelian base | Grössencharacter L nonvanishing on Re ≥ 1; ζ_K = ζ L(χ₋₃) | **[L]** isAbelianBase_angle |
| C13 | Cost theorem of the Gauss family: c = k·w(S) + Σ_rows (k/m − 1); c ≥ k/2 + 1 off {3,4,6}, sharp at k = 8 | row slack | **[L]** half_period_add_one_le_pairingC |
| C12 | Finite monodromy (Chebotarev classes) ⇒ ruler | fibres = abelian bases with trivial character group | **[L]** summable_classMomentTerm_iff |
| C11 | Gauss pairings never below the sign line; on it only at k ∈ {3,4,6}; hyperbolic gap 1/5 | signature weight, orbifold parity | **[L]** half_period_le_pairingC, signatureWeight_dichotomy |

## Log
- 2026-11-15 — created; README; modules C1–C6 formalized.
- 2026-11-16 — C7–C13 formalized; paused by user.
