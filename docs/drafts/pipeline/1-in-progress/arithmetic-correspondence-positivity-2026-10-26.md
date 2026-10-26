# Arithmetic Correspondence Positivity (ACP)

- **ID:** acp-2026-10-26
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (programme card)
- **Source:** ../../../reports/review-2610/hard-obstacles-summary.md §4 (and §3 Q1–Q3)
- **Statement:** Found the programme `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/`:
  the positivity theory of arithmetic correspondences (dilations, affine maps, the archimedean
  flow), their graphs, degrees, budgets and Rosati traces; which layers of Weil's proof exist over
  `ℤ`, which are free, which are provably absent.

## Goal
Answer §4.4 questions 1–10 and §3 Q1–Q3 with unconditional Lean theorems (sharp theorems or
sharp no-gos with positive survivors); build the §4.5 tools; foundational README.

## Gates
- [x] 0 → 1  report read; sibling programmes surveyed (ACS, AOG, APD, ACG, MPG, SBWF, AKT)
- [x] 1 → 2  paper proofs of pillars P1–P8 (in module docstrings)
- [x] 2 → 3  16 modules (P1–P16) checked with `lake --old env lean`, wired into the umbrella and
  `MainTheorems`; axiom audit of 37 key theorems: only `propext`, `Classical.choice`, `Quot.sound`

## Approach (pillars, in order)
1. Normalized graphs on polar surfaces / scaling data: `N(y) = y + (1 − y·V)H + β(y)V`,
   `N(y)·V = 1`, `N(y)² = 0`, `deg N(y) = δ(y,y)/2`; theorem of the square is an identity;
   degree form on the correspondence algebra = Rosati trace / 2; ℤ: RH ⇔ every normalized Hecke
   graph has degree ≥ 0; genus one: ACS `graphCycle m n = N(mΔ − nΓ_F)`; golden: TOS holds, deg −1.
   Answers Q3 / §4.4.2: TOS is free, carries no budget.
2. Kernel counts vs Rosati: determinant degree `Π_i P(α_i)` on curve data; multiplicative;
   ≥ 0 for all real `P` when no eigenvalue is real; genus ≥ 2 impure datum with only complex
   quartets passes every degree test; real off-line pairs are detected. Over ℤ off-line candidates
   are non-real, so kernel-count effectivity is blind to them; the sign must be Rosati (trace).
3. Local hyperbolic geometry of reflection pairs: local form signature (1,1) (complex) / (2,2)
   (real); Hecke symbols are boosts off line, rotations on line; positive boost-invariant subspaces
   are isotropic; phase law for reflection-symmetric real carriers.
4. Aperture carriers: full fibres at every finite point set (interpolation), positivity at small
   aperture: positivity beyond isotropy exists but does not localize.
5. Budget law: similitude ⇒ fixed budget; sufficiency ⇔ Weil-plane positivity; budget = rank over 𝔽_q.
6+. Charged positivity, coupling, oscillatory capacity, escape, base, selection, shared budget.

## Log
- 2026-10-26 — created; survey of ACS/AOG/APD/ACG done; another agent is extending APD
  (`AContinuousArchimedeanSpectrumIsSeenByTheSuccessor`), so archimedean–finite coupling is cited,
  not duplicated.
- 2026-10-26 — P1–P16 checked clean; a parallel agent added P17
  (`SymmetricSquareContractionsAndExteriorCounts`: exterior-power kernel counts force unitarity). Escape states are developed by ACG/ADR agents
  (EscapeStatesAreSpectralMeasuresOnTheGaugeTorus) — cite, do not duplicate.
- Open: first gauge-charged window (odd 181/500 vs the 2-flipped twin); localizing carrier with
  elliptic local symmetry; Rosati-type effectivity from counts; W8 / escape completeness.
