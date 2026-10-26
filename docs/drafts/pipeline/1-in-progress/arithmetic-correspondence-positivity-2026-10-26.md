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
- [x] 2 → 3  W8 / Q1 and the remaining §4.5 tools: 13 modules (P18–P24, P26–P30, P32) checked,
  wired; P5 extended by the two-sided defect bound (B3.29); axiom audit of 44 headline theorems: only
  `propext`, `Classical.choice`, `Quot.sound`

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
- 2026-10-26 — W8 done (P18 translation Gram, P19 Laplace symbol `G`); Q1 answered for dominant
  configurations (P20 phase kernels of rank = number of zeros, P24 transfer to power rows), with
  P21 (horizon averages select zeros), P22 (dilation = archimedean flow on escape states),
  P23 (family averages lose linearly). Q1 residual for `ζ`: the explicit-formula split of the
  profile with symbol `G` (growth of `1/ζ(s+ε)` between zeros).
- 2026-10-26 — P32: the successor defect in the strip, `|D_Λ(σ+it)| ≪ (|t|+1)^{1−σ+η}` (B3.29). A
  parallel agent added P31 (intrinsic exterior obstructions).
- 2026-10-26 — P30: the Stepanov count (one-sided prime-power bound) is RH; Hecke auxiliaries kill
  only critical symbols (B3.30 settled as a strength statement).
- 2026-10-26 — P29: a section count with Riemann–Roch and Bézout is the Hodge index (RH over `ℤ`,
  purity over `𝔽_q`); each axiom alone is free (B3.5 settled as a strength statement).
- 2026-10-26 — P28: the escape alternative (RH ⇔ no escape; escape set = `(0, Θ−½]` up to a
  countable set); P5 sharp on the real axis. README §9 restated with proved statuses.
- 2026-10-26 — P27: the escape-completeness criterion in ADR's normalization (W7 ix), with the
  vanishing critical kernel. P26: summable infinite configurations are complete (Bohr uniqueness); P5 bound
  `|D_Λ(s)| ≤ |s||ζ′/ζ(1+σ)|`. A parallel agent added P25 (`ExteriorAndHeightCoupledQuartetContractions`).
- Open: first gauge-charged window (odd 181/500 vs the 2-flipped twin); localizing carrier with
  elliptic local symmetry; Rosati-type effectivity from counts; the explicit-formula split;
  non-summable dominant configurations; the non-attained abscissa.
