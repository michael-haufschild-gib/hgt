# Wasserstein barycenter of positive definite operators (Kim–Mer–Pálfia, arXiv:2607.29142)

- **ID:** kmp-2026-wass-barycenter
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** arXiv:2607.29142v1 (31 Jul 2026), `W_M_of_positive_operators_V16.tex`
- **Statement:** Formalize, unconditionally and closed, every lemma/theorem/provable proposition of
  the paper that mathlib and the hgt corpus do not already own.

## Goal
Full Lean 4 formalization of the operator-level Bures–Wasserstein barycenter theory:
existence/uniqueness of the Wasserstein mean of positive definite operators, its ODE/no-dice/SLLN
approximation theory, and its order/norm inequalities.  Along the way the corpus gains a reusable
C*-algebraic **operator geometric mean** layer (`#`, `#_t`, Riccati, congruence, self-duality,
joint concavity, AM–GM–HM), which mathlib does not have.

## Corpus/mathlib audit (2026-08-22)
- mathlib v4.32.2 **has**: `CFC.sqrt`, `CFC.rpow`, `CFC.nnrpow`, `CFC.conjSqrt`,
  `CFC.monotone_sqrt`, `CFC.monotone_rpow` (p∈[0,1]), `CFC.concaveOn_sqrt`, `CFC.concaveOn_rpow`,
  `CStarAlgebra.ringInverse_le_ringInverse` (antitone inverse), `IsStrictlyPositive`.
- mathlib **lacks**: operator geometric mean `A # B`, weighted `A #_t B`, Riccati characterization,
  congruence invariance, self-duality, AM/GM/HM chain, joint concavity, Kubo–Ando means,
  Wasserstein/Karcher/power means, Bures–Wasserstein distance of operators.
- hgt corpus **has**: `positiveMatrixGeometricMean` (matrices only, `HTGeometry/
  ConstitutivePositiveConeMidpointRecovery.lean`), Bures *reporter/minimax* laws (unrelated),
  `kantorovichRubinstein` (W1 dual, unrelated).
- hgt corpus **lacks**: everything operator-geometric-mean and Wasserstein-mean related.

## Paper inventory (target list)
Sec 2: Thm 2.1 (Gelbrich/MPZ), Def 2.2, Thm 2.3 (Minh) — *cited literature, not proved in paper*.
Sec 3: Thm 3.1 (min problem), **Thm 3.2** (strict concavity of `tr_ex ∘ sqrt`), **Lem 3.3** (order
bounds on fixed points), **Lem 3.4** (homogeneity), Thm 3.5 (IFT, cited), Thm 3.6, Cor 3.7, Thm 3.8,
Cor 3.9, **Lem 3.10** (`‖AYB‖²` two-sided spectral bounds), **Lem 3.11** (`⟨DΦ(X)Y,Y⟩ ≥ α³/2β⁴‖Y‖²`),
Thm 3.12, Rmk 3.13, **Lem 3.14** (iso ↔ adjoint iso), **Thm 3.15** (`AYA+BYB+CYC` iso), Thm 3.16.
Sec 4: Rmk 4.1, Thm 4.2 (cited OP), **Lem 4.3** (renorming / logarithmic norm), Prop 4.4,
Thm 4.5 (Banach–Finsler contraction), **Lem 4.6**, **Lem 4.7** (flow invariance of `[αI,βI]`),
Cor 4.8, **Lem 4.9/4.10** (Taylor), **Lem 4.11/4.12**, Cor 4.13, **Prop 4.14**, **Prop 4.15**,
**Thm 4.16** (No-dice).
Sec 5: Thm 5.1, **Lem 5.2** (Etemadi weight recursion), Thm 5.3 (SLLN).
Sec 6: **Prop 6.1** (1)–(5)+fixed point, **Thm 6.2** (Loewner bounds), **Cor 6.3**, Cor 6.4
(Lie–Trotter), **Thm 6.5** (norm bounds), Rmk 6.6, **Thm 6.7**, **Thm 6.8** (power mean),
**Thm 6.9** (block-matrix minimum), **Lem 6.10** (`A◇_t B = B◇_{1-t} A`), **Thm 6.11**,
**Thm 6.12**, **Thm 6.13**, **Cor 6.14**, **Prop 6.15**, **Lem 6.16** (Kantorovich converse AM–GM),
**Thm 6.17** (near-order two-sided comparison with dual).

## Module plan (`formal/GaloisForLFunctions/HTGeometry/BuresWasserstein/`)
1. `OperatorGeometricMean.lean` — `CFC.wgm t a b`, `CFC.gm`, Riccati + uniqueness, symmetry,
   congruence invariance, self-duality, monotonicity, max characterization, AM/GM/HM,
   joint concavity, `X A⁻¹ X` joint operator convexity.
2. `WassersteinEquation.lean` — `IsWassersteinPoint`, equivalence of the two forms of (gradF),
   Lem 3.3, Lem 3.4.
3. `SqrtStrictConcavity.lean` — Thm 3.2 operator core (equality case of operator concavity of sqrt).
4. …further modules per section.

## Log
- 2026-08-22 — created; paper downloaded to `scratchpad/paper/`; corpus + mathlib audit done.
