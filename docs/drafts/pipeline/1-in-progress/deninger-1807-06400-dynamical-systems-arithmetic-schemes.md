# Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4) — full Lean formalization

- **ID:** deninger-1807-06400
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** arXiv:1807.06400v4 (Feb 2024), C. Deninger, math.DS/math.AG
- **Statement:** Formalize unconditionally in Lean 4 every lemma / proposition / theorem of the
  paper whose content is not already owned by mathlib or by this corpus.

## Goal
Bring the whole "rational Witt space" programme (sheafified rational Witt vectors, the
`Q^{>0}`-spaces `\check X(C)`, the `R^{>0}`-dynamical systems, the `p`-adic subsystem `\hat Y`,
and the relation to the Fargues–Fontaine curve) into the corpus as closed Lean theorems.

## Paper inventory (78 numbered results, 15 sections)
| § | results | notes |
|---|---|---|
| 1 Rational Witt vectors | Prop 1.1–1.3, Thm 1.4, Cor 1.5, Lem 1.6, Cor 1.7, Thm 1.8 | corpus already owns large parts of 1.1/1.2/Fatou |
| 2 Rational Witt spaces | Prop 2.1, Def 2.2/2.3/2.5, Prop 2.4 | scheme/ringed-space layer |
| 3 C-valued points | Cor 3.1–3.3, Prop 3.4, Def 3.5, Prop 3.6, Cor 3.7 | |
| 4 Character classes | Def 4.1, Prop 4.2, Lem 4.3, Cor 4.4, Prop 4.5, Lem 4.6 | 4.3 and 4.6 are pure algebra |
| 5 Q^{>0}-orbits | Prop 5.1, Thm 5.2, Lem 5.3, Thm 5.4 | |
| 6 R^{>0}-system | Thm 6.1 | |
| 7 Topology | Lem 7.1–7.3, Prop 7.4–7.7, Cor 7.8/7.9, Thm 7.10 | 7.7 pure metric geometry |
| 8 Closure of periodic orbits | Claim 8.1 (conjectural), Thm 8.2, Lem 8.3 | Thm 8.2 conditional on Claim 8.1 in dim ≥ 2 |
| 9 Connectedness | Prop 9.1, Thm 9.2/9.3, Lem 9.4, Def 9.5, Thm 9.6, Cor 9.7, Thm 9.8 | needs de Jong alterations |
| 10 Leafwise H^0 | Def 10.1, Thm 10.2, Prop 10.3 | 10.3 adelic irreducibility |
| 11 Generalized functions | Lem 11.1/11.2, Def 11.3/11.4, Prop 11.5–11.7 | |
| 12 Invertible functions | Prop 12.1 | |
| 13 o-valued points | Prop 13.1, Def 13.2, Thm 13.3, Prop 13.4, Cor 13.5, Def 13.6, Supple 13.7, Prop 13.8/13.9, Thm 13.10, Cor 13.11/13.12 | |
| 14 A_inf rings | Def 14.1/14.2, Prop 14.3/14.4, Def 14.5, Prop 14.6, Prop 14.7, Def 14.8, Supple 14.9, Prop 14.10, Def 14.11, Prop 14.12–14.15 | 14.7/14.13/14.14 pure algebra |
| 15 Fargues–Fontaine | Thm 15.1, Prop 15.2, Thm 15.3, Cor 15.4, Thm 15.5, Prop 15.6/15.7 | |

## Ledger (Lean modules landed)

| Paper result | Lean module | Status |
|---|---|---|
| Thm 1.8 (`t29`) `V_N(W) ∩ W_rat = V_N(W_rat)` | `RHTower/DeningerDynSysVerschiebungRational.lean` | closed (Fatou hypothesis removed: holds over every commutative ring) |
| Prop 1.2(a) (`t21n`) finite-orbit Galois descent | `RHTower/DeningerDynSysWittGaloisFiniteOrbits.lean` | closed |
| Lemma 4.6 (`t46n`) `N`-th roots of pointed multiplicative maps, incl. the value of `N'` | `RHTower/DeningerDynSysPointedMultiplicativeRoot.lean` | closed |
| Lemma 5.3 (`t5`) Frobenius-twist quotient | `RHTower/DeningerDynSysFrobeniusTwistQuotient.lean` | closed |
| Prop 7.7 (`t87`) compact-orbit quotient metric | `HTGeometry/CompactOrbitQuotientMetric.lean` | closed |
| Prop 1.2(b) (`t21n`) field case of Galois descent | `RHTower/DeningerDynSysWittGaloisField.lean` | closed (integrally-closed-domain case still open) |
| Prop 14.7(c) (`t125`) perfection surjects along a quotient | `RHTower/DeningerDynSysPerfectionLocal.lean` | closed |
| Prop 14.14(2) (`t1213`) locality of the tilt | `RHTower/DeningerDynSysPerfectionLocal.lean` | closed |

| Thm 1.4 (`t27n`) = Kucharczyk–Scholze Lemma 4.9 | `RHTower/DeningerDynSysInvariantPoints.lean` | closed |
| Lemma 1.6(2) (`t212n`), Cor 1.7(1) (`t213n`) | `RHTower/DeningerDynSysValuedPoints.lean` | closed |
| §1 `Hom(ℤ̲A, R) ≅ (A →*₀ R)` | `RHTower/DeningerDynSysReducedMonoidAlgebra.lean` | closed |
| Def 9.5 (`t95n`) + its two stated facts | `HTGeometry/AlmostPathConnected.lean` | closed |

Axiom audit: every capstone above depends only on `propext`, `Classical.choice`, `Quot.sound`.

### Duplication audit (2026-08-22)
The corpus's `Deninger*RationalWitt*` modules formalize a **different** Deninger paper (the 2025
rational-Witt paper: the `ω`-comparison `ℤ̲A → W_rat(A)`, absolute-Galois descent over perfect
fields, the corrected normal-domain descent, and the Fatou intersection).  A grep for this paper's
internal labels (`t29`, `t87`, `t46n`, `t21n`, `t1213`, `t125`, `t1110`, …) over `formal/` and over
the 77 pipeline cards citing arXiv:1807.06400 returns only the modules listed above.  §1 overlaps
partially: Prop 1.1 (a) and (b) are covered by
`deningerRationalWittReducedMonoidAlgebraToAdditive_injective` / `..._surjective` and the
AIC-domain comparison.

### Known heavy sub-projects (not yet started)
* Lemma 4.3 (`t3`) needs `dim_ℚ (C^× / μ(C)) = |C|` for an algebraically closed `C ≠ F̄_p`.
* Thm 1.4 (`t27n`) is Kucharczyk–Scholze Lemma 4.9 plus its rational-Witt corollary.  Mathlib now
  supplies the needed profinite invariant theory: `Algebra.IsInvariant.isIntegral_of_profinite`,
  `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`, and
  `Ideal.Quotient.stabilizerHom_surjective_of_profinite`.  Remaining work: extend a hom
  `A^H → C` along the integral extension (lying over + `IsAlgClosed.lift`), and turn the two
  transitivity statements into transitivity of `H` on `Hom (A, C)`.
* §§2, 3, 13, 14 need the ringed space `W_rat(X)` and its `S`-valued points as scheme-level
  infrastructure.
* Claim 8.1 is an open conjecture in the source; Thm 8.2 is conditional on it in dimension ≥ 2.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  paper proofs read and dependency-closed per item
- [ ] 2 → 3  Lean theorems, `lake build` green per module, axiom audit PASS

## Log
- 2026-08-22 — created; paper source downloaded, 78-result inventory extracted.
- 2026-08-22 — five results closed in Lean (see Ledger); duplication audit recorded.
- 2026-08-22 — eight results closed; axiom audit clean; next target is Theorem 1.4 (`t27n`).
- 2026-08-22 — Theorem 1.4 (`t27n`) and Lemma 1.6(2)/Cor 1.7(1) closed: ten results.
- 2026-08-22 — reduced monoid algebra representability and Definition 9.5 closed; 13 items in the
  ledger; `formal_tools.py lint` reports no error attributable to these modules.
