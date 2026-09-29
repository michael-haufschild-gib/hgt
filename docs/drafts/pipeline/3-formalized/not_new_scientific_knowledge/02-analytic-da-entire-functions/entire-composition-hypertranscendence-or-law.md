# Entire-composition hypertranscendence obeys the Boolean OR law

- **ID:** `entire-composition-hypertranscendence-or-law`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]` / source correction
- **Scientific status:** not new scientific knowledge
- **Scope:** nonconstant entire functions on `C`, differential algebraicity over `C(z)`
- **Source:** Steinmetz reduction; He--Yang; Huang--Ng, *Hypertranscendency of Perturbations of Hypertranscendental Functions* (2020), Theorem 3; DA composition and local-inverse closure.

## Statement

For nonconstant entire functions `f,g`,

`f o g is DA  <=>  f is DA and g is DA`.

Equivalently,

`f o g is HT  <=>  f is HT or g is HT`.

Thus the DA entire functions form a divisor-closed submonoid of the composition monoid, and the HT entire functions form its completely prime two-sided complement: hypertranscendence obeys Boolean OR under every finite entire composition.

## Proof

### Both factors DA implies the composite DA `[SEARCH]`

The DA germs form a class closed under composition. Hence `f,g` DA implies `f o g` DA.

### An HT outer factor forces an HT composite `[SEARCH]`

Huang--Ng Theorem 3, following He--Yang and Steinmetz reduction, states that if `f` is HT over `C(z)` and `g` is nonconstant entire, then `f o g` is HT (indeed over a larger small-function field).

The mechanism is global. If `f o g` satisfied an ADE, Faa di Bruno expansion would give

`sum_j (M_j(f) o g) H_j(g) = 0`,

where `M_j(f)` are differential monomials in `f` and `H_j(g)` are differential polynomials in `g` with Nevanlinna characteristic `O(T(r,g))`. Steinmetz reduction produces nonzero polynomials `Q_j` with

`sum_j Q_j M_j(f) = 0`,

an ADE for `f`, contradiction.

### An HT inner factor also forces an HT composite `[BRIDGE]`

Assume `g` is HT.

- If `f` is HT, the preceding outer-factor theorem applies.
- If `f` is DA and `f o g` were DA, choose a regular value of the nonconstant entire function `f`. A local inverse germ `f^(-1)` exists there and is DA by the DA inverse-closure theorem. On a nonempty open set,

  `g = f^(-1) o (f o g)`.

  The right side is DA. Hence the germ of `g` is DA, so analytic continuation of its ADE makes `g` DA globally, contradiction.

This exhausts the DA/HT dichotomy for `f`.

## Attack and boundary

- `[PROVED]` The theorem is false for arbitrary local analytic germs: take an entire HT local biholomorphism `G` and its inverse germ `G^(-1)`; both germs are HT while `G^(-1) o G = id` is DA.
- `[PROVED]` Global entire continuation is load-bearing. Steinmetz reduction is the step unavailable in the germ category.
- `[PROVED]` Every finite self-iterate of an entire HT function is HT.
- `[PROVED]` Every finite composition of nonconstant entire functions is HT exactly when at least one factor is HT.
- `[SEARCH]` This is not a new theorem. The outer-HT half is already Huang--Ng Theorem 3; the inner-HT half is a short consequence of that theorem and standard DA inverse closure.
- `[PROJECT CORRECTION]` The repository card `transcendental-composition-ht.md` treats entire HT-after-HT composition as open. In the stated global entire category it is source-settled. Its local-germ counterexample remains correct, and `Gamma o Gamma` remains outside the theorem because it is not meromorphic on the plane: poles of the outer Gamma accumulate near poles of the inner Gamma.

## Significance without novelty inflation

The law supplies a positive structural characteristic of the HT class: finite entire composition cannot create or cancel hypertranscendence. It also moves the real frontier from finite composition to limits, restricted domains, non-global meromorphic compositions, and composition constraints whose solutions are not global entire maps.

## Gates

- [x] Exact statement and proof.
- [x] Parent-theory reduction identified.
- [x] Local-germ and Gamma-composition boundaries stated.
- [x] Unconditional Lean formalization (2026-09-29): see *Lean closure* below.


## Lean status

Three of the law's four directions are unconditional Lean theorems; the fourth is the classical
input the card cites.

| Statement | Lean theorem | Module |
|---|---|---|
| both factors DA ⟹ composite DA | `differentiallyAlgebraic_comp_entire` | `CompositionInnerDecomposition` |
| inner DA + composite DA ⟹ outer DA | `differentiallyAlgebraic_outer_of_comp` | `CompositionInnerDecomposition` (from `CompositionDecompositionLaw.differentiallyAlgebraic_of_comp`) |
| **outer DA + composite DA ⟹ inner DA** | `differentiallyAlgebraic_inner_of_comp` | `CompositionInnerDecomposition` |
| the law, modulo the both-hypertranscendental case | `differentiallyAlgebraic_comp_iff_of_gap` | `CompositionInnerDecomposition` |
| a regular point of the composition | `exists_regular_point` | `CompositionInnerDecomposition` |
| a local analytic inverse with explicit domains | `exists_localInverse_domains` | `CompositionInnerDecomposition` |

Supporting corpus assets used: `RGTowerCoherence.differentiallyAlgebraicOn_comp`,
`LocalInverseHypertranscendence.differentiallyAlgebraicOn_of_localInverse` and
`differentiallyAlgebraic_of_differentiallyAlgebraicOn`,
`CrossDomainSubstitution.substitutionFaithful_of_rightInverse`,
`ParabolicFatouJetRealization.exists_localInverse_analytic`,
`DifferentialAlgebraicOnSum.differentiallyAlgebraicOn_of_eqOn`.

**The one remaining gap** is the hypothesis `hgap` of `differentiallyAlgebraic_comp_iff_of_gap`:
`f` hypertranscendental and `g` hypertranscendental make `f ∘ g` hypertranscendental.  This is
Steinmetz's Reduction Theorem (equivalently Huang--Ng Theorem 3), and by the analysis in
`_STAGE3-LEDGER.md` it rests on a second main theorem for small functions: the two-term case follows
from Clunie growth alone, but every differentiation of the substituted relation adds jet monomials
at least as fast as it adds equations, so no Wronskian elimination closes the system.

## Lean closure (2026-09-29) — card fully formalized

The remaining direction — `f` and `g` hypertranscendental make `f ∘ g` hypertranscendental — is
Steinmetz's Satz 2, now unconditional Lean.  The proof follows Steinmetz's 1980 paper (Math. Z. 170,
§4–§5), with his iterated construction of auxiliary functions replaced by one linear-algebra step.
No second main theorem for small functions is needed: only Nevanlinna's second main theorem for
**constant** targets, which the corpus owns.  Axioms of every capstone:
`[propext, Classical.choice, Quot.sound]`.

| Statement | Lean |
|---|---|
| interpolation: polynomials `P_μ`, `deg ≤ D`, not all zero, with `P_μ(t_j) = c_j F_μ(t_j)` | `SteinmetzInterpolation.exists_polynomials_proportional_at_points` |
| level-set counting `Σ_j N(r,t_j,g) ≤ N(r,0,N) + N(r,0,g')` | `SteinmetzNevanlinnaCore.sum_logCounting_le_of_vanishing` |
| `N = Σ P_μ(g) H_μ(z, g-jets)` vanishing on `s ≥ D + 4 + ((n+1)Σ deg H_μ + 1)2^{n+2}` level sets is `0` | `SteinmetzNevanlinnaCore.sum_eq_zero_of_vanishing_on_levels` |
| **Steinmetz Satz 1**: `Σ F_μ(g) h_μ ≡ 0`, `F_μ ≢ 0` ⇒ `Σ P_μ(g) h_μ ≡ 0`, `P` not all zero | `SteinmetzReduction.exists_polynomial_relation_of_comp_relation(_finset)` |
| **Steinmetz Korollar 1**: some `h_μ ≢ 0` ⇒ `Σ Q_μ F_μ ≡ 0`, `Q` not all zero | `SteinmetzReduction.exists_polynomial_relation_outer` |
| Faà di Bruno for entire functions | `EntireCompositionSteinmetz.iteratedDeriv_comp_eq_aeval_compJetPoly` |
| **Steinmetz Satz 2**: `f ∘ g` DA, `g` HT ⇒ `f` DA | `EntireCompositionSteinmetz.differentiallyAlgebraic_of_comp_of_not_differentiallyAlgebraic_inner` |
| **the Boolean law** `f ∘ g` DA ⟺ `f` DA ∧ `g` DA (nonconstant entire `f, g`) | `EntireCompositionSteinmetz.differentiallyAlgebraic_comp_iff` |
| every finite composition: DA ⟺ every factor DA | `EntireCompositionOrLaw.differentiallyAlgebraic_foldr_comp_iff` |
| every iterate `f^{[n+1]}` of an HT nonconstant entire `f` is HT | `EntireCompositionOrLaw.not_differentiallyAlgebraic_iterate` |
| the law fails for germs: `1/Γ` and its local inverse are HT germs with identity composite | `EntireCompositionOrLaw.exists_hypertranscendental_germ_pair` |

The key change from the paper: instead of Steinmetz's classes `H_s` (built by repeated
elimination), pick `s = (m+1)(q+1)` points avoiding the zeros of every `F_μ` and solve the
homogeneous system `P_μ(t_j) = c_j F_μ(t_j)`, which has `m + 1` more unknowns than equations.  The
resulting `N` vanishes on `g⁻¹{t_j}`.  The divisor inequality, the first main theorem, the corpus
jet bound `T(r, g^{(j)}) ≤ 2^{n+2}T(r,g) + C` along one sequence of good radii
(`IteratedDerivativeGrowth.exists_radii_jet_bound_and_error`), and the classical second main
theorem (`ValuePreimageInfinite.exists_sub_two_characteristic_le_sum_logCounting`) then force
`N ≡ 0`.  In Satz 2, hypertranscendence of `g` does the job of Steinmetz's highest-monomial
argument: every nonzero coefficient polynomial evaluates to a nonzero function.  The Gamma∘Gamma
remark is outside the theorem's hypotheses, and the card makes no claim about it.

- **Stage:** 3-formalized (2026-09-29).
