# Hostile referee report

Manuscript: *Cofinal Residue-Jet Universality for Zeta Determinants*  
Review date: 2026-08-04  
Standard: publishable in a renowned broad mathematical journal comparable in scope and selectivity
to *Advances in Mathematics* or *Mathematische Annalen*. This report does not claim likely
acceptance by Annals/JAMS/Inventiones/Acta.

## Verdict

**PASS AT SUBMISSION-QUALITY BAR, subject to clean final source/formal/PDF audit.**

Manuscript contains a genuine universal law, not merely determinant-line language:
under Schatten convergence, full corrected finite-part residue jet is exact and minimal
cofinal defect of normalized zeta determinants. Fixed-operator factorization is correctly
credited to Hartmann--Lesch. New content is converse cofinal completeness, compact-open cluster
transport, sharp all-order realization by graded superdeterminants, arbitrary-ordering interval
classification, number-field universality, and Baire-generic maximal torsion.

Result is broad enough for renowned general journal because it links spectral analysis,
determinant lines, analytic torsion, and arithmetic ordering dynamics through one invariant;
sharpness is proved in every Schatten order and natural number-field model is not confined to
one example.

## Hostile objections and disposition

### 1. “Universal law is immediate from Hartmann--Lesch”

**Objection.** Fixed factorization
\[
\det_\zeta(L-z)/\det_\zeta L
=e^{P_L(z)}\det_p(I-zL^{-1})
\]
is known. Renaming coefficients is not publication-level novelty.

**Disposition: answered.** Manuscript does not claim fixed factorization. It proves a
stability-and-defect theorem for sequences:

- any compact-open convergent determinant subsequence forces every corrected jet coefficient
  to converge;
- every convergent jet forces determinant convergence;
- cluster topology is transported homeomorphically;
- common divisor is rigid and quotient torsion is exact character of jet difference;
- no proper sub-jet supports continuous descent.

Converse uses zero-free disk, local logarithms, and coefficient recovery. New theorem is short
once factorization is available, but shortness is not a defect when sharpness and realizability
are substantial and complete.

### 2. “Residue correction is already Wodzicki/Quillen/Bismut--Freed theory”

**Objection.** Wodzicki corrections to curvature and regularized Chern forms are classical.

**Disposition: answered.** Paper explicitly marks them established. New invariant is mixed:
\[
b_j(L)=-\frac1j\operatorname{FP}_{s=j}\zeta_L(s)
-\frac{H_{j-1}}{jm}\operatorname{res}_W(L^{-j}).
\]
Local residue alone and determinant-line triviality alone are both incomplete. Paper no longer
claims metric or connection itself changes; it proves exact gauge transition between normalized
determinant sections. This wording survives hostile geometry review.

### 3. “All-order example is artificial signed subtraction”

**Objection.** Negative finite-difference weights may hide a virtual construction with no
determinant-line meaning.

**Disposition: answered.** Weights are implemented by finite even/odd multiplicities:
positive weights in even degree, negative weights in odd degree. Virtual zeta is supertrace and
determinant character is standard superdeterminant section of graded determinant line. This is
analytic-torsion geometry, not subtraction of positive operators. Constituent operators remain
positive and each inverse converges in required Schatten class.

### 4. “Sharpness calculations may lose signs or off-diagonal terms”

**Objection.** Finite differences at shifted scales are sign-sensitive.

**Disposition: passed.** With
\[
w_{j,r}=(-1)^{j-r}\binom jr,\qquad
V_j(s)=\sum_{r=0}^jw_{j,r}(r+1)^s,
\]
forward differences give \(V_j(k)=0\) for \(k<j\), \(V_j(j)=j!\).
At coordinate \(k\), terms \(j>k\) vanish, \(j<k\) are regular, and diagonal Laurent expansion
gives
\[
\mathfrak b_k
=-\frac{V_k(k)}k\gamma(P_k)
-(V_k'(k)+H_{k-1}V_k(k))a(P_k)
-\frac1k\sum_{j<k}V_j(k)Z_{P_j}(k/j).
\]
Along exhaustion this is \(C_k-(k-1)!\gamma(P_k)+o(1)\). No omitted term survives. Lean proves
moment cancellation and exact factorial determinant of full moment matrix.

### 5. “Divisor convergence is asserted, not proved”

**Disposition: repaired and passed.** Zeros are
\[
z=(r+1)^{-1}m^{1/j},\qquad (m,M_P)=1.
\]
Only finitely many lie in fixed compact. Every \(m>1\) is eventually removed by a prime divisor;
\(m=1\) persists. Divisor convergence is locally eventually exact.

### 6. “Diamond--Ford already studied these constants”

**Objection.** Arithmetic part may be rediscovery.

**Disposition: passed after claim narrowing.** Diamond--Ford finite-set distribution and
extremality are cited and not claimed. New constraint is nested exhaustive ordering. Paper proves:

- every cofinal cluster set is one closed interval above universal endpoint;
- every such interval occurs;
- same theorem for every number field;
- every interval fibre dense, full interval comeagre, spectrum map nowhere continuous;
- determinant lift and exact prime-ideal excision.

Exact stabilized theorem-wording searches found no collision. This is evidence, not proof of
priority; author should still solicit expert number-theory bibliographic check before submission.

### 7. “Number-field endpoint may depend on field”

**Disposition: passed.** If
\[
\zeta_K(s)=\rho_K/(s-1)+c_K+O(s-1),
\]
then corrected finite part is
\[
\kappa_K(P)=\rho_Ka_K(P)
\left(\gamma_K+\sum_{\mathfrak p\in P}
\frac{\log N\mathfrak p}{N\mathfrak p-1}\right).
\]
Number-field Mertens product contributes \(e^{-\gamma}/(\rho_K\log X)\);
weighted sum contributes \(\log X+O(1)\). Multiplication cancels \(\rho_K\) and forces endpoint
\(e^{-\gamma}\). Repeated norms are handled by reference ordering and non-increasing,
not necessarily strictly decreasing, replacement steps.

### 8. “Cluster interval construction has hidden cofinality gap”

**Disposition: passed.** Natural-fill downward stages consume least missing atoms, so every atom
is eventually used. Remote upward blocks are disjoint and above prior support. Vanishing mesh
forces order-convex cluster set; alternating sweeps realize every finite interval, with separate
arguments for infinite upper endpoint and singleton infinity.

### 9. “Baire genericity may only prove density”

**Disposition: passed.** Hitting each rational basic rectangle after every time \(N\) is open
dense by finite-prefix extension. Countable intersection yields recurrence in every basic
rectangle, hence full product cluster set. Full-spectrum fibre is comeagre; each proper fibre is
dense but contained in meagre complement. Two fixed positive-distance hyperspace cluster sets
in every cylinder prove nowhere continuity.

### 10. “Formalization is theatre”

**Disposition: passed for advertised scope.** Lean companion does not pretend to contain
Mathlib-absent Schatten, regularized Fredholm, or zeta determinant libraries. It unconditionally
checks:

- finite residue algebra, one-atom update, cleared excision;
- determinant/torsion factorization and cocycle;
- all-order finite-difference cancellation;
- nonsingularity and exact factorial determinant of suspension matrix;
- injective/surjective finite jet-polynomial classification;
- actual compact-open topology of continuous complex functions;
- forward and converse determinant-character convergence after zero-free core cancellation;
- exact “determinant converges iff all corrected coordinates converge” criterion.

No admitted goals, custom axioms, opaque declarations, or unsafe declarations are allowed by
project lint. Paper accurately separates machine-checked core from cited and paper-proved
analytic inputs.

## Correctness dependency audit

| Result | Critical dependency | Status |
|---|---|---|
| Universal cofinal law | Hartmann--Lesch factorization; continuity of \(\det_p\); local log | Closed |
| Corrected coefficient formula | relative-zeta binomial expansion; simple Laurent pole | Closed |
| Full-jet sharpness | forward differences; Mertens scalar spectrum; colored Baire argument | Closed |
| Rational interval classification | relative extremality; vanishing mesh; two controls | Closed |
| Number-field classification | ideal Mertens asymptotics; repeated-norm extremality | Closed |
| Determinant excision | coprime Euler factor; regularized determinant identity | Closed |
| Quillen/BF statement | gauge transformation only, no new curvature claim | Closed |
| Relative analytic torsion | positive two-term complex for \(z<1\); graded superdeterminant | Closed |

## Significance score

- Novelty: **8/10** — fixed factorization old; cofinal completeness, full-jet sharpness, and
  ordering classification appear new.
- Depth: **8/10** — combines operator topology, regularized determinants, arithmetic extremality,
  constructive cluster control, and Baire category.
- Breadth: **9/10** — functional analysis, spectral geometry, analytic torsion, number theory.
- Proof completeness: **8/10** — self-contained new arguments with classical inputs clearly cited.
- Exposition: **8/10** — 23-page focused manuscript; exact novelty boundary; no RH overclaim.
- Formal integrity: **9/10** for stated checked core.

## Required final audit before release

1. Re-run all three target Lean files and targeted umbrella module build.
2. Run formal lint and print-axiom checks on principal declarations.
3. Regenerate Lean index after new module.
4. Re-render final PDF and inspect all pages after latest edits.
5. Confirm no stale Lean process remains.
6. Preserve explicit “no collision found is not proof of priority” qualification.

If all six pass, report recommends submission to a renowned broad journal.
