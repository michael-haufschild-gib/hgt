# Hostile referee report

Manuscript: *The Determinant-Defect Completion Law and Cofinal Residue-Jet Torsion*
Review date: 2026-08-04  
Standard: publishable in a renowned broad mathematical journal comparable in scope and selectivity
to *Advances in Mathematics* or *Mathematische Annalen*. This report does not claim likely
acceptance by Annals/JAMS/Inventiones/Acta.

## Verdict

**PASS AT SUBMISSION-QUALITY BAR.**

Manuscript contains a genuine parent law, not merely determinant-line language or a relabeling
of regularized determinants. It identifies exact graph closure of raw finite-rank determinant
pencils under Schatten convergence as principal truncated-jet extension of regularized
determinant core. It proves every fibre direction by vanishing micro-spectra, family-level
homeomorphism, sharp rank--energy exponent, positivity trichotomy, and integer summability walls.
Corrected zeta jets, relative torsion, graded suspension, and arithmetic ordering spectra are
then explicit constrained sections or slices of this completion.

Result is broad enough for renowned general journal because it gives topology-forced mechanism
behind Quillen-type polynomial gauge ambiguity, then derives spectral-geometric and arithmetic
realizations with sharpness in every Schatten order. This report claims submission quality for
an *Advances in Mathematics*/*Mathematische Annalen*-level broad journal, not likely acceptance
at Annals/JAMS/Inventiones/Acta.

## Hostile objections and disposition

### 0A. “Parent theorem is just definition of \(\det_p\)”

**Objection.** Finite-rank identity
\[
 \det(I-A)=\det_p(I-A)
 \exp\left(-\sum_{k<p}\operatorname{Tr}(A^k)/k\right)
\]
and continuity of \(\det_p\) are classical. Exact closure may be a dressed-up textbook exercise.

**Disposition: answered.** Classical identity proves only necessity after a nontrivial normalized
logarithm argument. Sufficiency asks simultaneous inverse moment problem: for every
multivariable jet \(P\), construct finite-rank pencil \(B_n\to0\) in \(\mathcal S_p\) whose first
\(p-1\) trace moments correct arbitrary residual forms degree by degree. Root-of-unity blocks,
pure-power spanning, and ascending recursion solve it exactly. Result is full graph closure,
homeomorphism, functorial principal fibre, and not merely existence of one regularization.
Targeted exact-phrase and theorem-shape searches found no source stating this closure theorem;
absence of search collision is evidence, not proof of priority.

### 0B. “Quillen and Dang already proved polynomial-gauge torsor”

**Objection.** Quillen's 1989 notes predicted principal polynomial gauge bundle. Nguyen Viet
Dang proved renormalized elliptic determinants form torsor under local polynomial counterterms
(*Analysis & PDE* 15 (2022), 1--62). Calling polynomial fibre new without this source would be
unacceptable.

**Disposition: answered after mandatory revision.** Manuscript now cites Dang in introduction,
geometry section, novelty boundary, and bibliography. Quantifiers differ:

- Dang fixes elliptic background, imposes microlocal locality and determinant-like axioms, and
  classifies functions obtainable by subtraction of local counterterms.
- Present theorem closes raw uncorrected finite-dimensional determinants in Schatten topology,
  imposes no locality, and classifies all simultaneous operator/function limits.
- Present micro-spectrum construction and rank capacity are absent from Dang; conversely present
  theorem does not claim to classify which ambient directions are local counterterms.

Thus Quillen--Dang is conceptual ancestor and local subgroup, not theorem collision. Boundary is
now explicit enough to prevent priority theatre.

### 0C. “Holomorphic-family extension hides branch choices or nonuniform support”

**Objection.** Root blocks require choosing \(k\)th roots of coefficient; no global holomorphic
choice exists around zeros. Compact family may also fail uniform finite-rank approximation.

**Disposition: answered.** Weighted cyclic block uses weights
\(\delta,\ldots,\delta,c/(kN\delta^{k-1})\), so entries depend linearly on \(c\), lower traces
vanish, and \(k\)th trace is exactly \(c\ell^k\). Its \(N\)-copy Schatten cost is uniformly
\(O(N^{1-p/k})\) on bounded coefficient sets. Fixed compressions converge uniformly on compact
image of family. Compact exhaustion handles noncompact complex manifolds. Necessity recovers
finite jet by normalized logarithm on uniform zero-free neighbourhood. No branch remains.

### 0D. “Capacity exponent or positivity table may be only sufficient”

**Disposition: passed.** Rank inequality
\(|\operatorname{Tr}(B^k)|\le R^{1-k/p}\|B\|_p^k\) follows from Schatten Hölder and finite-rank
norm comparison; normal root block of rank multiple of \(k\) attains equality. Solving equality
gives exponent \(pk/(p-k)\), and threshold \(k=p\) forbids survival. Positive and self-adjoint
necessity follows from bounded first/second moment and vanishing operator norm; explicit blocks
give converse. Graded positive finite differences realize every real jet. Manuscript no longer
uses unproved categorical word “minimal” for grading.

### 0E. “Universal law is bolted onto unrelated arithmetic paper”

**Objection.** A late operator-theoretic section plus prime-ordering classification may read as
two papers joined after fact.

**Disposition: acceptable after structural revision.** Abstract is compressed around completion
law; introduction states theorem, family version, capacity, summability filtration, and explicit
shadow table. Roadmap explains concrete-to-structural proof order. Every later result has named
map into completion fibre: corrected zeta jet is lift, relative torsion is transition character,
graded suspension is real group completion, prime orderings are one-dimensional constrained
dynamics. Conclusion repeats these specialization maps. Breadth is synthesis, not juxtaposition.

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
- root-of-unity micro-spectrum cancellation and arbitrary pure homogeneous pencil realization;
- summability-transition character identity and cocycle.

No admitted goals, custom axioms, opaque declarations, or unsafe declarations are allowed by
project lint. Paper accurately separates machine-checked core from cited and paper-proved
analytic inputs.

## Correctness dependency audit

| Result | Critical dependency | Status |
|---|---|---|
| Determinant graph closure | finite-rank trace identity; \(\det_p\) continuity; normalized local log; micro-spectrum synthesis | Closed |
| Family completion | uniform finite compression; root-free cyclic blocks; compact exhaustion | Closed |
| Sharp capacity/statistics | Schatten Hölder; root blocks; moment domination; finite differences | Closed |
| Real summability/tower | \(\mathcal S_r\hookrightarrow\mathcal S_{\lceil r\rceil}\); trace transition cocycle | Closed |
| Universal cofinal law | Hartmann--Lesch factorization; continuity of \(\det_p\); local log | Closed |
| Corrected coefficient formula | relative-zeta binomial expansion; simple Laurent pole | Closed |
| Full-jet sharpness | forward differences; Mertens scalar spectrum; colored Baire argument | Closed |
| Rational interval classification | relative extremality; vanishing mesh; two controls | Closed |
| Number-field classification | ideal Mertens asymptotics; repeated-norm extremality | Closed |
| Determinant excision | coprime Euler factor; regularized determinant identity | Closed |
| Quillen/BF statement | gauge transformation only, no new curvature claim | Closed |
| Relative analytic torsion | positive two-term complex for \(z<1\); graded superdeterminant | Closed |

## Significance score

- Novelty: **8/10** — polynomial ambiguity and fixed factorization old; exact Schatten graph
  closure, vanishing micro-spectrum surjectivity/capacity, family completion, cofinal completeness,
  and ordering classification appear new after Quillen--Dang boundary correction.
- Depth: **8/10** — combines operator topology, a simultaneous trace-moment synthesis problem,
  regularized determinants, arithmetic extremality, constructive cluster control, and Baire
  category.
- Breadth: **9/10** — functional analysis, spectral geometry, analytic torsion, number theory.
- Proof completeness: **8/10** — self-contained new arguments with classical inputs clearly cited.
- Exposition: **8/10** — 29-page manuscript; compressed abstract, specialization table, exact
  novelty boundary, and no RH overclaim.
- Formal integrity: **9/10** for stated checked core.

## Completed release audit

| Gate | Evidence | Result |
|---|---|---|
| Lean source checks | All four determinant/residue-jet files pass `lake env lean` | PASS |
| Targeted build | `lake build GaloisForLFunctions.RHTower.DeterminantDefectMicroSpectrum` | PASS |
| Axiom audit | Principal declarations use only `propext`, `Classical.choice`, `Quot.sound` | PASS |
| Proof-debt audit | Generated `LEAN_GAPS.md` reports no `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration; scoped source scan clean | PASS |
| Wiring/index | New module imported by `RHTower.lean`; every declaration present in `LEAN_API.md` | PASS |
| PDF/source | Tectonic clean; 29 pages; no box/reference/citation warning; every page visually inspected | PASS |
| Novelty boundary | Quillen--Dang collision incorporated; no-collision search explicitly not treated as proof of priority | PASS |
| Process hygiene | No determinant-stack Lean process left running | PASS |

Repository-global umbrella build and global wiring lint were also attempted. They are presently
red for unrelated concurrent worktree routes: duplicate declaration
`RHTower.Sieve.card_divisors_of_squarefree` between two sieve modules, plus many unrelated
unreachable CCM/HTGeometry modules. Determinant-stack top module builds cleanly and its umbrella
import is present, so these global dirty-worktree failures do not alter manuscript/formal-core
verdict and were not “fixed” outside scope.

Report recommends submission to a renowned broad journal at stated level.
