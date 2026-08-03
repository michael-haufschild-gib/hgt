# Hostile referee report

Manuscript: *At most Lorentzian: a universal Stokes--Cartan signature law in genus zero*

Audit date: 2026-08-03

Target band: renowned general mathematics journal with strong geometry/representation-theory
readership (Compositio Mathematica / Duke Mathematical Journal / Advances in Mathematics level).
This is an internal adversarial review, not a claim of journal acceptance or a substitute for
external peer review.

## Recommendation

**Acceptable for submission after the corrections listed below, all now incorporated.** The paper
meets the mathematical and expository threshold of the target band. Its central result is short to
state, genuinely structural, and has consequences outside the immediate Stokes formalism. I would
not market the present 13-page version as Annals/Inventiones level without a categorical
microlocal lift or a major classification theorem, but rejection as “elementary matrix algebra”
would be wrong: the nontrivial content is that the entire geometric class is forced into the
rank-one-defect normal form.

## What I tried to break

### 1. “This is only the trivial fact that `P - vv^T` has index at most one.”

That fact is trivial and classical. If it were the novelty claim, I would reject the paper.
The actual new step is Theorem 3.2:

`C = I + sum_e ell_e u_e u_e^T - (H-1)rr^T`.

It converts the Stokes normalization, including diagonal loop terms and ramification factors, into
one positive laminar Gram form and one global total-rank square. The paper then proves that this
identity survives arbitrary type-A legs and the global genus-zero reading. Neither the 1994--1995
ultrametric matrix papers nor Nabben's July 2026 shifted-ultrametric paper states that geometric
identity or its nonabelian Hodge consequences. Objection fails, provided priority search remains
clear.

### 2. “Pairwise ultrametric inequalities do not give one common tree.”

Correct objection in principle. The paper now separates this issue in Definition 2.1,
Lemma 2.2, and Proposition 2.3. It constructs the threshold dendrogram and, for actual Stokes data,
uses the contact coarea formula

`kappa(v)=eta-integral_{h(v)}^eta du/R(u)`

to prove strict monotonicity and simultaneous meet realization. It cites the exact rescaled source
formula (Douçot, Lemma 4.3) and ultrametric theorem (Theorem 4.2). No collection of independent
pair witnesses is substituted for a rooted realization. Objection closed.

### 3. “The passage from arbitrary multi-pole data to one pole assumes an unproved Fourier
isomorphism.”

The first draft came too close to this overstatement. The revision cites Douçot 2026,
Theorems 1.4--1.6: the enriched tree and diagram are symplectic invariants and the generic class has
all Stokes circles at infinity. The proof transports only the invariant diagram matrix. It
explicitly does **not** claim the expected analytic isomorphism of all weak representations.
That is enough for a theorem about Cartan inertia. Objection closed at diagram level.

### 4. “Loops, twists, or legs can create another negative direction.”

Loops and ramification are absorbed into the diagonal contact identity

`B_ij = delta_ij + r_i r_j(K_ij-1)`.

They are not discarded. Type-A legs are handled by exact increment coordinates, not by an appeal
to intuition. Path completion produces a positive fluctuation block and Schur diagonal
`1/(l_i+1)`. Congruence therefore preserves nonpositive inertia. The theorem is correctly limited
to ordinary one-ended type-A legs. Objection fails within stated scope.

### 5. “The affine statement overlooks a simultaneous negative direction.”

Capacity completion is exact:

`x^T C x = z^T P z + M(x)^2 Omega`, with `r^T z=0`.

At `Omega=0`, strict positivity of `P` gives exactly one null line and no negative direction. At
`Omega<0`, the same line is negative; the determinant factorization rules out a kernel. Thus
negative and affine modes cannot coexist. Objection fails.

### 6. “Root height is arbitrary, so Omega is gauge fiction.”

The Sherman--Morrison update is computed explicitly:

`c_t=c/(1+tc)`, hence `c_t^{-1}-(lambda+t)=c^{-1}-lambda`.

The determinant prefactor is invariant as well. The electrical proof makes this transparent: a
root extension adds the same series resistance to effective resistance and global defect.
Objection fails.

### 7. “The dimension optimizer ignores integrality.”

Valid objection to the first draft. Corollary 8.2 now says **real relaxation** and states that an
integral dimension vector attains the bound only when the balanced profile is integral. Correction
incorporated.

### 8. “Conormal, Rees, corona, and vanishing-cycle vocabulary is decorative.”

The final version earns the first three terms precisely:

- `d nu_e=u_e` is the principal conormal of the explicit cluster hyperplane `nu_e=0`;
- the Hessian is exactly `D + sum ell_e dnu_e tensor dnu_e`;
- the multi-Rees family is explicitly defined by nonnegative edge parameters and proved one-defect
  for every specialization;
- corona pruning is the exact terminal-cluster Schur complement/parallel-resistance identity.

The manuscript expressly refuses to identify these coefficients with sheaf-theoretic
characteristic-cycle or vanishing-cycle multiplicities. The language is therefore bounded rather
than theatrical. Objection closed.

### 9. “The theorem is not sharp or has no realized indefinite example.”

Douçot's twisted triangle with edge multiplicities 6, 3, 4 is an actual nonabelian Hodge graph and
not an untwisted fission graph. Its Cartan form has `1^T C 1=-20`, `det C=-258`, and trace 6, hence
inertia `(2,1,0)`. The Lorentz phase is realized and the stronger positivity conjecture is false.
Sharpness established.

### 10. “The graph consequence is a restatement with no reach.”

For a graph, inertia of `2I-B` is exactly the count of adjacency eigenvalues above 2. The global
theorem therefore yields `lambda_2(B)<=2`, a simple affine eigenvalue, and exclusion of higher
Kac--Moody signature. Boalch's counting paper frames which graph/root-system classes occur as an
open structural problem and already contains hyperbolic examples; the new theorem identifies the
universal upper signature boundary. This is significant and easy to communicate beyond the
specialty.

## Proof-by-proof correctness audit

| Result | Attack | Outcome |
|---|---|---|
| Lemma 2.2 | Test transitivity orientation and strict diagonal | Correct: “two larger equal” forces threshold equivalence; leaves added separately |
| Proposition 2.3 | Look for pairwise-vs-simultaneous gap and weak-representation overreach | Corrected and closed as above |
| Theorem 3.2 | Check diagonal and off-diagonal entries separately | Both reduce to `delta_ij+r_i r_j(K_ij-1)`; signs are correct |
| Corollary 3.3 | Could a two-dimensional negative space avoid `ker r^T`? | No: any 2-plane meets the codimension-one hyperplane nontrivially |
| Theorem 4.1 | Check coefficient of mass term | `m^2/c-lambda m^2=m^2 Omega`; correct |
| Theorems 4.2--4.3 | Check zero/negative coexistence and determinant sign | Correct; determinant `det(P)c Omega` closes nonsingularity |
| Proposition 4.4 | Check root edge vector and denominator | New edge has cut vector `r`; Sherman--Morrison denominator `1+tc>0` |
| Theorem 5.3 | Compare constrained minimum with capacity | Both minima equal `M^2/c`; recursion is exact series--parallel reduction |
| Theorem 6.2 | Check whether core square is double-counted | No: path energy supplies the core square and yields Schur weight `1/(l_i+1)` |
| Corollary 7.2 | Could zero Rees weights destroy positive definiteness? | No: base diagonal `D>0` remains |
| Theorem 8.1 | Check root-extension cancellation | New all-leaf cut contributes `tM^2`, cancelling change in `lambda M^2` |
| Theorem 9.1 | Check transported object | Only diagram/Cartan matrix, not analytic moduli isomorphism |
| Theorem 10.1 | Check eigenvalue ordering and null multiplicity | Immediate spectral mapping; statements cover all three phases |

## Novelty audit verdict

Closest sources were checked through 2026-08-03, including the July 2026 Nabben preprint. Searches
for nonabelian Hodge/fission graph signature, Lorentzian Cartan form, second eigenvalue, negative
eigenvalue, rank-one defect, and effective resistance found no theorem matching the paper. This is
not an absolute priority guarantee. It is enough to make a serious submission; external experts
should be asked specifically about unpublished work and alternate terminology.

## Formal verification audit

New modules:

- `formal/GaloisForLFunctions/HTGeometry/StokesCartanLorentzCapacity.lean`
- `formal/GaloisForLFunctions/HTGeometry/StokesCartanTypeALegs.lean`
- `formal/GaloisForLFunctions/HTGeometry/StokesCartanCoronaCapacity.lean`

Audit results:

- direct source checks passed earlier in development;
- final targeted `lake build` passed for all three modules, sequentially;
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` occurs in the three modules;
- principal capstones use only `propext`, `Classical.choice`, and `Quot.sound` under
  `#print axioms`;
- all three imports occur in `GaloisForLFunctions/HTGeometry.lean`;
- no Lean/lake process owned by this task remained after audit.

Repository-wide lint is currently red for unrelated concurrent work: many unwired `RHTower`
modules and the unrelated `HTGeometry.LogPrimeExponentialCarrier` and
`HTGeometry.TwoRecordResolvedConnection`. The three Stokes modules are not among lint errors.
Direct umbrella checking likewise stopped at unrelated missing `.olean` files after the new modules
had built. I do not count shared-worktree failures against this paper, but they must not be reported
as a green global repository audit.

## PDF/exposition audit

- 13 A4 pages; every page visually inspected.
- No TeX errors, undefined references, overfull boxes, clipped equations, broken glyphs, or blank
  trailing page.
- Central theorem appears in abstract and introduction with novelty boundary stated.
- All strong global claims have a named scope and explicit falsifiers.
- References are primary where available; no fabricated citation or placeholder remains.

## Final publication-level judgment

**Yes: the corrected paper clears a renowned general-journal submission threshold.** Reasons:

1. one memorable universal theorem with a sharp realized boundary;
2. direct consequence for an open Kac--Moody/nonabelian-Hodge graph classification problem;
3. complete proofs, not a conjectural program;
4. exact capacity, determinant, corona, leg, conormal, Rees, dimension, and spectral consequences;
5. unusually clear separation between geometric inputs, classical matrix lemmas, new claims, and
   speculative microlocal directions.

Residual risk is priority and whether editors judge the contact-to-factorization insight broad
enough for their audience. That is normal publication risk, not a correctness or completeness
failure.
