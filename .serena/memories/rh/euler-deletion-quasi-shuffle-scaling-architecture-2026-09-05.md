# Euler-deletion multiplicative factorization-curvature architecture (2026-09-05)

Current high-risk provisional successor: multiplicative factorization curvature of the Mellin-deformed deletion grade (MDFGT). No RH implication or global novelty certificate.

- For modulus P, the literal coefficient is `a_P(n)=1-P[P|n]`. Every positive-real-part zeta zero closes every deletion endpoint via the pole-cleared identity for `(1-P^(1-s))ζ(s)`.
- Earlier closed core remains: finite zero level one and bracket `P(P-1)`; conditional convergence on `Re(s)>0`; square-summable complex chronological levels on `Re(s)>1/2`; squarefree cylinder closure; repetition obstruction `a_P²=(P-1)+(2-P)a_P`; negative literal composite interference; commutative-development collapse.
- Static factorization grading: `EulerDeletionFactorizationGraded.lean` proves `insert_P(a_Q)=a_Q-a_Pa_Q`, uniform grade orthogonality/replication factor P, and the weighted cross-grade defect
  `D_alpha(P,Q)=Z(alpha)(1-P P^(-alpha))(1+Q(Q-2)Q^(-alpha))>0`
  for coprime `P,Q>1`, `alpha>1`. Unweighting is exponent-blind.
- Depth-two strict schedules are exhausted by polarized quasi-shuffle; scalar cofactor insertion and nested floors commute exactly.
- New depth-three audit: `EulerDeletionFactorizationCurvature.lean` proves every additive factorization-tree associator made only from the same-clock weighted pairing is zero. Corpus promotion-associator laws predict this bilinear flatness.
- Pivot to modulus multiplication. Define
  `K_alpha(P,Q,R)=D_alpha(P,Q)+D_alpha(PQ,R)-D_alpha(Q,R)-D_alpha(P,QR)`.
  For positive pairwise-coprime P,Q,R,
  `K=Z(alpha)(Q Q^(-alpha))(1-P P^(-alpha))(Q-1)(1-R^(2-alpha))`.
  For P,Q,R>1 and alpha>1: K<0 on 1<alpha<2, K=0 iff alpha=2, K>0 above 2. Thus `K_(2 Re(rho))<0` for any hypothetical right-half critical-strip zero.
- Natural-lift no-go: on `Nat × Real`, define `(P,a) star_alpha (Q,b)=(PQ,a+b+D_alpha(P,Q))`. Its second-coordinate associator is exactly K, so this lift is provably nonassociative throughout `1<alpha<2`. Base modulus associativity cannot supply factorization-tree equality after the defect coordinate is attached.
- Formal status: scratch and direct checks passed; targeted leaf build passed; module wired into `RHTower.lean`; nine-capstone axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Critical limitation: endpoint closure does not yet annihilate K. Nonzero signed curvature alone is no contradiction. Next MDFGT-1d kill gate is to construct a source-defined three-channel chronological object whose two factorization-tree boundary evaluations differ by K, then prove simultaneous squarefree zero closure makes them equal through a separately justified observation/quotient, without assuming order invariance or leaving conditional rearrangements open. Retire route if this cannot be done.
- No Runpod computation was needed for this step: exact algebra and Lean sign proofs settle the candidate invariant. Prior numerical report remains at `docs/drafts/pipeline/2-fully-proven/computations/euler-deletion-quasi-shuffle-second-level/REPORT.md`.
- Corpus coverage: 196 numbered `scripts/formal_tools.py research` queries. Queries 169-196 targeted depth-three iterated sums, regrouping anomalies, promotion associators, bilinear cocycles, weak-order strata, zero-fibre cocycles, holonomy, bar boundaries, and three-channel closure. Generic quasi-shuffle/promotion machinery was found; it confirms that curvature needs a separate admission/observation theorem. No exact source-specific four-term curvature collision was found. A primary-literature screen found generic quasi-shuffle and adjacent zeta-distribution work, not this exact construction. Search misses are not novelty proof.
- Kill gates: no FE/1-s, Gamma, theta, spectral, Möbius, Weil positivity; no repeated generator, unweighting, zero-dependent quotient, assumed factorization-tree equality, or unproved conditional rearrangement.
- Prior multiplication-fibre route: `mem:rh/coprime-deletion-multiplication-fibre-architecture-2026-09-05`.
- Main card: `docs/drafts/pipeline/1-in-progress/rh-corpus-architecture-audit-2026-09-05.md`.
- Paper boundary note: `docs/drafts/pipeline/3-formalized/euler-deletion-factorization-boundaries.md`.
- STATUS facts: F680--F695, CANNOT-306--319, MUST-215--223.
