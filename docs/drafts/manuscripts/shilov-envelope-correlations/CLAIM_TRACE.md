# Claim trace: Shilov correlation law

## Main claims

| Manuscript claim | Status | Dependency | Formal target |
|---|---|---|---|
| Edge common quotient \(Q_q\) and pullback \(\Gamma_q=E_S\times_{Q_q}E_T\) | Paper proof complete | Universal-cover epimorphism; second isomorphism theorem | Pullback relation theorem |
| Vertical extension \(0\to\mathcal K_q\to\ker p_T\to\Def(q)\to0\) and \(\ker p_S\cong\Esc(q)\) | Paper proof complete | Quotient kernel calculation | Existing quotient core + new exact kernel wrapper |
| Correlations form a category | Paper proof complete | Fiber product and closed image of a \(C^*\)-homomorphism | Abstract relation composition |
| \(q\mapsto\Gamma_q\) is normal oplax | Paper proof complete | Universal maps compose uniquely | Inclusion under relational composition |
| Finite path ambiguity equals transported ideal join | Paper proof complete | Induction on intermediate representatives | Finite family quotient/join theorem |
| Minimal semisimplicial Shilov join completion | Paper proof complete | Face inclusions; compatibility of universal maps | Edge-join minimality formalized; general simplex layer remains paper-only |
| Long exact sequence \(H^*(\mathcal M)\to H^*(\mathcal A)\to H^*(\mathcal Q)\) | Paper proof complete, algebraic | Degreewise short exact sequence | Short-complex exactness only; no topology surrogate |
| \(\operatorname{Mig}^{k+1}=\operatorname{im}\partial=\ker(H^{k+1}\mathcal M\to H^{k+1}\mathcal A)\) isolates boundary-specific cohomology | Paper proof complete | Exactness | Image/kernel identity |
| \(H^0(\mathcal Q)\) equals compatible-correlation algebra | Paper proof complete | Edge pullback theorem | Kernel/equalizer theorem |
| Path migration exact sequence | Paper and Lean proofs complete | Representative correction and recursive lifting | localMigrationSequence_shortExact |
| Zero-escape local envelope continuity and \(\varprojlim^1J_n=0\) | Paper proof complete; analytic dependency cited | Joiţa local Shilov existence/minimality | Existing Lean algebraic core only |
| Universal two-edge transmutation for every unital \(D\) | Paper proof complete | Graph extension, essential ideal, functional calculus | Algebraic shadow only; operator-system layer outside current mathlib |
| Matricial coupling | Paper proof complete | Positive lifting through \(C^*\)-quotients | Existing finite positive lift theorem |
| Faithful boundary detection | Paper proof complete for separable target | Boundary representations determine Shilov ideal | Existing faithful-kernel detection |

## Old-paper shadow map

| Earlier finding | Universal-law location |
|---|---|
| Escape obstructs envelope descent | Source-vertical ideal of \(\Gamma_q\); graph-locus corollary |
| Deficit measures kernel nonexactness | Opposite vertical extension and edge quotient \(M_q/\alpha J_S\) |
| Complete positive/matricial lifting | Both coordinate epimorphisms of \(\Gamma_q\); zero deficit strengthens lifting into \(J_S\) |
| Maximal functorial category | Graph locus of normal oplax correlation functor |
| Deficit composition exact sequence | Quotient sequence of transported-ideal filtration \(\beta\alpha J_S\subseteq\beta J_T\subseteq J_U\) |
| Prescribed deficits and cancellation | Edge faces can be arbitrary; cohomology measures coherent rather than pointwise obstruction |
| Roos exact sequence | One-dimensional zero-escape specialization of long exact sequence |
| Derived Shilov acyclicity | Local-envelope minimality forces \(H^1(\mathcal M)=0\) on zero-escape towers |
| Local \(C^*\)-envelope continuity | \(H^0(\mathcal Q)=R_\Gamma\), specialized to graphs and identified by minimality |
| Faithful positive representations | Vertex Shilov kernels and transported joins detected by boundary sums |
| Representable \(K\)-theory Milnor sequence | Downstream consequence after zero escape identifies local envelope with inverse limit |

## Forbidden upgrades

- Do not call general \(H^1(\mathcal M)\) a \(C^*\)-algebra.
- Do not call all of \(H^k(\mathcal M)\) boundary migration on higher-dimensional diagrams; use \(\operatorname{Mig}^k\).
- Do not claim topological exactness without closed coboundary range.
- Do not claim finite ideal Čech acyclicity as novel.
- Do not claim external novelty audit complete until MathSciNet/zbMATH expert checks.
- Do not formalize operator-system analytic assertions as surrogate axioms.
