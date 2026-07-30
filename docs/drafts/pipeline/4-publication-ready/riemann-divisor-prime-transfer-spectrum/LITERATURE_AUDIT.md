# Literature and novelty audit

Audit date: 2026-07-30.

## Audited theorem package

The manuscript does not claim novelty for Möbius inversion, \(k\)-free Dirichlet series,
same-zero modifications of zeta, individual hypertranscendence, logarithmic residues, or the
phrase “critical line as unitary locus.” Its priority claim is the following exact conjunction.

1. The largest-prime-exponent partition gives pairwise coefficient-disjoint positive Dirichlet
   series \(S_n=\zeta H_n\).
2. Every \(H_n\), \(n\ge 12\), is holomorphic and zero-free on
   \(\operatorname{Re}s>1/2\); every positive channel therefore carries the complete zeta divisor
   there, with multiplicity.
3. The transverse multipliers \((H_n)_{n\ge2}\) are jointly differentially algebraically
   independent over \(\mathbb C(s)\langle\zeta\rangle\).
4. The same shell has the two successive cofinal atom laws
   \[
   2^{ns}H_n(s)\to1-2^{-s},
   \]
   \[
   3^{ns}\!\left(H_n(s)-2^{-ns}(1-2^{-s})\right)\to1-3^{-s}.
   \]
5. Adjacent-depth transfer produces \(2^{1/2-s}\) and, after first-atom removal,
   \(3^{1/2-s}\). Their pair is globally injective because
   \(\log3/\log2\) is irrational. More generally,
   \[
   s\longmapsto(q^{c/2-s},r^{c/2-s})
   \]
   is globally injective if and only if \(\log r/\log q\) is irrational, while no
   single-scale reporter is injective. Thus unrestricted modular tomography has exact minimal
   rank two.
6. The centered Xi divisor-current residue and every base-normalized cofinal transfer entropy
   are the same invariant:
   \[
   \operatorname{Re}\operatorname{Res}_{s=\rho}
   \!\left[-(s-\tfrac12)\frac{\Xi'(s)}{\Xi(s)}\right]
   =
   m_\rho\frac{\log|q^{1/2-\rho}|}{\log q}
   =
   m_\rho(\tfrac12-\operatorname{Re}\rho).
   \]
7. Unit-weight scalar label erasure is nonclosable, while the two-prime cofinal spectrum retains
   the complete spectral point.

No checked source states this package, the second-atom transfer theorem, its universal
incommensurable two-scale tomography law as the cofinal spectrum of an isodivisorial positive
frame, or the local–cofinal residue transgression.

## Closest primary literature

| Source | Prior result | Collision boundary |
|---|---|---|
| A. Ostrowski, “Über Dirichletsche Reihen und algebraische Differentialgleichungen,” *Math. Z.* 8 (1920), 241–298, [DOI](https://doi.org/10.1007/BF01206523) | Differential transcendence of Dirichlet series | Makes one-function hypertranscendence classical; no positive isodivisorial frame or cofinal transfer spectrum |
| A. G. Postnikov, “On the differential independence of Dirichlet series,” *Dokl. Akad. Nauk SSSR* 66 (1949), 561–564 | Differential independence of systems | Parent subject; no relative independence over the zeta differential field or RH divisor application |
| H. N. Shapiro and G. H. Sparer, “On algebraic independence of Dirichlet series,” *Comm. Pure Appl. Math.* 39 (1986), 695–745, [DOI](https://doi.org/10.1002/cpa.3160390602) | Jacobian methods for algebraic independence | Parent method; no largest-exponent shell, divisor replication, or transfer transgression |
| W. Y. Pong, “Applications of differential algebra to algebraic independence of arithmetic functions,” *Acta Arith.* 172 (2016), 149–173, [DOI](https://doi.org/10.4064/aa8112-12-2015) | Arithmetic derivations and differential-algebraic independence | Parent algebraic framework; no isodivisorial positive frame or two-atom tomography |
| H. Nagoshi, “The hypertranscendence of \(L\)-functions for \(\mathrm{GL}_m(\mathbb A_{\mathbb Q})\),” *Bull. Aust. Math. Soc.* 93 (2016), 388–399, [DOI](https://doi.org/10.1017/S000497271500129X) | Hypertranscendence of broad \(L\)-function classes | Excludes novelty for individual hypertranscendence |
| E. Grosswald and F. J. Schnitzer, “A class of modified \(\zeta\) and \(L\)-functions,” *Pacific J. Math.* 74 (1978), 357–364, [DOI](https://doi.org/10.2140/pjm.1978.74.357) | Modified Euler products preserving zeros and multiplicities | Excludes novelty for same-zero replicas alone; their family is not a positive coefficient-disjoint, relatively differential-free resolution with cofinal tomography |
| X.-J. Li, “The positivity of a sequence of numbers and the Riemann hypothesis,” *J. Number Theory* 65 (1997), 325–333, [DOI](https://doi.org/10.1006/jnth.1997.2137) | Cayley-coordinate zero criterion | No exponent-shell transfer or local–cofinal current identity |
| E. Bombieri and J. C. Lagarias, “Complements to Li’s criterion for the Riemann hypothesis,” *J. Number Theory* 77 (1999), 274–287, [DOI](https://doi.org/10.1006/jnth.1999.2392) | General multiset form of Li’s criterion | No positive isodivisorial frame or prime transfer spectrum |
| A. Voros, “Zeta functions over zeros of zeta functions and an exponential-asymptotic view of the Riemann hypothesis,” [arXiv:1403.4558](https://arxiv.org/abs/1403.4558) | Large-order exponential signatures of off-line zeros | Closest asymptotic vocabulary; the expansion is in Li order, not successive Möbius atoms of a positive divisor frame |
| P. M. Gauthier and X. Xarles, “Perturbations of \(L\)-functions with or without non-trivial zeros off the critical line,” [arXiv:0911.5135](https://arxiv.org/abs/0911.5135) | Functional-equation-preserving insertion of off-line quartets | Establishes compact-open instability; no cofinal recovery theorem |
| A. Connes and C. Consani, “The scaling Hamiltonian,” *J. Operator Theory* 85 (2021), 257–276, [arXiv:1910.14368](https://arxiv.org/abs/1910.14368) | Scaling/trace-formula framework and positivity boundary | “Scaling” and “unitarity” language overlap only; no adjacent reciprocal-dilation shell cocycle or modular-residue transgression |

## Exact-expression and concept searches

Searches included:

- `"zeta((n+1)s)" "zeta(ns)"`;
- `"1/zeta((n+1)s)" "1/zeta(ns)"`;
- `"3^(ns)" reciprocal zeta asymptotic`;
- `"second atom" reciprocal Riemann zeta Möbius`;
- `"2^{1/2-s}" "3^{1/2-s}" Riemann zeta`;
- `Riemann zeta exponent shells Möbius atoms transfer spectrum`;
- `Riemann zeta critical line Lyapunov exponent transfer matrix unitarity`;
- `divisor current residue Lyapunov exponent zeros zeta transgression`;
- formula and citation-trail searches around Grosswald–Schnitzer, Ostrowski, Shapiro–Sparer,
  Pong, Li, Voros, and Connes–Consani.

No formula-level collision was found. Search failure is evidence, not proof of absence; specialist
priority review remains required.

## Claims allowed

- new positive hypertranscendental isodivisorial frame, as a conjunction;
- new first-two-atom cofinal transfer spectrum of that frame;
- new exact minimal-rank-two modular tomography classification and its globally injective
  prime-two/prime-three shell realization;
- new base-independent local–cofinal modular-residue transgression;
- new information-localization theorem separating divisor replication, finite differential rank,
  Hilbert label erasure, and cofinal recovery;
- a new structural route for RH: derive asymptotic isometry of the arithmetic transfer before
  scalarization, rather than attempt to recover orientation after an even or diagonal observer.

## Claims prohibited

- proof or disproof of RH;
- zero exclusion;
- a source-derived upper bound for off-line defect count;
- novelty for \(k\)-free Euler products, Möbius inversion, same-zero replicas, individual
  hypertranscendence, or logarithmic residues;
- a no-go for all Hilbert–Pólya, Connes–Consani, Hedenmalm, trace-formula, or diagonal routes;
- that reflection symmetry implies ordinary unitarity;
- that positivity of Dirichlet coefficients survives analytic continuation as a sign theorem;
- that literature search proves priority.

## Antagonist significance boundary

The two formulas \(p^{1/2-s}\) and
\(\log|p^{1/2-s}|/\log p=1/2-\operatorname{Re}s\) are elementary once written down.
They are not independently significant. The publication case rests on their forced emergence from
successive asymptotic layers of one explicit positive coefficient-disjoint family which:

- carries the exact Riemann divisor in every channel;
- has maximal relative differential rank after zeta and all its derivatives are adjoined;
- cannot be assembled by a closable unit scalar codiagonal;
- nevertheless recovers the entire spectral coordinate from two cofinal atom transitions; and
- identifies its horizontal transfer entropy exactly with the local Xi divisor-current residue.

This is a closed localization and tomography theorem, not an RH solution. It is potentially
publishable in a strong broad mathematics journal if specialist review confirms priority and the
full proofs remain as transparent as the theorem statement. It is not an honest Nature/Science or
top-four mathematics claim without an additional arithmetic mechanism forcing transfer
isometry—and the manuscript does not pretend otherwise.
