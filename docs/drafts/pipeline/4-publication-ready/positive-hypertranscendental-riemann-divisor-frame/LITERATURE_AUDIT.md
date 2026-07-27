# Literature and novelty audit

Audit date: 2026-07-27  
Scope: largest-prime-exponent shells, \(k\)-free Dirichlet series, zeta-divisor
replication, adjacent reciprocal zeta dilations, joint differential algebraic
independence, and RH reformulations by positive Dirichlet subseries.

## Verdict

No checked source contains the paper's theorem package:

1. the coefficient-disjoint positive partition by largest prime exponent;
2. zero-free adjacent reciprocal-dilation factors
   \(H_m=\zeta((m+1)s)^{-1}-\zeta(ms)^{-1}\) on \(\Re s>1/2\);
3. exact replication, with multiplicity, of the zeta zero divisor by every shell
   \(S_m=\zeta H_m\), \(m\ge 12\);
4. joint differential algebraic independence of the larger multiplier family
   \((H_m)_{m\ge2}\) over the enlarged base
   \(\mathbb C(s)\langle\zeta\rangle\);
5. the \(\Omega\)-leading-echelon criterion that proves finite-jet independence
   from pure-prime lowest layers while ignoring every higher arithmetic layer;
6. coexistence of exact infinite positive fusion with maximal finite
   differential rank;
7. the resulting RH failure law: every off-critical zero must recur, with the
   same multiplicity, in every pairwise-disjoint positive shell.

Novelty should be claimed as the simultaneous theorem and relative statement,
not for any one classical ingredient. External specialist review remains needed
before asserting priority without qualification.

## Closest primary literature

| Source | Established result | Collision boundary |
|---|---|---|
| A. Ostrowski, *Über Dirichletsche Reihen und algebraische Differentialgleichungen*, Math. Z. 8 (1920), 241–298, [DOI](https://doi.org/10.1007/BF01206523) | Classical differential transcendence results for Dirichlet series | Establishes that one-source hypertranscendence is old; does not give this countable relative family, common divisor, or positive shell partition |
| A. G. Postnikov, *On the differential independence of Dirichlet series*, Dokl. Akad. Nauk SSSR 66 (1949), 561–564 | Differential independence for systems of Dirichlet series | Establishes that system-level differential independence is old; the paper's candidate novelty must rest on the explicit relative base, \(\Omega\)-graded tail immunity, and RH divisor frame |
| H. N. Shapiro and G. H. Sparer, *On algebraic independence of Dirichlet series*, CPAM 39 (1986), 695–745, [DOI](https://doi.org/10.1002/cpa.3160390602) | Jacobian methods for algebraic independence of Dirichlet series | Parent method; no largest-exponent zeta shells, zero-free dilation theorem, or independence over the zeta differential field |
| W. Y. Pong, *Applications of differential algebra to algebraic independence of arithmetic functions*, Acta Arith. 172 (2016), 149–173, [DOI](https://doi.org/10.4064/aa8112-12-2015) | Differential-algebraic use of arithmetic-function derivations and Jacobians | Parent algebraic framework; no explicit RH divisor frame or relative multiplier theorem |
| H. Nagoshi, *The hypertranscendence of L-functions for \(\mathrm{GL}_m(\mathbb A_{\mathbb Q})\)*, Bull. Aust. Math. Soc. 93 (2016), 388–399, [DOI](https://doi.org/10.1017/S000497271500129X) | Hypertranscendence for broad \(L\)-function classes | Rules out novelty claims based on individual hypertranscendence; does not imply the stated joint relative independence without a new independence argument |
| E. Grosswald and F. J. Schnitzer, *A class of modified \(\zeta\) and \(L\)-functions*, Pacific J. Math. 74 (1978), 357–364, [DOI](https://doi.org/10.2140/pjm.1978.74.357) | Modified Euler products preserving zeros and multiplicities in a half-plane | Rules out novelty of “same zeros as zeta” alone; their replicas are not this positive disjoint partition and carry no relative hypertranscendence theorem |
| M. Chiang and S. Feng, *On the Nevanlinna characteristic of \(f(z+\eta)\) and difference equations in the complex plane*, Ramanujan J. 16 (2008), 105–129, and related zeta-shift work | Difference independence and growth tools for shifted meromorphic functions | Additive shifts, not reciprocal integer dilations or a coefficient-disjoint common-divisor family |
| S. M. Voronin, work on functional independence and universality of zeta | Functional/differential independence phenomena for zeta values and shifts | Different variables and approximation mechanism; no largest-exponent shell source or relative family over \(\mathbb C(s)\langle\zeta\rangle\) |

## Exact-expression searches

Current searches included:

- `"largest prime exponent" Dirichlet series zeta zeros`;
- `"zeta((m+1)s)" "zeta(ms)" differential algebraic independence`;
- `"reciprocal zeta" dilations algebraic independence`;
- `"same zeros" zeta Dirichlet series positive coefficients`;
- `largest exponent prime factorization shell Dirichlet series`;
- `joint hypertranscendence zeta dilations`;
- `differential independence reciprocal Riemann zeta functions`;
- `positive Dirichlet subseries same zeros Riemann zeta`;
- MathSciNet-style searches by formula, title terms, and citation trails from
  Ostrowski, Shapiro–Sparer, Pong, and Nagoshi.

No exact formula-level or theorem-package collision was located. Search results did
recover generic observations that multiplying zeta by a zero-free Dirichlet series
preserves its zeros; that fact is explicitly excluded from the novelty claim.

## Priority boundaries

Paper may claim:

- new explicit positive Riemann-divisor frame;
- new uniform zero-free theorem for the adjacent reciprocal-dilation factors in
  the strict right half-plane;
- new joint relative hypertranscendence statement, starting at \(m=2\), over
  \(\mathbb C(s)\langle\zeta\rangle\);
- new \(\Omega\)-leading-echelon source criterion in the stated tail-immune form;
- new simultaneous-cancellation law for any hypothetical off-critical zero.

Paper must not claim:

- a proof or disproof of RH;
- novelty for \(k\)-free Euler products;
- novelty for same-zero replicas in general;
- novelty for individual Dirichlet-series hypertranscendence;
- the first Jacobian criterion for arithmetic functions;
- optimality of the threshold \(12\);
- that differential independence alone excludes common zeros;
- a no-go for Hilbert–Pólya, CCM, trace formulas, or Euler products.

## Significance assessment

The bare identity \(S_m=\zeta H_m\) is not significant. The publishable object is
the relative theorem:

\[
\{H_m:m\ge2\}
\text{ is differentially algebraically independent over }
\mathbb C(s)\langle\zeta\rangle,
\]

combined with positive coefficient disjointness and exact divisor replication.
Adjoining zeta and all of its derivatives removes the obvious common-factor
explanation before rank is measured. This answers the principal referee objection
“these are merely zeta times units.”

The \(\Omega\)-leading-echelon theorem supplies a reusable result beyond RH.
The RH application adds a concrete and surprising consequence: a single off-line
zero would be forced as an equal-multiplicity cancellation in countably many
disjoint nonnegative arithmetic channels whose normalized directions have no
finite differential-algebraic coupling.

Expected audience: analytic number theorists, differential algebraists, and
researchers studying structural or positivity approaches to RH.
