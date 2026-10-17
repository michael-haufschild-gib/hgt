# Unbounded dissipative calculus on the literal prime Burnol core

- **ID:** cross-route-11-prime-dissipative-core
- **Stage:** 1-in-progress
- **Type:** CANDIDATE — uncounted
- **Source:** whole local Lean corpus; no external novelty claim
- **Target:** Every holomorphic function psi on Re z > 0 with Re psi >= 0
  defines a unique closed maximal dissipative generator whose graph is the
  closure of the literal finite-prime pairs (v_p, -psi(log p) v_p).
  Its exact domain is the range of the bounded operator with symbol
  1/(1+psi); its contraction evolution has symbol exp(-t psi) and is strongly
  continuous. No extra core or source-admission assumption is permitted.

## Required structural payoff

This moves the actual-prime Burnol route from bounded operators and bounded
finite-jump generators to arbitrary accretive holomorphic symbols, including
unbounded generators. The decisive statement is the exact closed graph and
its equality with the literal right-derivative domain of the evolution.
Scalar multiplier identities alone are not a contribution.

Required actual instance: psi(z)=1/z gives an unbounded generator even though
all its actual-prime eigenvalues have modulus at most 1/log 2. This exhibits
why bounded individual prime readings cannot replace the graph-domain audit.
The full realization, domain classification and instance count once.

## Gates

- [x] Source-pure statement and dependency-closed paper proof.
- [x] Whole-corpus search and direct-source comparison completed for the lead.
- [ ] Targeted Lean construction and maximal-domain proof.
- [ ] Explicit unbounded reciprocal-symbol instance with bounded prime readings.
- [ ] Public axiom/signature audit, novelty reassessment, wiring, index and lint.
- [ ] Count only after all required parts close.

## Dependency-closed paper proof [PROVED HERE]

Write H for the actual Burnol half-line Hilbert space and v_p for the literal
critical-prime feature. The corpus proves span{v_p} dense and uniquely realizes
every bounded holomorphic symbol as a bounded operator with equal norm.

1. Set r(z)=1/(1+psi(z)). Since Re psi >= 0, r is holomorphic, |r|<=1,
   r never vanishes, and |1-2r|<=1. Realize r as R and 1-2r as C=I-2R.
   The nonzero eigenvalues r(log p) imply range(R) contains every v_p, hence
   is dense. If Rf=0, Cf=f. For a contraction, Cf=f implies C* f=f:
   expand ||C* f-f||^2 and use ||C* f||<=||f|| and
   inner(C* f,f)=inner(f,Cf)=||f||^2. Therefore R* f=0; dense range(R)
   forces f=0. Thus R is injective with dense range.

2. Let G be the closure of span{(v_p,-psi(log p)v_p)} in H x H.
   Every generating pair satisfies R(u-v)=u, so G lies in this closed
   kernel. Conversely, for every w in H the pair (Rw,Rw-w) is in G:
   the preimage of G under this continuous map is a closed subspace
   containing every v_p, because its value there is r(log p) times the
   generating pair. Density finishes the argument. Hence
   G={(u,v):R(u-v)=u}={(Rw,Rw-w):w in H}. Injectivity of R makes this a
   graph, with dense domain range(R), exactly the closure of the finite-prime
   graph. This proves closability and the core property together.

3. The Cayley contraction gives ||u+v||<=||u-v|| on G, so
   Re inner(u,v)<=0. Every forcing f has the unique solution
   u=Rf, v=Rf-f to u-v=f. Any dissipative linear extension of G equals G:
   subtract its pair (u,v) from the G-pair with the same u-v; the difference
   is (w,w), whose dissipativity implies ||w||^2<=0. This is maximality,
   derived without an external maximality premise.

4. Realize exp(-t psi) as T_t for t>=0. Norm(T_t)<=1. Equality on the
   dense actual-prime features gives T_0=I, T_(s+t)=T_s T_t and T_t R=R T_t.
   Scalar exponential continuity holds on the finite-prime span. Uniform
   contraction extends it to every H-vector by the corpus dense-set strong
   convergence theorem. Thus this is a genuine C0 contraction evolution.

5. Define L_t f=integral_0^t T_s f ds; strong continuity makes this a bounded
   operator, norm<=t. The scalar exponential fundamental theorem, first on
   each v_p and then by density, gives T_t R-R=L_t(R-I).
   A G-pair (u,v) therefore satisfies T_t u-u=L_t v; the vector fundamental
   theorem gives right derivative v at zero. Conversely, if that right
   derivative is v, commute R with T_t and differentiate
   R(T_t u-u)=L_t(Ru-u) to get Rv=Ru-u, exactly the defining equation of G.
   Hence the graph domain is the complete literal right-derivative domain.

6. For every z with Re z>0, the realized r-eigenvalue gives
   (e_z,-psi(z)e_z) in G, with e_z the nonzero actual complex Burnol feature.
   For psi(z)=1/z, Re psi>0 on the half-plane, while psi(x)=1/x tends to
   infinity as x decreases to zero. These graph pairs violate every bound
   ||v||<=B||u||. Yet at actual primes |psi(log p)|<=1/log2. All data are
   explicit. No RH premise or unknown spectral/source class enters.

## Direct-source novelty audit

- Contributions 6 and 7 classify bounded actual-prime operators, their norms
  and physical positivity. They do not identify unbounded generator graphs.
- Contribution 9 assumes a bounded generator and proves its finite-jump
  classification. It excludes the reciprocal-symbol instance above.
- PrimeLogLaplaceMaximalDomain (contribution 4) closes a map from prime l2
  coefficients into literal Laplace profiles. Here both graph coordinates
  lie in the physical Burnol space and psi is arbitrary accretive holomorphic.
- FokasLenellsCausalGeneratorCriterion and FokasLenellsCausalAnalyticGraphCore
  prove exact derivative/core statements for a particular causal Cauchy
  evolution. Their method supplies the domain argument, but they contain no
  arbitrary-symbol construction or literal prime core.
- StrongConvergenceDense supplies the strong-continuity extension. The
  Cayley dense-range injectivity argument above avoids assuming an outer
  multiplier or injective resolvent.
- ContractionCayleyTransform already proves generic accretive partial-map
  maximality and a resolvent-image graph core, conditional on its specified
  injectivity and density data. Those generic facts are not claimed as new.
  Here the literal prime source discharges every admission for arbitrary psi,
  and the closed graph is proved to be the full C0 derivative graph.
- BurnolValuationCayleyFrame already realizes the particular Cayley transforms
  of phase-weighted shifts, with depth-span cores and unbounded valuation
  contrasts. An unbounded Burnol operator or bounded diagonal readings alone
  are therefore not novel here. The proposed advance is the entire accretive
  holomorphic class on the actual prime core, with exact C0 derivative domain;
  the reciprocal symbol is a required concrete instance, not a separate count.
- RoutePPrimitiveBurnolWardResolvedGeneratorGraph treats the particular radial
  multiplication generator and its energy blow-up. The aperture damping
  semigroup treats forward shifts and literal source energies. Neither gives
  the arbitrary accretive-symbol calculus or reciprocal prime-core instance.
- Whole-corpus deep dissipative query: partial=false, 73,192 inventoried
  files, 1,083,280 declarations; compiler freshness and semantic-coverage
  warnings remain. Direct source and compiler verification are authoritative.
- Earlier Bockstein/Smith/Koszul and Bernstein-semigroup searches were only
  exploratory. No theorem from either exploration was counted or formalized.

## Work plan

1. Generic Cayley contraction, dense-range injectivity and closed graph lemma.
2. Actual accretive-symbol resolvent and exact finite-prime graph closure.
3. Contractive C0 evolution, integrated identity and full derivative criterion.
4. Reciprocal-symbol unbounded instance, audits and integration.

- 2026-10-17 — card opened before new Lean code. Count remains 10/100.
- Generic Cayley, accretive resolvent, and exact prime graph leaves compile
  cleanly. This includes graph closure, dense exact domain, single-valuedness
  and maximal dissipativity. Evolution, integrated identity and derivative
  criterion are written and awaiting their targeted compiler checks.
- Strong contraction evolution, integrated resolvent identity, and both
  directions of the complete right-derivative criterion now compile cleanly.
  A direct unique-closed-dissipative-prime-realization theorem is being checked;
  reciprocal instance and the final axiom/signature/wiring gates remain.
