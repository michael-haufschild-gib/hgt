# Literature and novelty audit

Audit frozen: 2026-08-03. Scope: Stokes/fission contact matrices, generalized Cartan signatures,
nonabelian Hodge graphs, ultrametric/tree matrices, effective resistance, and type-A leg
extensions. A negative search is evidence, not a proof that differently worded or unpublished work
does not exist.

## Primary geometric sources

### Biquard--Boalch (2004)

- O. Biquard and P. Boalch, *Wild non-abelian Hodge theory on curves*, Compos. Math. 140,
  179--204, DOI 10.1112/S0010437X03000010.
- Supplies wild nonabelian Hodge context. Does not state a Cartan inertia law.

### Boalch--Yamakawa (2020)

- P. Boalch and D. Yamakawa, *Diagrams for nonabelian Hodge spaces on the affine line*, C. R.
  Math. 358, 59--65, DOI 10.5802/crmath.11.
- Supplies diagram/core/type-A-leg framework. No universal signature or second-eigenvalue theorem
  located.

### Douçot (2021)

- J. Douçot, *Diagrams and irregular connections on the Riemann sphere*, arXiv:2107.02516v3.
- Theorem 1.1 gives `dim M_B = 2-(d,d)` for Cartan matrix `C=2-B`; paper defines diagrams for
  arbitrary multi-pole, possibly ramified data and proves invariance under symplectic Weyl-algebra
  automorphisms, including Fourier--Laplace.
- Search of full HTML found no Cartan signature, inertia, Lorentzian, capacity, effective-resistance,
  or `lambda_2 <= 2` theorem.

### Boalch--Douçot--Rembado (2025)

- P. Boalch, J. Douçot, G. Rembado, *Twisted local wild mapping class groups: configuration
  spaces, fission trees and complex braids*, PRIMS 61, 391--445, DOI 10.4171/PRIMS/61-3-4.
- Supplies general fission-tree/deformation-class framework. No Cartan one-defect theorem located.

### Boalch (2025)

- P. Boalch, *Counting the fission trees and nonabelian Hodge graphs (untwisted case)*, J. Geom.
  Phys. 214, 105512, DOI 10.1016/j.geomphys.2025.105512.
- Explicitly frames which special graphs/Kac--Moody systems occur as an open classification
  question and records hyperbolic examples. Full-text search found no `eigenvalue` or Cartan
  signature theorem. Current paper does not claim discovery of hyperbolic examples; it excludes
  every signature beyond Lorentzian.

### Douçot (2026)

- J. Douçot, *Basic representations of genus zero nonabelian Hodge spaces*, SIGMA 22 (2026), 027,
  DOI 10.3842/SIGMA.2026.027.
- Theorems 1.4--1.6 provide symplectic-invariant enriched trees and a generic class whose Stokes
  circles are all at infinity. The paper carefully distinguishes weak representations and says the
  analytic isomorphisms of the resulting isomonodromy systems are expected in general.
- Current manuscript uses only invariant combinatorial diagram equality, never the expected
  analytic isomorphism.

### Douçot (2025/2026 twisted graphs)

- J. Douçot, *New nonabelian Hodge graphs from twisted irregular connections*,
  arXiv:2509.24861.
- Theorem 1.8 gives rescaled ultrametric/loop inequalities; Theorem 1.10 characterizes untwisted
  fission graphs by the ultrametric condition. Proposition 3.3 supplies the sharp twisted triangle
  with edge multiplicities 6, 3, 4.
- Full-text search found no occurrences of `eigenvalue` or `signature`. The paper gives necessary
  graph conditions and examples, not the Cartan rank-one defect or global inertia theorem.

## Matrix-theory parent literature

### Martínez--Michon--San Martín (1994)

- *Inverse of strictly ultrametric matrices are of Stieltjes type*, SIAM J. Matrix Anal. Appl. 15,
  98--106, DOI 10.1137/S0895479891217011.
- Strict ultrametric inverse positivity and filtered spectral decomposition. Parent theory only.

### McDonald--Neumann--Schneider--Tsatsomeros (1995)

- *Inverse M-matrix inequalities and generalized ultrametric matrices*, Linear Algebra Appl. 220,
  321--341, DOI 10.1016/0024-3795(94)00077-Q.
- Generalized ultrametric/inverse M-matrix inequalities. Does not specialize the Stokes
  normalization `C=2I-B` or give the genus-zero one-defect conclusion.

### Nabben--Varga (1995)

- *Generalized ultrametric matrices---a class of inverse M-matrices*, Linear Algebra Appl. 220,
  365--390, DOI 10.1016/0024-3795(94)00086-S.
- Weighted-tree characterization and rank-at-most-two decompositions for generalized ultrametric
  matrices. This makes the tree Gram component classical. It does not state the Stokes--Cartan
  rank-one subtraction, capacity wall, leg conservation, or Kac--Moody exclusion.

### Nabben (July 2026)

- R. Nabben, *Inverse acyclic Z-matrices, matrices of tree structure and shifted generalized
  ultrametric matrices*, arXiv:2607.27221.
- Audited because it is the closest current collision. It characterizes tree-structured matrices,
  shifted generalized ultrametric matrices, and inverse acyclic Z/M/N matrices. Full-text searches
  for `inertia`, `negative eigenvalue`, `rank-one`, and `Lorentz` returned no match. It contains no
  Stokes/fission application, capacity trichotomy, type-A leg law, or `lambda_2` obstruction.

## Searches run

Exact and near-exact web searches included:

- `"nonabelian Hodge graph" "second eigenvalue"`
- `"fission graph" Lorentzian Cartan signature`
- `"nonabelian Hodge" Cartan "negative eigenvalue"`
- `Stokes Cartan capacity effective resistance fission tree`
- `nonabelian Hodge graph Cartan signature inertia`
- `generalized ultrametric rank one perturbation Lorentzian`

Results returned the primary diagram/fission papers above and unrelated uses of the terms. No
direct statement of the manuscript's theorem surface was found.

## Novelty verdict

The abstract linear algebra fact “positive definite matrix minus one rank-one matrix has negative
index at most one” is classical and is not a publishable novelty claim. The surviving new claim is
the geometric identity forcing **every** type-A genus-zero Stokes--Cartan matrix into that form,
together with:

1. intrinsic capacity/effective-resistance wall and determinant factorization;
2. exact corona pruning;
3. arbitrary type-A leg preservation;
4. principal-conormal and dimension conservation identities;
5. global finite/affine/Lorentz trichotomy;
6. `lambda_2(B) <= 2` and exclusion of higher-signature Kac--Moody diagrams.

This boundary survived source-by-source audit through 2026-08-03. External expert review and normal
journal priority checks remain necessary; no internal audit can certify absence of unpublished work.
