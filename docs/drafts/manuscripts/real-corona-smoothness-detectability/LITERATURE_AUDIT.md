# Literature and novelty audit

Audit date: 2026-08-03. Target: theoretical paper at general-journal level. Searches used primary
papers/preprints and author manuscripts; no novelty conclusion rests on a survey snippet.

## Primary sources checked

1. Connes--Consani--Marcolli, *The Weil proof and the geometry of the adeles class space*,
   [arXiv:math/0703392](https://arxiv.org/abs/math/0703392). It defines cyclic homology of the
   cokernel of the class-space restriction in the abelian category of cyclic modules and formulates
   the Weil explicit formula as a Lefschetz trace.
2. Meyer, *On a representation of the idele class group related to primes and zeros of
   L-functions*, [arXiv:math/0311468](https://arxiv.org/abs/math/0311468). It constructs the
   bornological idele-class representation whose character is the Weil distribution.
3. Paugam, *Spectral symmetries of zeta functions*,
   [arXiv:0803.0199](https://arxiv.org/abs/0803.0199). It constructs symplectic/orthogonal spectral
   pairings compatible with functional equations.
4. Carboni--Guccione--Guccione, *Cyclic homology of crossed products*,
   [arXiv:0805.0582](https://arxiv.org/abs/0805.0582). It gives mixed complexes and spectral
   sequences for crossed-product cyclic homology.
5. Moscovici, *Local index formula and twisted spectral triples*,
   [arXiv:0902.0835](https://arxiv.org/abs/0902.0835). It analyzes JLO retraction and local index
   formulas when twisted commutators change cocycle identities.
6. Connes--Consani, *Hochschild homology, trace map and zeta-cycles*,
   [arXiv:2207.10419](https://arxiv.org/abs/2207.10419). It studies spectral realizations and stable
   zeta-cycles through Hochschild homology and trace maps.
7. Connes--Consani--Moscovici, *Zeta spectral triples*,
   [arXiv:2511.22755](https://arxiv.org/abs/2511.22755). It constructs finite/truncated self-adjoint
   spectral models numerically approximating low zeta zeros and discusses convergence as an open
   problem.
8. Cortiñas--Valqui, *Excision in bivariant periodic cyclic cohomology: a categorical approach*,
   [arXiv:math/0207178](https://arxiv.org/abs/math/0207178). It extends Cuntz--Quillen excision to
   categorical/topological/bornological bivariant settings.

Classical local-index, JLO, entire-function, isolated-zero, Haar-measure, and Dirichlet-L-function
inputs were also checked against the bibliographic sources cited in the manuscript and against the
pinned mathlib APIs used by the formal proof.

## Novelty matrix

| Result in manuscript | Closest prior structure | Difference checked |
|---|---|---|
| Smoothness--detectability conservation | standard grading decomposition and bounded-commutator definition | Exact invariant-domain equivalence `D bounded iff even and odd bounded`, followed by classification of every unbounded smooth realization as unbounded-even/bounded-odd, was not found as a named law or applied to zeta divisor orientation. |
| Complete-divisor local-series no-go | Connes--Moscovici/JLO local formulas; zeta spectral triples | Prior work seeks or computes local characters. No source found proving termwise extinction of every positive orientation jet plus exact functional-equation cancellation of every summable degree-zero term on the complete multiplicity divisor. |
| Exact CCM strong landing in all degrees | CCM cyclic cokernel; Meyer's strong class-space target | CCM supplies conceptual target. No source found carrying the actual rational Bruhat source through finite-adelic Haar normalization, common-period Poisson cancellation, profinite local constancy, Schatten-1 Morita continuity, and total-product reduction in every cyclic degree. |
| Multiplication fracture | cyclic-module cokernel in CCM; general crossed-product cyclic complexes | Sources treat target as cyclic-linear. No source found giving actual Schatten matrix-unit witnesses with trace `0,0,1`, proving exact strong degree zero is not two-sided, and deducing impossibility of representative-preserving quotient multiplication. |
| Clifford Lefschetz comparison | Paugam symmetry; CCM Lefschetz action; bivariant cyclic theory | No source found identifying the parity obstruction between anti-Real corona character and Real-even CCM Lefschetz translations, classifying every scalar correction by `conj z = -z`, or proving the positive Clifford choice `iL_c` has square `-1` at identity. |
| Endpoint-holomorphic classification | identity theorem; dense polynomial restrictions | Classical ingredients are elementary. Novel part is exact crossed-product classification for the compactified Real-corona idempotent and its coupling to complete self-dual divisor geometry. |
| Positive-degree P3 no-go | Hadamard factorization and standard infinitude of L zeros | No source found using a zero-count-free finite-divisor rigidity route to derive endpoint nonsmoothness for the stated analytic completion class, then formalizing actual Riemann and self-dual primitive Dirichlet cases. |
| Fixed-sector/rank variation | functional-equation parity and analytic rank | Root-number parity is standard. No source found decomposing Real-corona fixed cyclic defect variation as rank variation plus twice off-central variation, while isolating coordinate-K0 support and exact multiplicity excess. |

## Anti-theatre checks

- P1 does not call a commuting orientation a local index formula. It defines the full allowed local
  series and proves its value is zero; the nonzero target charge is separately formalized.
- P2 does not place an idempotent in a cyclic-module quotient. It first proves the target is not
  two-sided and that no representative multiplication descends.
- P2's positive result is a cyclic-module morphism, not an asserted equality in unconstructed
  bivariant homology. Manuscript calls it a bivariant cyclic representative and states completion
  limits explicitly.
- P3 does not assume zero infinitude in its positive-degree analytic interface. Lean derives it
  from subquadratic growth and superlinear ray growth. The more general divisor theorem, which does
  assume infinitude, is labeled separately.
- P3 does not claim all possible dense smooth algebras. It classifies the explicitly defined,
  reflection-invariant endpoint-holomorphic algebra.
- P4 distinguishes coordinate K0 rank, total cyclic rank, analytic multiplicity, and support.
- No result is advertised as RH, GRH, Weil positivity, or convergence of zeta spectral triples.

## Novelty verdict

No checked source contains the universal law or any of the four exact resolution packages. Several
ingredients are classical; novelty lies in the dependency-closed conservation/obstruction theorem,
the literal CCM strong target calculation, and the forced Clifford/fixed-sector dichotomy. The P2
landing and multiplication fracture provide the strongest specialist content. P1, P3, and P4 are
structural consequences that make the package broad enough for a general journal while retaining
explicit limits.

Status: **novel after primary-source audit**, subject to ordinary referee discovery of uncatalogued
work and final citation update immediately before submission.
