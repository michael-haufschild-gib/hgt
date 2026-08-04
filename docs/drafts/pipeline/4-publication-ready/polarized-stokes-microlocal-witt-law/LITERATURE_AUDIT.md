# Literature and priority audit

Audit date: 2026-08-04. Scope: exact polarization/inertia claim, not its classical ingredients.

## Strongest parent results

1. Boalch--Yamakawa, *Diagrams for nonabelian Hodge spaces on the affine line* (C. R. Math.
   358 (2020), 59--65), and Douçot, arXiv:2107.02516v3: established diagram adjacency
   `B_ij = Irr Hom(i,j) - r_i r_j + delta_ij` and the dimension identity
   `dim M_B = 2 - (d,d)`.
2. Boalch, *Counting the fission trees and nonabelian Hodge graphs (untwisted case)*,
   J. Geom. Phys. 214 (2025), 105512: fission-tree classification/counting.
3. Douçot, arXiv:2509.24861: twisted fission trees, ultrametric graph constraints, and the
   three-circle weighted triangle used in the manuscript.
4. Boalch and Boalch--Yamakawa: quasi-Hamiltonian fission/fusion and twisted wild character
   varieties; these supply the geometric ancestry of the global dimension polynomial.
5. Hiroe, J. Geom. Phys. 162 (2021), 104060, and related 2017 work: scalar rigidity/Euler and
   Milnor/intersection identities under additional spectral-curve hypotheses.
6. Sabbah and D'Agnolo--Kashiwara: Stokes structures and irregular/enhanced
   Riemann--Hilbert realization.
7. Martínez--Michon--San Martín (1994), McDonald--Neumann--Schneider--Tsatsomeros (1995), and
   Nabben--Varga (1995): inverse strictly/generalized ultrametric matrix theory.
8. Connes, [*Trace formula in noncommutative geometry and the zeros of the Riemann zeta
   function*](https://arxiv.org/abs/math/9811068), and Connes--Consani--Marcolli,
   [*The Weil proof and the geometry of the adeles class
   space*](https://arxiv.org/abs/math/0703392): spectral/trace and cyclic-homology geometry of
   the adeles class space.
9. Boalch, [*Quasi-Hamiltonian geometry of meromorphic
   connections*](https://arxiv.org/abs/math/0203161): finite-dimensional monodromy/Stokes
   moduli and arbitrary-genus fusion. D'Agnolo--Kashiwara,
   [*On the irregular Riemann--Hilbert correspondence*](https://arxiv.org/abs/2408.04260):
   enhanced realization theory for irregular holonomic systems.
10. F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. Reine Angew. Math. 78 (1874),
    46--62: prime-harmonic asymptotics used for the susceptibility and critical-window measure.
11. S. Jana, [*Applications of analytic newvectors for GL(n)*](https://doi.org/10.1007/s00208-021-02207-5),
    Math. Ann. 380 (2021), 915--952, especially Lemma 5.2: modern weighted-prime test-function
    limit of the same analytic type. This confirms that the Mertens limit engine is classical.

## What is not new

- Highest-difference ultrametricity and its rooted dendrogram.
- Published nonabelian-Hodge diagram and quasi-Hamiltonian dimension formula.
- Rank-one perturbation inertia, Sherman--Morrison, determinant lemma, Schur complement.
- Exit-path/cellular calculation of a one-dimensional constructible sheaf germ.
- Scalar rigidity-index/Euler-characteristic identities.
- Douçot's weighted triangle and all its edge multiplicities.
- Rank-one Betti characters, common scalar tensor twists, determinant scaling, the classical
  theta transform of completed zeta, and adeles-class-space cyclic sources considered separately.
- Mertens's first theorem, partial summation, weak limits of logarithmically weighted prime
  measures, and the hyperbolic identity `g+g^-1-2=4sinh^2((log g)/2)`.

## Candidate novelty residue

The manuscript's candidate new statement is the simultaneous polarization theorem:

`published Cartan form = positive coefficient coarea - one physical-rank square`,

including exact cyclic-orbit descent. Consequences not found in the parent sources are:

- joint bound `negative inertia + nullity <= 1`, excluding coexistence of Lorentz and affine
  channels;
- arbitrary-genus physical-rank fibre-product version and nonnegative multi-Rees stability;
- spectral obstruction `lambda_2(B) <= 2` for every realized honest graph;
- equality of directed analytic-wall microstalk polarization with the published mixed-Hom
  polarization;
- exact Euler--capacity and corona recursions of the same unique rank channel.
- classification of the full relative-channel scalar kernel by interaction components, followed
  by the exact identification of its connected determinant weight with the coarea port `M`;
- a pre-divisor arithmetic realization in which the determinant holonomy defect at clock `n^M`
  is the literal rational-adelic Xi transgression `(delta_n(rho)^M - 1)c_rho`.
- the reflection-product theorem identifying the negative product of the two normalized
  rank-powered Xi transgressions with a positive prime energy, plus the rank-renormalized
  subcritical/critical/supercritical Mertens law. The limit profile itself is not claimed as new;
  the residue is its forced Stokes determinant exponent and its Xi-transgression factorization.

## Rediscovery attacks

- **Ultrametric-matrix attack.** Classical inverse-M-matrix results concern positivity/inverses of
  ultrametric matrices. They make the positive coarea kernel unsurprising, but the searched papers
  do not state the Stokes normalization, published Cartan identification, common-rank fusion law,
  or joint inertia/nullity consequence.
- **Dimension-formula attack.** `dim M = 2-(d,d)` evaluates the quadratic form at a dimension
  vector. It does not determine the full polarization or inertia on all real charges.
- **Fission-tree attack.** Trees generate contact coefficients, but the literature located does
  not isolate the one physical-rank subtraction after orbit descent and global fusion.
- **Microlocal-index attack.** Irregular Riemann--Hilbert theory realizes the objects; the exact
  normalized directed microstalk sum and its identification with the Cartan polarization were not
  found as a theorem in the searched sources.
- **Central-twist attack.** Common scalar cancellation and determinant exponents are elementary.
  They are not standalone novelty. The searched Stokes sources construct monodromy/Stokes moduli
  and fusion, but no result found identifies the scalar-kernel determinant weight with the unique
  nonpositive coarea functional of the published nonabelian-Hodge diagram.
- **Adelic-realization attack.** Connes and Connes--Consani--Marcolli provide adelic spectral,
  trace, and cyclic-homology realizations of zeta zeros. Their RH-bearing steps are trace-pairing
  positivity or analogous global conditions. No source found contains the paper's connected
  Stokes-port factorization or rank-powered paracyclic identity. Conversely, this paper does not
  claim a new adelic spectral realization or a proof of the required global annihilation.
- **Tautological-clock attack.** Setting `q=n^M` is forced twice: determinant restriction gives
  `delta_n^M`, while multiplicativity gives `delta_(n^M)=delta_n^M`. The representation theorem
  alone would not be new number theory. The strengthened statement pairs the two reflected
  unsquared residues and proves their exact finite vanishing locus and full logarithmic scaling
  trichotomy. It remains a selection classifier, not an RH proof.
- **Classical-Mertens attack.** Weighted-prime convergence and the profile integral follow from
  classical Mertens theory; they are not a priority claim. No located source identifies the
  scaling coordinate with the determinant restriction of the unique Hom-invisible scalar of a
  coefficient-generated Stokes skeleton, or realizes the two factors as normalized
  rational-adelic Xi transgressions.
- **Positive-square attack.** Squaring can detect off-line displacement without annihilating it.
  Here positivity is not presented as zero exclusion. New exact content is the factorization
  before squaring: the energy is the negative product of two reflected unsquared source residues.
  Global vanishing on Xi support remains precisely the open arithmetic step.

## Search limits and verdict

Exact-title, formula, inertia, Lorentzian, second-eigenvalue, fission-tree, ultrametric, and
microlocal-multiplicity searches were run across arXiv, publisher pages, and the cited ancestry.
Search-engine recall was poor for several exact phrases, so absence is not proof of priority.

Verdict: `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`, not a priority claim. Mathematical novelty is
plausible and sharply isolated; independent expert circulation remains mandatory before asserting
historical novelty.
