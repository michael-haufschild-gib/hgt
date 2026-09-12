# Route L: original Green germ at zero damping

- **ID:** L-C52
- **Date:** 2026-09-12
- **Stage:** 3-formalized; final named leaf audit passed under default limits
- **Depends on:** C44 literal source Euler formula; C49 original Green transform; C51 full Xi norm admission
- **RH status:** unproved

Chain: complete original Green/BV source → fixed physical-reader agreement
→ conormal vanishing → RH. C51 proves fixed-damping admission, not the
source-forced singular comparison. Integration-by-parts templates retain
the actual boundary; endpoint-free templates require unavailable vanishing
premises. The next test is the singularity already forced by the actual
source's exact Euler formula.

For the original prime p and spectral coordinate s, consider the complex
damping continuation

`H(a,s)=G(s)/(zeta(a+s)*zeta(a+1-s)*(1-p^(-s)))`,

where G is the original reflected Gaussian Mellin transform. On the proved
real damping admission region this is the literal original Green integral.
No source at zero damping is defined by this notation.

Proved in Lean: at every actual Xi zero rho of native multiplicity m, the
function `a ↦ H(a,rho)` has exact pole order `2*m` at zero. If c and cR are
the actual first nonzero zeta Taylor coefficients at rho and 1-rho, the
leading Laurent coefficient is

`G(rho)/((1-p^(-rho))*c*cR)`.

Proof: zeta is analytic at both original points; its
order equals the native Xi order and reflection preserves that order.
The two local factorizations therefore pull back to `a^m*u(a)` and
`a^m*v(a)`, with nonzero analytic units at zero. Their product has order
`2*m`, and the original prime denominator and Gaussian factor are nonzero.
The exact unit product fixes the normalization. No simple-zero premise,
critical-line placement, deleted pole, or fitted residue is allowed.

This yields the positive singular germ, including its exact nonzero
coefficient and the sharp power-normalization classification.
Its relation to a complete source-domain continuation and the fixed
physical reader remains to be derived; a scalar meromorphic continuation
alone does not supply that relation.

## Corpus and cross-field audit

- [Boundary trace search](route-l-complete-boundary-trace-search.json): all
  20 candidates and 20 method summaries inspected. Generation 878650,
  57,023 inventoried files; retrieval partial. Finite endpoint pairings,
  trace-generator definitions, and arbitrary boundary trace-zero identities
  do not establish incidence with the fixed original source and reader.
- [Damping collision search](route-l-damping-collision-search.json): all
  20 candidate statements and 20 method entries inspected; generation
  878657, 57,024 files, retrieval partial. The proposed damping/zeta-ratio
  group concerns different Poincaré/Fokas–Lenells/Gamma sources. Method 18
  lacks method metadata; its inspected excerpt requires correction factors.
  No transfer supplies a zero-damping source-domain passage.
- [Germ calculus search](route-l-damping-germ-calculus-search.json): all
  20 candidates and 20 method summaries inspected; generation 878691,
  57,025 files (47,416 Lean, 9,609 prose). Query expansion and text/source
  retrieval interrupted; compiler coverage mostly pending. Actual useful
  ingredients: analytic finite-order factorization, inverse/product rules
  for the canonical meromorphic trailing coefficient, and normalized-germ
  convergence. Candidate applications remain source-only until checked.
  The proposed Xi/Gamma ingredient group does not identify the same germ;
  its generated `pole order zero` obligation contradicts the cited pole
  mechanism. Definitions described as computations are not proof producers.

Broad arXiv search `reciprocity`, sorted newest first, found Camacho et al.,
[*Temporal Localisation of Waves from Imaginary Line-Gap Topology*](https://arxiv.org/html/2609.11577v1),
submitted 10 September 2026. The inspected End Matter E9–E12 derives an
intensity law from two eigenmodes, paired imaginary parts, and a constant
cross term. Localization additionally needs a gapped Hamiltonian, a phase
switch, and the specified initial overlap. It may last only a finite time.
No such Hamiltonian, gap, or overlap is supplied by Route L. The useful
lesson is to retain the exact nonzero mode coefficients through a singular
transition; the paper supplies no reader agreement or critical confinement.

## Lean attempt

The complete scratch check passed under default limits. One generic analytic
unit lemma translates a native finite-order zero to the damping origin and
identifies its value with the canonical trailing coefficient. The same unit
supplies the order, coefficient, limit and analytic extension proofs. A shared
Leibniz collapse identifies the original Taylor jets without expanding every
derivative. Explicitly typed function equalities and a direct integer-coercion
equality replace unsuccessful rewrite matching. No heartbeat or recursion
limits changed. The global meromorphic formula also passed a separate small
scratch check; the zero-local theorem now reuses that global result.

The stronger positive survivor is proved: multiplication by `a^k`
admits a finite limit exactly for `k>=2*m`, and a nonzero finite limit exactly
for `k=2*m`. Filling that normalized scalar function with its forced leading
coefficient gives an analytic germ at zero. The coefficient is also identified
with the actual `m`th zeta derivatives divided by `m!` at both reflected points.
This prevents a choice of normalization from silently imposing simplicity.

## Next analytic obstacle

Coordinatewise Laurent continuation has not constructed a vector in the
original full Xi norm. Its exact coefficient contains reciprocals of both
native leading zeta jets. C51's Gaussian envelope bounds the original Green
denominator, not these additional inverses. A source-domain continuation
requires new uniform control and an identification with the complete original
BV boundary; neither follows from scalar analyticity.

[Reciprocal-coefficient deep search](route-l-singular-coefficient-norm-search.json)
returned 20 candidates and 20 method entries, all inspected. Generation 878845
reported pending coverage and a decomposition deadline. Gaussian zero-count
summability does not include inverse native jets. Gamma–Gaussian multiplication
preserves nonvanishing but gives no lower jet bound. The all-complex-time heat
bound requires precisely an unproved summability hypothesis. The separated-point
method requires additional separation data. No applicability claim was made.

The broadened [inverse-jet hybrid search](route-l-inverse-jet-bound-hybrid-search.json)
returned 20 candidates and 20 method entries, all inspected. Generation 878878
inventoried 57,030 files (47,420 Lean); text/source retrieval remained partial,
compiler coverage mostly pending. Useful reciprocal-zeta bounds hold in a
zero-free region near real part one; derivative upper bounds do not lower-bound
the first nonzero jet at an actual zero. Finite damped-product estimates already
assume an inverse-zeta bound. Thus none of the inspected results supplies the
required full-Xi coefficient envelope. This is a retrieval audit, not a claim
that the whole corpus contains no such theorem.

## Final verification

`GaloisForLFunctions.RHTower.DeningerOriginalGreenZeroDampingGerm` contains
17 public declarations. The full source expression is meromorphic on the
complex damping plane and agrees with the actual original Green integral
throughout the proved real admission range `a>1`. The exact pole order,
nonzero native-jet coefficient, sharp normalization classification and
filled analytic scalar germ are unconditional at every actual Xi support
point and every original prime.

The final audit
`lake build GaloisForLFunctions.RHTower.DeningerOriginalGreenZeroDampingGerm`
passed, compiling only the new leaf (131 seconds); its required dependency
jobs were cached. No full or umbrella build ran. The module is wired once
into `RHTower.lean`. Both scratch checks passed via `lake env lean`.

Logs: [full scratch](route-l-zero-damping-scratch.log),
[global meromorphic scratch](route-l-zero-damping-meromorphic-scratch.log),
[final leaf audit](route-l-zero-damping-build.log).

Full-Xi admission of these normalized coefficients, a complete zero-damping
source-domain passage, and fixed physical-reader agreement remain unproved.
This card is a closed singularity and normalization theorem, not a proof of RH.
