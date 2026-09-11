# Route L: original Green germ at zero damping

- **ID:** L-C52
- **Date:** 2026-09-12
- **Stage:** 1-in-progress; paper conjecture and corpus audit
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

Conjecture: at every actual Xi zero rho of native multiplicity m, the
function `a ↦ H(a,rho)` has exact pole order `2*m` at zero. If c and cR are
the actual first nonzero zeta Taylor coefficients at rho and 1-rho, the
leading Laurent coefficient is

`G(rho)/((1-p^(-rho))*c*cR)`.

Paper mechanism to verify: zeta is analytic at both original points; its
order equals the native Xi order and reflection preserves that order.
The two local factorizations therefore pull back to `a^m*u(a)` and
`a^m*v(a)`, with nonzero analytic units at zero. Their product has order
`2*m`, and the original prime denominator and Gaussian factor are nonzero.
The exact unit product fixes the normalization. No simple-zero premise,
critical-line placement, deleted pole, or fitted residue is allowed.

This must yield the positive singular germ, including its exact nonzero
coefficient, rather than only a negative statement about regular limits.
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

The first scratch check passed under default limits: one generic analytic
unit lemma translates a native finite-order zero to the damping origin and
identifies its value with the canonical trailing coefficient. Both Xi/zeta
order equality and analyticity were checked on the current toolchain.
The full pole, coefficient, normalized-limit and literal-integral bridge
proofs are now being checked. No heartbeat or recursion limits changed.
