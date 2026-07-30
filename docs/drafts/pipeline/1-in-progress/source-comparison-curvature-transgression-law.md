# Source-comparison curvature and divisor transgression

- **ID:** `source-comparison-curvature-transgression-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL REINTERPRETATION / RIEMANN-SOURCE OBJECT / NOVELTY SEARCH
- **Status:** `[PARENT LAW FROZEN] [XI SHADOW MAPS PARTLY FORMALIZED] [NOT RH]`
- **Scientific gate:** no paper promotion unless the Xi instance is more than a repackaged Gram
  identity and yields at least one new theorem not obtainable from a scalar log-derivative
  equality.
- **Parents:**
  - `adjoint-duality-cauchy-nerve-purity-law.md`
  - `source-record-relative-hyperrigidity-purity-law.md`
  - `divisor-augmentation-nonproperness-law.md`
  - `../4-publication-ready/arithmetic-julia-normal-cone/main.tex`
  - `../4-publication-ready/riemann-orientation-boundary-fracture/main.tex`

## Frozen hunch

Known positivity laws, Julia defects, Hodge commutators, prime seams, Ward columns, exterior
currents, response signatures, differential common-mode no-gos, and compact-open charge escape
are shadows of one bivariant source-comparison curvature.

Let a source record be a matrix or kernel \(G\), and let a comparison act from its two
polarizations by \(L\) and \(R\). Define
\[
  \Omega_{L,R}(G)=LGR-G. \tag{1}
\]
If comparisons compose as
\[
  (L_2,R_2)\circ(L_1,R_1)=(L_2L_1,R_1R_2),
\]
then
\[
 \boxed{
 \Omega_{L_2L_1,R_1R_2}(G)
 =
 L_2\Omega_{L_1,R_1}(G)R_2+\Omega_{L_2,R_2}(G).
 } \tag{2}
\]
Thus a defect is not a terminal error. It is a crossed cocycle: the present comparison transports
the preceding defect and adds its own innovation. This is the exact algebraic content required by
“the record generates the next comparison.”

For differentiable paths \(L_\alpha,R_\alpha\) with \(L_0=R_0=1\),
\[
 \dot\Omega_0(G)=A_LG+GA_R,\qquad
 A_L=\dot L_0,\quad A_R=\dot R_0. \tag{3}
\]
With an inverse right action this becomes the Sylvester/Hodge commutator
\[
 \dot\Omega_0(G)=A_LG-GA_R. \tag{4}
\]

The proposed Riemann-source object is not a scalar function and not another RH-equivalent
positivity condition. It is the full augmented comparison curvature before compression:

1. the node--node block is the non-diagonal Julia cross-defect;
2. the distinguished boundary column differentiates to the anti-causal Xi Ward response;
3. the full trace is obtained from the positive Euler/Möbius Fisher tangent after Gamma sewing;
4. antisymmetric \(2\times2\) exterior components are the oriented Euler phase Wronskians;
5. the reflected prime loop has holonomy \(p^{1-\rho-\bar\rho}\);
6. the infinitesimal generator of that loop is the Deninger/Hodge purity curvature;
7. the Kadison defect and FE--Schwarz seam are finite transgressions of the same holonomy.

## Exact shadow table

| Shadow | Map from \(\Omega\) | Existing exact endpoint |
|---|---|---|
| Julia cross-defect | matrix entry | `xiRightWardJuliaCrossDefect_eq_transport_sub_gram` |
| Ward response | derivative of boundary column | `hasDerivAt_mobiusGammaXiAntiCausalWardPacketTransportV_zero` |
| full Xi trace | Gamma-sewn Fisher transport | `eulerPositiveGammaXiWardHilbertTransportAt_eq_continuedSource` |
| oriented Euler current | exterior coefficient | `xiGammaEulerHeightBoundaryWronskianAtZero_eq_I_mul_exterior` |
| Hodge obstruction | infinitesimal reflected loop | `deningerCompactOpenLocalJetHodge_theta_defect_eq_purityCurvature` |
| FE--Schwarz seam | exponential transgression | `orbitwiseScaleSeamCharge_eq_purityCurvatureTransgression` |
| two-channel drift anomaly | commutator block | `bipolarGramDriftAnomaly_eq` |
| response signature | odd exterior minor | `symmetricThreePointDet_poissonScaleRefinementKernel_neg` |
| differential common-mode loss | augmentation-kernel projection | `ker_commonModeDifferentialOperatorHom_eq_ker_augmentation` |
| charge escape | nonproper boundary index | `CompactOpenKolchinWardChargeEscape` endpoints |

The last two rows are not literal matrix entries. They are quotient shadows: differential
augmentation kills the diagonal/common mode, while compact-open restriction forgets the boundary
class at infinity.

## Required new theorem

`[TARGET: XI_SOURCE_COMPARISON_CURVATURE_CAPSTONE]`

Construct one typed augmented comparison object \(\mathcal C_{\Xi}\), using the already-defined
Euler/Möbius Fisher state, Gamma seam, strict-right Wiener--Hopf factor, Julia phase transport,
and Schwarz boundary channel, and prove without divisor-selected coefficients:

1. its finite comparison defect obeys `(2)`;
2. its tangent obeys `(3)` or `(4)`;
3. its full-trace compression is the continued prime--Gamma Xi trace;
4. its boundary-column compression is the continued anti-causal Ward column;
5. its exterior compression is the calibrated Euler Wronskian;
6. its reflected prime holonomy is \(p^{1-\rho-\bar\rho}\);
7. every listed scalar obstruction factors through a named compression of this single object.

Clauses 3--6 must be proved as commuting diagrams between existing independently defined objects.
A structure populated by restating the endpoint theorems is not sufficient.

## Consequences if the capstone is genuine

1. **Exact information-loss classification.** Squaring, taking a determinant, taking a scalar
   trace, passing to a differential-matroid quotient, and restricting to compact windows become
   explicit functors out of one curvature object. Their lost components are computable rather
   than described heuristically.
2. **Source-first proof target.** RH would follow from source-derived triviality of the reflected
   comparison holonomy in a controlled dagger category. This is stronger than asking for a scalar
   inequality because the holonomy is constructed before any zero is read.
3. **No scalar repair.** Rational-gauge surgery and compact-open charge escape show that no
   compression factoring through finite differential data and compact windows can trivialize the
   holonomy.
4. **Generated-comparison route.** Equation `(2)` supplies the missing successor rule: the
   innovation from one source comparison is transported into the next. Global coherence can now
   be stated as a cocycle-trivialization problem for an explicit object, not as unspecified
   “positivity.”

## Fatal falsifiers

1. The typed Xi capstone is merely a direct-sum Gram with no cross-definition theorem.
2. The boundary column is inserted coordinatewise rather than forced by the augmented matrix.
3. The reflected holonomy \(p^{1-\rho-\bar\rho}\) is declared from \(\rho\) rather than computed
   from source comparison composition.
4. The composition law `(2)` is the only new statement; that law is elementary parent algebra.
5. The construction uses a selected zero before defining its source comparison.
6. An off-line generalized-prime system realizes the same typed capstone and controlled dagger
   trivialization.
7. “Global coherence” is defined to mean vanishing holonomy, making the RH implication circular.
8. No new corollary survives after replacing every object by its scalar logarithmic derivative.

Any of 1--5 or 7 kills the headline. Falsifier 6 forces classification of the missing
ordinary-prime/discreteness input. Falsifier 8 demotes the result to a synthesis note.

## Immediate audit

- The augmented Julia defect already forces its boundary column from the same matrix; this passes
  falsifier 2 locally.
- The positive Euler Fisher transport and strict-right Julia transport are currently two
  consecutive exact constructions, but no single commuting source diagram yet identifies their
  comparison curvature.
- The local Tate--Julia factorization computes the centered clock, but it is only paper-proved and
  classical. Its use is admissible only as the local holonomy face of the larger capstone.
- No claim of RH, zero exclusion, novelty, or journal readiness is authorized at this stage.

## Gates

- [x] frozen universal parent law and exact successor identity
- [x] mapped principal existing shadows
- [x] listed fatal tautology/circularity/off-line falsifiers
- [ ] formalize generic bivariant defect cocycle only if needed by Xi diagram
- [ ] construct one non-tautological Xi commuting comparison diagram
- [ ] derive one new cross-object theorem
- [ ] prove local Tate--Julia reflected holonomy in Lean
- [ ] audit generalized-prime and rational-gauge countermodels
- [ ] primary-literature novelty search
- [ ] antagonist review
- [ ] promote or kill

