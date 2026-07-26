# Deninger arithmetic cohomology for the arithmetic curve

- **ID:** `deninger-arithmetic-cohomology-construction`
- **Stage:** 1-in-progress
- **Type:** CONJECTURAL CONSTRUCTION / RH PROGRAM
- **Primary target:** `docs/Deninger program.md`
- **Rule:** construct from the completed Euler--Gamma source before extracting the Xi divisor.

## Scope correction

The desired object is not one analytic estimate and not a Hilbert--Pólya operator in isolation.
For \(\overline{\operatorname{Spec}\mathbb Z}\), it must simultaneously provide:

1. \(K_{\mathbb R}\)-valued cohomology in degrees \(0,1,2\);
2. a closed Frobenius-flow generator \(\Theta\);
3. cup product, trace, and Poincaré duality;
4. a distributional Lefschetz formula with prime-power and archimedean local terms;
5. a regularized determinant equal to the completed zeta function;
6. an odd quaternionic Hodge star and a positive metric;
7. a source-derived comparison identifying the middle spectrum with the nontrivial Xi divisor.

CCM cyclic cohomology is only a possible realization/comparison for items 2, 4, and 7. It is not
the arithmetic cohomology theory itself and will not drive this card.

## Literature constraints

Deninger's properties 2.1--2.7 require:

- \(\Theta\) is a derivation of cup product;
- \(H^0=\mathbb C\) with \(\Theta=0\);
- \(H^1\) is infinite-dimensional and its generalized eigenvalues are nontrivial zeta zeros;
- \(H^2\cong\mathbb C(-1)\), so \(\Theta=1\) after trace;
- the \(H^1\times H^1\to H^2\) pairing is perfect;
- an anti-linear \(*\) on \(H^1\) satisfies \(*^2=-1\), commutes with \(\Theta\), and turns
  \(\operatorname{tr}(x\cup *y)\) into a positive scalar product.

The 2022 no-real-coefficients theorem rules out an ordinary functorial real-valued Weil theory.
Odd degree must instead carry quaternionic parity in \(K_{\mathbb R}\); degrees \(0,2\) are even.

## Source-first candidate

Let \(C_{\mathrm{EG}}\) denote the completed Euler--Gamma seam complex. It must be constructed from
the prime Dirichlet source, Gamma factor, functional-equation reflection, and their boundary
colligation before any zero or divisor expansion.

`[DAC_SOURCE_PACKET_QUOTIENT]`

Absolute Euler convergence is not invariant under complex conjugation, so one packet space cannot
carry a diagonal Hermitian kernel at this stage. Let
\(\mathcal T_{\mathrm{EG}}^-\) be the free finite-packet space on lower Cauchy parameters in the
honest Euler half-plane and let \(\mathcal T_{\mathrm{EG}}^+\) be its conjugate upper sector.
Define their bilinear source polarization only from the prime--Gamma source by
\[
 B_{\mathrm{EG}}(z,w)=
 \begin{cases}
 \dfrac{R_{\mathrm{EG}}(\bar w)-R_{\mathrm{EG}}(z)}
      {z-\bar w},&z\ne\bar w,\\[6pt]
 -R'_{\mathrm{EG}}(z),&z=\bar w,
 \end{cases}
\]
where \(R_{\mathrm{EG}}\) is the von-Mangoldt Dirichlet series plus the completed Gamma/boundary
term. The diagonal value is the removable divided-difference limit. The existing explicit formula
proves off the reflected diagonal that this form agrees with the multiplicity-exact divisor Weil
form, but that theorem is a comparison, not the definition. The diagonal comparison requires a
separate termwise-derivative/local-holomorphy proof.

Conjecture: the exact left/right radical quotients of this two-sector pairing, completed in the
source-conormal graph topology, admit a closed differential and a closed generator. Their
reflection gluing is the middle term of `[DAC_SOURCE_COMPLEX]`. Functional-equation reflection
defines cup duality; Hodge star and positivity are not built into this algebraic quotient. The
Gamma contact line fixes normalization. This is falsified if the radical or graph closure can be
defined only after enumerating Xi zeros.

`[DAC_REFLECTED_DIAGONAL]`

On the honest Euler half-plane the source trace is holomorphic and its derivative can be taken
termwise after the canonical genus-one subtraction. Consequently the reflected-diagonal value
\(-R'_{\mathrm{EG}}(z)\) equals the divisor-side squared-Cauchy polarization. This is the missing
local analytic lemma needed to extend the existing off-diagonal source/target comparison to all
finite packets. It is a construction/comparison statement, not positivity.

`[DAC_SOURCE_COMPLEX]`

There is a closed \(\mathbb Z/2\)-graded rigged complex
\[
  (C_{\mathrm{EG}},d,\Gamma,J,\Theta)
\]
with:

1. \(d^2=0\), \(d\Gamma=-\Gamma d\), \(Jd=dJ\), and \([\Theta,d]=0\);
2. even Tate endpoint cohomology
   \(H^0\cong\mathbb C(0)\) and \(H^2\cong\mathbb C(-1)\);
3. odd residual cohomology \(H^1\) carrying the induced \(K_{\mathbb R}\) structure;
4. finite-window residue comparison equal to
   `completedSEMContourIndexZ_eq_xiOrder`, with multiplicity and compatible exhaustion;
5. a source-defined cup product and trace whose degree-one pairing is perfect;
6. a renormalized graded trace whose distribution is the complete prime--Gamma explicit formula;
7. a zeta-regularized determinant
   \[
     \widehat\zeta(s)=
     \prod_{i=0}^2
       \det_\infty\!\left((s-\Theta)/(2\pi)\mid H^i\right)^{(-1)^{i+1}} .
   \]

This conjecture constructs the arithmetic cohomology and its spectral/trace realization, but does
not assert positivity or RH.

`[DAC_HODGE_GREEN]`

The source colligation supplies a closable Hodge operator and Green operator
\[
  d^*=*^{-1}d*,\qquad
  \Delta=dd^*+d^*d,\qquad
  1-P_{\mathrm{harm}}=dH+Hd,
\]
compatible with the two-filtered completion. On \(H^1\), the anti-linear star satisfies
\(*^2=-1\), commutes with \(\Theta\), and
\[
  \langle x,y\rangle=\operatorname{tr}(y\cup *x)
\]
is positive definite.

The derivation law then forces
\[
  \langle\Theta x,y\rangle+\langle x,\Theta y\rangle=\langle x,y\rangle,
\]
so \(\Theta-\tfrac12\) is skew-symmetric. Together with `[DAC_SOURCE_COMPLEX]`, this implies RH.
This conjecture is the genuine purity/Hodge-index core and must not be assumed inside the
construction of \(H^1\).

`[DAC_REALIZATION_COMPARISON]`

After both sides exist, the source complex is compared with the single CCM cyclic closed cokernel
and with the Hardy--Green residual model. The comparison must preserve \(K_{\mathbb R}\) parity,
\(\Theta\), cup-trace, local Lefschetz terms, and the Hodge metric. A comparison may not define the
metric by transporting a form already known to be positive exactly under RH.

## Existing unconditional bricks

- `DeningerWeightOnePolarization`: exact cup derivation, Hodge-star transport,
  \(\Theta-\frac12\) skew-symmetry, critical-line eigenvalue theorem, and exclusion of
  length-two Jordan chains.
- `DeningerClosedOperatorPolarization`: same implications on a dense domain for a closed
  unbounded generator.
- `DeningerDivisorFlow`: explicit \(H^0,H^1,H^2\) spectral target, nondegenerate cup-trace,
  one-parameter flow, exact zero spectrum, and Hadamard determinant identity. This is
  divisor-indexed and therefore a target model, not the source construction.
- `DeningerDivisorClosedGenerator`: maximal diagonal \(\ell^2\) domain, with closedness,
  density, and coordinate eigenvectors proved.
- `DeningerLefschetzTrace`: exact resolvent Lefschetz equality between the divisor spectral trace
  and the independently defined continued prime--Gamma source trace, including the honest
  von-Mangoldt half-plane and determinant/log-derivative compatibility.
- `DeningerPrimeGammaPacketCohomology`: source-only lower/upper Euler packet sectors, the completed
  prime--Gamma divided-difference kernel (including its derivative diagonal), bilinear finite
  packet polarization, exact left/right radical quotients, and atomic off-diagonal comparison
  with the divisor Weil polarization.
- `KRealGradedAdjoint`, `KRealKernelCokernel`, `KRealClosedCokernel`, and
  `KRealMoritaParityShift`: even/odd \(K_{\mathbb R}\) algebra and quotient descent.
- `SeamSuspensionTrace`: completed prime--Gamma logarithmic derivative and finite graded Hodge
  compression identities.
- `CompletedSEMContourBoundary`: source-defined integral contour index equals Xi order.
- `IntegralOrbitTateExtension` and `ReflectionFermionBoundary`: exact fixed/free integral
  reflection algebra and RH consumer.
- `BRSTHodgeConstraint`: abstract positive Hodge Hamiltonian, Green commutation, and chain
  homotopy identities once a source \(d\), adjoint, and Green operator exist.
- `SeamKreinStructure`: reciprocity must first live in a signed Green/Krein space; a full
  Lagrangian graph has zero quotient, so nonzero \(H^1\) must be a domain/closure/boundary defect.
- `SeamCrossingTower`: prime crossing energies and Euler factors, plus proof that the final
  self-adjoint spectral endpoint is exactly RH.
- `CCMRationalPeriodicWeightedPoisson`: supporting finite-periodic signed Poisson theorem only.

## Hostile checks

- Defining \(H^1\) as the free space on Xi zeros is circular.
- Declaring a Hilbert metric, self-adjoint generator, modular Hamiltonian, or Hodge positivity
  without a source construction imports RH.
- Ordinary real coefficients contradict Deninger's Artin-multiplicity obstruction.
- Functional-equation equivariance gives reflection pairs but does not kill free pairs.
- Measured or density positivity can miss density-zero off-line zeros; the form must be faithful.
- A full doubled reciprocity graph is Lagrangian and has zero quotient; boundary defects are
  essential.
- Finite graded trace identities do not establish infinite renormalized cyclicity.
- Determinant equality without prime-orbit Lefschetz comparison is only a spectral repackaging.
- Prime-side positive energies alone cannot manufacture the archimedean polarization.
- Absolute Euler convergence supplies a two-sector pairing, not a Hermitian form on one
  half-plane. Conflating these would silently use meromorphic continuation across the critical
  strip.
- The source radical quotient alone does not make Hodge star descend: the needed Hermitian
  compatibility/positivity is precisely part of the unresolved purity gate.

## Stepwise attack

1. Formalize Deninger 2.1--2.7 and the exact skew-shift/eigenvalue consequence.
2. Define a source-first finite-window seam cochain complex and its \(K_{\mathbb R}\) parity.
3. Prove its cohomology carries the integral source contour multiplicity.
4. Construct cup product, endpoint trace, and Poincaré pairing at finite window.
5. Prove the graded Lefschetz identity and finite determinant identity.
6. Build compatible transition maps; prove closability and reduced-cohomology exactness.
7. Establish the distributional prime--Gamma trace and regularized determinant on the limit.
8. Construct the source adjoint/Green operator and prove faithful Hodge positivity.
9. Derive skew-adjointness after the half shift, spectrum on the critical line, and RH.
10. Only then prove comparison with CCM/Hardy--Green models.

## Gates

- [x] Exact Deninger requirements and coefficient obstruction extracted
- [x] Prior failed Hodge/modular/completed-cohomology routes audited
- [x] Source-first conjectures separated from the RH-equivalent positivity conjecture
- [x] Abstract Deninger 2.1--2.7 cup/star/closed-generator implication foundation complete
- [x] Multiplicity-exact divisor target \(H^0,H^1,H^2\), flow, cup, determinant, and closed
      diagonal generator formalized
- [x] Resolvent Lefschetz comparison with the independent prime--Gamma source formalized
- [x] Source prime--Gamma packet sectors and exact algebraic radical quotients formalized
- [ ] Reflected-diagonal source/target derivative comparison proved
- [ ] Finite source cochain complex constructed
- [ ] Finite cup/trace/Lefschetz/determinant package proved
- [ ] Closed cofinal arithmetic cohomology constructed
- [ ] Source Hodge--Green positivity proved
- [ ] RH derived

## Log

- 2026-07-25 — Opened as primary card after correcting an over-focus on CCM support. Extracted
  Deninger's actual six-layer program, the \(K_{\mathbb R}\) constraint, and the source-first
  construction/positivity separation. No RH premise or numerical computation used.
- 2026-07-25 — Formalized the abstract bounded and closed-operator polarization implications,
  a divisor-indexed \(H^0,H^1,H^2\) target with flow/cup/determinant, the maximal closed diagonal
  generator, and the exact prime--Gamma resolvent Lefschetz comparison. Isolated the next
  source-only object as `[DAC_SOURCE_PACKET_QUOTIENT]`; no divisor model is accepted as the
  arithmetic source theory.
- 2026-07-25 — Constructed `[DAC_SOURCE_PACKET_QUOTIENT]` algebraically from the von-Mangoldt plus
  Gamma source: two absolute-convergence sectors, removable derivative diagonal, finite bilinear
  pairing, and exact left/right radical quotients. Lean proves the off-diagonal atomic comparison.
  Audit exposed `[DAC_REFLECTED_DIAGONAL]` and showed why Hodge-star descent cannot be declared at
  this stage without resolving the Hermitian/positivity gate.
