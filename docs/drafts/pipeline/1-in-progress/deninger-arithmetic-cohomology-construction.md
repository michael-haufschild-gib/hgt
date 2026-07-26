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

The exact left/right radical quotients give arithmetic trace/cup **test spaces**, not middle
cohomology itself. This distinction is forced: finite Cauchy packets are not stable under
coordinate multiplication, and treating their parameter labels as eigenvalues would create a
continuum of spurious spectrum. Their correct role is to supply source-defined matrix
coefficients for the ordinary/compact-support pairing. Hodge star and positivity are not built
into the packet quotient.

`[DAC_REFLECTED_DIAGONAL]`

On the honest Euler half-plane the source trace is holomorphic and its derivative can be taken
termwise after the canonical genus-one subtraction. Consequently the reflected-diagonal value
\(-R'_{\mathrm{EG}}(z)\) equals the divisor-side squared-Cauchy polarization. This is the missing
local analytic lemma needed to extend the existing off-diagonal source/target comparison to all
finite packets. It is a construction/comparison statement, not positivity.

`[DAC_ENTIRE_QUOTIENT]`

The intrinsic algebraic middle cohomology is
\[
  H^1_{\mathrm{ent}}=\mathcal O(\mathbb C)/\Xi_C\mathcal O(\mathbb C),
  \qquad
  \Theta[F]=[(\tfrac12+iz)F].
\]
This is source-defined by the completed Euler--Gamma function and is automatically stable under
\(\Theta\). It has no divisor index in its definition. Removable divided chains give its
multiplicity-exact local Jordan chains. An explicit entire divided-difference Bézout inverse
shows that coordinate multiplication has no eigenvector away from the Xi divisor. Conversely,
the first nonzero class of every divided chain is a genuine eigenvector. Therefore
\[
 \Xi_C(\alpha)=0
 \iff
 \exists\,0\ne x\in H^1_{\mathrm{ent}},\quad
 \Theta x=(\tfrac12+i\alpha)x .
\]
This exact point-spectrum theorem is proved in Lean without a zero-defined carrier.

The quotient is naturally nonreduced at a multiple zero. Hence a positive Hodge realization
which makes the centered generator skew forces not only RH but semisimplicity of these local
blocks. This is an honest strengthening, not an assumption.

`[DAC_SOURCE_COMPLEX]`

The algebraic source complex is
\[
 C^0=\mathbb C\oplus\mathcal O(\mathbb C)
 \xrightarrow{\,d^0(c,F)=\Xi_CF\,}
 C^1=\mathcal O(\mathbb C)
 \xrightarrow{\,d^1=0\,}
 C^2=\mathbb C .
\]
The analytic identity theorem proves multiplication by \(\Xi_C\) injective, so its cohomology is
\[
 H^0\simeq\mathbb C,\qquad
 H^1=H^1_{\mathrm{ent}},\qquad
 H^2\simeq\mathbb C .
\]
Multiplication by \(\tfrac12+iz\) is a cochain map and induces endpoint weights \(0,1\).

The remaining topological enhancement is a closed \(\mathbb Z/2\)-graded rigged realization
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
5. a source-defined ordinary/compact-support cup product and trace whose degree-one pairing is
   perfect;
6. a renormalized graded trace whose distribution is the complete prime--Gamma explicit formula;
7. a zeta-regularized determinant
   \[
     \widehat\zeta(s)=
     \prod_{i=0}^2
       \det_\infty\!\left((s-\Theta)/(2\pi)\mid H^i\right)^{(-1)^{i+1}} .
   \]

Algebraic Poincaré duality is already canonical:
\[
 H^1_c=(H^1_{\mathrm{ent}})^\vee,\qquad B(x,\ell)=\ell(x),\qquad
 \Theta_c\ell=\ell-\ell\circ\Theta.
\]
The pairing separates both variables, and
\[
 B(\Theta x,\ell)+B(x,\Theta_c\ell)=B(x,\ell)
\]
holds identically. The unresolved part is identifying the arithmetic packet/continuous dual
inside this algebraic dual and constructing the closed topology, trace, and determinant.

`[DAC_HODGE_GREEN]`

The source colligation must supply a conjugate-linear bijection
\[
  *:H^1_{\mathrm{ent}}\longrightarrow H^1_c
\]
which intertwines \(\Theta\) and \(\Theta_c\) and satisfies
\(\operatorname{Re}((*x)(x))>0\) for every \(x\ne0\). This exact datum and its implication to RH
are formalized. At the closed-complex level it must arise from a closable Hodge operator and
Green operator
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
  packet polarization, exact left/right radical quotients, and atomic comparison with the divisor
  Weil polarization.
- `DeningerPrimeGammaReflectedDiagonal`: local uniform derivative domination, termwise
  differentiation, the reflected-diagonal squared-Cauchy identity, and full finite-packet
  source/Weil comparison.
- `DeningerPrimeGammaPoincareDuality`: universal left/right radical descent and nondegenerate
  alternating source cup form on the arithmetic packet test space.
- `DeningerEntireQuotientCohomology`: source-defined entire quotient, multiplicity-exact Jordan
  chains, explicit off-divisor Bézout resolvent, and exact Xi-zero/Frobenius-point-spectrum
  equivalence.
- `DeningerArithmeticCochainComplex`: explicit three-term source complex, analytic injectivity of
  the Xi differential, computed \(H^0,H^1,H^2\), and cochain Frobenius action.
- `DeningerArithmeticPoincareDuality`: canonical perfect ordinary/compact-support pairing, forced
  weight-one dual Frobenius, exact Hodge-star obligation, and its unconditional implication to RH.
- `DeningerArithmeticResidueDuality` and `DeningerArithmeticJetDuality`: source evaluations and
  multiplicity-bounded jets descend to compact-support cohomology, with complementary Frobenius
  weight for the residue class.
- `DeningerArithmeticFlow`: source quotient flow and endpoint flows, including the one-parameter
  group laws.
- `DeningerArithmeticCharacteristic`: exact cyclic characteristic ideal, centered and uncentered
  characteristic sections \(\Xi_C\) and \(\xi\), endpoint quotient formula, and source-only
  prime--Gamma logarithmic-derivative Lefschetz identity.
- `DeningerArithmeticRealStructure`: functional-equation Schwarz reflection descends to an even
  \(K_{\mathbb R}\) structure on source \(H^1\), fixes \(\Xi_C\), and commutes with \(\Theta\).
  Its square is \(+1\), so it does not pretend to be the missing odd positive Hodge star.
- `DeningerArithmeticCompactOpen`: compact-open entire source is closed, completely metrizable,
  and Baire; point evaluations and Xi multiplication are continuous; unreduced and reduced
  quotient topologies are constructed without assuming closed Xi range.
- `DeningerArithmeticProductDual`: every continuous linear functional on a product of complex
  jet coordinates depends on finitely many coordinates, proving the abstract compact-support
  mechanism needed after source jet interpolation.
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
- The finite Cauchy-packet quotient is a trace test space, not \(H^1\): it is not intrinsically
  stable under coordinate multiplication and its parameter labels are not zeta spectrum.
- The full algebraic dual is larger than desired continuous compact-support cohomology. A source
  topology and comparison with prime--Gamma packet functionals must be proved, not declared.
- A positive Hodge identification on the nonreduced entire quotient also excludes nontrivial
  Jordan chains, hence would imply simplicity as well as RH.

## Stepwise attack

1. Formalize Deninger 2.1--2.7 and the exact skew-shift/eigenvalue consequence.
2. Define the source entire quotient and prove its exact point spectrum.
3. Construct the three-term source cochain complex and compute \(H^0,H^1,H^2\).
4. Construct ordinary/compact-support Poincaré pairing and identify the packet continuous dual.
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
- [x] Reflected-diagonal source/target derivative comparison proved
- [x] Intrinsic source \(H^1=\mathcal O(\mathbb C)/(\Xi_C)\) constructed
- [x] Exact Xi-zero/Theta point-spectrum equivalence proved
- [x] Algebraic source cochain complex constructed and \(H^0,H^1,H^2\) computed
- [x] Perfect ordinary/compact-support Poincaré pairing and dual Theta law proved
- [x] Evaluation and multiplicity-bounded jet classes descended to compact-support cohomology
- [x] Source cohomological flow and endpoint flow laws proved
- [x] Source cyclic characteristic ideal and prime--Gamma logarithmic-derivative identity proved
- [x] Functional-equation even \(K_{\mathbb R}\) structure descended to source \(H^1\)
- [x] Compact-open source topology and reduced/unreduced quotient topologies constructed
- [x] Continuous dual of product jet carrier proved finite-support
- [ ] `[DAC_CLOSED_XI_RANGE]`: compact-open Xi multiplication has closed range
- [ ] Prime--Gamma packets identified with continuous compact-support dual
- [ ] Source topology, scalar cup trace, distributional Lefschetz formula, and regularized
      topological determinant proved
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
- 2026-07-25 — Closed `[DAC_REFLECTED_DIAGONAL]`: proved local derivative domination, termwise
  differentiation, diagonal squared-Cauchy comparison, and full finite-packet equality. Radical
  descent gives a nondegenerate alternating packet cup form.
- 2026-07-25 — Corrected packet-space overreach and constructed `[DAC_ENTIRE_QUOTIENT]`.
  Formalized `O(C)/(XiC)`, divided-chain Jordan recurrences, terminal-class nonvanishing, an
  explicit off-divisor Bézout inverse, and the exact source point-spectrum theorem.
- 2026-07-25 — Constructed the three-term arithmetic source complex and computed its cohomology.
  Formalized canonical Poincaré duality with compact-support algebraic dual, forced dual
  Frobenius `Theta_c=1-Theta^vee`, and the precise positive conjugate-linear Hodge identification
  whose construction would imply RH.
- 2026-07-25 — Added compact-support residue and multiplicity-bounded jet classes, source
  cohomological flow, and the exact cyclic characteristic ideal. The evaluated characteristic
  section is \(\Xi_C\) (equivalently \(\xi\)); its logarithmic derivative equals the independently
  defined prime--Gamma source trace. This does not yet claim a topological zeta-regularized
  determinant.
- 2026-07-25 — Descended the functional-equation Schwarz involution
  \(F(z)\mapsto\overline{F(-\bar z)}\) through the Xi ideal. It is multiplicative, fixes the source
  differential, commutes with Frobenius, and gives the unconditional even \(K_{\mathbb R}\)
  structure. Its \(+1\) square isolates the required odd Morita/Hodge lift as genuinely additional.
- 2026-07-25 — Constructed the compact-open source topology. Entire functions form a closed,
  completely metrizable Baire subspace of \(C(\mathbb C,\mathbb C)\); evaluation and the Xi
  differential are continuous and injective. Defined unreduced quotient topology by the Xi range
  and reduced quotient topology by its closure. Named `[DAC_CLOSED_XI_RANGE]` rather than assuming
  equality.
- 2026-07-25 — Proved the abstract product-dual theorem: any continuous complex-linear functional
  on an arbitrary product \(\prod_i\mathbb C\) is supported on finitely many coordinates. This
  supplies the compact-support conclusion once the Xi quotient is topologically identified with
  its multiplicity-jet product.
