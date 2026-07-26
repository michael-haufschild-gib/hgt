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

Algebraic Poincaré duality is a useful provisional separation theorem:
\[
 H^1_c=(H^1_{\mathrm{ent}})^\vee,\qquad B(x,\ell)=\ell(x),\qquad
 \Theta_c\ell=\ell-\ell\circ\Theta.
\]
The pairing separates both variables, and
\[
 B(\Theta x,\ell)+B(x,\Theta_c\ell)=B(x,\ell)
\]
holds identically. It is not the final compact-support object: the full algebraic dual is too
large.

The compact-open source now gives the topological distribution boundary
\[
 H^1_{\mathrm{ent,co}}=E/\Xi_CE
\]
and its strong continuous dual gives the test boundary \(H^1_c\). Deninger's Hodge star acts on
middle cohomology itself, and his Hilbert space is the completion in the resulting positive
metric. Therefore the correct final topology is the Gelfand triple
\[
 H^1_c\ \subset\ \mathcal H^1\ \subset\ H^1_{\mathrm{ent,co}},
\]
with dense test embedding, injective distribution embedding, and the original dual pairing equal
to the Hilbert pairing. It is not a bijection between the full product-like compact-open quotient
and its finite-support continuous dual. This corrected completion interface, the closed
polarized generator on \(\mathcal H^1\), source-distribution intertwining, and survival of every
source Xi eigenclass are formalized. Constructing the source Hilbert metric remains the purity
gate.

`[DAC_COMPACT_OPEN_JETS]`

Let \(E=\mathcal O(\mathbb C)\) carry the compact-open Fréchet topology, and for each zero
\(\rho\) of \(\Xi_C\) let \(m_\rho=\operatorname{ord}_\rho(\Xi_C)\). The source jet map is
\[
 J:E/\Xi_CE\longrightarrow
   \prod_{\rho\in Z(\Xi_C)}\mathbb C^{m_\rho},\qquad
 [F]\longmapsto\bigl(F^{(k)}(\rho)\bigr)_{\rho,\ 0\le k<m_\rho}.
\]
The target has product topology. The required theorem splits into two named conjectures:

1. `[DAC_CLOSED_XI_RANGE]`: multiplication
   \(M_{\Xi_C}:E\to E\) has closed range;
2. `[DAC_JET_INTERPOLATION]`: \(J\) is a topological complex-linear equivalence.

Injectivity reduces to analytic division: vanishing of all multiplicity-bounded jets means that
\(F/\Xi_C\), initially defined off the discrete divisor, has removable singularities everywhere.
Surjectivity is the global Hermite interpolation theorem on a discrete divisor. One paper route
is the exact coherent-sheaf sequence
\[
 0\longrightarrow\mathcal O
 \xrightarrow{\cdot\Xi_C}\mathcal O
 \longrightarrow\mathcal O_{Z(\Xi_C)}\longrightarrow0
\]
on the Stein line \(\mathbb C\); Cartan theorem B gives exactness on global sections and identifies
\(\Gamma(Z(\Xi_C),\mathcal O_{Z(\Xi_C)})\) with the displayed product of local jet algebras.
The constructive alternative is a Mittag--Leffler/Weierstrass exhaustion: finite Hermite CRT
supplies each correction, while compact-open error bounds make the correction series normally
convergent. Lean already contains the finite Hermite CRT brick; infinite normal-convergence and
analytic division are the two missing dependency-closed lemmas.

Continuity of \(J\) is proved because every point jet is compact-open continuous. Once the
algebraic bijection and closed Xi range are known, the Fréchet open mapping theorem makes
\(J^{-1}\) continuous. The continuous dual of the product then has finite support, already proved
abstractly, yielding
\[
 H^1_c\cong
 \bigoplus_{\rho\in Z(\Xi_C)}(\mathbb C^{m_\rho})^\vee .
\]
Thus compact support is derived from source topology rather than imposed through a divisor-indexed
definition.

The global observation map before quotienting is constructed as one continuous linear map
\[
 \widetilde J:E\longrightarrow
   \prod_{\rho\in Z(\Xi_C)}\mathbb C^{m_\rho}.
\]
Lean proves the sharper `[DAC_GLOBAL_JET_DIVISION]`
\[
 \Xi_CE=\ker\widetilde J.
\]
The reverse inclusion is obtained by normalizing the meromorphic quotient \(F/\Xi_C\). At every
Xi zero, vanishing jets give a numerator factor of the exact Xi multiplicity, while the canonical
Xi divided chain supplies the nonzero denominator cofactor. Mathlib's meromorphic normal-form
extension fills every removable value simultaneously, and the identity theorem proves the global
quotient identity. Since \(\ker\widetilde J\) is closed, `[DAC_CLOSED_XI_RANGE]` follows.
Full `[DAC_JET_INTERPOLATION]` now consists only of surjectivity of \(\widetilde J\).
Finite Hermite interpolation already proves that \(\widetilde J\) has dense range. Hence global
division makes the descended map
\[
 E/\Xi_CE\hookrightarrow
 \prod_{\rho\in Z(\Xi_C)}\mathbb C^{m_\rho}
\]
a continuous injective map with dense range, unconditionally. Full surjectivity remains a useful
coordinate theorem, but it is not allowed to delay construction of the intermediate self-dual
Hilbert cohomology.

Global jet interpolation now identifies the two topological boundaries exactly:
\[
 H^1_c=\bigoplus_{\rho,k}\mathbb C,\qquad
 H^1_{\mathrm{ent,co}}=\prod_{\rho,k}\mathbb C .
\]
Their canonical middle carrier is
\(\mathcal H^1_{\mathrm{jet}}=\ell^2(\rho,k)\). The Hilbert-to-distribution map is coordinate
inclusion followed by the inverse jet homeomorphism. On the other side, strong-dual restriction
along this inclusion is continuous; Fréchet--Riesz turns it into the required conjugate-linear
test embedding. Finite jets map to their coefficientwise conjugates and are dense. Hence
\[
 H^1_c\subset\mathcal H^1_{\mathrm{jet}}\subset H^1_{\mathrm{ent,co}}
\]
is an unconditional source-defined Gelfand triple with exact Poincaré evaluation pairing. This
constructs Hilbert carrier and topology, but not yet a Hodge metric polarizing Frobenius.

`[DAC_LOCAL_QUOTIENT_OPENNESS]`

A constructive route to `[DAC_JET_INTERPOLATION]` avoids postulating arbitrary global
Mittag--Leffler series. Given a compact-open seminorm on a closed disk, peel the finitely many Xi
zeros meeting a larger disk by exact finite Hermite interpolation. The remaining function is
locally divisible by the corresponding finite Xi factor. Taylor polynomials approximate this
local quotient uniformly on the smaller disk, while the polynomial Hermite correction preserves
the prescribed finite jets. This should prove inverse continuity of the descended jet embedding.
Completeness of the compact-open quotient then makes its dense image closed in the complete jet
product, forcing surjectivity. The dependency-closed core is therefore local quotient control plus
Taylor approximation, not an unformalized appeal to Cartan theorem B.

`[DAC_TIME_DISTRIBUTION]`

On the open time domain \(\mathbb R_+=(0,\infty)\), the full source jet flow has a canonical
distributional trace.  For a multiplicity copy \(q\) of a Xi zero \(\rho_q\), put
\[
  F_q(t)=\frac{e^{t\rho_q}}{\rho_q^2}.
\]
The source reciprocal-square divisor estimate and \(0<\Re\rho_q<1\) make
\(\sum_q F_q\) locally normally convergent.  Its second distributional derivative is therefore
the multiplicity-exact \(H^1\) trace; the nilpotent jet terms have zero finite-block trace.
The \(H^0\) and \(H^2\) traces are the regular distributions defined by \(1\) and \(e^t\).
Independently, finite places define the locally finite measure
\[
  \sum_{n\ge2}\Lambda(n)\delta_{\log n}
  =\sum_p\log p\sum_{k\ge1}\delta_{k\log p},
\]
and the archimedean place defines the regular distribution
\((1-e^{-2t})^{-1}\) on \(\mathbb R_+\).  The exact conjectured theorem is the equality in
\(\mathcal D'(\mathbb R_+,\mathbb C)\)
\[
  T_{H^0}-T_{H^1}+T_{H^2}
  =T_{\mathrm{prime}}+T_\infty .
\]
The proof must derive equality from the already formalized Xi divisor and the independently
defined von-Mangoldt/Gamma source, via a full compact-test Guinand--Weil theorem or an injective
Laplace-transform continuation theorem.  Equality on the finite resolvent algebra alone is not
accepted as distribution equality.

`[DAC_HODGE_GREEN]`

The source colligation must supply a Hilbert middle cohomology \(\mathcal H^1\) in the displayed
Gelfand triple, an odd Hodge star
\[
  *:\mathcal H^1\longrightarrow\mathcal H^1,
\]
and a cup trace such that
\(\langle x,y\rangle=\operatorname{tr}(y\cup *x)\) is positive definite. The Hodge star preserves
the domain of the closed Frobenius generator and commutes there with \(\Theta\). At the
closed-complex level it must arise from a closable Hodge operator and Green operator
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
Lean now proves this in the exact unbounded Hilbert/Gelfand category: if the Hilbert completion
intertwines with the source distribution quotient and lifts every source Xi eigenclass, the
closed polarization implies RH. This conjecture is the genuine purity/Hodge-index core and must
not be assumed inside construction of the source quotient or its spectrum.

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
  and Baire; point evaluations and Xi multiplication are continuous. The Xi quotient is now an
  actual topological complex module with a continuous class map and continuous descent/lift of
  invariant observations; unreduced and reduced quotients are constructed without assuming
  closed Xi range.
- `DeningerArithmeticProductDual`: every continuous linear functional on a product of complex
  jet coordinates depends on finitely many coordinates, proving the abstract compact-support
  mechanism needed after source jet interpolation.
- `DeningerArithmeticContinuousJets`: compact-open convergence controls every iterated
  derivative; local Xi jets are continuous and annihilate coboundaries below analytic
  multiplicity.
- `DeningerArithmeticFiniteJetInterpolation`: polynomial Hermite CRT embeds into the compact-open
  source. Explicit centered Taylor polynomials convert arbitrary scalar derivative packets into
  local polynomial classes, so every finite packet of complex Xi jets is realized. This is
  finite-stage surjectivity, not the missing global interpolation theorem.
- `DeningerArithmeticJetProduct`: all local jets assemble into one continuous linear product map;
  the Xi range lies in its closed kernel. Exact global division is named separately and implies
  closed Xi range without using interpolation.
- `DeningerArithmeticGlobalDivision`: meromorphic normal-form extension and exact local Xi
  multiplicities prove that the all-jet kernel equals the Xi range. Hence Xi multiplication has
  closed range and reduced/unreduced compact-open cohomology use the same coboundaries.
- `DeningerArithmeticDenseJets`: finite Hermite interpolation makes the all-jets observation
  dense in the full product. Global division descends it to a continuous injective dense
  realization of the compact-open Xi quotient.
- `DeningerArithmeticTopologicalCohomology`: continuous source Frobenius on the compact-open
  quotient, strong continuous compact-support dual, exact weight-one Poincaré law, compact-open
  divided-chain eigenvectors for every Xi point, and the continuous-Hodge implication to RH.
- `DeningerArithmeticGelfandTriple`: corrected test--Hilbert--distribution completion interface,
  closed polarized unbounded Frobenius, exact source-distribution intertwining, spectral-survival
  gate, and unconditional theorem that any constructed realization proves RH.
- `DeningerArithmeticJetHilbertRigging`: exact direct-sum/`ell^2`/product source Gelfand triple,
  including strong-dual restriction, Fréchet--Riesz test embedding, density, injectivity, and
  exact Poincaré pairing.
- `DeningerArithmeticPrimeGammaHilbert`: lower linear and upper conjugate-linear prime--Gamma
  packet realizations in the canonical jet `ell^2` carrier. Their source cup is exactly the
  critical-line-reflected Hilbert pairing. Packet vectors are constant across every
  analytic-multiplicity fiber, and a multiple zero makes their image provably proper.
- `DeningerArithmeticJetFrobenius`: source Leibniz law on every multiplicity jet, maximal
  square-summable domain, closed graph, dense finite-jet core, and exact intertwining with
  compact-open arithmetic Frobenius. Its local predecessor term is the full nilpotent Jordan
  contribution.
- `DeningerArithmeticJetDeterminant`: normalized centered source Frobenius on every full local jet
  fiber, including its nilpotent predecessor terms. Each local block has trace
  \(m_\rho\rho\), characteristic determinant \((z-\rho)^{m_\rho}\), and genus-one determinant
  \(E_1(z/\rho)^{m_\rho}\). The finite-window determinant net is multipliable, its global product
  is the Xi canonical product, Hadamard completion gives \(\Xi_C\), the uncentered determinant is
  \(\xi\), and its logarithmic derivative is the prime--Gamma resolvent Lefschetz trace.
- `DeningerArithmeticTopologicalJetDual`: every multiplicity-bounded local jet is a continuous,
  nonzero compact-support class; the full family separates source cohomology, and zeroth jets obey
  the reflected weight-one Frobenius law.
- `DeningerArithmeticLocalHodgeObstruction`: canonical source-local rank-one Hodge forms are
  positive semidefinite and nonzero. Their exact Frobenius commutator is the local purity defect
  `1 - lambda - conj(lambda)`; commutation at one Xi point is equivalent to that centered point
  being real, and global commutation implies RH.
- `DeningerArithmeticGeometricJetExhaustion`: Xi support in every centered closed ball is finite;
  the resulting natural finite windows are monotone and exhaust every source spectral point.
- `DeningerArithmeticFiniteHodgePackets`: positive finite sums of local Hodge forms have an exact
  weighted purity defect. Finite source Hermite interpolation isolates each summand, proving
  defects cannot cancel; commuting positive packets on the geometric exhaustion imply RH.
- `DeningerArithmeticJordanObstruction`: every positive-depth Xi divided chain survives in both
  algebraic and compact-open source cohomology. A positive weight-one Hodge star kills every
  length-two Jordan chain, so this cyclic source model would also force all Xi zeros to be simple.
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
- The full compact-open quotient is product-like while its continuous dual is finite-support.
  Requiring a Hodge bijection directly between them is overstrong and is not Deninger's Hilbert
  completion. They are the distribution/test boundaries around a missing self-dual Hilbert
  middle space.
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
- [x] Multiplicity-bounded Xi jets proved continuous on compact-open source
- [x] Arbitrary finite scalar Xi-jet packets realized inside compact-open entire source
- [x] Global continuous jet-product map constructed; its kernel proved closed
- [x] `[DAC_GLOBAL_JET_DIVISION]`: vanishing of all Xi jets implies global divisibility by Xi
- [x] `[DAC_CLOSED_XI_RANGE]`: compact-open Xi multiplication has closed range
- [x] Compact-open quotient upgraded to a topological complex module with continuous operator
      descent and continuous-dual compact support
- [x] Descended all-jets realization proved continuous, injective, and dense
- [x] Source Gelfand-triple/Hilbert-completion interface and spectral-survival RH theorem
      formalized
- [x] Continuous local compact-support jets proved nonzero and jointly separating
- [x] Canonical local positive Hodge forms and exact Frobenius purity obstruction formalized
- [x] Natural finite geometric Xi exhaustion formalized
- [x] Positive finite Hodge packets, pointwise no-cancellation, and RH implication formalized
- [x] Positive-depth Jordan-chain survival and Hodge simplicity obstruction formalized
- [x] `[DAC_LOCAL_QUOTIENT_OPENNESS]`: compact-open inverse jet control proved
- [x] `[DAC_JET_INTERPOLATION]`: quotient identified topologically with local jet product
- [x] Continuous compact-support dual identified exactly with finite-support local Xi jets
- [x] Canonical source Gelfand triple `direct sum of jets ⊂ ell^2(jets) ⊂ product of jets`
      constructed with exact Poincaré pairing
- [x] Prime--Gamma packets embedded in canonical `ell^2` middle cohomology with exact source cup
- [x] Product-topology obstruction recorded: prime--Gamma Cauchy packets are not compact-support
      finite jets and cannot recover positive-depth Jordan coordinates at a multiple zero
- [x] Closed densely defined source Frobenius constructed on canonical jet `ell^2`, including
      exact local Jordan action and distribution intertwining
- [x] Every compact-open source eigenclass classified and lifted nontrivially into the maximal
      closed jet Frobenius domain with exact eigenvalue
- [x] Full local source jet Frobenius characteristic determinants and traces computed without
      diagonalizing away nilpotent terms
- [x] Cofinal genus-one source-jet determinant constructed and identified with the Xi canonical
      product; Hadamard completion identified with `XiC` and uncentered determinant with `xi`
- [x] Source-jet determinant logarithmic derivative identified with the continued and
      absolute-convergence prime--Gamma resolvent Lefschetz traces
- [ ] Prime--Gamma radical quotients identified with their Hilbert Cauchy subspaces
- [x] Scalar source cup trace and algebraic Poincaré nondegeneracy proved
- [ ] Full time-distribution Lefschetz formula proved
- [ ] Closed-operator realization of the cofinal determinant proved trace class/Fredholm or
      Deninger-zeta-regularized in the exact Hilbert topology
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
- 2026-07-25 — Proved locally uniform convergence of every iterated derivative on the compact-open
  source. Hence all point jets are continuous linear functionals, and every jet below the Xi
  multiplicity annihilates the continuous differential range. Remaining topology core is the
  global Xi jet-interpolation/closed-range theorem.
- 2026-07-25 — Embedded polynomial Hermite CRT into the compact-open entire source. Every finite
  packet of local polynomial residue classes on the actual Xi divisor has one polynomial entire
  representative. Explicit centered Taylor polynomials then realize every arbitrary finite scalar
  derivative packet. This proves the finite stage of `[DAC_JET_INTERPOLATION]`; infinite normal
  convergence remains.
- 2026-07-25 — Assembled all multiplicity-bounded Xi jets into one continuous linear product map.
  Its kernel is closed and contains the Xi differential range. Consequently
  `[DAC_CLOSED_XI_RANGE]` follows from the strictly local-to-global analytic division equality
  `[DAC_GLOBAL_JET_DIVISION]`; global interpolation is not needed for that gate.
- 2026-07-25 — Proved `[DAC_GLOBAL_JET_DIVISION]` unconditionally. Normalized the meromorphic
  quotient \(F/\Xi_C\); multiplicity-bounded jet vanishing removes each numerator zero, the
  canonical Xi divided chain removes the denominator zero with exact multiplicity, and
  meromorphic normal form fills all removable values. Thus the Xi range is the closed all-jet
  kernel, proving `[DAC_CLOSED_XI_RANGE]`. Only global jet surjectivity remains.
- 2026-07-25 — Corrected the compact-open quotient from a bare setoid quotient to an actual
  topological complex module. Added continuous descent/lift for source operators and
  observations. Constructed continuous Frobenius, strong continuous compact-support dual,
  weight-one Poincaré law, and multiplicity-exact source eigenvectors on this quotient.
- 2026-07-25 — Proved finite interpolation already makes the all-jets map dense. Combined with
  global Xi division, the source quotient embeds continuously and injectively with dense range in
  the full local jet product; infinite interpolation is now isolated as surjectivity only.
- 2026-07-25 — Primary-source audit corrected the Hodge topology: Deninger's star acts on middle
  cohomology and the positive metric is completed afterward. Formalized the source-defined
  Gelfand triple \(H^1_c\subset\mathcal H^1\subset H^1_{\mathrm{ent,co}}\), a closed polarized
  unbounded generator, source-distribution intertwining, survival of all Xi eigenclasses, and the
  unconditional theorem that construction of this exact Hilbert realization implies RH.
- 2026-07-25 — Constructed all local compact-support jet classes in the strong continuous dual.
  Finite source interpolation proves each is nonzero; exact global division proves the family
  separates compact-open \(H^1\). Constructed the canonical rank-one local Hodge form
  \(\star_\rho(x)(y)=\overline{j_\rho(x)}j_\rho(y)\), proved unconditional semipositivity, and
  computed its full Frobenius commutator as
  \((1-\lambda_\rho-\overline{\lambda_\rho})\star_\rho(x)\). Thus local commutation is exactly
  realness of the centered Xi point, and simultaneous commutation implies RH.
- 2026-07-25 — Replaced the possible global-cancellation loophole by an exact no-cancellation
  theorem. Centered closed balls give a natural finite exhaustion of Xi support. Positive weighted
  finite sums of the local Hodge forms remain semipositive, and finite Hermite interpolation
  isolates any selected summand; packet commutation therefore forces every included local purity
  defect to vanish. Commuting packets over the exhaustion imply RH.
- 2026-07-25 — Proved every positive-depth divided chain survives in source cohomology. A direct
  positive weight-one Hodge star excludes a length-two Jordan chain by Poincaré compatibility and
  strict positivity. Consequently this cyclic entire-quotient realization requires simplicity of
  all Xi zeros in addition to RH. Isolated `[DAC_LOCAL_QUOTIENT_OPENNESS]` as the constructive
  compact-open route from finite peeling and Taylor approximation to full jet interpolation.
- 2026-07-25 — Closed `[DAC_LOCAL_QUOTIENT_OPENNESS]` constructively. Local Xi division, Taylor
  control, finite jet sections, and finite peeling prove inverse control for the descended all-jets
  embedding. Small Xi-coboundary corrections plus an antitone Cauchy construction then interpolate
  arbitrary infinite multiplicity-bounded jet families by one compact-open entire source. Hence
  compact-open arithmetic \(H^1\) is homeomorphic to the full local Xi-jet product.
- 2026-07-25 — Transported the elementary finite-coordinate theorem through the jet
  homeomorphism. Every continuous compact-support class is exactly a finite linear combination of
  local Xi-jet evaluations. This proves the source Gelfand boundary
  \(H^1_c=\bigoplus_\rho J_\rho^\vee\) against
  \(H^1_{\mathrm{ent,co}}=\prod_\rho J_\rho\), without a quotient-completeness assumption.
- 2026-07-25 — Corrected a variance error in the abstract Gelfand interface: a complex-linear
  test embedding cannot realize the ordinary dual pairing through mathlib's
  conjugate-linear-first inner product except trivially. Replaced it by the forced
  conjugate-linear embedding and proved the obstruction theorem. Constructed the canonical
  source middle carrier `ell^2(rho,k)`. Strong-dual restriction plus Fréchet--Riesz gives the
  dense test embedding, while coordinate inclusion gives the injective distribution embedding;
  their Hilbert pairing is exactly source Poincaré evaluation. No Hodge positivity, Frobenius
  symmetry, zero-location, or simplicity assumption is used.
- 2026-07-25 — Corrected the proposed prime--Gamma/compact-dual identification. Cauchy packets
  have infinitely supported divisor evaluations, whereas the continuous dual of product
  cohomology is finite-support. Embedded lower packets linearly and upper packets
  conjugate-linearly into canonical jet `ell^2`; proved source prime--Gamma cup equals the
  unconditional critical-line-reflected Hilbert pairing. Both images are constant across local
  multiplicity indices. If any Xi zero has multiplicity at least two, Lean proves the packet map
  is not surjective onto full jet Hilbert cohomology. Thus the explicit trace sees algebraic
  multiplicity but not positive-depth Jordan jets.
- 2026-07-25 — Derived full Frobenius action from source multiplication, rather than a diagonal
  divisor declaration:
  \((\Theta a)_{\rho,k}=(1/2+i\rho)a_{\rho,k}+ki\,a_{\rho,k-1}\).
  Constructed its maximal `ell^2` `LinearPMap`, proved graph closed as an intersection of
  continuous coordinate kernels, proved finite jets form a dense operator core, and proved exact
  intertwining with compact-open source Frobenius through the Gelfand distribution embedding.
- 2026-07-25 — Classified the full compact-open point spectrum by the source jet recurrence.
  An eigenclass at \(\rho\) vanishes on every other divisor fiber and on every jet below the
  highest multiplicity index, hence is a scalar top-jet basis vector. Used this theorem to
  construct a canonical nonzero `ell^2` lift of every chosen source Xi eigenclass, prove it belongs
  to the maximal closed Frobenius domain, and prove the closed generator acts with the exact source
  eigenvalue. No RH, Hodge positivity, zero simplicity, or divisor-model premise is used.
- 2026-07-26 — Proved `[DAC_JET_COFINAL_DETERMINANT]`. Kept the complete normalized source
  Frobenius jet block
  \((Ba)_k=\rho a_k+k a_{k-1}\), proved it lower triangular, and computed its trace and
  characteristic determinant exactly. The nilpotent Jordan terms contribute neither trace nor
  determinant. Genus-one normalization gives \(E_1(z/\rho)^{m_\rho}\); the finite-support
  determinant net is multipliable and its product is the multiplicity-exact Xi canonical product.
  The nowhere-zero Hadamard quotient completes this to `XiC`, the uncentered determinant is `xi`,
  the alternating endpoint quotient is completed zeta, and the determinant logarithmic derivative
  is exactly the continued/absolute prime--Gamma resolvent Lefschetz trace. Remaining determinant
  gate is its realization as the trace-class/Fredholm or zeta-regularized determinant of the
  closed Hilbert operator itself, rather than only the dependency-closed cofinal block net.
- 2026-07-26 — Froze the CCM detour and returned to Deninger's Proposition 3.2 on
  \((0,\infty)\). Constructed the actual test/distribution spaces, endpoint traces, the
  multiplicity-exact reciprocal-square regularized \(H^1\) flow and its second distributional
  derivative, the locally finite von-Mangoldt Dirac comb, and the regular archimedean density.
  For every \(\phi\in C_c^\infty((0,\infty))\), proved its Laplace amplitude is entire, two exact
  integrations by parts give reciprocal-square Xi-divisor summability, and the constructed
  \(H^1\) trace acts exactly as \(\sum_\rho\Phi(\rho)\). Centering this arbitrary test gives the
  finite admissible source-contour identity and cofinal contour approximation to the full spectral
  sum. Formalized the exact equivalence between the remaining scalar Deninger explicit formula
  and equality in \(\mathcal D'((0,\infty),\mathbb C)\). No special CCM test family, RH premise,
  or numerical computation is used.
- 2026-07-26 — `[CONJECTURE] [DAC_ARCH_LINE]`: for every
  \(\phi\in C_c^\infty((0,\infty))\), \(\Phi(s)=\int\phi(t)e^{st}\,dt\), and \(c>1\),
  \[
    \int_{\mathbb R}\Phi(c-2\pi i\xi)
      \frac{\operatorname{archFactor}'}
           {\operatorname{archFactor}}(c-2\pi i\xi)\,d\xi
    =\Phi(0)+\Phi(1)-
      \int_0^\infty\frac{\phi(t)}{1-e^{-2t}}\,dt .
  \]
  Hostile audit verdict: `REDISCOVERED` as the arbitrary-test archimedean component of the
  classical Weil explicit formula, but it is the exact missing direct Deninger bridge and does
  not assume RH. `[PAPER-PROVED]` dependency-closed proof: compact support inside the open
  positive axis makes the zero extension Schwartz and gives \(\phi(0)=0\). Fourier inversion
  gives
  \[
    \int_{\mathbb R}e^{2\pi i\xi x}\Phi(c-2\pi i\xi)\,d\xi
      =\phi(x)e^{cx}.
  \]
  For \(a>0\), insert
  \((a-2\pi i\xi)^{-1}=\int_0^\infty e^{-at}e^{2\pi i\xi t}\,dt\);
  Tonelli/Fubini is justified by the Schwartz \(L^1\) Fourier amplitude and the \(L^1\)
  exponential. Hence
  \[
    \int_{\mathbb R}\frac{\Phi(c-2\pi i\xi)}
      {a-2\pi i\xi}\,d\xi
      =\int_0^\infty\phi(t)e^{(c-a)t}\,dt .
  \]
  The closed identity
  \[
    (\log\operatorname{archFactor})'(s)
      =s^{-1}+(s-1)^{-1}
       -\tfrac12\log\pi+\tfrac12\psi(s/2)
  \]
  makes the two rational terms equal \(\Phi(0)\) and \(\Phi(1)\). Gauss's absolutely
  convergent series
  \(\psi(s/2)=-\gamma+\sum_{n\ge0}((n+1)^{-1}-(n+s/2)^{-1})\)
  has constant terms integrating to \(\phi(0)=0\); every remaining resolvent contributes
  \(-\int_0^\infty\phi(t)e^{-2nt}\,dt\). Dominated convergence is valid because the support
  lies in \([\delta,M]\subset(0,\infty)\), so the geometric series is uniformly dominated there.
  Summing gives the stated density. `[OPEN CORE]`: formalize this exact arch line, then identify
  the right Xi logarithmic-derivative line with the multiplicity-exact spectral sum by the
  relative-resolvent/Bromwich transform.
- 2026-07-26 — `[LEAN-PROVED] [DAC_ARCH_LINE]` in
  `DeningerArithmeticArchimedean.lean`. For every smooth compactly supported positive-time test,
  proved a positive support gap, absolute summability of all negative-even Laplace samples,
  Tonelli interchange with their geometric series, and the exact identity
  \[
    \sum_{n\ge0}\Phi(-2n)
      =\int_{\mathbb R}\frac{\phi(t)}{1-e^{-2t}}\,dt .
  \]
  Independently constructed an integrable Gauss-series majorant on the Euler line, passed its
  finite resolvent integrals to the digamma limit by dominated convergence, removed the Euler
  constant using the zero-frequency Fourier integral, and combined the Gamma connection with
  the two boundary resolvents. Lean now proves unconditionally
  \[
    \int_{\mathbb R}\Phi(3/2-2\pi i\xi)
      (\log\operatorname{archFactor})'(3/2-2\pi i\xi)\,d\xi
      =\Phi(0)+\Phi(1)
       -\int_{\mathbb R}\frac{\phi(t)}{1-e^{-2t}}\,dt .
  \]
  Cached direct check:
  `lake env lean GaloisForLFunctions/RHTower/DeningerArithmeticArchimedean.lean`.
  No RH premise, special test family, CCM theorem, or numerical computation occurs.
  `[OPEN CORE]`: identify the right Xi logarithmic-derivative line with
  \(\sum_\rho\Phi(\rho)\) using the existing multiplicity-exact relative resolvent and a
  dependency-closed Bromwich/sum-interchange argument.
- 2026-07-26 — `[CONJECTURE] [DAC_XI_LINE]`: for every
  \(\phi\in C_c^\infty((0,\infty))\), with
  \(\Phi(s)=\int\phi(t)e^{st}\,dt\),
  \[
    \int_{\mathbb R}\Phi(3/2-2\pi i\xi)
      \frac{\xi'}{\xi}(3/2-2\pi i\xi)\,d\xi
      =\sum_\rho\Phi(\rho),
  \]
  with analytic multiplicities. Hostile audit verdict: `REDISCOVERED`; this is the
  multiplicity-exact spectral half of the classical explicit formula, but its arbitrary-test
  Lean realization is absent from the corpus. `[PAPER-PROVED]` dependency-closed route:
  put \(s_\xi=3/2-2\pi i\xi\) and
  \(z_\xi=(s_\xi-1/2)(-i)=-2\pi\xi-i\). The existing centered Hadamard theorem gives
  \[
    \frac{\xi'}{\xi}(s_\xi)
      =-i\sum_a\left(a^{-1}-(a-z_\xi)^{-1}\right),
    \qquad a=(\rho-1/2)(-i).
  \]
  Since \(0<\Re\rho<1\), the horizontal centered line
  \(\Im z=-1\) has distance at least \(1/2\) from every \(a\). For each term,
  \[
    \left|a^{-1}-(a-z)^{-1}\right|
      =\frac{|z|}{|a||a-z|}
      \le \frac{|z|+2|z|^2}{|a|^2}.
  \]
  The Euler-line amplitude is Schwartz, so its product with the polynomial majorant is
  integrable; \(\sum_a|a|^{-2}<\infty\) then gives the required Tonelli interchange.
  Algebraically
  \[
    -i\left(a^{-1}-(a-z_\xi)^{-1}\right)
      =(\rho-1/2)^{-1}+(s_\xi-\rho)^{-1}.
  \]
  The constant integrates to zero because the test is supported in positive time. The complex
  Bromwich identity, valid for \(\Re A>0\),
  \[
    \int_{\mathbb R}
      \frac{\Phi(c-2\pi i\xi)}{A-2\pi i\xi}\,d\xi
      =\Phi(c-A),
  \]
  applied to \(A=3/2-\rho\), returns \(\Phi(\rho)\). Absolute summability closes the
  multiplicity-exact sum. `[OPEN CORE]`: formalize the complex Bromwich extension and this
  inverse-square dominated interchange, then combine `[DAC_XI_LINE]`, `[DAC_ARCH_LINE]`, and the
  already formalized Euler line to close Deninger's full distributional Lefschetz equality.
- 2026-07-26 — `[LEAN-PROVED] [DAC_XI_LINE]` in
  `DeningerArithmeticSpectralLine.lean`. Generalized the arbitrary-test Bromwich theorem from
  positive real resolvents to all complex resolvents with positive real part. On the centered
  right line \(z_\xi=-2\pi\xi-i\), proved the uniform distance bound
  \(\|a-z_\xi\|\ge 1/2\) for every multiplicity copy of every Xi zero and the exact estimate
  \[
    \left\|a^{-1}-(a-z_\xi)^{-1}\right\|
      \le (\|z_\xi\|+2\|z_\xi\|^2)\|a\|^{-2}.
  \]
  Polynomial multiplication preserves the Schwartz Euler amplitude, so the resulting common
  majorant is integrable. Reciprocal-square divisor summability then justifies the full
  integral/tsum interchange. Each term reduces algebraically to one zero-frequency constant,
  whose integral vanishes, and one complex Bromwich resolvent, whose integral is
  \(\Phi(\rho)\). Lean proves
  \[
    \int_{\mathbb R}\Phi(3/2-2\pi i\xi)
      (\xi'/\xi)(3/2-2\pi i\xi)\,d\xi
      =\sum_\rho\Phi(\rho)
  \]
  with exact analytic multiplicities and no RH or simplicity premise.
- 2026-07-26 — `[LEAN-PROVED] [DAC_DISTRIBUTIONAL_LEFSCHETZ]` in
  `DeningerArithmeticLefschetz.lean`. Combined `[DAC_XI_LINE]`, `[DAC_ARCH_LINE]`, and the
  independently proved von-Mangoldt Euler line. This closes Deninger's Proposition 3.2 for every
  \(\phi\in C_c^\infty((0,\infty))\) and then transports the scalar identity through the already
  proved extensional equivalence to
  \[
    \operatorname{Tr}(S_t|H^0)-\operatorname{Tr}(S_t|H^1)
      +\operatorname{Tr}(S_t|H^2)
      =\sum_{p,k\ge1}\log p\,\delta_{k\log p}
        +\frac{1}{1-e^{-2t}}
  \]
  in \(\mathcal D'((0,\infty),\mathbb C)\). Direct all-source audit:
  `lake env lean /tmp/deninger_lefschetz_audit.lean`. No `.olean` generation, early `lake build`,
  numerical computation, CCM hypothesis, RH premise, or unproved declaration was used.
  `[OPEN CORE]`: construct Deninger's Hodge star/Green operator on arithmetic cohomology, prove
  its positive definite polarization and Frobenius adjoint law
  \(\Theta^\ast=1-\Theta\), then derive RH from spectral purity.
- 2026-07-26 — `[LEAN-PROVED] [DAC_SEMISIMPLE_HODGE_GATE]` in
  `DeningerArithmeticSemisimpleHodge.lean`. Distinguished the nonreduced cyclic source quotient
  from its multiplicity-exact semisimplification. The associated-graded algebraic carrier uses
  the same source local-jet copy index
  \[
    \coprod_{\rho\in\operatorname{Supp}\operatorname{div}\xi}
      \{0,\ldots,m_\rho-1\},
  \]
  but lets Frobenius act by the support eigenvalue on every graded copy; definitionally this is
  the already constructed multiplicity-copy divisor target. Functional-equation reflection
  followed by coefficient conjugation gives a bijective Hodge identification. Lean proves
  unconditionally
  \[
    \langle a,a\rangle_{\mathrm H}
      =\sum_{\rho,k}|a_{\rho,k}|^2>0\qquad(a\ne0),
  \]
  its involutivity, and the weight-one Poincaré derivation law. This removes the false
  “positive metric itself is missing” diagnosis on the semisimplification and avoids the
  nonreduced model's extra zero-simplicity conclusion.

  The exact remaining defect is now computed coordinatewise:
  \[
    \bigl(\Theta\star-\star\Theta\bigr)(a)_q
      =\left(\lambda_q-\overline{\lambda_{Rq}}\right)
        \overline{a_{Rq}},
    \qquad \lambda_{Rq}=1-\lambda_q.
  \]
  Consequently Lean proves, with both directions and exact multiplicities,
  \[
    \Theta\star=\star\Theta
      \quad\Longleftrightarrow\quad
    \operatorname{Re}\lambda_q=\tfrac12\ \forall q
      \quad\Longleftrightarrow\quad \mathrm{RH}.
  \]
  Direct cached check:
  `lake env lean GaloisForLFunctions/RHTower/DeningerArithmeticSemisimpleHodge.lean`.
  No CCM object, numerical computation, RH premise in the forward implication, simplicity
  premise, `sorry`, or new axiom occurs.

  `[CONJECTURE] [DAC_SOURCE_GREEN_PURITY]`: construct, from the prime--Gamma source complex and
  its archimedean boundary operator, a Green/Hodge comparison whose chain-level naturality
  descends to the above semisimple star and proves
  \(\Theta\star=\star\Theta\). Hostile audit: the bare commutation statement is exactly RH by the
  theorem just proved and therefore is not an admissible provider. A valid proof must establish
  an independent source identity before divisor evaluation; it may not use Xi zero locations,
  Weil positivity, self-adjointness, or a measure whose support is assumed real. The next attack
  is to formulate the required chain homotopy/Green identity on the prime--Gamma source domain
  and test whether its boundary term is a genuinely positive square or the already known Weil
  sign in disguise.

- 2026-07-26 — `[PAPER-PROVED] [BRIDGE] [DAC_REAL_HODGE_FACTORIZATION]`.
  Deninger's original formalism distinguishes two structures that must not be conflated:
  a flow-invariant real structure and an antilinear Hodge star.  In the original notation the
  required middle-degree law for \(d=\nu=1\) is
  \[
    \Theta\circ\star=\star\circ\Theta
  \]
  and the Hodge metric is \(\operatorname{tr}(a\cup\star b)\); see Deninger,
  *The Hilbert--Polya strategy and height pairings*, pp. 3--4,
  <https://www.uni-muenster.de/SFB878/publications/files/php7aMxKR3029.pdf>.

  The source jet model makes the distinction exact.  Write \(C(\rho)=\bar\rho\),
  \(R(\rho)=1-\rho\), and \(L(\rho)=1-\bar\rho=R C(\rho)\), with the same derivative-copy
  index \(k\).  The compact-open source theorem already proves that Schwarz reflection acts on
  raw jets by
  \[
    (\sigma_{\rm raw}a)_{\rho,k}
      =(-1)^k\overline{a_{C\rho,k}}.
  \]
  Rephase degree \(k\) by \(U_k=i^k\).  Since
  \(i^k(-1)^k=(-i)^k=\overline{i^k}\), the conjugated source Real structure is
  \[
    S=U\sigma_{\rm raw}U^{-1},\qquad
    (Sa)_{\rho,k}=\overline{a_{C\rho,k}}.                 \tag{15}
  \]
  It is an antilinear involution and commutes with the semisimple Frobenius
  \((\Theta a)_{\rho,k}=\rho a_{\rho,k}\), because
  \(\rho=\overline{C\rho}\).

  Define the complex-linear arithmetic Weil transport
  \[
    (Wa)_{\rho,k}=a_{L\rho,k}.                            \tag{16}
  \]
  It is an involutive unitary permutation.  Direct substitution gives the exact factorization
  \[
    (WSa)_{\rho,k}
      =\overline{a_{C L\rho,k}}
      =\overline{a_{R\rho,k}}
      =(\star a)_{\rho,k}.                               \tag{17}
  \]
  Thus the positive Hodge star already constructed on semisimplified arithmetic cohomology is
  not the source Real structure: it is the source Real structure followed by \(W\).

  Because \(S\Theta=\Theta S\) and \(S^2=1\), equation `(17)` gives
  \[
    \Theta\star=\star\Theta
      \Longleftrightarrow
    \Theta W=W\Theta.
  \]
  On the coordinate vector \(e_{\rho,k}\), the latter is
  \[
    \rho\,e_{L\rho,k}=(L\rho)\,e_{L\rho,k},
  \]
  hence \(\rho=L\rho=1-\bar\rho\).  Conversely this equality makes the two diagonal actions
  agree.  Therefore
  \[
    \Theta W=W\Theta
      \Longleftrightarrow
    \operatorname{Re}\rho=\tfrac12\quad\text{for every Xi zero}
      \Longleftrightarrow \mathrm{RH}.                   \tag{18}
  \]

  Hostile audit verdict: `REDISCOVERED/BRIDGE`.  This is the standard Hodge-theoretic
  factorization of an antilinear star into a Real structure and a complex-linear Weil operator,
  made multiplicity-exact on the actual Xi divisor.  It proves no source positivity theorem.
  Its value is to sharpen `[DAC_SOURCE_GREEN_PURITY]`: a Green construction must produce the
  specific source realization of \(W\), not another Real involution, and must prove its
  Frobenius naturality before divisor evaluation.  Assuming that naturality is exactly RH by
  `(18)`.

- 2026-07-26 — `[CORRECTION] [PAPER-PROVED] [DAC_ORIENTED_HODGE]`.
  The positive identification in `[DAC_SEMISIMPLE_HODGE_GATE]` is mathematically valid as an
  ordinary/compact-support comparison, but it is not yet Deninger's genuine degree-one Hodge
  structure: its reflected cup form is symmetric and its antilinear map squares to \(+1\).
  Degree-one graded commutativity requires an alternating cup form, and the corresponding Hodge
  operator must square to \(-1\), exactly as required by `DeningerWeightOnePolarization.lean`.

  This defect has a canonical repair.  Functional-equation reflection
  \(R(\rho,k)=(1-\rho,k)\) is fixed-point free because the centered spectral coordinate
  \(a_\rho=(\rho-\tfrac12)(-i)\) is nonzero and \(a_{R\rho}=-a_\rho\).  Orient every \(R\)-orbit
  by the lexicographic positive half-plane:
  \[
    \epsilon_q=
    \begin{cases}
      +1,&\Re a_q>0\text{ or }(\Re a_q=0\text{ and }\Im a_q>0),\\
      -1,&\text{otherwise}.
    \end{cases}
  \]
  Then \(\epsilon_q\in\{\pm1\}\) and
  \[
    \epsilon_{Rq}=-\epsilon_q.                            \tag{19}
  \]

  On the multiplicity-exact finite-support carrier define
  \[
    \omega(a,b)=\sum_q\epsilon_q\,a_q b_{Rq},\qquad
    (\star_\epsilon a)_q=-\epsilon_q\,\overline{a_{Rq}}. \tag{20}
  \]
  Reindexing the finite sum by \(R\), using `(19)`, gives
  \(\omega(a,a)=-\omega(a,a)\), hence \(\omega(a,a)=0\).  If \(a_q\ne0\), pairing with
  \(e_{Rq}\) gives \(\epsilon_q a_q\ne0\), so \(\omega\) is nondegenerate.  Moreover
  \[
    \star_\epsilon^2a=-a,\qquad
    \omega(b,\star_\epsilon a)
      =\sum_q b_q\overline{a_q}
      =\langle a,b\rangle_{\ell^2}.                       \tag{21}
  \]
  Thus `(20)` is an odd positive Hodge structure, not merely a positive Real identification.

  For \((\Theta a)_q=\lambda_q a_q\) and
  \(\lambda_{Rq}=1-\lambda_q\), finite reindexing proves the weight-one derivation law
  \[
    \omega(\Theta a,b)+\omega(a,\Theta b)=\omega(a,b).    \tag{22}
  \]
  The exact Hodge defect is
  \[
    ((\Theta\star_\epsilon-\star_\epsilon\Theta)a)_q
      =-\epsilon_q
        \bigl(\lambda_q-\overline{\lambda_{Rq}}\bigr)
        \overline{a_{Rq}}.                                \tag{23}
  \]
  Testing `(23)` on coordinate vectors shows
  \[
    \Theta\star_\epsilon=\star_\epsilon\Theta
      \Longleftrightarrow
    \lambda_q=\overline{1-\lambda_q}\ \forall q
      \Longleftrightarrow \mathrm{RH}.                    \tag{24}
  \]

  The same formulas extend to the canonical \(\ell^2\) completion.  The cup series is absolutely
  convergent by Cauchy--Schwarz, \(\star_\epsilon\) is antiunitary, and it preserves the maximal
  closed Frobenius domain unconditionally because
  \(|\lambda_{Rq}|=|1-\lambda_q|\le1+|\lambda_q|\).

  Hostile audit verdict: `REDISCOVERED/BRIDGE`; this is the standard symplectic orientation of a
  fixed-point-free involutive spectral divisor, specialized to Deninger's exact multiplicity
  carrier.  The positive survivor is substantial: it upgrades the constructed carrier to the
  correct alternating/odd Hodge category without assuming RH.  The remaining source theorem is
  still `(24)`, and may not be assumed.  `[OPEN CORE]`: formalize `(19)`--`(24)`, then construct
  the oriented Weil transport from the prime--Gamma/positive-time source Green operator and prove
  its Frobenius naturality before divisor evaluation.

- 2026-07-26 — `[FORMALIZED] [DAC_ORIENTED_HILBERT_HODGE]`.
  Equations `(19)`--`(24)` are now formalized on both finite support and the canonical Hilbert
  completion.  Direct Lean checks pass for:
  `DeningerArithmeticSemisimpleHodge.lean`,
  `DeningerArithmeticOrientedHodge.lean`,
  `XiDivisorHilbertCarrier.lean`,
  `DeningerDivisorClosedGenerator.lean`, and
  `DeningerArithmeticOrientedHilbertHodge.lean`.

  The completed operator is
  \[
    (Ja)_q=-\epsilon_q\overline{a_{Rq}},\qquad
    \omega(a,b)=\langle Ja,b\rangle.
  \]
  Lean proves unconditionally:
  \(J^2=-1\), antiunitarity, alternation and nondegeneracy of \(\omega\),
  \(\omega(a,Ja)>0\) for \(a\ne0\), preservation of the maximal diagonal Frobenius domain,
  closedness and density of that domain, and the weight-one cup derivation law.  It also proves
  the exact equivalence
  \[
    J\Theta=\Theta J\text{ on }\operatorname{Dom}\Theta
      \Longleftrightarrow \mathrm{RH}.                   \tag{25}
  \]
  This is a target-side purity gate, not an RH proof.

  To keep this construction independent of the unrelated resolvent/positivity import graph, the
  bare carrier `XiDivisorL2` was extracted to `XiDivisorHilbertCarrier.lean`; the existing
  `XiWeilDivisorHilbert.lean` and closed-generator module now share that minimal definition.

  `DeningerArithmeticCompletedCohomology.lean` has been drafted to assemble
  \(H^0=\mathbf C\), \(H^1=\ell^2(\operatorname{Div}\Xi)\), and
  \(H^2=\mathbf C(-1)\), with endpoint and middle Poincare pairings, endpoint and middle Hodge
  metrics, endpoint weights, closed middle Frobenius, derivation laws, and `(25)`.  Direct checking
  is pending while another repository-wide build is replacing transitive `.olean` files.

  `[SCOPE LOCK]`: no CCM construction belongs to this card.  Reusable generic lemmas may be used
  only when they directly close the Deninger chain
  \(H^0/H^1/H^2\to\) cup/Poincare \(\to\) Frobenius \(\to\) determinant/Lefschetz
  \(\to\) source Green/Hodge positivity \(\to\) RH.

  `[OPEN CORE]`: construct a prime--Gamma/positive-time source Green operator whose completed
  comparison map lands densely in this Hilbert \(H^1\), prove it induces the oriented Hodge
  operator \(J\), and prove Frobenius naturality before any divisor evaluation.  By `(25)`, that
  naturality is the precise non-circular theorem from which RH follows.

- 2026-07-26 — `[SCOPE RESET] [DIRECT DENINGER ONLY]`.
  Work is now locked to the theorem chain stated in `docs/Deninger program.md`:
  \[
    H^0/H^1/H^2
      \longrightarrow \cup/\operatorname{PD}
      \longrightarrow \Theta
      \longrightarrow \det_\infty/\operatorname{Lefschetz}
      \longrightarrow \operatorname{Green}/\star
      \longrightarrow \mathrm{RH}.
  \]
  No CCM conjecture, packet, positivity criterion, or module is an allowed research branch.
  Only an isolated generic lemma may be reused when its statement is independently part of the
  displayed Deninger chain.

  Direct corpus audit against the nine sections of the program:

  | Deninger obligation | Direct source theorem/module | Status |
  |---|---|---|
  | \(H^0=\mathbf C,\ H^1=\mathcal O/\Xi\mathcal O,\ H^2=\mathbf C(-1)\) | `DeningerArithmeticCochainComplex` | Lean-proved |
  | compact-open topology and \(H^1_c\subset\mathcal H^1\subset H^1\) | `DeningerArithmeticJetProductEquivalence`, `DeningerArithmeticJetHilbertRigging` | Lean-proved |
  | source Frobenius and closed dense Hilbert domain | `DeningerArithmeticTopologicalCohomology`, `DeningerArithmeticJetFrobenius` | Lean-proved |
  | cup/Poincaré derivation law | `DeningerArithmeticPoincareDuality`, `DeningerPrimeGammaPoincareDuality` | Lean-proved |
  | regularized determinant \(=\widehat\zeta\) | `DeningerArithmeticJetDeterminant` | Lean-proved |
  | prime-power plus archimedean Lefschetz distribution | `DeningerArithmeticLefschetz` | Lean-proved |
  | odd positive completed Hodge form | `DeningerArithmeticOrientedHilbertHodge` | Lean-proved |
  | source derivation of semisimple completed \(H^1\) | `DeningerArithmeticAssociatedGraded` | drafted; direct check pending |
  | Frobenius naturality of source Green/Hodge operator | `[DAC_SOURCE_GREEN_PURITY]` | open mathematical core |
  | RH extraction from that naturality | `deningerDivisorClosedTheta_orientedHodge_iff_riemannHypothesis` | Lean-proved equivalence |

  `[CONJECTURE] [DAC_SOURCE_ASSOCIATED_GRADED]` has now been reduced to a paper proof and a Lean
  draft.  On compact-open source cohomology define the decreasing jet-depth filtration
  \[
    F^nH^1=\{x:\ j_{\rho,k}(x)=0\text{ for every }k<n\}.
  \]
  The exact source formula
  \[
    j_{\rho,k}(\Theta x)
      =\lambda_\rho j_{\rho,k}(x)
        +k i\,j_{\rho,k-1}(x)
  \]
  gives \(\Theta(F^n)\subseteq F^n\), while
  \[
    (\Theta-\Theta_{\rm ss})(F^n)\subseteq F^{n+1}.
  \]
  Hence the induced map on every \(F^n/F^{n+1}\) is multiplication by
  \(\lambda_\rho\).  Taking the Hilbert direct sum of all grades yields the already constructed
  multiplicity-exact \(\ell^2(\rho,k)\) carrier and its maximal diagonal closed generator.
  `DeningerArithmeticAssociatedGraded.lean` formalizes the filtration, preservation, congruence
  modulo the next step, and comparison on finite source jets.  Its first direct check reached a
  missing transitive `.olean` cache before elaborating the new file; no unrelated dependency was
  rebuilt.
