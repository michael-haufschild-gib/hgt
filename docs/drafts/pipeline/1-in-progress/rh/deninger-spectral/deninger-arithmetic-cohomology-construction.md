# Deninger arithmetic cohomology for the arithmetic curve

- **ID:** `deninger-arithmetic-cohomology-construction`
- **Stage:** 1-in-progress
- **Type:** CONJECTURAL CONSTRUCTION / RH PROGRAM
- **Primary target:** `docs/Deninger program.md`
- **Rule:** construct from Deninger's rational-Witt dynamical space with the derived
  Milnor--Witt coefficient complex.  Euler--Gamma/Xi objects are comparison targets only.
- **Active concise ledger:**
  `deninger-source-native-arithmetic-cohomology-roadmap.md`.

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

CCM cyclic cohomology is frozen. It is not the arithmetic cohomology theory, it supplies none of
the missing source Hodge--Green positivity, and no further CCM work is in scope before every
Deninger gate on this card is closed. A later comparison theorem may be opened only after the
arithmetic theory and RH derivation are complete.

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

## Active Deninger source coefficient

The active middle coefficient is no longer the entire Xi quotient described
later in this historical card.  It is Meyer's source-defined
Poisson--zeta quotient
\[
 H_\cap
 =
 \{f\in\mathcal S(\mathbb R)^{\mathrm{even}}:
       f(0)=\mathcal Ff(0)=0\},
 \qquad
 M_\zeta
 =
 H_-\Big/\left\{x\mapsto\sum_{n\ge1}f(nx):f\in H_\cap\right\}.       \tag{A}
\]
The differential in `(A)` is the sum of Deninger's discrete
positive-time flow pullbacks on the canonical Hilbert--Kummer
suspension radius:
\[
 [F_nP,u]=[P,nu]=\phi^{\log n}[P,u].
\]
It is defined without a zero divisor.  Poisson summation supplies its
real-place gluing; its Euler factorization supplies the finite-prime
maps.

Joining `(A)` to the proved strict Milnor--Arakelov endpoint gives a
source-defined three-term complex with
\[
 H^0=\mathbb C,\qquad H^1=M_\zeta,\qquad H^2=\mathbb C(-1).
\]
The abstract assembly and its concrete finite-plus-real Arakelov
endpoint are now formalized unconditionally in Lean:
`DeningerArithmeticPoissonZetaAssembly.lean` proves the quotient
calculation, while
`DeningerArithmeticArakelovPoissonComplex.lean` proves the concrete
\(H^0/H^1/H^2\) equivalences and endpoint cup pairing.
Meyer's theorems give the exact zero spectrum with multiplicity and the
prime-plus-archimedean Weil character.  Deninger's regularized-product
theorem gives the completed-zeta determinant.  Paugam gives the
unconditional alternating spectral pairing and, through upper/lower
sign--conjugation, the odd spectral \(K_{\mathbb R}\)-operator with
square \(-1\).  Positivity of the resulting sesquilinear form remains
the RH-bearing gate.  These statements are
recorded, with topology caveats, in
`DAC_POISSON_ZETA_THREE_TERM_COHOMOLOGY`.

The two exact open source gates are:

1. `DAC_DENINGER_POISSON_RELEVANT_COMPLEX_COMPARISON`: construct the
   logarithmic Schwartz collar on Deninger's rational-Witt suspension
   and identify \(R\Gamma_c(X_{\mathrm{Den}},R\alpha_*\mathcal G)\)
   with the Poisson--zeta complex.
2. Construct a positive flow-natural Hodge polarization on the resulting
   \(M_\zeta\), including its generalized-jet topology.  This is the
   RH-bearing theorem and may not be replaced by a metric declared from
   the zero divisor.

All Xi-divisor, Euler--Gamma, and Hilbert completions below are frozen
comparison targets and obstruction tests.  They do not define arithmetic
cohomology.

## Frozen analytic comparison target

Everything in this section is retained as already proved comparison infrastructure.  None of it
is the arithmetic coefficient theory, and no extension of these Xi/Euler--Gamma models counts
toward the active construction gates below.

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

After arithmetic cohomology exists, compare it directly with the analytic Xi characteristic
target and Hardy--Green residual model.  The comparison must preserve
\(K_{\mathbb R}\) parity, \(\Theta\), cup-trace, local Lefschetz terms, and the Hodge metric.
A comparison may not define the metric by transporting a form already known to be positive
exactly under RH.  CCM is not part of this comparison.

## Existing unconditional comparison and source-independent bricks

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

1. Keep \(W_{\mathrm{rat}}\) as the geometry constructing Deninger's
   character space.  On each cyclotomic component use the paper-proved
   leafwise unit-amalgamated derived sheaf as primary coefficient and prove
   its derived sections have ordinary cohomology
   \(K_*^M(F)_{\mathrm{tf}}\).  Use
   `DAC_GEOMETRIC_MW_RANK_COLLAPSE` to identify the
   nonnegative MW and ordinary geometric stalks, then place the genuinely quadratic data in
   twisted Rost--Schmid residues and the archimedean rank/signature pullback.  Prove local
   \(H^0=\mathbb Z\), \(H^1=F^\times_{\mathrm{tf}}\), and power/residue
   descent.  Treat coherent Baumslag construction of
   \(\alpha_F:X_F^M\to X_F\) and
   \(R\alpha_{F,*}\mathbb R\simeq\mathscr A^M_{F,\mathrm{geom}}\) as an
   optional geometrization.
2. Construct coherent Frobenius/Verschiebung operations and form
   Deninger's degreewise invariant sheaf
   \((\pi_*\widetilde{\mathscr A})^{\mathbb Q_{>0}}\) on the coarse
   suspension.  Prove its generic and prime-packet derived sections have
   internal amplitude \([0,1]\), without commuting cohomology with
   invariants.  Construct the separate Rost--Schmid differential and
   unital real Betti--Deligne boundary gluing.  Apply
   `DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE` to obtain amplitude
   \([0,2]\), choose a closed three-term representative, and construct the
   commuting transverse generator \(\Theta\).
3. Prove preservation of Deninger's constant \(H^0\); define \(H^1,H^2\) as cohomology of
   that complex.
4. Descend MW cup/residue/trace to cohomology and prove exact radical identities, hence
   Poincaré duality.  Derive \(H^2\simeq\mathbb R(-1)\) and \(\Theta_2=1\) from \(H^0\).
5. Prove the Flach--Morin Weil--Arakelov mapping-fiber equivalence and complementary-weight
   duality.
6. Construct the realified regulator Hilbert complex; prove closability, reduced Hodge
   decomposition, and
   `DAC_KAHLER_RIEMANN_ARITHMETIC_LEAF_REALIZATION`.  Then
   `DAC_KAHLER_RIEMANN_FLOW_PURITY` gives
   \(\Theta_1=\frac12+S\) with \(S\) skew-adjoint.
7. Prove centered power maps are unitary, extend to a strongly continuous flow, and obtain
   \(\Theta_1=\frac12+S\) with \(S\) skew-adjoint.
8. Prove source trace-class fixed-orbit localization and identify it with the already
   formalized prime--archimedean explicit-formula distribution.  Use a
   pro-nuclear limit of finite Kähler--Riemann/Leichtnam stages; a single
   finite-harmonic lamination is ruled out by
   `DAC_SINGLE_FINITE_TRANSVERSE_LAMINATION_NO_GO`.
9. Construct the regularized determinant, prove determinant uniqueness and faithful spectral
   divisor comparison with \(\xi\).
10. Derive RH from Hodge positivity plus spectral comparison.  Only afterward may any unrelated
    comparison program be opened.

## Gates

### Active arithmetic-construction gates

- [x] Rational-Witt finite-correspondence representable identified
- [x] Raw MW degree-zero comparison falsified; multiplicative derived rank quotient isolated
- [x] Full \(\mathbb A^1\)-localized coefficient falsified by target-scaling contraction
- [x] Identification of coefficient \(H^0\) with \(W_{\mathrm{rat}}\) falsified;
      rational-Witt geometry separated from coefficient cohomology
- [x] Generic derived rank-quotient universal property and \(H^0\) theorem proved on paper
- [x] Positive Steinberg cells proved to preserve \(H^0\); monic rational-Witt generators
      proved to admit surjective MW rank lifts
- [x] Real shape-cochain formality of geometric character components and real ordinary
      Milnor unit-amalgamation comparison proved on paper
- [x] Geometric nonnegative MW-to-Milnor rank collapse proved on paper; local rank quotient
      and degree-one rank-Tor gate eliminated
- [x] Real geometric coefficient amplitude \([0,1]\) over Deninger's algebraic character
      fields proved on paper
- [x] False inference from local amplitude to global amplitude retired; exact two-column
      hypercohomology theorem proved on paper
- [x] Sheaf/global-section type error isolated; Deninger's actual leafwise
      coefficient \(\mathcal R_X\) reinstated
- [x] Formal sheaf-level Kummer \(E_\infty\) amalgamation construction proved on paper
- [x] Stalkwise two-term shortcut falsified by explicit
      \(\operatorname{Tor}_1\cong\Lambda^2V\) obstruction
- [x] Relative Sullivan algebra resolving the real Milnor quotient proved on paper
- [x] Divisible-kernel plus exact \(\pi_1\) sequence proved to preserve every finite cover
- [x] One-shot infinite Sullivan realization falsified by infinite \(H^1\)
- [x] Finite-unit Sullivan realization also falsified at rank two by
      nonzero \(H_2\) of free-group \(\mathbb Q\)-completion
- [x] Basis-chosen Baumslag free-rational finite packet proved to have
      square-zero rational cohomology and divisible kernel
- [x] Any connected CDGA with only \(H^0,H^1\) proved formal; isolated
      Baumslag packet cochains match the Milnor square-zero model
- [x] Finite-unit derived base changes proved to have filtered colimit
      \(\mathbb Q\oplus V_{F,\mathbb Q}\)
- [x] Exact \(\pi_1\)-preserving correction falsified by Hopf exact sequence;
      nontrivial divisible kernel proved necessary
- [x] Pure scalar suspension cohomology proved incapable of carrying the
      zeta-zero spectrum
- [x] Prime-indexed diagonal descent retired: its factor-order relations
      have higher Koszul syzygies and it is not Deninger's source
      invariant-sheaf construction
- [x] Universal local scalar-Frobenius homotopy defect and multiplicative
      cocycle law proved on paper; Lean source written
- [ ] Optional: construct basis-independent coherent Baumslag pro-realization
      \(\alpha_F:X_F^M\to X_F\), twisted Eilenberg--Moore comparison,
      effective pro-cover descent, then integral/profinite enhancement
- [ ] Prove sheafified unit-amalgamation global-section and integral comparisons, plus
      coherent power/Rost--Schmid/Galois/archimedean-signature descent
- [ ] Construct `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`: form the
      degreewise invariant coarse sheaf, prove internal amplitude
      \([0,1]\), and prove its sheaf-level generic/prime localization
      triangle
- [ ] Construct `DAC_FINITE_CORRESPONDENCE_ANALYTIC_REALIZATION`; transfer the
      length-one Rost--Schmid complex on the arithmetic curve to
      Deninger's coarse invariant analytic sheaf
- [ ] Construct `DAC_FROBENIUS_COHERENCE_DEFECT_SPECTRUM`; prove local
      scalar homotopies exist, their obstruction classes descend, and
      their span supplies the non-scalar reduced \(H^1\)
- [ ] Construct multiplicative arithmetic-curve signature window: one real orientation in
      degree two and no higher MW signature tower
- [ ] Construct two-level Rost--Schmid derived-section localization equivalence on the
      rational-Witt flow site
- [x] Generic three-term \(H^0,H^1,H^2\) and commuting-\(\Theta\) algebra written
- [ ] Concrete three-term complex from the derived coefficient
- [x] Generic cup/Poincaré descent and exact radical criterion proved on paper
- [ ] Concrete MW residue pairing and exact radical identity
- [x] Weil--Arakelov four-term fiber algebra and complementary duality written
- [ ] Flach--Morin comparison for the concrete complex
- [x] Abstract bounded Hilbert-complex Hodge decomposition written
- [x] Dense-leaf Kähler--Riemann Hodge decomposition, Poincaré duality,
      polarization, and conformal-flow purity extracted from the primary
      source
- [ ] Construct `DAC_KAHLER_RIEMANN_ARITHMETIC_LEAF_REALIZATION`,
      including coefficient pushforward, bundle-like conformal metric,
      closed reduced differential, and harmonic-limit comparison
- [ ] Source Lefschetz trace-class localization
- [x] Single compact finite-harmonic lamination ruled out; exact
      pro-nuclear Kähler trace-tower survivor isolated
- [ ] Regularized determinant and faithful spectral-divisor comparison
- [ ] RH derivation from the constructed source

### Frozen historical comparison checklist

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
- [x] Full time-distribution Lefschetz formula proved on all smooth compactly supported
      positive-time tests
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
  `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticArchimedean.lean`.
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
  `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticSemisimpleHodge.lean`.
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

  Historical direct corpus audit against the nine sections of the program.
  **Status correction (2026-07-27):** “Lean-proved” in this table meant that
  an Xi-defined comparison model or abstract implication compiled.  It did
  not mean that source-native arithmetic cohomology or the RH-bearing
  structures were constructed.  Corrected classification:

  | Deninger obligation | Direct source theorem/module | Status |
  |---|---|---|
  | \(H^0=\mathbf C,\ H^1=\mathcal O/\Xi\mathcal O,\ H^2=\mathbf C(-1)\) | `DeningerArithmeticCochainComplex` | `[LEAN-PROVED]` Xi-defined analytic comparison model; not source-native |
  | compact-open topology and \(H^1_c\subset\mathcal H^1\subset H^1\) | `DeningerArithmeticJetProductEquivalence`, `DeningerArithmeticJetHilbertRigging` | `[LEAN-PROVED]` Xi-jet comparison rigging |
  | source Frobenius and closed dense Hilbert domain | `DeningerArithmeticTopologicalCohomology`, `DeningerArithmeticJetFrobenius` | `[LEAN-PROVED]` on Xi-defined comparison carrier |
  | cup/Poincaré derivation law | `DeningerArithmeticPoincareDuality` | `[LEAN-PROVED]` abstract law; Hodge-star constructor absent |
  | regularized determinant \(=\widehat\zeta\) | `DeningerArithmeticJetDeterminant` | `[LEAN-PROVED]` zero-indexed comparison determinant; source transport open |
  | prime-power plus archimedean Lefschetz distribution | `DeningerArithmeticLefschetz` | `[LEAN-PROVED]` Xi explicit formula; source trace identification open |
  | odd positive completed Hodge form | `DeningerArithmeticOrientedHilbertHodge` | `[LEAN-PROVED]` on `XiDivisorL2`; closed Frobenius-natural polarization requires RH |
  | source derivation of semisimple completed \(H^1\) | `DeningerArithmeticAssociatedGraded` | `[LEAN-PROVED]` Xi-jet associated graded only |
  | source Green operator, dense range, cup representation, graded Frobenius transport | `DeningerArithmeticSourceGreen` | `[LEAN-PROVED]` Xi-divisor comparison Green transport; global arithmetic Green open |
  | Frobenius naturality of source Riesz/Hodge metric factor | `[DAC_SOURCE_GREEN_PURITY]` | open mathematical core |
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
  modulo the next step, and comparison on finite source jets.  It passes its direct Lean check.

- 2026-07-26 — `[LEAN-PROVED] [DAC_SOURCE_GREEN_TRANSPORT]`.
  `DeningerArithmeticSourceGreen.lean` constructs the continuous linear map
  \[
    G:H^1_c\longrightarrow\mathcal H^1,\qquad
    G\ell=-J\,\mathcal R\ell ,
  \]
  where \(\mathcal R\) is the Fréchet--Riesz restriction map and \(J\) is the completed odd Hodge
  operator.  Lean proves:
  \[
    \operatorname{cup}(G\ell,x)=\ell(x),\qquad
    \overline{\operatorname{ran}G}=\mathcal H^1.
  \]
  On finite source jets \(G\) is the explicit oriented functional-equation reflection,
  \( (Ga)_q=\varepsilon_q a_{Rq}\), and \(G^2=-1\).  It unconditionally intertwines ordinary and
  compact-support associated-graded Frobenius because their weights add to one under functional
  equation reflection.

  This separates the open core more sharply.  Linear Green transport is not the RH-bearing step.
  The remaining factor is the anti-linear Riesz/Hodge metric identification:
  \[
    G=-J\mathcal R,\qquad
    G\Theta_c=\Theta G\ \text{unconditionally},\qquad
    J\Theta=\Theta J\Longleftrightarrow
    \mathcal R\text{ has the required flow naturality}.
  \]
  The last condition is still equivalent to RH and may not be assumed.

- 2026-07-26 — `[PRIMARY-SOURCE AUDIT] [DAC_WITT_LEAFWISE_PURITY]`.
  Deninger's 2022 formulation requires complex/\(K_{\mathbb R}\)-valued arithmetic cohomology:
  a real Weil cohomology is obstructed, while the desired degree-one anti-linear star has
  \(\star^2=-1\).  The current odd quaternionic package is therefore the correct coefficient
  category, not an accidental strengthening.

  The proved foliated model identifies the exact missing geometric mechanism.  Reduced leafwise
  cohomology obtains its positive metric from harmonic representatives, and a flow leafwise
  homotopic to an isometric flow makes the Hodge star flow-natural; the middle generator is then
  skew-symmetric.  Deninger's rational-Witt suspension for arithmetic schemes already supplies
  prime packets with periods \(\log p\), but its finite-dimensional Riemann-surface lamination,
  Fuller index \(1\), leafwise metric, and cohomological comparison remain open in the primary
  source.

  `[CONJECTURE] [DAC_WITT_LEAFWISE_PURITY]`: for
  \(X=\operatorname{Spec}\mathbb Z\), the rational-Witt suspension contains a functorial
  three-dimensional Riemann-surface lamination \(Y\) meeting every prime packet with Fuller index
  \(1\), equipped with a leafwise metric whose normalized flow is leafwise isometric, such that
  reduced leafwise cohomology compares densely and cup-isometrically with
  `DeningerArithmeticCompletedCohomology`.  The comparison must be constructed before evaluating
  the Xi divisor.  If proved, leafwise Hodge theory supplies exactly the missing Riesz naturality,
  while the existing determinant/Lefschetz comparison and closed-polarization theorem derive RH.

  Adversarial boundary: merely postulating this comparison, metric, or faithfulness is
  RH-equivalent.  A valid construction must reject shifted-Xi, Helson-twist, indefinite
  functional-equation-pair, and full-Jordan-jet fakes at chain level.  Next work is construction
  of \(Y\)'s leafwise de Rham complex and metric from rational-Witt source data, not another
  divisor-side positivity declaration.

- 2026-07-26 — `[PRIMARY-SOURCE AUDIT] [DAC_ABSOLUTE_F1_PRIME_TUBE]`.
  Connes--Consani's absolute \(\mathbb F_1\)-curve supplies a precise local object at every prime:
  \[
    E_p=\mathbb C^\times/p^{\mathbb Z}
       \simeq C_p\times\widetilde X_\infty,\qquad
    C_p=\mathbb R_{+}^{\times}/p^{\mathbb Z},
  \]
  with rectangular modulus \(i\log(p)/(2\pi)\) and canonical logarithmic form
  \(d\lambda/\lambda+i\,d\theta\).  Thus it geometrically supplies the prime longitude of length
  \(\log p\) and a \(p\)-independent phase meridian.

  It does **not** yet supply Deninger's three-dimensional arithmetic flow.  Under the local radial
  flow \([z]\mapsto[e^t z]\), the time-\(\log p\) map on \(E_p\) is the identity.  Consequently
  every phase gives a periodic orbit and
  \[
    \det\!\left(1-D\phi^{k\log p}\right)=0
  \]
  on the local tangent plane.  This violates the simple-closed-orbit hypothesis used by the
  proved leafwise Lefschetz/determinant theorem.  The rectangular Tate curve is therefore a prime
  packet or boundary torus, not by itself the required isolated prime orbit.

  The strongest positive survivor is a prime-tube formulation.  A valid global arithmetic
  dynamical system should fill \(E_p\) by a solid-torus neighborhood
  \(V_p=C_p\times D^2\), with \(C_p\) as core orbit and nontrivial return holonomy
  \(A_p:D^2\to D^2\).  To reproduce the unsigned Euler factor for every iterate it is enough that
  \[
    \det(1-DA_p^k)>0\qquad(k\geq1);
  \]
  an irrational oriented rotation is the local model.  The natural rectangular marking has
  trivial angular return, so the necessary holonomy must come from global arithmetic gluing or
  from a leaf plane not identified with the tangent plane of \(E_p\).

  `[CONJECTURE] [DAC_ABSOLUTE_F1_PRIME_TUBE]`: the absolute-\(\mathbb F_1\)/rational-Witt
  comparison admits a functorial three-dimensional subquotient \(Y\) in which each local
  \(E_p\) bounds a prime tube \(V_p\), its core is the unique selected orbit of length \(\log p\),
  all return iterates have positive Lefschetz sign, and the resulting foliation has a
  flow-natural leafwise Hodge metric.  The chain-level comparison
  \(\overline H^1_{\mathcal F}(Y)\to H^1_{\mathrm{arith}}\) must then prove cup-isometry and
  dense range without evaluating the Xi divisor.  Local Tate geometry proves the longitude,
  meridian, and complex orientation inputs; orbit selection, nondegenerate holonomy, global
  gluing, archimedean compactification, and cohomological comparison remain conjectural.

- 2026-07-26 — `[SCOPE-CORRECTION] [DIRECT-DENINGER-CHAIN]`.
  CCM is not a dependency of the arithmetic-cohomology construction; it entered only through an
  unused transitive import.  All CCM research is frozen.  The sole allowed dependency chain is
  \[
    H^0/H^1/H^2\to\cup/\operatorname{PD}\to\Theta
      \to\det/\operatorname{Lefschetz}\to\operatorname{Green}/\star\to RH.
  \]
  `DeningerArithmeticSourceGreen` closes the linear source Green transport.  The remaining
  mathematical theorem is global arithmetic descent of a positive flow-natural Hodge/Riesz
  factor.

- 2026-07-26 — `[PAPER-PROVED] [DAC_RECTANGULAR_QUATERNIONIC_HODGE]`.
  The moving rectangular local source has now been upgraded from a weight-one metric atom to the
  correct local \(K_{\mathbb R}\)-odd Hodge object.  On \(V_r=\mathbb C^2\), define
  \[
    J_r(z,w)=(-rw,z/r),\qquad
    \star_r(z,w)=J_r(\overline z,\overline w),\qquad
    \|(z,w)\|_r^2=\frac{|z|^2}{r}+r|w|^2.
  \]
  Then \(\star_r\) is anti-linear, \(\star_r^2=-1\), and it preserves the positive energy.
  The moving-modulus map \(A_q(z,w)=(qz,w)\) intertwines
  \(\star_r\) with \(\star_{qr}\) and scales energy by \(q\).  Hence
  \(U_q=q^{-1/2}A_q\) is a unitary Hodge intertwiner and the centered exponent
  \(1/2\) is forced by the source metric law.  No Xi divisor or RH premise occurs.

  Paper proof:
  `docs/drafts/pipeline/2-fully-proven/deninger-rectangular-quaternionic-hodge.md`.
  Lean batch:
  `DeningerArithmeticRectangularHalfDensity.lean` and
  `DeningerArithmeticRectangularQuaternionicHodge.lean`, pending one direct low-load check.

  This supersedes `[DAC_ABSOLUTE_F1_PRIME_TUBE]` as active local conjecture: local positivity and
  local centered Hodge naturality are no longer conjectural.  Prime holonomy remains a possible
  geometric realization, while the active cohomological source is
  `[DAC_POLARIZED_MILNOR_WITT_FLOW_REALIZATION]`.  Deninger's 2025 sheafification result shows that ordinary
  finite-flat/\(h\)/\(qfh\) descent recovers \(W_{\mathrm{rat}}\), so it cannot restore the
  missing Steinberg relation.  Exact open core is stronger additive/Steinberg descent of these
  local quaternionic atoms plus dense cup-isometric comparison with completed arithmetic
  cohomology.

- 2026-07-26 — `[DIRECT SOURCE H1] [DAC_PRIME_GAMMA_PACKET_COHOMOLOGY]`.
  The prime--Gamma source has now been organized into a divisor-free algebraic middle
  cohomology.  In the strict absolute Euler half-plane, the von-Mangoldt plus archimedean
  relative trace defines a divided-difference cup kernel.  Finite lower and upper Cauchy packets,
  quotiented by the exact left and right radicals, give
  \[
    H^1_{\mathrm{PG},-}\oplus H^1_{\mathrm{PG},+}.
  \]
  The descended cross-pairing is separating on both sides, and its canonical alternating
  extension is nondegenerate.  These constructions and proofs are in
  `DeningerPrimeGammaPacketCohomology.lean`,
  `DeningerPrimeGammaReflectedDiagonal.lean`, and
  `DeningerPrimeGammaPoincareDuality.lean`.  Xi data occur only in a later comparison theorem,
  not in the definition of the source packet quotient.

  `[PAPER-PROVED] [DAC_EULER_SECTOR_HODGE_OBSTRUCTION]`: this source core supplies Poincare
  duality but not the Hodge diagonal.  Its lower and upper parameter sectors satisfy
  \[
    \Im z<-\frac12,\qquad \Im w>\frac12.
  \]
  Canonical conjugation sends a lower atom \(c/(a-z)\) to the upper atom
  \(c/(a-\overline z)\); for \(c\ne0\) these are distinct.  Therefore the positive Hodge metric
  cannot be obtained by merely identifying the two absolute-convergence packet sectors.
  Full proof:
  `docs/drafts/pipeline/2-fully-proven/deninger-prime-gamma-euler-sector-hodge-obstruction.md`;
  Lean batch: `DeningerPrimeGammaEulerSectorObstruction.lean`, pending the shared low-load check.

  This sharpens `[DAC_SOURCE_GREEN_PURITY]`: next object must extend the packet theory across the
  critical strip by source-controlled arithmetic continuation or by the rational-Witt
  correspondence geometry.  Positivity after Xi-divisor evaluation is a comparison target, not
  an allowed construction.

- 2026-07-26 — `[LITERATURE-CORRECTED CONJECTURE]
  [DAC_POLARIZED_MILNOR_WITT_FLOW_REALIZATION]`.
  Integral Milnor--Witt motivic cohomology over \(\operatorname{Spec}\mathbb Z\) is no longer an
  invented source category: Kolderup--Röndigs--Østvær construct its spectrum as
  \[
    \widetilde{\mathrm M}\mathbb Z
      =\mathrm M\mathbb Z\times_{\mathrm M\mathbb Z/2}\mathrm W\mathbb Z
  \]
  over arithmetic Dedekind bases.  Very effective hermitian \(K\)-theory
  \(\mathrm{ko}_{\mathbb Z}\) exists integrally, and Shin proves normed structure over qcqs
  bases.  Exact new frontier is a Deninger flow realization of these established motivic
  objects, compatible with ramified power-map framed transfers and prime--Gamma completion.

  Hostile audit also retires the claim that the canonical degree-\(p\) Milnor--Witt transfer is
  already positive.  Its real quadratic multiplicity \(p_\epsilon\) has rank \(p\) but signature
  \(0\) for \(p=2\) and \(1\) for odd \(p\), hence is indefinite for every prime.  Strongest
  survivor separates structures:
  \[
    \text{MW/ko transfer}\Rightarrow\text{Steinberg descent + Poincare pairing},
    \qquad
    \Gamma_\infty\text{ polarization}\Rightarrow\text{positive Hodge metric}.
  \]
  The archimedean boundary must construct \(J_\infty^2=-1\), prove
  \(\operatorname{tr}(x\cup J_\infty x)>0\), and make centered power transfers unitary before
  any Xi-divisor comparison.  Active construction card:
  `deninger-milnor-witt-hodge-realization`; exact failed route and survivor:
  `deninger-bare-milnor-witt-transfer-positivity`.

- 2026-07-26 — `[PAPER-PROVED SOURCE TRANSFER PACKAGE]`.
  The direct Deninger chain now has four additional source theorems, none using Xi zeros:

  1. power correspondences act through the inhomogeneous bar coboundaries \(d^0,d^1,d^2\);
     associativity proves \(d^1d^0=d^2d^1=0\), and the good degree-two truncation
     \(C^2=\ker d^2\) avoids spurious \(H^2\);
  2. composable monic power-map cotangent presentations reduce by determinant-one elementary
     transformations to one contractible block plus the composite derivative, proving
     determinant-orientation coherence;
  3. Poincare adjunction, Hodge naturality, and \(F_nV_n=n\,\mathrm{id}\) force
     \(\|V_nx\|^2=n\|x\|^2\), so \(U_n=n^{-1/2}V_n\) is isometric and the centered
     \(\tfrac12\)-shift is intrinsic;
  4. a unital real \(GW\)-character strictly positive on the hyperbolic class is necessarily
     rank, hence sends the Milnor--Witt degree \(n_\epsilon\) to \(n\).
  5. more strongly, hyperbolic localization \(GW[h^{-1}]\) constructs the rank channel
     algebraically: \((1-\epsilon)h=0\) forces \(\epsilon=1\), so
     \(GW_{\mathbb R}[h^{-1}]\simeq\mathbb Z[1/2]\) and \(n_\epsilon=n\).
  6. a unitary centered transfer commuting with the source differential automatically commutes
     with its adjoint, the BRST--Hodge Laplacian, and the harmonic sector.

  Paper proofs:
  `deninger-power-bar-cochain`, `deninger-power-map-orientation-coherence`,
  `deninger-polarized-transfer-half-density`, and
  `deninger-gamma-rank-character-rigidity`, together with
  `deninger-hyperbolic-localization-rank-collapse` and
  `deninger-unitary-brst-hodge-descent`.  Direct Lean checks pass for all six source statements.

  The remaining transfer-layer theorem is now precise: construct the finite
  MW/\(\mathrm{ko}\)--Gamma coefficient packet, its coherently framed power action, and a
  positive odd Hilbert realization of the now-explicit hyperbolically localized rank boundary.
  The subsequent open purity theorem is compatibility with the incidence differential,
  moving-Hodge naturality, and cofinal harmonic convergence, not another divisor-side Hodge
  declaration.

  The Gamma-rank realization and its bar-skeleton compatibility are now constructed rather than
  conjectured.  `DeningerArithmeticGammaRankRegular.lean` gives the dense algebraic core,
  \(\ell^2(G\sqcup G)\) completion, antiunitary \(J^2=-1\), alternating cup, strict
  cup--Hodge positivity, unitary centered power action, and exact commutation with
  \(Q^0,Q^1,Q^2\), including preservation of the good degree-two cocycle kernel.  Remaining
  incidence gate is specifically the closed \(J\)-stability of the MW/Steinberg relation
  subspace and coherent framed transfer, followed by cofinal harmonic convergence.

- 2026-07-26 — `[SCOPE CORRECTION] [DIRECT COEFFICIENT COMPLEX]`.
  The Gamma/CCM support branches are frozen.  They do not construct Deninger's missing
  arithmetic cohomology and no further theorem in either branch counts toward this card.

  Deninger's own exact gap is \(R\alpha_*\mathscr G\) on the rational-Witt dynamical
  approximation.  The active conjecture is now
  `[DAC_ROST_SCHMID_FLOW_REALIZATION]` on
  `deninger-rost-schmid-flow-realization`: derive the coefficient complex from the forgetful
  functor from Milnor--Witt to ordinary finite correspondences, resolve it by arithmetic
  Rost--Schmid residues, add the archimedean boundary, construct the three-term leafwise
  complex, and make transverse flow act on it by a commuting chain endomorphism.

  `[CORRECTION] [DAC_RESIDUE_FLOW_TOTALIZATION]`.
  `DeningerArithmeticResidueFlowTotalization.lean` formalizes the three-term mapping fiber
  of a chain endomorphism on a two-term complex:
  \[
    A^0\longrightarrow A^1\oplus A^0\longrightarrow A^1,
    \qquad
    d^0(a)=(\partial a,\nabla^0a),\quad
    d^1(b,a)=\nabla^1b-\partial a.
  \]
  It proves \(d^1d^0=0\) from
  \(\nabla^1\partial=\partial\nabla^0\), identifies \(H^0\)-cocycles,
  \(H^1\)-cocycles and coboundaries, and proves
  \(\operatorname{im}d^1=\operatorname{im}\nabla^1+
  \operatorname{im}\partial\), giving the exact \(H^2\) quotient.  Direct Lean check passes
  cleanly.  It does **not** construct dynamical \(H^0,H^1,H^2\): transverse flow is an
  endomorphism of leafwise cochains, not a cohomological differential.

  `[OPEN CORE]` Construct the actual archimedean Milnor--Witt/Rost--Schmid coefficient sheaf
  and its three-term leafwise complex, then construct the transverse flow chain endomorphism.

- 2026-07-26 — `[LITERATURE] [DAC_RS_FROBENIUS_CHAIN_MAP]`.
  Déglise--Feld--Jin Proposition 1.4.6 proves that proper pushforward commutes with the
  Rost--Schmid differential.  Since every monic power map is finite, its Frobenius pushforward
  is already a source chain map; Proposition 1.4.1 gives the multiplicative composition law.
  Their smoothable-lci Gysin map exists on homology, while cycle-level
  \(\infty\)-categorical refinement is explicitly future work.  The next direct construction is
  therefore coherent chain-level Verschiebung for the ramified power maps, followed by its
  \(\mathbb Q_{>0}\)-suspension and archimedean boundary—not another coefficient positivity
  model.

- 2026-07-26 — `[LITERATURE] [DAC_RS_GYSIN_COHERENCE]`.
  The May 2026 sequel *Homotopy coherent Gysin functoriality* closes that stated future-work
  gap.  It constructs a strict simplicial contravariant Gysin functor and applies it to
  Rost--Schmid MW-homodules over noetherian excellent bases.  Therefore the ramified power-map
  pullbacks \(V_n=\pi_n^*\) on \(\mathbb A^1_{\mathbb Z}\) exist with all higher composition
  coherences.  Together with proper pushforward, finite-place Frobenius/Verschiebung
  functoriality is source-available.

  `[LITERATURE] [DAC_MW_ORDINARY_RANK_BRIDGE]`.
  Kolderup--Röndigs--Østvær construct integral Milnor--Witt motivic cohomology over arithmetic
  bases as
  \[
    \widetilde{\mathsf M\mathbb Z}
    =
    \mathsf M\mathbb Z
    \mathop{\times}^{h}_{\mathsf M\mathbb Z/2}
    \mathsf W\mathbb Z.
  \]
  The canonical projection to \(\mathsf M\mathbb Z\) is rank on degree-zero quadratic
  coefficients and therefore sends \(n_\epsilon\) to \(n\).  This comparison is finite-place
  algebra, not an archimedean positivity theorem.

  `[OPEN CORE]` Compare the ordinary projection of this derived MW coefficient system with
  Deninger's finite-correspondence/rational-Witt site while retaining the Witt homotopy fiber
  as the duality channel; descend the \(\mathbb Q_{>0}\)-localization to the leafwise flow
  connection; then construct the archimedean extension and its positive flow-natural Hodge
  operator.

- 2026-07-26 — `[LITERATURE] [DAC_WEIL_ARAKELOV_DYNAMICAL_LIFT]`.
  Flach--Morin give the precise direct compatibility that the missing dynamical complex must
  satisfy:
  \[
    R\Gamma_{\mathrm{ar},c}(X,\widetilde{\mathbb C}(n))
    \simeq
    \operatorname{Fib}\!\left(
      \Theta-n:R\Gamma_{\mathrm{dyn},c}(X)\to
      R\Gamma_{\mathrm{dyn},c}(X)\right).
  \]
  Their left side is constructed from the mapping fiber of the motivic-to-Deligne regulator,
  followed by the Weil--Arakelov two-copy extension with acyclic cup-\(\theta\).  This exposes
  the correct roles: a three-term leafwise complex supplies dynamical degrees \(0,1,2\);
  \(\Theta\) is a commuting endomorphism; its Weil--Arakelov specialization is a four-term
  mapping fiber.

  `[LEAN-PROVED] [DAC_WEIL_ARAKELOV_FIBER_ALGEBRA]`.
  `DeningerArithmeticWeilArakelovFiber.lean` formalizes that four-term fiber and proves both
  consecutive differential compositions vanish, together with endpoint and transgression
  formulas.  Direct Lean check passes.  Active construction is now
  `deninger-weil-arakelov-dynamical-lift`: build the Milnor--Witt regulator fiber on the
  rational-Witt flow space and prove the Flach--Morin equivalence, before Hodge or determinant
  comparison.

- 2026-07-26 — `[SUPERSEDED LOCAL-RANK COEFFICIENT CORRECTION]`
  `[DAC_DERIVED_MW_RATIONAL_WITT_COEFFICIENT]`.
  Raw MW correspondences fail degree zero: a rank-zero, nonzero-signature coefficient on
  \(\Gamma_1\) survives the reduced correspondence quotient.  The earlier module cofiber is
  also insufficient because it has no automatic \(E_\infty\) multiplication.  The corrected
  rank step is the commutative-algebra homotopy pushout
  \[
    M_{\mathrm{St}}
      \mathop{\otimes}^{\mathbb L}_{
        \operatorname{Free}_{E_\infty}^{+}
        (\tau_{\le0}\operatorname{Fib}(r))}
    \mathbbm1 .
  \]
  Here \(M_{\mathrm{St}}\) is obtained from the non-\(\mathbb A^1\)-localized
  bar--residue envelope by attaching only the specified degree-two Steinberg cells.  Full
  Suslin/\(\mathbb A^1\)-localization is forbidden because target scaling contracts the
  reduced rational-Witt coordinate to the killed zero section.  The two-stage construction
  uses no multiplicative section of rank, kills the low rank kernel derivatively, and retains
  higher symmetric-power/Tor correction.  Positive fiber
  \(=\tau_{\ge1}\operatorname{Fib}(r)\) is no longer assumed without a flatness theorem.
  Deninger's concrete cohomology is now fixed as derived global sections of its
  \(\mathbb Q_{>0}\)-localized descent after unital real Betti--Deligne boundary gluing; the
  required amplitude \([0,2]\) is an explicit source theorem, not a claim that the current
  rational-Witt partition is already a smooth two-dimensional foliation.

- 2026-07-26 — `[SUPERSEDED THIRD COEFFICIENT CORRECTION]`
  `[DAC_UNIT_AMALGAMATED_MW_COCHAIN_COEFFICIENT]`.
  Deninger's primary text separates the rational-Witt structure sheaf constructing the
  approximation from the relevant complex \(R\alpha_*\mathscr G\) on that approximation.
  Kucharczyk--Scholze require corrected local cohomology
  \(H^q=K_q^M(F)_{\mathrm{tf}}\), hence \(H^0=\mathbb Z\), while Deninger's global
  \(H^0\) is one-dimensional.  The earlier target
  \(\pi_0R\alpha_*\mathscr G=W_{\mathrm{rat}}\) was therefore a geometry/coefficient
  conflation and is retired.

  Current coefficient on a character component is
  \[
    \mathcal C_F^M
      =C^*(X_F,\mathbb Z)
        \otimes_{\operatorname{Free}_{E_\infty}
          (\Sigma_{\mathrm{ar}}H(F^\times/\mu_\infty))}^{\mathbb L}
        \mathcal K_F^M,
    \qquad
    \mathcal C_F^{MW}
      =C^*(X_F,\mathbb Z)
        \otimes_{\operatorname{Free}_{E_\infty}
          (\Sigma_{\mathrm{ar}}H(F^\times/\mu_\infty))}^{\mathbb L}
        \mathcal K_F^{MW}.
  \]
  The full motivic symbol algebra supplies Steinberg plus all higher syzygies without
  \(\mathbb A^1\)-localizing the rational-Witt coordinate.  At this stage a
  relative multiplicative rank quotient and degree-one Tor gate were still
  proposed.  Both are eliminated by the fourth correction below.

- 2026-07-26 — `[FOURTH COEFFICIENT CORRECTION]`
  `[DAC_GEOMETRIC_MW_RANK_COLLAPSE]`.
  Déglise's Milnor--Witt fundamental square gives
  \(K_q^{MW}(F)\cong K_q^M(F)\) for every \(q\geq0\) when \(F\) is algebraically closed:
  every unit is a square, \(GW(F)\cong\mathbb Z\), and the positive fundamental-ideal
  terms vanish.  Hence the local geometric map
  \(\mathcal C_F^{MW}\to\mathcal C_F^M\) is an equivalence and its derived rank quotient is
  trivial.  More generally cyclotomic fields are nonreal, so the same comparison holds
  after realification.

  Quadratic information is therefore not an extra nonnegative geometric-stalk summand.
  It belongs to twisted Rost--Schmid residue/Gysin maps before realification and to the
  real-signature term in the archimedean comparison.  Active construction is now the
  homotopy pullback
  \[
    \mathscr A_{\mathrm{ar},\mathbb R}
    =
    \mathscr A_{\mathrm{cyc},\mathbb R}
    \mathop{\times}^{h}_{\mathscr A_{\mathbb C,\mathbb R}}
    \mathscr A_{\infty,\mathbb R}^{\mathrm{sig}},
  \]
  followed by coherent power localization and Deninger's suspension.  Exact open gate is
  construction and low-degree computation of this Rost--Schmid/Galois/signature pullback,
  not local rank-Tor control.

- 2026-07-26 — `[SUPERSEDED FIFTH-CORRECTION AMPLITUDE MECHANISM]`
  `[DAC_ARITHMETIC_ROST_SCHMID_SIGNATURE_RESOLUTION]`.
  The signature-window constraint survives.  The claim that its two columns
  are resolutions of two-term homotopy sheaves is superseded by the seventh
  correction and its explicit stalk-Tor obstruction.
  The real geometric character coefficient is now proved to have amplitude
  \([0,1]\): for every algebraic \(F/\mathbb Q\),
  \(K_q^M(F)\otimes\mathbb R=0\) for \(q\ge2\).  This does not by itself bound
  derived global sections on Deninger's infinite-dimensional space.  The
  failed implication is recorded in
  `deninger-local-amplitude-implies-global-amplitude`.

  Déglise--Feld--Jin's Theorem 4.4.20 also shows that full arithmetic
  Milnor--Witt theory has a real-place \(\mathbb Z^r\) survivor in every
  weight \(q>1\).  Therefore the untruncated signature pullback written in
  the fourth correction is too large.  Replace it by its multiplicative
  arithmetic-curve Postnikov window:
  \[
    \mathscr A_{\mathrm{ar},\mathbb R}
    =
    \tau_{\le2}^{\mathrm{arith}}\!\left(
      \mathscr A_{\mathrm{cyc},\mathbb R}
      \mathop{\times}^{h}_{\mathscr A_{\mathbb C,\mathbb R}}
      \mathscr A_{\infty,\mathbb R}^{\mathrm{sig}}
    \right).
  \]
  This retains the connected rank unit, geometric degree-one character
  classes, and exactly one real orientation
  \(i_{\infty,*}\mathbb R(-1)[-2]\), while excluding higher signature
  weights from Deninger's weight-one theory.

  `[PAPER-PROVED] [DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE]`.
  If the degree-zero and degree-one coefficient sheaves admit exact
  global-section-acyclic Rost--Schmid resolutions of length one and the real
  orientation sheaf is acyclic, derived global sections are represented by
  \[
    \Gamma\mathscr G^{0,0}
    \longrightarrow
    \Gamma\mathscr G^{1,0}\oplus\Gamma\mathscr G^{0,1}
    \longrightarrow
    \Gamma\mathscr G^{1,1}\oplus\mathbb R(-1)
  \]
  and have amplitude \([0,2]\).  Exact open core is now concrete:
  construct those sheaves and prove their acyclicity on the actual
  rational-Witt flow site; construct the multiplicative signature window;
  then prove residue/signature reciprocity and self-duality.  No CCM object
  occurs in this dependency chain.

- 2026-07-26 — `[SIXTH COEFFICIENT CORRECTION]`
  `[DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE]`.
  Deninger already defines the leafwise coefficient sheaf
  \[
    \mathcal R_X=(\pi_*\mathcal R_{\widetilde X})^{\mathbb Q_{>0}}
  \]
  and his cohomology as
  \(H^\bullet_{\mathcal F}(X)=H^\bullet(X,\mathcal R_X)\).
  The previously written character algebra
  \(C^*_{\mathrm{sh}}(X_F;\mathbb R)
  \otimes_{\mathcal P_F}^{\mathbb L}\mathcal K_F^M\)
  is a derived-global-section comparison object, not a sheaf or stalk.
  Using it directly under \(Rj_*^G\) was a type error, now retired in
  `deninger-chart-cochains-as-coefficient-sheaf`.

  The corrected construction takes place in commutative algebra objects in
  the derived category of sheaves over \(\mathcal R_X\).  The Kummer map
  adjoints to
  \(H\mathscr V_F[-1]\to\mathcal R_{X_F}\), hence gives
  \[
    \mathscr A^M_{F,\mathrm{geom}}
    =
    \mathcal R_{X_F}
      \mathop{\otimes}^{\mathbb L}_{\mathscr P_F}
    \underline{\mathcal K}^M_{F,\mathbb R}.
  \]
  Existence and functorial universal property are paper-proved.  Exact new
  comparison gate is
  `[DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON]`: prove that derived global
  sections of this sheaf equal the chartwise algebra already handled by
  shape formality.  This requires a projection formula, acyclic relative
  cells, or monoidal hypercover descent; it cannot be inferred from the
  global cochain calculation alone.

- 2026-07-26 — `[SEVENTH COEFFICIENT CORRECTION]`
  `[DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION]`.
  The sheafified Kummer pushout exists, but chartwise two-term amplitude
  cannot be transferred to its stalks.  A Kummer class is null after taking
  a stalk.  With \(E=\Lambda(V)\) and
  \(K=E/\Lambda^{\ge2}V=\mathbb R\oplus V\), the stalk is controlled by
  augmentation base change and
  \[
    \operatorname{Tor}_1^E(\mathbb R,K)
    \cong
    \Lambda^2V.
  \]
  The proof is the long exact Tor sequence for
  \(0\to\Lambda^{\ge2}V\to E\to K\to0\).  Thus the prior fifth-correction
  language about two-term homotopy sheaves is retired.

  The positive survivor is a two-level **derived-section** localization
  theorem:
  \[
    R\Gamma(X_W,\mathscr A_{\mathrm{arith}})
    \simeq
    \operatorname{Tot}\!\left(
      G^{0,\bullet}\xrightarrow{\partial}G^{1,\bullet};
      \mathbb R(-1)[-2]
    \right),
  \]
  where the generic and prime-packet derived-section columns have amplitude
  \([0,1]\).  The already paper-proved
  `DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE` then yields a three-term complex
  even though \(R\alpha_*\mathscr G\) may have complicated stalks.  Exact
  open gate is the arithmetic localization/hypercover equivalence, not a
  fictitious stalkwise Gersten resolution.

- 2026-07-26 — `[EIGHTH COEFFICIENT CORRECTION]`
  `[DAC_RELATIVE_SULLIVAN_MILNOR_RESOLUTION]`,
  `[DAC_RELATIVE_MILNOR_CHARACTER_REALIZATION]`.
  The sheafified unit-amalgamated algebra cannot by itself construct the
  missing map \(\alpha_F:X_F^M\to X_F\).  The primary local coefficient is
  now restored to Deninger's form
  \[
    \mathscr A_{F,\mathbb R}^{\mathrm{geom}}
      =R\alpha_{F,*}\mathbb R.
  \]
  The real algebraic model for \(\alpha_F\) is paper-proved: the quotient
  \(\Lambda(V_F)\twoheadrightarrow
  K_*^M(F)\otimes\mathbb R=\mathbb R\oplus V_F\) has a functorial relative
  Sullivan resolution.  Its degree-one relative generators kill the
  degree-two cup products and its later generators kill every syzygy.

  Ordinary Sullivan realization is falsified, including at finite rank
  two.  `DAC_BAUMSLAG_FREE_RATIONAL_MILNOR_PACKET` replaces it: a
  basis-chosen finite packet has square-zero rational cohomology, formal
  connected CDGA cochains, and a genuinely divisible fiber, so its
  finite-cover category is unchanged.  Exact open geometric core is
  basis-independent homotopy-coherent assembly of these packets, twisted
  Eilenberg--Moore comparison, and effective pro-cover descent, followed by
  an integral/profinite, residue-, Galois-, and power-compatible enhancement.
  The leafwise unit-amalgamated sheaf is retained only as a comparison
  candidate for \(R\alpha_{F,*}\mathbb R\).  Proving this pushforward
  comparison is now the first bridge from local Milnor geometry to global
  arithmetic descent.

- 2026-07-26 — `[NINTH COEFFICIENT CORRECTION]`
  `[DAC_BAUMSLAG_FREE_RATIONAL_MILNOR_PACKET]`,
  `[DAC_BAUMSLAG_MILNOR_PRO_REALIZATION]`.
  Ordinary Sullivan realization does not construct the Milnor character
  space.  Zhou's theorem rules out the one-shot infinite model, and the
  obstruction persists at rank two: Sullivan/Bousfield--Kan
  \(\mathbb Q\)-completion of a free group has nonzero \(H_2\).

  Baumslag rationalization is the positive survivor.  For every
  basis-chosen finite unit space \(U\), the free rational group packet
  \[
    B\operatorname{Bau}(F_{\dim U})\longrightarrow B(U^\vee)
  \]
  has rational cohomology
  \(\mathbb Q\oplus U[-1]\), formal connected CDGA cochains, and connected
  uniquely divisible kernel.  Its fiberwise pullback over \(X_F\)
  therefore preserves all finite covers at that stage.  Hopf's exact
  sequence separately proves that this nontrivial divisible kernel is
  necessary: exact \(\pi_1\) preservation would force nonzero \(H^2\).

  Exact open local core is no longer existence of an isolated finite
  packet.  It is basis-independent homotopy-coherent assembly under field,
  Galois, and power maps; twisted Eilenberg--Moore comparison for the
  fiberwise pullbacks; continuous pro-cochain and effective finite-cover
  descent; then integral/profinite and MW enhancement.  Only after these
  gates can \(R\alpha_{F,*}\mathbb R\) enter arithmetic
  Rost--Schmid/signature descent.

- 2026-07-26 — `[TENTH COEFFICIENT CORRECTION]`
  `[DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE]`.
  The eighth and ninth corrections overconstrained the construction by
  making a true Milnor character space and
  \(R\alpha_{F,*}\mathbb R\) prerequisites.  Deninger's primary text,
  introduction pp. 4--5, says that if a true space maps to the
  rational-Witt approximation then its cohomology is computed by a derived
  pushforward, but that working on the approximation instead amounts
  directly to finding the relevant complexes of sheaves on it.

  Therefore the primary local coefficient is the genuine derived leafwise
  sheaf
  \[
    \mathscr A^M_{F,\mathrm{geom}}
    =
    \mathcal R_{X_F}
    \mathop{\otimes}^{\mathbb L}_{\mathscr P_F}
    \underline{\mathcal K}^M_{F,\mathbb R}.
  \]
  Its existence and universal property are paper-proved.  Its
  derived-global-section, Galois, power, and Rost--Schmid comparisons
  remain open.  The Baumslag packet program remains a valid optional
  geometrization theorem
  \(R\alpha_{F,*}\mathbb R\simeq\mathscr A^M_{F,\mathrm{geom}}\), but it
  no longer blocks global arithmetic descent, cup/trace, Hodge theory, or
  the zeta comparison.  Stalk Tor remains real and is handled by the
  two-column derived-section localization theorem, not by asserting
  two-term homotopy sheaves.

- 2026-07-26 — `[ELEVENTH SOURCE CORRECTION]`
  `[DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT]`.
  The prime-indexed diagonal descent proposal is retired.  Deninger's
  Definition 10.1 forms
  \[
    \mathscr A_X^\bullet
    =
    (\pi_*\widetilde{\mathscr A}^{\bullet})^{\mathbb Q_{>0}}
  \]
  degreewise on the coarse quotient and only then takes derived global
  sections.  Section 12 uses
  \(H^1(\widetilde X,Q_0(1))^{\widetilde G}\) as a replacement regulator
  target precisely because the action is not properly discontinuous; it
  does not identify this group with the sought spectral \(H^1\).

  The universal identity
  \[
    \Delta_{mn}=T_m\Delta_n+\Delta_mF_n
  \]
  is paper-proved, and its two factor orders expose the standard
  prime--prime Koszul syzygy.  Therefore a two-term prime relation module
  is not a source-defined resolution of the quotient.  The positive
  survivor keeps nonproper descent inside the hypercohomology of
  Deninger's invariant sheaf and uses prime Rost--Schmid localization as
  the sole horizontal codimension-one differential.  The first global
  gate is now exact: prove generic and prime-packet internal amplitude
  \([0,1]\), their localization triangle, closed reduced differentials,
  and the local \(\log p\) trace.

- 2026-07-26 — `[TWELFTH SOURCE CORRECTION]`
  `[DAC_NAIVE_ADELIC_L2_KUMMER_COMPLETION_NO_GO]`,
  `[DAC_ADELIC_L1_L2_ROST_SCHMID_HODGE_COEFFICIENT]`.
  Allcock--Vaaler's place-space realization gives a canonical source
  form on logarithmic Kummer classes,
  \[
    B_2(\alpha,\beta)
      =\int_Y\log\|\alpha\|_y\log\|\beta\|_y\,d\lambda .
  \]
  It is positive and field-independent.  Under Deninger's
  \(\mathbb R(s)\)-twist the power map scales this metric by
  \(n^{2-2s}\), so \(s=\tfrac12\) is the unique weight-one
  normalization.  Its centered action is nevertheless the identity.

  Bare \(L^2\) is not the arithmetic coefficient: Allcock--Vaaler prove
  that the product-formula Kummer functions are dense in \(L^2(Y)\).
  Hence the product-formula integral has no nonzero continuous
  extension to the \(L^2\)-completion.  The corrected coefficient uses
  the mixed topology
  \[
    E_{\mathrm{Kum}}
      =\overline{\mathcal F}^{\,\|\cdot\|_1+\|\cdot\|_2}
      \subset L^1(Y)\cap L^2(Y).
  \]
  Its \(L^1\) channel retains product formula, real boundary, and
  Rost--Schmid residues; its \(L^2\) channel supplies local positive
  energy.  Nontrivial centered spectrum must lie in the descended
  Frobenius coherence-defect quotient.  Exact next gate is sheafifying
  this mixed coefficient on the standard finite-correspondence category and
  proving MW residue, norm, reduced-cohomology, and Kähler-Hodge
  compatibility.  No CCM/Gamma object occurs in this route.

- 2026-07-26 — `[THIRTEENTH SOURCE CORRECTION]`
  `[DAC_WRAT_CORRESPONDENCE_TOPOS_REALIZATION_NO_GO]`,
  `[DAC_FINITE_CORRESPONDENCE_ANALYTIC_REALIZATION]`.
  Deninger's 2025 Theorem 5.1 proves
  \[
    W_{\mathrm{rat}}(\mathcal O(X))
      \cong
    \underline{\operatorname{Corr}}(X,\mathbb A^1)
  \]
  on normal Noetherian affine schemes.  Proposition 5.2 identifies
  \(F_n,V_n\) with pushforward and pullback along \(x\mapsto x^n\).
  This represents one coefficient in the standard
  Suslin--Voevodsky finite-correspondence category; it does not define
  a new Witt correspondence category, topology, or dimension-one
  topos.  That earlier language is retired.

  The corrected realization gate starts with
  \(\mathbb Z_{\mathrm{tr}}(\mathbb A^1)/
    \mathbb Z_{\mathrm{tr}}(0)\) in the standard correspondence
  category over the regular arithmetic curve.  Arithmetic dimension
  one comes from the base Rost--Schmid complex.  Exact open work is:
  lift ordinary correspondences to the framed/MW determinant
  orientation, construct the character-evaluation analytic
  realization on Deninger's coarse invariant sheaf, and prove mixed
  \(L^1/L^2\), residue, derived-section, amplitude, and regulator
  compatibility.

- 2026-07-26 — `[FOURTEENTH SOURCE CONSTRUCTION]`
  `[DAC_ADELIC_PLACE_AVERAGE_RESIDUE]`,
  `[DAC_ADELIC_KUMMER_GELFAND_TRIPLE]`,
  `[DAC_ADELIC_KUMMER_NUCLEAR_TEST_SCALE]`.
  On the Allcock--Vaaler place space, integration over \(Y(K,v)\)
  recovers the exact normalized \(K_1\) residue:
  \[
    \int_{Y(K,v)}\log\|\alpha\|_y\,d\lambda
      =-\frac{\operatorname{ord}_v(\alpha)}
              {[K:\mathbb Q]}\log Nv.
  \]
  Fili--Miner's normalized field norms are contractions in \(L^1\)
  and \(L^2\).  The mixed completion therefore gives the canonical
  rigged Hilbert triple
  \[
    E_{\mathrm{Kum}}\hookrightarrow L^2(Y,\lambda)
      \hookrightarrow E_{\mathrm{Kum}}'.
  \]
  Closing the real Kummer span inside
  \(C_c^{\mathrm{lc}}(Y)\) adds a complete nuclear LF test layer and
  yields the source scale
  \[
    \mathcal S_{\mathrm{Kum}}\subset E_{\mathrm{Kum}}\subset L^2
      \subset E_{\mathrm{Kum}}'\subset\mathcal S_{\mathrm{Kum}}'.
  \]
  This constructs local residue, product-formula, positive-energy, and
  distribution topologies without CCM or zeta zeros.  Remaining gates
  are extension to the full Tate--Milnor/MW sheaf, global
  invariant-sheaf localization, Kähler positivity on the defect
  quotient, and trace-class estimates for the flow.

- 2026-07-26 — `[FIFTEENTH SOURCE CONSTRUCTION]`
  `[DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT]`.
  Product formula, finiteness of the ideal class group, and Dirichlet's
  unit theorem give the exact real-linearized Arakelov divisor row
  \[
    0\to(K^\times/\mu_K)\otimes\mathbb R
      \to\operatorname{Div}_{\mathrm{Ar}}(K)_{\mathbb R}
      \xrightarrow{\deg}\mathbb R\to0.
  \]
  For \(K=\mathbb Q\), the finite coordinate space is the real
  finitely supported prime divisor space, the archimedean coordinate
  compensates \(\sum_p d_p\log p\), and kernel equals principal range.
  The abstract coordinate exactness is written unconditionally in
  Lean.  This constructs the algebraic \(\mathbb R(-1)\) endpoint; the
  remaining endpoint gate is analytic comparison with Deninger's
  invariant-sheaf totalization.

- 2026-07-26 — `[SIXTEENTH SOURCE CORRECTION]`
  `[DAC_COARSE_STACK_EXACTNESS_SCALAR_SPECTRUM_NO_GO]`,
  `[DAC_COARSE_STACK_COMPARISON_DEFECT]`.
  For the quotient-stack-to-coarse-space map
  \(c:[\widetilde X/\mathbb Q_{>0}]\to X\), Deninger's coefficient is
  the underived invariant sheaf
  \(c_*\widetilde{\mathscr A}\).  If the canonical comparison
  \[
    c_*\widetilde{\mathscr A}\to Rc_*\widetilde{\mathscr A}
  \]
  were a quasi-isomorphism, locally scalar Tate cohomology would
  remain scalar after coarse descent and could not realize the zeta
  spectrum.  Hence the canonical comparison cone
  \[
    \mathscr D_c
      =\operatorname{Cone}(c_*\widetilde{\mathscr A}
          \to Rc_*\widetilde{\mathscr A})[-1]
  \]
  is a mandatory nonzero source object.  The universal Frobenius
  homotopy cocycles now have a precise target: their open task is to
  map into \(\mathbb H^1(X,\mathscr D_c)\), survive Rost--Schmid
  localization and mixed completion, generate the non-scalar harmonic
  complement, and produce the prime-power trace.

- 2026-07-26 — `[SEVENTEENTH SOURCE TYPE CORRECTION]`
  `[DAC_KAHLER_RIEMANN_ARITHMETIC_LEAF_REALIZATION]`.
  A real two-dimensional leafwise de Rham complex cannot be compared
  directly with the raw local two-term Tate--Milnor coefficient.  Its
  correct target is the full sheaf-level arithmetic object obtained
  only after generic/prime Rost--Schmid localization and adjoining the
  real orientation boundary:
  \[
    R\alpha_*\mathbb R_{\mathcal F}
      \simeq\mathscr A_{\mathrm{arith}}^\bullet.
  \]
  This prevents both loss and double counting of degree two.  The
  Kähler realization is therefore downstream of the localization
  triangle, not a construction of the raw coefficient.

- 2026-07-26 — `[EIGHTEENTH SOURCE COEFFICIENT CORRECTION]`
  `[DAC_TRUE_TO_APPROXIMATE_DERIVED_COEFFICIENT]`,
  `[DAC_GENERIC_RATIONAL_STEINBERG_POSTNIKOV_CORRECTION]`.
  Deninger's primary source does not identify the raw invariant sheaf
  with the missing arithmetic coefficient.  It distinguishes the
  rational-Witt approximation from the true space and explicitly says
  that the relevant object on the approximation is
  \(R\alpha_*\mathcal G\).  Kucharczyk--Scholze compute the exact
  generic defect: raw rational-Witt cohomology is an exterior algebra
  and its degree-two products violate the Steinberg relation.

  On the algebraic generic fibre the correction is now constructed
  canonically, without a basis or a point-set true space:
  \[
    A_{\mathrm{St}}
      =\tau_{\le1}^{E_\infty}
        R\Gamma(X_{\overline{\mathbb Q}},\mathbb Q).
  \]
  Borel--motivic vanishing for algebraic extensions of \(\mathbb Q\)
  gives \(K_n^M\otimes\mathbb Q=0\) for \(n\ge2\), so the induced
  cohomology map is exactly the rational Steinberg quotient.  Exact
  rational Galois descent yields degrees
  \(\mathbb Q\), \(\mathbb Q^\times\otimes\mathbb Q\), and zero above
  one.

  This supersedes the MW-first and coarse-stack-first source wording.
  Core generic coefficient is Milnor/Steinberg; Milnor--Witt is a
  separate real-orientation enhancement.  The coarse/stack cone is a
  possible middle-defect summand, not the definition and not known to
  be exhaustive.  Exact next gate is sheafifying the canonical
  Postnikov correction over Deninger's quotient-adapted charts,
  adjoining finite residues and the real Arakelov boundary, and proving
  reduced leafwise comparison.  The concise authoritative dependency
  ledger is `deninger-source-native-arithmetic-cohomology-roadmap`.

- 2026-07-27 — `[NINETEENTH SOURCE SHEAF CORRECTION]`
  `[DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE]`,
  `[DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON]`,
  `[DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION]`.
  The eighteenth correction correctly identified the Steinberg defect
  but made a source type error: a Postnikov truncation of
  \(R\Gamma(X_{\overline{\mathbb Q}},\mathbb Q)\) is a global
  \(E_\infty\)-algebra, not a sheaf on Deninger's approximation.
  It has no restriction, residue, Gysin, or power-descent data.

  The source is instead the already constructed equivariant
  Tate-graded leafwise sheaf
  \[
    \widetilde{\mathscr A}^M_{F,\mathrm{geom}}
    =
    \mathscr T_{\widetilde X_F}
    \mathop{\otimes}^{\mathbb L}_{\mathscr P_F}
    \underline{\mathcal K}^{M}_{F,\mathbb R}.
  \]
  Its chartwise derived-section algebra is computed by character-shape
  formality and algebraic cyclotomic Milnor amplitude.  That
  calculation is a comparison target, not the source definition.
  Moreover, the stalk Tor class
  \[
    \operatorname{Tor}_1^{\Lambda(V)}
      (\mathbb R,\mathbb R\oplus V)\cong\Lambda^2V
  \]
  proves that chartwise two-term amplitude cannot be promoted to
  stalkwise two-term amplitude.

  Exact next gate is therefore the sheafified
  unit-amalgamation/derived-section comparison, followed by
  degreewise coarse power descent, arithmetic generic/prime
  localization, and the real signature window.  The global-Postnikov
  route is retired in
  `deninger-global-postnikov-cochains-as-source-coefficient`.

- 2026-07-27 — `[TWENTIETH SOURCE-ONLY CORRECTION]`
  `[DAC_COARSE_INVARIANT_SHEAF_EXISTENCE]`,
  `[DAC_ARITHMETIC_PROJECTION_LERAY_ROST_SCHMID_RESOLUTION]`.
  The quotient-stack endpoint and coarse-to-derived fiber were
  promoted too far.  They are auxiliary diagnostics, not Deninger's
  source and not dependencies of arithmetic cohomology.

  For the corrected equivariant Tate--Milnor cover sheaf, Deninger's
  coefficient is exactly the degreewise invariant sheaf
  \[
    \mathscr E_{\mathrm{Den}}^\bullet
    =
    (\pi_*\widetilde{\mathscr A}^{\bullet})^{\mathbb Q_{>0}}.
  \]
  This is a genuine dg-algebra sheaf: direct image is a right adjoint,
  fixed points are a limit, and all commuting differentials,
  products, flows, correspondences, residues, and traces restrict.
  Fixed points are only left exact, so none of this commutes
  invariants with cohomology.

  Exact open core is now source-native.  Push
  \(\mathscr E_{\mathrm{Den}}\) along Deninger's arithmetic projection
  to \(\operatorname{Spec}\mathbb Z\); prove that its derived
  pushforward has two analytic rows; identify both as real Milnor
  homotopy-module rows with length-one Rost--Schmid resolutions; prove
  strictness in the mixed \(L^1/L^2\) topology; then adjoin the unique
  real signature skyscraper.  The existing two-column theorem gives
  degrees \(0,1,2\), and the middle degree is intrinsic source
  hypercohomology.  No derived rational-power invariants, bar
  contraction, quotient-stack endpoint, CCM object, Xi zero, or RH
  premise defines it.

- 2026-07-27 — `[TWENTY-FIRST KÄHLER SOURCE CORRECTION]`
  `[DAC_EQUIVARIANT_RADIUS_ORBIT_TRIVIALIZATION]`,
  `[DAC_DENINGER_HILBERT_KUMMER_KAHLER_ORBIT_COLLAR]`.
  No Gamma-rank, bar, or conjectural unitary-phase identification is
  needed to construct the positive-radius Kähler orbit collar.
  The canonical radius satisfies
  \(x(\phi^t p)=e^t x(p)\), hence globally trivializes the nonunitary
  flow space:
  \[
    X_{\rm HK}^{\times}
      \cong x^{-1}(1)\times\mathbb R_{>0}.
  \]
  Its canonical half-density circle refinement is
  \[
    \{(p,z):|z|^2=x(p)\}
      \cong x^{-1}(1)\times\mathbb C^\times .
  \]
  The complex leaves carry standard Kähler form, flow
  \(z\mapsto e^{t/2}z\), positive \(J=*c\), exact Poisson dilations,
  and Meyer's critical radial \(L^2(dx)\) measure.

  This closes the radial collar and local Hodge calculation for the
  isolated \(\mathbb Q\) object.  Its flow is tangent to closed orbit
  leaves, so it is not yet Deninger's dense arithmetic foliation and
  no purity theorem is applied.  It does not identify the
  uncompactified unitary locus \(r(P)=0\) with the flow limit
  \(u\to0\).

  `[DAC_RADIAL_KAHLER_ENDPOINT_FOURIER_TRACE]` further proves that
  cone-apex restriction is \(f(0)\), while leafwise Kähler trace is
  \((\pi/2)\mathcal Ff(0)\).  Thus \(H_\cap\) is geometrically the
  common relative kernel; no second Fourier boundary point is needed.
  Exact next gates are strict apex/trace sheafification, mixed
  \(L^1/L^2\)-nuclear pushforward to the Poisson complex, cup-isometric
  harmonic comparison, and faithfulness on every Meyer generalized
  jet.
