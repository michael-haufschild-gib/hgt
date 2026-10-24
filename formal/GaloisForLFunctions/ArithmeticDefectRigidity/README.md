# Arithmetic Defect Rigidity

Arithmetic defect rigidity studies which failures of critical arithmetic estimates can survive
normalization, localization and passage to infinity. Its central question is quantitative:
**which relations of the actual source restrict an escaping defect, and do those restrictions
control the signed quantity consumed by an established receiver?**

The first tools concern the centered damped Möbius receiver. They separate its energy from the
larger positive forcing, retain the receiver as a signed Gram difference, locate the forcing in
the cofactor tail, and price every finite word of successor translations and floor dilations.
An explicit power subtraction pays the remaining forcing in the global receiver norm. A
separate pronic mass estimate pays bounded boundary errors even against the complete forcing.
These results constrain how an arithmetic defect state can be constructed and renormalized.

**The open core is exclusion.** These constraints do not prove that receiver energy is bounded.
A source estimate excluding every escaping state for a cofinal family of positive dampings
would imply RH through the existing critical-energy receiver. Such an estimate is not an input
or an axiom of this programme.

## Motivation

The corpus has exact receivers for the same unresolved arithmetic sign: critical energy,
continuation, Weil positivity, Hodge index, source effectivity and orientation. An equivalence
identifies what must be controlled. It does not produce that control.

Arithmetic compensation already constructs normalized receiver profiles and proves that their
energy escapes every fixed window. The next issue is what survives that escape. A pointwise
limit can be zero while total energy remains one. A cofactor identity can become homogeneous
on fixed cells while its complete forcing grows without bound. A successor label can survive
in the notation while its action becomes the identity in the chosen norm.

The programme therefore keeps three parts together:

1. Actual arithmetic source data and exact finite-horizon identities.
2. Quantitative costs of the operations used to observe those data.
3. The signed residual, moving support and normalization required by the receiver.

The purpose is an estimate or a rigorously justified restriction on possible defects. Naming a
state, reconstructing the source, or adding a positivity field to a structure is insufficient.

## Objects and language

Fix a damping $0<\varepsilon<1/2$. Write

\[
c_\varepsilon(n)=\sum_{d\mid n}\mu(d)d^{-\varepsilon},\qquad
m_\varepsilon=\zeta(1+\varepsilon)^{-1},\qquad
A_\varepsilon(n)=\sum_{j=1}^n(c_\varepsilon(j)-m_\varepsilon).
\]

The pronic pairing and energy are

\[
\langle u,v\rangle_T=\sum_{n=1}^T\frac{u(n)v(n)}{n(n+1)},\qquad
E_T=\|A_\varepsilon\|_T^2.
\]

The actual inversion identity is

\[
\rho_\varepsilon(n)
=n-m_\varepsilon\sum_{j=1}^n j^{-\varepsilon}\lfloor n/j\rfloor
=A_\varepsilon(n)+D_\varepsilon(n),
\quad
D_\varepsilon(n)=\sum_{j=2}^n j^{-\varepsilon}A_\varepsilon(\lfloor n/j\rfloor).
\]

| Object | Meaning | Lean source |
|---|---|---|
| Subcritical damping | The declared parameter domain $0<\varepsilon<1/2$ | `SubcriticalDamping` |
| Receiver energy $E_T$ | Actual critical pronic energy | Existing `dampedMobiusEnergy` |
| Forcing energy $F_T$ | Complete energy $\|\rho_\varepsilon\|_T^2$ | `forcingEnergy` |
| Forcing floor | Explicit positive coefficient of $T^{1-2\varepsilon}$ | `forcingFloor` |
| Signed covariance $P_T$ | $\langle A_\varepsilon,\rho_\varepsilon\rangle_T$ | `receiverForcingPairing` |
| Cofactor Gram coordinates | $G_T=\|D_\varepsilon\|_T^2$, $Q_T=\langle\rho_\varepsilon,D_\varepsilon\rangle_T$ | `cofactorEnergy`, `forcingCofactorPairing` |
| Gram determinant | $F_TG_T-Q_T^2$ | `forcingGramDefect` |
| Cofactor head coefficient | $H_{\varepsilon,J}=\sum_{2\le j\le J}j^{-\varepsilon}/\sqrt j$ | `cofactorHeadCoefficient` |
| Signed cofactor tail | $D_\varepsilon-D_{\varepsilon,\le J}$ | `cofactorTail` |
| Tail error | Squared distance of that tail from the complete forcing | `cofactorTailErrorEnergy` |
| Growing source window | $\lfloor\log(F_T/E_T)\rfloor$ | `forcingCofactorWindow` |
| Forcing power | $c_\varepsilon n^{1-\varepsilon}$ with $c_\varepsilon=-m_\varepsilon\zeta(1-\varepsilon)/(1-\varepsilon)>0$ | `forcingPower` |
| Paid forcing remainder | $R_\varepsilon=\rho_\varepsilon-c_\varepsilon n^{1-\varepsilon}$ | `forcingRemainder` |
| Renormalized cofactor residual | $D_\varepsilon-c_\varepsilon n^{1-\varepsilon}$ for the actual source | `renormalizedCofactor` |
| Pronic forcing mass | $\sum_{n\le T}\rho_\varepsilon(n)/(n(n+1))$ | `forcingPronicMass` |
| Exact forcing mass | $L_\varepsilon=\sum_n\Lambda(n)n^{-1-\varepsilon}=-\zeta'(1+\varepsilon)/\zeta(1+\varepsilon)$ | `forcingMassLimit` |
| Cell word | Finite composition of successor translations and positive integer floor dilations | `CellWord` |
| Word boundary cost | Total translation length, with division allowed to reduce the displacement | `CellWord.boundaryCost` |

The programme uses *defect state* for a proposed carrier of escaping energy together with its
arithmetic operations, signed covariances, scales and forcing. No abstract interface asserting
the desired exclusion is supplied. The finite objects above are constructed directly from the
source; a complete compactification retaining all required information remains a research task.

The distinctions matter:

- A source observation is data; an estimate controls its size in a specified norm.
- Reconstruction does not imply a bounded output.
- A unique arithmetic source need not have a coercive energy estimate.
- Relative smallness does not imply an absolute energy bound.
- A limiting Gram matrix need not retain its small signed distance coordinate.
- Divisor support does not retain multiplicity or local vanishing orders.
- A finite operation may have a growing boundary cost when its parameters move.

## Foundational results

### 1. The forcing and receiver require different scales

[TheForcingDominatesTheReceiver](TheForcingDominatesTheReceiver.lean) and
[ForcingScaleSeparation](ForcingScaleSeparation.lean) combine the exact positive majorant
identity with the actual-source Vinogradov–Korobov estimate. With

\[
b_\varepsilon=\frac{m_\varepsilon^2}{2}\,2^{-2(1+\varepsilon)}>0,
\qquad
\sigma(T)=(\log T)^{3/5}(\log\log T)^{-5/3},
\]

they give

\[
F_T\ge b_\varepsilon T^{1-2\varepsilon},\qquad
E_T\le C_\varepsilon e^{-\kappa\sigma(T)/270}F_T
\quad\text{for all sufficiently large }T.
\]

Consequently

\[
F_T\longrightarrow\infty,\qquad E_T/F_T\longrightarrow0,\qquad
F_T/E_T\longrightarrow\infty.
\]

The receiver is nonzero at every positive horizon. These statements hold whether its energy
is admitted or divergent. No divergent-energy premise is needed.

The strongest normalization consequence is `no_common_scalar_normalization`: there is no
scalar sequence $a_T$ for which $a_T^2F_T$ is eventually bounded while $a_T^2E_T$ has an
eventual positive lower bound. A state preserving nonzero receiver energy and finite forcing
must therefore use more than one scalar scale, a suitable renormalized difference, or another
explicit way of retaining the large forcing.

This estimate is source-selective. For the unsigned majorant energy $M_T$, the exact identity
is $F_T=m_\varepsilon^2M_T$, hence

\[
M_T/F_T=m_\varepsilon^{-2}>0\qquad(T\ge1).
\]

The majorant fails the actual receiver's vanishing-ratio law. The new comparison uses the
existing arithmetic VK saving; positivity of the forcing alone does not supply it. Neither
the comparison nor its source selectivity proves admission: $E_T$ may still diverge more
slowly than $F_T$.

### 2. The receiver is a signed Gram difference

[TheReceiverIsTheGramTangent](TheReceiverIsTheGramTangent.lean) retains the exact geometry of

\[
\begin{pmatrix}F_T&Q_T\\Q_T&G_T\end{pmatrix}.
\]

The identities and bounds are

\[
G_T=F_T+E_T-2P_T,\qquad Q_T=F_T-P_T,\qquad
F_T+G_T-2Q_T=E_T,
\]

\[
0\le F_TG_T-Q_T^2=E_TF_T-P_T^2\le E_TF_T.
\]

The determinant divided by $F_T^2$ tends to zero for the actual source. Yet the signed
distance divided by $E_T$ is exactly one. The small receiver is therefore retained by a
tangent coordinate of the larger Gram system; positivity or rank of the limiting matrix
does not recover its size.

In normalized vector notation, let $u_T=A_\varepsilon/\sqrt{E_T}$,
$f_T=\rho_\varepsilon/\sqrt{F_T}$ and $\eta_T=\sqrt{E_T/F_T}$. Then

\[
D_\varepsilon/\sqrt{F_T}=f_T-\eta_Tu_T.
\]

Retaining the bounded covariance $\langle u_T,f_T\rangle_T$ alone does not bound

\[
P_T/E_T=\langle u_T,f_T\rangle_T/\eta_T.
\]

The rate $\eta_T\to0$ and the signed covariance must remain attached. The programme has
not proved a horizon-uniform estimate for this last quantity.

### 3. The signed cofactor tail carries the forcing

[TheCofactorTailCarriesTheForcing](TheCofactorTailCarriesTheForcing.lean) gives, for every
cutoff and horizon,

\[
\|D_{\varepsilon,>J}-\rho_\varepsilon\|_T^2
\le(1+H_{\varepsilon,J})^2E_T.
\]

The proof uses the existing sharp $1/\sqrt j$ pronic dilation contraction and the exact
identity $D_{>J}-\rho=-(A+D_{\le J})$. The finite-head norm estimate is the vector form of
the bound already used in the existing finite-head pairing theorem.

For the actual source the estimate becomes

\[
\|D_{\varepsilon,>J}-\rho_\varepsilon\|_T^2
\le C_\varepsilon(1+H_{\varepsilon,J})^2e^{-\kappa\sigma(T)/270}F_T,
\]

uniformly over $J$ once $T$ is sufficiently large. Every fixed cofactor tail therefore
converges to the complete forcing in the forcing-energy normalization. The conclusion concerns
the signed vector tail, including its cross terms.

The same inequality prices a moving cutoff without exchanging limits. Its cost is explicit:
$(1+H_{\varepsilon,J(T)})^2E_T/F_T$. A fixed-label cofactor limit that discards all large
indices loses the entire forcing. A useful extraction must retain the moving tail or subtract
it with a proved error in the receiver norm.

[ForcingEscapesAMovingCofactorWindow](ForcingEscapesAMovingCofactorWindow.lean) supplies a
concrete growing window. Set $r_T=F_T/E_T$ and $J_T=\lfloor\log r_T\rfloor$. Then

\[
J_T\longrightarrow\infty,\qquad
\frac{\|D_{\varepsilon,>J_T}-\rho_\varepsilon\|_T^2}{F_T}
\le\frac{(1+\log r_T)^2}{r_T}\longrightarrow0
\]

for sufficiently large $T$. The cutoff is defined by finite source energies. Its proof uses
$H_{\varepsilon,J}\le J$ and the proved scale separation, so no admission assumption or
unproved moving-cutoff estimate enters. The complementary cofactor indices grow even when
receiver energy is admitted; this is a statement about where forcing is represented.

### 4. Fixed successors disappear on an escaping receiver

[FixedSuccessorsDisappearFromEscapingProfiles](FixedSuccessorsDisappearFromEscapingProfiles.lean)
uses actual arithmetic coefficient bounds $0\le c_\varepsilon(n)\le1$ and
$0<m_\varepsilon\le1$. They imply

\[
|A_\varepsilon(n+k)-A_\varepsilon(n)|\le k,\qquad
\|A_\varepsilon(\cdot+k)-A_\varepsilon\|_T^2\le k^2.
\]

Together with the existing admission-or-divergence dichotomy, this proves an unconditional
alternative: the receiver is admitted, or every fixed successor displacement divided by
$E_T$ tends to zero.

The positive quantitative output is the moving translation budget $k^2/E_T$. Translations
with $k(T)^2/E_T\to0$ cannot retain a nonzero displacement. This is a necessary scale test,
not a claim that every larger translation detects an arithmetic defect.

### 5. Every finite cofactor-successor word has a boundary budget

[CofactorSuccessorWordsHaveABoundaryCost](CofactorSuccessorWordsHaveABoundaryCost.lean) closes
the preceding estimate under finite compositions. For a word $w$, let $q(w)$ be the product
of its cofactor denominators and $B(w)$ the sum of its successor translation lengths. Then

\[
\lfloor n/q(w)\rfloor\le w(n)\le\lfloor n/q(w)\rfloor+B(w),
\]

and for the actual receiver,

\[
\|A_\varepsilon(w(\cdot))-A_\varepsilon(\lfloor\cdot/q(w)\rfloor)\|_T^2
\le B(w)^2.
\]

Thus the receiver is admitted, or every fixed word reduces to its pure multiplicative dilation
in normalized energy. Adding finitely many interlaced successor and cofactor labels does not
repair the loss of successor information. The surviving tool is the explicit budget for moving
words, $B(w_T)^2/E_T$, together with the exact finite word action.

This result uses bounded arithmetic increments. It does not distinguish the source from every
sequence with bounded increments and does not prohibit successor methods using moving scales,
amplified derivatives, raw coefficient observations, or a different justified topology.

If $W_{w,T}$ is the boundary displacement's signed pairing with the complete forcing,
Cauchy–Schwarz gives

\[
|W_{w,T}|^2\le B(w)^2F_T,\qquad
|W_{w,T}/E_T|^2\le B(w)^2F_T/E_T^2.
\]

This generic estimate alone does not justify dropping the boundary work. The forcing's
stronger pronic mass bound below supplies the missing control:

\[
|W_{w,T}|\le B(w)L_\varepsilon,\qquad
|W_{w,T}|/E_T\le B(w)L_\varepsilon/E_T.
\]

Thus fixed words lose their boundary work as well as their vector displacement on the escaping
branch. Moving words have two distinct costs: $B(w_T)^2/E_T$ in squared norm and
$L_\varepsilon B(w_T)/E_T$ in normalized forcing work. This conclusion uses a proved dual
estimate; it is not inferred from norm disappearance.

### 6. An explicit power subtraction pays the complete forcing remainder

[TheForcingSplitsIntoAPowerAndAnAdmittedRemainder](TheForcingSplitsIntoAPowerAndAnAdmittedRemainder.lean)
connects the forcing to the existing smooth-power expansion in Trans-Horizon Incidence
Mechanics. Put

\[
Z_\varepsilon=\frac{\zeta(1-\varepsilon)}{1-\varepsilon}<0,\qquad
c_\varepsilon=-m_\varepsilon Z_\varepsilon>0,\qquad
M_\varepsilon=K_\varepsilon+|Z_\varepsilon|,
\]

where $K_\varepsilon$ is the existing `floorSumRate` at $1-\varepsilon$. Then

\[
\rho_\varepsilon(n)=c_\varepsilon n^{1-\varepsilon}+R_\varepsilon(n),\qquad
\|R_\varepsilon\|_T
\le m_\varepsilon\sqrt{1+1/\varepsilon}\,M_\varepsilon
=:B_\varepsilon
\]

at every horizon. The hyperbola expansion and its pointwise remainder estimate are existing
THIM results. The contribution here identifies their exact forcing normalization and carries
the paid remainder into the actual cofactor identity.

Define $\widetilde D_\varepsilon=D_\varepsilon-c_\varepsilon n^{1-\varepsilon}$. The
finite-cell relation and its global error are

\[
A_\varepsilon+\widetilde D_\varepsilon=R_\varepsilon,\qquad
\|A_\varepsilon+\widetilde D_\varepsilon\|_T^2\le B_\varepsilon^2.
\]

The receiver is therefore admitted, or

\[
\frac{\|A_\varepsilon+\widetilde D_\varepsilon\|_T^2}{E_T}\longrightarrow0.
\]

This is a valid homogeneous relation in the global receiver norm after an explicit paid
subtraction. It handles moving cells as well as fixed cells. The full forcing itself cannot
be discarded at that normalization.

The residual $\widetilde D_\varepsilon$ is an affine expression for the actual source.
No bounded linear cofactor operator, invertibility, coercivity or exclusion theorem follows
from this subtraction. Constructing a source-compatible operator domain and retaining its
boundary trace remain separate questions.

[TheRenormalizedCofactorIsAntipodalOnEscape](TheRenormalizedCofactorIsAntipodalOnEscape.lean)
retains the signed pairing. If $\widetilde P_T=\langle A_\varepsilon,\widetilde
D_\varepsilon\rangle_T$, then

\[
E_T+\widetilde P_T=\langle A_\varepsilon,R_\varepsilon\rangle_T,\qquad
|E_T+\widetilde P_T|\le B_\varepsilon\sqrt{E_T},\qquad
\left(\frac{\widetilde P_T}{E_T}+1\right)^2\le\frac{B_\varepsilon^2}{E_T}
\quad(T\ge1).
\]

Hence every escaping receiver has renormalized cofactor pairing tending to $-1$. The relation
is a necessary signed constraint on an escaping state, not a contradiction.

### 7. Infinite forcing energy coexists with finite forcing mass

[TheForcingHasFinitePronicMass](TheForcingHasFinitePronicMass.lean) uses the same expansion
to prove

\[
0\le\rho_\varepsilon(n)
\le m_\varepsilon M_\varepsilon n^{1-\varepsilon},\qquad
0\le\sum_{n=1}^T\frac{\rho_\varepsilon(n)}{n(n+1)}
\le M_\varepsilon.
\]

The power envelope is summable in pronic $L^1$ for every damping in the declared range,
although the forcing's pronic $L^2$ energy diverges. The factor $m_\varepsilon$ cancels
the zeta series in the mass estimate.

The existing THIM first-moment identity supplies the exact mass:

\[
\sum_{n=1}^{\infty}\frac{\rho_\varepsilon(n)}{n(n+1)}
=L_\varepsilon
=\sum_{n=1}^{\infty}\Lambda(n)n^{-1-\varepsilon}
=-\frac{\zeta'(1+\varepsilon)}{\zeta(1+\varepsilon)}
\le M_\varepsilon.
\]

The finite masses converge to $L_\varepsilon$ and are all bounded by it. This identifies the
optimal constant for pairing the positive forcing with rows bounded by one; the constant
row itself exhausts that bound.

This pays the forcing pairing of any bounded cell error. In particular, the actual word
boundary bound gives the uniform work estimate in pillar 5. The estimate does not pay
$\langle A_\varepsilon,\rho_\varepsilon\rangle_T$: the receiver prefix is not uniformly
bounded, and inserting such a bound would assume the missing arithmetic control.

## Mechanisms and foundational principles

The programme starts with source identities, establishes the cost of observing them, and only
then forms a limit or a quotient. The established mechanisms are:

- **Scale separation:** compare actual signed cancellation with positive forcing using a proved
  arithmetic estimate.
- **Signed Gram coordinates:** retain small differences and mixed terms before normalization.
- **Tail accounting:** carry a complete cofactor tail as a vector with an explicit cutoff cost.
- **Word calculus:** price additive boundaries through finite compositions with multiplicative
  operations.
- **Paid renormalization:** subtract an explicit forcing power only after its complete
  remainder has a uniform critical-norm budget.
- **Dual mass control:** price bounded cell errors using the forcing's finite pronic mass,
  instead of losing its divergent L2 norm.

Further mechanisms must satisfy the same principles:

1. Construct objects from actual coefficients, theta data or exact source identities.
2. Retain signs until any absolute-value loss has a proved budget.
3. Keep horizon, damping, cutoff, location and scale quantifiers visible.
4. Preserve the defect being studied; erasing it cannot establish its absence.
5. Charge overlap, new cells, boundaries and the Gamma/polar reserve exactly once.
6. Keep multiplicity and local vanishing orders whenever a divisor transfer uses them.
7. Test source selectivity against the relevant surviving countermodels.
8. Allow diffuse escape and growing carriers; do not assume a fixed finite bad packet or a
   positive spectral gap.
9. Separate exact identities, estimates, extraction and exclusion. Each needs its own proof.

These are requirements on theorem design, not new axioms about arithmetic.

## Research questions and tools to develop

| Topic | Question | Required output |
|---|---|---|
| Joint extraction | How can nonzero receiver mass, moving cofactor tails and signed forcing covariance survive in one construction? | A compactness or decomposition theorem retaining the rate and tangent coordinates, including diffuse escape. |
| Quantitative source selectivity | Which actual arithmetic relation constrains the surviving tangent state beyond the present VK separation? | An independently proved estimate violated by the relevant impure models. |
| Mixed Bézout/Vaughan covariance | Can additive coprimality and multiplicative factorization give a summable signed gain after correct centering? | A bound for the complete mixed residual with horizon and damping dependence. |
| Successor dynamics | Which moving words or amplified coefficient operations retain source information at a controlled cost? | A nontrivial action at the escape scale and a proved boundary estimate consumed by a receiver. |
| Repairing modules | How do these operations act on ideals, hulls and local vanishing orders? | A defined action or transport relation preserving the required local algebra; ideal invariance must be proved. |
| Absolute compensation | Can the signed tail and its newly entering horizon cells be paid in the receiver norm? | An absolute bound including all cross terms; summable relative errors alone are insufficient. |
| Shared allocation | Can one certificate control the full signed form across overlapping carriers? | A global allocation including frustration, boundary flux and one Gamma/polar reserve. |
| Arithmetic anti-collapse | How much local depth mass must an actual divisor packet carry, with multiplicity? | A quantitative lower bound and its width-to-energy transfer; a total zero-count bound does not suffice. |
| Source effectivity | Can source-defined sections force the required sign independently of that sign? | A section or energy law with a proved landing in the effectivity receiver. |
| Enumerative certificates | Can a source-defined incidence count bound a quantized defect in the right direction? | An identity such as $D+H=B$, $H\ge0$, together with an independent bound below the defect quantum. |

The extraction problem must accommodate fixed-word collapse, forcing in growing cofactor
tails, and the impossibility of a common scalar normalization. The paid power subtraction
offers one concrete response: retain the explicit power separately and carry the residual
cofactor relation in the receiver norm. Its operator domain, joint source observations and
diffuse escape still require construction. A finite Gram matrix without its rates does not
resolve these questions.

The exclusion problem is separate. Even a complete extraction theorem would leave the need
for a source estimate forbidding its nonzero states. The current results give no such universal
exclusion and no independent all-damping admission producer.

## Traps

- Pointwise disappearance of forcing does not justify discarding its global pairing.
- Subtracting a power from the actual cofactor residual does not establish a bounded linear
  operator on arbitrary rows.
- Finite forcing mass controls bounded cell errors, not arbitrary receiver prefixes.
- A positive forcing is not a bound for its signed pairing with the receiver.
- Vanishing $E_T/F_T$ allows $E_T\to\infty$.
- A positive semidefinite or rank-one limiting Gram matrix can lose the entire critical
  distance coordinate.
- Universal floor commutators and multiplicativity identities need not contain Möbius
  cancellation.
- Fixed-word observations cannot be assumed to retain successor selectivity under energy
  normalization.
- Termwise absolute cofactor control has the known half-damping threshold; a new notation
  does not change its divergent series.
- A finite source certificate must retain its quantitative transfer cost as its carrier grows.
- A nonnegative count $h=D+R$, with $D,R\ge0$, gives no upper bound forcing $D=0$.
- A density-one or eventual-height result may leave finitely many off-line zeros.
- Aperture and damping are different parameters and require an explicit bridge.

## Place among the programmes

| Programme | Relationship |
|---|---|
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | Supplies normalized profiles, origin costs and escape. Defect rigidity studies which operations and forcing survive that normalization. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Supplies the receiver, inversion identity, signed pairings and dilation calculus. Defect rigidity retains their moving residuals and scales. |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Supplies actual-source bounds, successor covariance and the VK estimate. Its mixed arithmetic interactions are candidate sources of stronger rigidity. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Supplies finite incidence, smooth-power expansions and remainder estimates. Defect rigidity uses these to pay the explicit forcing subtraction on moving horizons. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Preserves Möbius signs when passing from source incidence to energy. The same discipline governs the tangent covariance. |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Provides source-orientation and repairing objects whose quantitative defect dynamics remain to be constructed. |
| [Arithmetic Orientation Geometry](../ArithmeticOrientationGeometry/README.md) | Places signed compatibility in geometric carriers. Defect rigidity requires the carrier to preserve the adverse mode and its cost. |
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Supplies Hodge defects, source-effectivity questions and finite-field calibration. A source certificate still needs the correct sign and transfer. |
| [Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md) | Supplies the global Weil–Gamma–pole form. Any allocation certificate must pay its complete signed budget. |
| [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | Supplies incidence decompositions and shared allocation questions. A defect limit must retain their overlap and polar costs. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) | Supplies ground energies and critical degeneracies; defect rigidity does not assume a forbidden fixed gap. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Supplies width, visibility and threshold transfers. Local mass and multiplicity must accompany these transfers. |
| [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | Studies what bounded observations can detect. The finite-word collapse is another quantitative limit on an observation scheme. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Supplies countermodels and uncertainty constraints against which source claims must be tested. |
| [Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md) | Supplies signed surplus mechanisms and proportion results; their strength must be distinguished from all-zero exclusion. |

The programme does not replace these receivers. It aims to produce quantitative inputs for
them while preserving the defects their equivalences expose.

## Success and contribution criteria

A full arithmetic no-escape theorem must extract a nonzero state from any divergent actual
receiver, retain the required signed and moving data, and exclude every such state by an
independently proved source relation for a cofinal damping family. An alternative success is
a direct absolute energy estimate reaching the same receiver. Either would be substantially
stronger than the results above.

A contribution need not prove RH. It must supply a new estimate, exact decomposition,
classification, transport law or obstruction with a nontrivial positive survivor. Its statement
must specify:

- the actual source property used and the countermodels it does or does not exclude;
- the signed residual controlled, its norm and parameter dependence;
- the treatment of moving support, overlap, boundary terms and multiplicity;
- the established receiver or extraction step that consumes its output;
- the independently proved input, separated from the remaining open estimate.

Framework-only interfaces, renamed equivalences and hidden analytic assumptions do not meet
these criteria. The present pillars provide source scale separation, paid forcing subtraction,
dual boundary control and quantitative restrictions on extraction. Their next use must improve
the retained signed residual or produce the missing exclusion estimate.
