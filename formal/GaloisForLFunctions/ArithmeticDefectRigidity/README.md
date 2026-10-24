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
The actual receiver's absolute Mellin trace identifies this subtraction as a linear source
operation. Energy quantiles then retain diffuse receiver mass together with its signed
renormalized cofactor pairing. These results constrain how an arithmetic defect state can be
constructed and renormalized. A common subsequence also retains all fixed cofactor
covariances, finite packet energies and their dilation bounds.

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

Read the forcing/receiver scale separation before choosing a normalization.
The Gram identity then identifies the small signed distance that must survive.
The power subtraction and absolute pole trace explain how to remove the large
forcing without adding an assumption. Finally compare the two extraction tools:
energy quantiles retain moving mass and signed cofactor work, while a common
subsequence retains all fixed cofactor covariances. Neither construction alone
is the complete defect state required for exclusion.

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
| Absolute pole-trace domain | Zero-origin rows with summable pairing against the Mellin cells at $1-\varepsilon$ | `poleTraceDomain` |
| Fixed trace-domain dilations | Proved domain endomorphisms with exact damped trace weight $1/j$ | `traceDilation`, `traceCofactorPacket` |
| Linear cofactor subtraction | Finite cofactor operator minus the row's own trace times $n^{1-\varepsilon}$ | `renormalizedCofactorOperator` |
| Energy quantile | First crossing of a prescribed fraction of $E_T$ | `receiverEnergyQuantile` |
| Quantile cofactor work | Signed renormalized cofactor pairing between two energy crossings | `quantileCofactorWork` |
| Fixed-cofactor Gram table | All signed pairings of floor-dilated receiver rows, divided by receiver energy | `cofactorGram` |
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

This expression specifies an affine residual for the actual source. The absolute
trace construction below realizes it as a linear operation on a proved domain. Boundedness,
invertibility, domain invariance and coercivity require additional estimates.

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

The same paid remainder controls absolute localization. Define

\[
V_T=\sum_{n\le T}\frac{|A_\varepsilon(n)^2+
  A_\varepsilon(n)\widetilde D_\varepsilon(n)|}{n(n+1)}.
\]

Then

\[
V_T=\sum_{n\le T}\frac{|A_\varepsilon(n)|\,|R_\varepsilon(n)|}{n(n+1)}
\le B_\varepsilon\sqrt{E_T}.
\]

On escape, $V_T/E_T\to0$. This is total-variation control of the signed cofactor-density
error. [MovingLocalizationsRetainTheSignedDensity](MovingLocalizationsRetainTheSignedDensity.lean)
makes the consequence explicit: any cell multiplier of absolute value at most one, including
one moving with the horizon, has normalized error at most $V_T/E_T$. The single global remainder budget
pays every such localization; cancellation of the total pairing is not being substituted for
absolute control. No analogous estimate has been proved for the unsubtracted forcing pairing.

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

[BoundedWordErrorsHaveAnAbsoluteHorizonTail](BoundedWordErrorsHaveAnAbsoluteHorizonTail.lean)
also prices newly entering cells. With
$C_\varepsilon^{\mathrm{tail}}=m_\varepsilon M_\varepsilon(1+\varepsilon)/\varepsilon$,

\[
0\le\sum_{H<n\le T}\frac{\rho_\varepsilon(n)}{n(n+1)}
\le C_\varepsilon^{\mathrm{tail}}(H+1)^{-\varepsilon},
\]

\[
\left|\sum_{H<n\le T}
\frac{[A_\varepsilon(w(n))-A_\varepsilon(\lfloor n/q(w)\rfloor)]\rho_\varepsilon(n)}
{n(n+1)}\right|
\le B(w)C_\varepsilon^{\mathrm{tail}}(H+1)^{-\varepsilon}.
\]

Both estimates hold uniformly in the final horizon $T$. For every fixed word and positive
error allowance, one sufficiently large cutoff pays all later final horizons. No receiver
normalization is used. Moving words carry the displayed boundary-cost factor. This is an
absolute compensation theorem for bounded word errors; it does not supply the same control
for the unbounded receiver prefix or the full signed compensation problem.

### 8. The actual source determines its linear boundary subtraction

[TheActualReceiverHasAnAbsolutePoleTrace](TheActualReceiverHasAnAbsolutePoleTrace.lean)
extends the actual Mellin pairing to its cofactor pole. Put $\alpha=1-\varepsilon$ and
$\Delta_\alpha(n)=n^{-\alpha}-(n+1)^{-\alpha}$. Then

\[
\sum_{n\ge1}|A_\varepsilon(n)|n^{\varepsilon-2}<\infty,
\qquad
\mathcal L_\varepsilon(A_\varepsilon)
:=\frac1\alpha\sum_{n\ge1}A_\varepsilon(n)\Delta_\alpha(n)
=c_\varepsilon>0.
\]

Absolute convergence comes from the actual VK estimate. Its exponential saving dominates a
summable envelope proportional to $n^{-1}\exp(-\sqrt{\log n}/120)$. To identify the value,
approach $\alpha$ from the right in the existing THIM Mellin identity:

\[
\sum_n A_\varepsilon(n)\Delta_\sigma(n)
=\zeta(\sigma)\left(\frac1{\zeta(\sigma+\varepsilon)}-m_\varepsilon\right),
\qquad \alpha<\sigma<1.
\]

A common summable envelope permits passage to $\sigma=\alpha$, while the reciprocal zeta
factor tends to zero. This argument does not represent the conditionally convergent
$\sum\mu(n)/n$ as an absolutely summable series. The Mellin cells and their bounded-energy
continuity are existing THIM tools; the source endpoint membership and exact value are the
inputs supplied here.

[ThePoleTraceDefinesALinearCofactorRenormalization](ThePoleTraceDefinesALinearCofactorRenormalization.lean)
constructs the real vector space

\[
\mathcal X_\varepsilon
=\left\{v:v(0)=0,\quad
\sum_n|v(n)\Delta_\alpha(n)|<\infty\right\}
\]

and the linear map

\[
\widetilde{\mathcal D}_\varepsilon v(n)
=\sum_{j=2}^{n}j^{-\varepsilon}v(\lfloor n/j\rfloor)
-\mathcal L_\varepsilon(v)n^\alpha.
\]

The actual receiver belongs to $\mathcal X_\varepsilon$ independently of critical-energy
admission. Its image is exactly $\widetilde D_\varepsilon$, so

\[
\|A_\varepsilon+\widetilde{\mathcal D}_\varepsilon A_\varepsilon\|_T\le B_\varepsilon.
\]

The operator is defined with values in all rows. For the actual receiver, its image lies again
in $\mathcal X_\varepsilon$: the paid remainder has bounded pronic energy, hence an absolute
Mellin trace, and $\widetilde D_\varepsilon=R_\varepsilon-A_\varepsilon$. General domain
invariance and boundedness in critical energy remain unproved. They are mathematical
requirements for any proposed iteration or resolvent argument. An escaping source would give
an approximate eigenrelation with value $-1$ after normalization; identifying that relation
is not a proof that it is impossible.

[FixedCofactorsHaveAHarmonicBoundaryTrace](FixedCofactorsHaveAHarmonicBoundaryTrace.lean)
proves that each fixed floor dilation preserves $\mathcal X_\varepsilon$. The missing
summability is paid by finite absolute Mellin blocks:

\[
\sum_{n<Tj}|v(\lfloor n/j\rfloor)|\Delta_\alpha(n)
=j^{-\alpha}\sum_{m<T}|v(m)|\Delta_\alpha(m).
\]

Every partial sum is bounded by a complete block, which establishes absolute convergence
before applying the existing Mellin dilation law. The absolute trace mass
$\sum_n|v(n)\Delta_\alpha(n)|$ scales by exactly $j^{-\alpha}$ under fixed dilation;
this prices the operation without relying on signed cancellation. Consequently

\[
\mathcal L_\varepsilon(v(\lfloor\cdot/j\rfloor))
=j^{-\alpha}\mathcal L_\varepsilon(v),\qquad
\mathcal L_\varepsilon(j^{-\varepsilon}v(\lfloor\cdot/j\rfloor))
=\frac1j\mathcal L_\varepsilon(v).
\]

For every finite set $S$ of positive cofactor indices,

\[
\mathcal L_\varepsilon\left(\sum_{j\in S}j^{-\varepsilon}
  v(\lfloor\cdot/j\rfloor)\right)
=\left(\sum_{j\in S}\frac1j\right)\mathcal L_\varepsilon(v).
\]

For the actual source the last factor is the proved positive $c_\varepsilon$. This is an exact
boundary cost for finite packets. It does not authorize exchanging the complete cofactor sum
with the trace: its harmonic coefficients are not summable. Fixed-dilation domain stability
and stability under the full variable-horizon cofactor operator are different obligations.

The same trace pays the dilation commutator in pillar 11, including when the dilation moves
with the horizon. This compatibility law does not establish boundedness of the full cofactor
operator or general invariance of its trace domain.

### 9. Energy quantiles retain diffuse mass and signed cofactor work

[EnergyQuantilesRetainDiffuseEscape](EnergyQuantilesRetainDiffuseEscape.lean) uses the actual
increment bound to give

\[
|A_\varepsilon(n)|\le n,\qquad
0\le E_{n+1}-E_n\le1,\qquad E_{n+k}-E_n\le k.
\]

For $r\in[0,1]$, define $q_T(r)$ as the first integer with $E_{q_T(r)}\ge rE_T$.
The horizon itself supplies a crossing. The quantile is monotone in $r$, lies at most at $T$,
and satisfies

\[
0\le E_{q_T(r)}-rE_T\le1.
\]

For $0\le r\le s\le1$ and $T\ge1$ this implies

\[
\left|\frac{E_{q_T(s)}-E_{q_T(r)}}{E_T}-(s-r)\right|\le\frac1{E_T}.
\]

On the escaping branch, every fixed energy interval therefore retains its prescribed mass.
No fixed spatial window or finite packet is required. This transport uses bounded increments;
it does not by itself distinguish arithmetic from other rows with the same increment bound.

[EnergyQuantilesPreserveTheSignedCofactorPairing](EnergyQuantilesPreserveTheSignedCofactorPairing.lean)
adds the signed actual-source constraint. Let

\[
W_T(r,s)=\widetilde P_{q_T(s)}-\widetilde P_{q_T(r)}.
\]

The globally paid remainder and the quantile overshoot give, uniformly in both endpoints,

\[
|W_T(r,s)+(s-r)E_T|\le2B_\varepsilon\sqrt{E_T}+1,
\]

\[
\left(\frac{W_T(r,s)}{E_T}+(s-r)\right)^2
\le\frac{8B_\varepsilon^2}{E_T}+\frac2{E_T^2}
\qquad(T\ge1).
\]

Thus energy-quantile transport preserves both positive energy mass and its antipodal signed
cofactor work, even under diffuse escape. This is a joint transport theorem for these two
specific observables. It does not preserve every cofactor/successor covariance, recover the
original spatial geometry from the quantile labels, or exclude the resulting signed state.

### 10. All fixed cofactor covariances admit one common limit

[CountableCofactorCovariancesHaveACommonLimit](CountableCofactorCovariancesHaveACommonLimit.lean)
uses the existing countable compactness theorem on the actual signed tables

\[
K_T(j,k)=\frac{\langle D_jA_\varepsilon,D_kA_\varepsilon\rangle_T}{E_T},
\qquad D_jv(n)=v(\lfloor n/j\rfloor),\quad j,k\ge1,\quad T\ge1.
\]

There is one increasing sequence of horizons along which every entry converges to a real
kernel $K$. The same limit retains

\[
K(1,1)=1,\qquad K(j,k)=K(k,j),\qquad
|K(j,k)|\le\frac1{\sqrt j\sqrt k}.
\]

For every finite cofactor set $S$ and every real coefficient family $a$,

\[
0\le Q_K(a):=\sum_{j,k\in S}a_ja_kK(j,k),
\qquad
\sum_{j,k\in S}a_ja_kK(pj,pk)\le\frac1p Q_K(a)
\quad(p\ge1).
\]

These conclusions hold at each fixed `ε`, without an admission or divergence premise.
The subsequence may depend on `ε`; no simultaneous limit across a cofinal damping
family is asserted. They follow from exact
finite packet energies and the existing sharp pronic dilation law. Compactness is applied to
all mixed entries together, so signed cross terms cannot disappear through independently
chosen subsequences. On the finite coefficient space modulo zero-energy packets, the index
operation $j\mapsto pj$ consequently defines a bounded operator of norm at most $p^{-1/2}$.
The operators compose by integer multiplication; the contraction inequality makes their
quotient action well-defined. This last interpretation is a consequence of the displayed
quadratic inequalities, rather than an additional Hilbert-space construction.

The normalized receiver is nonzero in this carrier. That repairs the elementary loss of mass
in a pointwise zero limit, but it does not retain a moving infinite cofactor sum. In particular,
$\sum_jj^{-\varepsilon}K(1,j)$ cannot be substituted for the complete forcing relation without
a proved tail estimate in the same normalization. Fixed word boundaries can be priced by
pillar 5; moving successor information still carries its explicit boundary budget. These
limitations distinguish a fixed-cofactor Gram carrier from the full defect state needed for
arithmetic exclusion.

### 11. The cofactor commutator has a uniform trace budget

[CofactorRenormalizationHasABoundedDilationCommutator](CofactorRenormalizationHasABoundedDilationCommutator.lean)
prices the interaction of the linear subtraction and floor dilation on its proved domain.
The finite cofactor operator commutes with each $D_p$. Its renormalization satisfies the exact
identity

\[
(\widetilde{\mathcal D}_\varepsilon D_p-
 D_p\widetilde{\mathcal D}_\varepsilon)v(n)
=\mathcal L_\varepsilon(v)
 \left(\lfloor n/p\rfloor^\alpha-p^{-\alpha}n^\alpha\right),
\qquad \alpha=1-\varepsilon.
\]

The right side is meaningful for every $v\in\mathcal X_\varepsilon$. The left side uses
$D_p$ on arbitrary rows after applying $\widetilde{\mathcal D}_\varepsilon$; it does not
assume that the full renormalized operator preserves the trace domain.

Since $0<\alpha<1$, concavity gives

\[
\left|\lfloor n/p\rfloor^\alpha-p^{-\alpha}n^\alpha\right|\le1.
\]

Consequently

\[
\|(\widetilde{\mathcal D}_\varepsilon D_p-
 D_p\widetilde{\mathcal D}_\varepsilon)v\|_T
\le|\mathcal L_\varepsilon(v)|
\]

uniformly in both $p$ and $T$. For the actual receiver the bound is $c_\varepsilon$.
On the escaping branch, the squared commutator norm divided by $E_T$ tends to zero for
**every horizon-dependent choice $p=p(T)$**. No rate restriction on that integer dilation
is needed for this estimate.

This is a paid compatibility law, not a source-exclusion theorem. The finite cofactor
commutation and power rounding hold for general rows; the actual arithmetic input is the
independently proved trace value. Successor transport on repairing ideals and boundedness
of the full renormalized operator remain different questions.

### 12. Residual and trace determine the row exactly

[TheResidualAndPoleTraceDetermineTheRow](TheResidualAndPoleTraceDetermineTheRow.lean)
uses the existing weighted Möbius floor inverse. Put

\[
\mathcal R_\varepsilon(v)=v+\widetilde{\mathcal D}_\varepsilon v,
\qquad
q_\varepsilon(n)=\sum_{d\le n}\mu(d)d^{-\varepsilon}
  \lfloor n/d\rfloor^{1-\varepsilon}.
\]

For every $v\in\mathcal X_\varepsilon$, exact reconstruction gives

\[
v(n)=\sum_{d\le n}\mu(d)d^{-\varepsilon}
  \mathcal R_\varepsilon(v)(\lfloor n/d\rfloor)
  +\mathcal L_\varepsilon(v)q_\varepsilon(n).
\]

Thus $(\mathcal R_\varepsilon,\mathcal L_\varepsilon)$ is injective. Two rows with the same
residual and the same trace coincide. Every possible residual-kernel row is a scalar multiple
of the explicit row $q_\varepsilon$, and a kernel row with trace zero vanishes.

This is a containment statement. It does not assert that $q_\varepsilon$ belongs to the trace
domain, that its trace is one, or that the residual kernel is nonzero. Those analytic questions
cannot be discharged by floor inversion alone.

For the actual receiver,

\[
A_\varepsilon(n)=\sum_{d\le n}\mu(d)d^{-\varepsilon}
 R_\varepsilon(\lfloor n/d\rfloor)+c_\varepsilon q_\varepsilon(n).
\]

The remainder $R_\varepsilon$ is globally paid. Its Möbius floor inverse and the row
$q_\varepsilon$ have not been proved paid here. The displayed reconstruction therefore
isolates the two unestimated terms rather than transferring the known remainder bound through
an unproved bounded inverse. Source uniqueness on a trace slice is exact; coercivity remains
a separate quantitative question.

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
  with a uniform absolute tail budget for newly entering cells.
- **Paid commutation:** expose the exact rank-one boundary term and price its norm before
  interchanging renormalization with a moving arithmetic operation.
- **Source boundary trace:** determine the linear subtraction from the actual row and prove
  domain membership independently of energy admission.
- **Joint covariance extraction:** retain every fixed mixed cofactor entry and every finite
  packet energy along one subsequence, including its quantitative dilation action.
- **Energy quantile transport:** retain diffuse energy and its signed cofactor work with a
  uniform, explicitly vanishing error.

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
| Joint extraction | Fixed cofactor covariances already have a common limit, and quantiles retain moving signed work. How can these coexist with the complete moving cofactor tail in one carrier? | A compatible compactness or decomposition theorem preserving both constructions, the rate and spatial data, without exchanging an uncontrolled infinite sum with a limit. |
| Quantitative source selectivity | Which actual arithmetic relation excludes the surviving tangent state or its approximate renormalized cofactor eigenrelation? | An independently proved estimate violated by the relevant impure models. |
| Mixed Bézout/Vaughan covariance | Can additive coprimality and multiplicative factorization give a summable signed gain after correct centering? | A bound for the complete mixed residual with horizon and damping dependence. |
| Successor dynamics | Which moving words or amplified coefficient operations retain source information at a controlled cost? | A nontrivial action at the escape scale and a proved boundary estimate consumed by a receiver. |
| Renormalized operator domains | Dilations preserve the trace domain and have a uniformly paid renormalization commutator; the actual renormalized image also belongs to the domain. On which larger source-compatible spaces can the full subtraction be iterated or controlled? | General domain invariance and quantitative critical-norm estimates, including the harmonic boundary cost of growing packets. |
| Repairing modules | How do these operations act on ideals, hulls and local vanishing orders? | A defined action or transport relation preserving the required local algebra; ideal invariance must be proved. |
| Absolute compensation | Can the signed tail and its newly entering horizon cells be paid in the receiver norm? | An absolute bound including all cross terms; summable relative errors alone are insufficient. |
| Shared allocation | Can one certificate control the full signed form across overlapping carriers? | A global allocation including frustration, boundary flux and one Gamma/polar reserve. |
| Arithmetic anti-collapse | How much local depth mass must an actual divisor packet carry, with multiplicity? | A quantitative lower bound and its width-to-energy transfer; a total zero-count bound does not suffice. |
| Source effectivity | Can source-defined sections force the required sign independently of that sign? | A section or energy law with a proved landing in the effectivity receiver. |
| Enumerative certificates | Can a source-defined incidence count bound a quantized defect in the right direction? | An identity such as $D+H=B$, $H\ge0$, together with an independent bound below the defect quantum. |

The extraction problem must accommodate fixed-word collapse, forcing in growing cofactor
tails, and the impossibility of a common scalar normalization. The paid power subtraction
offers one concrete response: retain the explicit power separately and carry the residual
cofactor relation in the receiver norm. The absolute trace supplies a linear operator domain;
energy quantiles retain diffuse energy and signed antipodal work. The countable Gram limit
retains every fixed finite packet with its dilation bound. A complete extraction must reconcile
these observations on moving carriers and retain their spatial and scale data. Neither a
finite Gram matrix nor a countable table without a tail theorem resolves that requirement.

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
- Entrywise convergence of every fixed cofactor covariance does not justify a moving
  cutoff or an infinite cofactor sum.
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
| [Signed Successor Arithmetic](../SignedSuccessorArithmetic/README.md) | Supplies exact successor counts and density-scale rigidity. Their transfer to an escaping receiver must overcome fixed-successor collapse and retain the moving boundary cost. |
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
dual boundary control, a source-defined linear subtraction, and joint transport of diffuse
energy and signed work. Their next use must improve
the retained signed residual or produce the missing exclusion estimate.
