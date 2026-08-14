# Route E Gibbs antiscale determinant Mellin odd-cube law

- **ID:** `ROUTE-E-GIBBS-ANTISCALE-DETERMINANT-MELLIN-ODD-CUBE-001`
- **Stage:** 2-fully-proven
- **Type:** `[PAPER-PROVED EXACT SOURCE FACTORIZATION]` / `[SPECTRAL TRANSVERSALITY LAW]`
- **Scientific status:** `[PAPER-PROVED] [INTERNAL COLLISION-AUDITED] [EXTERNAL PRIORITY UNCLAIMED]`
- **Parent:** `../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **Companion:** `../../3-formalized/new_scientific_knowledge/route-e-critical-half-density-terminal-frame-minimax-law.md`
- **RH used:** no
- **Computation used:** no
- **Lean status:** the exact finite determinant/odd-cube/rapidity core `(11)`--`(19)` is
  formalized in `RHTower/GibbsAntiscaleDeterminantOddCube.lean`, the finite Gibbs Mellin--Euler
  factorization `(5)`--`(7)` in `RHTower/GibbsCriticalDissipationAntiscaleResonance.lean`. The PNT
  layer is now formalized as well, on the reusable prime-window infrastructure
  (`HTGeometry/RpowKernelRemainder.lean`, `HTGeometry/WindowRpowIntegral.lean`,
  `RHTower/PrimeRpowLogSumAsymptotic.lean`, `RHTower/PrimeWindowLaw.lean`,
  `RHTower/PrimeWindowLawNoLog.lean`):
  * `(20)`--`(27)` terminal antiscale chamber — `RHTower/RouteEGibbsTerminalChamber.lean`:
    `terminalChamber`, `cos_terminalChamber_le` (`(21)`/`(22)`), `tendsto_chamberMass`
    (`(25)`: `∑_{X/e<p≤X}p^{-1/2}·log X/√X → 2 - 2e^{-1/2}`), `chamberDeterminant`,
    `exp_chamberMass_div_three_sub_one_le` (`(26)`), `log_one_add_abs_chamberDeterminant_le` and
    `chamberMass_div_three_le_log_one_add` (`(27)`, two-sided `≍ √X/log X`);
  * `(28)`/`(29)` prefix modulus positivity — `prefixModulus_ge` in
    `RHTower/RouteEGibbsWideBatch.lean`;
  * the linear grade of `(36)` — `tendsto_criticalCosSum`
    (`∑_{p≤X}p^{-1/2}cos(t_X log p)·log X/√X → -2`) in the same module;
  * `(30)`--`(33)` prefix phase — `RHTower/RouteEGibbsPrefixPhase.lean`: `prefixPhaseWeight` and
    `tendsto_prefixPhaseWeight` (`(32)`), `prefixPhase`, `abs_prefixPhase_add_le` (`(31)`, the
    linear law with explicit cubic error `68 t³(log Y)²∑p^{-1/2}log p`), and
    `tendsto_prefixPhase_threshold` (`(33)`: `Φ_{(log X)^A}(t_X)·(log X)^{1-A/2} → -4π`, so
    `A = 2` is the exact threshold), on the new Taylor bricks
    `HTGeometry/ArctanSinTaylor.lean` (`|arctan u - u| ≤ |u|³`, `|sin u - u| ≤ |u|³`);
  * Mertens' third theorem `∏_{p≤N}(1-1/p) ≍ 1/log N` — new reusable
    `RHTower/Sieve/MertensThird.lean`;
  * `(34)` prefix modulus stability — `RHTower/RouteEGibbsPrefixModulus.lean`: the exact local
    identity `norm_one_sub_smul_exp_sq` (`|1-p^{-1-2it}|² = (1-1/p)² + (2/p)(1-cos 2t log p)`),
    the two-sided product bounds `prefixModulus_ge'` / `prefixModulus_le`
    (`≤ ∏(1-1/p)·exp(8t²(log Y)²∑1/p)`), and `tendsto_prefixModulus_ratio`
    (the ratio to `∏_{p≤Y}(1-1/p)` tends to one at `t_X` for every `A > 0`), which with
    Mertens' third theorem gives the exact order `1/log Y`.
  All of these build and audit `[propext, Classical.choice, Quot.sound]`.
  Still paper-only: the full rapidity `(37)`/`(38)` (needs the `artanh` quadratic bound, the
  `d_p` versus `p^{-1/2}` correction and the `sinh` resummation) and the four-field
  Mellin--Plancherel polarization `(8)`.

## 1. Literal Gibbs determinant

For a finite prime set (Q), put

\[
 Z_Q(x)=\sum_{U\subseteq Q}e^{-m_Ux},
 \qquad
 J_Q(x)=\sum_{U\subseteq Q}(-1)^{|U|}e^{-m_Ux},
 \qquad
 m_U=\prod_{p\in U}p.                                    \tag{1}
\]

Let (S,P) be disjoint finite prime sets.  For (T\subseteq P), write

\[
 w_T(x)=Z_S(m_Tx),
 \qquad
 k_T(x)=J_S(m_Tx).                                       \tag{2}
\]

The four parity-coarse fields from Route E are

\[
 \begin{aligned}
 W(x)&=\sum_{T\subseteq P}w_T(x),
 &B(x)&=\sum_{T\subseteq P}(-1)^{|T|}w_T(x),\\
 A(x)&=\sum_{T\subseteq P}k_T(x),
 &J(x)&=\sum_{T\subseteq P}(-1)^{|T|}k_T(x).
 \end{aligned}                                           \tag{3}
\]

Thus (W=W_++W_-), (B=W_+-W_-), (A=K_++K_-), and (J=K_+-K_-).  The literal
antiscale-transverse determinant is

\[
 \boxed{D_{S,P}(x)=W(x)A(x)-B(x)J(x)=D_{\rm anti}(x).}    \tag{4}
\]

No surrogate weights occur in `(1)`--`(4)`.

## 2. Euler coordinates

For a finite prime set (Q) and (Re s>0), define

\[
 \mathcal Z_Q(s)=\prod_{p\in Q}(1+p^{-s}),
 \qquad
 \mathcal M_Q(s)=\prod_{p\in Q}(1-p^{-s}).               \tag{5}
\]

Finite summation and the elementary Mellin integral of (e^{-mx}) give

\[
 \widehat Z_Q(s)=\Gamma(s)\mathcal Z_Q(s),
 \qquad
 \widehat J_Q(s)=\Gamma(s)\mathcal M_Q(s).               \tag{6}
\]

The corpus already proves this finite Gibbs Mellin--Euler factorization in
`RHTower/GibbsCriticalDissipationAntiscaleResonance.lean`.  Applying `(6)` to the four fields in
`(3)` gives

\[
 \begin{aligned}
 \widehat W(s)&=\Gamma(s)\mathcal Z_S(s)\mathcal Z_P(s),
 &\widehat A(s)&=\Gamma(s)\mathcal M_S(s)\mathcal Z_P(s),\\
 \widehat B(s)&=\Gamma(s)\mathcal Z_S(s)\mathcal M_P(s),
 &\widehat J(s)&=\Gamma(s)\mathcal M_S(s)\mathcal M_P(s).
 \end{aligned}                                           \tag{7}
\]

This is the first exact source splice: the physical parity determinant and finite Euler
characters use the same four corners.

## 3. Mellin--Plancherel determinant identity

Fix (sigma>0).  All four fields are finite exponential sums, hence belong to the weighted
Mellin (L^2) space on the line (Re s=\sigma).  Mellin--Plancherel and `(7)` yield

\[
 \begin{aligned}
 &\int_0^\infty x^{2\sigma-1}D_{S,P}(x)\,dx\\
 &\quad={1\over2\pi}\int_{-\infty}^{\infty}
   |\Gamma(\sigma+it)|^2
   \mathcal Z_S(\sigma+it)
   \overline{\mathcal M_S(\sigma+it)}\\
 &\hspace{40mm}\cdot
   \left(
     |\mathcal Z_P(\sigma+it)|^2
     -|\mathcal M_P(\sigma+it)|^2
   \right)dt.
                                                               \tag{8}
 \end{aligned}
\]

Proof is exact: apply Parseval to (WA) and (BJ) separately,

\[
 \int x^{2\sigma-1}WA
 ={1\over2\pi}\int\widehat W\,\overline{\widehat A},
 \qquad
 \int x^{2\sigma-1}BJ
 ={1\over2\pi}\int\widehat B\,\overline{\widehat J},
\]

then substitute `(7)` and factor the common term.  There is no interchange of infinite prime
sums and no analytic continuation.

Equation `(8)` retains the literal physical determinant, but it is an integrated signed identity.
It is not yet a pointwise lower bound for the nonnegative coarse defect

\[
 \mathcal C_{S,P}(x)
 ={D_{S,P}(x)^2\over W(x)(W(x)^2-B(x)^2)}.                \tag{9}
\]

## 4. Critical half-density coordinates

Set (sigma=1/2).  The source-selected reflected WKB/Fisher half-density is

\[
 d_p={p^{-1/2}\over1+p^{-1}}.                             \tag{10}
\]

For real (t), define

\[
 u_p(t)=2d_p\cos(t\log p).                                \tag{11}
\]

Since (p>1), the arithmetic--geometric mean inequality gives

\[
 |u_p(t)|\le {2\sqrt p\over p+1}<1.                       \tag{12}
\]

Direct local multiplication gives

\[
 \begin{aligned}
 |1+p^{-1/2-it}|^2&=(1+p^{-1})(1+u_p(t)),\\
 |1-p^{-1/2-it}|^2&=(1+p^{-1})(1-u_p(t)).
 \end{aligned}                                           \tag{13}
\]

Consequently, with

\[
 R_P=\prod_{p\in P}(1+p^{-1}),                            \tag{14}
\]

the exact batch factor in `(8)` is

\[
 \boxed{
 |\mathcal Z_P(1/2+it)|^2-|\mathcal M_P(1/2+it)|^2
 =R_P\left(\prod_{p\in P}(1+u_p(t))
            -\prod_{p\in P}(1-u_p(t))\right).}           \tag{15}
\]

This proves that the (p^{-1/2}) half-density in the companion minimax law is not an inserted
weight.  It is the exact first transverse coordinate of the literal Gibbs parity determinant on
the critical Mellin line.

## 5. Odd-cube completion

Expanding the two products in `(15)` cancels every even grade and doubles every odd grade:

\[
 \boxed{
 |\mathcal Z_P|^2-|\mathcal M_P|^2
 =2R_P
   \sum_{\substack{U\subseteq P\\|U|\ {\rm odd}}}
      \prod_{p\in U}u_p(t).}                              \tag{16}
\]

The first grade is

\[
 2R_P\sum_{p\in P}u_p(t)
 =4R_P\sum_{p\in P}d_p\cos(t\log p).                    \tag{17}
\]

All higher odd grades are forced by the same source determinant.  The mass-divergent
half-density carrier and the growing-arity parity cube are therefore not two unrelated Route E
survivors: `(17)` is the first grade of `(16)`.

There is also an exact nonlinear resummation.  Since (|u_p|<1),

\[
 1\pm u_p=\sqrt{1-u_p^2}\,
           \exp(\pm\operatorname{artanh}u_p).
\]

Hence

\[
 \boxed{
 |\mathcal Z_P|^2-|\mathcal M_P|^2
 =2R_P\prod_{p\in P}\sqrt{1-u_p(t)^2}\,
   \sinh\left(\sum_{p\in P}\operatorname{artanh}u_p(t)\right).}
                                                               \tag{18}
\]

The complete spectral escape condition is now exact:

\[
 |\mathcal Z_P(1/2+it)|^2=|\mathcal M_P(1/2+it)|^2
 \quad\Longleftrightarrow\quad
 \sum_{p\in P}\operatorname{artanh}
   \bigl(2d_p\cos(t\log p)\bigr)=0.                      \tag{19}
\]

Thus linear first-grade cancellation is only the tangent approximation to a nonlinear additive
rapidity law.  The higher odd grades are its exact hyperbolic completion.

## 6. Terminal antiscale chamber is spectrally transverse

Let

\[
 P_X=\{p:\ X/e<p\le X\},
 \qquad L=\log X,
 \qquad t_X={\pi\over L}.                                \tag{20}
\]

For (p\in P_X),

\[
 \pi- {\pi\over L}\le t_X\log p\le\pi.                  \tag{21}
\]

For sufficiently large (X), `(21)` gives

\[
 \cos(t_X\log p)\le-\frac12,
 \qquad
 a_p:=-u_p(t_X)\ge d_p>0.                                \tag{22}
\]

Every odd monomial in `(16)` now has the same sign.  More sharply, `(15)` becomes

\[
 \left||\mathcal Z_{P_X}|^2-|\mathcal M_{P_X}|^2\right|
 =R_{P_X}\left(\prod_{p\in P_X}(1+a_p)
                -\prod_{p\in P_X}(1-a_p)\right).         \tag{23}
\]

Since (0<a_p<1),

\[
 \prod(1-a_p)\le1,
 \qquad
 \log\prod(1+a_p)\ge\frac12\sum a_p.                   \tag{24}
\]

The prime number theorem and (d_p\asymp X^{-1/2}) on (P_X) give

\[
 \sum_{p\in P_X}a_p\ge\sum_{p\in P_X}d_p
 \asymp {\sqrt X\over L}.                                \tag{25}
\]

Combining `(23)`--`(25)` proves the unconditional lower bound

\[
 \boxed{
 \left||\mathcal Z_{P_X}(1/2+it_X)|^2
       -|\mathcal M_{P_X}(1/2+it_X)|^2\right|
 \ge \exp\left(c{\sqrt X\over L}\right)-1.}             \tag{26}
\]

The reverse estimate follows from
(log(1+a_p)\le a_p), (R_{P_X}=\exp(O(L^{-1}))), and
(sum a_p\ll\sqrt X/L).  Therefore

\[
 \boxed{
 \log\left(1+\left||\mathcal Z_{P_X}|^2
       -|\mathcal M_{P_X}|^2\right|\right)
 \asymp {\sqrt X\over L}.}                               \tag{27}
\]

at the explicit terminal resonance.

This reverses the additive antiscale-frame behavior.  The scalar factor
(|1+p^{it_X}|) is small, but the critical signed/unsigned Euler determinant sees
(1-p^{-1/2-it_X}\) versus (1+p^{-1/2-it_X}); their metric imbalance is maximal.  Antiscale
coherence is a null direction only after premature scalarization.  The full parity determinant is
spectrally transverse to it.

## 7. Prefix magnitude does not erase the lobe

The base factor in `(8)` satisfies

\[
 \left|\mathcal Z_S(s)\overline{\mathcal M_S(s)}\right|
 =\prod_{p\in S}|1-p^{-2s}|.                              \tag{28}
\]

On the critical line,

\[
 |1-p^{-1-2it}|\ge1-p^{-1},
\]

so

\[
 \left|\mathcal Z_S(1/2+it)
       \overline{\mathcal M_S(1/2+it)}\right|
 \ge\prod_{p\in S}(1-p^{-1})>0.                          \tag{29}
\]

For an initial prime aperture this is only logarithmically small by Mertens' product theorem.
Also (|\Gamma(1/2+it_X)|^2\to\pi).  Thus neither Gamma damping nor prefix amplitude can destroy
the exponential terminal spectral lobe `(26)`.  The unresolved issue is its moving complex phase
inside the integral `(8)`.

## 8. Sharp prefix-phase threshold and coherent wide batch

The terminal-band theorem above leaves a possible conflict: enlarging (P) supplies growing arity,
but the remaining prefix (S) may rotate the factor in `(28)` too quickly.  That conflict can be
resolved exactly in spectral coordinates.

For an initial prime prefix (S_Y=\{p:p\le Y\}), write the continuous argument of the factor in
`(28)`, normalized to zero at (t=0), as (Phi_Y(t)).  Direct local multiplication gives

\[
 \mathcal Z_{S_Y}(1/2+it)\overline{\mathcal M_{S_Y}(1/2+it)}
 =\prod_{p\le Y}
   \left(1-p^{-1}-2ip^{-1/2}\sin(t\log p)\right),         \tag{30}
\]

and therefore, while (|t|\log Y=o(1)),

\[
 \begin{aligned}
 \Phi_Y(t)
 &=-\sum_{p\le Y}
   \arctan\left({2\sqrt p\sin(t\log p)\over p-1}\right)\\
 &=-2t\sum_{p\le Y}{\sqrt p\log p\over p-1}
   +o(t\sqrt Y).                                         \tag{31}
 \end{aligned}
\]

The PNT weighted by ((\log p)/\sqrt p) gives

\[
 \sum_{p\le Y}{\sqrt p\log p\over p-1}
 =2\sqrt Y(1+o(1)).                                      \tag{32}
\]

The errors in `(31)` are dependency-closed.  Replacing (sin z) by (z) costs

\[
 O\left(t^3\sum_{p\le Y}{(\log p)^3\over\sqrt p}\right)
 =O(t^3\sqrt Y(\log Y)^2)=o(t\sqrt Y),
\]

and replacing (arctan z) by (z), or (p-1) by (p), contributes still less.

Now put (L=\log X), (t_X=\pi/L), and (Y=L^A) for fixed (A>0).  Equations `(31)`--`(32)`
give the sharp phase law

\[
 \boxed{
 \Phi_{L^A}(t_X)
 =-4\pi L^{A/2-1}(1+o(1)).}                              \tag{33}
\]

Hence (A=2) is the prefix-phase threshold:

- (0<A<2): prefix phase tends to zero;
- (A=2): prefix phase has a finite nonzero limit;
- (A>2): unwrapped prefix phase makes arbitrarily many rotations.

The modulus is stable on the same range.  Taylor expansion of `(30)` and Mertens' product theorem
give, for every fixed (0<A<2),

\[
 \left|\mathcal Z_{S_Y}(1/2+it_X)
       \overline{\mathcal M_{S_Y}(1/2+it_X)}\right|
 =(1+o(1))\prod_{p\le Y}(1-p^{-1})
 \asymp {1\over\log Y}.                                  \tag{34}
\]

Take the complementary growing batch

\[
 \widetilde P_X=\{p:\ Y<p\le X\},
 \qquad Y=L^A,
 \qquad 0<A<2.                                           \tag{35}
\]

Its complete rapidity from `(18)` is

\[
 \mathcal R_X
 =\sum_{p\in\widetilde P_X}
   \operatorname{artanh}\bigl(2d_p\cos(t_X\log p)\bigr).
\]

PNT partial summation at the moving frequency gives

\[
 \sum_{p\le X}p^{-1/2+it_X}
 ={X^{1/2+it_X}\over(1/2+it_X)\log X}(1+o(1))
 =-{2\sqrt X\over L}(1+o(1)).                            \tag{36}
\]

The primes below (Y) contribute (o(\sqrt X/L)).  Also
(d_p=p^{-1/2}(1+O(p^{-1}))), and the total error in replacing
\(\operatorname{artanh}u_p\) by \(u_p\) is

\[
 O\left(\sum_{p>Y}p^{-3/2}\right)=o(1).
\]

Taking real parts in `(36)` therefore proves

\[
 \boxed{
 \mathcal R_X=-{4\sqrt X\over L}(1+o(1)).}                \tag{37}
\]

In `(18)`, the logarithms of (R_{\widetilde P_X}) and
\(\prod\sqrt{1-u_p^2}\) are only \(O(\log\log X)\). Thus

\[
 \boxed{
 \log\left(1+\left|
 |\mathcal Z_{\widetilde P_X}(1/2+it_X)|^2
 -|\mathcal M_{\widetilde P_X}(1/2+it_X)|^2
 \right|\right)
 ={4\sqrt X\over L}(1+o(1)).}                             \tag{38}
\]

Equations `(33)`, `(34)`, and `(38)` close the spectral prefix-stabilization subproblem.  At the
same explicit physical frequency, one source split has

\[
 \text{prefix phase}=o(1),\qquad
 \text{prefix modulus}\asymp(\log\log X)^{-1},\qquad
 \text{batch transverse log-capacity}\sim4\sqrt X/L.     \tag{39}
\]

Therefore large prefix rotation is avoidable without sacrificing growing-arity capacity.  The
remaining obstruction is not spectral prefix stabilization; it is conversion of this coherent
spectral lobe into the pointwise normalized physical determinant.

## 9. Conjecture--proof--failure loop

### Loop A: critical half-density is external to Gibbs source

`[CONJECTURE]` The (p^{-1/2}) carrier in the companion minimax law may be an arbitrary analytic
reweighting with no literal Route E meaning.

`[FALSIFIED]` Equations `(13)`--`(17)` derive (d_p) as the first critical transverse coordinate
of the exact signed/unsigned Gibbs batch determinant.

### Loop B: higher odd grades cancel terminal first grade

`[CONJECTURE]` Growing arity may destroy the physical first-grade signal at antiscale resonance.

`[FALSIFIED ON THE TERMINAL CHAMBER]` All (u_p(t_X)) have the same negative sign.  Every odd
grade reinforces it, and the full determinant grows on the exponential scale `(26)`.

### Loop C: mass-divergent carrier and growing-arity cube are independent avenues

`[CONJECTURE]` Route E must choose between the two survivor classes.

`[FALSIFIED]` Equation `(16)` identifies the half-density carrier as grade one of the unique
source-predeclared odd Euler cube.  Equation `(18)` resums the entire cube into one additive
rapidity coordinate.

### Loop D: spectral transversality proves the physical coarse defect

`[CONJECTURE]` The exponential lower bound `(26)` closes (D_{\rm anti}).

`[FALSIFIED]` Equation `(8)` is a signed Mellin inner-product identity, not a pointwise inverse
Mellin inequality.  Prefix factor in `(28)` has nonvanishing magnitude but aperture-dependent
phase.  Frequency localization with an arbitrary complex test would not retain the positive Gibbs
weights, moving cutoff, or denominator in `(9)`.  No pointwise (D_{S,P}(x)) bound follows.

### Loop E: prefix stabilization and batch capacity are incompatible

`[CONJECTURE]` Making prefix phase stable forces a terminal batch too small to retain physical
transverse mass.

`[FALSIFIED SPECTRALLY]` Choose (S=\{p\le(\log X)^A\}), (0<A<2), and put every remaining
prime through (X) into one growing batch.  Equations `(33)`--`(39)` prove simultaneous phase
stabilization and exponentially large odd-cube transversality.

## 10. Revised Route E hard core

The analytic carrier problem is no longer open in spectral coordinates:

- literal Gibbs determinant produces critical half-density (d_p);
- complete growing-arity odd cube is explicit;
- its nonlinear escape coordinate is the rapidity sum `(19)`;
- terminal antiscale chamber has exponential transverse capacity `(26)`;
- Gamma and prefix magnitude do not remove that capacity;
- a polylogarithmic-prefix/wide-batch split simultaneously stabilizes prefix phase and retains
  the sharper capacity `(38)`.

What remains is a precise signed Tauberian problem:

> **PREFIX-STABILIZED-MELLIN-DETERMINANT-TO-GIBBS-TRANSVERSE-TRANSFER.**  Convert a co-moving
> frequency neighborhood of the terminal lobe `(26)` through `(8)` into physical-power control of
> (D_{S,P}(x)), or directly of the coarse defect `(9)`, while retaining literal prefix phase,
> Gibbs denominators, recurrence weights, prime-dilation intervals, alternating finite-volume
> signs, and the physical relation between (P) and (x).

This is strictly narrower than “find a singular or growing-arity carrier.”  Carrier and its
source formula now exist.  Missing theorem is phase-stable inverse Mellin transfer into the
normalized physical determinant.  Route E and RH remain open.

## 11. Why ordinary positivity and Halász do not close transfer

1. Positivity of coarse defect occurs after squaring (D_{S,P}(x)).  Equation `(8)` controls a
   signed first moment before that square.
2. Taking absolute values inside `(8)` loses prefix phase and gives an upper bound, not the needed
   physical lower bound.
3. A generic Mellin (L^2) estimate controls frequency average but need not retain coherent
   terminal lobe or one physical (x).
4. Halász/GHS controls multiplicative mean values after pretentious minimization.  It does not
   supply the aperture-uniform inverse Mellin sign theorem or Gibbs denominator comparison in
   `(9)`.
5. The terminal lobe is exponentially large, so spectral size is not the limiting resource.
   Any further argument that only increases spectral capacity is theatre.

## 12. Collision and formalization notes

Internal search found the following separate ingredients:

- finite Gibbs Mellin--Euler factorization in
  `RHTower/GibbsCriticalDissipationAntiscaleResonance.lean`;
- Mellin--Plancherel infrastructure in `RHTower/L2MellinUnitary.lean` and
  `RHTower/MobiusLaplaceMellinPlancherelBridge.lean`;
- algebraic (D_{\rm anti}) decomposition in
  `RHTower/GibbsBatchParityCoarseGraining.lean`;
- reflected WKB/Fisher identity in `RHTower/DeningerMobiusCriticalWKBSeam.lean`.

No internal theorem combines them into `(8)`, derives the odd-cube/rapidity laws `(16)`--`(19)`,
proves terminal determinant transversality `(26)`--`(27)`, or identifies the sharp prefix threshold
and coherent wide-batch law `(33)`--`(39)`.  Broad external arXiv searches were performed during
the parent Route E audit; no external priority claim is made.  Status remains project-local
`[PAPER-PROVED NEW KNOWLEDGE]` pending dedicated publication-level collision audit.

Future Lean work should reuse the four modules above.  New formal blocks are only the four-field
Mellin--Plancherel polarization, finite odd-subset product identity, real `artanh` resummation, and
PNT terminal lower bound.  No Lean file is created during corpus refactor.

## 13. Physical-saddle correction

Subsequent hostile audit found one further obstruction. Spectral capacity (38) is unconditioned
Euler mass; it does not by itself live on physical product scale.

For prime cutoff \(Y\) and Mellin line \(\sigma\), positive squared Euler law has exact mean
log-product

\[
 \Lambda_{\sigma,Y}
 =2\sum_{p\le Y}\frac{p^{-\sigma}}{1+p^{-\sigma}}\log p
 =\frac{2}{1-\sigma}Y^{1-\sigma}(1+o(1)).
\tag{40}
\]

When (40) is tuned to \(2\log X\), so each subset coordinate is centered at ordinary scale \(X\),
optimal antiscale resonance satisfies

\[
 \frac{\left|\prod_{p\le Y}(1-p^{-\sigma-it_{\sigma,Y}})\right|^2}
 {\prod_{p\le Y}(1+p^{-\sigma})^2}
 =X^{-\,\pi^2/((1-\sigma)^2(\log Y)^3)+o((\log Y)^{-3})}
 =X^{-o(1)},
\qquad
 t_{\sigma,Y}=\frac{\pi}{\log Y}
 +\frac{\pi}{(1-\sigma)(\log Y)^2}.
\tag{41}
\]

At \(\sigma=1/2\), centering forces \(2\sqrt Y\sim\log X\), and exact exponent in (41) is
\(-4\pi^2/(\log Y)^3+o((\log Y)^{-3})\). Full proof is
`route-e-physical-saddle-antiscale-coercivity-barrier.md`.

Thus Loop E's spectral theorem remains correct, but unconditioned inverse Mellin transfer is no
longer the precise positive survivor. Any useful transfer must retain physical log-product shell
before Euler fusion:

`PHYSICAL-SHELL-CONDITIONED-GROWING-ODD-CUBE-TRANSVERSALITY`.

Without this conditioning, increasing batch capacity merely moves saddle away from product scale
\(X\), while centering saddle restores explicit antiscale escape (41). Route E and RH remain open.

## 14. Subsequent microcanonical closure

Paper theorem **route-e-physical-shell-conditioned-parity-energy-regression-law.md** constructs
required pre-scalarization shell explicitly.  Gaussian Fourier inversion changes equation (16)
into

\[
 \prod_p(B_p(\tau)+U_p(\tau,t))-\prod_p(B_p(\tau)-U_p(\tau,t))
 =2\sum_{|R|\ {\rm odd}}\prod_{p\in R}U_p
   \prod_{p\notin R}B_p,
\]

so complete odd cube survives exactly with one common energy frequency.  Its finite Bernoulli
form identifies alternating sign with \(e^{i\pi N}\), physical shell with energy \(E\), and sharp
escape with parity--energy Schur complement

\[
 \pi^2\left(\operatorname{Var}N-
 \frac{\operatorname{Cov}(N,E)^2}{\operatorname{Var}E}\right).
\]

At physical center, conditioned determinant is
\(-X^{-\pi^2/(a^2(\log Y)^3)+o((\log Y)^{-3})}\).  Thus shell-conditioned transversality is
proved; missing theorem is its source-faithful ordinary-integer/Gibbs-denominator/seam descent,
not construction of conditioned odd cube.
