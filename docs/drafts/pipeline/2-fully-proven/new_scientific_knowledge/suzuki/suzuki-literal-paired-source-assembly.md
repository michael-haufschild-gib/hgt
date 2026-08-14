# Literal completed Suzuki modes assemble into the paired primitive-flux equation

- **ID:** suzuki-literal-paired-source-assembly
- **Stage:** 2 — fully proved on paper
- **Type:** LITERAL COMPLETED-SOURCE ASSEMBLY / TWO-COSET SIGN CORRECTION
- **Scientific status:** [PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]
  [NOVELTY UNVERIFIED] [NOT RH]
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Primary source:** M. Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, especially (2.7), (2.8), and (2.11)
- **Inputs:** suzuki-completed-eigenmode-atomic-jump-boundedness.md,
  suzuki-paired-seam-carleman-logistic-normal-form.md,
  suzuki-tempered-orbit-carrier-aperture-recurrence-dichotomy.md,
  suzuki-coordinate-cutoff-primitive-flux-identity.md,
  suzuki-polar-remainder-lipschitz-gamma-subcriticality.md
- **Lean core:** GaloisForLFunctions.RHTower.SuzukiLiteralPairedSourceAssembly

## 1. Result

Fix an aperture \(a>0\), let \(u\) be any completed eigenmode of Suzuki's restricted-Weil
operator, and extend its continuous representative by zero outside \((-a,a)\). Let \(P_a\) be
the finite visible-prime set, put

\[
G_a=\mathbb Z^{P_a},\qquad
\ell(\nu)=\sum_{p\in P_a}\nu_p\log p,\qquad
w_\kappa(\nu)=e^{-\kappa|\nu|_1},
\]

and retain both rooted cosets

\[
x_{+,\nu}=a-\ell(\nu),\qquad
x_{-,\nu}=-a+\ell(\nu).                                  \tag{1}
\]

For puncture orientation \(o\in\{+1,-1\}\), define

\[
F_{\epsilon,\nu,o}(L)
 =w_\kappa(\nu)
  \bigl[u(x_{\epsilon,\nu}+o e^{-L})-u(x_{\epsilon,\nu})\bigr]. \tag{2}
\]

Let \(\mathcal H=\ell^2(\{+,-\}\times G_a\times\{+1,-1\})\). Then

\[
F\in L^\infty_{\rm loc}((0,\infty);\mathcal H),\qquad
\sup_L\|F(L)\|_{\mathcal H}
 \le 2\sqrt2\,\|u\|_\infty\|w_\kappa\|_{\ell^2}.          \tag{3}
\]

Choose the standard smooth transition \(\vartheta\), equal to zero on
\((-\infty,0]\) and one on \([1,\infty)\). With
\(s_{\epsilon,\nu,o}(L)=x_{\epsilon,\nu}+o e^{-L}\), put

\[
\begin{aligned}
 A^R_{\epsilon,\nu,o}(L)&=e^L(a-s_{\epsilon,\nu,o}(L)),\\
 A^L_{\epsilon,\nu,o}(L)&=e^L(a+s_{\epsilon,\nu,o}(L)),\\
 \chi_{\epsilon,\nu,o}(L)
   &=\vartheta(A^R_{\epsilon,\nu,o}(L))
     \vartheta(A^L_{\epsilon,\nu,o}(L)).                 \tag{4}
\end{aligned}
\]

Let \(M(L)\) be diagonal multiplication by \(\chi(L)\). Then:

1. \(\chi_{\epsilon,\nu,o}(L)\ne0\) exactly when
   \(s_{\epsilon,\nu,o}(L)\in(-a,a)\), so Suzuki's interior weak equation is never used outside
   its literal support;
2. \(\sup_{\epsilon,\nu,o,L}|\chi'_{\epsilon,\nu,o}(L)|<\infty\);
3. every transition block has length \(O(1)\) in \(L\) and is centered at
   \[
   -\log|a-x_{\epsilon,\nu}|+O(1)
   \quad\hbox{or}\quad
   -\log|a+x_{\epsilon,\nu}|+O(1);                       \tag{5}
   \]
4. at a physical root, the exterior puncture cutoff is identically zero and the interior
   puncture cutoff is eventually one.

Write the exact differentiated paired operator as

\[
\mathcal N=(2L I+C)\partial_L+Z,\qquad
C=R-T_{a,\lambda,\kappa},\qquad
Z=I-KJ,                                                  \tag{6}
\]

where \(R\) is the literal differentiated Gamma remainder, \(KJ\) is the logistic
cross-orientation block, and \(T_{a,\lambda,\kappa}\) is the scalar/eigenvalue term plus the
complete weighted symmetric visible-prime adjacency with Suzuki's source sign. Exponentially
small \(q\)-terms are retained in the physical primitive.

There are explicit physical source vectors \(G_{\rm phys},H_{\rm phys}\), consisting only of the
fixed-window correction, polar convolution, and exponential \(q\)-term, such that the actual
completed mode satisfies, in \(\mathcal D'((0,\infty);\mathcal H)\),

\[
\mathcal N F=\partial_LG_{\rm phys}+H_{\rm phys}
\quad\hbox{on the literal interior support}.             \tag{7}
\]

After applying \(M\), the complete equation is

\[
\mathcal N(MF)=\partial_LG_{\rm tot}+H_{\rm tot},         \tag{8}
\]

with exact signs

\[
\begin{aligned}
G_{\rm tot}
 &=M G_{\rm phys}+[C,M]F,\\
H_{\rm tot}
 &=M H_{\rm phys}
   +M'\bigl[(2L I+C)F-G_{\rm phys}\bigr]
   +[Z,M]F.                                              \tag{9}
\end{aligned}
\]

No derivative of \(F\) occurs in either source datum in (9).

If the aperture has finite prime-log recurrence type, then for every fixed \(0<\sigma<1\) one can
choose \(\kappa\) so that

\[
e^{\sigma L}G_{\rm tot},
\ e^{\sigma L}H_{\rm tot}
 \in L^2((0,\infty);\mathcal H).                         \tag{10}
\]

Thus the literal two-coset completed source enters the already-proved primitive-flux graph.
The former literal infinite paired-source assembly gate is closed. Remaining work is not
assembly: one must prove arbitrary finite-order expansion of this exact solution, isolate its
all-orders-flat residual, and invoke the proved flat primitive-flux Liouville theorem.

## 2. Correct rooted prime transport

The earlier conjecture card wrote the same valuation direction on both endpoint cosets. That is
false coordinatewise. From (1),

\[
\begin{aligned}
x_{+,\nu}-\ell(s)&=x_{+,\nu+s},\\
x_{-,\nu}-\ell(s)&=x_{-,\nu-s}.                          \tag{11}
\end{aligned}
\]

Equivalently, if \(\epsilon=+1\) for the right root and \(\epsilon=-1\) for the left root,

\[
x_{\epsilon,\nu}-\ell(s)=x_{\epsilon,\nu+\epsilon s}.   \tag{12}
\]

This sign is invisible only after summing a symmetric prime pair: replacing \(s\) by \(-s\)
leaves the full adjacency unchanged. It is load-bearing for marked descendants and center
constants.

For either puncture orientation \(o\), (12) gives the exact decomposition

\[
\begin{aligned}
u(x_{\epsilon,\nu}+oe^{-L}-\ell(s))
={}&u(x_{\epsilon,\nu+\epsilon s}+oe^{-L})
     -u(x_{\epsilon,\nu+\epsilon s})\\
 &+u(x_{\epsilon,\nu+\epsilon s}),                       \tag{13-}\\
u(x_{\epsilon,\nu}+oe^{-L}+\ell(s))
={}&u(x_{\epsilon,\nu-\epsilon s}+oe^{-L})
     -u(x_{\epsilon,\nu-\epsilon s})\\
 &+u(x_{\epsilon,\nu-\epsilon s}).                       \tag{13+}
\end{aligned}
\]

The first two terms are precisely centered descendant profiles. Final center values are constant
in \(L\) and disappear under distributional differentiation. With weight included, ratios
\(w(\nu)/w(\nu\pm\epsilon s)\) are the bounded nonnormal shifts already constructed in the
tempered-orbit theorem. Since Suzuki's visible prime block is symmetric in \(\pm s\), total
operator \(T_{a,\lambda,\kappa}\) is identical on both rooted cosets even though its
coordinatewise derivation uses opposite directions.

This is the missing exact sign bookkeeping.

## 3. Canonical cutoff and event geometry

Expanding (4) using \(e^Le^{-L}=1\) gives

\[
A^R=e^L(a-x_{\epsilon,\nu})-o,\qquad
A^L=e^L(a+x_{\epsilon,\nu})+o.                           \tag{14}
\]

Because \(e^L>0\) and \(\vartheta(t)\ne0\) exactly for \(t>0\),

\[
\chi(L)\ne0
\Longleftrightarrow
a-s(L)>0\ \hbox{and}\ a+s(L)>0
\Longleftrightarrow
s(L)\in(-a,a).                                           \tag{15}
\]

This proves literal support rather than assuming an adapted cutoff exists.

On support of \(\vartheta'(A^R)\), one has \(0<A^R<1\), and (14) gives

\[
\frac{dA^R}{dL}=e^L(a-x_{\epsilon,\nu})=A^R+o.
\]

Hence \(|(A^R)'|\le2\). Similarly, on support of \(\vartheta'(A^L)\),

\[
\frac{dA^L}{dL}=e^L(a+x_{\epsilon,\nu})=A^L-o,
\]

so \(|(A^L)'|\le2\). Fixed smooth transition has bounded derivative; product rule proves the
uniform derivative bound.

A transition requires \(e^L|a\mp x_{\epsilon,\nu}|\) in a fixed compact subinterval of
\((0,\infty)\), proving (5). Each factor transitions once, so each coordinate has at most two
unit-scale event blocks. Exact root distances equal zero and give constant factors: physical
exterior orientation has argument \(\le0\), while interior orientation has argument at least one
on the terminal ray.

The cutoff is source-derived and canonical up to harmless choice of \(\vartheta\); no
coordinate-dependent shrinking spatial chart is introduced.

## 4. Coordinatewise physical equation

Use Suzuki's exact weak equation in normalization fixed in the polar-source card:

\[
\frac12L_\Delta u
=[\lambda+\log(2\pi)]u
 +\sum_{n\le e^{2a}}\frac{\Lambda(n)}{\sqrt n}
   \bigl[u(\,\cdot-\log n)+u(\,\cdot+\log n)\bigr]
 +K_au.                                                  \tag{16}
\]

At rooted center \(x_{\epsilon,\nu}\), split logarithmic kernel into fixed window
\((x_{\epsilon,\nu}-1,x_{\epsilon,\nu}+1)\) and complement. Paired fixed-window theorem is exact
in distributions and gives, for two puncture orientations,

\[
[2L+q(L)]F-\int_0^L F+RF-CJF.                            \tag{17}
\]

Equation (13) turns finite prime sum into bounded rooted weighted adjacency plus an
\(L\)-constant center vector. Scalar center values are likewise constant. Polar convolution and
fixed-window complement are Lipschitz in physical position; after
\(x=x_{\epsilon,\nu}+oe^{-L}\), centered profiles and derivatives are \(O(e^{-L})\).

If full profile is replaced by matched high-frequency carrier, low-frequency theorem contributes
exactly two physical endpoint constants plus same subcritical rate. This optional replacement is
not needed for full physical profile used in (2).

Differentiate (17) distributionally. Keep

\[
(qF)'=\partial_L(qF)
\]

as primitive source instead of treating \(qF'\) as zero-order datum. Put centered Lipschitz
corrections into \(G_{\rm phys}\), and their absolutely continuous derivatives, if not kept
primitive, into \(H_{\rm phys}\). This gives (7). It uses no derivative of \(u\): derivative of
\(F\) is distributional unknown on operator side.

Equation is valid wherever sample lies in \((-a,a)\). By (15), multiplication by \(M\) uses it
only there.

## 5. Exact primitive assembly

For smooth profiles first, let dot denote \(\partial_L\). Since \(C\) commutes with
\(\partial_L\),

\[
\mathcal N(MF)-M\mathcal N F
 =\partial_L([C,M]F)+M'(2LI+C)F+[Z,M]F.                 \tag{18}
\]

Also,

\[
M(\partial_LG_{\rm phys})
 =\partial_L(MG_{\rm phys})-M'G_{\rm phys}.              \tag{19}
\]

Insert (7) into (18), use (19), and obtain exactly (8)--(9). Physical primitive is multiplied
before differentiation, so event term is \(-M'G_{\rm phys}\), already included in bracket in
(9).

For weak completed modes, (18)--(19) hold in distributions. \(F\) is locally
\(\mathcal H\)-bounded by (3), \(M,M'\) are bounded coordinate multipliers, \(C\) is used in its
Gamma graph sense, and identity is distributional product rule. No unknown spatial derivative
norm is invoked.

## 6. Infinite Hilbert assembly

Fix scalar test function \(\phi\in C_c^\infty(0,\infty)\) and finitely supported carrier test
vector \(z\). Only finitely many coordinates occur, so coordinatewise distribution identities
from Section 4 may be summed without exchange of infinite sums or integrals.

Resulting pairing is bounded in \(z\):

- (3) controls \(F\);
- \(T_{a,\lambda,\kappa}\) is bounded by exact weighted prime-intertwining theorem;
- \(K\) is bounded by logistic \(L^1\) norm;
- local Gamma graph term is recovered from literal undifferentiated equation (17);
- fixed-window and polar sources have bounds stated above.

Finitely supported vectors are dense in \(\mathcal H\). Therefore finite-coordinate identity
extends uniquely to every \(z\in\mathcal H\), precisely (8) in
\(\mathcal D'((0,\infty);\mathcal H)\). This is direct-sum proof, not assumption that
coordinatewise weak equations automatically define a Bochner equation.

## 7. Weighted source estimate

Every transition time in (5) is one of two elementary families

\[
-\log|\ell(\nu)|+O(1),\qquad
-\log|2a-\ell(\nu)|+O(1).                                \tag{20}
\]

First is at most linear in \(|\nu|_1\) by rational separation. At finite recurrence type, second
is also at most linear. On a transition block:

- \(F\) is bounded by \(2w_\kappa(\nu)\|u\|_\infty\);
- \(M'\) is uniformly bounded;
- \((2L+C)F\) is polynomially bounded by solving (17) for \(RF\);
- prime, Gamma, and logistic commutators have exponentially decaying off-block kernels;
- physical source terms have at most fixed polynomial in event time.

Consequently, for each fixed source polynomial degree \(N\),

\[
\sum_\nu
 e^{-2\kappa|\nu|_1}
 e^{2\sigma\tau_\nu}(1+\tau_\nu)^N<\infty               \tag{21}
\]

after choosing \(\kappa\) larger than finite recurrence slope times \(\sigma\), with fixed margin
for finite prime steps. Same estimate controls exponentially decaying off-block tails by
convolution in block index. Away from event blocks, only already-proved polar, far-window, and
\(q\) rates remain, all valid for \(\sigma<1\). This proves (10).

## 8. Source moment and marked descendants

Rooted sign correction does not change Suzuki's symmetric prime adjacency, but prevents false
identification of individual marked descendants. Formula (13) retains every descendant center
constant until differentiation.

At interior center, complete undifferentiated right-hand side of (16) is continuous: \(u\) and
every translate of \(u\) are continuous, while polar and far-window blocks are locally Lipschitz.
Hence two puncture limits agree. Paired dipole theorem applies to actual physical equation and
kills antisymmetric order-one coefficient. Cutoff cannot create physical dipole:
(18)--(19) are exact identities, and every artificial event term is paired with its primitive
commutator in (9).

At physical roots, one-sided half-log coefficient is genuine signed trace. When it vanishes,
proved physical endpoint indicial theorem and automatic flat-flux charge theorem kill order-one
dipole and terminal charge. Assembly introduces no new matching premise. It still does not prove
that arbitrary completed mode has inverse-log expansion.

## 9. Hostile audit

1. **Source support proved.** Equation (15), not informal adapted cutoff, prevents use of interior
   equation outside \((-a,a)\).
2. **Left-coset sign corrected.** Individual descendants use \(\nu-s\) on left and \(\nu+s\) on
   right. Symmetry is invoked only after both prime directions are retained.
3. **Center values retained.** They vanish only after distributional differentiation.
4. **No derivative circularity.** Cutoff defects in (9) contain \(F\), \(CF\), or physical sources,
   never event-supported \(F'\).
5. **No illegal infinite evaluation.** State is \(\ell^2\) family of actual scalar samples;
   distribution equation is first tested on finite carrier support and extended by density.
6. **No hidden Bochner Plancherel step.** Physical carrier does not exchange
   \(L^2(\ell^1)\) and \(\ell^1(L^2)\).
7. **No recurrence overclaim.** Estimate (10) is proved only for finite recurrence type.
8. **No expansion smuggling.** Assembly supplies exact equation and source class, not conormal
   expansion or flatness.
9. **No RH claim.** Even finite-type trace-zero \(H^1_0\) leaves exceptional apertures, completed
   Evans injectivity, nonzero-trace return, raw Evans positivity, and rest of Route O.

## 10. Novelty boundary

Coordinatewise Hilbert distribution assembly and smooth step cutoffs are classical separately.
Candidate-new knowledge is their exact source-faithful conjunction for Suzuki's completed
restricted-Weil equation:

\[
\text{oppositely oriented endpoint cosets}
\to\text{correct marked prime descendants}
\to\text{canonical literal-support cutoff}
\to\text{primitive event source with exact signs}
\to\text{finite-recurrence weighted Hilbert equation}.  \tag{22}
\]

Sign correction (11), cutoff (4), and total source split (9) are absent from Suzuki's source paper
and predecessor corpus. External priority remains unverified.

## 11. Lean certificate

SuzukiLiteralPairedSourceAssembly.lean proves unconditionally:

- suzukiSeamLocation_add_sourceOrientedStep and
  suzukiSeamLocation_sub_sourceOrientedStep: exact root-dependent transport;
- suzuki_primeTranslate_sub_centered and
  suzuki_primeTranslate_add_centered: exact marked-descendant plus center decomposition;
- suzukiRightScaleBufferArgument_eq and
  suzukiLeftScaleBufferArgument_eq: affine event-time formulas;
- suzukiScaleBufferedCutoff_ne_zero_iff: literal aperture support;
- literalPairedCutoffSourceAssembly_pointwise: complete physical-plus-cutoff source identity,
  including uncut residual and sign \(-M'G\).

Vector-valued distribution extension and weighted Gamma estimates remain paper analysis; no Lean
wrapper assumes them.

## Gates

- [x] correct left/right rooted prime-transport signs
- [x] retain every marked-descendant center constant
- [x] construct one canonical smooth cutoff supported exactly in physical aperture
- [x] prove uniform event width and recurrence-time classification
- [x] derive exact primitive and zero-order source signs
- [x] assemble both rooted cosets first on finite carrier tests
- [x] extend by density to weighted Hilbert distribution equation
- [x] prove finite-recurrence Gamma-strip source bounds
- [x] formalize unconditional rooted, cutoff-support, and source-algebra core
- [ ] formalize vector-valued distribution extension and analytic weighted estimates
- [ ] prove arbitrary finite-order expansion of every assembled completed mode
- [ ] isolate and annihilate all-orders-flat residual
- [ ] obtain finite-type trace-zero \(H^1_0\)
- [ ] pass recurrence-infinite apertures
- [ ] prove raw Evans positivity or whole-Route-O no-go

