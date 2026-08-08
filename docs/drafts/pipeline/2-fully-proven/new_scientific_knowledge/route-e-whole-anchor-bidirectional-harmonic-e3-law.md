# Route E whole-anchor bidirectional harmonic \(E_3\) law

- **ID:** ROUTE-E-WHOLE-ANCHOR-HARMONIC-E3-001
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NEW PHYSICAL RELATION / POLYLOG-CARLESON REDUCTION
- **Parent:** route-e-reciprocal-allocation-square-root-jacobian-carleson-reduction.md
- **Source:** OPEN-SOURCE-001
- **RH used:** no
- **Computation used:** no
- **Lean status:** intentionally not started during corpus refactor

## 1. Result

Block decomposition is unnecessary for opposite-sign half-density admission.  Replace whole
central squarefree anchor by one reservoir times one structured \(E_3\) token.

Put

\[
 L=\log\log X,\quad
 W=\exp(\exp\sqrt L),\quad
 Z=\exp\!\left(\frac{\log X}{L^2}\right),\quad
 {\cal P}_X=\{p:W<p\le Z\}.                             \tag{1}
\]

Let \(n\in[X,2X]\) be squarefree with
\[
 \frac12L\le s:=\omega(n)\le2L.                         \tag{2}
\]
For either \(\varepsilon\in\{+1,-1\}\), put
\[
 b_\varepsilon=s-3+\varepsilon
 =\begin{cases}s-2,&\varepsilon=+1,\\s-4,&\varepsilon=-1.
 \end{cases}                                            \tag{3}
\]
For every set
\[
 R\subseteq{\cal P}_X\setminus\operatorname{supp}(n),
 \qquad \#R=b_\varepsilon,\qquad t_R=\prod_{p\in R}p,   \tag{4}
\]
apply sparse-forbidden all-interval \(E_3\) theorem at \(y_R=n/t_R\).  For every admitted
squarefree three-prime token
\[
 y_R<m\le y_R+\sqrt{y_R}(\log y_R)^{1.55},             \tag{5}
\]
coprime to \(nR\), set \(q=t_Rm\).  Then
\[
 \boxed{
 \omega(q)=s+\varepsilon,\qquad
 \mu(q)=-\mu(n),\qquad
 0<q-n\le\sqrt{nt_R}(\log X)^{1.55}.}
 \tag{6}
\]

Every fixed allocation has \(X^{1/2-o(1)}\) terminals, every terminal has
\(X^{1/2+o(1)}\) incoming anchors, reservoir is uniquely decoded from terminal, and reciprocal
allocation kernel has
\[
 \boxed{
 \sup_q\sum_nP^{\rm whole}_{X,\varepsilon}(n,q)
 \le(\log X)^C}
 \tag{7}
\]
for an absolute \(C\).  Both grade directions obey same moving-seam law and one-edge Gibbs cost
\(X^{-1/2+o(1)}\).  Unit load and normalized seam flux remain open.

## 2. Token scale and exact parity

Since \(b_\varepsilon\le2L\),
\[
 t_R\le Z^{2L}=X^{2/L},\qquad
 y_R\ge X^{1-2/L}.                                     \tag{8}
\]
Thus \(y_R\ge\exp((\log X)^{1/3})\), and forbidden support has \(O(L)\) primes.  Existing theorem
supplies
\[
 N(n,R,\varepsilon)
 \gg\frac{\sqrt{n/t_R}}{(\log X)^{0.45}}               \tag{9}
\]
distinct tokens.  Existing disjoint \(p_1\)-slice aggregation is used after sparse-forbidden
deletion: \(O(L)\) source-predeclared slices fill common interval (5) and cancel single-slice
\(\log\log y_R\) loss.  Also
\[
 \omega(q)=b_\varepsilon+3=s+\varepsilon,
\qquad
 \mu(q)=(-1)^{s+\varepsilon}=-(-1)^s=-\mu(n),          \tag{10}
\]
because \(\varepsilon\) is odd.

## 3. Exact reservoir decoding

Structured token has
\[
 p_1\asymp(\log y_R)^{1.1},\qquad
 p_2,p_3\asymp\frac12\sqrt{\frac{y_R}{p_1}}.            \tag{11}
\]
For large \(X\),
\[
 p_1<W,\qquad p_2,p_3>Z.                               \tag{12}
\]
Indeed \(\log p_1=O(L)\ll\exp\sqrt L=\log W\), while (8) gives
\(\log p_j=(1/2-o(1))\log X\gg\log X/L^2=\log Z\).  Hence
\[
 \boxed{R=\{p\mid q:W<p\le Z\}.}                       \tag{13}
\]
No block, allocation, or structured-factor ambiguity remains.

## 4. Reciprocal kernel and column bound

Define
\[
 H_\varepsilon(n)
 =\sum_{\substack{R\subseteq{\cal P}_X\setminus\operatorname{supp}(n)\\
                   \#R=b_\varepsilon}}\frac1{t_R}
 =e_{b_\varepsilon}
   \left((1/p)_{p\in{\cal P}_X\setminus\operatorname{supp}(n)}\right)
 \tag{14}
\]
and
\[
 P^{\rm whole}_{X,\varepsilon}(n,q)
 =\sum_{\substack{R:q\in{\cal V}_\varepsilon(n,R)}}
  \frac1{H_\varepsilon(n)t_RN(n,R,\varepsilon)}.        \tag{15}
\]
Rows sum exactly one.

Prime reciprocal mass satisfies
\[
 S({\cal P}_X)=L-2\log L-\sqrt L+O(1),                 \tag{16}
\]
so elementary-symmetric law gives
\[
 H_\varepsilon(n)
 =\frac{S({\cal P}_X)^{b_\varepsilon}}{b_\varepsilon!}(1+o(1)).
 \tag{17}
\]
For \(b_\varepsilon/L\in[1/2+o(1),2+o(1)]\), Stirling gives one \(c_0>0\) with
\[
 H_\varepsilon(n)\ge\exp(c_0L).                        \tag{18}
\]

Fix \(q\).  Equation (13) fixes \(R\) and \(t\).  Every incoming \(n\) lies in inverse interval
of length
\[
 O(\sqrt{qt}(\log X)^{1.55}).                          \tag{19}
\]
From (9), one edge has weight at most
\[
 \frac{(\log X)^{0.45}}
 {H_\varepsilon(n)\sqrt{nt}}.                          \tag{20}
\]
Multiplying (19) and (20), using \(q/n=1+o(1)\), gives
\[
 \sum_nP^{\rm whole}_{X,\varepsilon}(n,q)
 \ll\frac{(\log X)^2}{\inf_nH_\varepsilon(n)}
 \le(\log X)^C.                                        \tag{21}
\]
This proves (7).  Reservoir square-root Jacobian cancels and structural assignment factor is gone.

## 5. Gibbs cost and moving seam

At \(x\asymp X^{-1}\),
\[
 |e^{-xq}-e^{-xn}|
 \le x(q-n)
 \le X^{-1/2+1/L}(\log X)^{1.55}
 =X^{-1/2+o(1)}.                                       \tag{22}
\]
No higher cube is required to reach strict-half aggregate scale.

Let \(z/\sqrt X\to\infty\) and \(\log z=(1/2+o(1))\log X\).  Reservoir primes, \(p_1\), and
balanced factors \(p_2,p_3\) are all below \(z\).  Therefore
\[
 \ell_z(n)=1\Longrightarrow
 \ell_z(q)=0,\qquad\mu(q)=-\mu(n).                     \tag{23}
\]
Both grade directions cross same seam.

## 6. Conjecture--proof--failure loops

### Loop A: growing arity is necessary

[CONJECTURE] Product of block gaps is required for strict-half cost.

[FALSIFIED] Whole-anchor reservoir product is \(X^{O(1/L)}\); first difference already has
strict-half scale (22).

### Loop B: whole-anchor reservoir cannot be decoded

[CONJECTURE] Terminal admits too many choices of its \(s+O(1)\) reservoir primes.

[FALSIFIED] Factor separation (12) makes reservoir exact band support (13).

### Loop C: reciprocal weighting closes unit load

[CONJECTURE] Unique decoding plus harmonic normalization makes column load \(1+o(1)\).

[FAILED] Existing structured \(E_3\) theorem, after all available disjoint-slice aggregation,
supplies only \(h/(\log y)^2\) tokens at \(h=\sqrt y(\log y)^{1.55}\).  Bound (21) remains
polylogarithmic and cannot be renamed unit.

### Loop D: replace exact \(E_3\) by natural-density rough \(P_5\)

[CONJECTURE] Lower-bound sieve at level \(h\asymp\sqrt y\) should produce
\(\gg h/\log y\) squarefree integers with at most five prime factors.  Use actual breadth
\(r\le5\) and set reservoir breadth to \(s+\varepsilon-r\).

[FAILED AS STATED] Token interval depends on reservoir product.  Changing reservoir breadth after
observing \(r\) changes \(t\), hence changes \(y=n/t\) and invalidates token.  Running five
reservoir breadths separately gives five different intervals; pigeonhole theorem that some
\(r\le5\) is abundant in each interval does not guarantee fixed point where abundant breadth
equals breadth used to define that interval.  Keeping one reservoir breadth accepts only one
token-parity class and hits sieve parity barrier.  No opposite-sign relation follows.

Positive survivor is exact parity-synchronization target: either natural-density tokens of one
predeclared odd breadth, or a two-stage physical relation whose first natural-density rough step
is followed by capacity-preserving exact sign correction.  Neither is currently proved.

## 7. Exact new frontier

Whole-anchor route reduces fixed relation to

WHOLE-ANCHOR-NATURAL-DENSITY-E3-WOLD-LAYER-CARLESON:

1. prove sparse-forbidden all-interval supply
   \[
   \#E_3(y,y+h]\gg\frac h{\log y},
   \qquad h=\sqrt y(\log y)^{1.55};                    \tag{24}
   \]
2. prove matching upper local law for squarefree layer \(\omega(n)=s\) in inverse intervals
   (19), with constants compatible with harmonic factorial (17);
3. deduce interval unit Hall/Carleson for union of directions \(s\mapsto s\pm1\);
4. prove normalized \(1\to0\) seam flux for same kernel.

Threshold (24) is exactly one logarithmic power denser than current aggregated structured
minorant, but much weaker
than full expected \(E_3\) density.  It is exact amount harmonic layer (17) can convert into modal
Wold capacity.  Existing theorem does not supply it.

This avenue has no multi-coordinate collision.  Open core is one short-interval almost-prime
density law plus one unsigned local Wold-layer law.

Natural-density rough \(P_5\) may replace (24) only together with new parity-synchronization
theorem; raw lower-bound sieve alone is insufficient.

## 8. Scientific and formal status

[PAPER-PROVED] [NOVELTY UNVERIFIED] for relation (3)--(23) and polylogarithmic Carleson reduction
(7).  Natural-density threshold (24), unit load, and seam flux are conjectural.  No external
literature search was performed under current instruction.  No Lean was written or built while
corpus refactor is active.

## 9. 2026-08-08 quantitative correction

Claim in §7 that `(24)` is exact density threshold is false after factorial normalization is
spent sharply. At central breadth, product-truncated reservoir mass is

\[
 H_b\asymp \frac{\log X}{g(L)L^{3/2}},
\]

and incoming exact squarefree breadth layer has density \(\asymp L^{-1/2}\). Square-root Jacobian
cancellation therefore leaves column scale

\[
 \mathcal L_X\asymp\frac{g(L)L}{\delta_X\log X}
\]

for token density \(\delta_X\). Thus \(\delta_X=1/\log X\) leaves divergent factor \(g(L)L\); it
does not imply unit load. Corrected fixed-breadth threshold is
\(\delta_X\gtrsim g(L)L/\log X\). Full natural \(E_3\) density \(L^2/\log X\) would suffice for
\(g=o(L)\), but current structured all-interval support is much thinner.

Positive successor is `route-e-entropy-complement-breadth-mixture-load-law.md`: vary reservoir
breadth and complementary rough-token breadth together across their natural conditional window
while keeping total terminal breadth exactly \(s\pm1\). This correction does not alter proved
relation (3)--(23) or its polylogarithmic column bound; it retracts only claimed sufficiency and
“exactness” of `(24)`.
