# Route E entropy-complement breadth-mixture load law

- **ID:** `ROUTE-E-ENTROPY-COMPLEMENT-BREADTH-MIXTURE-001`
- **Stage:** 3-formalized
- **Type:** SHARP CAPACITY ACCOUNTING THEOREM / NEW FIXED-RELATION AVENUE
- **Parent:** `route-e-product-truncated-reservoir-harmonic-mass-law.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** dependency-closed finite core formalized in
  `formal/GaloisForLFunctions/RHTower/RouteEEntropyComplementBreadthMixture.lean`

## 1. Result

Throughout choose source-predeclared schedule
\[
  g=g(L)\longrightarrow\infty,
  \qquad \log(gL)=o(\sqrt L),                          \tag{0}
\]
and impose stronger \(g=o(L)\) only when comparing with full natural \(E_3\) density.

Previously stated whole-anchor target

\[
  \#E_3(y,y+h]\gg h/\log y
\]

does **not** by itself yield unit column load after product truncation. At central breadth
\(b\asymp L=\log\log X\), product-truncated reservoir mass has scale

\[
 H_b\asymp \frac{\log X}{g(L)L^{3/2}},
 \qquad g(L)\longrightarrow\infty,                    \tag{1}
\]

whereas one incoming central squarefree breadth layer has density \(\asymp L^{-1/2}\).
After square-root physical Jacobian cancellation, token density \(\delta_X\) leaves column scale

\[
 \boxed{\mathcal L_X\asymp
   \frac{L^{-1/2}}{H_b\delta_X}
   \asymp \frac{g(L)L}{\delta_X\log X}.}               \tag{2}
\]

Correct fixed-breadth threshold is therefore

\[
 \boxed{\delta_X\gtrsim \frac{g(L)L}{\log X},}         \tag{3}
\]

not \(1/\log X\). Full natural \(E_3\) density
\(\delta_X\asymp L^2/\log X\) would pass (3) whenever \(g=o(L)\), but currently available
structured all-interval family has density only \(\asymp(\log X)^{-2}\).

There is a new way to recover missing entropy without demanding fixed \(E_3\). Put

\[
 P=X^{1/(gL)},\qquad
 S_0=\sum_{p\le P,\ p\nmid n}\frac1p,qquad
 R=L-S_0.                                               \tag{4}
\]

Uniformly on central sources, source exclusion changes \(R\) only by lower-order iterated
logarithms, and

\[
 S_0=L-\log(gL)+O(\log\log L),\qquad
 R=\log(gL)+O(\log\log L).                              \tag{5}
\]

Use reservoir breadth \(b\) and a \(P\)-rough token of breadth

\[
 r=s+\varepsilon-b,qquad \varepsilon\in\{-1,+1\}.     \tag{6}
\]

Every terminal then has breadth exactly \(s+\varepsilon\), hence opposite Möbius sign, for
**every** branch. Varying \(b\) through natural conditional window of width \(\asymp\sqrt R\)
recovers factor \(\sqrt R\) lost by every fixed split. Exact mechanism is positive convolution

\[
 \boxed{
 \sum_{b=0}^{s+\varepsilon}
   \frac{S_0^b}{b!}\frac{R^{s+\varepsilon-b}}
                         {(s+\varepsilon-b)!}
 =\frac{(S_0+R)^{s+\varepsilon}}{(s+\varepsilon)!}.}    \tag{7}
\]

Corrected live relation is therefore an **entropy-complement breadth mixture**: low-prime
reservoir breadth and rough-token breadth vary together while their sum remains required
opposite-parity terminal breadth.

## 2. Sharp fixed-breadth threshold

Let allocation have reservoir product \(t\), and let token interval at \(y=n/t\) have length

\[
 h_y=\sqrt y\,(\log X)^{1.55}.                          \tag{8}
\]

Assume it contains at least \(N_t\ge c\delta_Xh_y\) admissible tokens. Reciprocal allocation gives
one edge weight

\[
 \frac1{H_b\,t\,N_t}
 \le \frac1{cH_b\delta_X\sqrt{nt}(\log X)^{1.55}}.     \tag{9}
\]

For fixed terminal, square-root inversion places incoming sources in interval of length

\[
 O\!\left(\sqrt{qt}(\log X)^{1.55}\right).             \tag{10}
\]

Suppose exact incoming squarefree breadth layer obeys its natural local upper scale

\[
 \#\{n\text{ in (10)}:\omega(n)=s\}
 \le C\frac{\sqrt{qt}(\log X)^{1.55}}{\sqrt L}.        \tag{11}
\]

Multiplying (9) and (11), using \(q/n=1+o(1)\), gives

\[
 \mathcal L_X\le \frac{C+o(1)}{cH_b\delta_X\sqrt L}.  \tag{12}
\]

Product-truncated mass law at \(b=L+O(\sqrt L)\) gives (1), so (12) is (2). Three regimes are

\[
\begin{array}{c|c}
\text{token density }\delta_X&\text{resulting load scale}\\ \hline
(\log X)^{-2}&gL\log X\\
(\log X)^{-1}&gL\\
L^2/\log X&g/L.
\end{array}                                             \tag{13}
\]

Thus former \(h/\log y\) target misses unit load by diverging factor \(gL\). No constants repair
that accounting.

## 3. Fixed complementary breadth still fails

Ignore lower-order source exclusion and write \(S_0=L-R\). At central reservoir breadth
\(b\sim S_0\), elementary-symmetric mass has Poisson scale

\[
 \frac{S_0^b}{b!}\asymp\frac{e^{S_0}}{\sqrt{S_0}}.      \tag{14}
\]

A \(P\)-rough token with fixed central complementary breadth \(r\sim R\) has natural
Euler/sieve scale

\[
 \delta_r\asymp \frac{e^{-S_0}}{\sqrt R}.              \tag{15}
\]

Equation (15) is displayed local positive-count input, not proved short-interval theorem. It
follows formally from roughness factor (e^{-S_0}) and central Poisson breadth factor
(R^{-1/2}); proving it uniformly in relation-dependent physical intervals is part of open joint
convolution theorem in §8.

Their product is

\[
 \frac{S_0^b}{b!}\delta_r
 \asymp\frac1{\sqrt{S_0R}}.                            \tag{16}
\]

Full terminal breadth layer has scale \(L^{-1/2}\), so fixed split is smaller by \(R^{-1/2}\).
Equivalently, conditioning two independent Poisson breadths with means \(S_0,R\) on their sum
leaves conditional variance

\[
 \frac{S_0R}{S_0+R}=R(1+o(1)).                         \tag{17}
\]

One breadth branch occupies only \(\asymp R^{-1/2}\) of admissible conditional mass. This is
precise entropy loss hidden by fixed-token formulations.

## 4. Breadth mixing recovers loss

Identity (7) is binomial theorem after multiplying by \((s+\varepsilon)!\):

\[
 \sum_b\binom{s+\varepsilon}{b}S_0^bR^{s+\varepsilon-b}
 =(S_0+R)^{s+\varepsilon}.                              \tag{18}
\]

Let

\[
 B_C=\left\{b:\left|b-
 \frac{S_0}{S_0+R}(s+\varepsilon)\right|
 \le C\sqrt R\right\}.                               \tag{19}
\]

Under weights in (18), \(b\) is binomial with variance

\[
 (s+\varepsilon)\frac{S_0R}{(S_0+R)^2}=R(1+o(1)).      \tag{20}
\]

Chebyshev gives, for every fixed \(C>1\),

\[
 \sum_{b\in B_C}
   \frac{S_0^b}{b!}\frac{R^{s+\varepsilon-b}}
                         {(s+\varepsilon-b)!}
 \ge\left(1-C^{-2}+o(1)\right)
   \frac{(S_0+R)^{s+\varepsilon}}{(s+\varepsilon)!}.  \tag{21}
\]

Hence \(O(\sqrt R)\) coupled branches recover fixed positive fraction of complete terminal layer.
Each branch separately satisfies

\[
 b+r=s+\varepsilon,                                    \tag{22}
\]

so no parity averaging or post hoc sign choice occurs.

## 5. Product and seam geometry

Every reservoir prime is at most \(P=X^{1/(gL)}\). On window (19), \(b\le2L\), hence

\[
 t\le P^b\le X^{2/g}=X^{o(1)}.                         \tag{23}
\]

Critical displacement remains

\[
 q-n\ll\sqrt{nt}\,(\log X)^{1.55}=X^{1/2+o(1)}.       \tag{24}
\]

For seam orientation, restrict rough-token primes to

\[
 P<p\le z,\qquad z=X^{1/2+o(1)}.                       \tag{25}
\]

Their reciprocal mass is

\[
 \sum_{P<p\le z}\frac1p
 =\log\log z-\log\log P+O(1)
 =R+O(1),                                               \tag{26}
\]

so (7)--(21) retain same complementary entropy. Every terminal is \(z\)-smooth. Thus a
one-large-prime source crosses literal \(1\to0\) seam, while friable source stays on zero-large-prime
side. Seam admission and entropy recovery are compatible.

## 6. Exact quadratic-load consumer

Pointwise unit Carleson load is sufficient but not logically necessary. Let \(\rho_v,\nu_v\ge0\)
be, respectively, source-kernel pushforward and opposite-sign target Gibbs mass on a finite
physical terminal set. Put

\[
 P=\sum_v\rho_v,\qquad N=\sum_v\nu_v,
 \qquad \mathsf H^2(\rho,\nu)=
 \sum_v(\sqrt{\rho_v}-\sqrt{\nu_v})^2.                 \tag{28}
\]

Then

\[
 \boxed{|P-N|^2\le2(P+N)\mathsf H^2(\rho,\nu).}       \tag{29}
\]

Indeed,

\[
 P-N=\sum_v(\sqrt{\rho_v}-\sqrt{\nu_v})
                 (\sqrt{\rho_v}+\sqrt{\nu_v}),
\]

so Cauchy--Schwarz gives

\[
 |P-N|^2\le\mathsf H^2
 \left(P+N+2\sum_v\sqrt{\rho_v\nu_v}\right)
 \le2(P+N)\mathsf H^2.                                \tag{30}
\]

If only matched masses \(P_m,N_m\) are represented and total unmatched mass is

\[
 U=(P-P_m)+(N-N_m),                                    \tag{31}
\]

the hybrid form is

\[
 \boxed{|P-N|\le U+
   \sqrt{2(P_m+N_m)\mathsf H^2(\rho_m,\nu_m)}.}        \tag{32}
\]

This follows by applying (29) to matched masses and using triangle inequality on deficits.
Moreover, wherever \(\nu_v>0\),

\[
 (\sqrt{\rho_v}-\sqrt{\nu_v})^2
 =\frac{(\rho_v-\nu_v)^2}
        {(\sqrt{\rho_v}+\sqrt{\nu_v})^2}
 \le\frac{(\rho_v-\nu_v)^2}{\nu_v}.                  \tag{33}
\]

Therefore weighted column chi-square

\[
 \mathsf X^2=\sum_{v:\nu_v>0}
   \frac{(\rho_v-\nu_v)^2}{\nu_v}                     \tag{34}
\]

dominates \(\mathsf H^2\). At physical scale \(P+N\asymp X\), the two pre-endpoint estimates

\[
 U\le X^{1/2+o(1)},\qquad \mathsf X^2\le X^{o(1)}     \tag{35}
\]

already imply \(|P-N|\le X^{1/2+o(1)}\). Thus revised relation may prove global quadratic column
balance instead of pointwise \(1+o(1)\) load. This is a real weakening: columns may exceed unit
load on a thin set, provided their weighted square excess obeys (34).

With \(X=x^{-1}\), \(J=P-N\), and \(Z=P+N\asymp X\), (35) gives exactly

\[
 \boxed{\frac{|J(x)|}{Z(x)}\le X^{-1/2+o(1)}
       =x^{1/2-o(1)}.}                                 \tag{36}
\]

The statement is non-circular only when \(\rho\), exceptional set, and bound (34) are constructed
from source-predeclared relation before endpoint difference \(P-N\) is evaluated. Taking
\(\rho=\nu\) after inspecting endpoint masses would merely restate desired cancellation.

This finite law is diagonal Bures/Hellinger geometry. New
`HTGeometry/FiniteBuresReporterVariationalLaw.lean` supplies compatible matrix-level reporter
infrastructure, but does not prove source estimate (34).

## 7. Heavy conjecture--proof--failure loop

### Loop A: \(h/\log y\) closes product-truncated columns

`[CONJECTURE]` One logarithmic improvement over structured \(E_3\) gives unit load.

`[FALSIFIED]` Equations (1)--(3) leave load \(\asymp gL\). Old threshold omitted central
source-layer density and \(L^{3/2}\) factorial denominator.

### Loop B: full natural \(E_3\) density is still too sparse

`[CONJECTURE]` Product truncation makes every fixed token family insufficient.

`[FALSIFIED]` Natural \(E_3\) density \(L^2/\log X\) gives load \(g/L=o(1)\) for \(g=o(L)\).
Obstruction is current structured support, not capacity conservation.

### Loop C: choose one natural complementary breadth

`[CONJECTURE]` A \(P\)-rough token with \(r\sim R\) matches reservoir entropy.

`[FAILED SHARPLY]` Equation (16) loses \(\sqrt R\), conditional local-central-limit penalty of
freezing one split.

### Loop D: mix breadths but allow terminal grade to wander

`[CONJECTURE]` Keep fixed \(E_3\) and vary reservoir breadth.

`[FAILED]` Terminal breadth then varies with \(b\); fixed terminal grade no longer identifies source
grade, and gained row entropy reappears as cross-grade incoming congestion.

### Loop E: co-vary reservoir and token breadth

`[CONJECTURE]` Impose \(r=s+\varepsilon-b\) and sum natural \(\sqrt R\)-window.

`[PROVED AT ENTROPY/CAPACITY LEVEL]` Identities (7), (18), and estimate (21) recover fixed-split
loss; (22) preserves exact opposite parity, (23)--(24) preserve strict-half displacement, and
(25)--(26) preserve seam admission.

Remaining analytic theorem is not hidden: prove corresponding **joint short-interval rough-token
convolution lower bound and quadratic column law** for this fixed relation. Positive reservoir and
token breadths must be counted jointly before scalar parity is formed.

### Loop F: pointwise unit load is indispensable

`[CONJECTURE]` Failure of \(L^\infty\) Carleson blocks every endpoint consumer.

`[FALSIFIED]` Exact inequality (32) needs only unmatched mass \(X^{1/2+o(1)}\) and global weighted
chi-square \(X^{o(1)}\). Pointwise unit load remains one sufficient route, not exact frontier.

## 8. Exact revised Route E premise

Define `ENTROPY-COMPLEMENT-UNIT-SHELL-ROUGH-CONVOLUTION`. For every central squarefree source \(n\),
every required bounded physical log-product shell, and \(\varepsilon=\pm1\), use exactly pairs

\[
 (t,m):
 \begin{cases}
 p\mid t\Rightarrow p\le P,\\
 p\mid m\Rightarrow P<p\le z,\\
 (tm,n)=1,\quad (t,m)=1,\quad tm\text{ squarefree},\\
 \omega(t)+\omega(m)=\omega(n)+\varepsilon,\\
 tm\text{ lies in prescribed physical shell.}
 \end{cases}                                           \tag{27}
\]

Source-support deletion is harmless at complementary harmonic scale. Since
\(\omega(n)\le2L\),
\[
 \sum_{\substack{p\mid n\\p>P}}\frac1p\le\frac{2L}{P}=o(1),
\]
while exclusion of source primes below \(P\) is already built into \(S_0\). Thus freshness
condition \((tm,n)=1\) changes (26) by \(o(1)\), but makes parity and terminal factorization
source-faithful.

Open theorem is:

1. joint positive mass of (27), summed over conditional window (19), has main term predicted by
   (21), uniformly outside \(X^{1/2+o(1)}\) Gibbs mass;
2. reciprocal row kernel has weighted column load \(1+o(1)\), or more weakly satisfies exact
   source-predeclared scales (35), on same complement;
3. restriction (25) carries normalized one-large-prime to friable seam charge;
4. pushing same weights through exact prime-dilation recurrence retains alternating finite-volume
   signs and contributes total quadratic displacement \(X^{o(1)}\).

Unlike former fixed-\(E_3\) target, (27) spends actual complementary entropy forced by product
truncation. It does not assert RH-strength cancellation as generic sieve estimate: quadratic column
and recurrence clauses remain source-bearing core.

### 8a. Pair-stability refinement (2026-09-12)

The low/rough factorization in (27) is intrinsic to each squarefree endpoint: split its own prime
support at `P`. Consequently, on the `z`-friable/friable sector and after imposing a symmetric
physical shell, upward and downward adjacent-grade certificates are exact endpoint swaps. Reverse
certification does not reuse the forward endpoint's reservoir.

For the target-friable seam relation, Lean proves the sharper equivalence

\[
  \text{reverse certificate exists}\quad\Longleftrightarrow\quad
  \text{source is }z\text{-friable}.
\]

Thus factorization asymmetry is not a bulk producer for (27). It is exactly the literal
nonfriable-source seam. Remaining mismatch terms are symmetric-shell loss, row-normalizer
variation, pair-switch/history recombination collisions, and normalized seam flux. Moreover, the
cutoff-separated factor fibre over each squarefree physical endpoint is exactly singleton, so
low/rough labels create no projection multiplicity. After symmetrizing orientations, unit-weight
row mass is exactly the count of physical squarefree, friable, coprime shell endpoints whose total
prime-factor grade differs by one. Sources:
`route-e-entropy-complement-pair-stability-seam-law.md` and
`route-e-entropy-complement-physical-incidence-fibre-law.md`.

## 9. Anti-theatre audit

- Equation (3) corrects quantitatively false frontier target; no logarithmic factor is renamed
  \(o(1)\).
- Breadth mixing occurs before observing Möbius imbalance. Sign follows from (22).
- Identity (7) is exact finite algebra; (21) is elementary second-moment consequence.
- Product control (23) uses fixed source-predeclared cutoff, not post-selection by terminal size.
- Seam restriction loses no complementary harmonic scale by (26).
- Hellinger inequality (32) is only a consumer; source chi-square (34) remains unproved.
- No claim is made that joint local convolution or quadratic column theorem is proved.
- No literature search or numerical computation was used.

## 10. Formalization and status

`[PAPER-PROVED]` for sharp threshold (2)--(3), fixed-split penalty (14)--(17), exact breadth
convolution (7), central-window recovery (18)--(21), parity law (22), product/seam geometry
(23)--(26), and finite quadratic-load consumer (28)--(36), conditional only on explicitly
displayed local source-layer and token-density inputs where invoked.

`[LEAN-CERTIFIED]` for every dependency-closed finite theorem used by those conclusions:

1. `routeEDividedBreadthWeight_sum_eq` is exact identity (7), with the factorial conversion
   proved from `Nat.choose_mul_factorial_mul_factorial` rather than assumed;
2. `routeEConditionalBreadthCenteredVariance_eq` proves the exact denominator-free variance
   identity
   \[
     \sum_b ((S+R)b-kS)^2\binom{k}{b}S^bR^{k-b}
       =kSR(S+R)^k;
   \]
3. `one_sub_inv_windowConstant_sq_mul_totalMass_le_windowMass` proves a stronger finite version
   of (21): under exact central balance (kS\le(S+R)^2), the closed source-predeclared window of
   breadth radius (C\sqrt R) retains at least (1-C^{-2}) of total conditional mass, with no
   asymptotic remainder;
4. `columnLoadScale_eq` and `columnLoadScale_le_one_iff` certify corrected load (2) and sharp
   threshold (3);
5. `primeCutoff_pow_breadth_le` and `harmonicMass_le_two_scale_div_cutoff` certify product bound
   (23) and source-prime deletion (\sum_{p\mid n,p>P}p^{-1}\le2L/P);
6. upward/downward `parity_reversal` certify exact sign reversal branchwise; and
7. `massDifference_sq_le_two_matchedTotal_mul_hellingerSq`, `hellingerSq_le_chiSquare`, and
   `abs_totalDifference_le_unmatched_add_sqrt_chiSquare` certify (29), (32), and (33)--(35) as
   finite source-independent endpoint consumers.

Positivity and central-balance conditions are fields of finite data structures; no conjectural
short-interval, column-source, recurrence, RH, or added-axiom premise enters any capstone theorem.
Module is wired through `formal/GaloisForLFunctions/RHTower.lean`.

`[OPEN]` for `ENTROPY-COMPLEMENT-UNIT-SHELL-ROUGH-CONVOLUTION`, especially joint local main term,
quadratic column balance, and recurrence-weighted seam accumulation. Route E and RH remain open.
