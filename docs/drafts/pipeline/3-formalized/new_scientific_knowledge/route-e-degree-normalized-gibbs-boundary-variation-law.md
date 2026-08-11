# Route E degree-normalized Gibbs boundary-variation law

- **ID:** ROUTE-E-DEGREE-NORMALIZED-GIBBS-BV-001
- **Stage:** 3-formalized
- **Type:** [DIRECT SIGNED PRODUCER REDUCTION] / [LEAN-CORPUS SYNTHESIS] /
  [SHARPNESS FIREWALL]
- **Parent:** ../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md
- **Lean basis:** formal/GaloisForLFunctions/RHTower/MobiusBoundaryOppositeSignTransport.lean
- **RH used:** no
- **Computation used:** no
- **Literature used:** no; internal-corpus derivation only
- **Lean status:** exact finite content formalized in umbrella-wired
  `RouteEDegreeNormalizedGibbsBoundaryVariation.lean`.

## 1. Result

Grown Lean corpus exposes direct Route E producer absent from prior frontier map. For any finite
symmetric sign-reversing graph on physical squarefree atoms, canonical degree-normalized
conductance bounds signed Gibbs current by:

1. Gibbs mass of isolated vertices;
2. co-moving Gibbs displacement, automatically strict-half when edge length is strict-half; and
3. one positive reciprocal-degree variation.

Let $V$ be finite set of distinct positive integers, let $n\sim m$ be symmetric adjacency with
no loops, and let $\epsilon_n\in\{-1,+1\}$ satisfy

\[
 n\sim m\Longrightarrow\epsilon_n+\epsilon_m=0.
\tag{1}
\]

Write

\[
 d_n=\#\{m\in V:n\sim m\},
 \qquad w_x(n)=e^{-xn},
 \qquad J_V(x)=\sum_{n\in V}\epsilon_nw_x(n),
 \qquad Z_V(x)=\sum_{n\in V}w_x(n).
\tag{2}
\]

Let $V_{\rm iso}=\{n:d_n=0\}$. If every edge obeys $|n-m|\le H$, define

\[
 \mathcal V_{\deg}(x)
 =\sum_{\{n,m\}:n\sim m,\ n<m}
 e^{-xm}\left|\frac1{d_n}-\frac1{d_m}\right|.
\tag{3}
\]

Then

\[
 \boxed{
 |J_V(x)|
 \le
 \sum_{n\in V_{\rm iso}}e^{-xn}
 +xH Z_V(x)
 +\mathcal V_{\deg}(x).}
\tag{4}
\]

Thus for $x=X^{-1}$, $Z_V(X^{-1})=X^{1+o(1)}$, and
$H=X^{1/2+o(1)}$, Route E closes on this finite aperture if

\[
 \boxed{
 \sum_{n\in V_{\rm iso}}e^{-n/X}
 +\mathcal V_{\deg}(X^{-1})
 \le X^{1/2+o(1)}.}
\tag{5}
\]

More strongly, let $P$ be actual recurrence-compatible nonnegative substochastic kernel, with row
mass $r_n=\sum_mP_{nm}\le1$ and column load $\ell_n=\sum_mP_{mn}$. Symmetrization
$b=(P+P^\mathsf T)/2$ gives weighted degree $(r_n+\ell_n)/2$. Cauchy--Schwarz reduces entire
degree-BV term to edge Dirichlet energy of $q_n=2/(r_n+\ell_n)$ off weighted-isolated set.
Exact nonisolated endpoint target becomes

\[
 \mathcal E_P(X^{-1})
 =\sum_{n<m}\frac{P_{nm}+P_{mn}}2e^{-m/X}(q_n-q_m)^2
 \le X^{o(1)}.
\tag{5a}
\]

This lane does not require separate target normalization, chi-square transfer, universal Fisher
identification, or postselected max-flow. Alternating signs are built into graph, physical
prime-dilation intervals are edge support, and finite-volume/recurrence weights are retained.
Weighted-isolated Gibbs mass is additional explicit residual.

Reduction is sharp in hostile sense. On complete bipartite graph with constant weights,
reciprocal-degree variation is exactly absolute signed imbalance. Therefore (5) is new explicit
positive arithmetic target, not automatic consequence of breadth, row/co-degree exponents, or
co-moving displacement.

## 2. Existing Lean consumer

For nonisolated vertices set

\[
 a_n=\frac{w_x(n)}{d_n}.
\tag{6}
\]

Existing unconditional theorem
abs_sum_sign_weight_le_degreeNormalizedReplacementDefect gives

\[
 |J_V(x)|\le
 \sum_{n\in V_{\rm iso}}w_x(n)
 +\sum_n\sum_{m\sim n}
 \left(a_n-\min(a_n,a_m)\right).
\tag{7}
\]

Lean theorem applies to every finite symmetric parity-flipping adjacency and every nonnegative
vertex weight. Its concrete Möbius specializations already use $w_x(n)=e^{-xn}$ and exact
factor-replacement sign reversal. No analytic premise occurs in (7).

### Theorem A — directed defect is edge total variation

\[
 \boxed{
 \sum_n\sum_{m\sim n}
 \left(a_n-\min(a_n,a_m)\right)
 =\sum_{\{n,m\}:n\sim m}|a_n-a_m|.}
\tag{8}
\]

#### Proof

No loop contributes. Pair two directed copies of every unordered edge. For real $u,v$,

\[
 (u-\min(u,v))+(v-\min(v,u))=|u-v|.
\tag{9}
\]

Sum (9) over unordered edges. ∎

Thus canonical Lean consumer is exactly graph total variation of degree-normalized Gibbs density.

## 3. Co-moving Gibbs term is already strict-half

### Theorem B — Gibbs/degree fracture

Under hypotheses of §1, inequality (4) holds.

#### Proof

Orient every unordered edge as $n<m$. Then $w_x(n)\ge w_x(m)$ for $x\ge0$, and

\[
 \begin{aligned}
 \left|\frac{w_x(n)}{d_n}-\frac{w_x(m)}{d_m}\right|
 &=
 \left|
 \frac{w_x(n)-w_x(m)}{d_n}
 +w_x(m)\left(\frac1{d_n}-\frac1{d_m}\right)
 \right|\\
 &\le
 \frac{w_x(n)-w_x(m)}{d_n}
 +w_x(m)\left|\frac1{d_n}-\frac1{d_m}\right|.
 \end{aligned}
\tag{10}
\]

Existing sharp one-edge exponential transport inequality gives

\[
 0\le w_x(n)-w_x(m)
 \le x(m-n)w_x(n)
 \le xH w_x(n).
\tag{11}
\]

For fixed $n$, number of oriented edges leaving $n$ toward larger integer is at most $d_n$.
Therefore

\[
 \sum_{\{n,m\}:n<m}
 \frac{w_x(n)-w_x(m)}{d_n}
 \le xH\sum_nw_x(n)
 =xH Z_V(x).
\tag{12}
\]

Sum (10), use (8), (12), and Lean consumer (7). Remaining term is exactly (3), proving (4). ∎

At physical scale, $(H/X)Z_V=X^{1/2+o(1)}$. This term is closed unconditionally once relation
has strict-half displacement. All new arithmetic content lies in isolated mass and
$\mathcal V_{\deg}$.

## 4. Sharpness: degree variation can equal signed current

### Theorem C — complete-bipartite saturation

Let graph be complete bipartite between $L$ positive vertices and $R$ negative vertices, with
constant weight one. Then no vertex is isolated and

\[
 d_n=R\quad(n\in L),
 \qquad d_m=L\quad(m\in R).
\tag{13}
\]

Consequently

\[
 \boxed{
 \sum_{\{n,m\}}\left|\frac1{d_n}-\frac1{d_m}\right|
 =LR\left|\frac1R-\frac1L\right|
 =|L-R|
 =|J|.}
\tag{14}
\]

#### Proof

There are $LR$ edges and each has same reciprocal-degree difference. Last equality is signed sum
of $L$ plus signs and $R$ minus signs. ∎

This proves:

- co-moving edge length alone cannot close current;
- large minimum degree alone cannot close current;
- matching row/co-degree only to exponent $1/2+o(1)$ cannot close current; and
- reciprocal-degree variation may encode entire scalar imbalance.

These obstructions remain joint at physical scale, not only on abstract complete graph. Tile
$[X,2X]$ by blocks of length $H=o(X)$. In each block put seven eighths of vertices on plus side,
one eighth on minus side, and use complete bipartite block. Every edge has length at most $H$ and
both degrees are comparable to $H$. Since every block weight lies between $e^{-2}$ and $e^{-1}$,
placing plus vertices before minus vertices gives positive signed Gibbs mass bounded below by a
fixed constant times block length. Total current is therefore $\gg X$. Inequality (4), with no
isolates and $xHZ=O(H)$, forces $\mathcal V_{\deg}\gg X$ whenever $H=o(X)$. Thus strict-half
geometry plus degree exponent balance still does not control degree BV.

Hence (5) must be proved from source-specific degree coherence before signed sum is evaluated.

## 5. Weighted-degree and row-kernel symmetrization

Simple degree is not canonical when Route E already has reciprocal recurrence weights. Existing
Lean unused-conductance theorem permits exact weighted extension.

Let $b_{nm}=b_{mn}\ge0$ be any symmetric base edge weight supported on sign-reversing edges, put

\[
 D_n=\sum_mb_{nm},
 \qquad a_n=
 \begin{cases}
 w_x(n)/D_n,&D_n>0,\\
 0,&D_n=0,
 \end{cases}
\tag{15}
\]

and define conductance $c_{nm}=b_{nm}\min(a_n,a_m)$. It is symmetric, sign-reversing, and
$\sum_mc_{nm}\le w_x(n)$.

### Theorem D — weighted-degree Gibbs fracture

If every supported edge has length at most $H$, then

\[
 \boxed{
 |J_V(x)|
 \le W_{D=0}(x)+xH Z_V(x)
 +\sum_{\{n,m\}:n<m}
 b_{nm}e^{-xm}
 \left|\frac1{D_n}-\frac1{D_m}\right|.}
\tag{16}
\]

#### Proof

Unused conductance is

\[
 \sum_n\left(w_x(n)-\sum_mc_{nm}\right)
 =W_{D=0}(x)+\sum_{\{n,m\}}b_{nm}|a_n-a_m|.
\]

First equality follows from $w_x(n)=D_na_n$ off weighted-isolated set; second pairs two edge
orientations as in Theorem A. For $n<m$, repeat split (10) with $D_n,D_m$ and multiply by
$b_{nm}$. Summing Gibbs-displacement term uses
$\sum_{m>n}b_{nm}\le D_n$, hence is at most $xHZ_V(x)$. Remaining term is displayed weighted
reciprocal-degree variation. Apply unconditional Lean unused-conductance consumer. ∎

Now let $P=(P_{nm})$ be one source-predeclared nonnegative substochastic kernel on finite aperture:

\[
 P_{nm}\ge0,
 \qquad r_n:=\sum_mP_{nm}\le1,
 \qquad P_{nm}>0\Longrightarrow
 \epsilon_n+\epsilon_m=0\text{ and }|n-m|\le H.
\tag{17}
\]

Let column load, symmetric base, weighted degree, inverse weighted degree, and edge Dirichlet
energy be

\[
 \ell_n=\sum_mP_{mn},
 \qquad b_{nm}=\frac{P_{nm}+P_{mn}}2,
 \qquad D_n=\frac{r_n+\ell_n}2,
\tag{18}
\]

\[
 q_n=
 \begin{cases}
 1/D_n,&D_n>0,\\
 0,&D_n=0,
 \end{cases}
 \qquad
 \mathcal E_P(x)
 =\sum_{\{n,m\}:n<m}b_{nm}e^{-xm}(q_n-q_m)^2.
\tag{19}
\]

Indeed $D_n=\sum_mb_{nm}$. Put
$W_{P,0}(x)=\sum_{n:D_n=0}e^{-xn}$.

### Theorem E — recurrence-weighted Dirichlet bridge

\[
 \boxed{
 |J_V(x)|
 \le W_{P,0}(x)+xH Z_V(x)
 +\frac12
 \sqrt{(1+e^{xH})Z_V(x)\mathcal E_P(x)}.}
\tag{20}
\]

#### Proof

Theorem D leaves

\[
 \mathcal V_P
 =\sum_{\{n,m\}:n<m}b_{nm}e^{-xm}|q_n-q_m|.
\]

Cauchy--Schwarz gives $\mathcal V_P^2\le B_P\mathcal E_P$, where
$B_P=\sum_{n<m}b_{nm}e^{-xm}$. Since $e^{-xm}$ is smaller endpoint weight,

\[
 B_P\le\frac12\sum_nb_{n\bullet}e^{-xn}
 =\frac14\left(\sum_ne^{-xn}r_n+\sum_ne^{-xn}\ell_n\right).
\tag{21}
\]

Here $b_{n\bullet}=D_n$. Further,

\[
 \sum_ne^{-xn}\ell_n
 =\sum_m\sum_ne^{-xn}P_{mn}
 \le e^{xH}\sum_me^{-xm}r_m
 \le e^{xH}\sum_me^{-xm}
 =e^{xH}Z_V(x),
\tag{22}
\]

because every supported transition has $|n-m|\le H$. Substitute (21)--(22) into Cauchy and then
Theorem D, using $\sum_ne^{-xn}r_n\le Z_V(x)$. ∎

At $x=X^{-1}$, $H=X^{1/2+o(1)}$, $Z=X^{1+o(1)}$, exact new sufficient producer is only

\[
 \boxed{
 W_{P,0}(X^{-1})\le X^{1/2+o(1)},
 \qquad
 \mathcal E_P(X^{-1})\le X^{o(1)}.}
\tag{23}
\]

This is geometrically weaker on slow modes than global column ANOVA
$\operatorname{Var}(\rho/\nu)\le X^{-1+o(1)}$: it asks inverse column load to have
subpolynomial edge Dirichlet energy under actual recurrence weights, while permitting order-one
variation accumulated gradually across moving aperture. Kernel $P$ remains source-defined; no
optimizer is selected from endpoint. Symmetrizing
$P$ uses union of forward and transposed supports and therefore does not require Metropolis
forward/reverse support overlap.

Current reciprocal-allocation formula is parity-agnostic in anchor $n$, so it is a candidate for
outgoing rows on both signs. What is not proved is one common finite aperture closed enough that
its physical terminal quotient and next outgoing rows use same kernel, especially after
entropy-complement successor. Theorem E also permits absent boundary rows, but their zero-incidence
atoms remain explicit. No row deficit is silently renormalized.

But one-sided embedding does not reduce quantitative burden.

### Theorem F — one-sided energy is co-moving reverse column chi-square

Suppose $V=S\sqcup T$, rows on $S$ have mass one, rows on $T$ vanish, and $P$ is supported from
$S$ to $T$. Put $\ell_t=\sum_{s\in S}P_{st}$. Then on nonisolated targets,

\[
 q_s=2,
 \qquad q_t=\frac2{\ell_t},
 \qquad b_{st}=\frac{P_{st}}2,
\tag{23a}
\]

and therefore

\[
 \boxed{
 \mathcal E_P(x)
 =2\sum_{t:\ell_t>0}
 \omega_t(x)\frac{(\ell_t-1)^2}{\ell_t},
 \qquad
 \omega_t(x):=\frac1{\ell_t}\sum_sP_{st}e^{-x\max(s,t)}.}
\tag{23b}
\]

Moreover the displacement hypothesis gives

\[
 e^{-xH}e^{-xt}\le \omega_t(x)\le e^{-xt},
\tag{23c}
\]

and if every supported transition has $s<t$, then $\omega_t(x)=e^{-xt}$ exactly.

#### Proof

Substitute (23a) into (19). Remembering that the endpoint weight on an unoriented edge is
$e^{-x\max(s,t)}$ gives

\[
 \sum_s\frac{P_{st}}2e^{-x\max(s,t)}
 \left(2-\frac2{\ell_t}\right)^2
 =2\omega_t(x)\frac{(\ell_t-1)^2}{\ell_t}.
\]

Sum over targets. Since $|s-t|\le H$, one has
$t\le\max(s,t)\le t+H$ on every supported transition; averaging its exponential proves
(23c). If $s<t$, then $\max(s,t)=t$. ∎

Thus restricting reciprocal relation to one sign source recovers a co-moving reverse Pearson
column divergence and needs same strict-half scale. At $x=X^{-1}$ and
$H=X^{1/2+o(1)}$, its weight differs from $e^{-xt}$ by only $1+o(1)$; for monotone forward
transitions it is literally $e^{-xt}$. Genuine Dirichlet escape uses parity-agnostic rows on both
classes so inverse incidence load can change through alternating paths. This does not require
detailed balance or common forward/reverse support: symmetrized base still uses union support.

## 6. Exact collision with existing local replacement graph

Same grown Lean module proves following finite obstruction. In literal
MobiusBoundaryFactorReplacementWindowAdjacent graph generated by one-prime to two-prime and
one-prime to four-prime replacements below $z$, if every prime factor of $n$ is at most $y<z$,
then

\[
 n\le y^4|n-m|
\tag{24}
\]

for every replacement neighbor $m$. Therefore

\[
 y^4H<n
 \Longrightarrow
 n\text{ is isolated in displacement-}H\text{ graph}.
\tag{25}
\]

This is theorem
not_boundaryFactorReplacementWindowAdjacent_of_primeFactors_le_of_pow_mul_lt. It proves bounded
prime local replacement graph cannot be inserted into (5). Internal failed-route card
route-e-sublinear-factor-replacement-flow.md combines this exact theorem with its already-audited
squarefree-friable density input and proves linear isolated Gibbs capacity in every uniformly
sublinear pruning. That graph is retired, not an open subcase. No row normalization repairs
isolation.

Full entropy-complement/coalesced relation is not covered by (25): it changes growing number of
prime coordinates and spends complementary breadth. It remains legitimate candidate for (5), but
must be quotiented to ordinary physical integers before degrees are formed.

## 7. Relation to weighted-Hall ANOVA lane

Two lanes solve different components.

1. Weighted-Hall projection normalizes positive and negative masses separately. It can make
   centered column energy zero while scalar difference survives for recurrence.
2. Symmetric conductance consumes equal physical mass across sign-reversing edges and directly
   bounds scalar signed current. Its defect cannot be smaller than global imbalance, but it needs
   no separate mean channel.

Arbitrary complete-bipartite conductance is tautological: existing Lean theorem
completeBipartiteProportionalConductance_attains_signedImbalance proves minimum unused capacity
equals signed imbalance. Scientific content must therefore come from canonical arithmetic graph
and source-side bound for (5).

## 8. Heavy conjecture--proof--failure loop

### Loop A: canonical conductance plus strict-half displacement closes Route E

[FAILED SHARPLY] Theorem C. Displacement controls Gibbs variation but not reciprocal-degree
variation, which can equal entire current.

### Loop B: row and co-degree $X^{1/2\pm o(1)}$ control reciprocal-degree variation

[FAILED] Complete bipartite examples with two degrees differing by subpower factor retain linear
variation. Exponent balance is much weaker than total weighted edge variation (3).

### Loop C: existing one/two/four-prime boundary graph supplies required adjacency

[FAILED SHARPLY] Exact isolation law (25) plus internal failed-route density audit gives linear
isolated Gibbs mass for every uniformly sublinear window. This graph does not use
entropy-complement breadth and is retired.

### Loop D: use unrestricted optimal fractional flow

[FAILED AS THEATRE] Existing complete-bipartite optimality theorem says unused capacity is exactly
signed imbalance. Choosing unrestricted flow reparameterizes endpoint.

### Loop E: full entropy-complement graph may have small canonical BV defect

[SURVIVES] It has opposite parity, strict-half displacement, source-predeclared breadth mixture,
and enough row incidence at power scale. Fixed-token friable isolation theorem does not apply.
Neither current corpus nor degree counts prove isolated Gibbs mass or (3).

### Loop F: restrict reciprocal kernel to one sign source

[FAILED AS BURDEN REDUCTION] Theorem F. Its Dirichlet energy is co-moving reverse column
chi-square (23b)--(23c), uniformly equivalent to target-weighted reverse chi-square at strict-half
displacement, so column balance remains.

### Loop G: two-sided alternating rows without detailed balance

[SURVIVES] Use parity-agnostic reciprocal formula on one common physical aperture, then
$b=(P+P^\mathsf T)/2$. Forward and reverse supports need not overlap. Open formation step is
closure/boundary control of this two-sided kernel; open estimate is (23), with moving seam labels
retained.

## 9. New alternate Route E target

Define symmetric ordinary-integer graph before forming current:

1. vertices are one cofinal finite Gibbs aperture of squarefree atoms;
2. edges are physical quotients of actual entropy-complement/coalesced relation and reverse
   adjacency, with repeated labels collapsed;
3. every edge reverses Möbius sign and has $|n-m|\le X^{1/2+o(1)}$;
4. same graph retains moving zero/one-large-prime sector labels and prime-dilation aperture.

Two nested versions now exist. For arbitrary symmetric graph prove

\[
 \boxed{
 W_{\rm iso}(X)
 +\sum_{\{n,m\}:n<m}
 e^{-m/X}\left|\frac1{d_n}-\frac1{d_m}\right|
 \le X^{1/2+o(1)}.}
\tag{26}
\]

For actual reciprocal row kernel, sharper target is (23). Name:

**ENTROPY-COMPLEMENT-RECURRENCE-WEIGHTED-INVERSE-LOAD-DIRICHLET-STRICT-HALF**.

Equation (20) then gives $|J_{S(X)}(X^{-1})|\le X^{1/2+o(1)}$ directly, hence normalized
$x^{1/2-o(1)}$ endpoint when $Z_{S(X)}(x)=x^{-1+o(1)}$. Finite alternating signs, Gibbs weights,
prime-dilation displacement, and recurrence weights $P_{nm}$ are retained atomwise.
Finite-aperture row deficits must be included as explicit residual Gibbs mass; they cannot be
renormalized away. If recurrence accumulation remains chosen presentation, (23) must hold
uniformly on same nested apertures so boundary increments retain their signs.
One-sign restriction yields (23b)--(23c), so genuine new branch must retain parity-agnostic outgoing rows
already suggested by full relation and close them on common aperture. This is weaker than detailed
balance and does not require Metropolis support overlap.

## 10. Honest status

Theorems A--F and inequalities (4), (16), and (20) are dependency-closed paper consequences of existing
unconditional Lean consumer and exact exponential edge bound. They create new Route E knowledge:

- grown corpus converts direct current into explicit graph BV;
- strict-half displacement term is already exactly right size;
- simple-graph form leaves isolated mass and reciprocal-degree variation;
- substochastic-kernel form isolates only zero-incidence mass and reduces remaining producer to
  subpolynomial inverse-load Dirichlet energy (23);
- one-sided specialization collapses to co-moving reverse column chi-square, uniformly equivalent
  to target-weighted chi-square at strict-half displacement, so only genuinely
  two-sided alternating rows open new lane;
- exponent-level near-Hall cannot control this variation; and
- local bounded-prime replacement graph is retired by linear friable isolation.

No estimate (23) or (26), entropy-complement physical degree/Dirichlet theorem, Route E endpoint,
or RH proof is claimed.

## Lean implementation and verification

- Theorems A--F, weighted isolated-mass decomposition, co-moving Gibbs bound, recurrence-weighted
  Cauchy--Schwarz bridge `(20)`, complete-bipartite saturation, and one-sided reverse-column
  chi-square identity are unconditional Lean theorems in
  `RouteEDegreeNormalizedGibbsBoundaryVariation.lean`.
- Public co-moving variation wrapper retains Laplace scale, displacement, and total physical
  weight without hiding an asymptotic premise.
- Module is imported by `GaloisForLFunctions.RHTower`; targeted `lake env lean` and
  `lake build GaloisForLFunctions.RHTower.RouteEDegreeNormalizedGibbsBoundaryVariation` pass.
- Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
