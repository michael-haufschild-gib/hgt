# Route E weighted-Hall ANOVA projection duality law

- **ID:** `ROUTE-E-WEIGHTED-HALL-ANOVA-PROJECTION-DUALITY-001`
- **Stage:** 3-formalized
- **Type:** `[EXACT FINITE DUALITY]` / `[RATE FIREWALL]` /
  `[RECURRENCE-SEAM DECOMPOSITION]`
- **Parent:** `../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **Companion:** `../../2-fully-proven/new_scientific_knowledge/route-e-critical-antiscale-diffuse-codiagonal-transfer-law.md`
- **RH used:** no
- **Computation used:** no
- **Literature used:** no; internal-corpus derivation only
- **Lean status:** unconditional and umbrella-reachable. `RouteEWeightedHallANOVA.lean` formalizes
  physical normalization, exact collision defect, sharp one/two-sided capacity rates, and
  partition/seam ANOVA. `RouteEWeightedHallProjectionDuality.lean` formalizes compact convex
  projection, quadratic and homogeneous reporter duality, weighted-Hall necessity and sufficiency,
  exact zero-energy classification, and sharp normalized Hall-deficit obstruction. No project
  axiom, `sorry`, `admit`, `opaque`, `unsafe`, or numerical computation is used.

## 1. Result

The finite physical column-ANOVA target has an exact graph-theoretic producer formulation.
Let (S,T) be finite source and target sets, let (E\subseteq S\times T) be a
source-predeclared relation with every source having a neighbor, and let positive physical masses
(a_s,b_t) have totals

\[
 A=\sum_sa_s>0,
 \qquad B=\sum_tb_t>0.
\tag{1}
\]

Normalize

\[
 \alpha_s=\frac{a_s}{A},
 \qquad \beta_t=\frac{b_t}{B}.
\tag{2}
\]

For a row-stochastic kernel (K) supported on (E), put

\[
 \gamma_t^K=\sum_s\alpha_sK_{st},
 \qquad \rho_t^K=A\gamma_t^K,
 \qquad r_t^K=\frac{\gamma_t^K}{\beta_t}.
\tag{3}
\]

Then the physical centered column energy is

\[
 \boxed{
 E_{\rm cent}(K)
 =\sum_t\frac{(\rho_t^K-(A/B)b_t)^2}{b_t}
 =\frac{A^2}{B}\sum_t\frac{(\gamma_t^K-\beta_t)^2}{\beta_t}.}
\tag{4}
\]

Its optimum over every supported row kernel is exactly the squared distance from target law
(\beta) to the relation's reachable marginal polytope. That distance has three equivalent
faces:

1. a minimum physical column ANOVA;
2. a nonlinear all-reporter dual involving the minimum reporter value in each source
   neighborhood; and
3. zero distance exactly when normalized weighted Hall holds.

This produces a sharp rate correction. A one-sided column ceiling (r_t\le1+\varepsilon) gives
only chi-square at most (\varepsilon), and this is sharp. Therefore the previously used phrase
“unit load (1+o(1))” is not an endpoint-rate theorem. At (A,B=X^{1+o(1)}), the strict-half
target requires either exact normalized weighted-Hall transport, one-sided load excess
(X^{-1+o(1)}), two-sided relative load error (X^{-1/2+o(1)}), or the equivalent all-reporter
bound below.

Finally, every marker or moving-seam partition splits the optimum's chi-square into exact
within-sector energy plus between-sector mass variance. Thus a global column estimate cannot
discard normalized seam flux and repair it afterward.

## 2. Reachable marginal and physical ANOVA

Let

\[
 \mathcal C_E=
 \left\{\gamma\in\mathbb R_{≥0}^T:
 \gamma_t=\sum_s\alpha_sK_{st}
 \text{ for a row-stochastic }K\text{ supported on }E\right\}.
\tag{5}
\]

It is a nonempty compact convex polytope of probability laws. Define

\[
 d_E^2(\alpha,\beta)
 :=\min_{\gamma\in\mathcal C_E}
 \sum_t\frac{(\gamma_t-\beta_t)^2}{\beta_t}.
\tag{6}
\]

### Theorem A — exact finite physical optimum

\[
 \boxed{
 \min_K E_{\rm cent}(K)
 =\frac{A^2}{B}d_E^2(\alpha,\beta).}
\tag{7}
\]

In particular, when (A,B=X^{1+o(1)}), the physical strict-half target

\[
 \min_KE_{\rm cent}(K)\le X^{o(1)}
\tag{8}
\]

is equivalent to

\[
 \boxed{d_E^2(\alpha,\beta)\le X^{-1+o(1)}.}
\tag{9}
\]

#### Proof

Since (b_t=B\beta_t), (\rho_t^K=A\gamma_t^K), and the centered physical mean ratio is
(A/B), direct substitution gives `(4)`. Minimizing over (K) is the same as minimizing over
its reachable marginal (\gamma^K\in\mathcal C_E), proving `(7)`. The scale equivalence
`(8)`--`(9)` follows from (A^2/B=X^{1+o(1)}). ∎

## 3. Exact nonlinear reporter dual

For (f:T\to\mathbb R), define relation lower envelope

\[
 \mathcal M_Ef
 :=\sum_s\alpha_s\min_{t:(s,t)\in E}f_t,
\tag{10}
\]

and target variance

\[
 \operatorname{Var}_\beta(f)
 :=\sum_t\beta_t\left(f_t-\sum_u\beta_uf_u\right)^2.
\tag{11}
\]

### Theorem B — projection duality

The squared distance `(6)` obeys

\[
 \boxed{
 d_E^2(\alpha,\beta)
 =\sup_{f:T\to\mathbb R}
 \left\{
 2\left(\mathcal M_Ef-\sum_t\beta_tf_t\right)
 -\sum_t\beta_tf_t^2
 \right\}.}
\tag{12}
\]

Equivalently,

\[
 \boxed{
 d_E(\alpha,\beta)
 =\sup_{\operatorname{Var}_\beta(f)>0}
 \frac{\left[\mathcal M_Ef-\mathbb E_\beta f\right]_+}
      {\sqrt{\operatorname{Var}_\beta(f)}}.}
\tag{13}
\]

Consequently `(9)` is exactly the all-reporter inequality

\[
 \boxed{
 \mathcal M_Ef-\mathbb E_\beta f
 \le X^{-1/2+o(1)}\sqrt{\operatorname{Var}_\beta(f)}
 \quad\text{for every }f:T\to\mathbb R.}
\tag{14}
\]

This is the precise non-scalar producer hidden behind “unit column capacity.”

#### Proof

Let (\gamma_*\in\mathcal C_E) minimize `(6)` and put

\[
 u_t=\frac{\gamma_{*,t}-\beta_t}{\beta_t}.
\tag{15}
\]

For every (\gamma\in\mathcal C_E), differentiating the squared distance along segment
(\gamma_*+\lambda(\gamma-\gamma_*)) at (\lambda=0^+) gives projection inequality

\[
 \sum_tu_t(\gamma_t-\gamma_{*,t})\ge0.
\tag{16}
\]

Thus (\gamma_*) minimizes (\sum_tf_t\gamma_t) over (\mathcal C_E) when (f=u). For any
(f), row masses can be sent independently among allowed neighbors, so

\[
 \min_{\gamma\in\mathcal C_E}\sum_tf_t\gamma_t
 =\sum_s\alpha_s\min_{t:(s,t)\in E}f_t
 =\mathcal M_Ef.
\tag{17}
\]

For arbitrary (f), `(17)` and (\gamma_*\in\mathcal C_E) give

\[
 \begin{aligned}
 2(\mathcal M_Ef-\mathbb E_\beta f)-\mathbb E_\beta f^2
 &\le2\sum_tf_t(\gamma_{*,t}-\beta_t)-\sum_t\beta_tf_t^2\\
 &=2\sum_t\beta_tf_tu_t-\sum_t\beta_tf_t^2\\
 &\le\sum_t\beta_tu_t^2=d_E^2,
 \end{aligned}
\tag{18}
\]

where last line is square completion. Taking (f=u), `(16)`--`(17)` give
(\mathcal M_Eu=\sum_tu_t\gamma_{*,t}). Since

\[
 \sum_t\beta_tu_t=\sum_t(\gamma_{*,t}-\beta_t)=0,
 \qquad
 \sum_t\beta_tu_t^2=d_E^2,
\tag{19}
\]

expression in `(12)` equals (d_E^2). This proves `(12)`.

Adding a constant to (f) leaves
(\mathcal M_Ef-\mathbb E_\beta f) unchanged and only increases the quadratic cost away from
target centering. On every centered ray (\lambda f), (\lambda\ge0), maximizing
(2\lambda D-\lambda^2\operatorname{Var}_\beta(f)), where
(D=\mathcal M_Ef-\mathbb E_\beta f), gives
([D]_+^2/\operatorname{Var}_\beta(f)). Taking square roots proves `(13)`, and `(14)` is `(9)`.
∎

## 4. Weighted Hall and its quantitative obstruction

For (U\subseteq S), let (N_E(U)\subseteq T) be its target neighborhood.

### Theorem C — exact zero-energy classification

Following are equivalent:

1. (d_E(\alpha,\beta)=0);
2. some supported row kernel has (\gamma^K=\beta);
3. there is a coupling on (E) with marginals (\alpha,\beta);
4. normalized weighted Hall holds:
   
   \[
    \boxed{\alpha(U)\le\beta(N_E(U))\quad\text{for every }U\subseteq S.}
   \tag{20}
   \]

#### Proof

The first three statements are the definitions `(5)`--`(6)` rewritten using
(\pi_{st}=\alpha_sK_{st}). For the last equivalence, build finite network with source-to-(s)
capacity (\alpha_s), infinite capacity on allowed (s\to t) edges, and (t)-to-sink capacity
(\beta_t). Every finite cut has capacity at least one exactly when `(20)` holds. Finite
max-flow/min-cut then gives a unit flow, which is required coupling; any coupling proves `(20)` by
summing its mass from (U) into (N_E(U)). ∎

There is also a sharp normalized Hall-deficit obstruction. Put

\[
 \delta_U=\left[\alpha(U)-\beta(N_E(U))\right]_+,
 \qquad b_U=\beta(N_E(U)).
\tag{21}
\]

When (0<b_U<1),

\[
 \boxed{
 d_E^2(\alpha,\beta)
 \ge\frac{\delta_U^2}{b_U(1-b_U)}.}
\tag{22}
\]

Indeed every reachable (\gamma) has (\gamma(N_E(U))\ge\alpha(U)). Cauchy--Schwarz on
(N_E(U)) and its complement gives

\[
 \sum_t\frac{(\gamma_t-\beta_t)^2}{\beta_t}
 \ge
 \frac{(\gamma(N_E(U))-b_U)^2}{b_U}
 +\frac{(\gamma(N_E(U))-b_U)^2}{1-b_U},
\tag{23}
\]

which implies `(22)`. Thus strict-half ANOVA forces every weighted Hall deficit to be at most

\[
 \delta_U\le X^{-1/2+o(1)}\sqrt{b_U(1-b_U)}.
\tag{24}
\]

Current unweighted near-Hall
(\#N_E(U)\ge\#U\,X^{-o(1)}) has neither coefficient one nor physical Gibbs weights and cannot
imply `(24)`.

## 5. Collision form of a fixed kernel

For a supported row kernel define normalized two-row collision kernel

\[
 C_K(s,s')=\sum_t\frac{K_{st}K_{s't}}{\beta_t}.
\tag{25}
\]

### Theorem D — exact collision defect

\[
 \boxed{
 \sum_t\frac{(\gamma_t^K-\beta_t)^2}{\beta_t}
 =\sum_{s,s'}\alpha_s\alpha_{s'}C_K(s,s')-1.}
\tag{26}
\]

#### Proof

Because (\sum_t\gamma_t^K=\sum_t\beta_t=1), left side equals
(\sum_t(\gamma_t^K)^2/\beta_t-1). Substitute `(3)` and expand finite sums. ∎

Equation `(26)` is the exact second-moment producer form for reciprocal allocation. Row degree,
co-degree, and pointwise column ceilings bound pieces of it but do not show its average equals
(1+X^{-1+o(1)}). Any collision proof must retain physical (\alpha,β), not merely count
labeled representations.

## 6. Capacity-rate fracture

### Theorem E — sharp one-sided and two-sided rates

For any probability output (\gamma), write (r_t=\gamma_t/\beta_t). If

\[
 0\le r_t\le1+\varepsilon\quad\text{for every }t,
\tag{27}
\]

then

\[
 \boxed{\chi^2(\gamma\mid\beta)=\operatorname{Var}_\beta(r)\le\varepsilon.}
\tag{28}
\]

This is sharp. If instead

\[
 |r_t-1|\le\varepsilon\quad\text{for every }t,
\tag{29}
\]

then

\[
 \boxed{\chi^2(\gamma\mid\beta)\le\varepsilon^2.}
\tag{30}
\]

#### Proof

Since (\mathbb E_\beta r=1), `(27)` gives
(\mathbb E_\beta r^2\le(1+\varepsilon)\mathbb E_\beta r=1+\varepsilon), proving `(28)`.
For sharpness, take two target atoms with
(\beta=(1/(1+\varepsilon),\varepsilon/(1+\varepsilon))) and
(r=(1+\varepsilon,0)); variance is exactly (\varepsilon). Equation `(30)` is immediate from
pointwise square bound. ∎

Therefore, at Route E scale:

- exact normalized weighted Hall gives (d_E=0);
- one-sided load (1+\varepsilon_X) reaches `(9)` only if
  (\varepsilon_X\le X^{-1+o(1)});
- two-sided relative column balance reaches `(9)` if
  (\varepsilon_X\le X^{-1/2+o(1)});
- unquantified (1+o(1)) unit Carleson is not a strict-half producer.

This does not invalidate matching receiver with (X^{-1/2+o(1)}) discarded mass: unmatched mass
enters that different endpoint inequality linearly. It proves that unmatched-mass and chi-square
routes must not share rates implicitly.

## 7. Exact marker and seam ANOVA

Let (T=\bigsqcup_{j\in J}T_j) be any finite target partition with

\[
 \beta_j=\beta(T_j)>0,
 \qquad \gamma_j=\gamma(T_j),
 \qquad \bar r_j=\frac{\gamma_j}{\beta_j}.
\tag{31}
\]

### Theorem F — total-variance seam law

\[
 \boxed{
 \chi^2(\gamma\mid\beta)
 =\sum_j\sum_{t\in T_j}\beta_t(r_t-\bar r_j)^2
  +\sum_j\beta_j(\bar r_j-1)^2.}
\tag{32}
\]

For a two-sector seam (T=T_0\sqcup T_1), putting
(b=\beta(T_1)) and (g=\gamma(T_1)) gives exact between-sector term

\[
 \boxed{
 \sum_{j=0}^1\beta_j(\bar r_j-1)^2
 =\frac{(g-b)^2}{b(1-b)}.}
\tag{33}
\]

#### Proof

On each (T_j), expand
(r_t-1=(r_t-\bar r_j)+(\bar r_j-1)). Cross term vanishes because
(\sum_{t\in T_j}\beta_t(r_t-\bar r_j)=\gamma_j-\beta_j\bar r_j=0). Summing proves `(32)`.
For two sectors, substitute means (g/b) and ((1-g)/(1-b)) and simplify. ∎

Taking (T_j) to be reciprocal ternary marker states makes first term within-state physical
codiagonal energy and second term marker-state mean energy. Taking (T_0,T_1) to be friable and
one-large-prime sectors makes `(33)` normalized seam charge. Therefore recurrence weights,
prime-dilation intervals, and alternating signs must act on same partition means used by column
proof; global chi-square cannot erase seam term.

## 8. Heavy conjecture--proof--failure loop

### Loop A: centered ANOVA still needs universal Fisher identification

`[FALSIFIED]` Theorems A--B identify it directly as finite relation-to-target projection distance.
Universal critical Fisher clock has no role in this identity.

### Loop B: unit column load (1+o(1)) gives strict half

`[FAILED SHARPLY]` Theorem E. One-sided excess (\varepsilon) yields variance only
(O(\varepsilon)), sharply. Required rate is (X^{-1+o(1)}), not unspecified (o(1)).

### Loop C: current near-Hall expansion already makes ANOVA subpolynomial

`[FAILED SHARPLY]` Exact zero needs weighted Hall with coefficient one. Bound `(22)` shows every
physical Hall deficit is squared and divided by its target-sector variance. Existing
(X^{-o(1)}) neighborhood ratio permits macroscopic normalized deficit.

### Loop D: subset deficits alone characterize approximate ANOVA

`[FAILED AS A QUANTITATIVE SUFFICIENCY]` Subset indicators give necessary bounds `(22)`--`(24)`.
Exact positive distance is the supremum over every real reporter in `(13)`, not only indicators.
At zero distance, finite weighted Hall collapses full reporter family back to subset cuts.

### Loop E: optimize a kernel and inspect recurrence seam afterward

`[FAILED EXACTLY]` Theorem F. Seam-sector mismatch is an orthogonal summand of same chi-square.
Dropping sector labels during optimization can spend entire endpoint budget in between-sector term.

### Loop F: exact normalized flow proves signed Gibbs cancellation

`[FAILED AS AN ENDPOINT CLAIM]` Exact weighted-Hall flow makes centered energy zero, but masses
(A,B) were normalized separately. Scalar difference (A-B) survives untouched. It must be
bounded by ternary mean dissipation plus signed prime-dilation recurrence, not inferred from
transport normalization.

### Loop G: choose an arbitrary optimal max-flow after forming endpoint

[FAILED ADMISSIBILITY AUDIT] The minimum in equation (6) is an exact diagnostic and lower burden,
not permission to select weights after reading scalar current. A Route E producer must give a
source-defined kernel or coupling from unsigned physical atom data, and that selection must
commute with marker partition, moving seam, and prime-dilation recurrence. An arbitrary optimizer
can annihilate centered energy while destroying every retained recurrence coordinate.

## 9. Revised Route E producer

The finite physical part of
`FINITE-PHYSICAL-COLUMN-ANOVA-STRICT-HALF-AND-SIGNED-RECURRENCE-SEAM` is now exact. For actual
entropy-complement/Ramaré relation, with physical Gibbs laws chosen before evaluating signed
discrepancy, prove one of equivalent quantitative producers:

1. **projection:** (d_E^2(\alpha,\beta)\le X^{-1+o(1)});
2. **all reporters:** inequality `(14)` for every target potential;
3. **one kernel:** collision defect `(26)` is at most (X^{-1+o(1)});
4. **zero-energy stronger route:** exact normalized weighted Hall `(20)`;
5. **capacity sufficient routes:** one-sided excess (X^{-1+o(1)}) or two-sided error
   (X^{-1/2+o(1)}).

Then apply partition identity `(32)` before scalarization: reciprocal ternary state means carry
critical dissipation, friable/one-large-prime means carry normalized seam, and within-state terms
carry physical codiagonal. Push those same means and weights through exact prime-dilation
recurrence. The scalar (A-B) is final signed recurrence channel and may not be inserted into
`(6)` or `(20)` as a premise.
Any kernel realizing items 1--5 must be selected source-faithfully and be recurrence-compatible;
the unconstrained minimizer in equation (6) is not itself such a selection theorem.

Current row degree (X^{1/2-o(1)}), co-degree (X^{1/2+o(1)}), reciprocal Jacobian cancellation,
unweighted neighborhood factor (X^{-o(1)}), and column ceiling
(\exp(O((\log\log X)^{3/2}))) do not imply any of items 1--5. They establish relation breadth
and admissibility, not rate-sharp weighted expansion.

## 10. Honest status

Theorems A--F are dependency-closed finite mathematics. New Route E knowledge is their exact
physical synthesis:

- centered column ANOVA is graph-to-Gibbs projection distance;
- its missing estimate is exactly nonlinear all-reporter expansion `(14)`;
- exact weighted Hall annihilates centered energy, but not scalar parity imbalance;
- (1+o(1)) one-sided capacity is quantitatively insufficient;
- collision defect `(26)` is exact second-moment producer for reciprocal allocation; and
- marker/seam imbalance is an orthogonal ANOVA summand that recurrence must retain.

No weighted Hall theorem for actual physical relation, estimate `(9)`, reporter inequality `(14)`,
collision bound `(26)`, signed recurrence accumulation, Route E endpoint, or RH proof is claimed.

## 11. Lean formalization audit

Formal modules:

- `formal/GaloisForLFunctions/RHTower/RouteEWeightedHallANOVA.lean`
- `formal/GaloisForLFunctions/RHTower/RouteEWeightedHallProjectionDuality.lean`

The projection module proves a finite upper-tail layer-cake identity and uses it to derive every
nonlinear reporter inequality from weighted Hall. Applying that inequality to canonical projection
reporter forces projection distance zero, constructs exact supported transport, and proves weighted
Hall iff exact transport iff zero projection distance. This replaces paper proof's max-flow step by
internal convex/reporter geometry.

It also totalizes homogeneous quotient at zero variance and proves

\[
 \max_f \frac{[\mathcal M_Ef-\mathbb E_\beta f]_+}
                    {\sqrt{\operatorname{Var}_\beta(f)}}
 =\sqrt{d_E^2},
\]

with zero-variance reporters assigned quotient zero. Canonical projection reporter attains positive
distance; zero reporter attains degenerate zero-distance case. Optimal all-reporter inequality
`(14)` follows directly from weighted Cauchy--Schwarz against projection reporter.

Verification on 2026-08-11:

- direct `lake env lean GaloisForLFunctions/RHTower/RouteEWeightedHallProjectionDuality.lean`
  passed without diagnostics;
- targeted `lake build GaloisForLFunctions.RHTower.RouteEWeightedHallProjectionDuality` passed;
- requested Gibbs comparison and component-history modules passed both direct Lean checks and
  targeted module builds;
- axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound` for all new Hall,
  homogeneous-dual, conditional-mean, and product-history capstones;
- formal lint reports no issue in these Route E modules. Its nonzero exit is pre-existing unrelated
  umbrella reachability debt in Deninger adiabatic, Huxley/Maynard sieve, and one HTGeometry module.

No umbrella or full build was run.
