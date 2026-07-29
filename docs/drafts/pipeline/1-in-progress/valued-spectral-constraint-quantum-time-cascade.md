# Valued spectral-constraint law of quantum time

- **ID:** `valued-spectral-constraint-quantum-time-cascade`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL LAW / TEMPORAL WALL CROSSING / QUANTUM
  RECURRENCE / ANALYTIC INTERACTION
- **Source:** higher-conjecture gate above
  `interaction-generated-observer-time-universality.md`
- **Scientific status:** `[NEW CONJECTURAL INTERPRETATION]`
  `[ABSTRACT WALL-CROSSING AND LOCALITY THEOREMS PAPER-PROVED BELOW]`
  `[GRAPH-DISTANCE CONTRAST CORE LEAN-PROVED]`
  `[NOVELTY AUDIT OPEN] [LOCAL-HAMILTONIAN JET TRANSFER OPEN]`

## Public law

> **Quantum time is a cascade of broken spectral constraints.**

The claim is not that coordinate time has several spacetime axes. A
stationary quantum system carries many relative spectral phases. Exact
integer relations among its energies constrain those phases to a smaller
compact temporal world. An interaction creates an observable temporal
direction exactly when it breaks one of those relations.

The missing structure is not only the relation lattice. Near a
constraint-rich point, every relation has:

1. a **height**: the first correlation order that can detect it;
2. a **breaking order**: the first interaction jet that destroys it;
3. a **resolution time**: the inverse detuning needed to observe that
   destruction.

These are three views of one valued constraint. They respectively explain
the replica-order, perturbative-order, and finite-horizon obstructions in the
existing recurrence programme.

## Exact object

Let \(I\) be a finite or arbitrary discrete energy label set. Characters
always have finite support. Put
\[
 \Gamma_I
 =
 \left\{
   k\in\mathbb Z^{(I)}:\sum_{j\in I}k_j=0
 \right\}.                                             \tag{1}
\]
Let \(E_j(g)\) be real analytic near \(g=0\), and define
\[
 \delta_k(g)=\sum_j k_jE_j(g),\qquad
 v(k)=\operatorname{ord}_{g=0}\delta_k(g)
       \in\mathbb N_0\cup\{\infty\}.                  \tag{2}
\]
Here \(v(k)=\infty\) exactly when \(\delta_k\) vanishes identically near
zero. Define the spectral-constraint filtration
\[
 F^r
 =
 \{k\in\Gamma_I:v(k)\ge r\},
 \qquad r=0,1,2,\ldots,\infty.                        \tag{3}
\]
Thus
\[
 F^0=\Gamma_I,\qquad
 F^1=\{k:\delta_k(0)=0\},\qquad
 F^\infty=\{k:\delta_k(g)\equiv0\}.                   \tag{4}
\]

For a finite \(I\), let
\[
 K_r=\operatorname{Ann}(F^r)
 \subset \mathbb T^I/\mathbb T                       \tag{5}
\]
be the compact projective phase group whose characters satisfy the
order-\(r\) constraints.

## Theorem A — the constraint filtration is intrinsic

For every analytic spectral path:

1. \(F^{r+1}\subseteq F^r\) is a decreasing filtration by saturated
   subgroups of \(\Gamma_I\);
2. for finite \(I\), the filtration stabilizes after finitely many rank
   changes at \(F^\infty\);
3. the compact groups form an increasing temporal cascade
   \[
    K_1\subseteq K_2\subseteq\cdots\subseteq K_\infty;
                                                               \tag{6}
   \]
4. the dimension created at interaction order \(r\) is
   \[
    \boxed{
    \Delta d_r
    =
    \operatorname{rank}F^r-\operatorname{rank}F^{r+1},
    }
                                                               \tag{7}
   \]
   and
   \[
    \boxed{
    \sum_{r\ge1}\Delta d_r
    =
    \operatorname{rank}F^1-\operatorname{rank}F^\infty
    =
    \dim K_\infty-\dim K_1.
    }
                                                               \tag{8}
   \]

### Proof

Write
\[
 \epsilon_\ell
 =
 \left(\frac{E_j^{(\ell)}(0)}{\ell!}\right)_{j\in I}.
\]
Then
\[
 F^r
 =
 \Gamma_I\cap
 \bigcap_{\ell=0}^{r-1}
 \ker(k\mapsto k\cdot\epsilon_\ell).                 \tag{9}
\]
This is a subgroup. It is saturated because \(nk\) lies in every displayed
real kernel only if \(k\) does. The inclusions follow immediately.

Analyticity gives
\[
 F^\infty=\bigcap_{r\ge0}F^r.                         \tag{10}
\]
For finite \(I\), the real linear functionals
\(k\mapsto k\cdot\epsilon_\ell\) span a finite-dimensional space. A finite
subfamily has the same common kernel as the whole family, so \(F^r\)
eventually equals \(F^\infty\). Pontryagin annihilation reverses inclusions,
giving `(6)`. Since every \(F^r\) is saturated, the character rank of
\(K_r\) is
\[
 \dim K_r=\operatorname{rank}\Gamma_I-\operatorname{rank}F^r.
                                                               \tag{11}
\]
Equations `(7)`--`(8)` follow by subtraction and telescoping. \(\square\)

## Theorem B — exact double-scaling wall crossing

Let
\[
 z_g(t)=
 \bigl(e^{-itE_j(g)}\bigr)_{j\in I}\pmod{\mathbb T}
 \]
and let \(\mu_{g,T}\) be the temporal probability measure obtained by
sampling \(t\) uniformly from \([-T,T]\). For every character
\(\chi_k\), \(k\in\Gamma_I\),
\[
 \boxed{
 \widehat{\mu_{g,T}}(k)
 =
 \frac1{2T}\int_{-T}^{T}e^{-it\delta_k(g)}\,dt
 =
 \operatorname{sinc}\!\bigl(T\delta_k(g)\bigr).
 }
                                                               \tag{12}
\]

Fix \(\tau>0\), \(s>0\), and set
\[
 T(g)=\tau |g|^{-s}.                                  \tag{13}
\]
If \(s\notin\mathbb N\), then
\[
 \boxed{
 \mu_{g,T(g)}
 \Longrightarrow
 m_{K_{\lfloor s\rfloor+1}}
 \qquad(g\to0),
 }
                                                               \tag{14}
\]
where \(m_K\) is Haar probability measure on \(K\).

At the integer transition \(s=r\ge1\), put
\[
 a_r
 =
 \left(\frac{E_j^{(r)}(0)}{r!}\right)_{j\in I}.
\]
Then
\[
 \boxed{
 \mu_{g,\tau|g|^{-r}}
 \Longrightarrow
 m_{K_r}*
 \left(
  u\mapsto e^{-i\tau u a_r}
 \right)_\#
 \operatorname{Unif}[-1,1].
 }
                                                               \tag{15}
\]
Equivalently, the limiting Fourier coefficient is
\[
 \begin{cases}
 0,&v(k)<r,\\
 \operatorname{sinc}(\tau\,k\cdot a_r),&v(k)=r,\\
 1,&v(k)>r.
 \end{cases}                                           \tag{16}
\]
As \(\tau\to\infty\), the transition measure in `(15)` converges to
\(m_{K_{r+1}}\).

### Proof

Equation `(12)` is direct integration. If \(v(k)=q<\infty\), then
\[
 \delta_k(g)=c_kg^q+o(g^q),\qquad c_k\ne0.            \tag{17}
\]
Therefore \(T(g)\delta_k(g)\) tends to zero when \(q>s\), has unbounded
absolute value when \(q<s\), and tends in absolute value to
\(\tau c_k\) when \(q=s\). Since \(\operatorname{sinc}(0)=1\) and
\(\operatorname{sinc}(x)\to0\) as \(|x|\to\infty\), this proves the
character limits.

For noninteger \(s\), the limit is \(1\) exactly on
\(F^{\lfloor s\rfloor+1}\) and zero outside it. Because this subgroup is
saturated, that is exactly the Fourier transform of Haar measure on its
annihilator, proving `(14)`.

For \(s=r\), Haar measure on \(K_r\) kills exactly the characters outside
\(F^r\). Convolution with the uniform segment in the \(a_r\)-direction
multiplies the surviving coefficient by
\(\operatorname{sinc}(\tau k\cdot a_r)\). This is `(16)` and proves
`(15)`. Letting \(\tau\to\infty\) kills precisely
\(F^r\setminus F^{r+1}\), leaving the Fourier transform of
\(m_{K_{r+1}}\). \(\square\)

For finite \(I\), character convergence implies weak convergence for every
continuous phase reporter. For arbitrary discrete \(I\), the same theorem
holds for every cylinder-continuous reporter and hence for every finite
state, observable, or replica experiment.

## Theorem C — exact detector/perturbation/time trinity

For \(k\in\Gamma_I\), write
\[
 k=k^+-k^-,
 \qquad
 h(k)=|k^+|=|k^-|=\frac12\|k\|_1.                    \tag{18}
\]
Then:

1. \(h(k)\) is the smallest balanced replica order in which the relation
   \(k\) can occur;
2. \(v(k)\) is the smallest interaction-derivative order that can detect
   the breaking of \(k\);
3. for \(0<v(k)<\infty\),
   \[
    |\delta_k(g)|^{-1}
    \sim |c_k|^{-1}|g|^{-v(k)}                       \tag{19}
   \]
   is its exact finite-time resolution scale;
4. its finite-horizon contribution is exactly
   \[
    \operatorname{sinc}\!\bigl(T\delta_k(g)\bigr).    \tag{20}
   \]

Thus no relation is independently responsible for a replica obstruction, a
perturbative obstruction, and a time-resolution obstruction. These are its
height, valuation, and finite-time Fourier profile.

### Proof

If \(k=\alpha-\beta\) with
\(\alpha,\beta\in\mathbb N^{(I)}\) and
\(|\alpha|=|\beta|=m\), then \(k^+\le\alpha\) and
\(k^-\le\beta\), so \(h(k)\le m\). Equality is attained by
\((\alpha,\beta)=(k^+,k^-)\), proving minimality. The definition of the
order of vanishing proves item 2. Expansion `(17)` proves `(19)`, and
`(12)` proves `(20)`. \(\square\)

## Corollary D — finite-order activation has an upper theorem

Fix a finite energy support and replica order \(m\). Only finitely many
characters \(k=\alpha-\beta\) with
\(|\alpha|=|\beta|=m\) occur. For every such nonpersistent relation,
\[
 \left|
 \operatorname{sinc}(T\delta_k(g))
 \right|
 \le
 \min\left(1,\frac1{T|\delta_k(g)|}\right).           \tag{21}
\]
Consequently the complete \(m\)-replica temporal tensor converges to its
post-interaction infinite-time tensor once
\[
 T\min_{\substack{h(k)\le m\\v(k)<\infty\\
                   \delta_k(g)\ne0}}
 |\delta_k(g)|
 \longrightarrow\infty.                              \tag{22}
\]
Near \(g=0\), this is guaranteed by
\[
 T|g|^{R_m}\longrightarrow\infty,\qquad
 R_m=
 \max_{\substack{h(k)\le m\\0<v(k)<\infty}}v(k),     \tag{23}
\]
with a finite positive constant depending on the fixed spectral path and
order. This is the missing upper half of the finite-order crossover. It
does not give a uniform all-order or thermodynamic mixing time.

## Corollary E — complete temporal reconstruction

Let \(\mathcal M_m\) be the infinite-time mixed replica tensor whose
\((\alpha,\beta)\)-coefficient is the long-time average of
\[
 e^{-it(\alpha-\beta)\cdot E}.
\]
Then
\[
 (\alpha,\beta)\text{ survives in }\mathcal M_m
 \quad\Longleftrightarrow\quad
 \alpha-\beta\in F^1.                                \tag{24}
\]
The complete hierarchy \((\mathcal M_m)_{m\ge1}\) reconstructs \(F^1\)
exactly because every \(k\in F^1\) first appears at order \(h(k)\).
Therefore the following data are equivalent:

1. the full labeled zero-sum relation lattice;
2. the compact temporal phase group;
3. every mixed infinite-time replica tensor.

Scalar fidelity moments are only weighted sums of these tensor
coefficients and need not retain the complete labeled lattice.

## Theorem F — locality imposes a perturbative light cone on quantum time

Let
\[
 \mathcal H=(\mathbb C^q)^{\otimes n},\qquad
 X=\{1,\ldots,q\}^n,\qquad D=q^n.
\]
Let
\[
 A=\sum_{i=1}^n A_i
\]
be onsite and have a simple product spectrum labeled by \(x\in X\). Let
\[
 V=\sum_{i=1}^{n-1}V_{i,i+1},\qquad H(g)=A+gV,        \tag{25}
\]
with arbitrary nearest-neighbour terms. Let
\[
 E_x(g)=\sum_{\ell\ge0}g^\ell\epsilon_\ell(x)         \tag{26}
\]
be the analytic eigenvalue branch issuing from product state \(x\).

For \(r\ge0\), let \(\mathcal L_r\subset\mathbb Q^X\) be the rational span
of all configuration indicator functions supported on a contiguous interval
of at most \(\min(r+1,n)\) sites, and put
\[
 M_r=\dim_{\mathbb Q}\mathcal L_r.                    \tag{27}
\]
Then:

1. every coefficient \(\epsilon_\ell\), \(0\le\ell\le r\), belongs to
   \(\mathbb R\otimes_{\mathbb Q}\mathcal L_r\);
2. the temporal group exposed by interaction jets through order \(r\)
   satisfies
   \[
    \boxed{\dim K_{r+1}\le M_r-1;}                    \tag{28}
   \]
3. for \(0\le r<n\), the interval-function capacity is exactly
   \[
    \boxed{
    C_{n,q}(r):=M_r-1
    =
    n(q-1)q^r
    -(q-1)^2\sum_{d=1}^{r}d\,q^{d-1};
    }                                                 \tag{29}
   \]
4. its exact missing-capacity remainder is
   \[
    \boxed{
    q^n-1-C_{n,q}(r)
    =
    (q-1)^2
    \sum_{d=r+1}^{n-1}(n-d)q^{d-1};
    }                                                 \tag{30}
   \]
5. consequently, for \(0\le r\le n-2\),
   \[
    \boxed{
    \operatorname{rank}F^{r+1}
    \ge
    (q-1)^2
    \sum_{d=r+1}^{n-1}(n-d)q^{d-1}>0;
    }                                                 \tag{31}
   \]
6. if additionally \(F^\infty=\{0\}\), the right side of `(31)` is a
   lower bound for the number of independent temporal directions whose
   breaking order is at least \(r+1\).

In particular, at \(r=n-2\), at least
\[
 \boxed{(q-1)^2q^{n-2}}                               \tag{32}
\]
independent temporal directions cannot activate before perturbative order
\(n-1\).

### Proof

Introduce one coupling \(\lambda_e\) per edge and let
\[
 H(\lambda)=A+\sum_e\lambda_eV_e.
\]
Simplicity of the spectrum of \(A\) gives, for each \(x\), a unique analytic
eigenvalue germ \(\mathcal E_x(\lambda)\) at \(\lambda=0\).

For an edge subset \(C\), define its Möbius cluster contribution
\[
 W_{x,C}(\lambda_C)
 =
 \sum_{S\subseteq C}
 (-1)^{|C|-|S|}
 \mathcal E_x(\lambda_S),                             \tag{33}
\]
where \(\lambda_S\) sets all couplings outside \(S\) to zero. Boolean-lattice
Möbius inversion gives
\[
 \mathcal E_x(\lambda)
 =
 \sum_{C\subseteq E(P_n)}W_{x,C}(\lambda_C).          \tag{34}
\]

Every Taylor monomial surviving `(33)` contains every variable
\(\lambda_e\), \(e\in C\), with positive exponent. Hence
\[
 [\lambda^{\alpha}]W_{x,C}=0
 \quad\text{when}\quad |\alpha|<|C|.                 \tag{35}
\]
If \(C\) is disconnected, the Hamiltonian with only the edges of \(C\)
splits as a tensor sum over its connected components and isolated sites.
The eigenvalue branch issuing from \(x\) is the corresponding sum of
component branches. A mixed Boolean difference involving edges in two
different components annihilates such an additive function, so
\[
 W_{x,C}=0
 \qquad\text{for every disconnected }C.              \tag{36}
\]

Set every \(\lambda_e=g\). Equations `(34)`--`(36)` show that the
coefficient of \(g^\ell\) is a sum only over connected edge sets with at
most \(\ell\) edges. On a path, each such set is an interval on at most
\(\ell+1\) sites. Its cluster weight depends only on the restriction of
\(x\) to that interval: all onsite contributions outside the interval
cancel in `(32)`. Thus
\[
 \epsilon_\ell\in
 \mathbb R\otimes_{\mathbb Q}\mathcal L_\ell
 \subseteq
 \mathbb R\otimes_{\mathbb Q}\mathcal L_r,
 \qquad \ell\le r,                                   \tag{37}
\]
proving item 1.

Choose a rational basis \(f_1,\ldots,f_{M_r}\) of \(\mathcal L_r\) and
write
\[
 \epsilon_\ell(x)=\sum_{a=1}^{M_r}c_{\ell a}f_a(x).
\]
For each configuration \(x\), form its jet vector
\[
 J_r(x)=(\epsilon_0(x),\ldots,\epsilon_r(x))
       =\sum_{a=1}^{M_r}f_a(x)c_a
       \in\mathbb R^{r+1},                            \tag{38}
\]
where \(c_a=(c_{0a},\ldots,c_{ra})\). The rational span of all differences
\(J_r(x)-J_r(x_0)\) has dimension at most \(M_r-1\): choose the first basis
vector to be the constant function, whose contribution cancels in every
difference.

The quotient \(\Gamma_X/F^{r+1}\) is exactly the subgroup generated by
these projective jet differences: a zero-sum integer vector \(k\) maps to
\[
 \left(\sum_xk_x\epsilon_0(x),\ldots,
       \sum_xk_x\epsilon_r(x)\right),                 \tag{39}
\]
and its kernel is `(9)`. Hence
\[
 \dim K_{r+1}
 =
 \operatorname{rank}(\Gamma_X/F^{r+1})
 \le M_r-1,                                           \tag{40}
\]
which is `(28)`.

To compute \(M_r\), choose at each site a rational basis consisting of the
constant function and \(q-1\) contrast functions. Their tensor products
form a basis of \(\mathbb Q^X\). A nonconstant tensor basis vector lies in
\(\mathcal L_r\) exactly when its active-site set is contained in an
interval of length at most \(r+1\), equivalently when its diameter is at
most \(r\).

There are \(n(q-1)\) basis vectors with one active site. For active diameter
\(d\ge1\), choose the left endpoint in \(n-d\) ways, choose nonconstant
contrasts at both endpoints in \((q-1)^2\) ways, and choose at each of the
\(d-1\) interior sites either the constant or one of the \(q-1\) contrasts,
in \(q^{d-1}\) ways. Therefore
\[
 M_r-1
 =
 n(q-1)
 +(q-1)^2\sum_{d=1}^{r}(n-d)q^{d-1},                 \tag{41}
\]
which is algebraically identical to `(29)`. The basis vectors absent from
\(\mathcal L_r\) have diameter \(d\ge r+1\); counting them by the same
argument proves `(30)`.

Equations `(28)` and `(30)` give `(31)`. If \(F^\infty=\{0\}\), all
independent constraints in \(F^{r+1}\) eventually disappear, and each has
breaking order at least \(r+1\). Substituting \(r=n-2\) gives `(32)`.
\(\square\)

### Physical consequence

Local interaction can make the completed temporal dimension exponential,
but locality forbids this from being a bounded-order perturbative event.
If the local generator theorem supplies \(F^\infty=\{0\}\), at least one
and in fact at least \((q-1)^2q^{n-2}\) independent new temporal directions
have breaking order at least \(n-1\). Each therefore requires a resolution
horizon
\[
 T\asymp |g|^{-v(k)}
 \gtrsim |g|^{-(n-1)}.                                \tag{42}
\]
Equation `(42)` concerns complete phase reconstruction; a fixed low-order
reporter may activate much earlier.

## Arbitrary-spectrum completion

For a probability spectral law \(\mu\) on \(\mathbb R\), finite or
continuous, put
\[
 \rho_m=\mu^{*m}*\widetilde{\mu}^{*m}.                \tag{43}
\]
Then, for every \(m\ge1\),
\[
 \boxed{
 \frac1{2T}\int_{-T}^{T}|\widehat\mu(t)|^{2m}\,dt
 =
 \int_{\mathbb R}\operatorname{sinc}(Tx)\,d\rho_m(x),
 \qquad
 \lim_{T\to\infty}(\cdots)=\rho_m(\{0\}).
 }
                                                               \tag{44}
\]
This is the measure-valued completion of `(12)`: exact collisions are the
zero atom; near-collisions are the mass close enough to zero to survive the
finite horizon. It covers every spectral type. The valued-lattice
wall-crossing theorem is the sharper atomic analytic specialization.

Equation `(44)` is classical Fourier/spectral analysis and is not a novelty
claim.

## Exact synthesis of prior results

| Prior result or obstruction | Shadow of the valued constraint law |
|---|---|
| Observer-dependent temporal dimension | Character rank of the observer-visible quotient of \(K_1\). |
| Exact recurrence and periodicity | Cyclicity and return geometry of \(K_1\). |
| Higher no-resonance hierarchy | Height truncations \(h(k)\le m\) of \(F^1\). |
| Replica-collision floor | Vanishing of every nonzero relation at every finite height. |
| Finite-horizon stability | Small-\(T\delta_k\) side of the sinc crossover. |
| Missing upper crossover | Large-\(T\delta_k\) side of `(21)`--`(23)`. |
| Finite perturbation no-go | A relation with \(v(k)>r\) is invisible through interaction order \(r\). |
| Weak-coupling/completed-time noncommutation | Jump from \(K_1\) to \(K_\infty\). |
| Perturbative locality | Theorem F bounds stage-\(r\) temporal dimension by interval-function capacity. |
| Local interaction maximality | Generic local interaction makes \(F^\infty=\{0\}\). |
| Free/integrable excess collisions | Nonzero \(F^1\), often of extensive rank. |
| Infinite pure-point systems | Infinite filtered relation group with finite-support characters. |
| Continuous spectrum | Relation measures `(43)` replace discrete relation vectors. |
| Failed horizon criterion | Spectral type changes temporal return law, but no universal horizon equivalence follows. |

The synthesis claim is exact: these rows are not merely analogous. They are
obtained by applying height truncation, perturbation valuation, observer
restriction, Pontryagin duality, or spectral-measure completion to one
constraint object.

## Relation to the local-interaction theorem

For an onsite \(n\)-qudit Hamiltonian, the initial compact temporal group
has dimension at most \(n(q-1)\). The parent local theorem claims that for
almost every nearest-neighbour interaction profile the persistent relation
lattice is trivial, so
\[
 \dim K_\infty=q^n-1.                                 \tag{45}
\]
If that parent theorem survives formalization, `(7)`--`(8)` refine its
single jump into an exact cascade:
\[
 \sum_{r\ge1}\Delta d_r
 \ge q^n-1-n(q-1).                                   \tag{46}
\]
Every one of those exponentially many activated dimensions has a definite
first interaction order and inverse-detuning observation scale. Theorem F
adds that the final stages cannot occur at bounded perturbative order:
locality forces at least one finite breaking order to be
\(n-O(\log n)\) when \(q\) is fixed.

## Competing higher conjectures and kill decisions

### Candidate 1 — time is the annihilator of spectral relations

Correct:
\[
 K_1=\operatorname{Ann}(F^1).
\]
**Killed as novelty.** This is classical resonance-module/Pontryagin
duality and repeats the failure mode of the corpus's Cauchy-constraint
Schubert route. It remains infrastructure only.

### Candidate 2 — every observable is its transformation algebra modulo its
annihilator

Correct at the level of cyclic modules.
**Killed as master law.** It is too general, tautological, and physically
nonpredictive. It does not produce a finite-time scale, a wall-crossing
profile, or a new quantum consequence.

### Candidate 3 — time is the failure of observational and spectral
completion to commute

This captures the weak-coupling singularity but is incomplete.
**Absorbed, not selected.** The valued filtration says exactly when the
limits fail to commute and resolves the transition into power-law stages.

### Candidate 4 — valued spectral constraints generate quantum time

**Provisional survivor.** It adds the filtration, exact double-scaling
limit, sinc transition measure, detector/perturbation/time trinity, and
finite-order upper crossover. Theorem F then turns interaction locality into
a perturbative temporal light cone. Those consequences are absent from bare
annihilator duality.

## Primary-literature boundary

1. Mark et al., *Phys. Rev. X* **14**, 041051 (2024),
   <https://arxiv.org/abs/2403.11970>, prove that the infinite-time temporal
   ensemble equals the random-phase ensemble exactly under all-order
   no-resonance and study finite-time sinc convergence. They do not in the
   checked source formulate the order-of-vanishing filtration of an
   interacting spectral path, its dual dimension cascade, or the
   double-scaling laws `(14)`--`(16)`.
2. Riddell and Pagliaroli,
   <https://arxiv.org/abs/2307.05417>, study violations and near violations
   of higher no-resonance conditions and their consequences for quantum
   equilibration. Their checked statement does not give the analytic
   interaction-valuation classification.
3. Campos Venuti, Odavić and Hamma,
   <https://arxiv.org/abs/2505.05199>, derive exact arbitrary spectral-form
   factor moments under finite-order nondegeneracy and the
   independent-phase thermodynamic law. Those are consequences here, not
   novelty.
4. Short and Farrelly,
   <https://arxiv.org/abs/1110.5759>, give finite-time equilibration bounds
   under controlled energy-gap degeneracy. This is a parent finite-time
   result, not the filtered wall-crossing theorem.
5. Parameter-dependent resonance lattices occur in normal-form theory.
   A targeted search found the ordinary persistent intersection of
   resonance lattices, but not the valued filtration joined to quantum
   temporal ensembles and exact crossover measures. Full specialist
   priority audit remains mandatory.
6. Linked-cluster literature already establishes cancellation of
   disconnected energy contributions and perturbative cluster-size bounds;
   for example Bastianello and Sotiriadis,
   <https://arxiv.org/abs/1601.02532>. Theorem F does not claim that parent
   fact. Its candidate-new content is the exact conversion from cluster
   locality to interval-function capacity `(29)`, spectral-relation
   remainder `(30)`--`(32)`, and temporal activation depth.

## Hostile attack

### 1. “This is Taylor expansion plus a sinc integral”

Valid mechanism attack. Equations `(12)` and `(17)` are elementary.
Novelty cannot rest on either ingredient. It must rest on the exact joined
classification: a saturated filtration, its Pontryagin-dual cascade, the
all-reporter double-scaling measure, minimal replica-height reconstruction,
and the local-interaction consequence.

### 2. “Temporal dimension is rhetoric”

The paper must define \(K_r\) operationally as the weak limit of temporal
sampling and prove its metric/character dimension. It must never imply
extra spacetime coordinates.

### 3. “The theorem concerns a tuned integrable point, not generic physics”

The theorem quantifies every analytic path, not only generic ones:
persistent constraints have \(v=\infty\); broken constraints have a unique
finite activation order. The local generator supplies a broad physical
family in which all nontrivial constraints are broken. Symmetry-restricted
paths remain classified rather than excluded.

### 4. “Infinite time still does the work”

The double-scaling theorem is specifically finite-horizon. For each fixed
replica order it gives both sides of the crossover and the complete
transition profile. It does not yet give one uniform all-order or
thermodynamic observation time.

### 5. “No device can measure all mixed tensors”

Complete reconstruction is a classification theorem, not a proposed single
experiment. A publishable physics paper still needs a finite low-order
protocol or an existing platform where a predicted \(g^{-r}\) cascade can
be distinguished.

### 6. “The local maximality parent is not formally closed”

Fatal for the local-physics claim. Until formalized, the abstract
wall-crossing theorem may be used only for arbitrary analytic spectral
paths; equations `(45)`--`(46)` cannot appear as proved manuscript claims.

### 7. “The locality result is a loose parameter count”

It is not a parameter count. Equation `(29)` is the exact dimension of the
rational interval-function space, and `(30)` is its exact complement in
the full configuration-function space. The theorem is nevertheless an
upper bound on temporal rank; sharp attainment at every intermediate order
has not been proved.

### 8. “Simple onsite spectrum excludes important models”

Theorem F needs a simple product spectrum to label analytic eigenvalue
branches without degenerate perturbation theory. Generic inhomogeneous
onsite Hamiltonians satisfy this. Translation-invariant,
symmetry-degenerate, and thermodynamic starting points need block-valued or
symmetry-resolved extensions and cannot be claimed from the present proof.

### 9. “Continuous and open systems are missing”

Continuous unitary spectra are covered by `(43)`--`(44)`, but the valued
wall crossing is presently atomic. General quantum channels require a
separate peripheral-spectrum version with decay rates and must not be
claimed from this theorem.

### 10. “Nature significance is not earned by a universal formalism”

Correct. A Nature case requires one surprising physical consequence beyond
classification: preferably a proved local many-body cascade, a measurable
finite-order activation exponent, or a theorem constraining black-hole/SYK
spectral-form-factor crossover. This card has found the candidate generator
law, not yet earned that application.

## New generator: spectral causality on an interaction graph

The interval-capacity theorem has a much smaller and stronger witness. Let
\(G\) be the interaction graph, let \(u\ne v\) be sites at graph distance
\(d_G(u,v)\), and fix a product configuration \(x\). Choose alternative
local values \(a\ne x_u\) and \(b\ne x_v\). Write \(x^a,x^b,x^{ab}\) for
the configurations obtained by changing the indicated coordinates and
define the four-level relation
\[
 \kappa_{u,v;x,a,b}
   =e_{x^{ab}}+e_x-e_{x^a}-e_{x^b}. \tag{47}
\]
It is balanced, has replica height two, and pairs with a configuration
function \(f\) as the mixed finite difference
\[
 \langle\kappa_{u,v;x,a,b},f\rangle
   =f(x^{ab})+f(x)-f(x^a)-f(x^b). \tag{48}
\]

**Theorem G (graph-distance spectral causality).** Suppose the order-\(r\)
energy jet is a sum of functions supported on connected interaction
clusters using at most \(r\) edges. Then, for every finite interaction
graph, every pair \(u,v\), every background \(x\), and every pair of local
changes,
\[
 \left\langle\kappa_{u,v;x,a,b},\epsilon_r\right\rangle=0
 \qquad(0\le r<d_G(u,v)). \tag{49}
\]
Consequently
\[
 v(\kappa_{u,v;x,a,b})\ge d_G(u,v),\qquad
 \delta_{\kappa_{u,v;x,a,b}}(g)=O(|g|^{d_G(u,v)}). \tag{50}
\]
The proof is exact: a connected cluster with fewer than \(d_G(u,v)\)
edges cannot contain both sites. Its local function therefore misses at
least one of the two changed coordinates, so its mixed difference `(48)`
cancels pairwise.

For a \(q\)-level \(n\)-site product system and a fixed pair \(u,v\), the
relations `(47)` obtained from every configuration of the other \(n-2\)
sites and every pair of non-base endpoint values contain
\[
 (q-1)^2q^{n-2} \tag{51}
\]
linearly independent height-two relations. Independence is witnessed by
the configuration in which both endpoints take their chosen non-base
values: it occurs in exactly one standard contrast within each fixed
background block.

The finite-horizon implication is operational. If
\(T(g)|g|^{d_G(u,v)}\to0\), then
\[
 T(g)\delta_{\kappa_{u,v;x,a,b}}(g)\to0,\qquad
 \operatorname{sinc}\!\left(
   T(g)\delta_{\kappa_{u,v;x,a,b}}(g)\right)\to1. \tag{52}
\]
No second-replica temporal measurement can yet distinguish the broken
relation. If its distance-order coefficient is nonzero, the crossover
occurs on the sharp scale
\[
 T\asymp |g|^{-d_G(u,v)}. \tag{53}
\]
If symmetry cancels that coefficient, the horizon is later, never earlier.

This is the candidate physical headline:

> **Quantum time cannot activate across space faster than interactions can
> connect that space.**

It is not a Lieb--Robinson propagation bound. It concerns the birth of
independent spectral phases and recurrence directions under weak coupling,
not signal velocity at fixed coupling. At \(|g|<1\), the minimum
observation horizon grows exponentially with graph distance even though
the reporter uses only two replicas.

Theorem G supplies what Theorem F lacked:

1. a low-order reporter rather than an all-order reconstruction device;
2. exponentially many independent witnesses for each fixed distant pair;
3. a spatially resolved prediction, not only a global rank remainder;
4. a direct experimental scaling exponent: change distance and measure the
   weak-coupling crossover exponent;
5. an exact reinterpretation of the earlier corpus. Replica order is
   detector complexity, interaction-graph distance is activation depth,
   inverse detuning is observation time, and recurrence dimension is the
   number of already activated contrasts.

The connected-cluster premise in Theorem G is not manuscript-ready until
proved for the actual analytic eigenvalue branches of finite local
Hamiltonians. The finite-difference cancellation and relation count are
independent unconditional algebraic theorems and should be formalized
first.

## Frozen jump: the spectral birth--recurrence law `[CONJECTURE]`

The linked-cluster statement alone is established physics and cannot carry
novelty. The stronger conjecture is that its support obstruction is
generically sharp and is the missing first half of the recurrence law.

For a finite interaction graph \(G=(V,E)\) and a nontrivial site packet
\(S\subset V\), define its birth depth
\[
 \tau_G(S)
 =
 \min\{|C|:C\subset E,\ C\text{ is connected and spans }S\}. \tag{54}
\]
Let \(\epsilon_x(g)\) be the analytic eigenvalue branch born from product
configuration \(x\) under a generic edge-local perturbation, and let
\(\mathcal M_S\epsilon(g)\) be any nonzero anchored Möbius contrast on
exactly the sites in \(S\).

The frozen conjecture is
\[
 \boxed{
 \operatorname{ord}_{g=0}\mathcal M_S\epsilon(g)=\tau_G(S)
 }
 \qquad\text{simultaneously for every }S\text{ and contrast}. \tag{55}
\]
Equivalently, the multivariate Taylor tensors through depth \(r\) generate
exactly—not merely a subspace of—the Steiner-eligible interaction modes at
depth \(r\). The lower bound in `(55)` is the universal obstruction; equality
is the generic saturation claim.

If the leading coefficient is \(c_S\ne0\), then the corresponding balanced
spectral relation has
\[
 \delta_S(g)=c_Sg^{\tau_G(S)}+O(g^{\tau_G(S)+1}),\qquad
 T_S(g)\asymp |g|^{-\tau_G(S)}. \tag{56}
\]
After these packets become resolvable, their rational span is the
observer-visible temporal dimension; Haar target volume then gives exact
recurrence density. Thus the proposed one-law cascade is
\[
 \boxed{
 \text{interaction connectivity}
 \longrightarrow
 \text{spectral birth depth}
 \longrightarrow
 \text{resolvability time}
 \longrightarrow
 \text{temporal rank}
 \longrightarrow
 \text{return rarity}.
 } \tag{57}
\]

This conjecture is false if one can exhibit a graph, local alphabet and
Steiner-eligible contrast whose depth-\(\tau_G(S)\) coefficient vanishes
identically throughout the full edge-local interaction space. A symmetry or
fine-tuned Hamiltonian is not a counterexample to the generic equality; an
identical polynomial cancellation is.

## Universal generator law: connectivity is observable depth

The prior results are not separate effects. They are shadows of one exact
generator--observer law:

> **An irreducible joint observable becomes visible at exactly the first
> generator depth whose interaction support can contain it.**

There are two dual filtrations. The generator filtration asks which
interaction packets can be made by words of length \(n\). The observer
filtration asks which packets survive Möbius contrast. A word of length
\(n\) uses at most \(n\) distinct interaction labels; a Möbius probe
extracts only words using every label in its packet. Therefore, for every
finite interaction set \(E\), every field, every order \(n\), every
coefficient assignment to length-\(n\) words, and every packet \(C\subset
E\),
\[
 |C|>n
 \quad\Longrightarrow\quad
 \mathcal M_C F_n=0. \tag{58}
\]
This is exact, not asymptotic.

For an arbitrary formal analytic series
\[
 P=(P_0,P_1,\ldots),\qquad
 P_n:(\mathbb C^E)^n\longrightarrow\mathbb C, \tag{59}
\]
restrict the coupling vector \(z\) to \(D\subset E\), and define the
packet coefficient
\[
 W_C^{(n)}(z)=
 \mathcal M_C\!\left[
   D\longmapsto P_n(z|_D,\ldots,z|_D)
 \right]. \tag{60}
\]
The exact Taylor-depth law is
\[
 W_C^{(n)}(z)=0\quad(n<|C|), \qquad
 P_n(z,\ldots,z)=\sum_{\substack{C\subset E\\|C|\le n}}
 W_C^{(n)}(z). \tag{61}
\]
Thus order \(n\) is not merely bounded by a parameter count: it is
*exactly decomposed* into interaction packets of depth at most \(n\).

Connectivity supplies the second half. For arbitrary finite matrices over
any commutative domain, if \(a\) is a characteristic root of \(A\) and
\(b\) is a characteristic root of \(B\), then
\[
 a+b\text{ is a characteristic root of }
 A\otimes I+I\otimes B. \tag{62}
\]
For analytic matrix families with simple product energy, branch uniqueness
upgrades `(58)` to equality of germs:
\[
 \epsilon_{A\boxplus B}=\epsilon_A+\epsilon_B. \tag{63}
\]
No self-adjointness, normality, diagonalizability, or closed-system
assumption is needed for `(58)`--`(59)`.

If a packet \(C=C_1\sqcup C_2\) is dynamically disconnected, `(59)` makes
its restricted spectral response additive across \(C_1,C_2\). Boolean
Möbius contrast then cancels it exactly:
\[
 \mathcal M_C(F_1+F_2)=0. \tag{64}
\]
Combining `(61)` and `(64)` leaves only connected packets with at most
\(n\) interactions. Combining that fact with the exact
Steiner--Möbius duality proves the desired causal statement: an
irreducible site packet is spectrally invisible below its Steiner
connectivity cost.

This answers “what does it mean?”:

1. perturbative order is generator depth;
2. graph/Steiner cost is the birth depth of a joint spectral fact;
3. Möbius contrast is the canonical observer for that fact;
4. recurrence dimension counts facts already born at the available
   depth;
5. inverse detuning converts birth depth into observation time;
6. replica height measures detector complexity, independently of spatial
   connectivity.

The worldview claim is therefore not “the future cannot be hidden for
free.” It is:

> **The dimension of observable quantum time is built, packet by packet,
> by interaction connectivity.**

This can become the master law only after the remaining transfer below is
closed. Until then it is a proved universal analytic-combinatorial law
plus a proved disconnected spectral theorem, not yet a proved theorem for
every local Hamiltonian.

### Formal closure ledger for the generator law

`formal/GaloisForLFunctions/HTGeometry/ParametricSpectralBranch.lean`
now checks:

1. analytic simple-eigenvalue branches for arbitrary finite complex
   matrix families;
2. uniqueness of continuous characteristic-root germs at every simple
   diagonal eigenvalue;
3. exact Kronecker-sum root addition over every commutative domain;
4. exact additivity of analytic disconnected eigenvalue branches.

`formal/GaloisForLFunctions/HTGeometry/SpectralClusterTransfer.lean`
now checks:

1. every length-\(n\) interaction word has support cardinality at most
   \(n\);
2. Möbius probes annihilate every larger interaction packet;
3. arbitrary homogeneous analytic coefficients are word-generated;
4. exact vanishing `(57)` below packet depth;
5. exact bounded reconstruction `(57)` at every order;
6. exact Möbius cancellation for every response additive across two
   nonempty disconnected packets.

The remaining fatal bridge is no longer a linked-cluster theorem in the
abstract. It is the concrete tensor-reindexing instance:

1. define the full finite local Hamiltonian
   \(H_0+\sum_e\lambda_eV_e\) on product configurations;
2. prove that restriction to a disconnected edge packet is, after basis
   reindexing, the Kronecker sum of its component Hamiltonians;
3. use germ uniqueness to identify the globally labelled branch with the
   component sum;
4. prove the resulting connected packet coefficient is local on its
   incident sites;
5. compose `(57)`, `(60)`, and the already proved
   Steiner--Möbius theorem.

Only after those five items may the manuscript state the local-Hamiltonian
law or its \(T\asymp |g|^{-\tau}\) observation-time consequence.

### Formal closure ledger for Theorem G

The following are now checked in
`formal/GaloisForLFunctions/HTGeometry/SpectralCausality.lean`:

1. every coordinate-local function missing either endpoint has zero mixed
   contrast;
2. finite sums preserve the cancellation;
3. every connected subgraph containing \(u,v\) has at least
   \(d_G(u,v)\) edges;
4. every depth-\(r\) connected-cluster sum has zero two-site contrast when
   \(r<d_G(u,v)\);
5. the rectangle relations are linearly independent;
6. their span has exact dimension `(51)`;
7. every rectangle relation has an explicit two-replica balanced
   representation.

The new
`formal/GaloisForLFunctions/HTGeometry/ParametricSpectralBranch.lean`
proves a holomorphic implicit-function theorem over an arbitrary complete
complex parameter space. This supplies the branch engine for assigning one
coupling coordinate to every interaction edge.

All listed declarations compile with `lake env lean`; their axiom audit
contains only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. The missing theorem is now sharply isolated: prove that the
Taylor jet of every simple product-spectrum eigenvalue branch of
\(H_0+\sum_e\lambda_eV_e\) is a sum of connected cluster-local functions
using no more edges than its order.

## Exact falsifiers

Retire or demote the route if:

1. a primary source already proves the filtered Pontryagin-dual
   double-scaling theorem with equal scope;
2. the limit in `(14)` fails for some finite analytic spectrum;
3. \(F^r\) is not saturated or Haar Fourier reconstruction fails;
4. mixed moment tensors do not reconstruct every finite-support relation;
5. no physical family yields a nontrivial \(v>1\) stage or a measurable
   consequence beyond the standard \(1/|\delta|\) resolution heuristic;
6. the local generator theorem fails formal audit.

## Open core

1. Complete specialist literature audit in parameter-dependent normal
   forms, resonance modules, temporal ensembles, and singular perturbation.
2. Formalize Theorems A--C and Corollaries D--E unconditionally.
3. Formalize the local nearest-neighbour generator and instantiate
   \(F^\infty=\{0\}\).
4. Formalize the connected-cluster Möbius theorem, exact interval capacity,
   and relation-rank remainder of Theorem F.
5. Derive a finite physical witness of \(\Delta d_r\) or \(R_m\) using
   low-order temporal tensors. Theorem G gives the candidate height-two
   witness; formalize it and its graph-distance specialization.
6. Determine whether a symmetry class forces a nontrivial multi-stage
   cascade \(v=1,2,\ldots\), rather than one generic first-order activation.
7. Only then rewrite the master manuscript and run a hostile Nature review.

## Abductive jump: the temporal Steiner spectrum `[FROZEN CONJECTURE]`

The preceding law still describes several projections of one filtration. The
stronger candidate says what that filtration *is* for a local quantum system.

Let \(G=(V,E)\) be a finite connected interaction graph. Site \(v\) has a
finite pointed alphabet of size \(q_v\ge2\). For a nonempty site packet
\(S\subseteq V\), put
\[
 w(S)=\prod_{v\in S}(q_v-1)
 \quad\text{and}\quad
 \tau_G(S)=
 \min\{|C|:C\subseteq E,\ C\text{ is connected and spans }S\}.
                                                               \tag{65}
\]
Singletons have cost zero. Define the weighted Steiner birth spectrum
\[
 B_r(G,\mathbf q)
 =
 \sum_{\substack{\varnothing\ne S\subseteq V\\\tau_G(S)=r}}w(S).
                                                               \tag{66}
\]

The frozen conjecture is that, for a generic edge-local Hermitian affine
perturbation of a simple onsite product Hamiltonian, the order-\(r\)
associated graded piece of the projective spectral-constraint cascade has
dimension exactly
\[
 \boxed{\Delta d_r=B_r(G,\mathbf q).}                         \tag{67}
\]
Equivalently, the eigenvalue jets through depth \(r\) generate the entire
Steiner-eligible interaction-mode space and no more:
\[
 \boxed{
 \dim K_{r+1}
 =
 \sum_{\substack{\varnothing\ne S\subseteq V\\\tau_G(S)\le r}}
 \prod_{v\in S}(q_v-1).
 }                                                             \tag{68}
\]
This is simultaneous over every site packet and every anchored contrast.
It is stronger than generic final rational independence and stronger than
the universal lower obstruction. It identifies the complete temporal birth
profile with a graph invariant.

The conceptual law is

> **A local quantum system's temporal architecture is the weighted Steiner
> geometry of its interaction network.**

This answers the recurring “what does it mean?” question:

1. a temporal direction is an irreducible joint distinction between product
   configurations;
2. its birth depth is the least interaction network capable of joining the
   sites carrying that distinction;
3. its detector cost is the replica height of the corresponding spectral
   relation;
4. its observation horizon is the inverse detuning created at that depth;
5. recurrence rarity is the Haar target volume after those directions have
   been born.

Disconnected cancellation, graph-distance delay, interval-capacity
remainders, weak-coupling singularity, observer quotients and recurrence
rank are therefore shadows of one object: the temporal Steiner spectrum and
its observer-visible quotient.

### Exact chain prediction

For the open \(n\)-site \(q\)-level chain, `(66)` is elementary:
\[
 B_0=n(q-1),\qquad
 \boxed{
 B_r=(n-r)(q-1)^2q^{r-1}
 }\quad(1\le r\le n-1).                                \tag{69}
\]
Indeed, a packet of path cost \(r\) has fixed left and right endpoints,
nonconstant contrasts at both endpoints, and an arbitrary constant or
nonconstant choice at each of the \(r-1\) interior sites. Consequently
\[
 \sum_{r=0}^{n-1}B_r=q^n-1,                            \tag{70}
\]
and the exact fraction of final temporal dimension still unborn after
depth \(R\) would be
\[
 \boxed{
 \frac{\sum_{r=R+1}^{n-1}B_r}{q^n-1}
 =
 \frac{(q-1)^2\sum_{r=R+1}^{n-1}(n-r)q^{r-1}}
      {q^n-1}.
 }                                                       \tag{71}
\]

For every fixed \(0<\alpha<1\), `(71)` tends to one when
\(R=\lfloor\alpha n\rfloor\). Thus asymptotically almost every independent
temporal direction is born only at interaction order linear in system size,
not at any bounded or subextensive order.

More sharply, choose one of the \(q^n-1\) nonconstant temporal modes
uniformly and let \(R_n\) be its birth depth. For every fixed \(s\ge1\),
\[
 \boxed{
 \lim_{n\to\infty}\Pr[n-R_n=s]
 =
 \frac{(q-1)^2s}{q^{s+1}}.
 }                                                       \tag{72}
\]
The limiting mean distance from full-system depth is
\[
 \boxed{
 \lim_{n\to\infty}\mathbb E[n-R_n]
 =
 \frac{q+1}{q-1}.
 }                                                       \tag{73}
\]
For qubits, a typical temporal mode is therefore born only three
interaction edges short of spanning the whole chain.

At weak coupling, a mode of depth \(r\) has the sharp generic horizon
\[
 T_r(g)\asymp |g|^{-r}.                                 \tag{74}
\]
Equations `(69)`--`(74)` predict an extensive-depth concentration of an
exponential number of clocks. This is stronger than the earlier statement
that at least one mode is late and stronger than a dimension-linear
remainder: it gives the entire proposed birth distribution.

### What this would newly explain

The free or commuting limit is not merely a model with unusually many
resonances. It is the depth-zero face of a temporal birth spectrum. Turning
on local noncommuting interaction does not create the final projective torus
at once. It resolves a sequence of Steiner layers. Almost all of the final
torus lies in layers whose generator words nearly span the system.

The resulting worldview is:

> **Most many-body quantum time is globally born, even when every
> interaction is local.**

This does not assert extra spacetime dimensions. It says that almost all
rationally independent phases controlling complete recurrence are
irreducible global facts and become operational only on horizons set by
system-spanning virtual interaction depth.

### Hard falsifiers

The conjecture is killed, not weakened, by any of:

1. a finite graph, finite local alphabet and anchored contrast whose
   coefficient at exact Steiner cost vanishes identically over the full
   edge-local Hermitian interaction space;
2. a path-local counterexample to the exact birth numbers `(69)`;
3. a structural parity, closed-walk or perturbative-selection rule forcing
   birth strictly after Steiner cost for an open set of unrestricted
   edge-local interactions;
4. a primary source already proving the exact associated-graded
   identification `(67)`--`(68)` for local Hamiltonian eigenvalue branches;
5. failure of the existing generic maximal-rank endpoint, which would make
   `(70)` physically unattainable.

Fine tuning, symmetry restriction or a specially chosen interaction does
not falsify generic equality. An identically zero leading coefficient does.

### Proven lower half and new obligations

The generator-support, disconnected-sector and Steiner--Möbius theorems
already prove the inclusion
\[
 \text{order-\(\le r\) spectral jets}
 \subseteq
 \text{Steiner-eligible modes of cost \(\le r\)}.       \tag{75}
\]
They also prove the exact dimension of the right side for every finite graph
and alphabet. The observation-horizon theorem converts every strict
inclusion into an operational delay.

The missing new theorem is the reverse inclusion generically for actual
local Hamiltonian eigenbranches. Before manuscript promotion:

1. attack `(67)` first on qubit paths, including parity and closed-walk
   selection rules;
2. prove or kill exact pair-distance birth;
3. if pair birth survives, prove the full path associated-graded statement;
4. only then attempt arbitrary trees and graphs;
5. formalize `(69)`--`(73)` independently of the sharpness conjecture, since
   they are unconditional properties of the weighted Steiner spectrum;
6. state physical recurrence consequences only after generic spectral
   sharpness and maximal final rank are both unconditional.

## First sharpness theorem: pair distance is generically exact

`[PAPER-PROVED; DEPENDENCY AUDIT PASSED; LEAN OPEN]`

The first hard falsifier does not occur for two-site contrasts.

**Theorem H (generic exact pair birth).** Let \(G\) be a finite interaction
graph, let \(u,v\) lie in one connected component, and put
\(d=d_G(u,v)\). Fix any product configuration \(x\) and alternatives
\(a\ne x_u\), \(b\ne x_v\). For every simple onsite product Hamiltonian
\(A\), the coefficient
\[
 V\longmapsto
 [g^d]\,
 \left(
 E_{x^{ab}}(g)+E_x(g)-E_{x^a}(g)-E_{x^b}(g)
 \right)                                               \tag{76}
\]
is a nonzero real-analytic function on the full space of edge-local
Hermitian interactions \(V\). Hence, outside a proper analytic null set,
\[
 \boxed{
 \operatorname{ord}_{g=0}
 \left(
 E_{x^{ab}}(g)+E_x(g)-E_{x^a}(g)-E_{x^b}(g)
 \right)
 =
 d_G(u,v).
 }                                                       \tag{77}
\]
Because there are only finitely many pairs, backgrounds and endpoint
alternatives, `(77)` holds simultaneously for all of them on a dense
full-measure set of interactions.

### Witness construction

Choose a shortest path
\[
 v_0=u,v_1,\ldots,v_d=v.
\]
At every internal path site choose one auxiliary local value different from
its background value. Set every interaction off the path to zero. In the
endpoint sector where \(v_0=a\) and \(v_d=b\), consider the configurations
\[
 s_0=x^{ab},\qquad
 s_j=\text{the configuration with one auxiliary token at }v_j
 \quad(1\le j\le d-1).
\]
Choose the edge interactions as follows:

1. the first edge creates or removes the token at \(v_1\), conditional on
   \(v_0=a\);
2. every internal edge swaps the token between its two endpoints;
3. the last edge removes or creates the token at \(v_{d-1}\), conditional
   on \(v_d=b\).

Each term is the sum of one local matrix unit and its adjoint, hence
Hermitian and edge-local. The reachable configuration block born from
\(s_0\) is the labelled cycle
\[
 s_0
 \mathrel{\mathop{\longleftrightarrow}^{\lambda_1}}
 s_1
 \mathrel{\mathop{\longleftrightarrow}^{\lambda_2}}
 \cdots
 \mathrel{\mathop{\longleftrightarrow}^{\lambda_{d-1}}}
 s_{d-1}
 \mathrel{\mathop{\longleftrightarrow}^{\lambda_d}}
 s_0.                                                    \tag{78}
\]
For \(d=2\), `(78)` is a two-vertex block with two independently labelled
parallel couplings. For \(d=1\), use the diagonal endpoint projector.

If either endpoint alternative is absent, one closing edge of `(78)` is
absent. The reachable block is a path, so it has no closed walk using every
edge label exactly once.

### Noncancellation of the leading coefficient

Write the distinct onsite energies of \(s_j\) as \(A_j\). For \(d\ge2\),
the square-free coefficient of the eigenvalue branch issuing from \(s_0\)
is
\[
 \boxed{
 [\lambda_1\cdots\lambda_d]E_{s_0}(\lambda)
 =
 \frac{2}{\prod_{j=1}^{d-1}(A_0-A_j)}
 \ne0.
 }                                                       \tag{79}
\]
The two terms are the two orientations of the labelled cycle. No
normalization counterterm contributes to this square-free monomial: every
proper edge subset is a forest and has no closed walk using each selected
label once. Equivalently, in the characteristic determinant, the only
permutations carrying \(\lambda_1\cdots\lambda_d\) are the two cyclic
orientations, while the simple-root derivative at \(A_0\) is nonzero.

For the other three endpoint sectors the coefficient is zero because the
cycle is open. Their mixed rectangle `(76)` therefore equals the nonzero
quantity `(79)`. For \(d=1\), the chosen diagonal endpoint projector gives
coefficient one.

The universal lower theorem gives vanishing below \(d\); `(79)` supplies a
witness at \(d\). Thus `(76)` is not identically zero. Real-analytic
zero-set theory gives `(77)` generically.

### Consequence

Graph distance is not merely a lower speed limit for spectral birth. It is
the exact generic activation exponent of every height-two endpoint
contrast:
\[
 T_{u,v}(g)\asymp |g|^{-d_G(u,v)}.                     \tag{80}
\]
This proves the complete pairwise layer of the temporal Steiner spectrum.
The remaining conjecture is genuinely higher-order: simultaneous exact
birth for arbitrary multi-site packets, especially branched Steiner trees.

### Formal status

`TemporalSteinerBirthSpectrum.lean` now unconditionally defines the
projective Steiner capacity and its exact birth multiplicities, proves
monotonicity, proves the telescoping birth-sum law, and proves that every
finite connected graph saturates at
\[
 |\text{local alphabet}|^{|V|}-1.
\]
The pair witness still requires formalization of the labelled-cycle
square-free eigenbranch coefficient `(79)` and its edge-local tensor
embedding. Until those declarations compile and pass the axiom/lint gate,
Theorem H and `(80)` are not authorized manuscript claims.

## Exact observer connected-sector law

`[LEAN-PROVED; MODULE AUDIT PASSED; MANUSCRIPT OPEN]`

The common invariant is now stronger than the earlier graph-only Steiner
filtration.  For every finite family of arbitrary many-site interaction
labels and every analytic eigenvalue branch born from a simple product level,
Boolean inversion in coupling space gives an exact direct packet
decomposition.  A second Boolean inversion over changed product-state sites
then leaves only packets that:

1. are nonempty;
2. are spatially indecomposable under every disjoint packet partition; and
3. touch every site queried by the observer.

Distinct packet sectors are pairwise orthogonal Möbius projectors.  Therefore
they cannot cancel as multivariate germs.  The full observer contrast is a
nonzero germ if and only if at least one connected spanning packet sector is
nonzero.  Every packet of cardinality \(n\) is
\(O(\lVert g\rVert^n)\) on every scalar coupling ray.

This exposes an exact observer-dependent invariant:
\[
  \dim_{\mathrm{time}}(O)
  :=
  \min\left\{
    |P|:\;
    P\text{ is connected, spans }O,\text{ and its irreducible observer
    response is a nonzero germ}
  \right\}.                                             \tag{81}
\]
It is the minimum number of jointly indispensable interaction channels
carrying any spectral-time response visible to observer \(O\).  Every purely
geometric hypergraph-Steiner lower bound is a lower bound for `(81)`.

The precise unconditional law is thus not that graph distance always equals
analytic onset.  Selection rules may delay a packet.  The law is:
\[
 \boxed{\text{observer-visible spectral time is the direct sum of its
 connected spanning interaction sectors.}}             \tag{82}
\]
Geometry fixes which sectors can exist and their earliest possible
perturbative order; dynamics fixes which eligible sectors are active.
Observer choice fixes which connected sectors survive.

Formal modules:

- `LocalSpectralObserverSteinerLaw.lean`: exact connected-spanning germ
  decomposition and hypergraph-Steiner \(O(|g|^r)\) onset bound;
- `LocalSpectralObserverDirectSumLaw.lean`: packet-projector orthogonality,
  exact noncancellation/visibility equivalence, active temporal layers,
  minimum observer spectral-time dimension, and its Steiner lower bound.

Both modules compile in the pinned toolchain with no warnings.  This law
requires neither Hermiticity, unitarity, positivity, pairwise interactions,
nor a closed-system dynamical interpretation.  It does require a finite
configuration matrix, a simple uncoupled product spectrum, finite local
interaction support, and local analyticity at zero coupling.  Those are
mathematical scope conditions, not claims about every physical regime.

### Antagonist status

The direct-sector theorem kills the most serious logical weakness of the
earlier framing: the paper no longer promotes a one-sided no-go bound into an
exact law.  Exactness now means exact decomposition and exact visibility,
while order sharpness is stated separately.

Remaining rejection risks:

1. calling `(81)` a dimension without proving its operational invariance
   under interaction-label refinement;
2. claiming a law of physical time instead of a law of observer-visible
   spectral response;
3. failing to specialize the arbitrary hypergraph law to standard
   \(k\)-local Hamiltonians and experimentally measurable spectroscopy;
4. failing to prove at least one nontrivial sharp family beyond the
   structural lower bound;
5. novelty overlap with linked-cluster/cumulant expansions if the
   observer-site Möbius projection, orthogonal packet sectors, and
   observer-dependent minimum are not distinguished by a primary-source
   literature audit;
6. extrapolating to black holes, cosmology, thermodynamic limits, continuous
   spectra, or open-system generators without separate theorems.
