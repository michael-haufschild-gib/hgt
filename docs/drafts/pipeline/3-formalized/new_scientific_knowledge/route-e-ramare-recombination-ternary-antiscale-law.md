# Route E Ramaré recombination and ternary antiscale law

- **ID:** `ROUTE-E-RAMARE-RECOMBINATION-TERNARY-ANTISCALE-001`
- **Stage:** 3-formalized
- **Type:** `[EXACT ARITHMETIC RECOMBINATION]` / `[ANALYTIC FIREWALL]` / `[POSITIVE SURVIVOR]`
- **Parent:** `../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **RH used:** no
- **Computation used:** no
- **Literature used:** no; internal-corpus derivation only
- **Lean status:** complete. Theorems A--G, including literal squarefree support, exact prime
  diagonal/off-diagonal recombination, collision split and bound, coprime firewall, cosine
  products, exact tail suprema, and measurable-set corollaries `(28)`, `(30f)`, are formalized
  unconditionally and imported by the RHTower umbrella.

## 1. Purpose

The current Gallagher lane isolates `ramarePrimeOffDiagonal P M W` and describes it as a sparse
prime-pair oscillatory residue. That description hides two exact phenomena:

1. Ramaré blocks recombine every nonrough squarefree integer with total coefficient exactly one;
2. different prime blocks collide at the same integer, so `p != q` does not imply distinct Mellin
   frequency.

This card proves the complete finite recombination formula. It identifies the part untouched by
prime incidence as the coprime Möbius near-diagonal covariance. It then rewrites that coprime part
as a ternary prime cube and proves a finite-height large-values law. The cube has cofinal antiscale
recurrences, but those peaks occupy an exponentially small proportion of a frequency interval once
the marker primorial is below the square root of the interval length.

The result does not prove `OffDiagonalSmall` and does not close Route E. It removes a false
prime-spacing route and exposes one new quantitative avenue: tensor the ternary marker law with a
source-faithful cofactor-flatness/column theorem.

## 2. Exact Ramaré recombination

Let `P` be a finite set of primes and put

\[
 \omega_P(n)=\#\{p\in P:p\mid n\},
 \qquad
 \mathcal N_P(M)=\{n\le M:\mu(n)^2=1,\ \omega_P(n)\ge1\}.
\tag{1}
\]

For `p in P` define the Ramaré cofactor polynomial

\[
 G_p(w)=
 \sum_{\substack{m\le M/p\\p\nmid m}}
 {\mu(m)\over \omega_P(m)+1}\,m^{2\pi i w}
\tag{2}
\]

and the bilinear polynomial

\[
 B_{P,M}(w)=\sum_{p\in P}\mu(p)p^{2\pi i w}G_p(w).
\tag{3}
\]

### Theorem A — exact recombination

For every real `w`,

\[
 \boxed{
 B_{P,M}(w)=\sum_{n\in\mathcal N_P(M)}\mu(n)n^{2\pi i w}.}
\tag{4}
\]

Moreover the square-multiple polynomial in the current Ramaré decomposition vanishes identically:

\[
 \boxed{
 \sum_{n\le M}\mu(n)
 {\#\{p\in P:p^2\mid n\}\over\omega_P(n)}n^{2\pi i w}=0,}
\tag{5}
\]

where a zero denominator contributes zero. Hence the exact Möbius decomposition is simply

\[
 \sum_{n\le M}\mu(n)n^{2\pi i w}
 =B_{P,M}(w)+
   \sum_{\substack{n\le M\\\omega_P(n)=0}}\mu(n)n^{2\pi i w}.
\tag{6}
\]

#### Proof

Fix `n <= M`. A contribution to `(3)` indexed by `p` has `n=pm`, `p in P`, and `p` does not divide
`m`. If it is nonzero, `m` is squarefree; adjoining `p` therefore gives a squarefree `n`, and

\[
 \mu(p)\mu(m)=\mu(n),
 \qquad
 \omega_P(m)+1=\omega_P(n).
\tag{7}
\]

Conversely, every `n in N_P(M)` occurs once for each of its `omega_P(n)` designated prime factors.
Each occurrence has coefficient `mu(n)/omega_P(n)`, so their sum is `mu(n)`. If `n` is not
squarefree, either the selected prime occurs twice, in which case the filter `p does not divide m`
removes it, or another prime occurs twice, in which case `mu(m)=0`. This proves `(4)`.

Every nonzero numerator count in `(5)` gives `p^2 | n` for some prime `p`, hence `mu(n)=0`. Thus
every summand in `(5)` is zero. Splitting the full squarefree support according to
`omega_P(n)=0` or `omega_P(n)>=1` proves `(6)`. No estimate is used.

## 3. The prime off-diagonal is an integer-incidence complement

For `n,m in N_P(M)` set

\[
 k_n=\omega_P(n),
 \qquad
 c_P(n,m)=\#\{p\in P:p\mid n\text{ and }p\mid m\}
             =\omega_P(\gcd(n,m)).
\tag{8}
\]

For `W >= 0`, let

\[
 K_W(n,m)=\int_{-W}^{W}(n/m)^{2\pi i w}\,dw
 =\begin{cases}
 2W,&n=m,\\[2mm]
 \displaystyle {\sin(2\pi W\log(n/m))\over\pi\log(n/m)},&n\ne m.
 \end{cases}
\tag{9}
\]

This is real and symmetric. Let `O_P(M,W)` denote the ordered `p != q` term called
`ramarePrimeOffDiagonal P M W` in Lean.

### Theorem B — exact prime-pair recombination law

\[
 \boxed{
 O_P(M,W)=
 \sum_{n,m\in\mathcal N_P(M)}
 \mu(n)\mu(m)
 \left(1-{c_P(n,m)\over k_nk_m}\right)K_W(n,m).}
\tag{10}
\]

Equivalently,

\[
 \begin{aligned}
 O_P(M,W)
 &=2W\sum_{n\in\mathcal N_P(M)}\left(1-{1\over k_n}\right)\\
 &\quad+
 \sum_{\substack{n,m\in\mathcal N_P(M)\\n\ne m}}
 \mu(n)\mu(m)
 \left(1-{c_P(n,m)\over k_nk_m}\right)K_W(n,m).
 \end{aligned}
\tag{11}
\]

The prime diagonal is the complementary incidence term

\[
 D_P(M,W)=
 \sum_{n,m\in\mathcal N_P(M)}
 \mu(n)\mu(m){c_P(n,m)\over k_nk_m}K_W(n,m),
\tag{12}
\]

and therefore

\[
 \boxed{
 D_P(M,W)+O_P(M,W)
 =\int_{-W}^{W}
 \left|\sum_{n\in\mathcal N_P(M)}\mu(n)n^{2\pi i w}\right|^2dw.}
\tag{13}
\]

#### Proof

After `(4)`, the coefficient of the copy of `n` in the `p`-block is `mu(n)/k_n` whenever
`p in P` divides `n`. For fixed `n,m`, there are `k_n k_m` ordered block pairs `(p,q)`. Exactly
`c_P(n,m)` have `p=q`. Thus the number with `p != q` is `k_n k_m-c_P(n,m)`, proving `(10)` after
frequency integration. For `n=m`, squarefreeness gives `c_P(n,n)=k_n`, `mu(n)^2=1`, and
`K_W(n,n)=2W`, proving `(11)`. Counting the `p=q` pairs gives `(12)`. Adding `(10)` and `(12)`
leaves coefficient one and proves `(13)`.

## 4. Coprime firewall and corrected budget

If `gcd(n,m)=1`, then `c_P(n,m)=0`. Hence every coprime pair in `(10)` survives with its complete
Möbius sign and coefficient one:

\[
 \boxed{
 \gcd(n,m)=1
 \quad\Longrightarrow\quad
 1-{c_P(n,m)\over k_nk_m}=1.}
\tag{14}
\]

This has four consequences.

1. Prime separation alone cannot bound `(10)`: distinct prime blocks can have identical integer
   frequency through `p(n/p)=q(n/q)`.
2. Enlarging `P` cannot attenuate coprime integer pairs. It only changes terms supported on a
   shared designated prime.
3. The same-integer collision in `(11)` is positive and obeys only

   \[
   0\le2W\sum_n(1-1/k_n)\le2WM.
   \tag{15}
   \]

   Therefore the sufficient target for the prime off-diagonal is affine,
   `O_P(M,W) <= C W M + o(M^2)`, with available diagonal constant tracked. The stronger slogan
   `O_P(M,W)=o(M^2)` uniformly up to `W=M` is not the correct isolated target.
4. The square-multiple branch cannot cancel this term: it is identically zero by `(5)`.

The positive survivor is the exact coprime covariance

\[
 \mathcal C_{P,M}(W)=
 \sum_{\substack{n\ne m\in\mathcal N_P(M)\\(n,m)=1}}
 \mu(n)\mu(m)K_W(n,m).
\tag{16}
\]

Any incidence proof acting only through common designated primes is termwise blind to `(16)`.
Global cancellation with noncoprime terms is not excluded, but it must use Möbius signs or a
nonlocal frequency average, not local prime incidence.

There is also a constant-level formalization warning. The displayed current Lean capstone has
`W M` coefficient

\[
 10(1+\delta)+24(1+1/\delta),
\tag{17}
\]

even before `(10)` is bounded. Its minimum is

\[
 34+2\sqrt{240}>50.
\tag{18}
\]

Thus that fixed-constant theorem alone does not imply the existing `alpha <= 50 M` interface.
This is not a mathematical obstruction: the rough support density can be made arbitrarily small by
increasing the designated harmonic mass, while `(5)` removes the square-multiple term. The needed
infrastructure is a parameterized rough/error budget before choosing the weighted-triangle
parameter, not the current fixed `12 W M` specialization.

## 5. Coprime pairs form a ternary prime cube

Let `Q` be a finite prime set and `R_Q=prod_{p in Q} p`. Sum over all ordered coprime squarefree
`Q`-smooth pairs:

\[
 \mathcal T_Q(t)=
 \sum_{\substack{a,b:\ (a,b)=1\\p\mid ab\Rightarrow p\in Q}}
 \mu(a)\mu(b)(a/b)^{it}.
\tag{19}
\]

Each prime has exactly three states: absent, assigned to `a`, or assigned to `b`.

### Theorem C — ternary antiscale factorization and saturation

\[
 \boxed{
 \mathcal T_Q(t)=
 \prod_{p\in Q}(1-p^{it}-p^{-it})
 =\prod_{p\in Q}(1-2\cos(t\log p)).}
\tag{20}
\]

For every real `theta`,

\[
 9-(1-2\cos\theta)^2
 =4(1+\cos\theta)(2-\cos\theta)\ge0.
\tag{21}
\]

Consequently

\[
 |\mathcal T_Q(t)|\le3^{|Q|},
\tag{22}
\]

and equality holds exactly when

\[
 e^{it\log p}=-1\qquad(p\in Q).
\tag{23}
\]

Because distinct prime logarithms are rationally independent, Kronecker recurrence gives, for
every `T`,

\[
 \sup_{t>T}|\mathcal T_Q(t)|=3^{|Q|}.
\tag{24}
\]

Thus antiscale coherence is the exact escape mode of the alternating coprime cube: near `(23)`,
the Möbius sign attached to every occupied prime is canceled by its phase, and all `3^{|Q|}` states
align.

#### Proof

Multiplying the three local choices gives `(20)`. Equation `(21)` is expansion. It shows each
factor has modulus at most three and reaches three exactly at `cos(theta)=-1`, proving
`(22)`--`(23)`. Unique factorization proves rational independence of the prime logarithms.
Kronecker recurrence approximates the all-`pi` torus point at arbitrarily large times; continuity
then proves `(24)`.

This kills any pointwise ternary-cube damping conjecture. It does not kill a mean-square route.

## 6. Finite-height large-values rarity

Write `r=|Q|`, `N=3^r`, and `R=R_Q`. The `N` frequencies in `(19)` are

\[
 \lambda_{A,B}=\log(p_A/p_B),
 \qquad A\cap B=\varnothing.
\tag{25}
\]

They are distinct. For two distinct states, their frequency difference is `log(u/v)` with unequal
positive integers `u,v <= R^2`; hence

\[
 |\lambda-\lambda'|\ge R^{-2}.
\tag{26}
\]

### Theorem D — explicit finite-height ternary mean square

For every `W>0`,

\[
 \boxed{
 \int_{-W}^{W}|\mathcal T_Q(t)|^2dt
 \le
 \left(2W+4R^2(1+r\log3)\right)3^r.}
\tag{27}
\]

Therefore, for `0<lambda<=1`,

\[
 \boxed{
 {1\over2W}\left|\left\{t\in[-W,W]:
 |\mathcal T_Q(t)|\ge\lambda3^r\right\}\right|
 \le
 {1+2R^2(1+r\log3)/W\over\lambda^2 3^r}.}
\tag{28}
\]

In particular, if

\[
 R^2(1+r)=O(W),
\tag{29}
\]

then antiscale peaks have relative measure `O_lambda(3^{-r})`, although they recur cofinally.

#### Proof

Order the frequencies in `(25)`. Separation `(26)` implies that the `j`-th frequency on either
side of a fixed frequency is at distance at least `j/R^2`. Hence every reciprocal-distance row is
at most

\[
 2R^2\sum_{j=1}^{N}{1\over j}
 \le2R^2(1+\log N)=2R^2(1+r\log3).
\tag{30}
\]

The diagonal terms in the expansion of the integral contribute `2WN`. For unequal frequencies,

\[
 \left|\int_{-W}^{W}e^{it(\lambda-\lambda')}dt\right|
 \le {2\over|\lambda-\lambda'|}.
\tag{31}
\]

All coefficients have modulus one. Summing `(31)` by rows and using `(30)` gives the second term
in `(27)`. Chebyshev applied to `(27)` proves `(28)`.

The proof retains the alternating coefficients. Taking absolute values occurs only after the exact
character expansion and costs the explicit reciprocal-spacing term in `(27)`.

## 7. Conjecture loop and frontier movement

The volume weights of a prime-dilation marker are reciprocal, not uniform. This yields a sharper
source-level statement before the conjecture audit.

### Theorem E — reciprocal ternary critical dissipation saturation

On each `p in Q`, put a probability law on the three states `0,L,R` with weights

\[
 1,\quad {1\over p},\quad {1\over p},
\qquad
 Z_p=1+{2\over p}.
\tag{30a}
\]

Let `N` count occupied marker states and let `E_L-E_R` be the oriented log-prime energy. Its
alternating characteristic is

\[
 \Phi_Q(t)=
 \mathbb E\left[(-1)^N e^{it(E_L-E_R)}\right]
 =\prod_{p\in Q}
 {1-p^{-1}e^{it\log p}-p^{-1}e^{-it\log p}\over1+2/p}.
\tag{30b}
\]

Then

\[
 |\Phi_Q(t)|\le1,
 \qquad
 \sup_{t>T}|\Phi_Q(t)|=1                              \tag{30c}
\]

for every `T`: exact antiscale recurrence remains the unique local saturation mode. Nevertheless,
putting

\[
 V_Q=\prod_{p\in Q}{1+2/p^2\over(1+2/p)^2},            \tag{30d}
\]

one has the finite-height estimate

\[
 \boxed{
 \int_{-W}^{W}|\Phi_Q(t)|^2dt
 \le\left(2W+4R_Q^2(1+|Q|\log3)\right)V_Q.}            \tag{30e}
\]

Consequently

\[
 {1\over2W}|\{t\in[-W,W]:|\Phi_Q(t)|\ge\lambda\}|
 \le {1+2R_Q^2(1+|Q|\log3)/W\over\lambda^2}V_Q.        \tag{30f}
\]

The dissipation factor obeys

\[
 V_Q
 \le\exp\left(2\sum_{p\in Q}{1\over p^2}
                  -2\sum_{p\in Q}{1\over p}\right).   \tag{30g}
\]

Thus `V_Q -> 0` along any growing packet with divergent reciprocal-prime mass, even though exact
escape recurs cofinally. Under `R_Q^2(1+|Q|)=O(W)`, the relative measure of every fixed
`lambda`-large recurrence set tends to zero.

#### Proof

Independence gives `(30b)`. The local factor is

\[
 {1-(2/p)\cos(t\log p)\over1+2/p},
\]

whose absolute value is at most one and reaches one at the antiscale phase. Kronecker recurrence
proves `(30c)`. In the character expansion, the squared coefficient mass at `p` is
`(1+2/p^2)/(1+2/p)^2`; multiplication gives `V_Q`. The proof of Theorem D applies unchanged because
the Gram row bound depends only on frequencies, while the quadratic coefficient mass becomes
`V_Q`. This proves `(30e)` and Chebyshev gives `(30f)`.

For `0 <= u <= 1/2`, `log(1+2u)>=u`, while `log(1+2u^2)<=2u^2`. Apply these at `u=1/p` and sum to
obtain `(30g)`.

Equation `(30e)` is the exact reconciliation missing from static recurrence no-gos: pointwise
coercivity fails, but recurrence-weighted mean-square dissipation saturates critically. It retains
the alternating finite-volume signs and the reciprocal prime-dilation weights.

The following attacks were made in order.

1. **Conjecture:** prime sparsity makes the Ramaré `p != q` term small.  
   **Failed:** `(10)`--`(14)`; product collisions have zero frequency separation and coprime pairs
   survive with coefficient one.
2. **Conjecture:** the square-multiple polynomial cancels prime collisions.  
   **Failed maximally:** the polynomial is identically zero by `(5)`.
3. **Conjecture:** increasing designated harmonic mass damps every integer pair.  
   **Failed:** common-prime incidence never touches coprime pairs, `(14)`.
4. **Conjecture:** the coprime ternary cube is uniformly pointwise dissipative.  
   **Failed sharply:** `(24)`; antiscale recurrence reaches the exact `3^r` supremum cofinally.
5. **Conjecture:** recurrence peaks are sparse in frequency measure.  
   **Proved with a finite-height rate:** `(27)`--`(29)`.
6. **Conjecture:** reciprocal prime-dilation weights destroy the finite-height saving.  
   **Refuted:** Theorem E; they improve it to the exact vanishing factor `V_Q` while preserving
   cofinal modulus-one antiscale recurrences.

The surviving route is not another generic large-values theorem. It is the following literal
source problem.

### `TERNARY-MARKER-COFACTOR-FLATNESS-AND-RECURRENCE-SEAM`

Choose a growing marker packet `Q=Q(W)` with

\[
 (\prod_{p\in Q}p)^2(1+|Q|)=O(W),
 \qquad |Q|\longrightarrow\infty.
\tag{32}
\]

Decompose each coprime pair in `(16)` into its three-state `Q`-marker assignment and its
`Q`-rough cofactors. Prove, with the actual sharp cutoffs and Ramaré/physical weights, that the
cofactor block is flat enough across the `3^{|Q|}` marker states for `(27)` to survive tensoring.
The required output is an affine covariance bound

\[
 \mathcal C_{P,M}(W)\le CWM+o(M^2)
\tag{33}
\]

uniformly in the moving Gallagher range, together with the same marker allocation's column load
and normalized prime-dilation recurrence seam in the physical Route E relation.

This target retains precisely what previous reductions discarded:

- alternating finite-volume Möbius signs through `(19)`;
- cofinal antiscale recurrence through `(24)`;
- quantitative recurrence weight through `(28)`;
- prime-dilation states through the ternary marker assignment;
- rough cofactors and column balance as the remaining nonfactorized object.

Existing Turán rough-count and Ramaré energy theorems control total support and diagonal energy,
but they do not prove statewise cofactor flatness. Theorem F below shows that this proposed burden
was too strong: after exact physical centering, the incidence-complement component has favorable
sign. The hard theorem is now the source-faithful centering and moving seam for the remaining
scalar mode, not uniform control of every state block.

### Theorem F — incidence complement is conditionally negative

The exact recombination permits a stronger conclusion than coefficient bounds. Let `S` be any
finite history set, let each `n in S` carry a nonempty incidence set `F_n subset P`, and put

\[
 C(n,m)=1-\frac{|F_n\cap F_m|}{|F_n||F_m|},
 \qquad
 L_p(z)=\sum_{\substack{n\in S\\p\in F_n}}\frac{z_n}{|F_n|}.
\]

Then for arbitrary complex coefficients `z_n`,

\[
 \boxed{
 \sum_{n,m\in S} C(n,m)\operatorname{Re}(z_n\overline{z_m})
 =\left|\sum_{n\in S}z_n\right|^2-\sum_{p\in P}|L_p(z)|^2.}
 \tag{34}
\]

In particular, on the centered hyperplane `sum_n z_n=0`,

\[
 \boxed{
 \sum_{n,m} C(n,m)\operatorname{Re}(z_n\overline{z_m})
 =-\sum_{p\in P}|L_p(z)|^2\le0.}
 \tag{35}
\]

Equality in `(35)` holds exactly when every normalized prime load `L_p(z)` vanishes.

#### Proof

Write `v_n(p)=1_{p in F_n}/|F_n|`. Then

\[
 C(n,m)=1-\sum_{p\in P}v_n(p)v_m(p).
\]

Expanding the constant kernel gives `|sum_n z_n|^2`; exchanging the three finite sums in the
second term gives `sum_p |sum_n v_n(p)z_n|^2`. This proves `(34)`. Centering proves `(35)`, and a
finite sum of nonnegative norm squares is zero exactly when every square is zero.

For the actual Ramaré active integers, take `F_n=P(n)`. The centered shared-incidence complement
is therefore not an uncontrolled positive covariance: it is exact negative prime-load energy.
This does not yet center the source-faithful moving cofactor reporter or transport it through the
physical recurrence seam, but it removes any need to estimate the centered incidence kernel from
above after that identification is made.

### Theorem G — Gibbs likelihood oscillation controls the only positive mode

Let `Omega` be a nonempty finite history cell, let `F_x subset P` be nonempty, let `w_x>0`, and
let `|f_x|<=1`. Assume the pairwise likelihood-ratio oscillation

\[
 \left|\log\frac{w_x}{w_y}\right|\le\eta.
\]

Put `a_x=w_x f_x/sum_y w_y` and let `u=|Omega|^{-1}sum_x f_x`. Then

\[
 \boxed{
 \sum_{x,y}C(x,y)\operatorname{Re}(a_x\overline{a_y})
 \le\left(|u|+2\tanh(\eta/4)\right)^2.}
 \tag{36}
\]

Indeed Theorem F bounds the left side by `|sum_x a_x|^2`, and the sharp physical-versus-uniform
comparison gives

\[
 \left|\sum_xa_x-u\right|\le2\tanh(\eta/4).
\]

For arbitrary-order product histories `h_x:R -> [X-H,X+H]` with equal products, the exact product
curvature theorem gives

\[
 \eta=\frac{|R|H^2}{X(X-H)}.
 \tag{37}
\]

Thus `(36)` holds at every history order with no centered covariance error term. The remaining
quantity is the uniform history mean `u`, already explicit for binary histogram cells. This is the
direct connector between Gibbs likelihood-ratio oscillation, all-order product histories, and the
Ramaré incidence complement.

## 8. Lean closure and honest status

The exact finite ternary marker core is formalized in
`GaloisForLFunctions.RHTower.Sieve.RouteERamareTernaryAntiscale` and imported by the RHTower
umbrella.  Lean proves:

- injectivity of ternary prime-log frequencies and the explicit `R_Q^(-2)` separation;
- exact reporter/history factorization and coefficient energy `3^|Q|`;
- the unweighted mean-square bound `(27)`;
- local norm at most three, equality exactly at antiscale, and cofinally late near-saturation;
- exact reciprocal Gibbs history expansion and energy `V_Q`;
- the weighted mean-square bound `(30e)` and exponential estimate `(30g)`;
- local norm at most one, equality exactly at antiscale, and cofinally late near-saturation;
- unconditional `V_Q -> 0` along canonical prime packets;
- squarefreeness and coprimality of the two history products, and equality of each history
  coefficient with the product of their actual Möbius values.

`GaloisForLFunctions.RHTower.Sieve.RouteERamareTernaryAntiscaleCapstone` closes the exact paper
surface omitted by the component modules. It proves the literal squarefree active-set identity
`(4)`, equations `(10)`--`(15)` with the integer shared-incidence diagonal identified with the
original prime-block diagonal, real-cosine products `(20)` and `(30b)`, `IsLUB` forms of `(24)` and
`(30c)` on every late-time tail, and the explicit restricted-volume and literal-set versions of
`(28)` and `(30f)`.

`RamareSquareMultiple.lean` separately proves the square-multiple coefficient is zero and the exact
rough/nonrough Möbius decomposition from Theorem A.
`GaloisForLFunctions.RHTower.Sieve.RouteERamareIntegerIncidence` now formalizes Theorem B: every
Ramaré prime block is re-expanded on ordinary active integers, ordered `p != q` block pairs are
counted exactly, and the finite-volume integral becomes

```text
sum_(n,m) mu(n) mu(m)
  * (1 - |P(n) inter P(m)|/(|P(n)| |P(m)|))
  * ramareMellinPairKernel(W,n,m).
```

Lean also proves this complement is the normalized count of distinct ordered prime incidences and
lies in `[0,1]` on active integer pairs. The capstone turns the mean-square inputs into the exact
measurable large-value corollaries `(28)` and `(30f)`.
`RouteERamareIncidenceConditionalNegative` formalizes Theorem F, while
`RouteERamareGibbsMeanLeakage` formalizes Theorem G and its all-order equal-product-history
specialization. Both are umbrella imported.

Targeted module build and direct Lean check pass.  Kernel axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; no route premise, `sorry`, `admit`, new `axiom`, `opaque`,
`unsafe`, or numerical computation occurs.

Theorems A--G are unconditional finite mathematics. They create new knowledge by changing the
identity of the open object:

- `ramarePrimeOffDiagonal` is not a sparse prime-pair sum after recombination;
- square-multiple error is absent for Möbius;
- exact untouched core is coprime Möbius covariance;
- its finite prime model has antiscale recurrence as exact pointwise escape but exponentially rare
  unweighted large values at finite height under `(29)`;
- its reciprocal-weighted Gibbs model has cofinal exact escape but vanishing finite-height
  recurrence mass `V_Q`.

Equation `(33)` and source-faithful moving cofactor centering/seam transport remain unproved.
Uniform tensorized cofactor flatness is not the correct remaining burden: Theorem F makes the
centered incidence-complement component automatically nonpositive. The unresolved positive term
is the noncentered scalar mode together with its sharp-cutoff and physical recurrence seams.
Route E and RH remain open.
