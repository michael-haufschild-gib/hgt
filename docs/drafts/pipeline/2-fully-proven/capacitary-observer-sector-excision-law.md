# Capacitary observer-sector excision law

- **ID:** `capacitary-observer-sector-excision-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `first-entrance-gate-capacity-discrepancy-law.md`, `first-entrance-gate-renewal-prefix-law.md`
- **Statement:** Circuit complexity is logarithmic loss of a capacity-normalized gate-accessibility likelihood; every subexponential observer sector sees only target-capacity mass, while estimating the global likelihood requires growing replica order.

## Goal

Remove a false obstruction from the static-local Brown problem.  Constant-local Hamiltonian
ensembles can remain efficiently distinguishable from Haar at every time, whereas Brown--Susskind
complexity is expected to become maximal.  The theorem below proves that these statements are not
in tension: every gate-invariant observer sector with subexponential resolvent kernel is invisible
at the exponentially small capacity scale relevant to the complete circuit union.  Only the
complementary high-mode Bellman remainder can obstruct growth.

## Gates

- [x] 0 -> 1 in-progress: exact survivor isolated after global-Haar and global-resolvent no-gos
- [x] 1 -> 2 fully-proven: dependency-closed proof below
- [ ] 2 -> 3 formalized: deferred while the shared Lean corpus is being refactored
- [ ] 3 -> 4 publication-ready: not a standalone paper; intended as a load-bearing reduction

## 1. Setting

Let `(X,pi)` be a probability space and let `P` be a self-adjoint Markov transition operator on
`L^2(pi)` which preserves bounded real functions.  Fix `0<a<1` and put

\[
 L_a:=I-aP.
\]

Let `A` be a measurable target of positive `pi`-measure.  Let

\[
 h_A(x)=\mathbb E_x\bigl[a^{\tau_A}\mathbf 1_{\{\tau_A<\infty\}}\bigr]
\]

be its discounted first-entrance potential.  Thus `0<=h_A<=1`, `h_A=1` on `A`, and

\[
 q_A:=L_ah_A
\]

is nonnegative and supported on `A`.  Define

\[
 \operatorname{cap}_a(A):=\langle h_A,L_ah_A\rangle_\pi.
\]

Because `h_A=1` on the support of `q_A`, self-adjointness gives

\[
 \operatorname{cap}_a(A)
 =\langle 1,q_A\rangle_\pi,
 \qquad
 \langle 1,h_A\rangle_\pi
 ={\operatorname{cap}_a(A)\over1-a}.
 \tag{1}
\]

Moreover, `1-a<=q_A<=1` on `A`, so

\[
 (1-a)\pi(A)\le\operatorname{cap}_a(A)\le\pi(A).
 \tag{1a}
\]

Consequently

\[
 d\rho_A:={q_A\over\operatorname{cap}_a(A)}\,d\pi
 \tag{2}
\]

is a probability measure supported on `A`.  It is the normalized equilibrium charge.

Let `E` be a finite-dimensional `P`-invariant real subspace of bounded functions containing the
constant function.  Self-adjointness supplies an orthonormal eigenbasis

\[
 \phi_0=1,\qquad P\phi_j=\lambda_j\phi_j,
 \qquad j=0,\ldots,K-1,
 \tag{3}
\]

where `lambda_0=1`.  Let `Pi_E` be the orthogonal projection onto `E`, and define the centered
discounted reproducing kernel

\[
 R_{E,a}(x,y)
 :=\sum_{j=1}^{K-1}
 {\phi_j(x)\phi_j(y)\over1-a\lambda_j},
 \qquad
 B_{E,a}:=\sup_{x,y}|R_{E,a}(x,y)|.
 \tag{4}
\]

## 2. Exact charge--mode transfer

### Theorem A (capacitary spectral projection)

For every `j`,

\[
 \boxed{
 \langle h_A,\phi_j\rangle_\pi
 ={\operatorname{cap}_a(A)\over1-a\lambda_j}
 \int\phi_j\,d\rho_A.}
 \tag{5}
\]

Hence, pointwise wherever the finite basis is defined,

\[
 \boxed{
 (\Pi_Eh_A)(x)
 ={\operatorname{cap}_a(A)\over1-a}
 +\operatorname{cap}_a(A)
   \int R_{E,a}(x,y)\,d\rho_A(y).}
 \tag{6}
\]

For every probability measure `nu` on `X`, including measures singular with respect to `pi`,

\[
 \boxed{
 \left|
  \int\Pi_Eh_A\,d\nu
  -{\operatorname{cap}_a(A)\over1-a}
 \right|
 \le \operatorname{cap}_a(A)B_{E,a}.}
 \tag{7}
\]

#### Proof

Since `L_a` is self-adjoint and `L_a phi_j=(1-a lambda_j)phi_j`,

\[
 (1-a\lambda_j)\langle h_A,\phi_j\rangle_\pi
 =\langle L_ah_A,\phi_j\rangle_\pi
 =\langle q_A,\phi_j\rangle_\pi.
\]

Equations (1)--(2) turn the last member into
`cap_a(A) int phi_j d rho_A`, proving (5).  Summing the finite orthogonal expansion and separating
`j=0` proves (6).  Integrating (6) against `nu`, then using that `nu` and `rho_A` are probability
measures, gives (7).  No density for `nu` is used.  QED.

### Corollary A.1 (basis bound)

\[
 \boxed{
 B_{E,a}
 \le\sum_{j=1}^{K-1}{\|\phi_j\|_\infty^2\over1-a\lambda_j}
 \le {1\over1-a}\sum_{j=1}^{K-1}\|\phi_j\|_\infty^2.}
 \tag{8}
\]

This follows directly from (4), because every eigenvalue of a self-adjoint Markov operator lies in
`[-1,1]`.

### Corollary A.2 (leverage bound)

Let

\[
 K_E^0(x,y):=\sum_{j=1}^{K-1}\phi_j(x)\phi_j(y),
 \qquad
 L_E:=\sup_x K_E^0(x,x).
 \tag{8a}
\]

Then

\[
 \boxed{B_{E,a}\le {L_E\over1-a}.}
 \tag{8b}
\]

If a compact group acts transitively on `X`, preserves `pi`, and leaves `E` invariant, then

\[
 \boxed{L_E=K-1,\qquad B_{E,a}\le {K-1\over1-a}.}
 \tag{8c}
\]

#### Proof

Finite-dimensional spectral calculus and the Neumann series give

\[
 R_{E,a}(x,y)
 =\sum_{m\ge0}a^m(P_x^mK_E^0)(x,y).
\]

The reproducing-kernel Cauchy--Schwarz inequality gives

\[
 |K_E^0(x,y)|^2\le K_E^0(x,x)K_E^0(y,y)\le L_E^2.
\]

Every Markov power is an `L^infty` contraction, so each summand has absolute value at most `L_E`.
Summing the geometric series proves (8b).  Under a transitive measure-preserving action,
`K_E^0(x,x)` is constant.  Its integral is the trace of the centered projection, namely `K-1`.
This proves (8c).  QED.

### Corollary A.3 (unconditional copy-sector bound)

Let `X=U(D)` with Haar measure.  Let `E_k` be constants together with the real and imaginary parts
of the matrix-coefficient space of the representation

\[
 U\longmapsto U^{\otimes k}\otimes\overline U^{\otimes k}.
 \tag{8d}
\]

For every gate walk that preserves this sector,

\[
 \boxed{
 \dim_{\mathbb R} E_k\le 2D^{4k}+1,
 \qquad
 B_{E_k,a}\le {2D^{4k}\over1-a}.}
 \tag{8e}
\]

Indeed the representation space has complex dimension `D^(2k)`, so its full complex
matrix-coefficient space has dimension at most `D^(4k)` and its realification has dimension at
most `2D^(4k)`.  Left translation preserves that space and acts transitively on
`U(D)`.  Apply (8c).  The same argument applies to projective-state copy sectors with the
corresponding smaller representation dimension.

## 3. Complete circuit union after observer excision

Let an inverse-closed gate alphabet `Gamma`, of cardinality `M>=2`, act isometrically on `X`, and
let `P` be the inverse-gate walk.  Fix a seed `chi` and let `A_epsilon` be its `epsilon`-tube.  For a
target `v`, let `C_epsilon(v)` be its robust word complexity from `chi`.

If `C_epsilon(v)<=s`, one word of length at most `s` drives the inverse walk from `v` into
`A_epsilon`.  Its discounted path mass is at least `(a/M)^s`.  Therefore

\[
 \mathbf 1_{\{C_\epsilon(v)\le s\}}
 \le (M/a)^s h_{A_\epsilon}(v).
 \tag{9}
\]

For an arbitrary endpoint law `nu`, define the high-mode Bellman remainder

\[
 \mathcal R_{E,a}(\nu,A)
 :=\int(I-\Pi_E)h_A\,d\nu,
 \qquad
 \mathcal R^+_{E,a}:=\max(\mathcal R_{E,a},0).
 \tag{10}
\]

### Theorem B (observer-excised complete union)

For every `s>=0`,

\[
 \boxed{
 \nu\{C_\epsilon\le s\}
 \le (M/a)^s
 \left[
  \operatorname{cap}_a(A_\epsilon)
  \left({1\over1-a}+B_{E,a}\right)
  +\mathcal R^+_{E,a}(\nu,A_\epsilon)
 \right].}
 \tag{11}
\]

#### Proof

Integrate (9).  Decompose `h_A=Pi_E h_A+(I-Pi_E)h_A`, apply the upper half of (7) to the first
term, and replace the second term by its positive part.  QED.

The crucial feature of (11) is what does **not** occur: no total-variation, chi-square,
negative-Sobolev, design, or Haar-mixing distance of `nu` appears.  The law `nu` may have order-one
distinguishing bias in every mode of `E`.  Its complete contribution is still multiplied by target
capacity.

### Theorem C (complexity--recurrence lives in the observer complement)

Put

\[
 r_{E,a,A}(x):=((I-\Pi_E)h_A)(x).
 \tag{11a}
\]

For every target `x` of finite robust word complexity `C_epsilon(x)`, prefix-free first entrance
gives

\[
 (a/M)^{C_\epsilon(x)}\le h_A(x)\le a^{C_\epsilon(x)}.
 \tag{11b}
\]

Consequently

\[
 \boxed{
 (a/M)^{C_\epsilon(x)}
 -\operatorname{cap}_a(A)\left({1\over1-a}+B_{E,a}\right)
 \le r_{E,a,A}(x)}
 \tag{11c}
\]

and

\[
 \boxed{
 r_{E,a,A}(x)
 \le a^{C_\epsilon(x)}
 -{\operatorname{cap}_a(A)\over1-a}
 +\operatorname{cap}_a(A)B_{E,a}.}
 \tag{11d}
\]

In particular, at every exact or robust return `x in A`,

\[
 \boxed{
 r_{E,a,A}(x)
 \ge1-\operatorname{cap}_a(A)
 \left({1\over1-a}+B_{E,a}\right),}
 \tag{11e}
\]

whereas whenever `C_epsilon(x)>=s`,

\[
 \boxed{
 r_{E,a,A}(x)
 \le a^s
 -{\operatorname{cap}_a(A)\over1-a}
 +\operatorname{cap}_a(A)B_{E,a}.}
 \tag{11f}
\]

#### Proof

Every successful inverse-gate path has length at least `C_epsilon(x)`, so its discounted mass is
at most `a^{C_epsilon(x)}`.  One shortest word occurs with probability `M^{-C_epsilon(x)}` and
contributes `(a/M)^{C_epsilon(x)}`.  This proves (11b).  The pointwise form of (6) implies

\[
 \left|(\Pi_Eh_A)(x)-{\operatorname{cap}_a(A)\over1-a}\right|
 \le\operatorname{cap}_a(A)B_{E,a}.
\]

Subtracting the two bounds proves (11c)--(11d).  A return has `h_A=1`; this gives (11e).  Finally
`a^{C_epsilon(x)}<=a^s` when `C_epsilon(x)>=s`, giving (11f).  QED.

Theorem C supplies an exact order parameter.  If `cap_a(A)B_{E,a}=o(1)`, recurrence forces the
observer-complement coordinate to one, while a growing complexity lower bound forces it toward
zero.  The low observer sector remains capacity-small in both regimes.  Thus neither recurrence
nor maximal preparation complexity is carried by any subexponential family of persistent locality
observables; both are encoded by its high-mode complement.

### Theorem D (capacity--replica uncertainty law)

Assume the homogeneous setting of Corollary A.2, so `dim E=K`.  Then

\[
 \boxed{
 \|\Pi_Eh_A\|_{L^2(\pi)}^2
 \le {\operatorname{cap}_a(A)^2K\over(1-a)^2}.}
 \tag{11g}
\]

Since `h_A=1` on `A` and `cap_a(A)<=pi(A)`,

\[
 \|h_A\|_{L^2(\pi)}^2\ge\pi(A)\ge\operatorname{cap}_a(A).
 \tag{11h}
\]

Therefore

\[
 \boxed{
 {\|\Pi_Eh_A\|_2^2\over\|h_A\|_2^2}
 \le {\operatorname{cap}_a(A)K\over(1-a)^2},}
 \tag{11i}
\]

and, because orthogonal projection is the best `L^2` approximation from `E`, every `f in E`
satisfies

\[
 \boxed{
 {\|h_A-f\|_2^2\over\|h_A\|_2^2}
 \ge1-{\operatorname{cap}_a(A)K\over(1-a)^2}.}
 \tag{11j}
\]

#### Proof

Write

\[
 \mu_j:=\int\phi_j\,d\rho_A.
\]

Theorem A and Parseval give

\[
 \|\Pi_Eh_A\|_2^2
 =\operatorname{cap}_a(A)^2
 \sum_{j=0}^{K-1}{|\mu_j|^2\over(1-a\lambda_j)^2}
 \le {\operatorname{cap}_a(A)^2\over(1-a)^2}
 \sum_{j=0}^{K-1}|\mu_j|^2.
\]

Let `K_E(x,y)=sum_j phi_j(x)phi_j(y)` be the full projection kernel.  Transitivity makes
`K_E(x,x)=K`; reproducing-kernel Cauchy--Schwarz gives `|K_E(x,y)|<=K`.  Hence

\[
 \sum_j|\mu_j|^2
 =\iint K_E(x,y)\,d\rho_A(x)d\rho_A(y)
 \le K,
\]

which proves (11g).  Equation (11h) is immediate.  Dividing proves (11i), and Pythagoras gives

\[
 \inf_{f\in E}\|h_A-f\|_2^2
 =\|h_A-\Pi_Eh_A\|_2^2
 =\|h_A\|_2^2-\|\Pi_Eh_A\|_2^2.
\]

This proves (11j).  QED.

### Corollary D.1 (replica order forced by rare preparation)

If a `K`-dimensional homogeneous observer sector captures a fraction `gamma>0` of the
first-entrance reporter's squared `L^2` mass, then

\[
 \boxed{K\ge{\gamma(1-a)^2\over\operatorname{cap}_a(A)}.}
 \tag{11k}
\]

For the projective pure-state space in dimension `D`, let `A_epsilon` be the trace-distance
`epsilon`-ball about the seed.  Haar measure gives

\[
 \pi(A_\epsilon)=\epsilon^{2(D-1)},
 \qquad
 \operatorname{cap}_a(A_\epsilon)\le\epsilon^{2(D-1)}.
 \tag{11l}
\]

The real `k`-copy polynomial sector has dimension at most `2D^{2k}+1`.  Consequently capture of a
fixed fraction `gamma` forces

\[
 \boxed{
 k\ge {1\over2\log D}
 \log\!\left(
 {\gamma(1-a)^2\epsilon^{-2(D-1)}-1\over2}
 \right),}
 \tag{11m}
\]

whenever the logarithm's argument exceeds one.  At fixed `a`, `epsilon`, and `gamma`, this is

\[
 \boxed{k=\Omega(D/\log D).}
 \tag{11n}
\]

Thus growing replica order is not an artifact of the circuit union or a weak proof technique.
It is forced already by the information geometry of the exact first-entrance reporter: every
`poly(log D)`-copy sector captures an exponentially vanishing fraction of its mass.  This does not
say that a return itself needs many copies to detect--a seed projector detects a return directly.
It says that no bounded-copy polynomial observer can represent the global preparation-accessibility
function which distinguishes a return from the full shortcut landscape.

### Corollary D.2 (operational copy lower bound)

Consider any experiment receiving `k` identical copies of an unknown pure state `x`, allowing
arbitrary joint measurements, adaptivity, ancillas, and classical postprocessing, and returning a
real random variable `Y` with finite second moment.  Its conditional mean has the form

\[
 f(x):=\mathbb E[Y\mid x]
 =\operatorname{tr}(B\rho_x^{\otimes k})
 \tag{11o}
\]

for one Hermitian operator `B`; hence `f` lies in the real `k`-copy polynomial sector.  Jensen's
inequality and Theorem D give

\[
 \boxed{
 {\mathbb E_{x\sim\pi}\mathbb E[(Y-h_A(x))^2\mid x]
  \over\|h_A\|_2^2}
 \ge1-{\operatorname{cap}_a(A)(2D^{2k}+1)\over(1-a)^2}.}
 \tag{11p}
\]

Therefore reducing the normalized Haar-average mean-square error below `1-gamma` requires the
replica lower bound (11m).  For `D=2^n` and fixed resolution this is

\[
 \boxed{k=\Omega(2^n/n).}
 \tag{11q}
\]

#### Proof

Every adaptive `k`-copy protocol is equivalent, by deferred measurement, to one POVM on
`rho_x^(tensor k)`.  Weighting its outcomes by the reported real values produces the Hermitian
first-moment operator `B` in (11o).  Conditional Jensen gives

\[
 \mathbb E[(Y-h_A(x))^2\mid x]\ge(f(x)-h_A(x))^2.
\]

Integrate over Haar and apply (11j) with the copy-sector dimension bound.  QED.

### Theorem E (capacity-normalized accessibility law)

Define the dimensionless accessibility amplification

\[
 \mathfrak A_{A,a}(x)
 :={(1-a)h_A(x)\over\operatorname{cap}_a(A)}.
 \tag{11r}
\]

Then

\[
 \boxed{
 \mathfrak A_{A,a}\ge0,
 \qquad
 \int\mathfrak A_{A,a}\,d\pi=1,
 \qquad
 x\in A\Longrightarrow
 \mathfrak A_{A,a}(x)={1-a\over\operatorname{cap}_a(A)}.}
 \tag{11s}
\]

Its observer-sector projection is

\[
 \boxed{
 (\Pi_E\mathfrak A_{A,a})(x)
 =1+(1-a)\int R_{E,a}(x,y)\,d\rho_A(y),}
 \tag{11t}
\]

so every homogeneous `K`-dimensional sector obeys

\[
 \boxed{|\Pi_E\mathfrak A_{A,a}-1|\le K-1.}
 \tag{11u}
\]

For every target of finite robust word complexity,

\[
 \boxed{
 {\log((1-a)/(\operatorname{cap}_a(A)\mathfrak A_{A,a}(x)))
  \over\log(M/a)}
 \le C_\epsilon(x)
 \le
 {\log((1-a)/(\operatorname{cap}_a(A)\mathfrak A_{A,a}(x)))
  \over\log(1/a)}.}
 \tag{11v}
\]

Finally, for every `z>0`,

\[
 \boxed{
 \pi\{x:\mathfrak A_{A,a}(x)\ge z\}\le z^{-1}.}
 \tag{11w}
\]

#### Proof

Equation (11s) is (1) and the boundary value `h_A=1` on `A`, after normalization.  Equation (11t)
is (6); (8c) gives (11u).  Since

\[
 {\operatorname{cap}_a(A)\mathfrak A_{A,a}(x)\over1-a}=h_A(x),
\]

the first-entrance sandwich `(a/M)^C<=h_A<=a^C`, followed by negative logarithms, proves (11v).
Markov's inequality and the unit mean in (11s) prove (11w).  QED.

The exact cycle is now visible without invoking Haar convergence:

\[
 \boxed{
 \begin{array}{c}
 \text{return}\;:\;\mathfrak A=(1-a)/\operatorname{cap}
 \\
 \downarrow\quad\text{logarithmic accessibility loss}\quad\downarrow
 \\
 \text{complexity plateau}\;:\;\mathfrak A\text{ exponentially below its return value}
 \\
 \downarrow\quad\text{recurrence reamplification}\quad\downarrow
 \\
 \text{return}
 \end{array}}
 \tag{11x}
\]

Equation (11x) is a representation law, not a physical-time theorem: it identifies a canonical
dimensionless order parameter whose Brown-rate evolution remains to be proved.  Its value separates
preparation accessibility from permanent low-mode locality, while (11v) converts its logarithmic
loss exactly into circuit-complexity bounds.  Unit Haar mean does not imply pointwise concentration
near one; no such concentration claim is made.

### Theorem F (accessibility likelihood and low-degree invisibility)

Define the accessibility-biased probability measure

\[
 d\sigma_{A,a}:=\mathfrak A_{A,a}\,d\pi.
 \tag{11y}
\]

Then `mathfrak A_(A,a)=d sigma_(A,a)/d pi`, and the return tube carries

\[
 \boxed{
 \sigma_{A,a}(A)
 ={(1-a)\pi(A)\over\operatorname{cap}_a(A)}
 \in[1-a,1].}
 \tag{11z}
\]

Writing `q=pi(A)`, data processing to the partition `{A,A^c}` gives

\[
 \boxed{
 D_{\mathrm{KL}}(\sigma_{A,a}\Vert\pi)
 \ge (1-a)\log(1/q)-\log2.}
 \tag{11aa}
\]

The chi-square divergence satisfies

\[
 \boxed{
 \chi^2(\sigma_{A,a}\Vert\pi)
 =\|\mathfrak A_{A,a}\|_2^2-1
 \ge{(1-a)^2\over\operatorname{cap}_a(A)}-1
 \ge{(1-a)^2\over\pi(A)}-1.}
 \tag{11ab}
\]

Nevertheless, every homogeneous `K`-dimensional observer sector obeys

\[
 \boxed{
 {\|\Pi_E\mathfrak A_{A,a}\|_2^2
  \over\|\mathfrak A_{A,a}\|_2^2}
 \le{\operatorname{cap}_a(A)K\over(1-a)^2}.}
 \tag{11ac}
\]

Finally, the pointwise complexity law (11v) is the exact log-likelihood formula

\[
 \boxed{
 {-\log h_A(x)}
 =\log{1-a\over\operatorname{cap}_a(A)}
  -\log{d\sigma_{A,a}\over d\pi}(x),}
 \tag{11ad}
\]

inserted between the two fixed gate-alphabet conversion factors in (11v).

#### Proof

Theorem E proves that (11y) has total mass one.  Because `h_A=1` on `A`, its mass there is the
displayed ratio in (11z); the capacity window (1a) gives the interval.  Relative entropy decreases
under the two-cell partition, so with `p=sigma_(A,a)(A)`,

\[
 D_{\mathrm{KL}}(\sigma_{A,a}\Vert\pi)
 \ge p\log{p\over q}+(1-p)\log{1-p\over1-q}.
\]

The right side equals

\[
 p\log(1/q)+(1-p)\log(1/(1-q))-H_2(p)
 \ge(1-a)\log(1/q)-\log2,
\]

proving (11aa).  Normalization gives the first equality in (11ab).  From (11h),

\[
 \|\mathfrak A_{A,a}\|_2^2
 ={(1-a)^2\over\operatorname{cap}_a(A)^2}\|h_A\|_2^2
 \ge{(1-a)^2\over\operatorname{cap}_a(A)}.
\]

Use `cap_a(A)<=pi(A)` for the last inequality.  Equation (11ac) is (11i) after multiplying numerator
and denominator by the same normalization factor.  Equation (11ad) is the definition (11r).  QED.

Theorem F supplies the ontological reversal suggested by all prior no-gos:

> circuit complexity is not convergence to Haar randomness; it is pointwise surprisal relative to
> a gate-accessibility-biased law whose likelihood ratio is globally enormous but invisible to
> every subexponential observer sector.

Permanent locality witnesses and preparation complexity can therefore coexist because they occupy
different likelihood sectors.  Brown growth would be the physical-time loss of this accessibility
likelihood, the plateau its prolonged suppression, and recurrence its reamplification.  Only the
last time-dependent sentence remains conjectural; equations (11y)--(11ad) are unconditional.

### Theorem G (subexponential accessibility closes the circuit union)

Let `R_D` be any return/carrier-excision event and let `V_D` have an arbitrary endpoint law.  Then

\[
 \boxed{
 \Pr\{R_D,\ C_\epsilon(V_D)\le s_D\}
 \le (M/a)^{s_D}
 {\operatorname{cap}_a(A_D)\over1-a}
 \mathbb E\!left[
  \mathbf1_{R_D}\mathfrak A_{A_D,a}(V_D)
 \right].}
 \tag{11ae}
\]

Suppose, for fixed `alpha>0` and `beta>=0`,

\[
 \operatorname{cap}_a(A_D)\le\exp[-\alpha D+o(D)],
 \qquad
 s_D\le\beta D,
 \tag{11af}
\]

and

\[
 \boxed{
 \mathbb E\!\left[
  \mathbf1_{R_D}\mathfrak A_{A_D,a}(V_D)
 \right]\le\exp[o(D)].}
 \tag{11ag}
\]

If

\[
 \alpha>\beta\log(M/a),
 \tag{11ah}
\]

then

\[
 \boxed{
 \Pr\{R_D,\ C_\epsilon(V_D)\le s_D\}
 \le\exp[-(\alpha-\beta\log(M/a))D+o(D)].}
 \tag{11ai}
\]

#### Proof

Multiply the pointwise complete-union inequality (9) by `1_(R_D)`, average, and substitute
`h_A=cap_a(A) mathfrak A_(A,a)/(1-a)`.  This proves (11ae).  Taking logarithms and inserting
(11af)--(11ah) proves (11ai).  QED.

Theorem G corrects an overstrong frontier formulation.  Brown growth does not require the
high-mode Bellman remainder to decay exponentially to zero.  Capacity already supplies the
exponential factor that pays the complete circuit union.  After its entropy margin is fixed, the
only remaining demand is **no exponential accessibility amplification away from returns and named
shortcut carriers**.  Permanent low-mode non-Haar memory is compatible with (11ag) by Theorem A.

## 4. Brown-scale blindness of subexponential observers

Consider a sequence with Hilbert-space dimension `D->infinity`.  Suppose

\[
 \operatorname{cap}_a(A_D)\le\exp[-\alpha D+o(D)],
 \qquad
 B_{E_D,a}\le\exp[o(D)],
 \qquad
 s_D\le\beta D,
 \tag{12}
\]

for fixed `a`, `alpha>0`, and `beta>=0`.  If

\[
 \alpha>\beta\log(M/a),
 \tag{13}
\]

then the entire observer-sector term on the right of (11) is exponentially vanishing.  Thus only
`R^+_{E_D,a}` can prevent a Brown-depth lower bound.

In particular, the `k(D)`-copy unitary observer sector in Corollary A.3 has

\[
 B_{E_D,a}\le {2D^{4k(D)}\over1-a}.
 \tag{14}
\]

Whenever `k(D)=poly(log D)`,

\[
 \log B_{E_D,a}=poly(\log D)=o(D).
\]

Therefore every `poly(log D)`-copy locality test whose acceptance function lies in this standard
matrix-coefficient sector lies below the Brown exponent.  Such a test can distinguish the endpoint
law from Haar with order-one advantage forever; equation (11) proves that this persistent low-mode
memory is not the source of a low-complexity shortcut.

## 5. Conjecture--failure--survivor loop

### C0. Permanent non-Haar locality obstructs maximal complexity

Verdict: `[FALSIFIED AS A MECHANISM]` by (7) and (11).

A bounded subexponential observer sector can retain arbitrary distinguishing bias while contributing
only capacity-scale first-entrance mass.

### C1. An `L^2` projection upper bound closes the complete circuit union

Verdict: `[FALSIFIED AT THE REQUIRED EXPONENT]`.

Cauchy--Schwarz bounds endpoint capture by a square root of target mass or capacity.  At Brown depth
that loses half the rare-target exponent and can fail after the circuit union.  The positive
equilibrium charge (2), followed by the `L^infty` resolvent-kernel bound (7), retains the full
capacity exponent.  Theorem D is a different use of `L^2`: it proves a lower bound on the observer
dimension needed to represent the reporter, not an upper bound on circuit capture.

### C2. Observer-sector suppression is dimension-free

Verdict: `[FALSIFIED]`.

For a target concentrated near a point where a reproducing kernel peaks, the sum in (4) can add
coherently.  A factor controlled by the observer kernel, and in worst cases by observer dimension,
is unavoidable.  The positive survivor is asymptotic: every `exp(o(D))` observer sector remains
negligible against `exp(-Theta(D))` target capacity.

### C3. Subexponential observer sectors are Brown-blind

Verdict: `[PAPER-PROVED]` by Theorems A--B and (12)--(14).

This proves the exact mathematical compatibility of permanent efficient non-Haar locality with a
future maximal-complexity theorem.  It does not assume that the endpoint ensemble approaches Haar.

### C4. Fixed-copy observers can represent global preparation accessibility

Verdict: `[FALSIFIED QUANTITATIVELY]` by Theorem D.

Capturing a fixed fraction of the discounted first-entrance reporter requires observer dimension
at least `Omega(1/cap_a(A))`.  For projective `epsilon`-balls this forces replica order
`Omega(D/log D)`.  The result concerns the global accessibility function, not direct one-copy
detection of a return.

### C5. Circuit complexity is logarithmic loss of capacity-normalized accessibility

Verdict: `[PAPER-PROVED AS AN EXACT REPRESENTATION]` by Theorems E--F.

The normalized first-entrance potential is the likelihood ratio of the accessibility-biased law
`sigma_(A,a)` to Haar.  It has Haar mean one, reciprocal-capacity amplification at returns, globally
exponential chi-square divergence, exponentially vanishing low-copy captured fraction, and
logarithmic loss bilipschitz-equivalent to robust word complexity.  This unifies growth, plateau,
and recurrence as regimes of one order parameter, but does not establish their physical-time
schedule.

### C6. The high-mode Bellman remainder has Brown-rate decay for ordinary static-local dynamics

Verdict: `[FROZEN PRIMARY CONJECTURE; OPEN]`.

For the Gaussian coefficient ensemble on the full nearest-neighbour two-local Pauli shell, fix
`a<1/M` and the product-state or Choi target used by the completed-phase theorem.  On the prescribed
geometric Brown skeleton, after the target-independent spectral-return excision and the named
capacity-compatible fast-forwardable-carrier excision already defined in the parent programme,

\[
 \boxed{
 \sup_{t\in\mathcal T_D}
 \mathbb E_H\!left[
  \mathbf1_{R_D(H,t)}\mathfrak A_{A_D,a}(V_{H,t})
 \right]=\exp[o(D)].}
 \tag{C6}
\]

At the first certified recurrence window, the same accessibility amplification returns to
`exp[Theta(D)]` on the recurrent coefficient set.  Statement (C6) is frozen as the truth-hunch; its
shape is not chosen around a visible proof route.

The remaining core is now strictly smaller:

\[
 \boxed{
 \mathbb E_H\!left[
  \mathbf1_{R_D(H,t)}\mathfrak A_{A_D,a}(V_{H,t})
 \right]\le\exp[o(D)]}
 \tag{15}
\]

on the geometric Brown skeleton, after the common return and fast-forwardable-carrier excision.
Unlike global Haar convergence, (15) only excludes exponential amplification of one
capacity-normalized first-entrance likelihood.  Theorem G proves that target capacity then pays the
entire complete circuit union.  Any future growing-replica or Bellman argument should be centered
against `Pi_E` before estimating this normalized quantity.

## 6. Hostile audit

1. **Classical core.**  Equilibrium charge, spectral calculus, and reproducing kernels are standard.
   Novelty is claimed only for the observer-excised complete-circuit reduction and its exact
   locality--complexity consequence.
2. **No Brown growth yet.**  Theorem B isolates but does not bound (15).  It removes the permanent
   locality sector from the open core; it does not solve the high-mode static reuse problem.
3. **Fixed fugacity.**  If `a` approaches one exponentially fast, `(1-a)^-1` may erase the gain.
   Brown tropicalization uses fixed `a`, for which this issue is absent.
4. **Observer sector must be identified.**  Corollary A.2 makes dimension sufficient for
   homogeneous invariant sectors, and Corollary A.3 covers the standard `k`-copy unitary
   matrix-coefficient space.  An arbitrary efficient experiment must still be represented in a
   named invariant sector before the bound applies.
5. **Invariant closure matters.**  A test function not lying in a finite `P`-invariant sector must
   be replaced by its gate-Krylov closure.  If that closure has exponential-in-`D` kernel, this
   theorem gives no suppression.
6. **Rare target required.**  The result preserves, but cannot create, an exponential capacity
   exponent.
7. **Singular endpoint laws are covered.**  The endpoint measure `nu` is never divided by Haar;
   only finite sums of bounded modes are integrated against it.
8. **Priority boundary.**  Potential theory already contains (1)--(7) in equivalent spectral
   language.  Targeted search found no prior composition with prefix-free circuit first entrance,
   complete shortcut unions, the capacity--replica uncertainty law, and permanent static-local
   non-Haar witnesses.  External priority is provisional pending specialist review.
9. **Not a return-detection lower bound.**  A seed projector detects a present return with one copy.
   Theorem D instead lower-bounds representation of the global first-entrance accessibility
   function.  Conflating these tasks would be a false physical claim.
10. **Low-degree is not automatically computational complexity.**  Theorem D is an unconditional
   approximation lower bound for named invariant copy sectors.  Turning it into a lower bound for
   arbitrary classical preprocessing or adaptive algorithms requires a separate representation
   theorem.  Corollary D.2 supplies that representation only for finite-copy quantum experiments.
11. **Accessibility law is not the physical endpoint law.**  `sigma_(A,a)` is a canonical tilt
   constructed from the gate first-entrance problem.  Its large KL or chi-square divergence does
   not assert that a static-Hamiltonian endpoint ensemble has that divergence, nor does it prove a
   black-hole interior statement.
12. **Lean boundary.**  No theorem from this card may enter a final manuscript until its exact
   finite-dimensional form is formalized and audited.  Lean work is intentionally deferred during
   the active corpus refactor.

## 7. External comparison

- Gaudilliere--Landim, *A Dirichlet principle for non reversible Markov chains and some recurrence
  theorems*, arXiv:1111.2445, represents the classical capacity/Poisson background.
- Kunisky--Wein--Bandeira, *Notes on Computational Hardness of Hypothesis Testing: Predictions
  using the Low-Degree Likelihood Ratio*, arXiv:1907.11636, studies low-degree projection as a
  predictor of statistical computational hardness.  It does not derive the exact
  `capacity x observer-dimension` law (11i), the first-entrance reporter, or the quantum-copy bound
  (11m).
- Cheng--Datta--Liu--Nuradha--Salzmann--Wilde, *An invitation to the sample complexity of quantum
  hypothesis testing*, arXiv:2403.17868, develops copy complexity for state discrimination.  It
  does not study estimation of global gate-preparation accessibility or the capacity-controlled
  mean-square lower bound (11p).
- Cui--Schuster--Mao--Huang--Brandao, *Random unitaries from Hamiltonian dynamics*,
  arXiv:2510.08434, proves that constant-local time-independent Hamiltonian ensembles remain
  efficiently distinguishable from Haar at every time.  It does not establish the capacity-scale
  observer excision (11) or a circuit-complexity plateau.
- Bohdanowicz--Brandao, *Universal Hamiltonians for Exponentially Long Simulation*,
  arXiv:1710.02625, obtains steady complexity growth for a specially engineered universal static
  Hamiltonian under computational assumptions.  It does not give the unconditional ordinary-shell
  high-mode estimate (15).

## 8. Exact frontier change

Before this theorem, the open problem mixed two logically different effects:

\[
 \text{permanent non-Haar locality}
 \quad+\quad
 \text{failure to hit short-circuit targets}.
\]

After Theorem B they separate exactly:

\[
 \boxed{
 \text{subexponential observer memory}
 \xrightarrow{\text{equilibrium charge}}
 \text{capacity-suppressed and harmless},
 \qquad
 \text{high-mode Bellman remainder}
 =\text{sole static shortcut core}.}
\]

Theorem D adds the quantitative uncertainty principle

\[
 \boxed{
 \text{captured accessibility fraction}
 \le {\operatorname{cap}_a(A)\times\text{observer dimension}\over(1-a)^2}.}
\]

Exponential recurrence capacity therefore forces growing replica order before any static-dynamics
estimate begins.  This identifies the order-`D/log D` observer scale as intrinsic rather than a
union-bound artifact.

Theorems E--F then identify the missing universal primitive:

\[
 \boxed{
 {d\sigma_{A,a}\over d\pi}
 ={(1-a)h_A\over\operatorname{cap}_a(A)},
 \qquad
 \text{complexity}
 \asymp-\log h_A
 =\log{1-a\over\operatorname{cap}_a(A)}
  -\log{d\sigma_{A,a}\over d\pi}.}
\]

The accessibility likelihood is globally exponentially non-Haar yet asymptotically absent from
every polynomial-copy sector.  Complexity therefore measures loss of gate accessibility, not
production of Haar randomness.

This is the positive advance.  It proves that locality's permanent visibility is compatible with
maximal complexity without appealing to Haar randomness, and it tells the next proof exactly which
component to estimate.

## Log

- 2026-08-11 -- conjectured, duplicate-audited, hostile-tested, and paper-proved
