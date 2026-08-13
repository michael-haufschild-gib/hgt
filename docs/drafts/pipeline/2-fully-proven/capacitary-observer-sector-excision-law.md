# Capacitary observer-sector excision law

- **ID:** `capacitary-observer-sector-excision-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `first-entrance-gate-capacity-discrepancy-law.md`, `first-entrance-gate-renewal-prefix-law.md`
- **Statement:** Circuit complexity is logarithmic loss of a capacity-normalized gate-accessibility likelihood; every subexponential observer sector sees only target-capacity mass, while the full nonlinear reporter is equivalent at exponential scale to one linear Abel average of circuit incidence.

## Goal

Remove a false obstruction from the static-local Brown problem.  Constant-local Hamiltonian
ensembles can remain efficiently distinguishable from Haar at every time, whereas Brown--Susskind
complexity is expected to become maximal.  The theorem below proves that these statements are not
in tension: every gate-invariant observer sector with subexponential resolvent kernel is invisible
at the exponentially small capacity scale relevant to the complete circuit union.  Only the
complementary high-mode Bellman remainder can obstruct growth in that decomposition.  Theorem J
then proves that the same unresolved content has an equivalent-scale linear occupation-resolvent
form, so growing replicas and nonlinear Bellman control are possible methods rather than mandatory
invariants.

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

### Theorem G (capacity--entropy--accessibility budget)

Let `R_D` be any return/carrier-excision event and let `V_D` have an arbitrary endpoint law.  Then

\[
 \boxed{
 \Pr\{R_D,\ C_\epsilon(V_D)\le s_D\}
 \le (M/a)^{s_D}
 {\operatorname{cap}_a(A_D)\over1-a}
 \mathbb E\!\left[
  \mathbf1_{R_D}\mathfrak A_{A_D,a}(V_D)
 \right].}
 \tag{11ae}
\]

Equivalently, define capacity surprisal and accessibility excess by

\[
 Q_D:=-\log\operatorname{cap}_a(A_D),
 \qquad
 X_D:=\log\mathbb E\!\left[
  \mathbf1_{R_D}\mathfrak A_{A_D,a}(V_D)
 \right],
 \qquad
 Q_D^{\mathrm{eff}}:=Q_D-X_D+\log(1-a)
 =-\log\mathbb E\!\left[
  \mathbf1_{R_D}h_{A_D}(V_D)
 \right],
 \tag{11ae1}
\]

with `X_D=-infinity` when the expectation vanishes.  Then

\[
 \boxed{
 -\log\Pr\{R_D,C_\epsilon(V_D)\le s_D\}
 \ge Q_D^{\mathrm{eff}}-s_D\log(M/a).}
 \tag{11ae2}
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
high-mode Bellman remainder to decay exponentially to zero.  The exact universal requirement is

\[
 \boxed{
 \text{circuit entropy}+\text{accessibility excess}
 <\text{capacity surprisal}.}
 \tag{11aj}
\]

For projective-state targets, `Q_D=Theta(D)`, so a depth chosen below the capacity rate leaves a
linear margin and subexponential accessibility (11ag) suffices.  For Choi/unitary targets the
stationary capacity may instead have `Q_D=Theta(D^2)`; then `X_D` may be exponential on the `D`
scale and still satisfy (11aj).  The difference `Q_D-X_D`, not either term separately, removes the
ambient-to-static-support codimension and is the physical source-relative accessibility surprisal.
No state-to-Choi scaling transfer is claimed.  Permanent low-mode non-Haar memory is compatible
with the budget by Theorem A.

### Theorem H (carrier soft-min law)

For a probability endpoint law `nu`, define its unexcised source-relative accessibility surprisal

\[
 \mathcal Q_{A,a}(\nu):=-\log\int h_A\,d\nu.
 \tag{11ak}
\]

Let `nu=sum_(i=1)^N w_i nu_i`, where `w_i>0`, `sum_i w_i=1`, and every `nu_i` is a probability
law.  Put `Q_i=mathcal Q_(A,a)(nu_i)`.  Then

\[
 \boxed{
 e^{-\mathcal Q_{A,a}(\nu)}
 =\sum_{i=1}^Nw_i e^{-Q_i}.}
 \tag{11al}
\]

Consequently

\[
 \boxed{
 \min_iQ_i
 \le\mathcal Q_{A,a}(\nu)
 \le\min_i\left(Q_i+\log{1\over w_i}\right).}
 \tag{11am}
\]

For a measurable carrier set `B` of endpoint-law mass `w in (0,1)`, let `nu_B` and `nu_G` be the
conditional carrier and good laws.  Then

\[
 \boxed{
 e^{-\mathcal Q(\nu)}
 =w e^{-\mathcal Q(\nu_B)}
 +(1-w)e^{-\mathcal Q(\nu_G)}.}
 \tag{11an}
\]

In particular, if the carrier can return or prepare the target with order-one first-entrance mass,
so `mathcal Q(nu_B)=O(1)`, its contribution to a depth-`s` complete-union bound is negligible at
exponent `kappa` only if

\[
 \boxed{w\le\exp[-s\log(M/a)-\kappa+O(1)].}
 \tag{11ao}
\]

#### Proof

The integral of `h_A` is linear in the endpoint law, proving (11al).  Since

\[
 e^{-\min_iQ_i}\ge\sum_iw_i e^{-Q_i}
 \ge w_j e^{-Q_j}
\]

for every `j`, negative logarithms give (11am).  The two-cell specialization is (11an).
Multiplying the carrier contribution by the circuit factor `(M/a)^s` gives (11ao).  QED.

Theorem H classifies exactly when carrier removal is mathematically necessary.  Small probability
alone is insufficient: an easy component pays its rarity only through `log(1/w)`.  Conversely, a
carrier below the threshold (11ao) may remain in the ensemble without changing the Brown exponent.
This replaces an informal exceptional-set instruction by a quantitative source-mixture law.

### Theorem I (completed-phase accessibility plateau)

Let `(Z,mu)` be a compact probability space, `Phi:Z->X` continuous, and assume the uniform circuit
target bound

\[
 \mu\{z:d(\Phi(z),W\chi)\le\epsilon\}\le B
 \tag{11ap}
\]

for every gate word `W`, including the empty word.  Then the discounted first-entrance potential
obeys

\[
 \boxed{
 \int_Zh_{A_\epsilon}(\Phi(z))\,d\mu(z)
 \le {B\over1-a}.}
 \tag{11aq}
\]

Consequently, for every `theta>0`,

\[
 \boxed{
 \mu\{z:h_{A_\epsilon}(\Phi(z))\ge\theta\}
 \le {B\over(1-a)\theta},}
 \tag{11ar}
\]

and for every circuit depth `s`,

\[
 \boxed{
 \mu\{z:C_\epsilon(\Phi(z))\le s\}
 \le{B\over1-a}\left({M\over a}\right)^s.}
 \tag{11as}
\]

#### Proof

For each word `W` of length `ell`, the inverse-word identity gives

\[
 W^{-1}\Phi(z)\in A_\epsilon
 \quad\Longleftrightarrow\quad
 d(\Phi(z),W\chi)\le\epsilon.
\]

Dropping the first-hit restriction only increases the discounted path sum, so pointwise

\[
 h_{A_\epsilon}(\Phi(z))
 \le\sum_{\ell\ge0}\sum_{|W|=\ell}
 \left({a\over M}\right)^\ell
 \mathbf1_{\{d(\Phi(z),W\chi)\le\epsilon\}}.
 \tag{11at}
\]

Tonelli, (11ap), and at most `M^ell` words of length `ell` give

\[
 \int h_A\,d\mu
 \le\sum_{\ell\ge0}M^\ell(a/M)^\ell B
 =B\sum_{\ell\ge0}a^\ell={B\over1-a}.
\]

Markov proves (11ar).  If `C_epsilon(Phi(z))<=s`, one shortest successful word contributes at
least `(a/M)^s` to first-entrance mass, so (11ar) with `theta=(a/M)^s` proves (11as).  QED.

### Corollary I.1 (static phase completion and recurrence)

Apply Theorem I to the equal-weight spectral phase torus of a `D`-level Choi trajectory.  The
formally proved phase-coherence target theorem supplies, for `0<delta<1/2`,

\[
 B=B_D(\delta)
 :=D e^{D/2}
 \left({\pi(1-\sqrt{1-4\delta^2})\over2}\right)^{(D-1)/2}.
 \tag{11au}
\]

Hence

\[
 \boxed{
 \int_{\mathbb T^D}h_{A_\delta}(\Phi(z))\,dz
 \le{B_D(\delta)\over1-a}.}
 \tag{11av}
\]

If the projective spectral gaps are rationally independent, unique ergodicity transfers the same
upper bound to completed physical time:

\[
 \boxed{
 \limsup_{T\to\infty}{1\over2T}
 \int_{-T}^T h_{A_\delta}(\Phi_H(t))\,dt
 \le{B_D(\delta)\over1-a}.}
 \tag{11aw}
\]

At every `delta`-return time, `h_(A_delta)(Phi_H(t))=1`.  If
`B_D(delta)/(1-a)<theta<1`, accessibility below `theta` occurs syndetically: there is a finite
`L` such that every interval of length `L` contains a time with `h_(A_delta)(Phi_H(t))<theta`.

#### Proof

Only the physical-time transfer and syndetic claim remain.  Truncate the right side of (11at) at
word length `N`.  It is a finite positive sum of indicators of closed phase-torus sets, hence an
upper-semicontinuous bounded function.  Portmanteau for the uniquely ergodic phase flow bounds its
upper time average by its torus integral.  The omitted tail is uniformly at most

\[
 \sum_{\ell>N}a^\ell={a^{N+1}\over1-a}.
\]

Letting `N->infinity` proves (11aw).  The infinite all-word majorant in (11at) is the uniform limit
of upper-semicontinuous functions and is therefore upper semicontinuous.  Its torus mean is at most
`B_D(delta)/(1-a)<theta`, so its strict sublevel set at `theta` is nonempty and open.  Minimality of
the projective phase rotation makes visits to every nonempty open set syndetic.  Since `h_A` is
bounded above by this majorant, each visit has `h_A<theta`.  The return statement is the boundary
condition `h_A=1` on `A`.  QED.

Corollary I.1 is an unconditional completed-time accessibility plateau plus exact recurrence
reamplification statement.  It contains no circuitwise maximum, design approximation, Haar-random
eigenbasis, or stochastic drive.  It does not prove growth: it neither locates the first
accessibility drop nor gives its Brown-rate time dependence.

### Corollary I.2 (zero-loss exponential compression of the circuit union)

For every integer `s>=1`, choose

\[
 a_s={s\over s+1}.
 \tag{11ax}
\]

Then Theorem I gives

\[
 \boxed{
 \mu\{C_\epsilon(\Phi(z))\le s\}
 \le (s+1)\left(1+{1\over s}\right)^sM^sB
 \le e(s+1)M^sB.}
 \tag{11ay}
\]

Moreover `a_s` minimizes `a^{-s}/(1-a)` over `0<a<1`.

#### Proof

Insert (11ax) into (11as).  The elementary inequality `(1+1/s)^s<=e` gives the second bound.
For optimality, differentiate

\[
 -s\log a-\log(1-a).
\]

Its derivative vanishes exactly at `a=s/(s+1)`, and its second derivative is positive.  QED.

Thus one accessibility reporter at an optimized fugacity replaces the complete depth-`s` circuit
union while losing only `log(s+1)+1` in the exponent.  The direct union remains sharper in its
prefactor; accessibility is stronger as a representation because the same scalar also has exact
return value, capacity normalization, observer-sector decomposition, and a physical-time plateau.

### Corollary I.3 (all-late-time fixed-shell accessibility plateau)

Let `H(theta)` be the unit coefficient-sphere nearest-neighbour two-local Pauli ensemble from
`fixed-shell-angular-dephasing-static-local-plateau-law.md`, and let `Phi_(H(theta))(t)` be its Choi
trajectory.  Then

\[
 \boxed{
 \limsup_{t\to\infty}
 \mathbb E_{\theta}
 h_{A_\delta}(\Phi_{H(\theta)}(t))
 \le{B_D(\delta)\over1-a}.}
 \tag{11az}
\]

Consequently, for every `theta_0>0`,

\[
 \boxed{
 \limsup_{t\to\infty}
 \Pr_\theta\!\left\{
 h_{A_\delta}(\Phi_{H(\theta)}(t))\ge\theta_0
 \right}
 \le{B_D(\delta)\over(1-a)\theta_0},}
 \tag{11ba}
\]

and

\[
 \boxed{
 \limsup_{t\to\infty}
 \Pr_\theta\{C_\delta(\Phi_{H(\theta)}(t))\le s\}
 \le{B_D(\delta)\over1-a}\left({M\over a}\right)^s.}
 \tag{11bb}
\]

The same-time local conserved-source witness remains nonzero for every member of the shell and
every time.  Thus every sufficiently late common time has an accessibility plateau and exponential
circuit hardness with high shell probability while the ensemble remains efficiently distinguishable
from Haar.

#### Proof

The fixed-shell angular-dephasing theorem proves weak convergence of the joint angular--projective
phase law to spherical angular measure times projective Haar phase measure.  Use the word-length
`N` truncation of the all-word majorant (11at) on each simple-spectrum eigenchart.  It is a bounded
upper-semicontinuous function of the angular--phase pair.  Portmanteau bounds its limiting upper
expectation by its product-measure integral.  The universal phase-target estimate (11au) is uniform
in the eigenbasis and every circuit target, so Theorem I bounds that product integral by
`B_D(delta)/(1-a)`.  The omitted tail is uniformly at most `a^(N+1)/(1-a)`.  Exhaust the null
spectral discriminant by compact simple-spectrum charts and let `N->infinity`; this proves (11az).
Markov gives (11ba), and the pointwise implication
`C_delta<=s => h_(A_delta)>=(a/M)^s` gives (11bb).  The local-witness statement is the exact
all-time conserved-source theorem already proved for this shell.  QED.

Corollary I.3 is stronger than radial Gaussian mixing: every Hamiltonian has the same normalized
interaction strength.  It is also stronger than a late subsequence: the `limsup` controls every
sufficiently late common time.  Its threshold is non-effective in `D`, so it does not solve Brown
onset.

### Imported Theorem J (renewal-linearized circuit-incidence law)

This is Corollaries 2.2--2.4 of `first-entrance-gate-renewal-prefix-law.md`, restated here because
its linear form becomes load-bearing after Theorem I.  The renewal identity itself is not new.

Define the linear discounted occupation resolvent

\[
 g_{A,a}:=(I-aP)^{-1}\mathbf1_A
 =\sum_{\ell\ge0}a^\ell P^\ell\mathbf1_A.
 \tag{11bc}
\]

For every starting point,

\[
 \boxed{
 (1-a)g_{A,a}(x)\le h_A(x)\le g_{A,a}(x).}
 \tag{11bd}
\]

More precisely, if `X_tau_A` is the first entrance point, then

\[
 \boxed{
 g_{A,a}(x)
 =\mathbb E_x\!\left[
   a^{\tau_A}g_{A,a}(X_{\tau_A})
   \mathbf1_{\{\tau_A<\infty\}}
  \right].}
 \tag{11be}
\]

For every finite positive endpoint measure `nu`, put

\[
 b_\ell(\nu,A):=\int P^\ell\mathbf1_A\,d\nu,
 \qquad
 Z_a(\nu,A):=\sum_{\ell\ge0}a^\ell b_\ell(\nu,A).
 \tag{11bf}
\]

For the uniform inverse-gate walk,

\[
 b_\ell(\nu,A)
 ={1\over M^\ell}\sum_{|W|=\ell}\nu(WA),
 \tag{11bg}
\]

with the harmless inverse convention determined by the chosen action.  Therefore

\[
 \boxed{
 (1-a)Z_a(\nu,A)
 \le\int h_A\,d\nu
 \le Z_a(\nu,A).}
 \tag{11bh}
\]

If `C_epsilon(x)` is finite, then the linear reporter satisfies

\[
 \boxed{
 \left({a\over M}\right)^{C_\epsilon(x)}
 \le g_{A_\epsilon,a}(x)
 \le {a^{C_\epsilon(x)}\over1-a}.}
 \tag{11bi}
\]

Consequently

\[
 \boxed{
 \nu\{C_\epsilon\le s\}
 \le\left({M\over a}\right)^s Z_a(\nu,A_\epsilon).}
 \tag{11bj}
\]

This scale is reversible: if `p=nu{C_epsilon<=s}`, then

\[
 \boxed{
 Z_a(\nu,A_\epsilon)
 \ge p\left({a\over M}\right)^s.}
 \tag{11bk}
\]

Finally, every eigenfunction in (3) obeys the exact linear source law

\[
 \boxed{
 \langle g_{A,a},\phi_j\rangle_\pi
 ={\langle\mathbf1_A,\phi_j\rangle_\pi
   \over1-a\lambda_j},
 \qquad
 \int g_{A,a}\,d\pi={\pi(A)\over1-a}.}
 \tag{11bl}
\]

#### Proof

The Neumann series in (11bc) converges monotonically and is the expected discounted occupation
time

\[
 g_{A,a}(x)=\mathbb E_x\sum_{\ell\ge0}a^\ell\mathbf1_A(X_\ell).
\]

There is no contribution before `tau_A`.  The strong Markov property at `tau_A` therefore gives
(11be).  On `A`, the `ell=0` term gives `g_(A,a)>=1`, while the geometric series gives
`g_(A,a)<=1/(1-a)`.  Substitution in (11be) proves (11bd).  Tonelli and the uniform word expansion
of `P^ell` give (11bf)--(11bg); integration of (11bd) proves (11bh).

The lower half of (11bi) follows from `g>=h` and (11b).  Before a shortest successful word of
length `C_epsilon(x)` no occupation is possible, so every term in (11bc) has
`ell>=C_epsilon(x)`; summing the remaining geometric tail proves the upper half.  On
`{C_epsilon<=s}`, the lower half of (11bi) is at least `(a/M)^s`.  Integrating gives both
(11bj) and (11bk).  Applying `(I-aP)g_(A,a)=1_A` against each eigenfunction proves the first
identity in (11bl); the constant eigenfunction gives the second.  QED.

### Corollary J.1 (one geometric-circuit collision replaces the complete union)

Let `L` be independent of `x` with

\[
 \Pr\{L=\ell\}=(1-a)a^\ell,
 \qquad \ell=0,1,\ldots,
 \tag{11bn}
\]

and, conditional on `L=ell`, let `W_L` be one uniformly random length-`ell` gate word.  For
`x` drawn from the normalized endpoint law `nu`, define

\[
 p_{\rm coll}(\nu,A;a)
 :=\Pr\{W_L^{-1}x\in A\}.
\]

Then

\[
 \boxed{
 p_{\rm coll}=(1-a)Z_a(\nu,A),
 \qquad
 p_{\rm coll}\le\int h_A\,d\nu
 \le{p_{\rm coll}\over1-a}.}
 \tag{11bo}
\]

Consequently

\[
 \boxed{
 \nu\{C_\epsilon\le s\}
 \le {1\over1-a}\left({M\over a}\right)^s
 p_{\rm coll}(\nu,A_\epsilon;a),}
 \tag{11bp}
\]

and the reverse scale bound is

\[
 \boxed{
 p_{\rm coll}(\nu,A_\epsilon;a)
 \ge(1-a)\nu\{C_\epsilon\le s\}
       \left({a\over M}\right)^s.}
 \tag{11bq}
\]

At the depth-optimal fugacity `a_s=s/(s+1)`, the geometric circuit has exact mean length
`E L=s`, and

\[
 \boxed{
 \nu\{C_\epsilon\le s\}
 \le e(s+1)M^s
 p_{\rm coll}(\nu,A_\epsilon;a_s).}
 \tag{11br}
\]

#### Proof

Expand the collision probability first in `L` and then in its uniform word.  Equations
(11bf)--(11bg) give `p_coll=(1-a)Z_a`.  Substitute this identity in (11bh), (11bj), and (11bk).
For `a_s=s/(s+1)`, the geometric mean is `a_s/(1-a_s)=s`, while
`(1+1/s)^s<=e`; this proves (11br).  QED.

Thus optimal fugacity is not merely a calculus choice: it matches the tested shortcut depth to the
mean length of one independent random circuit.  The remaining ordinary-static theorem can be
stated as anti-collision between the physical endpoint and that single geometric random-circuit
ensemble.  It is still exponentially demanding by (11bq).

### Theorem K (all-late same-Hamiltonian hardening shoulder)

Fix `0<epsilon_-<epsilon_+<1/2` and put `gamma=epsilon_+-epsilon_-`.  For the fixed-shell Hamiltonian
`H(theta)` of Corollary I.3, define the uniform simulation envelope

\[
 S_n(u,\gamma)
 :=\sup_\theta\min\left\{|w|:
 \|W_w-(e^{-iuH(\theta)}\otimes I)\|_{\rm op}\le\gamma
 \right\}.
 \tag{11bs}
\]

For every `U>=0`, integer `s>=0`, and `0<a<1`,

\[
 \boxed{
 \begin{aligned}
 \limsup_{T\to\infty}\Pr_\theta\bigl\{\exists u\in[0,U]:\;&
 C_{\epsilon_-}(\Phi_{H(\theta)}(T-u))\\
 &\le s-S_n(u,\gamma)\bigr\}
 \le {B_D(\epsilon_+)\over1-a}
       \left({M\over a}\right)^s .
 \end{aligned}}
 \tag{11bt}
\]

In particular, put

\[
 U_n(s,\gamma)
 :=\sup\left\{U\ge0:
   \sup_{0\le u\le U}S_n(u,\gamma)\le{s\over2}
  \right\}.
 \tag{11bu}
\]

Then

\[
 \boxed{
 \limsup_{T\to\infty}\Pr_\theta\left\{
  \inf_{0\le u\le U_n(s,\gamma)}
  C_{\epsilon_-}(\Phi_{H(\theta)}(T-u))\le{s\over2}
 \right\}
 \le {B_D(\epsilon_+)\over1-a}
       \left({M\over a}\right)^s.}
 \tag{11bv}
\]

For a polynomial-size local gate dictionary and fixed `a`, choose

\[
 s_D=\left\lfloor{\beta D\over\log(M_n/a)}\right\rfloor
\]

with `beta` below the positive completed-phase exponent of `B_D(epsilon_+)`.  Equivalently, at
optimized fugacity choose `s_D=Theta(D/log M_n)` with
`s_D log(M_n/a_(s_D))<=beta D`.  Standard time-independent local-Hamiltonian simulation,
uniformly on the fixed coefficient shell, gives

\[
 U_n(s_D,\gamma)\ge2^{n(1-o(1))},
\]

while the right side of (11bv) is `exp[-Omega(D)]` for fixed `a`, or for the optimized
`a=a_(s_D)`.  Throughout the same shoulder the exact conserved local-source witness remains
nonzero.

#### Proof

The deterministic hardening-cone inequality from
`fixed-shell-transversality-onset-hardening-cone-law.md` says

\[
 C_{\epsilon_+}(\Phi_H(T))
 \le C_{\epsilon_-}(\Phi_H(T-u))+S_n(u,\gamma).
 \tag{11bw}
\]

Hence the event inside (11bt), even though it quantifies over a continuum of times, is contained
in `{C_(epsilon_+)(Phi_H(T))<=s}`.  Corollary I.3 with `delta=epsilon_+` proves (11bt), with no time
mesh and no union loss.  Definition (11bu) gives (11bv).  The shell has `O(n)` bounded local Pauli
terms.  The uniform fixed-accuracy simulation theorem used by the hardening-cone parent bounds
`S_n(u,gamma)` by `(n(1+u))^(1+o(1))`; inserting `s_D=Theta(D/log M_n)` yields the stated
`2^(n(1-o(1)))` shoulder.  The phase-cap exponent and the condition on `beta` make the probability
exponent negative.  The all-time local witness is unchanged by restricting to this event.  QED.

Theorem K proves a Brown-scale *backward lower envelope* attached to every sufficiently late common
endpoint time.  It is pathwise for each Hamiltonian selected by that endpoint event and costs no
continuum union.  It does not locate the first plateau time, force monotonicity above the envelope,
or anchor a ramp at `t=0`; recurrence forbids replacing the time-dependent high-probability set by
one fixed set valid for all late times.

Imported Theorem J is the exact incidence-normalized survivor.  It counts circuit words with their true
multiplicity in (11bg), retains every repeated occupation sheet in `g_(A,a)`, and removes those
repetitions by first entrance only through the sharp universal factor in (11bd).  The nonlinear
Bellman reporter and the linear Abel incidence profile therefore carry the same exponential
information.  At Brown depth, proving

\[
 \boxed{
 Z_a(\nu_t,A_\epsilon)
 \le\exp\!\left[-s_D(t)\log(M/a)-\kappa D\right]}
 \tag{11bm}
\]

is sufficient for an `exp(-kappa D)` complete-shortcut bound, and (11bk) shows that this exponent
cannot be improved without additional information.  The open object is now one length-averaged,
positive incidence profile, not a maximum over targets, a growing-replica pseudodeterminant, or an
unknown equilibrium charge.  Equation (11bm) itself is not proved here.

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
`R^+_{E_D,a}` can prevent a Brown-depth lower bound through Theorem B; Theorem J supplies the
alternative linear Abel-incidence route.

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

### C6. Any small carrier neighbourhood is harmless

Verdict: `[FALSIFIED; EXACT SURVIVOR PROVED]` by Theorem H.

An easy carrier of endpoint-law mass `w` enters source-relative surprisal at cost only
`log(1/w)`.  It is harmless at circuit depth `s` precisely when that rarity pays the circuit
entropy as in (11ao).  Polynomial-codimension rarity cannot be silently discarded from an
exponential-tail theorem.

### C7. Completed phase controls only individual circuit layers

Verdict: `[FALSIFIED; STRONGER SURVIVOR PROVED]` by Theorem I.

Discounted path weights cancel gate-word branching exactly after phase averaging.  The entire
first-entrance accessibility reporter has completed-phase mean at most `B_D(delta)/(1-a)`, not only
each finite circuit layer.  Unique ergodicity transfers this to completed physical time, and
accessibility drops are syndetic.  The theorem closes the plateau/recurrence reporter law but gives
no first-drop time.

### C8. The high-mode Bellman remainder has Brown-rate decay for ordinary static-local dynamics

Verdict: `[OPEN SUFFICIENT FORM; SUPERSEDED AS PRIMARY BY C9]`.

For the Gaussian coefficient ensemble on the full nearest-neighbour two-local Pauli shell, use
either a fixed `0<a<1` or the depth-optimal fugacity `a_D=s_D/(s_D+1)` from Corollary I.2.  On the
prescribed geometric Brown skeleton, after the target-independent spectral-return excision and the
named capacity-compatible fast-forwardable-carrier excision already defined in the parent programme,
freeze the following scale-correct pair.

For the projective-state branch, where `Q_D=Theta(D)`,

\[
 \boxed{
 \sup_{t\in\mathcal T_D}
 \mathbb E_H\!\left[
  \mathbf1_{R_D(H,t)}\mathfrak A_{A_D,a}(V_{H,t})
 \right]=\exp[o(D)].}
 \tag{C8-S}
\]

For a Choi/unitary branch, no bound on `X_D` alone is frozen.  The scale-correct claim is instead

\[
 \boxed{
 \inf_{t\in\mathcal T_D}
 \left(Q_D^{\mathrm{eff}}(t)-s_D(t)\log(M/a)\right)
 \ge\kappa D}
 \tag{C8-C}
\]

for one `kappa>0` at the intended Brown depth.  This allows `X_D=Theta(D^2)` when it pays only the
ambient-to-static-support codimension.

At the first certified recurrence window, pointwise accessibility returns to its
reciprocal-capacity value, so the unexcised pointwise accessibility surprisal `-log h_A` collapses
to zero on the recurrent coefficient set.  Statements (C8-S)--(C8-C) remain a scale-correct
sufficient truth-hunch; Theorem J shows that they are not the unique invariant a proof must control.

The remaining core is now strictly smaller:

\[
 \boxed{
 Q_D^{\mathrm{eff}}(t)-s_D(t)\log(M/a)\ge\kappa D}
 \tag{15}
\]

on the geometric Brown skeleton, after the common return and fast-forwardable-carrier excision.
Unlike global Haar convergence, (15) asks only that source-relative accessibility surprisal beat
circuit entropy.  Theorem G proves that this pays the entire complete circuit union.  Any future
growing-replica or Bellman argument should be centered against `Pi_E` before estimating this
normalized quantity.  In the projective-state branch, (C8-S) is one sufficient way to prove (15);
it is not imposed on the Choi branch.

### C9. Brown escape requires targetwise or growing-replica coarea control

Verdict: `[FALSIFIED AS A NECESSITY; EXISTING LINEAR SURVIVOR REEXPOSED]` by imported Theorem J.

The exact Brown-scale target is the return/carrier-excised Abel incidence bound (11bm), with `nu_t`
allowed to be the corresponding subprobability law.  It averages the occupied image over all words
at each length before summing lengths, preserves word multiplicity, and is linearly generated by
`1_A`.  Thus a targetwise pseudodeterminant lower tail is one possible sufficient method, not the
mathematical invariant that must be estimated.  A proof of (11bm) may instead use cancellation,
geometry, or circuit-distribution structure visible only after the word average.

This does not make the remaining estimate easy.  The factor `(M/a)^s` in (11bj) is sharp by
(11bk), so `Z_a` still has to reach the full capacity exponent on the Brown skeleton.  The gain is
structural: the open core is a single positive linear resolvent matrix coefficient rather than a
complete circuit union or nonlinear first-entrance remainder.

### C10. An all-late annealed plateau cannot yield a same-Hamiltonian time interval without a mesh

Verdict: `[FALSIFIED; STRONGER SURVIVOR PROVED]` by Theorem K.

One hard endpoint deterministically casts the entire backward simulation-cost cone.  Therefore the
same high-probability Hamiltonian set selected at time `T` is hard on a continuum of preceding times,
with no grid union and no probability loss.  The survivor is a Brown-scale backward lower envelope,
not monotone growth from the laboratory origin.

## 6. Hostile audit

1. **Classical core.**  Equilibrium charge, spectral calculus, and reproducing kernels are standard.
   Novelty is claimed only for the observer-excised complete-circuit reduction and its exact
   locality--complexity consequence.
2. **No Brown growth yet.**  Theorems B and G isolate but do not prove (15).  Theorem I closes
   completed-time accessibility plateau and recurrence, not first-drop time or a linear ramp.
   Theorem J gives the equivalent-scale linear target (11bm), but does not prove it for ordinary
   local-Hamiltonian ensembles.
3. **Fugacity scale.**  If `a` approaches one exponentially fast, `(1-a)^-1` may erase the gain.
   Fixed `a` is safe; the depth-optimal `a=s/(s+1)` costs only the polynomial factor `s+1`.
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
12. **State and Choi capacity scales differ.**  The projective-state copy bound has
   `-log cap=Theta(D)` at fixed resolution.  A Choi/unitary gate space can have
   `-log cap=Theta(D^2)` while its static phase support has only `Theta(D)` effective target
   surprisal.  The accessibility excess `X_D` absorbs this codimension; imposing `X_D=o(D)` there
   would be false or needlessly strong.
13. **Reporter compression does not sharpen the direct union prefactor.**  Equation (11as) has
   factors `a^(-s)/(1-a)`.  Corollary I.2 reduces this to `e(s+1)`, preserving the exponential
   rate but not improving direct circuit counting.  Its gain is one reporter that simultaneously
   encodes every depth, capacity, plateau, and recurrence.
14. **Linearization is not anti-concentration.**  Renewal removes repeated-return and Bellman
   bookkeeping only.  It supplies no numerical upper bound on the averaged incidence coefficients
   `b_ell(nu_t,A)` at Brown time.
15. **Backward shoulder is not initial Brown growth.**  Theorem K attaches a deterministic lower
   envelope to a late hard endpoint.  It neither bounds first plateau entry nor excludes earlier
   complexity fluctuations and incubation.
16. **Lean boundary.**  No theorem from this card may enter a final manuscript until its exact
   finite-dimensional form is formalized and audited.  Lean work is intentionally deferred during
   the active corpus refactor.

## 7. External comparison

- Gaudilliere--Landim, *A Dirichlet principle for non reversible Markov chains and some recurrence
  theorems*, arXiv:1111.2445, represents the classical capacity/Poisson background.
- The strong-Markov decomposition of a Green occupation kernel through first entrance is classical;
  see Proposition 6.4 in Singh's *Advanced Probability Theory* notes and the occupation identities
  in Aldous--Fill, *Reversible Markov Chains and Random Walks on Graphs*.  No novelty is claimed for
  (11be) alone.  The candidate advance is its scale-sharp composition with gate-word incidence,
  robust word complexity, return multiplicity, and the Brown circuit-entropy threshold
  (11bf)--(11bm).
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
- Oszmaniec--Kotowski--Horodecki--Hunter-Jones, *Saturation and recurrence of quantum complexity in
  random local quantum dynamics*, arXiv:2205.09734, proves saturation and recurrence for random
  circuits and stochastic Hamiltonians through high designs.  It does not treat the deterministic
  static spectral phase orbit or the first-entrance accessibility reporter (11av)--(11aw).
- Balasubramanian--Caputa--Magan--Wu, *Quantum chaos and the complexity of spread of states*,
  arXiv:2202.06957, relates a Krylov/spread complexity to survival amplitude and spectral
  statistics.  That complexity is not gate word complexity, and its survival amplitude is not the
  gate first-entrance likelihood used here.
- Haferkamp--Faist--Kothakonda--Eisert--Yunger Halpern, *Linear growth of quantum circuit
  complexity*, proves forward growth for refreshed random circuits.  Hamiltonian-simulation theory
  supplies the upper simulator used in (11bw).  Targeted search located neither an all-late
  fixed-strength static-local Choi plateau nor its no-mesh same-Hamiltonian backward-shoulder
  composition.  This absence is not priority evidence; Theorem K's external novelty remains
  provisional pending specialist review.

## 8. Exact frontier change

Before this theorem, the open problem mixed two logically different effects:

\[
 \text{permanent non-Haar locality}
 \quad+\quad
 \text{failure to hit short-circuit targets}.
\]

After Theorem B they separate exactly at the nonlinear level:

\[
 \boxed{
 \text{subexponential observer memory}
 \xrightarrow{\text{equilibrium charge}}
 \text{capacity-suppressed and harmless},
 \qquad
 \text{high-mode Bellman remainder}
 =\text{remaining nonlinear shortcut core}.}
\]

Theorem D adds the quantitative uncertainty principle

\[
 \boxed{
 \text{captured accessibility fraction}
 \le {\operatorname{cap}_a(A)\times\text{observer dimension}\over(1-a)^2}.}
\]

Exponential recurrence capacity therefore forces growing replica order for any observer-sector
representation of the global reporter.  For projective-state `epsilon`-balls this identifies the
order-`D/log D` observer scale as intrinsic rather than a union-bound artifact; no identical Choi
scaling is asserted.  Theorem J later shows that growing replicas are not mandatory for the
dynamical estimate itself.

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

Theorem J then linearizes the remaining frontier without losing its exponent:

\[
 \boxed{
 Z_a(\nu,A)
 =\sum_{\ell\ge0}{a^\ell\over M^\ell}
   \sum_{|W|=\ell}\nu(WA),
 \qquad
 (1-a)Z_a\le\int h_A\,d\nu\le Z_a.}
\]

Thus the exact ordinary-static target is a Brown-rate upper bound on one positive Abel average of
occupied circuit incidence.  Complete targetwise coarea, growing replicas, and nonlinear Bellman
control remain possible proof methods, but none is logically necessary.  Theorem J does not prove
that Brown-rate estimate.

Theorem K supplies the complementary time geometry already available unconditionally: once any
late endpoint reaches the phase-cap plateau, local simulation forces the same Hamiltonian to carry
a nearly linear backward lower envelope over `2^(n(1-o(1)))` physical time, with the endpoint's
full high probability and no time-net loss.  The unproved part of Brown growth is therefore the
laboratory-time anchor/first escape, not the existence of a long local ramp shoulder adjacent to a
certified plateau endpoint.

This is the positive advance.  It proves that locality's permanent visibility is compatible with
maximal complexity without appealing to Haar randomness, and it tells the next proof exactly which
component to estimate.

## Log

- 2026-08-11 -- conjectured, duplicate-audited, hostile-tested, and paper-proved
- 2026-08-13 -- proved completed-phase accessibility plateau, optimized fugacity, fixed-shell
  all-late transfer, quantitative carrier soft-min law, and hostile scale correction between state
  and Choi branches.
- 2026-08-13 -- duplicate audit identified Theorem J's renewal core in the named parent; novelty
  attribution corrected.  Proved Theorem K by composing the all-late Choi plateau with the
  deterministic local-simulation cone, obtaining a no-mesh same-Hamiltonian backward shoulder.
