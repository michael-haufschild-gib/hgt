# Route E critical antiscale diffuse-codiagonal transfer law

- **ID:** `ROUTE-E-CRITICAL-ANTISCALE-DIFFUSE-CODIAGONAL-001`
- **Stage:** 2-fully-proven
- **Type:** `[EXACT DISSIPATION CLASSIFICATION]` / `[CENTERED TRANSFER LAW]` /
  `[PROOF-BURDEN REDUCTION]`
- **Parent:** `../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **Companions:** `route-e-ramare-recombination-ternary-antiscale-law.md`,
  `route-e-source-faithful-euler-tilt-unit-shell-law.md`
- **RH used:** no
- **Computation used:** no
- **Literature used:** no; internal-corpus derivation only
- **Lean status:** paper synthesis only. The constituent general Fisher-codiagonal contraction,
  squarefree critical lower-corner budget, and diffuse Möbius codiagonal recovery are already
  formal in the read-only corpus. No Lean source was edited during the active refactor.

## 1. Result

Two apparently different Route E obstacles have one exact resolution.

First, for every Mellin exponent \(0<r\le1\), normalized finite Euler parity energy is never
pointwise coercive: simultaneous antiscale phase is the unique zero-dissipation torus point and is
approached at arbitrarily large frequencies. Nevertheless its finite-height quadratic mass tends
to zero along every growing prime packet with divergent \(r\)-harmonic mass.

Second, tensoring this law with sharp state-dependent cofactors does **not** require every cofactor
block to be flat. Every cofactor family splits exactly into:

1. a state mean, multiplied by the dissipative Euler character;
2. a centered off-diagonal codiagonal reporter; and
3. an atomic collision whose norm is bounded by the largest reciprocal marker-state probability.

For ternary coprime markers that maximum probability tends to zero exponentially in marker
harmonic mass. Thus the previous target `TERNARY-MARKER-COFACTOR-FLATNESS` was sufficient but
strictly stronger than necessary. The surviving theorem is a centered one-corner contraction and
physical-normalization problem.

The grown Lean corpus supplies the abstract one-corner contraction and the critical squarefree
Fisher corner with four total units. Its small-cutoff consequence is a literal square-root law.
What remains unproved is the source-faithful identification of the finite sharp Ramaré/unit-shell
cofactor reporter with that contractive corner, with no inverse normalization loss and with the
same moving prime seam.

## 2. One-sided critical dissipation for every \(0<r\le1\)

Let \(Q\) be a nonempty finite prime set, put

\[
 R_Q=\prod_{p\in Q}p,
 \qquad u_{p,r}=p^{-r},
\tag{1}
\]

and define the normalized alternating Euler reporter

\[
 \Psi_{Q,r}(t)
 =\prod_{p\in Q}
   \frac{1-u_{p,r}e^{-it\log p}}{1+u_{p,r}}.
\tag{2}
\]

For one prime set

\[
 d_{p,r}(t)
 =\frac{u_{p,r}|1+e^{it\log p}|^2}{(1+u_{p,r})^2}.
\tag{3}
\]

### Theorem A — exact local deficit and escape classification

For every \(p,r,t\) with \(r>0\),

\[
 \boxed{
 \left|\frac{1-u_{p,r}e^{-it\log p}}{1+u_{p,r}}\right|^2
 =1-d_{p,r}(t).}
\tag{4}
\]

Moreover \(0\le d_{p,r}(t)\le1\), and

\[
 d_{p,r}(t)=0
 \quad\Longleftrightarrow\quad
 e^{it\log p}=-1.
\tag{5}
\]

Consequently

\[
 |\Psi_{Q,r}(t)|^2=\prod_{p\in Q}(1-d_{p,r}(t))\le1.
\tag{6}
\]

On the phase torus the modulus-one locus is the single all-antiscale point. Rational independence
of the prime logarithms and Kronecker recurrence imply

\[
 \boxed{\sup_{t>T}|\Psi_{Q,r}(t)|=1}
\tag{7}
\]

for every \(T\). Thus antiscale coherence is the exact cofinal escape mode, not an artifact of
quadratic approximation.

#### Proof

Expanding the numerator gives

\[
 |1-u e^{-i\theta}|^2
 =(1+u)^2-u|1+e^{i\theta}|^2.
\tag{8}
\]

Divide by \((1+u)^2\) to obtain `(4)`. Since \(0<u<1\),
\(0\le4u/(1+u)^2\le1\), proving the range. The deficit vanishes exactly when
\(1+e^{i\theta}=0\), proving `(5)`. Products give `(6)`. Unique factorization makes
\(\{\log p:p\in Q\}\) rationally independent; recurrence to the all-\(\pi\) torus point proves
`(7)`. ∎

### Theorem B — finite-height critical dissipation saturation

Put

\[
 V_{Q,r}=\prod_{p\in Q}\frac{1+p^{-2r}}{(1+p^{-r})^2}.
\tag{9}
\]

For every \(W>0\),

\[
 \boxed{
 \int_{-W}^{W}|\Psi_{Q,r}(t)|^2\,dt
 \le
 \left(2W+4R_Q(1+|Q|\log2)\right)V_{Q,r}.}
\tag{10}
\]

Also

\[
 \boxed{
 V_{Q,r}\le
 \exp\!\left(-\frac12\sum_{p\in Q}p^{-r}\right).}
\tag{11}
\]

Hence, for every \(0<r\le1\), \(V_{Q,r}\to0\) along any exhaustion of the primes. If
\(R_Q(1+|Q|)=O(W)\), every fixed positive large-value level has relative frequency measure
\(O(V_{Q,r})\), even though modulus-one escape recurs cofinally.

#### Proof

Expanding `(2)` gives one frequency \(-\log a\) for every divisor \(a\mid R_Q\), with squared
coefficient mass exactly `(9)`. Distinct divisors \(a,b\le R_Q\) satisfy

\[
 |\log a-\log b|\ge R_Q^{-1};
\tag{12}
\]

if \(a>b\), integrate \(1/x\) from \(b\) to \(a\) and use
\((a-b)/a\ge1/R_Q\). Ordering the \(2^{|Q|}\) frequencies therefore bounds every reciprocal-gap
row by

\[
 2R_Q(1+|Q|\log2).
\tag{13}
\]

The diagonal integral is \(2W V_{Q,r}\). For unequal frequencies,
\(|\int_{-W}^{W}e^{it\Delta}dt|\le2/|\Delta|\). Schur's row bound `(13)` gives the second term in
`(10)`.

For \(0<u\le1\),

\[
 \frac{1+u^2}{(1+u)^2}
 =1-\frac{2u}{(1+u)^2}
 \le e^{-u/2}.
\tag{14}
\]

Multiply `(14)` with \(u=p^{-r}\) to prove `(11)`. For \(0<r\le1\),
\(p^{-r}\ge p^{-1}\), so Euler's divergence of the reciprocal-prime sum finishes the proof. ∎

This is the exact requested critical classification. For \(r>1\), the accumulated
\(r\)-harmonic mass is finite and `(11)` does not force dissipation to zero. Thus \(r=1\) is the
sharp Euler boundary for this mechanism.

## 3. Centered diffuse codiagonal identity

Let \(\Omega\) be a finite state space, \(w_s>0\), and \(\sum_sw_s=1\). Let
\(A_s,d_s\in\mathbb C\) with

\[
 \sum_sw_sA_s=0.
\tag{15}
\]

Define

\[
 \begin{aligned}
 L_w(A,d)&=\sum_sw_sA_sd_s,\\
 O_w(A,d)&=\sum_{s\ne q}w_sw_q(A_s+A_q)d_s,\\
 R_w(A,d)&=\sum_sw_s^2A_sd_s.
 \end{aligned}
\tag{16}
\]

### Theorem C — exact centered codiagonal recovery

\[
 \boxed{O_w(A,d)=L_w(A,d)-2R_w(A,d).}
\tag{17}
\]

If \(|d_s|\le1\), then

\[
 \boxed{
 |L_w(A,d)-O_w(A,d)|
 \le2w_{\max}\left(\sum_sw_s|A_s|^2\right)^{1/2},
 \qquad w_{\max}=\max_sw_s.}
\tag{18}
\]

#### Proof

Insert the diagonal into the double sum. The complete sum is

\[
 \sum_{s,q}w_sw_q(A_s+A_q)d_s
 =L_w(A,d)+\left(\sum_sw_sd_s\right)
                 \left(\sum_qw_qA_q\right)
 =L_w(A,d)
\tag{19}
\]

by `(15)`. Its diagonal is \(2R_w(A,d)\), proving `(17)`. Finally,

\[
 |R_w(A,d)|
 \le w_{\max}\sum_sw_s|A_s|
 \le w_{\max}\left(\sum_sw_s|A_s|^2\right)^{1/2},
\tag{20}
\]

which proves `(18)`. ∎

Equation `(17)` is precisely the finite probability form of the corpus theorem
`diffuseFisherOffDiagonalCodiagonal_eq_score_sub_collision`. Generic codiagonal summation is
unbounded on \(\ell^2\), but centering changes the object: the desired score is an off-diagonal
rank-two reporter plus a collision controlled by diffuseness.

## 4. Ternary marker transfer without statewise flatness

For ternary coprime marker states \(s=(a,b)\), where \(a,b\) are coprime squarefree
\(Q\)-smooth integers, put

\[
 Z_Q=\prod_{p\in Q}(1+2/p),
 \qquad
 w_{a,b}=\frac1{Z_Qab},
 \qquad
 \chi_{a,b}(t)=\mu(a)\mu(b)(a/b)^{it}.
\tag{21}
\]

These weights sum to one and

\[
 w_{\max}=Z_Q^{-1}
 \le\exp\!\left(-\sum_{p\in Q}\frac1p\right).
\tag{22}
\]

Let \(G_{a,b}(t)\) be arbitrary complex state-dependent cofactor blocks and define pointwise

\[
 \bar G(t)=\sum_{a,b}w_{a,b}G_{a,b}(t),
 \qquad A_{a,b}(t)=G_{a,b}(t)-\bar G(t).
\tag{23}
\]

### Theorem D — mean/diffuse-codiagonal/collision trichotomy

With \(\Phi_Q(t)=\sum_{a,b}w_{a,b}\chi_{a,b}(t)\),

\[
 \boxed{
 \sum_{a,b}w_{a,b}\chi_{a,b}(t)G_{a,b}(t)
 =\bar G(t)\Phi_Q(t)
  +O_w(A(t),\chi(t))+2R_w(A(t),\chi(t)).}
\tag{24}
\]

The collision obeys

\[
 \boxed{
 |2R_w(A(t),\chi(t))|
 \le2e^{-\sum_{p\in Q}1/p}
   \left(\sum_{a,b}w_{a,b}|A_{a,b}(t)|^2\right)^{1/2}.}
\tag{25}
\]

#### Proof

Split \(G=\bar G+A\). The mean gives \(\bar G\Phi_Q\); apply Theorem C to the centered part.
For `(22)`, use \(\log(1+2/p)\ge1/p\), valid for \(p\ge2\). Equation `(25)` follows from
`(18)`. ∎

This theorem is pointwise and permits arbitrary \(t\)-dependence in the cofactor blocks. It does
not assume flatness, independence, or a probabilistic model for those blocks.

For the sharp coprime Ramaré decomposition, the unweighted state sum is recovered by taking

\[
 G_{a,b}(t)=Z_Qab\,H_{M/a,M/b}^{(Q)}(t),
\tag{26}
\]

where \(H^{(Q)}\) is the signed \(Q\)-rough cofactor block. The factor \(ab\) is not a loss
introduced by proof; it is exactly the inverse reciprocal volume weight of the marker state.
Equation `(24)` now gives a complete alternative to statewise flatness:

- the reciprocal state mean is governed by the already proved ternary dissipation factor;
- arbitrary centered cutoff dependence is concentrated in one off-diagonal reporter;
- atomic state collisions vanish with harmonic marker mass once their centered \(L^2(w)\) energy
  is controlled.

Thus no theorem comparing all \(3^{|Q|}\) sharp cofactor blocks to one common block is logically
required.

## 5. One-corner contraction and square-root critical budget

The internal Lean corpus proves following coordinate-free statement. If \(B\) is any
Hilbert--Schmidt source corner and a joined reporter is generated from a unit state by an
orthogonal cutoff and a contraction \(D\), then

\[
 \boxed{|\langle B,\operatorname{Reporter}_D\rangle_{HS}|^2
 \le\frac12\|B\|_{HS}^2.}
\tag{27}
\]

No diagonal, finite-rank, cutoff-commutation, compactness, or coordinate hypothesis occurs. For
the actual squarefree Möbius critical Fisher lower corner, its limiting energy
\(\mathcal E_{\downarrow}(u)\) satisfies

\[
 0\le\mathcal E_{\downarrow}(u)
 \le4(1-e^{-u}),
 \qquad
 \frac{\mathcal E_{\downarrow}(u)}u\longrightarrow4
 \quad(u\downarrow0),
\tag{28}
\]

and

\[
 \int_0^\infty\mathcal E_{\downarrow}(u)\,du=4.
\tag{29}
\]

Combining `(27)` and `(28)` gives the unconditional abstract receiver

\[
 \boxed{
 \limsup_{\sigma\downarrow1}
 |\langle B_{\sigma,u},\operatorname{Reporter}_D\rangle_{HS}|
 \le\sqrt{2(1-e^{-u})}
 \le\sqrt{2u}.}
\tag{30}
\]

This is the first corpus-supported non-diagonal source law with the literal square-root exponent.
The exponent is not inferred from row/co-degree counting: it is forced by half-unit contraction
against a four-density critical boundary.

The relevant formal declarations are:

- `norm_sq_hsInner_infiniteFisherOneCornerJoinedReporter_le_half`;
- `norm_sq_hsInner_squarefreeMobiusCriticalFisherLowerBoundary_joinedReporter_le_half`;
- `squarefreeMobiusCriticalFisherLowerBoundaryLimit_le_four_mul_CDF`;
- `tendsto_squarefreeMobiusCriticalFisherLowerBoundaryLimit_div`;
- `integral_squarefreeMobiusCriticalFisherLowerBoundaryLimit`;
- `tendsto_ofReal_mobiusFisherOffDiagonalCodiagonal` and the stronger one-corner recovery laws.

## 6. Finite Euler Fisher gauge-collapse law

The square-root receiver `(30)` cannot be amplified by choosing an arbitrarily small Euler gauge.
There is an exact finite-dimensional obstruction.

Let \(S\) be a finite prime set and let \(\Omega_S\) be its occupied subsets. Under reciprocal
Euler law

\[
 \nu_{\sigma,S}(T)=\frac{m(T)^{-\sigma}}{\mathcal P_{\sigma,S}},
 \qquad E(T)=\log m(T),
 \qquad \varepsilon=\sigma-1,
\tag{31}
\]

write \(\mu_{\sigma,S}=\mathbb E_\nu E\) and
\(V_{\sigma,S}=\operatorname{Var}_\nu E\). In \(\ell^2(\Omega_S)\), define signed unit state and
critical Fisher tangent

\[
 \psi(T)=\mu(m(T))\sqrt{\nu_{\sigma,S}(T)},
 \qquad
 h(T)=-2\varepsilon(E(T)-\mu_{\sigma,S})\psi(T).
\tag{32}
\]

Let

\[
 F_{\sigma,S}=2^{-1/2}
   (|h\rangle\langle\psi|+|\psi\rangle\langle h|).
\tag{33}
\]

### Theorem E — finite Fisher gauge collapse

One has

\[
 \langle\psi,h\rangle=0,
 \qquad
 \boxed{\|F_{\sigma,S}\|_{HS}^2=4\varepsilon^2V_{\sigma,S}.}
\tag{34}
\]

For every orthogonal cutoff \(e\), every contraction \(D\), lower corner
\(B=(1-e)F_{\sigma,S}e\), and corresponding joined reporter,

\[
 \boxed{
 |\langle B,\operatorname{Reporter}_D\rangle_{HS}|
 \le\sqrt2\,|\varepsilon|\sqrt{V_{\sigma,S}}.}
\tag{35}
\]

Thus, at fixed finite aperture, every raw Fisher one-corner contraction vanishes uniformly as
\(\sigma\to1\). Any connector recovering a nonzero Euler-gauge-invariant physical observable from
this pairing must carry inverse normalization at least on the scale
\((|\varepsilon|\sqrt V)^{-1}\).

#### Proof

Möbius signs have unit modulus on squarefree states, so \(\|\psi\|=1\). Centering gives
\(\langle\psi,h\rangle=0\), while

\[
 \|h\|^2=4\varepsilon^2
   \mathbb E_\nu[(E-\mu_{\sigma,S})^2]
 =4\varepsilon^2V_{\sigma,S}.
\tag{36}
\]

The two rank-one terms in `(33)` are Hilbert--Schmidt orthogonal and each has squared norm
\(\|h\|^2\|\psi\|^2\). The factor \(2^{-1/2}\) proves `(34)`. Orthogonal compression cannot
increase Hilbert--Schmidt norm, so \(\|B\|_{HS}^2\le4\varepsilon^2V\). Apply half-unit contraction
`(27)` and take square roots to obtain `(35)`. ∎

At source-faithful cofinal tilt from the existing unit-shell theorem,

\[
 \varepsilon
 =\frac{2\log\ell}{\ell^2}+O(\ell^{-2}),
 \qquad
 V_{\sigma,S}=\frac{\ell^2}{2}+O(\ell\log\ell),
\tag{37}
\]

so `(35)` is only \(O(\log\ell/\ell)\). More importantly, exact Euler-gauge cancellation says
every normalized physical observable is independent of \(\varepsilon\). Therefore choosing a
smaller \(\varepsilon\) merely shrinks the raw Fisher coordinate and forces the inverse connector
to grow; it cannot manufacture a strict-half estimate.

The finite physical theorem must consequently be **gauge-renormalized before contraction**. It
must prove that the renormalized centered source corner still has small physical energy. Raw
finite Fisher energy `(34)` is not that theorem.

## 7. Heavy conjecture--proof--failure loop

### Loop A: every cofactor state must be flat

`[CONJECTURE]` The reciprocal ternary mean-square can survive only if
\(G_{a,b}(t)=G(t)+o(1)\) uniformly over all marker states.

`[FALSIFIED]` Theorems C--D give exact decomposition `(24)`. Only state mean needs the Euler
character. Centered variation has an off-diagonal representation, and the discarded collision is
bounded by `(25)`.

### Loop B: generic codiagonal unboundedness kills tensor transfer

`[CONJECTURE]` Since algebraic summation is unbounded on \(\ell^2\), no Hilbert-space control can
scalarize state defects.

`[FALSIFIED IN THE CENTERED CLASS]` Centered rank-two Fisher structure supplies identity `(17)`.
The corpus's infinite squarefree realization proves collision disappearance at the critical
boundary. Unboundedness remains valid for arbitrary uncentered coordinates and therefore explains
why centering is essential.

### Loop C: critical dissipation is pointwise coercive

`[CONJECTURE]` For \(0<r\le1\), accumulated Euler mass forces a uniform gap below one.

`[FAILED SHARPLY]` Theorem A: antiscale recurrence approaches modulus one after every height.

### Loop D: antiscale recurrence destroys every averaged gain

`[CONJECTURE]` Cofinal saturation prevents a useful finite-height bound.

`[FALSIFIED]` Theorem B: recurrence-weighted quadratic mass is \(V_{Q,r}\to0\) at exactly the
critical range \(0<r\le1\).

### Loop E: half-unit Fisher contraction already proves Route E

`[CONJECTURE]` Insert the physical Gibbs observable as the contraction in `(27)` and choose
\(u=X^{-1+o(1)}\).

`[FAILED AS STATED]` A source multiplier is useful only after its normalization is tracked.
Dividing a bounded Euler observable by a vanishing source expectation can erase the
\(\sqrt u\) gain. The corpus contains no theorem identifying the sharp finite Gibbs/Ramaré
cofactor reporter with the critical Fisher joined reporter while preserving physical
normalization. Claiming `(30)` as the endpoint would be theatre.

### Loop F: choose an arbitrarily small Euler gauge

`[CONJECTURE]` Since physical Gibbs weights are gauge-invariant, choose
\(\varepsilon\) so small that `(35)` has strict-half size.

`[FAILED SHARPLY]` Theorem E. Raw finite Fisher corner is proportional to \(\varepsilon\), while
the physical observable is independent of it. Every source-faithful identification must undo this
factor. Small gauge changes coordinates, not arithmetic cancellation.

## 8. Revised Route E frontier

Replace

`TERNARY-MARKER-COFACTOR-FLATNESS-AND-RECURRENCE-SEAM`

by the strictly weaker and source-aligned target

**`CENTERED-COFACTOR-ONE-CORNER-CONTRACTION-AND-UNIT-SHELL-SEAM`**:

1. group the actual sharp Ramaré or physical unit-shell source by ternary marker state and use
   exact normalization `(26)`;
2. identify its centered term \(O_w(A,\chi)\) with a source-predeclared joined one-corner reporter
   generated by an \(L^2\)-contraction after the source-forced Fisher gauge is explicitly
   renormalized;
3. compare its finite moving source-corner energy to the critical squarefree Fisher budget without
   an inverse shell-probability loss, and prove that Euler-gauge renormalization does not cancel
   the desired physical saving;
4. take the same reporter through the normalized zero/one-large-prime seam and exact signed
   recurrence;
5. use `(24)`--`(25)` for state mean and collision, rather than proving uniform statewise
   cofactor flatness.

Two abstract ingredients in this list are already unconditional Lean theorems: contractive
one-corner half-energy and critical diffuse collision disappearance. Missing knowledge is the
finite physical connector in items 2--4. If that connector realizes cutoff parameter
\(u_X=X^{-1+o(1)}\) without normalization loss, `(30)` has exactly the strict-half scale. If its
normalization costs \(u_X^{-1/2}\) or worse, this avenue fails and that loss must be proved, not
hidden.

## 9. Honest status

Theorems A--D and inequalities `(27)`--`(30)` are dependency-closed finite/abstract mathematics.
They create new Route E knowledge:

- critical dissipation saturation is now classified for the full range \(0<r\le1\);
- antiscale coherence is the unique cofinal escape mode;
- statewise cofactor flatness is removed as an unnecessarily strong premise;
- generic codiagonal unboundedness is bypassed exactly by centering and diffuseness;
- the existing four-unit Fisher boundary exposes a genuine square-root receiver;
- finite Fisher gauge collapse proves that shrinking the Euler coordinate cannot supply the
  missing arithmetic power.

No finite physical Fisher/Ramaré connector, unit-shell normalization theorem, affine coprime
covariance estimate, Route E endpoint, or RH proof is claimed.
