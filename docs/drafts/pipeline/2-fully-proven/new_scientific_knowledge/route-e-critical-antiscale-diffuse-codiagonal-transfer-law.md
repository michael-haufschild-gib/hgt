# Route E critical antiscale diffuse-codiagonal transfer law

- **ID:** `ROUTE-E-CRITICAL-ANTISCALE-DIFFUSE-CODIAGONAL-001`
- **Stage:** 2-fully-proven
- **Type:** `[EXACT DISSIPATION CLASSIFICATION]` / `[CENTERED TRANSFER LAW]` /
  `[PROOF-BURDEN REDUCTION]`
- **Parent:** `../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **Companions:** `../../3-formalized/new_scientific_knowledge/route-e-ramare-recombination-ternary-antiscale-law.md`,
  `route-e-source-faithful-euler-tilt-unit-shell-law.md`,
  `../../3-formalized/new_scientific_knowledge/route-e-weighted-hall-anova-projection-duality-law.md`,
  `../../3-formalized/new_scientific_knowledge/route-e-degree-normalized-gibbs-boundary-variation-law.md`,
  `../../3-formalized/new_scientific_knowledge/route-e-ramare-incidence-conditional-negativity.md`
- **RH used:** no
- **Computation used:** no
- **Literature used:** no; internal-corpus derivation only
- **Lean status:** Theorems A--B are now closed unconditionally in umbrella-wired Lean by
  `RouteECriticalAntiscaleDissipationSaturation`; exact Stage-3 child:
  `../../3-formalized/new_scientific_knowledge/route-e-critical-antiscale-dissipation-saturation.md`.
  This includes local escape classification, cofinal recurrence, all-order squarefree expansion,
  exact finite-height constant, coefficient mass, arbitrary divergent-packet decay, and canonical
  `0<r<=1` aperture decay. Theorems C--D, including their literal finite complex form and
  maximum-atom collision estimate, and Theorems E, F, and H are now closed by
  `RouteEFinitePhysicalCodiagonalGaugeCollapse`; its one-corner refinement strengthens `(35)` and
  `(38)` by a factor `sqrt 2`. Exact Stage-3 child:
  `../../3-formalized/new_scientific_knowledge/route-e-finite-physical-codiagonal-gauge-collapse.md`.
  Theorem G's exact outward-node equation, half-line observer divergence, and stronger
  phase-independent non-`l2` classification are now closed by
  `RouteEStrictRightMellinObserverFirewall`; exact Stage-3 child:
  `../../3-formalized/new_scientific_knowledge/route-e-strict-right-mellin-observer-firewall.md`.
  The relation-specific estimate `(50)` and signed recurrence seam keep this parent at Stage 2.

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
strictly stronger than necessary. More sharply, the finite physical centered energy is exactly the
ANOVA remainder of column likelihood-ratio chi-square:

\[
 E_{\mathrm{cent}}(\rho\mid\nu)
 =N\operatorname{Var}_{\nu/N}(\rho/\nu)
 =\chi^2(\rho\mid\nu)-\frac{(P-N)^2}{N}.
\]

At physical mass \(N=X^{1+o(1)}\), the exact strict-half producer target is therefore
\(E_{\mathrm{cent}}\le X^{o(1)}\), equivalently
\(\operatorname{Var}_{\nu/N}(\rho/\nu)\le X^{-1+o(1)}\). This target is weaker than uniform
cofactor flatness and stronger than row/co-degree counting.

The grown Lean corpus supplies the abstract one-corner contraction and the critical squarefree
Fisher corner with four total units, but those theorems are receivers rather than arithmetic
producers. Gauge-neutralization and the source-faithful critical clock show that universal Fisher
identification has the wrong quantitative scale. What remains unproved is the finite physical
column-ANOVA estimate above, followed by transport of the same signed reporter through the moving
prime seam and exact recurrence, with mean and collision handled by the ternary decomposition.
The companion weighted-Hall projection law gives an exact equivalent: after normalizing physical
source and target laws, required variance is squared distance from target law to relation's
reachable marginal polytope. Its dual is an all-reporter minimum-neighbor inequality. It also
proves that an unquantified one-sided column ceiling \(1+o(1)\) is not rate-sufficient.
The exact Ramaré incidence decomposition further proves that the arithmetic
incidence-complement kernel is conditionally negative definite. Therefore its centered component
is already favorable once the physical cofactor reporter is shown to land in that exact kernel;
the landing, scalar mean estimate, and recurrence seam remain open.

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
 \le|\varepsilon|\sqrt{V_{\sigma,S}}.}
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
\(\|h\|^2\|\psi\|^2\). The factor \(2^{-1/2}\) proves `(34)`. More precisely than generic
compression, the two oriented off-diagonal corners of the self-adjoint pointed connection have
equal Hilbert--Schmidt energy. Hence one lower corner satisfies

\[
 \|B\|_{HS}^2\le\frac12\|F_{\sigma,S}\|_{HS}^2
 =2\varepsilon^2V_{\sigma,S}.
\]

Apply half-unit joined-reporter contraction `(27)` once more. The squared pairing is at most
\(\frac12\|B\|_{HS}^2\le\varepsilon^2V_{\sigma,S}\), proving `(35)`. ∎

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

### Corollary F — gauge-neutralized energy and forced-clock mismatch

For \(\varepsilon>0\), put

\[
 \widehat h=\varepsilon^{-1}h,
 \qquad
 \widehat F_{\sigma,S}=\varepsilon^{-1}F_{\sigma,S}.
\]

Then `(34)`--`(35)` give

\[
 \boxed{
 \|\widehat F_{\sigma,S}\|_{HS}^{2}=4V_{\sigma,S},
 \qquad
 |\langle(1-e)\widehat F_{\sigma,S}e,
       \operatorname{Reporter}_D\rangle_{HS}|
 \le\sqrt{V_{\sigma,S}}.}
\tag{38}
\]

At the source-faithful tilt `(37)`, the right side is

\[
 \sqrt{V_{\sigma,S}}
 =\frac{\ell}{\sqrt2}\left(1+O\!\left(\frac{\log\ell}{\ell}\right)\right).
\tag{39}
\]

Thus gauge-neutralization removes all apparent Fisher decay: universal one-corner contractivity
alone gives a growing, not shrinking, physical-scale budget.

There is a second exact scale obstruction. The hard cutoff in the corpus is the critical-clock
cutoff

\[
 (\sigma-1)\log n\le u.
\]

On the physical unit shell \(\log n=E^*_{\sigma,x}+O(1)\), the forced tilt satisfies

\[
 \boxed{
 u_{\mathrm{shell}}
 =(\sigma_x-1)E^*_{\sigma_x,x}+O(\sigma_x-1)
 =\frac{2\log\ell}{\ell}+O(\ell^{-1}).}
\tag{40}
\]

Indeed \(E^*_{\sigma_x,x}=L+O(\sigma_x-1)\),
\(L=\ell-\log\ell+O(1)\), and `(37)` gives `(40)`. Even if one grants the as-yet-unproved
uniform passage from the finite moving cutoff to the critical profile `(30)`, inserting the
source-forced shell scale yields only

\[
 \sqrt{2(1-e^{-u_{\mathrm{shell}}})}
 =2\sqrt{\frac{\log\ell}{\ell}}\,(1+o(1)),
\tag{41}
\]

which is \(X^{o(1)}\), not \(X^{-1/2+o(1)}\). The cutoff parameter in `(30)` therefore cannot be
declared to be \(X^{-1+o(1)}\): its physical meaning fixes it at `(40)`.

### Theorem G — graph-normal repair and strict-right firewall

The grown corpus contains an exact contragredient repair for the coordinate gauge. Let
\(\mathcal A_{\sigma,u}(x)\) be its affine Gamma--Xi source map and
\(N_{\sigma,u}\) the forced graph normalizer

\[
 N_{\sigma,u}
 =-2i(\sigma-1)\,
   \operatorname{Overlap}_{\sigma,u}.
\]

For every complex inward node \(\Re u\ge0\), it proves

\[
 \boxed{
 N_{\sigma,u}
   \bigl(\mathcal A_{\sigma,u}(x)-\mathcal A_{\sigma,u}(y)\bigr)
 =\langle x-y,\eta_{\sigma,u}\rangle,
 \qquad
 \|\eta_{\sigma,u}\|\le1.}
\tag{42}
\]

For the actual Fisher tangent this graph-normal coordinate is the division-free squarefree
Fisher numerator, while the unnormalized affine map lands in the completed prime--Gamma Xi trace.
Thus the corpus does solve Euler-coordinate covariance: contractivity holds before the singular
normal factor is inverted.

It does **not** supply the Route E physical connector. The analytic node reached by `(42)` is

\[
 s=\sigma+u(\sigma-1),
 \tag{43}
\]

so \(\Re u\ge0\) keeps \(\Re s>1\). Reaching the Mellin half-line \(\Re s=1/2\) would require

\[
 \Re u=\frac{1/2-\sigma}{\sigma-1}<0,
\tag{44}
\]

outside the controlled Hardy column. This is a strict-right firewall, not a technical omission.

There is a tempting but false Mellin shortcut. Formally,

\[
 e^{-xn}=\frac1{2\pi}\int_{\mathbb R}
   \Gamma(1/2+it)(xn)^{-1/2-it}\,dt,
\tag{45}
\]

and the prefactor \(x^{-1/2}\) has exactly the desired exponent. But representing
\(\sum_n\mu(n)n^{-s}\) as a Hilbert pairing against the normalized squarefree source at parameter
\(\sigma>1\) requires the observer

\[
 v_s(n)=\sqrt{\mathcal Z_\sigma}\,
        n^{\sigma/2-\overline s},
 \qquad
 \|v_s\|_2^2
 =\mathcal Z_\sigma\sum_{n\ \mathrm{squarefree}}
       n^{\sigma-2\Re s}.
\tag{46}
\]

At \(\Re s=1/2\), `(46)` diverges. It is exactly the nonclosable scalar codiagonal, not a bounded
graph-normal reporter. The diffuse-codiagonal recovery theorem does not change this: it recovers
the centered Fisher score \(\sum p_na_nd_n\), not the raw Möbius Dirichlet sum. Hence `(45)` does
not smuggle an RH-strength estimate out of the safe Hilbert source.

Lean now proves more than this pointwise statement. For every `Re s<=sigma/2`, the norm-square
profile in `(46)` is non-summable because its cofinal prime subsequence is bounded below by the
positive squarefree partition mass. Consequently every complex coefficient sequence with that
same magnitude profile is outside `l2`, independently of phase. The exact declarations are
`not_summable_routeEMellinObserverNormSqProfile`,
`routeEMellinHalfLineObserver_not_memℓp`, and
`routeEStrictRightMellinObserverFirewall` in
`RouteEStrictRightMellinObserverFirewall.lean`.

### Theorem H — finite column ANOVA is the physical centered energy

The centered physical target can be stated without any Fisher identification. Let
\(\rho_i\ge0\), \(\nu_i>0\) be finite pushed and target column masses, and put

\[
 P=\sum_i\rho_i,
 \qquad N=\sum_i\nu_i>0,
 \qquad w_i=\frac{\nu_i}{N},
 \qquad r_i=\frac{\rho_i}{\nu_i},
 \qquad A_i=r_i-\frac PN.
\tag{47}
\]

Then \(\sum_iw_iA_i=0\), and target-weighted column chi-square has exact orthogonal decomposition

\[
 \boxed{
 \sum_i\frac{(\rho_i-\nu_i)^2}{\nu_i}
 =N\sum_iw_i|A_i|^2+\frac{(P-N)^2}{N}.}
\tag{48}
\]

#### Proof

Since \(\sum_iw_ir_i=P/N\), score \(A\) is centered. Write
\(r_i-1=A_i+(P/N-1)\). Cross term in \(N\sum_iw_i(r_i-1)^2\) vanishes by centering, leaving
`(48)`. ∎

Equation `(48)` identifies physical meaning of Theorem C. Its first term is exactly centered
likelihood-ratio variance available to diffuse codiagonal identity; its second term is scalar
signed mass discrepancy Route E must bound. Thus global chi-square mixes producer and endpoint,
while centered formulation separates them without loss:

\[
 \boxed{
 E_{\mathrm{cent}}(\rho\mid\nu)
 :=N\operatorname{Var}_{w}(r)
 =\chi^2(\rho\mid\nu)-\frac{(P-N)^2}{N}.}
\tag{49}
\]

Ternary mean dissipation acts on mean channel; one finite physical codiagonal acts on `(49)`;
maximum state weight controls its atomic collision. No comparison with universal critical Fisher
clock is needed. At physical mass \(N=X^{1+o(1)}\), endpoint-scale centered target is

\[
 \boxed{
 E_{\mathrm{cent}}(\rho\mid\nu)\le X^{o(1)},
 \qquad\text{equivalently}\qquad
 \operatorname{Var}_{w}(r)\le X^{-1+o(1)}.}
\tag{50}
\]

This is concrete strict-half producer. It is columnwise, retains actual physical weights, and
cannot be discharged by row/co-degree counts alone.

Moreover, for every \(|d_i|\le1\), Cauchy--Schwarz and Theorem C give

\[
 \boxed{
 N|L_w(A,d)|\le\sqrt{N E_{\mathrm{cent}}},
 \qquad
 N|L_w(A,d)-O_w(A,d)|
 \le2w_{\max}\sqrt{N E_{\mathrm{cent}}}.}
\tag{51}
\]

Consequently `(50)` already puts both centered score and its atomic codiagonal correction at
unnormalized size \(X^{1/2+o(1)}\). Diffuseness improves the collision but is not another power
obligation once column ANOVA is proved. Remaining mean channel and moving seam must still be
controlled separately.

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

### Loop G: choose the critical cutoff at the desired power scale

`[CONJECTURE]` Put \(u_X=X^{-1+o(1)}\) in `(30)` and obtain the endpoint from the square-root
boundary law.

`[FAILED SHARPLY]` Corollary F. On the literal source-faithful shell the critical clock is forced
to \(u_{\mathrm{shell}}=2\log\ell/\ell+O(\ell^{-1})\). The limiting receiver then has only the
logarithmic scale `(41)`, and the corpus contains no uniform two-parameter theorem permitting a
different moving cutoff while retaining the physical reporter.

### Loop H: Mellin-superpose the graph-normal Hardy column on \(\Re s=1/2\)

`[CONJECTURE]` Equation `(45)` turns the uniform norm-one inward Hardy column into an
\(x^{-1/2}\) bound for the signed Gibbs sum.

`[FAILED EXACTLY]` Theorem G. The required scalar observer has divergent norm `(46)`, and the
half-line lies on the forbidden outward side `(44)`. The safe graph normalizer controls a Fisher
score and completed strict-right Xi source, not Möbius scalar summation.

### Loop I: centered codiagonal needs a new Fisher-source comparison

`[CONJECTURE]` To use Theorem C, first identify sharp physical columns with universal critical
Fisher lower corner.

`[FALSIFIED]` Theorem H. Center literal likelihood ratio \(r_i=\rho_i/\nu_i\). Its physical energy
is exactly ANOVA remainder `(49)` of existing column chi-square. Universal Fisher comparison is
unnecessary and, by Corollary F, has wrong scale. Genuinely new estimate is `(50)` for
source-predeclared finite relation.

## 8. Revised Route E frontier

Replace

`TERNARY-MARKER-COFACTOR-FLATNESS-AND-RECURRENCE-SEAM`

by the strictly weaker and source-aligned target

**`FINITE-PHYSICAL-COLUMN-ANOVA-STRICT-HALF-AND-SIGNED-RECURRENCE-SEAM`**:

1. group the actual sharp Ramaré or physical unit-shell source by ternary marker state and use
   exact normalization `(26)`;
2. form literal pushed/target likelihood ratio of finite physical relation and use `(48)` to
   identify its centered codiagonal energy exactly;
3. prove column ANOVA bound `(50)`, or equivalent unit-capacity estimate, without importing the
   scalar signed discrepancy being estimated. Universal Fisher budget cannot supply it:
   gauge-neutralization grows like `(39)` and forced critical clock gives only `(41)`. For the
   exact Ramaré incidence kernel, conditional negativity closes the centered upper bound after a
   source-faithful landing; proving that landing and controlling its scalar mean remain necessary;
4. take the same reporter through the normalized zero/one-large-prime seam and exact signed
   recurrence;
5. use `(24)`--`(25)` for state mean and collision, rather than proving uniform statewise
   cofactor flatness.

Two abstract ingredients in this list are already unconditional Lean theorems: contractive
one-corner half-energy and critical diffuse collision disappearance. They are receivers, not the
missing arithmetic producer. Missing knowledge is finite physical estimate `(50)` and seam
transport in items 3--4.
Corollary F proves that the existing critical-clock corner cannot be assigned endpoint scale by
parameter choice; Theorem G proves that the safe graph-normal Xi landing cannot be continued to
the Mellin half-line by bounded Hilbert observation.
The companion projection theorem sharpens “equivalent unit-capacity estimate”: exact normalized
weighted Hall gives zero centered energy; a one-sided ceiling \(1+\varepsilon_X\) needs
\(\varepsilon_X\le X^{-1+o(1)}\), while a two-sided relative ceiling needs
\(\varepsilon_X\le X^{-1/2+o(1)}\). Merely \(1+o(1)\) is not enough.

## 9. Honest status

Theorems A--H are dependency-closed finite/abstract mathematics or exact consequences of the
read-only formal corpus. They create new Route E knowledge:

- critical dissipation saturation is now classified for the full range \(0<r\le1\);
- antiscale coherence is the unique cofinal escape mode;
- statewise cofactor flatness is removed as an unnecessarily strong premise;
- generic codiagonal unboundedness is bypassed exactly by centering and diffuseness;
- the existing four-unit Fisher boundary exposes a genuine square-root receiver;
- finite Fisher gauge collapse proves that shrinking the Euler coordinate cannot supply the
  missing arithmetic power;
- the physical shell fixes critical clock at \(2\log\ell/\ell+O(\ell^{-1})\), ruling out the
  previously tempting \(u_X=X^{-1+o(1)}\) substitution;
- graph normalization restores exact coordinate covariance on the strict-right Hardy family, but
  the Mellin half-line requires an outward node and a non-\(\ell^2\) scalar observer;
- physical centered codiagonal energy is exactly column-likelihood ANOVA `(49)`, eliminating need
  for universal Fisher identification and isolating quantitative target `(50)`.

No finite physical Fisher/Ramaré connector, unit-shell normalization theorem, affine coprime
covariance estimate, Route E endpoint, or RH proof is claimed.
