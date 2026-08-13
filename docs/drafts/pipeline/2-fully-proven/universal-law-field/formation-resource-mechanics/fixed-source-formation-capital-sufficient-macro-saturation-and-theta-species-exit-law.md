# Fixed-source formation capital, sufficient-macro saturation, and theta species-exit law

- **ID:** ULF-FRM-2
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT FORMATION-CAPITAL THEOREM + SUFFICIENT-STATISTIC FUSION LAW
- **Source:** `../../../1-in-progress/universal-law-field/formation-resource-mechanics/field-programme.md`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [FINITE CORE]`
  `[STANDARD-BOREL THETA COROLLARY] [FOUR-ORGAN FUSION] [BRIDGE]`
  `[OCCUPIED RESOURCE-THEORY PARENT] [LEAN PENDING] [NOT RH]`
- **Statement:** A fixed binary source experiment can form independent target depth only by
  spending additive distinguishability capital; arbitrary exact depth forces a neutral target or a
  singular source, while sufficient macropackets attain every information bound exactly and allow
  the non-infinitely-divisible theta likelihood to form independent descendants only by exiting its
  one-particle species.

## 1. Binary experiments and formation depth

Let `S,X` be finite nonempty sets.  A binary source experiment is

\[
 \mathcal E=(S;r_0,r_1),
 \tag{FCAP.1}
\]

where `r_0,r_1` are probability packets on `S`.  A target experiment is

\[
 \mathcal F=(X;p_0,p_1).
 \tag{FCAP.2}
\]

For an integer `d>=1`, write `p_i^{\otimes d}` for the independent product packet on `X^d`.
A **fixed-source independent depth-`d` formation** is one Markov kernel

\[
 K_d:S\rightsquigarrow X^d
 \tag{FCAP.3}
\]

such that, simultaneously for `i=0,1`,

\[
 r_iK_d=p_i^{\otimes d}.
 \tag{FCAP.4}
\]

The same kernel must work for both marks.  It may use fresh randomness, but it may not be told
which source law was sampled.

Define Hellinger affinity and distance by

\[
 A(u,v)=\sum_z\sqrt{u(z)v(z)},
 \qquad h(u,v)=\sqrt{2-2A(u,v)}.
 \tag{FCAP.5}
\]

Put

\[
 c=A(r_0,r_1),\qquad a=A(p_0,p_1).
 \tag{FCAP.6}
\]

## 2. Fixed-source capital theorem

### Theorem 2.1 — exact Hellinger capital inequality

If `(FCAP.4)` holds, then

\[
 \boxed{c\le a^d.}
 \tag{FCAP.7}
\]

When `0<a<1` and `0<c<=1`, every exact formation depth satisfies

\[
 \boxed{
 d\le {\log c\over\log a}.}
 \tag{FCAP.8}
\]

Equivalently, with extended Bhattacharyya capital

\[
 C_H(u,v)=
 \begin{cases}
  -\log A(u,v),&A(u,v)>0,\\
  +\infty,&A(u,v)=0,
 \end{cases}
 \tag{FCAP.9}
\]

one has

\[
 \boxed{C_H(r_0,r_1)\ge d\,C_H(p_0,p_1).}
 \tag{FCAP.10}
\]

### Proof

Affinity is monotone upward under every Markov kernel:

\[
 A(r_0K_d,r_1K_d)\ge A(r_0,r_1)=c.
 \tag{FCAP.11}
\]

Independent products multiply affinity, so `(FCAP.4)` gives

\[
 A(r_0K_d,r_1K_d)
 =A(p_0^{\otimes d},p_1^{\otimes d})=a^d.
 \tag{FCAP.12}
\]

This proves `(FCAP.7)`.  Taking logarithms gives `(FCAP.8)`--`(FCAP.10)`; division in
`(FCAP.8)` reverses the inequality because `log a<0`.  QED.

### Corollary 2.2 — KL and Jeffreys capital

Whenever the directed relative entropies are finite,

\[
 \boxed{
 D(r_0\Vert r_1)\ge dD(p_0\Vert p_1),
 \qquad
 J(r_0,r_1)\ge dJ(p_0,p_1),}
 \tag{FCAP.13}
\]

where `J(u,v)=D(u||v)+D(v||u)`.

### Proof

KL data processing gives

\[
 D(r_0\Vert r_1)\ge D(r_0K_d\Vert r_1K_d).
\]

Product additivity and `(FCAP.4)` identify the right side with `dD(p_0||p_1)`.  Reverse the
marks and add to obtain Jeffreys.  QED.

The Hellinger theorem remains nontrivial when one or both directed KL divergences are infinite.

### Theorem 2.3 — Rényi formation-capital spectrum

For `0<alpha<1`, define

\[
 Q_\alpha(u,v)=\sum_z u(z)^\alpha v(z)^{1-\alpha},
 \qquad
 C_\alpha(u,v)=
 \begin{cases}
  -\log Q_\alpha(u,v),&Q_\alpha(u,v)>0,\\
  +\infty,&Q_\alpha(u,v)=0.
 \end{cases}
 \tag{FCAP.13a}
\]

Every exact depth-`d` formation satisfies

\[
 \boxed{
 Q_\alpha(r_0,r_1)\le Q_\alpha(p_0,p_1)^d,
 \qquad
 C_\alpha(r_0,r_1)\ge dC_\alpha(p_0,p_1).}
 \tag{FCAP.13b}
\]

Thus a source carries not one capital number but the profile

\[
 \alpha\longmapsto C_\alpha(r_0,r_1).
 \tag{FCAP.13c}
\]

### Proof

For each output `y`, concavity of the weighted geometric mean on the positive cone gives

\[
 \left(\sum_xr_0(x)K(x,y)\right)^\alpha
 \left(\sum_xr_1(x)K(x,y)\right)^{1-\alpha}
 \ge
 \sum_xr_0(x)^\alpha r_1(x)^{1-\alpha}K(x,y).
\]

Summing in `y` and using the Markov row sums proves data processing
`Q_alpha(r_0K,r_1K)>=Q_alpha(r_0,r_1)`.  Direct factorization proves
`Q_alpha(p_0^tensor d,p_1^tensor d)=Q_alpha(p_0,p_1)^d`.  Apply `(FCAP.4)` and take negative
logarithms, using the extended convention `-log 0=+infinity`.  QED.

At `alpha=1/2`, this is Theorem 2.1.  The profile is still not a complete one-shot Blackwell
coordinate; Section 4 remains load-bearing.

## 3. Cofinal classification and approximate properness

### Theorem 3.1 — arbitrary-depth classification

The following are equivalent:

1. for every integer `d>=1`, some fixed-source formation `(FCAP.3)`--`(FCAP.4)` exists;
2. either

   \[
   \boxed{p_0=p_1}
   \tag{FCAP.14}
   \]

   or

   \[
   \boxed{r_0\perp r_1.}
   \tag{FCAP.15}
   \]

### Proof

If formations exist for every `d`, `(FCAP.7)` gives `c<=a^d` for every `d`.  If `a<1`, then
`a^d` tends to zero, so `c=0`.  On a finite set, `a=1` is equivalent to `p_0=p_1`, while `c=0`
is equivalent to disjoint supports, hence `r_0\perp r_1`.

Conversely, if `p_0=p_1`, ignore the input and prepare the common product packet.  If
`r_0\perp r_1`, choose disjoint full-support sets for the two source laws.  On the first set prepare
`p_0^{\otimes d}` and on the second prepare `p_1^{\otimes d}`.  Define the kernel arbitrarily
elsewhere.  It is one kernel and satisfies `(FCAP.4)`.  QED.

This differs from the earlier clone theorem: the source packets need not equal the target packets.
The theorem classifies whether an arbitrary fixed source experiment can finance unbounded target
depth.

### Theorem 3.2 — approximate fixed-source properness

For an arbitrary Markov kernel `K_d:S -> X^d`, put

\[
 R_i=r_iK_d,
 \qquad
 \varepsilon_i=h(R_i,p_i^{\otimes d}).
 \tag{FCAP.16}
\]

Then

\[
 \boxed{
 \varepsilon_0+\varepsilon_1
 \ge \sqrt{2-2a^d}-\sqrt{2-2c}.}
 \tag{FCAP.17}
\]

If `c>0` and `a<1`, the right side tends to

\[
 \sqrt2-\sqrt{2-2c}>0.
 \tag{FCAP.18}
\]

Thus no fixed overlapping source admits asymptotically exact nonneutral target formation at
unbounded depth.

### Proof

The Hellinger triangle inequality gives

\[
 h(p_0^{\otimes d},p_1^{\otimes d})
 \le \varepsilon_0+h(R_0,R_1)+\varepsilon_1.
 \tag{FCAP.19}
\]

Data processing gives `h(R_0,R_1)<=h(r_0,r_1)`.  Product affinity gives

\[
 h(p_0^{\otimes d},p_1^{\otimes d})=\sqrt{2-2a^d}.
\]

Substitute and rearrange.  QED.

## 4. One scalar is not a complete formation coordinate

The inequality `(FCAP.7)` is necessary, not sufficient at fixed depth.

Let the source packets on two points be

\[
 r_0=(9/10,1/10),\qquad r_1=(1/10,9/10).
 \tag{FCAP.20}
\]

Their likelihood ratio takes values `9` and `1/9`.  For every Markov image `(u_0,u_1)`, whenever
`u_1(y)>0`, the ratio `u_0(y)/u_1(y)` is a convex combination of `9` and `1/9`; hence it lies in
`[1/9,9]`.

Now take

\[
 p_0=(1/100,99/100),\qquad p_1=(1/1000,999/1000).
 \tag{FCAP.21}
\]

At the first target atom the likelihood ratio is `10`, so no common Markov map from `(FCAP.20)` to
`(FCAP.21)` exists.  Yet

\[
 A(r_0,r_1)=3/5,
 \]

while

\[
 A(p_0,p_1)
 \ge\sqrt{(99/100)(999/1000)}>3/5.
 \tag{FCAP.22}
\]

The last strict inequality follows after squaring from
`98901/100000 > 9/25`.  Thus Hellinger capital allows the conversion while the full likelihood-ratio
order forbids it.

The complete finite coordinate is the Blackwell/relative-majorization spectrum, equivalently all
convex functionals of the likelihood ratio.  No claim that one scalar controls every route is
permitted.  Hellinger remains sufficient for the cofinal theorem because every nonneutral tensor
affinity decays to zero.

## 5. Common recovery and functional equation are capital-neutral

Let `L:X -> X x H` be a split common recovery,

\[
 \widehat p_i(x,h)=p_i(x)\kappa(x,h),
 \tag{FCAP.23}
\]

retaining `x`.  Then direct summation gives

\[
 A(\widehat p_0,\widehat p_1)=A(p_0,p_1).
 \tag{FCAP.24}
\]

Projection recovers `p_i`, so every data-processing divergence is equal in both descriptions.  In
particular KL and Jeffreys capital are unchanged.

If `R:X->X` is a bijective involution, coordinatewise action satisfies

\[
 R_*^{\otimes d}(p_i^{\otimes d})=(R_*p_i)^{\otimes d}
 \tag{FCAP.25}
\]

and preserves affinity and every relabelling-invariant divergence.  The existing canonical packet
lift regenerates the same recovery kernel after applying `R`, so the action square commutes on
formed laws.  Consequently `(FCAP.7)`, `(FCAP.13)`, and `(FCAP.17)` are invariant under
functional-equation action.

This is information neutrality: symmetry transports the formation bill without paying it.

## 6. Sufficient macropackets attain the capital bound

Let `X` be finite, let `b:X->R_{>0}`, and let `T:X->R`.  Define the one-parameter exponential
family

\[
 p_\theta(x)={b(x)e^{\theta T(x)}\over Z(\theta)},
 \qquad
 Z(\theta)=\sum_xb(x)e^{\theta T(x)}.
 \tag{FCAP.26}
\]

For depth `d`, define the sum statistic

\[
 S_d(x_1,\ldots,x_d)=\sum_{j=1}^dT(x_j)
 \tag{FCAP.27}
\]

and its finite image `Y_d`.  Put

\[
 B_d(t)=\sum_{S_d(x)=t}\prod_{j=1}^db(x_j).
 \tag{FCAP.28}
\]

Every `B_d(t)` is positive by definition of `Y_d`.  Define the macro law and recovery kernel

\[
 m_{d,\theta}(t)={B_d(t)e^{\theta t}\over Z(\theta)^d},
 \tag{FCAP.29}
\]

\[
 \kappa_d(t,x)
 ={\mathbf1_{S_d(x)=t}\prod_jb(x_j)\over B_d(t)}.
 \tag{FCAP.30}
\]

### Theorem 6.1 — exact sufficient-macro formation

For every `d>=1` and every real `theta`:

1. `kappa_d` is a Markov kernel independent of `theta`;
2. the deterministic statistic sends the product packet to the macro:

   \[
   (S_d)_*p_\theta^{\otimes d}=m_{d,\theta};
   \tag{FCAP.31}
   \]

3. the common recovery reconstructs the independent product:

   \[
   m_{d,\theta}\kappa_d=p_\theta^{\otimes d};
   \tag{FCAP.32}
   \]

4. hence, for all `theta,phi`,

   \[
   \boxed{
   A(m_{d,\theta},m_{d,\phi})=A(p_\theta,p_\phi)^d,}
   \tag{FCAP.33}
   \]

   \[
   \boxed{
   D(m_{d,\theta}\Vert m_{d,\phi})
   =dD(p_\theta\Vert p_\phi),}
   \tag{FCAP.34}
   \]

   with the parallel Jeffreys identity;
5. the canonical-parameter Fisher information satisfies

   \[
   \boxed{I_{m_d}(\theta)=dI_p(\theta)=d\operatorname{Var}_{p_\theta}(T).}
   \tag{FCAP.35}
   \]

### Proof

Summing `(FCAP.30)` over the fibre gives one, proving item 1.  Multiplying product weights in
`(FCAP.26)` shows that every microstate in the fibre `S_d=t` has weight

\[
 {e^{\theta t}\prod_jb(x_j)\over Z(\theta)^d}.
\]

Summing over the fibre proves `(FCAP.31)`.  Multiplying `(FCAP.29)` by `(FCAP.30)` cancels
`B_d(t)` and gives the same product weight, proving `(FCAP.32)`.

The statistic and recovery are Markov maps in opposite directions.  Data processing applied in
both directions proves exact equality for affinity and KL; product multiplicativity/additivity gives
`(FCAP.33)`--`(FCAP.34)`.

Finally, the one-packet score is `T-E_theta T`.  The macro score is
`t-d E_theta T`.  Under the macro law, `t` is the sum of `d` independent copies of `T`; its variance
is therefore `d Var_theta(T)`.  This is `(FCAP.35)`.  QED.

The same two-way data processing proves

\[
 C_\alpha(m_{d,\theta},m_{d,\phi})
 =dC_\alpha(p_\theta,p_\phi)
 \qquad(0<\alpha<1).
 \tag{FCAP.35a}
\]

Equations `(FCAP.33)`--`(FCAP.35a)` are the fusion identity: positive/Hellinger, Rényi spectrum,
entropy/KL, and moment/Fisher organs measure one conserved formation capital in different grades.

## 7. Functional-equation equivariance of sufficient formation

Assume additionally that `R:X->X` is an involution satisfying

\[
 b(Rx)=b(x),\qquad T(Rx)=-T(x).
 \tag{FCAP.36}
\]

Let `R^d` act coordinatewise and let `J:Y_d->Y_d` be `J(t)=-t`.

### Theorem 7.1 — commuting functional-equation formation square

One has

\[
 R_*p_\theta=p_{-\theta},
 \qquad
 J_*m_{d,\theta}=m_{d,-\theta},
 \tag{FCAP.37}
\]

and the recovery kernel is equivariant:

\[
 (R^d)_*\kappa_d(t,\cdot)=\kappa_d(-t,\cdot).
 \tag{FCAP.38}
\]

Consequently the diagram

\[
\begin{array}{ccc}
 m_{d,\theta}&\xrightarrow{\ \kappa_d\ }&p_\theta^{\otimes d}\\
 \downarrow J_*&&\downarrow (R^d)_*\\
 m_{d,-\theta}&\xrightarrow{\ \kappa_d\ }&p_{-\theta}^{\otimes d}
\end{array}
 \tag{FCAP.39}
\]

commutes, and every information identity `(FCAP.33)`--`(FCAP.35)` is unchanged.

### Proof

The change of variables `x->Rx` gives `Z(theta)=Z(-theta)`, hence the first identity in
`(FCAP.37)`.  Coordinatewise `R^d` is a bijection from the fibre `S_d=t` to the fibre
`S_d=-t` and preserves `prod b(x_j)`.  Therefore `B_d(t)=B_d(-t)`, proving the second identity and
`(FCAP.38)`.  Equation `(FCAP.39)` follows.  QED.

This is the functional-equation action on packet formation.  Its lift through common recovery is
information-neutral because it is an automorphism of an already sufficient experiment.

## 8. Fourth-organ theorem: theta formation without infinite divisibility

Let `P_B` be the corpus's normalized theta cusp likelihood on `R`, for `B>0`.  The formal corpus
proves:

1. `P_B` is a probability law;
2. relative to any fixed `B_0>0`,

   \[
   {dP_B\over dP_{B_0}}(t)
   ={Z(B_0)\over Z(B)}e^{-(B-B_0)t};
   \tag{FCAP.40}
   \]

3. `P_B` is not infinitely divisible because it charges the gap atom `3`, does not charge `6`,
   while its square convolution charges `6`.

For `d>=1`, let

\[
 \Sigma_d(t_1,\ldots,t_d)=\sum_jt_j,
 \qquad
 M_{d,B}=(\Sigma_d)_*P_B^{\otimes d}=P_B^{*d}.
 \tag{FCAP.41}
\]

### Theorem 8.1 — theta sufficient-macro formation and species exit

For each `d` and each baseline `B_0>0`, there is one standard-Borel Markov kernel

\[
 \kappa_d:\mathbb R\rightsquigarrow\mathbb R^d
 \tag{FCAP.42}
\]

independent of `B`, such that for every `B>0`,

\[
 \boxed{M_{d,B}\kappa_d=P_B^{\otimes d},
 \qquad
 (\Sigma_d)_*P_B^{\otimes d}=M_{d,B}.}
 \tag{FCAP.43}
\]

Therefore

\[
 \boxed{
 D(M_{d,B}\Vert M_{d,C})=dD(P_B\Vert P_C),
 \qquad
 A(M_{d,B},M_{d,C})=A(P_B,P_C)^d.}
 \tag{FCAP.44}
\]

For `d=2`, `M_{2,B}` has a nonzero atom at `6`, although `P_B` has no atom there.  Hence exact
sufficient formation exists, but the macro law necessarily exits the original one-particle theta
**atomic-support** species.  This separates formation from infinite divisibility unconditionally.

### Proof

Because `R` and `R^d` are standard Borel, disintegrate the baseline product
`P_{B_0}^{\otimes d}` along `Sigma_d`.  This gives a regular conditional kernel `kappa_d`, concentrated
on the fibre `Sigma_d=t`, with

\[
 P_{B_0}^{\otimes d}=M_{d,B_0}\kappa_d.
 \tag{FCAP.45}
\]

Tensoring `(FCAP.40)` gives

\[
 {dP_B^{\otimes d}\over dP_{B_0}^{\otimes d}}(t_1,\ldots,t_d)
 =\left({Z(B_0)\over Z(B)}\right)^d
 e^{-(B-B_0)\Sigma_d(t_1,\ldots,t_d)}.
 \tag{FCAP.46}
\]

The density depends only on `Sigma_d`.  Weight `(FCAP.45)` by this fibre-constant density.
Its pushforward weights `M_{d,B_0}` by the same function, producing `M_{d,B}`; its conditional
kernel remains `kappa_d`.  This proves `(FCAP.43)`.  Data processing in both directions and product
laws prove `(FCAP.44)`.

The corpus theorem
`thetaCuspLikelihoodProbabilityMeasure_selfConv_singleton_six_ne_zero` proves the atom at `6`, while
`thetaCuspLikelihoodProbabilityMeasure_singleton_six` proves its absence from `P_B`.  Therefore the
formed macro cannot remain in the original support species.  QED.

### Exact interpretation

Infinite divisibility would ask for a one-particle law to be decomposed into independent roots while
staying compatible with additive convolution at every scale.  Theorem 8.1 instead starts with the
depth-`d` macro `M_{d,B}`.  Its capital is already `d` times the one-packet capital, and sufficient
recovery spends exactly that amount to reconstruct `d` descendants.  No cloning paradox occurs.

## 9. Four structurally different exact specializations

The finite theorem has the following literal instances.

1. **Boolean/Bernoulli.**  The macro is `Binomial(d,p)`; conditional on count `k`, recovery is
   uniform on bitstrings of Hamming weight `k`.  Reflection `p<->1-p` acts by `k<->d-k`.
2. **Poisson.**  The macro is `Pois(d lambda)`; conditional recovery is multinomial allocation with
   equal cell probabilities.
3. **Hasse/geometric.**  The macro is negative binomial; conditional recovery is uniform on weak
   compositions of the total generation count.
4. **Theta cusp.**  The macro is `P_B^{*d}`; conditional recovery is the baseline conditional law
   on a fixed total gap.  It creates support atoms absent from the one-particle species.

These are not claims that the four endpoint formulas are identical.  They are four realizations of
one formation/recovery conservation law.

## 10. Selection corollary and exact remaining gate

Let `(p_a)_{a in I}` be an identifiable reflected family with common support,

\[
 R_*p_a=p_{-a},
 \qquad
 p_a=p_{-a}\iff a=0.
 \tag{FCAP.47}
\]

Let `(r_a,r_{-a})` be a fixed source experiment with positive overlap.  If this one source forms
arbitrarily large independent depths of `(p_a,p_{-a})`, Theorem 3.1 forces

\[
 \boxed{a=0.}
 \tag{FCAP.48}
\]

For an RH receiver, `(FCAP.48)` would be a selector.  The missing arithmetic theorem is exact and
not hidden by geometry:

> Construct from the literal pre-zero source a fixed overlapping experiment and source-natural
> formations of unbounded independent depth for the reflected physical packets.

The sufficient-macro theorem shows how such depth can be financed: the source macro itself must
carry linearly growing capital.  A fixed finite-capital source cannot do so.  Therefore any live RH
producer must exhibit an unbounded source reservoir, a singular source mark, or a neutral physical
packet.  Declaring the product packet by hand is circular.

## 11. Hostile boundaries

1. The Hellinger bound is not a complete finite conversion criterion; Section 4 is a counterexample.
2. A parameter-dependent kernel can ignore the source and prepare the requested target; commonness
   is load-bearing.
3. Fresh random coins are allowed and do not evade the hidden-mark capital bound.
4. Sufficient macro laws vary with depth.  They do not contradict the fixed-source theorem.
5. Infinite divisibility concerns same-species additive roots, not arbitrary sufficient recovery.
6. Functional equation is capital-neutral and supplies no formation budget.
7. Fisher information clause `(FCAP.35)` is for the regular canonical parameter of the finite
   exponential family; no infinite-dimensional Fisher claim is made.
8. Standard-Borel disintegration proves the theta kernel up to the usual almost-everywhere choice;
   no canonical pointwise conditional law is claimed.
9. The theorem gives a typed RH gate, not the required rational-adelic source formation.

## 12. Parent audit and corpus delta

Blackwell comparison, f-divergence monotonicity, Fisher--Neyman sufficiency, Chentsov geometry,
probabilistic no-cloning, generalized data thinning, and distinguishability resource theories are
established mathematics.  Relevant primary sources are:

- <https://arxiv.org/abs/1908.07021>
- <https://arxiv.org/abs/2303.12931>
- <https://arxiv.org/abs/2301.07276>
- <https://arxiv.org/abs/1701.08895>
- <https://arxiv.org/abs/quant-ph/0611295>
- <https://arxiv.org/abs/1905.11629>
- <https://arxiv.org/abs/2102.12512>

The generic fixed-source capital theorem is a classical/quantum resource-theory bridge and is not
claimed as external novelty.  The unconditional corpus delta is the combined source-specific
theorem:

- arbitrary fixed-source rather than self-cloning capital;
- cofinal neutral/singular classification;
- quantitative approximate properness;
- exact simultaneous Hellinger/KL/Fisher saturation by sufficient macros;
- functional-equation equivariance of that saturation;
- and theta cusp formation despite formally certified nondivisibility, with species exit witnessed
  by the new convolution atom.

## 13. Formalization gate

The paper theorem is dependency-closed.  Under current research-mode instructions, Lean was audited
but no Lean file was written or built in this pass.  The finite target module should formalize:

1. arbitrary-source affinity capital `A(source)<=A(target)^d`;
2. the Rényi capital spectrum;
3. arbitrary-depth neutral/singular classification;
4. the explicit likelihood-ratio counterexample;
5. finite exponential sufficient recovery and information conservation;
6. finite functional-equation equivariance.

Lean audit found the required existing infrastructure in
`Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean`: `Measure.condKernel`, its Markov
instance, and `Measure.compProd_fst_condKernel`.  The theta proof will additionally need a measurable
coordinate change from `R^d` to `(sum, fibre coordinate)` and transport of the baseline conditional
kernel under the fibre-constant exponential tilt.  No Lean file was written or built in this pass,
and no new axiom or placeholder is permitted.

## Log

- 2026-08-13 — fixed-source capital theorem, sufficient-macro saturation, functional-equation
  equivariance, and theta species-exit corollary proved on paper after broad corpus/literature audit.
