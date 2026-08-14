# Finite split-recovery index reconstruction, Rényi conservation, and cofinal no-go

- **ID:** ULF-RITM-2
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / POSITIVE SURVIVOR / FIELD-CORE NO-GO
- **Source programme:**
  `../../../1-in-progress/universal-law-field/recovery-index-tower-mechanics/field-programme.md`
- **Packet parent:**
  `../packet-formation-mechanics/functional-equation-split-formation-lift-information-isometry-and-work-no-go.md`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [FINITE COMMUTATIVE]`
  `[FULL INDEX PROFILE RECONSTRUCTION] [RÉNYI EQUATION OF STATE]`
  `[STRICT TENSOR LAW] [COFINAL BOUNDED-INDEX NO-GO] [BRIDGE]`
  `[FIELD CORE REJECTED] [LEAN PENDING] [NOT RH]`

## 1. Purpose

Common recovery is exactly information-neutral on observer laws.  The tempting higher claim was
that iterating such a recovery might nevertheless generate a Jones/Watatani standard invariant
capable of coupling formation, entropy, reflection, and properness.

The finite commutative model gives the strongest exact answer.  A recovery kernel does carry a
complete operator-algebraic index profile, and that profile obeys a full Rényi conservation law.
But the profile is independent of every horizontal observer law: it may be chosen freely subject
only to row normalization.  Therefore common recovery plus finite index is not a field producer.

## 2. Finite split recovery as a conditional expectation

Let `X` and `H` be finite nonempty sets and put `d=|H|`.  Let

\[
 \kappa_x(h)>0,
 \qquad
 \sum_{h\in H}\kappa_x(h)=1
 \tag{RIT.1}
\]

for every `x`.  Define the commutative unital algebras

\[
 A=\mathbb C^X,
 \qquad
 B=\mathbb C^{X\times H},
 \tag{RIT.2}
\]

the inclusion

\[
 \iota(a)(x,h)=a(x),
 \tag{RIT.3}
\]

and the conditional expectation

\[
 E_\kappa(f)(x)=\sum_{h\in H}\kappa_x(h)f(x,h).
 \tag{RIT.4}
\]

It is unital, positive, faithful, and `A`-bimodular.  Faithfulness follows because every
`\kappa_x(h)` is strictly positive.

For `h\in H`, define

\[
 u_h(x,k)=\frac{\mathbf 1_{h=k}}{\sqrt{\kappa_x(h)}}.
 \tag{RIT.5}
\]

### Theorem 2.1 — quasi-basis and complete index reconstruction

The family `((u_h,u_h^*))_{h\in H}` is a Watatani quasi-basis:

\[
 \sum_{h\in H}u_h\,\iota(E_\kappa(u_h^*f))=f
 =\sum_{h\in H}\iota(E_\kappa(fu_h))u_h^*.
 \tag{RIT.6}
\]

Its index element is the pointwise profile

\[
 \boxed{
 \operatorname{Ind}(E_\kappa)(x,h)
 =\sum_{k\in H}|u_k(x,h)|^2
 =\frac1{\kappa_x(h)}.}
 \tag{RIT.7}
\]

Consequently the full index profile reconstructs the recovery kernel coefficient by coefficient:

\[
 \boxed{\kappa_x(h)=\operatorname{Ind}(E_\kappa)(x,h)^{-1}.}
 \tag{RIT.8}
\]

Conversely, a positive function `J:X\times H\to\mathbb R_{>0}` is the full index profile of a
strictly positive split recovery exactly when

\[
 \boxed{\sum_{h\in H}J(x,h)^{-1}=1\quad(x\in X).}
 \tag{RIT.9}
\]

### Proof

At `(x,k)`, only the summand `h=k` in the first expression of `(RIT.6)` survives, and

\[
 E_\kappa(u_k^*f)(x)
 =\kappa_x(k)\frac{f(x,k)}{\sqrt{\kappa_x(k)}}
 =\sqrt{\kappa_x(k)}f(x,k).
\]

Multiplication by `u_k(x,k)=\kappa_x(k)^{-1/2}` returns `f(x,k)`.  Commutativity gives the second
identity.  Equation `(RIT.7)` is immediate from the disjoint supports of the `u_k`; `(RIT.8)`
follows by inversion.  For the converse set `\kappa_x(h)=J(x,h)^{-1}`.  Equation `(RIT.9)` makes
every row stochastic, and the preceding construction returns `J`.  QED.

## 3. Exact Pimsner--Popa scalar

Define

\[
 K_\kappa=\max_{x\in X,\,h\in H}\frac1{\kappa_x(h)}.
 \tag{RIT.10}
\]

### Theorem 3.1 — least positivity constant

`K_\kappa` is exactly the least `K` such that

\[
 K\,\iota(E_\kappa(f))-f\ge0
 \qquad(f\in B_+).
 \tag{RIT.11}
\]

Moreover,

\[
 \boxed{K_\kappa\ge d,}
 \tag{RIT.12}
\]

with equality if and only if every row of `\kappa` is uniform.

### Proof

At `(x,h)`, the left side of `(RIT.11)` equals

\[
 (K\kappa_x(h)-1)f(x,h)
 +K\sum_{k\ne h}\kappa_x(k)f(x,k).
 \tag{RIT.13}
\]

It is nonnegative for every positive `f` when `K\ge1/\kappa_x(h)` for all `(x,h)`.  Conversely,
testing the point mass at `(x,h)` forces that inequality.  This proves minimality.  Every
probability row has an entry at most `1/d`, proving `(RIT.12)`.  If `K_\kappa=d`, every entry is at
least `1/d`; their sum is one, so all equal `1/d`.  The converse is immediate.  QED.

## 4. Full Rényi index equation of state

Fix `x` and write `q(h)=\kappa_x(h)`, `I(h)=q(h)^{-1}`, and `u(h)=1/d`.  For `\alpha>0`,
`\alpha\ne1`, define

\[
 H_\alpha(q)=\frac1{1-\alpha}\log\sum_hq(h)^\alpha,
 \tag{RIT.14}
\]

\[
 D_\alpha(q\Vert u)
 =\frac1{\alpha-1}
 \log\sum_hq(h)^\alpha u(h)^{1-\alpha}.
 \tag{RIT.15}
\]

### Theorem 4.1 — index/Rényi conservation

For every such `\alpha`, one has

\[
 \boxed{
 H_\alpha(q)
 =\frac1{1-\alpha}\log\mathbb E_q[I^{1-\alpha}],}
 \tag{RIT.16}
\]

and

\[
 \boxed{D_\alpha(q\Vert u)+H_\alpha(q)=\log d.}
 \tag{RIT.17}
\]

At Shannon order the exact limiting identity is obtained directly:

\[
 \boxed{
 D(q\Vert u)+\mathbb E_q[\log I]=\log d.}
 \tag{RIT.18}
\]

Thus the full moment spectrum of the index profile is the Rényi entropy spectrum of latent
formation, while divergence from uniform is its complementary budget.

### Proof

By `I(h)=q(h)^{-1}`,

\[
 \mathbb E_q[I^{1-\alpha}]
 =\sum_hq(h)q(h)^{\alpha-1}
 =\sum_hq(h)^\alpha,
\]

which proves `(RIT.16)`.  Since `u(h)=1/d`,

\[
 D_\alpha(q\Vert u)
 =\frac1{\alpha-1}\log
 \left(d^{\alpha-1}\sum_hq(h)^\alpha\right)
 =\log d-H_\alpha(q).
\]

This is `(RIT.17)`.  Finally,

\[
 D(q\Vert u)=\sum_hq(h)\log(dq(h))
 =\log d+\sum_hq(h)\log q(h),
\]

while `\mathbb E_q\log I=-\sum_hq(h)\log q(h)`.  QED.

## 5. Iterated formation and strict tensor law

At depth `n`, put

\[
 \kappa_x^{(n)}(h_1,\ldots,h_n)=\prod_{j=1}^n\kappa_x(h_j).
 \tag{RIT.19}
\]

The product quasi-basis gives

\[
 \boxed{
 I_n(x,h_1,\ldots,h_n)
 =\prod_{j=1}^n\frac1{\kappa_x(h_j)},}
 \tag{RIT.20}
\]

and therefore

\[
 \boxed{K_n=K_\kappa^n.}
 \tag{RIT.21}
\]

Indeed the upper bound follows factorwise, while equality is attained by choosing an `x,h`
realizing `(RIT.10)` and repeating that `h` in every slot.

Let `\mu` be a probability law on `X`.  Define the formed packet and its uniform latent reference

\[
 P_{\mu,n}(x,\mathbf h)
 =\mu(x)\kappa_x^{(n)}(\mathbf h),
 \qquad
 U_{\mu,n}(x,\mathbf h)=\mu(x)d^{-n}.
 \tag{RIT.22}
\]

### Theorem 5.1 — global formation equation of state

One has

\[
 \boxed{
 D(P_{\mu,n}\Vert U_{\mu,n})
 +\mathbb E_{P_{\mu,n}}[\log I_n]
 =n\log d.}
 \tag{RIT.23}
\]

More explicitly, if

\[
 \overline H_\mu(\kappa)
 =\sum_x\mu(x)\left(-\sum_h\kappa_x(h)\log\kappa_x(h)\right),
 \tag{RIT.24}
\]

then the two summands in `(RIT.23)` are respectively

\[
 n(\log d-\overline H_\mu(\kappa)),
 \qquad
 n\overline H_\mu(\kappa).
 \tag{RIT.25}
\]

### Proof

The likelihood ratio in `(RIT.22)` is

\[
 \frac{P_{\mu,n}}{U_{\mu,n}}
 =d^n\prod_j\kappa_x(h_j)
\]

on every atom with `\mu(x)>0`.  Taking its logarithm and expectation gives the first expression in
`(RIT.25)`.  Equation `(RIT.20)` gives the second.  Their sum is `(RIT.23)`.  QED.

## 6. Horizontal information neutrality and vertical independence

For two observer laws `\mu,\nu`, common recovery gives

\[
 \boxed{
 D(P_{\mu,n}\Vert P_{\nu,n})=D(\mu\Vert\nu),}
 \tag{RIT.26}
\]

including extended value `+\infty`.  Projection to `X` is an exact left inverse, so data
processing gives both inequalities.

Equations `(RIT.9)` and `(RIT.26)` prove the decisive independence theorem:

> Keeping the entire observer experiment fixed, the vertical index profile may be replaced by any
> positive `J` satisfying `\sum_hJ(x,h)^{-1}=1`, without changing a single pairwise horizontal KL
> divergence.

Thus the horizontal experiment does not determine the vertical standard invariant.  Treating them
as coordinates of one field without an additional source law reproduces the corpus's independent-
slot nonprediction failure.

## 7. Functional-equation action

Let `R:X\to X` be a measurable bijection.  Its reset lift sends `(x,\mathbf h)` to `R(x)` and
regenerates a fresh history from `\kappa_{R(x)}^{(n)}`.  It maps

\[
 P_{\mu,n}\longmapsto P_{R_*\mu,n}.
 \tag{RIT.27}
\]

It preserves `(RIT.26)`, permutes the rows of the full index profile, and leaves `K_n` unchanged.
The sum in `(RIT.23)` is always `n\log d`.  If in addition the kernel is equivariant under `R`
(possibly after a latent-coordinate permutation), both summands in `(RIT.23)` are individually
invariant.  If `R` is involutive, the lifted action is involutive on formed laws.

## 8. Cofinal bounded-index classification

### Theorem 8.1 — no nontrivial uniformly bounded recovery tower

For a strictly positive finite split recovery,

\[
 \boxed{
 \sup_{n\ge1}K_n<\infty
 \quad\Longleftrightarrow\quad
 d=1.}
 \tag{RIT.28}
\]

If `d>1`, then

\[
 K_n\ge d^n,
 \qquad
 \log K_n=n\log K_\kappa\longrightarrow\infty.
 \tag{RIT.29}
\]

### Proof

Equations `(RIT.12)` and `(RIT.21)` give `K_n\ge d^n`.  Hence boundedness forces `d=1`.  For
`d=1`, the unique kernel is `1`, so every `K_n=1`.  QED.

This is a genuine properness theorem, but it selects only trivial hidden formation.  It has no
critical-line content.

## 9. Hostile verdict

### Failed conjecture

> Common recovery, Jones basic construction, reflection, and entropy form the missing universal
> field producer.

**False as a field claim.**

1. Finite-index conditional expectations, basic constructions, index elements, and their entropy
   relations are established operator-algebraic machinery.
2. Current work already couples higher reflection operators, canonical shifts, entropy, and minimal
   Watatani index.
3. Internally, formation-resource mechanics already proves common-recovery capital neutrality.
4. Most decisively, `(RIT.9)` and `(RIT.26)` show that vertical index data are independent of the
   horizontal observer experiment.

### Positive survivor

The finite commutative theorem contributes one exact calibration:

\[
 \text{full recovery profile}
 \Longleftrightarrow
 \text{full index profile},
 \qquad
 \text{Rényi entropy}+
 \text{uniformity deficit}=\log d,
\]

with strict tensor composition and cofinal index escape.  This is useful as an anti-theatre gate,
not as a universal field.

## 10. Parent boundary

Relevant parent theories include:

- Frank--Kirchberg, [On conditional expectations of finite index](https://arxiv.org/abs/math/9804074);
- Kajiwara--Pinzari--Watatani,
  [Jones index theory for Hilbert C*-bimodules](https://arxiv.org/abs/math/0301259);
- Gao--Junge--LaRacuente,
  [Relative entropy for von Neumann subalgebras](https://arxiv.org/abs/1909.01906);
- Zhao, [Relative Entropy for Quantum Channels](https://arxiv.org/abs/2312.16576);
- Bakshi--Guin--Pal--Sruthymurali,
  [Higher reflections and entropy of canonical shifts for inclusions of C*-algebras with finite
  Watatani index](https://arxiv.org/abs/2506.16130).

No priority claim is made for index/entropy ingredients.  The corpus-specific contribution is the
exact comparison with split packet formation and the resulting independence/no-selection gate.

## 11. Lean boundary

This card is dependency-closed on paper.  No Lean file was written or built during this research
pass, in accordance with the read-only Lean audit instruction.  Formalization remains pending.

