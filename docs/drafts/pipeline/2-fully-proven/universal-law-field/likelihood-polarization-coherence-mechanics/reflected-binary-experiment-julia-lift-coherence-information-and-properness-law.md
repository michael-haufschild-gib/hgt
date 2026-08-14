# Reflected binary experiment, Julia lift coherence, information, and properness

- **ID:** ULF-LPCM-1
- **Stage:** 2 — fully proven on paper
- **Type:** SOURCE-GENERATED POLARIZATION / LIFT-COMPARISON / INFORMATION-CONSERVATION THEOREM
- **Source:** functional-equation split packet formation, Constitutive Dilation Mechanics, and
  Constitutive Reflection-Space Mechanics
- **Statement:** Every equivalent reflected pair of probability laws canonically generates a
  posterior-contrast Julia dilation.  Sign-blind and polarized functional-equation lifts differ by
  exactly twice the hidden contrast; their squared disagreement is twice triangular
  discrimination, is bounded above by Jeffreys information, survives every common recovery
  kernel, has an exact rapidity fusion law, and is stably selective exactly at a likelihood-gap
  boundary.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL CORE]`
  `[THREE-ORGAN BRIDGE] [FOURTH-ORGAN FISHER PREDICTION VERIFIED]`
  `[QUOTIENT PROPERNESS CLASSIFIED] [COMMON-RECOVERY NEUTRAL]`
  `[SIGN-BLIND SOURCE LIFT NOT YET TYPED]`
  `[CLASSICAL COMPONENTS / NEW CORPUS COUPLING] [LEAN NOT YET WRITTEN] [NOT RH]`

## 1. Why a different mechanism is needed

The functional-equation packet theorem gives a sign-blind stochastic lift through every common
recovery kernel.  Constitutive Dilation Mechanics gives a positive visible channel and its forced
Julia defect.  Constitutive Reflection-Space Mechanics says that several properly positioned
reversals can select a common fixed state.  Those results still leave a possible theatre move:
choose the second polarization or reversal independently.

A reflected binary statistical experiment removes that freedom.  Its likelihood ratio itself
generates both coordinates

\[
 d=\tanh\chi,
 \qquad
 a=\operatorname{sech}\chi,
 \qquad
 a^2+d^2=1.
 \tag{LPC.1}
\]

Here `d` is the signed posterior contrast and `a` is the positive Hellinger visibility.  Thus the
same source pair generates:

1. a functional-equation involution;
2. a positive/hidden Julia split;
3. a likelihood-information packet;
4. a sharp comparison between two possible lifts.

The comparison, not either lift alone, is the new mechanism.

## 2. Canonical likelihood polarization

Let `(X,Sigma)` be a measurable space and let `P,Q` be mutually absolutely continuous probability
measures.  Put

\[
 \eta=\frac{P+Q}{2},
 \qquad
 p=\frac{dP}{d\eta},
 \qquad
 q=\frac{dQ}{d\eta}.
 \tag{LPC.2}
\]

Then `p+q=2` almost everywhere and mutual absolute continuity gives `p,q>0` almost everywhere.
Define

\[
 d=\frac{p-q}{2},
 \qquad
 \chi=\frac12\log\frac pq,
 \qquad
 a=\sqrt{1-d^2}.
 \tag{LPC.3}
\]

Since `p=1+d` and `q=1-d`, one has `|d|<1` and

\[
 \boxed{d=\tanh\chi,\qquad a=\operatorname{sech}\chi.}
 \tag{LPC.4}
\]

Let `H=L^2(eta;C)`.  Write `A=M_a` and `D=M_d` for the multiplication operators and define

\[
 C:H\longrightarrow H\oplus H,
 \qquad Cf=(Af,Df),
 \tag{LPC.5}
\]

\[
 Q_0:H\oplus H\longrightarrow H,
 \qquad Q_0(u,v)=Au+Dv,
 \tag{LPC.6}
\]

and the Julia reflection

\[
 \mathcal J=
 \begin{pmatrix}A&D\\D&-A\end{pmatrix}.
 \tag{LPC.7}
\]

### Theorem 2.1 — likelihood-generated Julia cycle

The likelihood pair alone determines `A,D,C,Q_0,J`, and

\[
 \boxed{
 A^2+D^2=I,
 \quad \|Cf\|=\|f\|,
 \quad \|Q_0\|=1,
 \quad Q_0C=I,
 \quad \mathcal J^*=\mathcal J,
 \quad \mathcal J^2=I,
 \quad \mathcal J(f,0)=Cf.}
 \tag{LPC.8}
\]

Thus neither positive visibility nor hidden defect is an independently selected channel.

#### Proof

Equation `(LPC.4)` gives `a^2+d^2=1` pointwise.  Therefore

\[
 \|Cf\|^2
 =\int_X(a^2+d^2)|f|^2\,d\eta
 =\|f\|^2.
\]

Cauchy--Schwarz in each two-dimensional fibre gives `||Q_0||<=1`, while `Q_0C=I` forces equality.
The fibre matrix

\[
 \begin{pmatrix}a&d\\d&-a\end{pmatrix}
\]

is self-adjoint and its square is the identity.  All assertions follow.  QED.

## 3. Reflection and the two lifts

Assume now that `R:X->X` is a measurable involution and

\[
 Q=R_*P.
 \tag{LPC.9}
\]

Then `R_*eta=eta`.  Let

\[
 (Uf)(x)=f(Rx).
 \tag{LPC.10}
\]

The Koopman operator `U` is a unitary involution.  Since reflection exchanges `p` and `q`,

\[
 d\circ R=-d,
 \qquad
 a\circ R=a.
 \tag{LPC.11}
\]

Equivalently,

\[
 UA=AU,
 \qquad
 UD=-DU.
 \tag{LPC.12}
\]

Once the likelihood Julia double has been formed, there are two algebraically canonical extensions
of `U` to that declared two-channel space:

\[
 F_+=U\oplus U,
 \qquad
 F_-=U\oplus(-U).
 \tag{LPC.13}
\]

`F_+` is sign-blind: it applies the same observer action to both channels.  `F_-` is the
likelihood-polarized lift: it remembers that the hidden contrast is reflection odd.  Only `F_-` is
forced to intertwine the likelihood-generated split.  The common Markov-recovery lift lives on a
different observer-history space; no identification of that space with this Julia double is assumed
or proved.  Thus `F_+` is an exact comparison doctrine, not yet a second source-derived realization.

### Theorem 3.1 — exact lift-coherence defect

Both `F_+` and `F_-` are unitary involutions.  The polarized lift is exactly compatible with the
source-generated split:

\[
 \boxed{F_-C=CU.}
 \tag{LPC.14}
\]

The sign-blind lift differs by

\[
 \boxed{
 (F_+C-CU)f=(F_+C-F_-C)f=(0,-2DUf).}
 \tag{LPC.15}
\]

Consequently its exact coherence energy is

\[
 \boxed{
 \mathcal E_{P,Q}(f)
 :=\|F_+Cf-F_-Cf\|^2
 =4\|Df\|^2
 =4\int_Xd^2|f|^2\,d\eta.}
 \tag{LPC.16}
\]

Moreover

\[
 F_-\mathcal J=\mathcal JF_-,
 \tag{LPC.17}
\]

whereas conjugation by `F_+` changes `D` to `-D`.  Thus polarized reflection preserves the Julia
law; sign-blind reflection exchanges its two oriented likelihood polarizations.

#### Proof

The first coordinate of `F_-Cf` is

\[
 UAf=AUf.
\]

The second is

\[
 -UDf=DUf.
\]

This proves `(LPC.14)`.  Replacing `-U` by `U` changes the second coordinate from `DUf` to
`-DUf`, proving `(LPC.15)` and `(LPC.16)`.  The matrix calculation for `(LPC.17)` uses exactly
`UA=AU` and `UD=-DU`.  QED.

### Corollary 3.2 — state-level coherence selection

For every `f in H`,

\[
 F_+Cf=F_-Cf
 \quad\Longleftrightarrow\quad
 df=0\quad\eta\text{-a.e.}
 \tag{LPC.18}
\]

If `f` is nonzero almost everywhere, then

\[
 \boxed{F_+Cf=F_-Cf\quad\Longleftrightarrow\quad P=Q.}
 \tag{LPC.19}
\]

In particular the canonical faithful vector `1` is selected exactly at reflection invariance.

This is a conditional selection interface, not an assertion that a physical source already
identifies the two lifts.  It says precisely what such source coherence would force.

## 4. The coherence energy is classical information in a new role

Use the convention

\[
 H^2(P,Q)=\int(\sqrt p-\sqrt q)^2\,d\eta
 \tag{LPC.20}
\]

for squared Hellinger distance and

\[
 \Delta(P,Q)=\int\frac{(p-q)^2}{p+q}\,d\eta
 \tag{LPC.21}
\]

for triangular discrimination.  Let

\[
 J(P,Q)=D_{KL}(P\Vert Q)+D_{KL}(Q\Vert P)
 \tag{LPC.22}
\]

be Jeffreys information, possibly infinite.

### Theorem 4.1 — information hierarchy and common zero locus

For the canonical vector `1`,

\[
 \boxed{
 \mathcal E_{P,Q}(1)=2\Delta(P,Q).}
 \tag{LPC.23}
\]

More precisely,

\[
 \boxed{
 2H^2(P,Q)
 \le \mathcal E_{P,Q}(1)
 \le 4H^2(P,Q),}
 \tag{LPC.24}
\]

and

\[
 \boxed{
 \mathcal E_{P,Q}(1)
 \le J(P,Q).}
 \tag{LPC.25}
\]

All four quantities vanish exactly when `P=Q`.

#### Proof

Since `p=1+d`, `q=1-d`, and `p+q=2`,

\[
 \Delta(P,Q)=\int\frac{(2d)^2}{2}\,d\eta
 =2\int d^2\,d\eta,
\]

which proves `(LPC.23)`.  Also `sqrt(pq)=sqrt(1-d^2)=a`, so

\[
 H^2(P,Q)=2\int(1-a)\,d\eta.
\]

But

\[
 \mathcal E_{P,Q}(1)
 =4\int(1-a^2)\,d\eta
 =4\int(1-a)(1+a)\,d\eta.
\]

Because `1<=1+a<=2`, inequality `(LPC.24)` follows.  Finally,

\[
 J(P,Q)
 =\int(p-q)\log\frac pq\,d\eta
 =4\int d\,\operatorname{artanh}(d)\,d\eta.
\]

For `|d|<1`, `d artanh(d)>=d^2`, proving `(LPC.25)`.  Equality of any zero locus with `P=Q`
follows from `d=0` almost everywhere.  QED.

The divergences and their inequalities are classical.  The new-to-corpus fact is that triangular
discrimination is exactly the work needed to compare the sign-blind and likelihood-polarized
functional-equation lifts of the source-generated Julia split.

## 5. Common recovery is exactly neutral

Let `K` be a Markov kernel from `X` to another measurable space `Y`.  Form

\[
 P_K(dx,dy)=P(dx)K(x,dy),
 \qquad
 Q_K(dx,dy)=Q(dx)K(x,dy),
 \tag{LPC.26}
\]

and `eta_K=eta tensor K`.

### Theorem 5.1 — common-recovery lift neutrality

Relative to `eta_K`, the densities of `P_K,Q_K` are `p(x),q(x)`.  Hence their contrast,
visibility, and rapidity are

\[
 d_K(x,y)=d(x),
 \qquad
 a_K(x,y)=a(x),
 \qquad
 \chi_K(x,y)=\chi(x).
 \tag{LPC.27}
\]

Consequently

\[
 \boxed{
 \mathcal E_{P_K,Q_K}(1)=\mathcal E_{P,Q}(1),
 \quad
 H^2(P_K,Q_K)=H^2(P,Q),
 \quad
 \Delta(P_K,Q_K)=\Delta(P,Q),
 \quad
 J(P_K,Q_K)=J(P,Q).}
 \tag{LPC.28}
\]

If `V:L^2(eta)->L^2(eta_K)` is `Vf(x,y)=f(x)`, then

\[
 \mathcal E_{P_K,Q_K}(Vf)=\mathcal E_{P,Q}(f).
 \tag{LPC.29}
\]

#### Proof

For every nonnegative measurable `g`,

\[
 \int g\,dP_K
 =\int_Xp(x)\left(\int_Yg(x,y)K(x,dy)\right)d\eta(x),
\]

so `dP_K/deta_K=p circ pi_X`; similarly for `Q_K`.  Equations `(LPC.27)--(LPC.29)` follow by
substitution and the fact that every conditional kernel has total mass one.  QED.

Thus common recovery neither creates nor removes the lift-coherence obstruction.  This sharpens
the earlier KL-isometry theorem: the entire likelihood polarization survives.

## 6. Product formation and nonlinear rapidity fusion

Let `(P_i,Q_i)` be two equivalent probability pairs with mixtures `eta_i`, contrasts `d_i`,
visibilities `a_i`, and rapidities `chi_i`, for `i=1,2`.  Form

\[
 P_{12}=P_1\otimes P_2,
 \qquad
 Q_{12}=Q_1\otimes Q_2.
 \tag{LPC.30}
\]

### Theorem 6.1 — likelihood-polarization fusion law

Relative to `eta_1 tensor eta_2`, the new mixture has density

\[
 \frac{d\eta_{12}}{d(\eta_1\otimes\eta_2)}=1+d_1d_2.
 \tag{LPC.31}
\]

The fused packet is

\[
 \boxed{
 \chi_{12}=\chi_1+\chi_2,
 \qquad
 d_{12}=\frac{d_1+d_2}{1+d_1d_2},
 \qquad
 a_{12}=\frac{a_1a_2}{1+d_1d_2}.}
 \tag{LPC.32}
\]

The operation is associative because rapidities add.  Moreover

\[
 \boxed{J(P_{12},Q_{12})=J(P_1,Q_1)+J(P_2,Q_2).}
 \tag{LPC.33}
\]

The coherence energy is not additive; it is the positive nonlinear shadow obtained after the
Einstein-type contrast fusion in `(LPC.32)`.

#### Proof

Relative to `eta_1 tensor eta_2`, the two product densities are

\[
 (1+d_1)(1+d_2),
 \qquad
 (1-d_1)(1-d_2).
\]

Their half-sum is `1+d_1d_2`, and their normalized half-difference is the displayed formula for
`d_12`.  Likelihood ratios multiply, so their half-logarithms add.  The identity for `a_12`
follows from

\[
 (1+d_1d_2)^2-(d_1+d_2)^2
 =(1-d_1^2)(1-d_2^2).
\]

KL divergence tensorizes for probability products, proving `(LPC.33)`.  QED.

This is a genuine formation law: information is additive in the unsquared rapidity packet, while
positive visibility and hidden contrast fuse nonlinearly.

## 7. Exact closed-range and quotient-properness boundary

Let

\[
 M=F_+C-F_-C:H\longrightarrow H\oplus H.
 \tag{LPC.34}
\]

By `(LPC.15)`, `M` is unitarily equivalent to multiplication by `2d` in one output coordinate.

### Theorem 7.1 — stable coherence selection iff likelihood gap

The following are equivalent:

1. `ran(M)` is closed;
2. `ran(D)` is closed;
3. there exists `c>0` such that
   \[
   |d(x)|\ge c
   \quad\text{for eta-a.e. }x\text{ with }d(x)\ne0;
   \tag{LPC.35}
   \]
4. on the orthogonal complement of its kernel,
   \[
   \|Mf\|\ge2c\|f\|.
   \tag{LPC.36}
   \]

The kernel is

\[
 \ker M=\ker D=L^2(\{d=0\},\eta).
 \tag{LPC.37}
\]

If `d` is nonzero almost everywhere but has essential infimum zero, then `M` is injective with
dense nonclosed range.

#### Proof

Equation `(LPC.15)` gives `||Mf||=2||Df||` and the kernel formula.  A bounded operator has closed
range exactly when it is bounded below on the orthogonal complement of its kernel.  For a
multiplication operator this lower bound is equivalent to `(LPC.35)`: the forward implication is
pointwise integration; if no such `c` exists, normalized indicators of the sets
`{0<|d|<1/n}` contradict every lower bound.  If `d` is nonzero almost everywhere, multiplication
by `d` has zero kernel; its range is dense because its adjoint has zero kernel.  Essential infimum
zero rules out closed range.  QED.

This is the exact closed-range theorem.  Positivity of the canonical coherence energy is strictly
weaker than stable selection on the whole response space.

More precisely, let `M_bar` be the injective operator induced by `M` on the Hilbert quotient
`H/ker(M)`, identified with `(ker M)^perp`.  Then `M_bar` is a topologically proper map onto its
image exactly under the equivalent conditions above: a lower bound makes it a homeomorphism onto a
closed subspace, while failure of every lower bound gives unit vectors whose images converge to
zero.  The raw operator `M` itself is proper only when its kernel is zero and the likelihood gap is
positive.  Thus the theorem classifies quotient properness, not properness of an operator carrying
a nontrivial invisible fibre.

## 8. Fourth-organ prediction: exponential-family Fisher response

Let `P_0` be an `R`-invariant probability measure, let `T:X->R` be reflection odd, and assume its
exponential moment is finite for `|t|<epsilon`.  Put

\[
 A(t)=\log\int e^{tT}\,dP_0,
 \qquad
 dP_t=e^{tT-A(t)}dP_0.
 \tag{LPC.38}
\]

Then `A` is even and `R_*P_t=P_{-t}`.

### Theorem 8.1 — Fisher Hessian predicted by lift mismatch

For the reflected pair `(P_t,P_-t)`,

\[
 \boxed{
 \chi_t=tT,
 \qquad
 d_t=\tanh(tT),
 \qquad
 a_t=\operatorname{sech}(tT).}
 \tag{LPC.39}
\]

Its coherence energy and Jeffreys information are

\[
 \boxed{
 \mathcal E_t
 =4e^{-A(t)}\int\frac{\sinh^2(tT)}{\cosh(tT)}\,dP_0,}
 \tag{LPC.40}
\]

\[
 \boxed{J(P_t,P_{-t})=4tA'(t).}
 \tag{LPC.41}
\]

At the neutral point,

\[
 \boxed{
 \lim_{t\to0}\frac{\mathcal E_t}{t^2}
 =4A''(0)
 =4\operatorname{Var}_{P_0}(T).}
 \tag{LPC.42}
\]

Thus the source-generated lift disagreement predicts four times the Fisher information of the
tilt family.  This is the promised fourth-organ theorem; Fisher geometry was not used to construct
the mismatch.

If `P_0(T\ne0)>0`, then `E_t>0` for every nonzero admitted `t`.  If `T=0` has measure zero but zero
lies in the essential range of `T`, then for every `t ne 0` the coherence operator is injective
with dense nonclosed range.  Hence pointwise selection and stable cofinal selection separate
sharply.

#### Proof

Reflection invariance and oddness give `A(-t)=A(t)`.  The likelihood ratio is

\[
 \frac{dP_t}{dP_{-t}}=e^{2tT},
\]

which proves `(LPC.39)`.  The mixture is

\[
 d\eta_t=e^{-A(t)}\cosh(tT)dP_0.
\]

Substitution into `(LPC.16)` gives `(LPC.40)`.  The two directed KL divergences are both
`2tA'(t)`, proving `(LPC.41)`.  Exponential integrability permits differentiation and dominated
convergence near zero; `A'(0)=0` and `A''(0)=Var(T)`.  Since `tanh(tT)/t->T`, `(LPC.42)` follows.
The last claims follow from Theorem 7.1.  QED.

### Corollary 8.2 — literal theta carrier

Take the even positive theta source `Phi(x)dx` normalized to a probability and `T(x)=x`.  Then
`P_t` is the literal positive theta tilt, reflection is `x->-x`, and the preceding theorem gives:

1. the exact functional-equation likelihood polarization `tanh(tx),sech(tx)`;
2. strict canonical coherence energy for every `t ne 0`;
3. exact center selection if the source identifies the sign-blind and polarized lifts on the
   canonical packet;
4. Fisher curvature `4 Var_{P_0}(X)` at the center;
5. injective dense nonclosed global coherence range because the positive theta density meets every
   neighborhood of `x=0`.

Appending the common Hasse recovery kernel changes none of these quantities by Theorem 5.1.

This is not RH.  The missing arithmetic theorem is that the literal pre-zero source demands the
two lift doctrines coincide on the physical packet.  The theorem proves that such coherence is
equivalent to the critical center and cannot be manufactured by recovery or positive completion.

## 9. Exact bridge across structural organs

| organ | one generated law |
|---|---|
| functional equation | reflection exchanges `P,Q` and negates rapidity `chi` |
| positive formation/dilation | likelihood creates `a=sech chi`, `d=tanh chi`, and the Julia cycle |
| information/recovery | mismatch is `2 Delta`, bounded by Jeffreys, and preserved by every common kernel |
| formation/history | rapidities add; `(a,d)` obey nonlinear product-fusion law `(LPC.32)` |
| Fisher/prolongation | second-order mismatch is four times Fisher information |
| topology/properness | closed range is exactly the nonzero likelihood-gap condition |

The theorem therefore does more than align scalar statistics.  One source likelihood ratio
reconstructs every entry in the table, and each law is forced by the same `chi`.  It does not yet
prove that the sign-blind Julia extension is the image of the common Markov-recovery lift; that
missing comparison is the precise boundary between a bridge and a source-generated field law.

## 10. Hostile conjecture loops

### Loop A — common recovery plus functional symmetry selects the center

**False.**  Common recovery preserves every quantity in `(LPC.28)`, including nonzero mismatch.

**Survivor.**  Selection can only come from coherence of two differently polarized lifts, not from
neutral transport through one kernel.

### Loop B — Julia completion itself selects

**False.**  `C` is an isometry and `Q_0C=I` for every pair, neutral or not.

**Survivor.**  The comparison `F_+C-F_-C`, not the dilation alone, has the exact zero locus.

### Loop C — positive mismatch gives global properness

**False.**  In the theta family the canonical energy is positive off center, but the multiplication
operator by `tanh(tx)` has dense nonclosed range.

**Survivor.**  Theorem 7.1 gives the exact likelihood-gap classification.

### Loop D — mismatch energy is additive under product formation

**False.**  Positive contrast is nonlinear under products.

**Survivor.**  Rapidity is the additive unsquared packet; visibility and contrast obey the exact
Einstein-type fusion law `(LPC.32)`, while Jeffreys information remains additive.

### Loop E — the construction is a new divergence

**False.**  The scalar energy is twice classical triangular discrimination, and the Hellinger and
Jeffreys comparisons are classical `f`-divergence mathematics.

**Survivor.**  Its new role is a source-generated operator comparison between two functional-
equation lifts, with exact recovery invariance and closed-range classification.

### Loop F — lift coherence already follows from the functional equation

**False.**  `F_+` and `F_-` are both valid unitary involutions for every nonneutral pair and differ
by `(LPC.15)`.

**Survivor.**  Coherence is now one precise, falsifiable source law.  It cannot be replaced by
endpoint reflection, KL symmetry, or common recovery.

### Loop G — both Julia lifts are source-derived recovery lifts

**False / ill-typed.**  The Markov lift acts on `X times H` and regenerates conditional history.
The operators `F_+` and `F_-` act on the likelihood Julia double `L^2(eta) plus L^2(eta)`.  No
source map identifies those spaces, and only `F_- C=C U` is forced by likelihood parity.

**Survivor.**  The lift-mismatch theorem remains an exact operator bridge and produces triangular
work, but it cannot itself be the selection producer.  A stronger theory must obtain comparison
maps from genuine observation/recovery morphisms.  Posterior-Martingale Polarization Geometry does
this by transporting contrast with conditional expectation and retaining the orthogonal vertical
residue.

## 11. Literature boundary

The components are occupied parent mathematics:

- binary statistical experiments and likelihood-ratio coordinates;
- Csiszar `f`-divergences, Hellinger distance, triangular discrimination, and Jeffreys information;
- Blackwell/Le Cam comparison and common-channel data processing;
- Halmos/Julia dilation theory; see Robinson,
  [*Julia operators and Halmos dilations*](https://arxiv.org/abs/1803.09329);
- divergence inequalities, including the classical triangular/Hellinger/Jeffreys hierarchy;
- exponential-family Fisher geometry and hyperbolic likelihood coordinates.

Recent adjacent work continues to study general divergence diagnostics for Markov processes, for
example Corenflos--Dau,
[*A coupling-based approach to f-divergences diagnostics for Markov chain Monte Carlo*](https://arxiv.org/abs/2510.07559),
and Kim--Taghvaei--Mehta,
[*Divergence metrics in the study of Markov and hidden Markov processes*](https://arxiv.org/abs/2404.15779).
Those works do not supply the exact operator bridge assembled here.  Conversely, the present card
does not derive the sign-blind Julia extension from a Markov recovery kernel, so it makes no claim
to have closed a source-natural comparison square.

No priority claim is made for any ingredient or scalar inequality.  The exact corpus advance is
the dependency-closed coupling:

\[
 \text{reflected likelihood}
 \to \text{Julia split}
 \to \text{two lift doctrines}
 \to \text{triangular work}
 \to \text{common-recovery invariance}
 \to \text{rapidity fusion}
 \to \text{Fisher/properness boundary}.
\]

## 12. Gates and next source theorem

- [x] source likelihood generates both positive and hidden channels
- [x] two functional-equation lifts constructed without a chosen metric
- [x] exact lift disagreement and information identities proved
- [x] common recovery neutrality proved
- [x] product fusion and additive rapidity proved
- [x] fourth-organ Fisher theorem predicted and verified
- [x] global closed-range and quotient-properness boundary proved
- [x] literal theta/Hasse packet instantiated
- [ ] source map from the Markov observer-history packet to the likelihood Julia double
- [ ] literal arithmetic source proves lift coherence on the physical current before divisor specialization
- [ ] coefficient-faithful transport from that current to the existing critical radical
- [ ] Lean formalization after hostile paper audit

The next source theorem is no longer “find a positive receiver.”  It is:

> Prove or falsify that the positive common-recovery lift and the likelihood-polarized lift are two
> realizations of the same pre-zero functional-equation operation on the physical source packet.

If true, `(LPC.19)` selects reflection invariance.  If false, `(LPC.16)` is the exact hidden
current that every neutral route has been omitting.

## Log

- 2026-08-14 — generated canonical `tanh/sech` polarization from reflected likelihood rather than
  choosing a Julia defect.
- 2026-08-14 — proved exact two-lift mismatch, divergence hierarchy, common-recovery invariance,
  product fusion, Fisher limit, and closed-range classification.
- 2026-08-14 — hostile audit rejected common recovery, Julia completion, scalar positivity, and
  additive mismatch as selectors; retained lift coherence as the precise source gate.
- 2026-08-14 — second hostile audit separated the Markov recovery space from the Julia double,
  downgraded `F_+` from source lift to comparison doctrine, and repaired raw versus quotient
  properness.  The resulting failure generated Posterior-Martingale Polarization Geometry.
