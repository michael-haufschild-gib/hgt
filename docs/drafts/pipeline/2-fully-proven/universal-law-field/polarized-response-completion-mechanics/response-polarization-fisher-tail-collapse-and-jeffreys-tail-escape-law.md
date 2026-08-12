# Response polarization, Fisher-tail collapse, and Jeffreys-tail escape law

- **ID:** ULF-PRCM-1
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / FIVE-ORGAN FUSION / COMPLETION NO-GO
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN PENDING] [NOT RH]`
- **Statement:** A single response density can have vanishing positive tail diameter and infinite
  reciprocal-work tail diameter; every nonconstant finite escort family realizes this separation,
  and common recovery preserves it exactly.

## 1. Abstract response-polarization theorem

Let `I : R -> [0,infinity)` be continuous.  For `a <= b`, define

\[
 L_I(a,b)=\int_a^b\sqrt{I(u)}\,du,
 \qquad
 W_I(a,b)=(b-a)\int_a^b I(u)\,du.
 \tag{RPC.1}
\]

`L_I` is a path pseudodistance.  `W_I` is a symmetric two-point work after extending it by
`W_I(b,a)=W_I(a,b)`.  Extend `L_I` symmetrically as well by
`L_I(b,a)=L_I(a,b)`.

### Theorem 1.1 — local fusion and global separation

For every `a <= b`,

\[
 \boxed{L_I(a,b)^2\le W_I(a,b).}
 \tag{RPC.2}
\]

At every `t`,

\[
 \boxed{
 \lim_{h\to0}\frac{L_I(t,t+h)}{|h|}=\sqrt{I(t)},
 \qquad
 \lim_{h\to0}\frac{W_I(t,t+h)}{h^2}=I(t).}
 \tag{RPC.3}
\]

Assume additionally that

\[
 \int_{T_0}^{\infty}\sqrt{I(u)}\,du<\infty
 \tag{RPC.4}
\]

for some `T_0`, and that

\[
 \int_T^\infty I(u)\,du>0
 \tag{RPC.5}
\]

for every finite `T`.  Then

\[
 \boxed{
 \lim_{T\to\infty}\sup_{a,b\ge T}L_I(a,b)=0,}
 \tag{RPC.6}
\]

but

\[
 \boxed{
 \sup_{a,b\ge T}W_I(a,b)=\infty
 \quad\text{for every finite }T.}
 \tag{RPC.7}
\]

### Proof

Cauchy--Schwarz on `[a,b]` gives

\[
 \left(\int_a^b\sqrt I\right)^2
 \le (b-a)\int_a^b I,
\]

which is `(RPC.2)`.  Continuity of `I` and `sqrt I` gives `(RPC.3)` by the integral mean-value
limit.

For `a,b >= T`,

\[
 L_I(a,b)\le\int_T^\infty\sqrt I.
\]

The right side tends to zero by `(RPC.4)`, proving `(RPC.6)`.

Fix finite `T`.  By `(RPC.5)`, some `b_0>T` has

\[
 c:=\int_T^{b_0}I(u)\,du>0.
\]

For every `b>=b_0`,

\[
 W_I(T,b)=(b-T)\int_T^bI(u)\,du\ge c(b-T)\longrightarrow\infty.
\]

This proves `(RPC.7)`.  QED.

### Theorem 1.2 — global reflected formation properness

Define

\[
 \mathcal W_I(T)=W_I(-T,T)=2T\int_{-T}^{T}I(u)\,du
 \qquad(T\ge0).
 \tag{RPC.7a}
\]

Then

\[
 \boxed{
 \sup_{T\ge1}\mathcal W_I(T)<\infty
 \iff I(t)=0\text{ for every }t\in\mathbb R.}
 \tag{RPC.7b}
\]

More generally, if `I=I_q` is a family of continuous nonnegative responses indexed by a law
coordinate `q`, and

\[
 I_q\equiv0\iff q=0,
 \tag{RPC.7c}
\]

then bounded complete reflected work is equivalent to the fixed-locus equation `q=0`.

### Proof

If `I` vanishes, the work vanishes.  Conversely, suppose `I(t_0)>0`.  Continuity supplies a compact
interval `[a,b]` containing `t_0` and a constant `c>0` such that

\[
 \int_a^b I(u)\,du=c.
\]

For every `T>=max(|a|,|b|,1)`,

\[
 \mathcal W_I(T)
 =2T\int_{-T}^{T}I(u)\,du
 \ge2cT\longrightarrow\infty.
\]

This contradicts boundedness and proves `(RPC.7b)`.  Equivalence `(RPC.7c)` then converts response
vanishing into coordinate selection.  QED.

### Interpretation

`(RPC.3)` says the two laws have identical infinitesimal response.  `(RPC.6)`--`(RPC.7)` says
their global uniformities are nevertheless incompatible.  A positive completion adds a tail end
that remains at infinite reciprocal-work diameter.

## 2. Finite escort realization

Let `S` be finite and nonempty.  Fix `w_i>0` with `sum_i w_i=1` and real scores `r_i`.  Put

\[
 Z(t)=\sum_iw_ie^{tr_i},
 \qquad
 p_t(i)=\frac{w_ie^{tr_i}}{Z(t)},
 \tag{RPC.8}
\]

\[
 m(t)=\sum_ip_t(i)r_i,
 \qquad
 I(t)=\sum_ip_t(i)(r_i-m(t))^2.
 \tag{RPC.9}
\]

Assume `r` is nonconstant.  Write

\[
 r_+=\max_i r_i,
 \quad r_-=\min_i r_i,
 \quad R=r_+-r_->0.
\]

Let `S_+={i:r_i=r_+}`, `w_+=sum_{i in S_+}w_i`, and

\[
 \Delta_+=\min_{i\notin S_+}(r_+-r_i)>0,
 \qquad
 C_+=\frac{1-w_+}{w_+}.
 \tag{RPC.10}
\]

Define `S_-`, `w_-`, `Delta_-`, and `C_-` analogously at the minimum score.

### Theorem 2.1 — one response, two completions

The escort response satisfies

\[
 \boxed{m'(t)=I(t)>0.}
 \tag{RPC.11}
\]

For `a<=b`, its Jeffreys divergence is

\[
 \boxed{
 J(p_a,p_b)
 =(b-a)(m(b)-m(a))
 =(b-a)\int_a^b I(u)\,du
 =W_I(a,b).}
 \tag{RPC.12}
\]

The intrinsic Fisher--Rao length of the escort arc is

\[
 \boxed{d_F(a,b)=\int_a^b\sqrt{I(u)}\,du=L_I(a,b).}
 \tag{RPC.13}
\]

The positive tail has the quantitative bound

\[
 \boxed{
 \int_T^\infty\sqrt{I(t)}\,dt
 \le
 \frac{2R\sqrt{C_+}}{\Delta_+}e^{-\Delta_+T/2}
 \qquad(T\ge0),}
 \tag{RPC.14}
\]

and the negative tail has the analogous bound with `(-,C_-,Delta_-)`.  Therefore the complete
escort curve has finite Fisher length and converges at each end to a boundary law supported on
`S_+` or `S_-`.

Nevertheless,

\[
 \boxed{
 \sup_{a,b\ge T}J(p_a,p_b)=\infty,
 \qquad
 \sup_{a,b\le-T}J(p_a,p_b)=\infty}
 \tag{RPC.15}
\]

for every finite `T`.  More precisely, reflected work satisfies

\[
 \boxed{
 \lim_{t\to\infty}\frac{J(p_t,p_{-t})}{2t}=R.}
 \tag{RPC.16}
\]

Thus every nonconstant finite escort direction is Fisher-precompact and Jeffreys-proper.

### Proof

Differentiating `m` gives the variance identity `(RPC.11)`.  The finite exponential-family
likelihood ratio is

\[
 \log\frac{p_a(i)}{p_b(i)}
 =(a-b)r_i+\log Z(b)-\log Z(a).
\]

Taking expectations in both orientations and adding cancels the partition terms, giving

\[
 J(p_a,p_b)=(b-a)(m(b)-m(a)).
\]

The fundamental theorem of calculus and `(RPC.11)` prove `(RPC.12)`.  A one-dimensional Fisher
metric has line element `sqrt(I(t)) |dt|`, proving `(RPC.13)`.

For `t>=0`, factor `e^{tr_+}` from `Z(t)`.  The probability outside `S_+` obeys

\[
 p_t(S\setminus S_+)
 =\frac{\sum_{i\notin S_+}w_i e^{-t(r_+-r_i)}}
        {w_++\sum_{i\notin S_+}w_i e^{-t(r_+-r_i)}}
 \le C_+e^{-\Delta_+t}.
 \tag{RPC.17}
\]

Variance minimizes mean-square error, hence

\[
 I(t)=\mathbb E_{p_t}(r-m(t))^2
 \le\mathbb E_{p_t}(r-r_+)^2
 \le R^2 C_+e^{-\Delta_+t}.
 \tag{RPC.18}
\]

Integrating its square root proves `(RPC.14)`.  Replacing `t` by `-t` gives the negative-tail
bound.  Equation `(RPC.17)` also gives `p_t(S_+) -> 1` and

\[
 m(t)\to r_+,
 \qquad
 m(-t)\to r_-.
 \tag{RPC.19}
\]

For fixed finite `T`, full support and nonconstant score imply `m(T)<r_+`.  Therefore

\[
 J(p_T,p_b)=(b-T)(m(b)-m(T))\longrightarrow\infty
 \quad(b\to\infty).
\]

The negative tail is identical after reflection.  Finally,

\[
 \frac{J(p_t,p_{-t})}{2t}=m(t)-m(-t)\longrightarrow r_+-r_-=R,
\]

proving `(RPC.15)`--`(RPC.16)`.  QED.

## 3. Sharp binary witness

Take two states with weights `1/2,1/2` and scores `0,1`.  Then

\[
 p_t(1)=\frac{e^t}{1+e^t},
 \qquad
 I(t)=p_t(1)(1-p_t(1))=\frac1{4\cosh^2(t/2)}.
 \tag{RPC.20}
\]

The Fisher coordinate

\[
 \theta(t)=2\arctan(e^{t/2})
\]

satisfies `theta'(t)=sqrt(I(t))` and maps the extended line `[-infinity,+infinity]` onto `[0,pi]`.
Hence

\[
 \boxed{\int_{-\infty}^{\infty}\sqrt{I(t)}\,dt=\pi.}
 \tag{RPC.21}
\]

But

\[
 \boxed{J(p_t,p_{-t})=2t\tanh(t/2)\longrightarrow\infty.}
 \tag{RPC.22}
\]

This is a minimal exact countermodel to the claim that compact positive completion supplies
selection properness.

## 4. Common-recovery invariance

Let `K` be any parameter-independent Markov kernel from the finite state space to a latent history
space.  Form

\[
 P_t(dx,dh)=p_t(dx)K(x,dh).
 \tag{RPC.23}
\]

### Theorem 4.1 — the separation lifts information-neutrally

For every `a,b`,

\[
 \boxed{
 D(P_a\Vert P_b)=D(p_a\Vert p_b),
 \qquad
 J(P_a,P_b)=J(p_a,p_b).}
 \tag{RPC.24}
\]

Moreover the local response reconstructed from work is unchanged:

\[
 \boxed{
 \lim_{h\to0}\frac{J(P_t,P_{t+h})}{h^2}=I(t).}
 \tag{RPC.25}
\]

Consequently the lifted family has the same Fisher length, the same finite positive completion,
and the same infinite Jeffreys tail diameters.

### Proof

The common-recovery chain rule gives the first identity in `(RPC.24)` because the conditional law
`K(x,dh)` is identical under both parameters.  Add the two orientations for Jeffreys equality.
Divide `(RPC.24)` by `h^2` and use `(RPC.3)` and `(RPC.12)` to obtain `(RPC.25)`.  The remaining
claims depend only on `I` and `J`, so they are preserved.  QED.

## 5. Fourth-organ theorem: observed compactness and deficit escape

Let `Phi` be any Markov observer of the complete formed packet, and write

\[
 J_\Phi(a,b)=J(\Phi_*P_a,\Phi_*P_b),
 \qquad
 \Delta_\Phi(a,b)=J(P_a,P_b)-J_\Phi(a,b).
 \tag{RPC.26}
\]

Data processing gives `Delta_Phi(a,b)>=0`.

### Corollary 5.1

Whenever the observed local Fisher response exists,

\[
 I_\Phi(t)=\lim_{h\to0}\frac{J_\Phi(t,t+h)}{h^2}\le I(t).
 \tag{RPC.27}
\]

Thus its positive tail length is no larger than the complete finite Fisher tail.  If, for some
finite `T`,

\[
 \sup_{a,b\ge T}J_\Phi(a,b)<\infty,
 \tag{RPC.28}
\]

then

\[
 \boxed{
 \sup_{a,b\ge T}\Delta_\Phi(a,b)=\infty.}
 \tag{RPC.29}
\]

### Proof

Apply KL data processing in both orientations, divide by `h^2`, and take the local limit to obtain
`(RPC.27)`.  For `(RPC.29)`, fix `a=T`.  Theorem 2.1 gives
`J(P_T,P_b)->infinity`; `(RPC.28)` bounds `J_Phi(T,b)`.  Their difference therefore diverges.
QED.

### Corollary 5.2 — observed-plus-deficit selection

For reflected endpoints, put

\[
 \mathcal W_\Phi(T)=J_\Phi(-T,T),
 \qquad
 \mathcal D_\Phi(T)=\Delta_\Phi(-T,T).
\]

The exact conservation law is

\[
 \boxed{
 \mathcal W_I(T)=\mathcal W_\Phi(T)+\mathcal D_\Phi(T).}
 \tag{RPC.29a}
\]

If both terms on the right are uniformly bounded for `T>=1`, then `I identically 0`.  Under the
faithfulness condition `(RPC.7c)`, the law coordinate is therefore `q=0`.

### Proof

Equation `(RPC.29a)` is the definition of the divergence deficit.  Uniform bounds give a uniform
bound on complete work; Theorem 1.2 applies.  QED.

This is a prediction in the observer/topology organ derived from positivity, information,
amplification, and recovery.  Fisher compactness cannot erase complete properness; bounded observed
work moves it into an unbounded deficit fibre.

## 6. No-go closure

- **Killed conjecture:** Fisher-precompactness of an amplified formation implies bounded global
  information work and can therefore select the reflection fixed point.
- **Killing theorem:** ULF-PRCM-1.  Every nonconstant finite escort orbit is Fisher-precompact, yet
  every tail has infinite Jeffreys diameter.
- **Strongest positive survivor:** local Fisher response and reciprocal information work are two
  exact accumulations of one response density, related by `(RPC.2)` and exactly preserved by common
  recovery.  Their completion mismatch forces the observer-deficit alternative `(RPC.29)`, while
  Theorem 1.2 gives an unconditional global formation/properness law.
- **New open core:** an RH selector must bound complete reciprocal work or prove observer
  sufficiency.  Positive/Fisher compactness and recurrence cannot substitute for that premise.
- **Lean status:** paper proof dependency-closed; formalization intentionally remains a Stage-2
  gate in the current research pass.

## 7. Literature and priority audit

Parent ingredients are occupied:

1. Miyamoto--Meneghetti--Pinele--Costa,
   [On Closed-Form Expressions for the Fisher--Rao Distance](https://arxiv.org/abs/2304.14885),
   surveys the one-dimensional Fisher--Rao integral formula.
2. Nielsen,
   [Approximation and bounding techniques for the Fisher--Rao distances](https://arxiv.org/abs/2403.10089),
   records dual-geodesic Jeffreys/Bregman energy and `d_F <= sqrt(J)`.
3. Pistone--Rapallo--Riccomagno,
   [The Fisher score on the closed simplex](https://arxiv.org/abs/2602.07665), develops Fisher
   structures at finite-state boundary laws.
4. Exponential-family likelihood, variance response, and Bregman identities are classical.

Broad arXiv search found these parents but no theorem packaging vanishing Fisher tail diameter,
infinite Jeffreys tail diameter, exact common-recovery invariance, and observer-deficit migration as
one formation law.  No external priority claim is made.  The contribution here is the exact
cross-organ mechanism and the resulting selection no-go.

## 8. Gates

- [x] abstract local/global polarization theorem
- [x] finite escort tail estimates
- [x] exact Fisher/Jeffreys fusion identity
- [x] common-recovery lift
- [x] fourth-organ observer-deficit theorem
- [x] global reflected properness and observed-plus-deficit selection
- [x] sharp binary countermodel
- [x] hostile correctness and literature audit
- [ ] Lean formalization
- [ ] literal arithmetic source realization

## Log

- 2026-08-12 — dependency-closed paper proof completed after full universal-law and Lean-corpus
  search found local Fisher and Jeffreys properness separately but not their dual-completion law.
