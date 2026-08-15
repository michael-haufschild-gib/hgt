# Polarized cross-effect complement intertwining and bounded-arity no-go

- **ID:** ULF-PCIM-1
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL INTERVENTION / FORMATION / DUALITY EXCHANGE LAW
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM, NOT ROUTE]
  [EXACT RECONSTRUCTION] [EXACT FUSION INTERTWINER] [BOUNDED-ARITY NO-GO]
  [INFORMATION-NEUTRAL DUALITY] [NOT SELECTION] [NOT RH] [LEAN PENDING]`

## 1. Setup

Let `I` be finite and identify `Omega_I={0,1}^I` with `P(I)`. For a real law
`f:P(I)->R`, define its Boolean cross-effect packet and packet recovery by

\[
 (\mathsf Mf)(S)=\sum_{T\subseteq S}(-1)^{|S\setminus T|}f(T),
 \qquad
 (\mathsf Zc)(S)=\sum_{T\subseteq S}c(T).
 \tag{PC.1}
\]

Let complement act by `(Cf)(S)=f(I\setminus S)`. For a polarization `q:I->(0,1)`, let `P_q` be
the product Bernoulli law. Put

\[
 w_i=q_i(1-q_i),\qquad
 \psi_i^q(X)={\mathbf1_{i\in X}-q_i\over\sqrt{w_i}},\qquad
 \psi_S^q=\prod_{i\in S}\psi_i^q,
 \tag{PC.2}
\]

and `widehat f_q(S)=E_q[f psi_S^q]`. Write `bar q_i=1-q_i` and `RX=I\setminus X`.

## 2. Complete raw reconstruction and complement action

### Theorem 2.1 -- Boolean packet reconstruction

\[
 \boxed{\mathsf M\mathsf Z=1,\qquad \mathsf Z\mathsf M=1.}
 \tag{PC.3}
\]

#### Proof

The coefficient of `c(U)` in `(MZc)(S)` is

\[
 \mathbf1_{U\subseteq S}
 \sum_{U\subseteq T\subseteq S}(-1)^{|S\setminus T|}
 =\mathbf1_{U\subseteq S}(1-1)^{|S\setminus U|}
 =\mathbf1_{U=S}.
\]

The same Boolean-interval calculation proves `ZM=1`. ∎

Define the raw packet complement action by

\[
 (\mathsf Kc)(S)=(-1)^{|S|}\sum_{U\supseteq S}c(U).
 \tag{PC.4}
\]

### Theorem 2.2 -- triangular raw complement

\[
 \boxed{\mathsf M\mathsf C\mathsf Z=\mathsf K,
 \qquad \mathsf K^2=1.}
 \tag{PC.5}
\]

#### Proof

The coefficient of `c(U)` in `(MCZc)(S)` is

\[
 \sum_{\substack{T\subseteq S\\U\subseteq I\setminus T}}
 (-1)^{|S\setminus T|}
 =(-1)^{|S|}\sum_{T\subseteq S\setminus U}(-1)^{|T|}.
\]

It vanishes unless `S subseteq U`, and then equals `(-1)^|S|`. This is `(PC.4)`.
The involution follows from `MZ=1`, `ZM=1`, and `C^2=1`. ∎

## 3. Exact raw-to-polarized fusion

For `S subseteq I`, write

\[
 w_S^{1/2}=\prod_{i\in S}\sqrt{w_i},
 \qquad
 q_{T\setminus S}=\prod_{j\in T\setminus S}q_j.
\]

Define

\[
 (\mathsf B_qc)(S)
 =w_S^{1/2}\sum_{T\supseteq S}q_{T\setminus S}c(T).
 \tag{PC.6}
\]

### Theorem 3.1 -- fusion transform and complement intertwining

For every law `f`,

\[
 \boxed{\widehat f_q=\mathsf B_q\mathsf Mf.}
 \tag{PC.7}
\]

The map `B_q` is invertible. If `(Dh)(S)=(-1)^{|S|}h(S)`, then

\[
 \boxed{\mathsf B_{\bar q}\mathsf K=\mathsf D\mathsf B_q.}
 \tag{PC.8}
\]

Thus source polarization conjugates degree-mixing triangular complement to degree-preserving parity.

#### Proof

Put `c=Mf`. Theorem 2.1 gives

\[
 f(X)=\sum_{T\subseteq I}c(T)\prod_{i\in T}\mathbf1_{i\in X}.
 \tag{PC.9}
\]

Since `1_{i in X}=q_i+sqrt(w_i) psi_i^q(X)`, expansion of `(PC.9)` shows that the coefficient of
`psi_S^q` is `(B_qc)(S)`, proving `(PC.7)`. Ordered by reverse inclusion, `B_q` is triangular with
diagonal entry `w_S^(1/2)` at `S`. Every diagonal entry is nonzero, so `B_q` is invertible.

Complement sends `P_q` to `P_barq`, and `psi_i^(bar q)(RX)=-psi_i^q(X)`. Therefore

\[
 \widehat{f\circ R}_{\bar q}(S)=(-1)^{|S|}\widehat f_q(S).
 \tag{PC.10}
\]

Theorem 2.2 says `M(f o R)=K Mf`. Applying `(PC.7)` to both sides of `(PC.10)` proves `(PC.8)`. ∎

### Corollary 3.2 -- degreewise information neutrality

For every degree set `E subseteq {0,...,|I|}`,

\[
 \boxed{
 \sum_{|S|\in E}|(\mathsf B_{\bar q}\mathsf Kc)(S)|^2
 =\sum_{|S|\in E}|(\mathsf B_qc)(S)|^2.}
 \tag{PC.11}
\]

#### Proof

Equation `(PC.8)` changes each polarized coordinate only by the sign `(-1)^|S|`. ∎

This is information-neutrality: complete functional-equation transport preserves every polarized
interaction-degree energy. It supplies no selection theorem.

## 4. Bounded-arity obstruction

Let `P_{<=d}` restrict a packet to subsets of size at most `d`.

### Theorem 4.1 -- no bounded raw duality closure

For every `d<|I|`, no map `K_d` on degree-at-most-`d` packets satisfies

\[
 P_{\le d}\mathsf K=\mathsf K_dP_{\le d}
 \tag{PC.12}
\]

for all raw packets.

#### Proof

Choose `U subseteq I` with `|U|=d+1`, and let `c` be the delta packet with `c(U)=1`. Then
`P_{<=d}c=0`. But `(Kc)(emptyset)=1`, so `P_{<=d}Kc` is nonzero. If `(PC.12)` held, the same
quantity would equal `K_d(0)`. Applying `(PC.12)` to the zero packet first gives `K_d(0)=0`, a
contradiction. ∎

An omitted interaction of arity `d+1` contributes under raw complement to every visible subset of
that interaction. No endomorphism of the truncated reporter can recover the missing action.

## 5. Three-organ fusion and fourth-organ prediction

The theorem couples three structurally different organs:

1. Boolean incidence/cross-effects `c=Mf`;
2. product probability/ANOVA coefficients `B_qc`;
3. Hilbert work `sum_S |(B_qc)(S)|^2`.

For real `f`, execute the same law as a coherent phase family

\[
 |\Psi_{q,f}(t)\rangle
 =\sum_{X\subseteq I}\sqrt{P_q(X)}e^{itf(X)}|X\rangle.
 \tag{PC.13}
\]

Its pure-state quantum Fisher information is

\[
 \mathcal I_q(f)=4\operatorname{Var}_q(f)
 =4\sum_{S\ne\varnothing}|(\mathsf B_q\mathsf Mf)(S)|^2.
 \tag{PC.14}
\]

Therefore `(PC.8)` predicts and proves the fourth-organ law

\[
 \boxed{\mathcal I_{\bar q}(f\circ R)=\mathcal I_q(f),}
 \tag{PC.15}
\]

including equality separately at every nonzero interaction degree.

## 6. Exact interpretation

```text
intervention cube
    -> complete raw cross-effect packet
    -> source-polarized packet
    -> positive work / coherent response

complement on laws
    -> triangular mixing on raw packet
    -> parity on polarized packet
    -> degreewise information-neutral response
```

The mechanism proves:

1. complete formation plus polarization converts external duality into diagonal transport;
2. every bounded raw interaction truncation is incapable of carrying that duality universally.

It does **not** prove that reciprocal polarization fibres are one physical fibre. That
internalization is a distinct global formation/properness problem. Treating cross-fibre unitarity
as same-fibre symmetry would recreate the corpus's failed information-neutral selection attempts.

## 7. Boundaries and parents

1. Finiteness of `I` and `0<q_i<1` are load-bearing for invertibility of `B_q`.
2. Product polarization is load-bearing. General dependent laws require a different orthogonal
   packet and need not diagonalize complement degreewise.
3. Complement is load-bearing. A general law involution may have a different packet action.
4. Squared work loses coefficient sign/phase; `(PC.11)` is conservation, not reconstruction from
   positive work alone.
5. Boolean Möbius inversion, cross-effects, biased Walsh/Hoeffding decomposition, Parseval, and
   pure-state QFI are classical parents. Exact content here is fused transform `(PC.6)` and
   intertwiner `(PC.8)`, together with obstruction `(PC.12)`.
6. Existing ULF interaction-spectrum mechanics already proves biased-Walsh reconstruction,
   work/QFI conservation, and cofinal properness. This theorem adds raw intervention formation and
   exact functional-equation action across the raw/polarized exchange.
7. No source-normal landing, cofinal selector, RH theorem, recurrence theorem, or physical clock is
   claimed.

## 8. Lean target

Formalize only the exact finite core:

- Boolean zeta/Möbius recovery;
- raw complement action and involution;
- explicit raw-to-polarized transform `(PC.6)--(PC.7)`;
- intertwining `(PC.8)`;
- bounded-arity nonfactorization `(PC.12)`.

Reuse existing finite Bernoulli/Walsh infrastructure. No new probability or QFI formalization is
required for this card.
