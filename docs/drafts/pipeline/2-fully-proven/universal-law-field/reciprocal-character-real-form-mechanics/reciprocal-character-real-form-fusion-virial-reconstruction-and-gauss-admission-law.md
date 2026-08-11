# Reciprocal-character real-form fusion, virial reconstruction, and Gauss admission law

- **ID:** ULF-RCRFM-2
- **Stage:** 2-fully-proven
- **Type:** FOUR-ORGAN FUSION / JOINT RECONSTRUCTION / COFINAL ADMISSION CLASSIFICATION
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [UNIVERSAL FINITE LAW]
  [LITERAL GAUSS SPECIALIZATION] [RH SELECTION GATE, NOT RH]

## 1. Finite reciprocal-character packet

Let `I` be a finite nonempty set.  For each `i in I`, fix a weight `a_i>0` and a distinct clock
`lambda_i>0`.  Put

\[
 U_i(z)=\exp(\lambda_i z/2).
 \tag{RCV.1}
\]

The split formation energy, virial current, and compact phase energy are

\[
 \mathcal E(t)=\sum_i a_i\bigl(e^{\lambda_i t/2}-e^{-\lambda_i t/2}\bigr)^2,
 \tag{RCV.2}
\]

\[
 \mathcal V(t)=\sum_i a_i\lambda_i t
          \bigl(e^{\lambda_i t}-e^{-\lambda_i t}\bigr),
 \tag{RCV.3}
\]

\[
 \mathcal P(s)=\sum_i a_i\left|e^{i\lambda_i s/2}
                         -e^{-i\lambda_i s/2}\right|^2.
 \tag{RCV.4}
\]

Equivalently,

\[
 \mathcal E(t)=2\sum_i a_i(\cosh(\lambda_i t)-1),
 \qquad
 \mathcal P(s)=2\sum_i a_i(1-\cos(\lambda_i s)).
 \tag{RCV.5}
\]

These are three structurally different organs:

1. reciprocal half-character/root formation;
2. positive Hellinger-type split energy;
3. compact phase/recurrent energy.

The moment/Hankel jet packet and Hodge/virial response will be forced from them.

## 2. Master real-form theorem

### Theorem 2.1 -- exact fusion and conservation

For every real `t,s`,

\[
 \boxed{\mathcal V(t)=t\,\mathcal E'(t),}
 \tag{RCV.6}
\]

and, for the entire complexified formation

\[
 \mathscr E(z)=\sum_i a_i(e^{\lambda_i z}+e^{-\lambda_i z}-2),
 \tag{RCV.7}
\]

\[
 \boxed{\mathcal E(t)=\mathscr E(t),\qquad
        \mathcal P(s)=-\mathscr E(is).}
 \tag{RCV.8}
\]

At their common fixed point,

\[
 \boxed{\mathcal E''(0)=\mathcal P''(0)=2\sum_i a_i\lambda_i^2.}
 \tag{RCV.9}
\]

Thus split energy, compact phase energy, the first positive clock moment, and the virial current
are forced shadows of one complexified source packet.

#### Proof

Squaring in `(RCV.2)` gives

\[
 (e^{x/2}-e^{-x/2})^2=e^x+e^{-x}-2=2(\cosh x-1).
\]

Differentiating termwise in the finite sum yields

\[
 \mathcal E'(t)=\sum_i a_i\lambda_i
 (e^{\lambda_i t}-e^{-\lambda_i t}),
\]

which proves `(RCV.6)`.  Substituting `z=is` into `(RCV.7)` and using
`e^{ix}+e^{-ix}=2cos x` proves `(RCV.8)`.  Two derivatives at zero prove `(RCV.9)`.  QED.

### Theorem 2.2 -- coercivity and exact radical

For every real `t`,

\[
 \boxed{\mathcal V(t)\ge 2t^2\sum_i a_i\lambda_i^2\ge0.}
 \tag{RCV.10}
\]

Consequently

\[
 \boxed{\mathcal V(t)=0\iff \mathcal E(t)=0\iff t=0.}
 \tag{RCV.11}
\]

#### Proof

For every real `x`,

\[
 x\sinh x\ge x^2.
 \tag{RCV.12}
\]

If `x>=0`, this is `sinh x>=x` multiplied by `x`; if `x<=0`, it is `sinh x<=x`
multiplied by the negative number `x`.  Since

\[
 \mathcal V(t)=2\sum_i a_i(\lambda_it)\sinh(\lambda_it),
\]

`(RCV.10)` follows.  Strict positivity of at least one `a_i lambda_i^2` gives the virial
radical.  The split energy is a sum of positive squares and has the same radical.  QED.

## 3. Joint reconstruction

### Theorem 3.1 -- finite jet reconstruction

Let `d=|I|`.  The even jet packet

\[
 \bigl(\mathcal E^{(2)},\mathcal E^{(4)},\ldots,
       \mathcal E^{(4d)}\bigr)(0)
 \tag{RCV.13}
\]

determines the unordered set of pairs `{(lambda_i,a_i)}`.  Hence it jointly determines
`mathscr E`, `mathcal E`, `mathcal P`, and `mathcal V`.

#### Proof

For `k>=0`,

\[
 {1\over2}\mathcal E^{(2k+2)}(0)
   =\sum_i a_i\lambda_i^{2k+2}.
 \tag{RCV.14}
\]

Set `x_i=lambda_i^2` and `b_i=a_i lambda_i^2`.  Then `(RCV.14)` is the ordinary positive
moment packet

\[
 M_k=\sum_i b_i x_i^k,
 \qquad 0\le k\le2d-1.
\]

The `d x d` Hankel matrix `(M_(r+s))_(0<=r,s<d)` factors as

\[
 V\,\operatorname{diag}(b_i)\,V^T,
\]

where `V` is the Vandermonde matrix of the distinct positive nodes `x_i`.  It is positive
definite.  The usual annihilating-polynomial recurrence uniquely recovers
`prod_i(X-x_i)` from `M_0,...,M_(2d-1)`.  Its roots recover `x_i`; positivity gives
`lambda_i=sqrt(x_i)`.  The first `d` moments then recover `b_i` by the square Vandermonde
system, and `a_i=b_i/x_i`.  QED.

## 4. Recurrent compact form and open lift

If the clocks `{lambda_i}` are rationally independent, Kronecker recurrence gives arbitrarily
large `s_n` such that every `e^{i lambda_i s_n}` tends to `1`.  Therefore

\[
 \mathcal P(s_n)\longrightarrow0,
 \tag{RCV.15}
\]

while the marked universal-cover history `s_n(lambda_i)_i` has norm tending to infinity.
For prime clocks `lambda_p=log p`, rational independence follows from unique factorization.

This is the exact coexistence requested by the field programme: closed recurrent observation and
open lifted history arise from the compact real form, while positive Hodge mass arises from the
split real form of the same complexified character.

## 5. Fourth-organ refinement: the Gauss Hodge/seam shape has a virial generator

Fix `m>=1`, a Xi zero copy `q`, and a prime `p`.  Write

\[
 t_q=2\operatorname{Re}(q)-1,
 \qquad \lambda_p=\log p,
 \tag{RCV.16}
\]

and define the source weight

\[
 a_{m,p}={\log2\over2}\,
 {\operatorname{GaussCurrent}_m(p)\,
  \operatorname{FisherDensity}(p)\over\log p}.
 \tag{RCV.17}
\]

All factors are strictly positive.  Existing corpus theorems already identify the Gauss Hodge
current with the reciprocal Hodge shape and compare that shape two-sidedly with the Burnol seam
energy.  They give the static pointwise bridge

\[
 H_m(q,p)={\log2\over2}\operatorname{GaussCurrent}_m(p)
 \operatorname{FisherDensity}(p)\,
 t_q(p^{t_q}-p^{-t_q}).
 \tag{RCV.18}
\]

Applying `(RCV.6)` to the one-label packet `(a_(m,p),lambda_p)` yields the additional generator
identity

\[
 \boxed{
 H_m(q,p)=t_q{d\over dt}\bigg|_{t=t_q}
 \left[a_{m,p}(p^t+p^{-t}-2)\right].}
 \tag{RCV.19}
\]

Thus the assembled Hodge/seam invariant is not merely comparable to reciprocal formation energy:
it is exactly its source-scale response.

From `(RCV.10)`,

\[
 \boxed{
 H_m(q,p)\ge
 \log2\,\operatorname{GaussCurrent}_m(p)
 \operatorname{FisherDensity}(p)\,\log p\,t_q^2.}
 \tag{RCV.20}
\]

This quantitative coercivity was not used to define the Hodge pairing.

## 6. Cofinal admission classification

### Theorem 6.1 -- prime-summable Gauss mass selects the neutral real form

For `m>=1` and a fixed Xi zero copy `q`,

\[
 \boxed{
 \operatorname{Summable}_{p\ \mathrm{prime}} H_m(q,p)
 \iff t_q=0
 \iff \operatorname{Re}(q)=1/2.}
 \tag{RCV.21}
\]

#### Proof

If `t_q=0`, every summand is zero.

Assume `t_q!=0`.  The exact Weil normalization and Fisher bound in the corpus are

\[
 \operatorname{GaussCurrent}_m(p)\log p
 ={2\over m^2}\left({p-1\over p}\right)^{2m}(p^m-1)^2,
 \tag{RCV.22}
\]

\[
 \operatorname{FisherDensity}(p)\ge {1\over4p}.
 \tag{RCV.23}
\]

Since `p>=2`,

\[
 \left({p-1\over p}\right)^{2m}\ge2^{-2m},
 \qquad
 (p^m-1)^2\ge {p^{2m}\over4}.
 \tag{RCV.24}
\]

Combining `(RCV.20)--(RCV.24)` gives

\[
 H_m(q,p)\ge
 {\log2\,t_q^2\over2^{2m+3}m^2}\,p^{2m-1}
 \ge {\log2\,t_q^2\over2^{2m+3}m^2}>0.
 \tag{RCV.25}
\]

The prime set is infinite, so a family bounded below by one fixed positive constant is not
summable.  This contradiction proves `(RCV.21)`.  QED.

### Corollary 6.2 -- exact RH admission gate

For every `m>=1`,

\[
 \boxed{
 \left(\forall q,\ \operatorname{Summable}_p H_m(q,p)\right)
 \iff \mathrm{RH}.}
 \tag{RCV.26}
\]

This is a selection consequence, not an RH proof: the left side is not yet known to be forced by
an independent pre-zero source theorem.  The field has nevertheless converted the missing step
into one exact obligation:

> construct the literal global trace/explicit-formula mechanism that admits the Gauss virial
> current in the prime trace ideal before Xi-zero specialization.

If that theorem is proved, `(RCV.26)` finishes the selection.  If it is impossible, the Gauss
packet cannot be the globally conserved field current and this branch must be retired.

## 7. Hostile audit

1. **Finite packets do not select.**  Every finite packet is entire and summable.
2. **Recurrence does not imply admission.**  The compact phase packet is bounded for every `t_q`,
   while the split Gauss packet is nonsummable for every `t_q!=0`.
3. **Reflection does not select.**  Both split energy and virial mass are even in `t_q`.
4. **Positive energy loses orientation.**  The root gap changes sign under reciprocal duality.
5. **The trace-ideal premise is load-bearing.**  It may not be inserted after locating zeros.
6. **No universal HT equivalence.**  The theorem couples jets to the same finite character packet;
   it does not claim that every hypertranscendental function arises this way.
7. **Weight dependence matters.**  A different cofinal weight can make split energies summable.
   The admission classification uses the literal Gauss residue and Fisher weights.

## 8. Corpus and literature placement

- `MarkedHalfCharacterDualityLaw` supplies the reciprocal root and its positive split square.
- `ComplexTimeGenerativeMechanics` supplies the broader real/imaginary execution principle.
- `PrimeSuperspaceWickAnisotropy` supplies the finite compact/split Fisher sandwich.
- `PrimeBooleanMassHankelQuantumFusion` supplies the precedent for source-generated moment
  reconstruction and recurrence/QFI fusion.
- `GaussHodgeMassCurrent` supplies the literal Hodge current and its exact critical radical.
- `GaussHodgeSeamEnergyBridge` supplies the existing pointwise Hodge/cosh/seam comparison.
- `GaussMultiPlaceAssembly` supplies the Weil-normalized residue current.
- `PrimeFirstTraceEssentialEdgeReflectedIdealGrade` supplies the Fisher-density bounds.

Connes--Consani's scaling Hamiltonian contains a logarithmic derivative inside a semi-local trace
formula; exponential-family information geometry treats positive real forms and Fisher/Bregman
data.  Neither the external parents nor the internal Wick/Hodge-seam parents give the common
Euler generator `(RCV.19)`, finite joint reconstruction from one real-form packet, or the cofinal
classification `(RCV.21)`.

## 9. Lean gate

The theorem is eligible for Lean only after the paper identities and the cofinal lower bound above
have been checked against the literal corpus definitions.  Formalization must include:

1. half-character square and virial derivative;
2. virial quadratic coercivity and radical;
3. compact phase identity at the common jet;
4. literal Gauss specialization `(RCV.19)--(RCV.20)`;
5. prime-summability classification `(RCV.21)` and RH gate `(RCV.26)`.
