# Rank-one orientation and Lorentzianization law

- **ID:** `rank-one-orientation-lorentzianization-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONSTRAINT RELATIVITY / COFRAME MODEL
- **Scientific status:** `[PAPER-PROVED] [NO LEAN WRITTEN OR BUILT] [NOT RH]`
- **Novelty status:** abstract proof is classical splitting, Riesz representation, and rank-one
  inertia. Candidate significance is its exact corpus conjunction: one source orientation
  quotient, same sole Stokes metric port, central determinant exponent, and reflected arithmetic
  displacement. Their canonical identification remains conjectural.
- **Parent:**
  `../../1-in-progress/constraint-relativity/constraint-relativity-and-relation-completion-spacetime.md`.

## 1. Purpose

The corpus repeatedly exposes one signed channel before it exposes a metric. This card proves the
strongest unconditional abstract conclusion:

> a one-dimensional absolute quotient plus one signed coframe and a positive transverse form
> permits at most one nonpositive metric direction.

It does not produce a canonical metric. “One time direction” is literal only in the Lorentz phase
of the resulting rank-one quadratic form.

## 2. Absolute source quotient

Let real vector spaces and maps

\[
 A_1\xrightarrow{D}A_2\xrightarrow{T}O
 \tag{2.1}
\]

admit `H:A_2->A_1` and `j:O->A_2` satisfying

\[
 DH+\jmath T=I,
 \qquad TD=0,
 \qquad T\jmath=I,
 \qquad \dim O=1.
 \tag{2.2}
\]

### Theorem 2.1 — unique absolute orientation quotient

There is a direct sum

\[
 \boxed{A_2=\operatorname{im}D\oplus\jmath(O),}
 \qquad
 \boxed{A_2/\operatorname{im}D\cong O.}
 \tag{2.3}
\]

Every linear observer `F:A_2->W` has the unique decomposition

\[
 \boxed{F=(F\jmath)T+(FD)H.}
 \tag{2.4}
\]

An observer blind to relative boundaries, `FD=0`, factors uniquely through the one-dimensional
absolute coordinate `T`.

#### Proof

Equation `(2.2)` writes every `x in A_2` as

\[
 x=DHx+\jmath Tx.
\]

If `Dy=j o`, applying `T` gives `o=0`, and then `Dy=0`; hence the displayed sum is direct.
Applying `F` to the splitting proves `(2.4)`. If `FD=0`, only the `T` term remains. QED.

## 3. Coframe before metric

Let `V` be finite-dimensional. Supply:

1. a positive-definite symmetric form `P`;
2. a nonzero signed port `M in V^*`;
3. a scalar `Gamma` and quadratic form
   \[
   Q(x)=P(x,x)+\Gamma M(x)^2.
   \tag{3.1}
   \]

Assume every nonpositive contribution factors through `M`.

### Theorem 3.1 — rank-one Lorentzianization

Let `r=P^{-1}M`, `c=M(r)=P(r,r)>0`, and `u=r/c`. Then

\[
 M(u)=1,
 \qquad
 V=\ker M\oplus\mathbb Ru
 \tag{3.2}
\]

orthogonally for `P`. Writing `x=z+tu`, with `z in ker M` and `t=M(x)`, gives

\[
 \boxed{Q(x)=P(z,z)+\Omega t^2,}
 \qquad
 \Omega=c^{-1}+\Gamma.
 \tag{3.3}
\]

Consequently:

\[
\begin{array}{c|c}
\Omega>0 & Q\text{ is positive definite},\\
\Omega=0 & \operatorname{Rad}Q=\mathbb Ru\text{ and }\operatorname{corank}Q=1,\\
\Omega<0 & \operatorname{sig}Q=(\dim V-1,1).
\end{array}
 \tag{3.4}
\]

In every phase,

\[
 \boxed{\operatorname{ind}_{-}(Q)+\dim\operatorname{Rad}(Q)\le1.}
 \tag{3.5}
\]

#### Proof

Riesz representation gives `P(r,x)=M(x)`. Therefore `c=P(r,r)>0` and `M(u)=1`. For
`t=M(x)` and `z=x-tu`, one has `M(z)=0` and

\[
 P(z,u)=c^{-1}M(z)=0.
\]

Hence `P(x,x)=P(z,z)+c^{-1}t^2`, proving `(3.3)`. The trichotomy and `(3.5)` follow immediately
because `P` is positive definite on `ker M`. QED.

## 4. Time reversal and orientation erasure

Assume `Omega<0` and `dim V>=2`. Then

\[
 Q(z+tu)=0
 \quad\Longleftrightarrow\quad
 P(z,z)=-\Omega t^2.
 \tag{4.1}
\]

The timelike set `Q<0` has two connected components distinguished by `t>0` and `t<0`. Define

\[
 \Theta(z+tu)=z-tu.
 \tag{4.2}
\]

### Proposition 4.1 — unique port reflection

`Theta` is the unique `P`-orthogonal reflection fixing `ker M` pointwise and negating `M`. It
preserves `Q` and exchanges the two time cones.

Every reader factoring through `P(z,z)`, `M(x)^2`, or `Q(x)` is `Theta`-invariant and cannot
recover the sign of `M(x)`. The positive rank tensor `M tensor M` is therefore an unoriented
metric shadow of the coframe `M`.

#### Proof

The direct sum `(3.2)` forces any such reflection to act as identity on `ker M` and as negation on
`u`, which is `(4.2)`. Formula `(3.3)` shows that `Q` is preserved. Each listed reader contains
only even powers of `t`; therefore it is `Theta`-invariant. QED.

Positivity alone does not erase orientation: for example `exp(M(x))` is positive and signed.
Erasure requires reflection invariance, squaring, norm scalarization, or factorization through
`M tensor M`.

## 5. Reciprocal-flow no-go

### Theorem 5.1 — nontrivial reciprocal invariant is indefinite

For `mu != 0`, let

\[
 B_s(a,b)=(e^{s\mu}a,e^{-s\mu}b).
 \tag{5.1}
\]

Every symmetric quadratic form invariant under all `B_s` is a multiple of `ab`. Every invariant
positive-semidefinite quadratic form is zero.

#### Proof

Write the form as `A a^2+2B ab+D b^2`. Invariance for every `s` forces

\[
 A e^{2s\mu}=A,
 \qquad
 D e^{-2s\mu}=D,
\]

so `A=D=0`. The remaining form `2B ab` is indefinite unless `B=0`. QED.

Thus a conserved quadratic reader of reciprocal expansion/contraction behaves Lorentzian; no
nonzero positive energy can be both complete and invariant.

## 6. Corpus instantiation

The publication-ready corpus independently supplies four organs.

1. **Absolute source quotient.** Oriented Calderon--Witt source cohomology has one absolute
   quotient, and boundary-blind consumers factor through its normalized orientation trace.
2. **Positive transverse Stokes form.** The Stokes Cartan form is positive coarea plus one scalar
   rank update and is strictly positive on the kernel of that rank functional. Therefore negative
   inertia plus nullity is at most one.
3. **Central holonomy port.** The same Stokes rank functional is the exponent of the sole central
   determinant channel.
4. **External arithmetic displacement.** Reflection gives
   \[
   \delta_n(s)=e^{(2\operatorname{Re}s-1)\log n},
   \qquad
   \log\det\operatorname{Hol}
   =(2\operatorname{Re}s-1)\log n\,M(x).
   \tag{6.1}
   \]

The exact corpus product is therefore

\[
 \boxed{\text{external signed displacement }\kappa
 \times\text{ internal rank port }M,}
 \qquad
 \kappa=2\operatorname{Re}\rho-1.
 \tag{6.2}
\]

What is not proved is a canonical source-covariant identification

\[
 O^\vee\cong\operatorname{span}(M)\cong\operatorname{span}(\kappa).
 \tag{6.3}
\]

Without `(6.3)`, the one-port conjunction is a synthesis, not a new unification theorem.

## 7. Component countermodel

Connectedness is load-bearing. With two independent ports, take

\[
 V=\mathbb R^2,
 \qquad P=x^2+y^2,
 \qquad M_1=x,
 \qquad M_2=y,
\]

and

\[
 Q=P-2M_1^2-2M_2^2=-x^2-y^2.
\]

There are two negative directions. Thus one-time behavior can only follow from a theorem that the
completed interaction/channel graph is connected or has rank-one invisible center.

The abstract orientation split also supplies no metric. Taking `A_2=B direct-sum R` with the
obvious projection and section satisfies Theorem 2.1 while distinguishing no inner product or
quadratic form. Metric is additional realization data.

## 8. Predictions and open field equations

### Prediction 1 — temporal rank equals invisible-center rank

For a completed heterogeneous relation atlas, the number of possible nonpositive directions is
bounded by rank of its channel-invisible center sheaf. Connected fusion gives at most one time
port; `b` completed components give at most `b`.

### Prediction 2 — coframe-before-metric equivalence

A source-covariant realization functor canonically identifies `(6.3)` before choosing `P`.
Every admissible metric is then a positive transverse form plus a quadratic expression in this
coframe. Two provenance-preserving realizations producing nonproportional ports falsify the
conjecture.

### Prediction 3 — source field equation

There is a pre-divisor provenant boundary operator

\[
 \partial_{\mathrm{src}}:C^{\mathrm{prov}}_2\longrightarrow O
 \tag{8.1}
\]

whose transported value is `kappa`, and an arithmetic source relation forces
`partial_src=0`. Positive Lorentz energy is only the quadratic shadow
`||partial_src||^2`. This is the missing dynamics, not a proved theorem.

## 9. Fatal limits

This card does not imply:

1. a canonical metric from the orientation quotient;
2. canonical identification `(6.3)`;
3. Lorentz phase for every source;
4. a preferred future sheet;
5. causal dynamics, geodesics, an Einstein equation, or physical time;
6. a black-hole surface, wormhole interior, or holographic duality;
7. source selection, `kappa=0`, or RH;
8. abstract novelty beyond rank-one inertia theory.

## 10. Lean handoff notes

No Lean code was written or built. Later formalization can split the algebraic direct-sum theorem
from the finite-dimensional real inner-product rank-one inertia theorem. Corpus instantiation and
source-covariant identification `(6.3)` must remain separate conjectural interfaces.
