# Coefficient-lift transgression: central history to higher coherence

- **ID:** ULF-CRT-2
- **Stage:** 2-fully-proven
- **Type:** CROSS-MODE LAW-GENESIS THEOREM
- **Statement:** A coarse coefficient-valued binary history cocycle lifts to a strict refined
  history law exactly when its canonical kernel-valued ternary transgression vanishes in
  cohomology.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [CENTRAL-TO-HIGHER EXCHANGE] [CONVERSE] [LEAN-CERTIFIED] [NOT RH]

## 1. Coefficient refinement

Let `M` be an additive monoid and let

\[
 0\longrightarrow K\xrightarrow{i}A\xrightarrow{q}B\longrightarrow0
 \tag{CLT.1}
\]

be a short exact sequence of additive abelian groups.  For a binary cochain
`kappa:M x M -> C`, write

\[
 (\delta\kappa)(x,y,z)
 =\kappa(x,y)+\kappa(x+y,z)-\kappa(y,z)-\kappa(x,y+z).
 \tag{CLT.2}
\]

Assume `kappa_B:M x M -> B` is closed:

\[
 \delta\kappa_B=0.
 \tag{CLT.3}
\]

Choose any pointwise lift `kappa_A:M x M -> A` with `q kappa_A=kappa_B`.

## 2. Forced higher law

### Theorem 2.1 -- coefficient-lift transgression

There is a unique ternary cochain `h:M^3->K` satisfying

\[
 i h=\delta\kappa_A.
 \tag{CLT.4}
\]

It obeys the pentagon identity

\[
\begin{aligned}
 &h(w,x,y)+h(w,x+y,z)+h(x,y,z)\\
 &\qquad=h(w+x,y,z)+h(w,x,y+z).
\end{aligned}
\tag{CLT.5}
\]

Hence failed coefficient lift produces a coherent ternary law without postulating one.

### Proof

Naturality of `(CLT.2)` gives

\[
 q(\delta\kappa_A)=\delta(q\kappa_A)=\delta\kappa_B=0.
\]

Exactness of `(CLT.1)` places every value of `delta kappa_A` in `im i`; injectivity of `i` gives
unique `h`.  Apply `i` to the difference between both sides of `(CLT.5)`.  It becomes the pentagon
identity `delta^2 kappa_A=0`.  Injectivity reflects equality.  QED.

## 3. Lift independence

### Theorem 3.1

If `kappa_A'` is another lift, there is a binary `K`-cochain `beta` such that

\[
 \kappa_A'=\kappa_A+i\beta.
 \tag{CLT.6}
\]

If `h'` is its ternary defect, then

\[
 \boxed{h'=h+\delta\beta.}
 \tag{CLT.7}
\]

Therefore the class

\[
 [h]\in Z^3(M;K)/\delta C^2(M;K)
 \tag{CLT.8}
\]

is independent of the chosen lift.

### Proof

The difference `kappa_A'-kappa_A` lies pointwise in `ker q=im i`; injectivity gives `(CLT.6)`.
Apply `delta`, use additivity and `(CLT.4)`, then cancel `i` by injectivity.  QED.

## 4. Strictification converse

### Theorem 4.1 -- exact mode-conversion criterion

The following are equivalent:

1. `[h]=0`;
2. there is a binary `K`-cochain `beta` with `h+delta beta=0`;
3. `kappa_B` admits an `A`-valued cocycle lift.

### Proof

The first two statements are the definition of vanishing in `(CLT.8)`.  If
`h+delta beta=0`, then `kappa_A+i beta` still lifts `kappa_B` and

\[
 \delta(\kappa_A+i\beta)=i(h+\delta\beta)=0.
\]

Conversely, compare any cocycle lift with `kappa_A` as in `(CLT.6)` and apply `(CLT.7)`.  QED.

This is the cross-mode mechanism:

\[
 \boxed{
 \text{coarse central history}
 \xrightarrow{\text{failed coefficient lift}}
 \text{fine higher coherence}.}
 \tag{CLT.9}
\]

The higher class is zero exactly when the conversion can be reversed to a strict refined binary
law.

## 5. Split boundary

### Corollary 5.1

If `q` has an additive section `s:B->A`, then every `B`-valued cocycle has the cocycle lift
`s kappa_B`, so every transgression class vanishes.

### Proof

Additivity gives `delta(s kappa_B)=s(delta kappa_B)=0`, and `qs=id`.  QED.

Thus coefficient refinement alone is not enough.  Nonsplitness or a stricter admission law is
load-bearing.

## 6. Finite nonliftable laboratory

Let

\[
 G=(\mathbb Z/2)^2,
 \quad K=B=\mathbb Z/2,
 \quad A=\mathbb Z/4,
\]

with `i(1)=2` and `q` reduction modulo two.  Define

\[
 \kappa_B(x,y)=x_1y_2.
 \tag{CLT.10}
\]

This is bilinear, hence a cocycle.  Let `kappa_A` be its binary-digit lift with values `0,1`.
For

\[
 e_1=(1,0),\qquad e_2=(0,1),
\]

direct substitution gives

\[
 (\delta\kappa_A)(e_1,e_2,e_2)=2,
 \qquad h(e_1,e_2,e_2)=1.
 \tag{CLT.11}
\]

### Theorem 6.1 -- the higher class is nonzero

No `Z/4`-valued cocycle lifts `(CLT.10)`.

### Proof

For any additive-group cocycle `alpha` and any element `x` with `2x=0`, the cocycle equations at
`(0,0,y)`, `(y,0,0)`, `(x,x,y)`, `(x,y,x)`, and `(y,x,x)` imply

\[
 2\bigl(\alpha(x,y)-\alpha(y,x)\bigr)=0.
 \tag{CLT.12}
\]

If `alpha` lifted `(CLT.10)`, its commutator at `(e_1,e_2)` would reduce modulo two to `1`.
It would therefore be odd in `Z/4`, so twice it would equal `2`, contradicting `(CLT.12)`.  QED.

By Theorem 4.1, `[h]` is nonzero.  The higher law is unavoidable for every fine lift, not an
artifact of the binary-digit section.

## 7. Second laboratory: linear exactness

Take the two-term coefficient complex

\[
 A\xrightarrow{d_A}A,
 \qquad d_A(a)=2a,
\]

with quotient `B=Z/2`, where the induced differential is zero, and kernel `K=Z/2`, also with zero
differential.  The coarse element `1 in B` is closed.  Every lift is odd in `Z/4`, hence has
differential `2`, so no closed lift exists.  Its connecting class is `1 in K`.

This is the same law of law genesis without multiplication, extensions of groups, or associativity.

## 8. Withheld predictions

1. A quotient observer may report a complete associative history law while every coefficient-fine
   realization necessarily carries ternary coherence.
2. Unary recalibration cannot remove the obstruction; it changes only its representative by a
   ternary coboundary.
3. Any claimed fine strictification must either kill `[h]`, split the coefficient extension, change
   admission, or erase the coarse cocycle.
4. In a refinement tower, first nonzero connecting class predicts first arity at which strict law
   execution fails.

The first three are proved here.  The tower statement is the next programme theorem.

## 9. Hostile conjecture loops

1. **Coarse cocycle always lifts as a cocycle.** False by Theorem 6.1.
2. **Nonzero associator is only bad splitting.** False: `(CLT.7)` and Theorem 4.1 isolate a
   splitting-independent class.
3. **Higher coherence must be separately supplied.** False in this sector: `(CLT.4)` produces it.
4. **Every coefficient refinement produces higher law.** False for split refinements.
5. **Nonzero class forbids all repair.** False: it forbids strict `A`-valued binary lift; a higher
   promotion, changed coefficient doctrine, or controlled erasure remains possible.
6. **This proves universal ULF dynamics.** False: it closes one cross-mode exchange law only.

## 10. Scope and parent mathematics

The theorem is the low-degree connecting homomorphism for a short exact coefficient sequence,
reinterpreted as law genesis.  Degree-two cohomology/central extensions and degree-three
2-group obstructions are classical.  Modern parents include
[Rumynin--Vakhrameev--Westaway](https://arxiv.org/abs/1709.09728),
[Ionescu--Kumjian](https://arxiv.org/abs/1612.07257), and
[Joshi--Spallone](https://arxiv.org/abs/2307.14658).

No topology, positivity, completion, physical model, proof route, or RH conclusion is asserted.

## Lean certification

Module `GaloisForLFunctions.HTGeometry.ConstitutiveCoefficientLiftTransgression` certifies:

1. existence and pentagon coherence of the kernel-valued higher defect;
2. correction formula and strict-lift equivalence;
3. lift-independence up to ternary coboundary;
4. split-coefficient vanishing boundary;
5. explicit `((Z/2)^2,Z/4,Z/2)` cocycle, nonzero lift associator, and no-cocycle-lift theorem;
6. structurally different two-term linear no-lift theorem;
7. one unconditional closed capstone.

No `sorry`, `admit`, project axiom, `opaque`, `unsafe`, or computational certificate is used.

## Log

- 2026-08-10 -- coefficient lift failure identified as exact central-history-to-higher-coherence
  conversion; converse, split boundary, finite nonzero cell, and linear validation closed.
- 2026-08-10 -- full significant core certified in Lean and wired into ULF umbrella.
