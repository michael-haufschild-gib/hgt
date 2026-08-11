# Mixed inverse-response Riccati reconstruction and Ward conservation law

**Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [DEPENDENCY-CLOSED] [UNIVERSAL-LAW-FIELD] [PRE-RH]`

## 1. Setup

Let `R` and `A` be commutative rings, let `A` be an `R`-algebra, and let

\[
 D_1,D_2:A\longrightarrow A
\]

be `R`-derivations.  Let `E,M in A` satisfy

\[
  ME=1.                                                    \tag{1}
\]

For any derivation `D`, define its inverse-formed logarithmic current by

\[
  \Theta_D(M,E):=M\,D(E).                                  \tag{2}
\]

Write `Theta_i=Theta_(D_i)(M,E)`.

## 2. Inverse response

### Theorem 2.1 — derivative of the inverse formation

For `i=1,2`,

\[
  D_i(M)=-M\Theta_i=-M^2D_i(E).                            \tag{3}
\]

#### Proof

Apply `D_i` to `(1)`.  Since a derivation kills `1`, Leibniz gives

\[
  D_i(M)E+M D_i(E)=0.                                      \tag{4}
\]

Multiply by `M`.  Commutativity and `ME=EM=1` give

\[
  D_i(M)+M^2D_i(E)=0.
\]

Rearrange and use `(2)`. ∎

## 3. Mixed Riccati law and reconstruction

### Theorem 3.1 — mixed inverse-response law

For every ordered pair `(D_1,D_2)`,

\[
  \boxed{D_1(\Theta_2)+\Theta_1\Theta_2=M D_1D_2(E).}       \tag{5}
\]

No commutation hypothesis on `D_1,D_2` is needed.

#### Proof

Differentiate `(2)` for `Theta_2` by `D_1`:

\[
\begin{aligned}
 D_1(\Theta_2)
 &=D_1(M)D_2(E)+M D_1D_2(E)\\
 &=-M^2D_1(E)D_2(E)+M D_1D_2(E)\\
 &=-\Theta_1\Theta_2+M D_1D_2(E),
\end{aligned}
\]

using Theorem 2.1 and commutativity.  Rearrangement gives `(5)`. ∎

### Corollary 3.2 — exact mixed-acceleration reconstruction

Multiplying `(5)` by `E` gives

\[
  \boxed{D_1D_2(E)=E\bigl(D_1(\Theta_2)+\Theta_1\Theta_2\bigr).} \tag{6}
\]

Thus the formed two-current packet reconstructs the mixed source acceleration exactly.

### Corollary 3.3 — diagonal Riccati law

For one derivation `D` and `Theta=M D(E)`,

\[
  D(\Theta)+\Theta^2=M D^2(E).                             \tag{7}
\]

If `D^2(E)=0`, then `D(Theta)=-Theta^2`.

## 4. Affine source experiments and Ward conservation

### Theorem 4.1 — exact product boundary

If

\[
  D_1D_2(E)=0,                                             \tag{8}
\]

then

\[
  \boxed{\Theta_1\Theta_2=-D_1(\Theta_2).}                 \tag{9}
\]

This follows immediately from `(5)`.

### Theorem 4.2 — Ward conservation

Let `B` be an additive commutative group and let `tau:A ->+ B` be an additive reporter satisfying

\[
  \tau(D_1x)=0\qquad(x\in A).                              \tag{10}
\]

Under `(8)`,

\[
  \boxed{\tau(\Theta_1\Theta_2)=0.}                        \tag{11}
\]

#### Proof

By `(9)` and additivity,

\[
  \tau(\Theta_1\Theta_2)=\tau(-D_1\Theta_2)
  =-\tau(D_1\Theta_2)=0.
\]

∎

### Corollary 4.3 — faithful positive selection schema

Assume `D_1=D_2=D`, `D^2E=0`, and that the reporter has the faithful-square property

\[
  \tau(x^2)=0\Longrightarrow x=0.                          \tag{12}
\]

Then `Theta_D(M,E)=0`.

#### Proof

Theorem 4.2 gives `tau(Theta^2)=0`; apply `(12)`. ∎

The hypothesis `(12)` is deliberately explicit.  Positivity is not manufactured by the algebraic
identity.

### Theorem 4.4 — anomalous Ward balance

Let `tau,beta:A ->+ B` be additive maps into an additive commutative group and assume

\[
  \tau(D_1x)=\beta(x)\qquad(x\in A).                        \tag{13}
\]

Then

\[
 \boxed{\tau(\Theta_1\Theta_2)
 =\tau(MD_1D_2E)-\beta(\Theta_2).}                          \tag{14}
\]

Apply `tau` to `(5)`, use `(13)`, and rearrange.  Under mixed affinity this becomes

\[
 \tau(\Theta_1\Theta_2)=-\beta(\Theta_2).                  \tag{15}
\]

### Theorem 4.5 — strict-trace grade blindness

Let `K` be a field, let `A` be a commutative `K`-algebra, let `D` be a `K`-derivation, and let
`tau:A ->_K K` be linear with `tau(Dx)=0` for every `x`.  If

\[
  Dx=w x,\qquad w\ne0,                                     \tag{16}
\]

then `tau(x)=0`.

#### Proof

`0=tau(Dx)=tau(wx)=w tau(x)`; divide by the nonzero field element `w`. ∎

For a logarithmic grading derivation, every positive grade has nonzero weight.  A strict invariant
linear reporter is therefore grade-zero-supported and cannot be the missing prime-labelled Hodge
reporter.  The arithmetic search must target `(14)`, not only `beta=0`.

## 5. Exact obstruction and countermodels

1. **Non-affine experiment.**  For `A=R[x]`, `E=1+x^2`, and `D=d/dx` on any localization where
   `E` is invertible, `D^2E=2`.  Equation `(7)` has the nonzero acceleration term `2M`; the square is
   not a total derivative.
2. **Reporter not conservative.**  Evaluation at a point need not kill derivatives, so `(11)` can
   fail even when `(9)` holds.
3. **Nonfaithful reporter.**  The zero reporter satisfies `(10)` and `(11)` for every current but
   selects nothing.
4. **Unrelated currents.**  Two arbitrary elements of `A` need not be currents of one common
   inverse formation, so `(5)` does not apply.
5. **Order matters without commuting derivations.**  The reverse law contains `D_2D_1(E)`.  Their
   difference is the derivation commutator applied to `E`; no false symmetry is asserted.
6. **Exponential source formation.**  For `E(t)=exp(lambda t)`, `M=E(t)^{-1}` and `D=d/dt`, one has
   `Theta=lambda`, `D Theta=0`, and `M D^2E=lambda^2=Theta^2`.  The Riccati law is exact but does not
   imply vanishing.  Literal Euler characters are log-affine, not affine.

## 6. Fourth-organ prediction

Suppose a realization functor sends the source experiment to a positive receiver and carries
`Theta_1 Theta_2` to a nonnegative mixed Fisher/Hodge density.  Equation `(14)` predicts its exact
integrated value in that fourth organ: **source acceleration trace minus boundary anomaly**.  If
those terms balance, total positive density vanishes and a faithful receiver annihilates the
realized current.

This is a theorem schema with fully exposed hypotheses, not an RH claim.  It predicts a new
identity in any fourth organ realizing the same experiment: its integrated mixed response is the
image of one explicit source acceleration/anomaly balance.

## 7. Frontier interface

The RH corpus already contains a two-component reflection-odd source carrier and a positive
reflection-even Hodge product whose total vanishing is equivalent to RH.  The present theorem says
exactly what additional source mechanism would force that vanishing: common inverse formation and
a pre-zero identification of Hodge mass with the anomalous Ward balance.  The grade-blindness
theorem rules out a strict logarithmic invariant trace; the live gate is equality of source
acceleration and boundary anomaly.  No arithmetic realization is smuggled into this card.

## 8. Formalization

Equations `(3)`, `(5)`, `(6)`, `(7)`, `(9)`, `(11)`, `(14)`, `(15)`, strict-trace grade blindness,
the faithful-square selection schema, and one closed capstone are formalized in
`GaloisForLFunctions.HTGeometry.InverseResponseWardMechanics` and imported by the universal-law
field umbrella.
