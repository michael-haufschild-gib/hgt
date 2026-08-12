# Positive-formation bi-axis logarithmic-work properness law

- **ID:** ULF-RFTM-3B
- **Stage:** 3 — formalized in Lean
- **Type:** THEOREM / GLOBAL FORMATION PROPERNESS / TWO-AXIS SELECTION GATE
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [EXACT BI-AXIS PROPERNESS]`
  `[REFLECTION-CENTRE RIGIDITY] [NOT RH]`

## 1. Mathematical delta

ULF-RFTM-3A reconstructs every ordered positive reciprocal packet as

\[
 (X,Y)=(RQR,RQ^{-1}R)
\]

and proves that functional-equation exchange fixes `R` and sends `Q` to `Q^{-1}`.  That theorem is
information-neutral and therefore cannot select the reflection centre.

The correct properness mechanism is not one scalar work.  The global chart has two independent
amplification axes:

- formation depth amplifies `R` and leaves recovered relative law unchanged;
- reciprocal depth amplifies `Q` and leaves recovered midpoint unchanged.

Their exact work vector is

\[
 \boxed{\mathcal W_{a,b}(R,Q)
   =\bigl(2a\|\log R\|_{HS},\;b\|\log Q\|_{HS}\bigr).}
 \tag{PFP.1}
\]

Joint boundedness selects the unique neutral packet `(R,Q)=(I,I)`.  Midpoint properness alone would
select only `R=I` and miss the functional-equation coordinate; the second axis is load-bearing.

## 2. Setup

Let `P_n` be the cone of positive-definite Hermitian complex matrices.  Fix `R,Q in P_n`.  For
`a,b in N`, define

\[
 X_{a,b}=R^a Q^b R^a,
 \qquad
 Y_{a,b}=R^a Q^{-b}R^a.
 \tag{PFP.2}
\]

Let `#` denote the unique positive Riccati midpoint from ULF-RFTM-3A.  Define

\[
 M_{a,b}=X_{a,b}\#Y_{a,b},
 \qquad
 \widehat Q_{a,b}=\operatorname{RecQ}(X_{a,b},Y_{a,b}),
 \tag{PFP.3}
\]

and Hilbert--Schmidt log works

\[
 W^R_{a,b}=\|\log M_{a,b}\|_{HS},
 \qquad
 W^Q_{a,b}=\|\log\widehat Q_{a,b}\|_{HS}.
 \tag{PFP.4}
\]

The same proof works for any definite absolutely homogeneous norm; Hilbert--Schmidt norm is fixed so
the paper and Lean statement coincide exactly.

## 3. Exact two-axis reconstruction

### Theorem 3.1 — midpoint and relative-law amplification

For every `a,b in N`,

\[
 \boxed{M_{a,b}=R^{2a},\qquad \widehat Q_{a,b}=Q^b.}
 \tag{PFP.5}
\]

Consequently,

\[
 \boxed{W^R_{a,b}=2a\|\log R\|_{HS},\qquad
        W^Q_{a,b}=b\|\log Q\|_{HS}.}
 \tag{PFP.6}
\]

### Proof

Positive natural powers remain positive definite.  Apply ULF-RFTM-3A's reconstruction theorem to
formation factor `R^a` and relative law `Q^b`:

\[
 X_{a,b}\#Y_{a,b}=R^aR^a=R^{2a},
 \qquad
 \operatorname{RecQ}(X_{a,b},Y_{a,b})=Q^b.
\]

Positive continuous functional calculus gives

\[
 \log(R^{2a})=(2a)\log R,
 \qquad
 \log(Q^b)=b\log Q.
\]

Hilbert--Schmidt homogeneity proves `(PFP.6)`. QED.

### Corollary 3.2 — exact decoupling

`W^R` is independent of `Q` and `b`; `W^Q` is independent of `R` and `a`.  Thus the work vector
reconstructs the two amplification rates without commutativity of `R` and `Q`.

## 4. Global properness

### Theorem 4.1 — separate axis rigidity

\[
 \boxed{
 (\exists C\;\forall a,b,\;W^R_{a,b}\le C)\iff R=I,}
 \tag{PFP.7}
\]

\[
 \boxed{
 (\exists C\;\forall a,b,\;W^Q_{a,b}\le C)\iff Q=I.}
 \tag{PFP.8}
\]

### Proof

If `R=I` or `Q=I`, the corresponding work vanishes.  Conversely, suppose
`d_R=||log R||_{HS}>0`.  Archimedean unboundedness gives `a` with `2a d_R>C`, contradicting
`(PFP.6)`.  Hence `d_R=0`, so `log R=0`.  Since `exp(log R)=R`, one gets `R=I`.  The proof for
`Q` is identical using `b d_Q`. QED.

### Theorem 4.2 — bi-axis properness capstone

\[
 \boxed{
 \begin{aligned}
 &\bigl(\exists C_R\;\forall a,b,\;W^R_{a,b}\le C_R\bigr)\\
 &\quad\land
 \bigl(\exists C_Q\;\forall a,b,\;W^Q_{a,b}\le C_Q\bigr)
 \end{aligned}
 \iff (R,Q)=(I,I).}
 \tag{PFP.9}
\]

This is the exact global formation/properness law missing from information-neutral packet recovery.

## 5. Functional-equation meaning

Packet exchange is conjugate under recovery to

\[
 \tau:(R,Q)\longmapsto(R,Q^{-1}).
 \tag{PFP.10}
\]

Therefore:

- formation work is fixed because `R` is fixed;
- the relative axis is the functional-equation displacement coordinate;
- information-neutrality retains that coordinate;
- properness, not symmetry, selects its centre `Q=I`;
- full packet neutrality requires both independent boundedness laws.

This separates two mechanisms that earlier one-scalar proposals conflated:

\[
 \boxed{\text{reversible functional-equation transport}\ne
        \text{properness-based selection}.}
 \tag{PFP.11}
\]

## 6. Hostile audit

1. **Ingredient parents.** Matrix geometric means, positive functional calculus, and linear escape of
   logarithmic rays are classical.  Status remains `[BRIDGE]`; no priority claim is made.
2. **Why this is not the old midpoint theorem.** Midpoint work alone cannot see `Q`.  The recovered
   relative work closes that exact blind spot and selects the reflection centre.
3. **No commutativity premise.** Congruence formation handles arbitrary positive `R,Q`; all
   noncommutativity is absorbed by exact recovery before logarithmic work is measured.
4. **No RH claim.** An RH consequence still requires a pre-zero source realization into this chart
   and a source theorem proving both complete work axes bounded.  Neither is assumed here.
5. **Finite-dimensional boundary.** Infinite/cofinal amplification needs a chosen topology and
   strict functional calculus.  Boundedness, compactness, and domain admission separate there.
6. **Determinant work is insufficient.** `|tr log R|` and `|tr log Q|` vanish on nontrivial
   determinant-one matrices.  Full matrix log norm is load-bearing.
7. **No scalar collapse.** The two coordinates can vary independently; boundedness on one axis says
   nothing about the other.  This is exactly why the field needs a vector-valued properness law.

## 7. Gates

- [x] 0 -> 1: exact bi-axis claim; scalar and one-axis falsifiers recorded
- [x] 1 -> 2: dependency-closed reconstruction, log scaling, and Archimedean proof
- [x] 2 -> 3: exact Lean theorem package, axiom audit, and umbrella wiring
- [ ] 3 -> 4: cofinal source realization and two-axis boundedness theorem

## Log

- 2026-08-12 — proved midpoint-axis properness.
- 2026-08-12 — hostile correction: midpoint axis is not functional-equation displacement.  Added
  recovered relative-law axis and proved joint properness selects `(R,Q)=(I,I)`.
- 2026-08-12 — formalized exact Hilbert--Schmidt theorem package in
  `ConstitutivePositiveFormationProperness.lean`; axiom audit clean modulo mathlib foundations.
