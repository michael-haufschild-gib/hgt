# Differential Rees formation number, reflection, and hypertranscendental gauge escape

**Card ID:** ULF-TAFM-25  
**Status:** Formalized in Lean 4  
**Programme:** Universal law field / topologically admitted formation mechanics  
**Field candidate:** Differential Hopf--Rees formation geometry  
**Scope:** Route-independent finite-history and differential-source mechanism

## 1. Result

Let

\[
  A=\mathbf Z[\mathbf Z]=\mathbf Z[T,T^{-1}],\qquad
  d=T-1,qquad I=(d),
\]

and let \(\iota(T)=T^{-1}\) be Laurent inversion.  There is a unique Laurent derivative
\(D=\partial_T\) determined by

\[
  D(aT^n)=naT^{n-1}.
\]

Define the **formation number connection**

\[
  N=dD=(T-1)\partial_T.
\]

The following laws hold.

1. **Exact grade law.** For every \(r\ge 0\) and \(P\in A\),

   \[
     N(d^rP)=r,d^rP+d^{r+1}D(P).                 \tag{1}
   \]

   Consequently, \(N\) acts by the integer \(r\) on \(I^r/I^{r+1}\).

2. **Exact reflection Jacobian.** For every \(P\in A\),

   \[
     D(\iota P)=-T^{-2}\iota(DP),                 \tag{2}
   \]

   and therefore

   \[
     N(\iota P)=T^{-1}\iota(NP).                  \tag{3}
   \]

3. **Associated-grade reflection compatibility.** If \(P\in I^r\), then

   \[
     N(\iota P)\equiv \iota(NP)\pmod{I^{r+1}}.    \tag{4}
   \]

   Thus formation number and functional-equation reflection are simultaneously visible on every
   grade: \(N\) has eigenvalue \(r\), while reflection has parity \((-1)^r\).

4. **Hypertranscendental gauge-escape law.** Let \(F\subset E\) be fields, let \(E\) carry a
   derivation \(\partial\), and choose a nonzero punctured-chart coordinate \(u\in E\).  Put

   \[
     N_u(x)=u\partial x.
   \]

   If a finite-dimensional \(F\)-linear state \(V\subset E\) is closed under both \(N_u\) and
   inverse gauge \(G_u(x)=u^{-1}x\), then it is closed under \(\partial\).  Hence it contains no
   element hypertranscendental over \(F\).

   Equivalently, if \(x\in V\) is hypertranscendental and \(V\) is finite-dimensional and
   \(N_u\)-stable, then

   \[
     \exists y\in V\quad u^{-1}y\notin V.         \tag{5}
   \]

Equation (5) is the positive theorem.  Hypertranscendence does not merely demand “many grades.”
It forces failure of a precise joint closure: finite formation evolution cannot coexist with
lossless reopening of the punctured gauge.

## 2. Why this is a new field mechanism rather than another route

The earlier augmentation tower supplied a common object for recovery, observer differences,
reflection parity, and recurrence residue.  It did not explain why hypertranscendence should be a
source of noncompactness.  Bare infinite augmentation support cannot do so: elementary rational or
differentially algebraic germs can have infinitely many nonzero Taylor coefficients.

The missing structure is a connection on the filtration.  The operator \(N=(T-1)\partial_T\)
measures formation order intrinsically.  It is neither a chosen route observable nor a new
positivity functional.  It is the infinitesimal generator of dilation normal to the augmentation
boundary.  Law (1) reconstructs filtration degree from dynamics.  Laws (2)--(4) show how the same
dynamics transforms under the functional equation.  Law (5) identifies exactly which finite-state
closure hypertranscendence destroys.

This produces the first defensible version of the requested slogan

> hypertranscendence is a source of noncompactness.

The word “noncompactness” here has a typed meaning: no finite-dimensional state containing the
source can be closed under both formation evolution and inverse-gauge recovery.  No equivalence
between hypertranscendence and generic infinite-dimensionality is asserted.

## 3. Proof of the Laurent derivative laws

Every Laurent polynomial is a finite sum

\[
  P=\sum_{n\in\mathbf Z} a_nT^n.
\]

Define

\[
  D(P)=\sum_n na_nT^{n-1}.
\]

The sum remains finite.  Additivity is immediate.  On monomials,

\[
\begin{aligned}
  D((aT^m)(bT^n))
    &=D(abT^{m+n})\\
    &=(m+n)abT^{m+n-1}\\
    &=(maT^{m-1})(bT^n)+(aT^m)(nbT^{n-1}).
\end{aligned}
\]

Finite additivity then gives the Leibniz rule

\[
  D(PQ)=D(P)Q+PD(Q).                               \tag{6}
\]

In particular \(D(d)=1\).  Induction using (6) gives

\[
  D(d^r)=r d^{r-1}.                                \tag{7}
\]

## 4. Proof of the exact grade law

Using (6) and (7),

\[
\begin{aligned}
  N(d^rP)
    &=dD(d^rP)\\
    &=d\bigl(rd^{r-1}P+d^rD(P)\bigr)\\
    &=r d^rP+d^{r+1}D(P).
\end{aligned}
\]

The correction belongs to \(I^{r+1}\).  Therefore on the associated grade

\[
  \operatorname{gr}_I^r(A)=I^r/I^{r+1}
\]

the induced endomorphism is multiplication by \(r\).  Formation order is thus spectral data of
\(N\); it is not an external label.

## 5. Proof of reflection covariance

It suffices to check a Laurent monomial.  For \(aT^n\),

\[
\begin{aligned}
  D\bigl(\iota(aT^n)\bigr)
    &=D(aT^{-n})\\
    &=-naT^{-n-1},
\end{aligned}
\]

whereas

\[
  -T^{-2}\iota\bigl(D(aT^n)\bigr)
    =-T^{-2}\iota(naT^{n-1})
    =-naT^{-n-1}.
\]

Additivity proves (2).  Since

\[
  \iota(d)=T^{-1}-1=-dT^{-1},
\]

we obtain

\[
\begin{aligned}
  T^{-1}\iota(NP)
    &=T^{-1}\iota(dD(P))\\
    &=T^{-1}(-dT^{-1})\iota(DP)\\
    &=-dT^{-2}\iota(DP)\\
    &=N(\iota P),
\end{aligned}
\]

which is (3).

If \(P\in I^r\), then \(NP\in I^r\) by (1), and inversion preserves \(I^r\).  Hence

\[
  N(\iota P)-\iota(NP)=(T^{-1}-1)\iota(NP)\in I^{r+1},
\]

proving (4).

Combining (1), (4), and the already proved associated-graded inversion law gives the joint spectral
table

\[
\begin{array}{c|cc}
  \text{grade} & N & \iota\\ \hline
  I^r/I^{r+1} & r & (-1)^r.
\end{array}
\]

The integer formation number and reflection orientation are two commuting shadows of one filtered
connection.

## 6. Differential Rees interpretation

The Rees algebra

\[
  \mathcal R_I(A)=\bigoplus_{r\ge0} I^r h^r
\]

records the full formation tower without collapsing adjacent orders.  Law (1) states that \(N\)
is the Euler connection on its associated graded.  In the completed boundary chart, write

\[
  u=T-1.
\]

Then \(N=u\partial_u\).  The punctured chart allows the inverse gauge \(u^{-1}\).  This pair is the
minimal mechanism needed to distinguish two notions that earlier formulations conflated:

- unbounded support in formation number;
- impossibility of a finite state closed under both evolution and gauge recovery.

Only the second is forced by hypertranscendence.

## 7. Proof of hypertranscendental gauge escape

Let \(V\subset E\) be closed under \(N_u\) and \(G_u\).  For \(x\in V\),

\[
  N_u(x)=u\partial x\in V.
\]

Applying inverse gauge gives

\[
  u^{-1}N_u(x)=u^{-1}u\partial x=\partial x\in V.
\]

Thus \(V\) is derivation-invariant.  If \(V\) is finite-dimensional, the first
\(\dim_F(V)+1\) derivatives of any \(x\in V\) are linearly dependent over \(F\).  That dependence is
a nonzero algebraic differential equation, so \(x\) is differentially algebraic over \(F\).
Therefore a hypertranscendental \(x\) cannot lie in such a state.

For the positive form, suppose \(x\in V\) is hypertranscendental and \(V\) is finite-dimensional
and \(N_u\)-stable.  If every \(y\in V\) also satisfied \(u^{-1}y\in V\), the preceding paragraph
would contradict hypertranscendence.  Hence some \(y\in V\) escapes under inverse gauge, proving
(5).

## 8. Fusion across route organs

This law uses one mechanism in four structurally different organs.

| Organ | Local expression | Universal meaning |
|---|---|---|
| finite recovery / packet formation | multiplication by \(d^r\) | Rees grade \(r\) |
| functional equation | Laurent inversion \(\iota\) | antipodal reflection with exact Jacobian |
| differential source / hypertranscendence | \(u\partial_u\) and \(u^{-1}\) | formation evolution versus lossless reopening |
| recurrence / observer closure | closed projected cycle with open lifted history | finite closure must lose inverse gauge when source is HT |

The fourth row is a prediction, not a retrospective analogy.  Any proposed finite recurrence
receiver for a hypertranscendental source that is closed under formation evolution must exhibit an
explicit inverse-gauge escape.  A construction claiming simultaneous finite closure under both
operations is impossible before any RH-specific estimate is considered.

## 9. Consequence for selection architecture

A final selection theorem cannot live entirely inside one finite state that is simultaneously

1. closed under formation evolution;
2. closed under inverse-gauge recovery;
3. faithful to a hypertranscendental source.

At least one closure must be weakened.  Recovery itself is information-neutral on finite Laurent
histories, so weakening recovery by quotienting would discard precisely the open history needed to
distinguish recurrence from periodicity.  The viable architecture is instead:

\[
  \text{completed open source state}
    \longrightarrow
  \text{closed observer quotient}
    \longrightarrow
  \text{positive selection}.
\]

The open state carries the inverse-gauge escape; the observer quotient may be recurrent and
positive.  Selection must prove properness of this projection on the RH-relevant constrained
sector, not compactness of the full hypertranscendental source state.

This narrows the global formation/properness problem.  Required theorem is no longer “make the
whole source compact.”  It is:

> prove the observer projection proper after quotienting exactly the inverse-gauge escape
> directions, while retaining adjacent-grade reflection polarization.

That statement is not proved here.  The present theorem proves why this asymmetric completion is
forced and supplies the exact escape direction that a candidate projection must control.

## 10. Lean certificate

Lean module:

`GaloisForLFunctions.HTGeometry.DifferentialReesFormationSpectrum`

Certified declarations:

- `laurentFormationDerivative_mul`
- `laurentFormationDerivative_unique`
- `laurentFormationDerivative_augmentationGenerator_pow`
- `augmentationFormationIdeal`
- `mem_augmentationFormationIdeal_pow_iff`
- `formationNumber_boundary`
- `formationNumber_associatedGrade`
- `laurentFormationDerivative_invert`
- `formationNumber_invert`
- `formationNumber_reflection_associatedGrade`
- `formationNumber_reflection_associatedGrade_of_mem`
- `differentialRees_jointGrade`
- `derivationInvariant_of_formationConnection_and_inverseGauge`
- `not_mem_finiteFormationState_of_hypertranscendentalOver`
- `exists_inverseFormationGauge_escape_of_hypertranscendentalOver`

The certificate is unconditional relative to its explicitly quantified algebraic structures and
contains no project axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration.

## 11. Boundary of the theorem

This card does not prove RH.  It does not prove the remaining observer-projection properness
theorem.  It does not identify hypertranscendence with infinite Taylor support, infinite dimension,
or noncompactness in an unspecified topology.

It proves a sharper mechanism:

\[
  \boxed{
  \text{finite }N_u\text{-closure}
  +\text{ inverse-gauge closure}
  \Longrightarrow
  \partial\text{-closure}
  \Longrightarrow
  \text{differential algebraicity}
  }
\]

and therefore

\[
  \boxed{
  \text{hypertranscendence}
  \Longrightarrow
  \text{inverse-gauge escape from every finite }N_u\text{-state}.
  }
\]

That is a route-independent law and a falsifiable design constraint on every future RH selection
architecture built from this field.

## 12. Stage-3 audit — 2026-08-31

Final exactness audit closed two omissions in the earlier certificate. The monomial rule now has a
uniqueness theorem for the Laurent derivative, and the conventional principal ideal
`I = (T - 1)` is represented explicitly, with `Q ∈ I^r` equivalent to order-`r` boundary
factorization. Reflection/formation compatibility is therefore available in the card's literal
arbitrary-membership form, not only for a displayed factorization. A joint-grade theorem records
the formation eigenvalue and reflection parity together.

Direct foreground elaboration and targeted
`lake build GaloisForLFunctions.HTGeometry.DifferentialReesFormationSpectrum` pass. Axiom audit of
the declarations added in this final sweep reports only `propext`, `Classical.choice`, and
`Quot.sound`. The module is explicitly imported by `GaloisForLFunctions.HTGeometry`; no umbrella
build was run.
