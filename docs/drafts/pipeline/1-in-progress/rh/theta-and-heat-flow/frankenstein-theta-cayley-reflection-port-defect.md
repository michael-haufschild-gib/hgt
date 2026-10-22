# Frankenstein theta-Cayley reflection port defect

- **Status:** paper proof complete; Lean formalization in progress
- **Role:** hostile pivot from proposed outgoing-to-incoming Cayley telescope
- **Inputs:** compact theta source inverse, direct Cayley clock, rank-two pinned boundary ports,
  functional-equation reflection
- **Axioms:** none

## Conjecture attacked

Let

\[
 X=icB,\qquad R=(1-X)^{-1},\qquad U=(1+X)R,
\]

where (B) is the fixed compact theta source inverse.  The tempting source-passivity conjecture
was that, on the canonical source orbit, the outgoing port at one Cayley step becomes the incoming
port at the next step.  Such a law would telescope the singular Green identity and could make the
already-proved observed Cayley growth criterion source-subexponential.

This conjecture is false on every noncritical Xi eigenline.  The failure is not arbitrary: it has
an exact reflection-covariant normal form.

## Exact theorem

For a multiplicity-exact Xi divisor copy (q), write

\[
 Xv_q=x_qv_q,\qquad Uv_q=k_qv_q,\qquad
 k_q=\frac{1+x_q}{1-x_q},
\]

and define the resolved (n)-th orbit mode and its port defect by

\[
 g_{q,n}=RU^nv_q,
 \qquad
 D_n(q)=\|\operatorname{in}(g_{q,n})\|^2-
        \|\operatorname{out}(g_{q,n})\|^2.
\]

Then, unconditionally,

\[
 g_{q,n}=k_q^n(1-x_q)^{-1}v_q,
\]

and

\[
 D_n(q)=
 \left\|k_q^n(1-x_q)^{-1}\right\|^2
 \bigl(2M_\theta\,\operatorname{Im}z_q\,E_q\bigr).
\]

All factors except (operatorname{Im}z_q) are strictly positive.  Consequently

\[
 D_n(q)=0\iff \operatorname{Im}z_q=0
 \iff \operatorname{Re}\rho_q=\tfrac12,
\]

and the sign of (D_n(q)) is exactly the retained horizontal orientation.

Functional-equation reflection (q\mapsto q^R) gives

\[
 x_{q^R}=-x_q,\qquad k_{q^R}=k_q^{-1},\qquad F(q^R)=-F(q).
\]

Therefore the two same-time defects obey the coefficient-faithful weighted annihilation law

\[
 D_n(q)+|k_q|^{4n+2}D_n(q^R)=0.
\]

Equivalently, reflection sends the bilateral Cayley time (n) to (-n-1).  The fixed time is
(-\tfrac12), not an integer time.  This half-step displacement is the exact obstruction hidden
by the informal “two orientations should cancel” argument.

## Paper proof

1. Since (1-X) is a unit and (Xv_q=x_qv_q), the inverse-eigenline identity gives
   (Rv_q=(1-x_q)^{-1}v_q).
2. Since (Uv_q=k_qv_q), induction gives (U^nv_q=k_q^nv_q); linearity of (R) gives the
   displayed formula for (g_{q,n}).
3. Both pinned ports are linear.  Hence their squared-norm difference on (c v_q) is
   (|c|^2) times their difference on (v_q).
4. The existing rank-two theta boundary identity identifies the latter difference with
   (2M_\theta\operatorname{Im}z_qE_q), where (M_\theta>0) and (E_q>0).
5. Reflection negates the unsquared theta eigenvalue and boundary flux.  Thus it negates (x_q),
   inverts (k_q), and replaces (|1-x_q|) by
   (|1+x_q|=|k_q|\,|1-x_q|).  Substitution gives
   (D_n(q^R)=-|k_q|^{-2n-2}|1-x_q|^{-2}F(q)), while
   (D_n(q)=|k_q|^{2n}|1-x_q|^{-2}F(q)).  Multiplying the first identity by
   (|k_q|^{4n+2}) proves weighted annihilation.

## Falsification result and pivot

- **Failed:** unweighted same-time port cancellation, next-in/previous-out shift, and ordinary
  integer-time Green telescoping.  On a Xi eigenline each would force (D_n(q)=0), hence the
  critical line.
- **Survivor:** exact positive coefficient (|k_q|^{4n+2}) and reflection time reversal
  (n\leftrightarrow -n-1).
- **New producer target:** construct a source-native half-step transport (U^{-1/2}), or an
  equivalent coefficient-neutralizing density, *before* divisor scalarization.  It must turn the
  forced weighted annihilation into equal-coefficient annihilation while retaining prime labels,
  multiplicity, and both reflection orientations.  Any theorem merely assuming
  (|k_q|^{4n+2}=1) is circular, since that is already critical-line placement.

## Lean target

New module:
`GaloisForLFunctions.RHTower.HedenmalmThetaDirectCayleyReflectionPortDefect`.
It will formalize port linearity, resolved orbit normal form, exact defect formula, sign/zero
classification, reflection multiplier inversion, and weighted same-time annihilation.
