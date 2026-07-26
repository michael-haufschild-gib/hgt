# Character-chart cochains used directly as a coefficient sheaf

- **ID:** `deninger-chart-cochains-as-coefficient-sheaf`
- **Stage:** 5-failed
- **Type:** RETIRED TYPE ERROR
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`

## Retired construction

Treat the chartwise \(E_\infty\)-algebra
\[
 C^*_{\mathrm{sh}}(X_F;\mathbb R)
 \otimes_{\mathcal P_{F,\mathbb R}}^{\mathbb L}
 \mathcal K^M_{F,\mathbb R}
\]
as a coefficient sheaf or a geometric stalk on Deninger's rational-Witt
flow space, then apply \(Rj_*^G\) to it.

## Failure

The displayed algebra is a derived **global-section** object on a character
component.  It is not a sheaf and is not a stalk.  Deninger already defines
the relevant starting sheaf on a suspension
\[
 \pi:\widetilde X=M\times\mathbb R_{>0}\longrightarrow
 X=M\times_Q\mathbb R_{>0}
\]
by
\[
 \mathcal R_X=(\pi_*\mathcal R_{\widetilde X})^Q,
\]
where sections of \(\mathcal R_{\widetilde X}\) are continuous in the
transverse variable and locally constant in the leaf variable.  His
leafwise cohomology is
\[
 H^\bullet_{\mathcal F}(X)=H^\bullet(X,\mathcal R_X).
\]

Replacing \(\mathcal R_X\) by its global cochain algebra before constructing
descent loses restriction maps, local residue data, sheaf extension
classes, and the distinction between local amplitude and derived global
amplitude.  The expression \(Rj_*^G\) is not defined on a bare global
cochain algebra.

## Positive survivor

Perform unit amalgamation inside commutative algebra objects in the derived
category of sheaves over \(\mathcal R_X\).  The Kummer classes define a map
from the free sheaf \(E_\infty\)-algebra on the degree-one unit local system,
and the motivic symbol map defines its second leg.  Their derived pushout is
the genuine geometric coefficient sheaf.  Only afterward take derived
global sections.

This construction is recorded in
`deninger-leafwise-sheafified-unit-amalgamation`.

## No-go closure

The chartwise cochain algebra remains useful: it is the expected value of
derived global sections and is the object to which real shape formality
applies.  Thus it survives as a comparison target, not as a sheaf or stalk.

**Verdict:** `FAILED; SHEAFIFIED POSITIVE SURVIVOR IDENTIFIED`.
