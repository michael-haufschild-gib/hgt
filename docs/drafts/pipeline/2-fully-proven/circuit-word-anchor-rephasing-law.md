# Circuit-word anchor rephasing law

- **ID:** `circuit-word-anchor-rephasing-law`
- **Stage:** 2 — fully proven on paper
- **Type:** deterministic circuit/recurrence bridge
- **Status:** `[PAPER-PROVED] [BRIDGE]`
- **Parent:** `lag-resolved-static-choi-shortcut-dichotomy-law.md`
- **Date:** 2026-08-07

## Failure-driven conjecture chain

`[FALSIFIED]` A static Krylov carrier could not separate a late shortcut from
an exact easy past target because carrier norm forgets lag.

`[PAPER-PROVED]` The lag-resolved shortcut dichotomy repairs this by
translating every target to its chosen orbit anchor and removing that anchor
component.

`[FALSIFIED]` Treating the translated residuals as a fixed target dictionary
is invalid.  The anchor may range continuously and depend on the Hamiltonian,
so direct targetwise replica bounds face an uncountable adaptive family.

The stronger replacement conjecture absorbs translation into the circuit
algebra before applying probability.

## Exact claim

Let \(G\) be a metric group whose multiplication is jointly one-Lipschitz in
the sum metric and whose inversion is an isometry.  Let a finite gate alphabet
\(\Gamma\) carry an inverse operation \(g\mapsto g^\dagger\) satisfying
\(U(g^\dagger)=U(g)^{-1}\).

If \(x\) has an \(s_x\)-gate approximation of error \(\epsilon_x\) and \(y\)
has an \(s_y\)-gate approximation of error \(\epsilon_y\), then

\[
 x^{-1}y
 \quad\hbox{has an}\quad
 (s_x+s_y)\hbox{-gate approximation of error }
 \epsilon_x+\epsilon_y.                                \tag{1}
\]

Consequently, if every early orbit point \(U(u)\), \(u\in A\), is
\(r\)-gate approximable with error \(\delta\), and every circuit target
\(V_w\) is \(s\)-gate approximable with error \(\epsilon\), then every
anchor-rephased target

\[
 U(u)^{-1}V_w,qquad (u,w)\in A\times W,                \tag{2}
\]

lies in the \((r+s)\)-word tube of radius \(\delta+\epsilon\).  Continuous
or adaptive anchor choice therefore creates no new target entropy beyond the
single enlarged finite word dictionary.

## Internal and external frontier

- `[CORPUS]` `circuitWordSeparated_autonomous_backward_cone` in
  `formal/GaloisForLFunctions/HTGeometry/AutonomousWordComplexityConeLaw.lean`
  transfers hardness backward through one approximable autonomous increment.
  It does not state approximation closure under inverse rephasing.
- `[CORPUS]` The lag-resolved Choi theorem shows spectral phase translation
  converts the anchor residual exactly to a zero-anchor traceless residual.
- `[LITERATURE]` Standard no-fast-forwarding results are worst-case lower
  bounds.  They do not perform this selector-safe entropy collapse for a
  recurrence tube.

Hostile novelty verdict: **`BRIDGE`**.  Word inversion and concatenation are
standard group facts.  Scientific novelty cannot be assigned to `(1)`.
Proof-frontier impact is nontrivial: it removes the continuum/adaptive-anchor
obstruction and leaves a finite zero-anchor traceless dictionary, the exact
object needed by the replica cancellation machinery.

## Complete paper proof

Choose words \(p,q\) of lengths at most \(s_x,s_y\) whose values approximate
\(x,y\).  Reverse \(p\) and replace every letter by its inverse.  The resulting
word \(p^{-1}\) has the same length and value exactly \(U(p)^{-1}\).  Hence
\(p^{-1}q\) has length at most \(s_x+s_y\) and value
\(U(p)^{-1}U(q)\).  Joint Lipschitz multiplication and isometric inversion
give

\[
 d(U(p)^{-1}U(q),x^{-1}y)
 \le d(U(p)^{-1},x^{-1})+d(U(q),y)
 =d(U(p),x)+d(U(q),y)
 \le\epsilon_x+\epsilon_y.
\]

This proves `(1)`.  Apply `(1)` pointwise to \(x=U(u)\), \(y=V_w\) to obtain
`(2)`.  Although witnesses may depend on \(u,w\), every witness belongs to
the same set of words of length at most \(r+s\).  For finite \(\Gamma\), that
set is finite independently of the cardinality or adaptivity of \(A\).

## Hostile proof audit

1. **Inverse gate hidden:** explicit and load-bearing.  Any universal alphabet
   may be symmetrized by adjoining inverses, changing alphabet size but not
   asymptotic depth.
2. **Error accumulation:** exactly one additive error from each of the two
   approximations; no dependence on anchor time or number of anchors.
3. **Continuum union:** eliminated at witness level; all witnesses lie in one
   finite word set.
4. **Residual is nonunitary:** `(1)` is applied before scalar removal.  The
   lag-resolved covariance theorem then removes the scalar component in the
   translated zero-anchor chart.
5. **Remaining open core:** `(1)` supplies no quenched small-ball or
   growing-replica estimate for the scalar-removed enlarged dictionary.

The argument is dependency closed.  Exact `[OPEN CORE]` after `(1)` is now:
prove a quenched growing-replica upper bound for zero-anchor traceless targets
in one finite word dictionary of depth `r+s`, strong enough to beat that
dictionary's cardinality.
