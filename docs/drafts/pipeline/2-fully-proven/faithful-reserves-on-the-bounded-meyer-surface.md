# Faithful reserves on the bounded Meyer surface

- **ID:** faithful-reserves-on-the-bounded-meyer-surface
- **Stage:** 2-fully-proven
- **Type:** CONJECTURE (Lean verification pending)
- **Source:** Q-II; bounded full-Hasse source algebra and faithful Hilbert–Schmidt reserve.
- **Statement:** On the bounded centered-orbit carrier, the faithful Hilbert–Schmidt source cone has RR exactly when every critical Xi zero is simple. Its reserve is flow invariant on that carrier regardless of this condition.
- **Status:** UNVERIFIED until the actual Lean module and its transitive axiom audit pass. No critical multiplicity or off-line zero is asserted to exist.

## Carrier and distinction

Let B consist of actual sources whose lower Xi jets vanish off the critical
line and whose critical jets vanish below the highest local order. The
certified bounded-orbit theorem identifies B with both bounded and isometric full-Hasse
centered orbits. B is a source subalgebra preserved by arithmetic sharp.

Restrict the original Meyer surface to both fibres and B. Its ordinary trace
degree cone has RR, Bézout, and ampleness unconditionally. The faithful reserve

    P(g)=(||T(g)||_HS²+||T(g#)||_HS²)/2

also has Bézout and ampleness there, and is zero precisely on genuine
boundaries. It is invariant under centered flow on B, since sharp reverses
that flow and both terms have constant HS norm. This invariance alone does
not remove a possible nilpotent adjoint defect within B.

## Necessity of critical simplicity

Suppose a critical point rho has multiplicity m>1. Its actual highest-jet
source e_(rho,m-1) belongs to B and is not principal. All its zeroth Xi values
are zero, so its ordinary trace square is zero. Faithfulness gives P(g)>0.
The source-cone RR criterion on the restricted surface would require
P(g)<=delta(g,g)=0, a contradiction.

Equivalently its source convolution matrix has a nonzero terminal lower
entry and its arithmetic sharp has the same lower position. The Hilbert
adjoint occupies the upper position. Their exact squared adjoint defect is
nonzero even though the source orbit moves only by a unit phase.
The actual candidate now states this witness explicitly as
`exists_bounded_meyer_source_adjoint_defect_pos`: an isometric nonprincipal
source in B with zero ordinary trace, strictly positive faithful reserve,
and strictly positive squared Hilbert adjoint defect. This packages the
preceding paper assertion; its Lean verification is pending.

## Sufficiency and exact adjoint criterion

Now suppose every critical Xi point is simple. For any g in B, all operator
rows at off-line points vanish, because every relevant source jet vanishes.
At a critical point the block has size one, so the actual convolution acts
by its zeroth Mellin value. Hence T(g) is diagonal, supported at simple critical
points. Sharp conjugates those values and again vanishes at every other block.
Thus T(g#)=T(g)* for every g in B.

The exact HS trace-defect identity gives P(g)=delta(g,g). This proves RR for
the restricted faithful cone, while Bézout and ampleness follow from the
already proved majorant inequalities. In fact the faithful cone and ordinary
degree cone coincide in this case. Conversely equality of cones implies RR
and therefore critical simplicity by the preceding highest-jet witness.

Consequently the following assertions are equivalent:

1. Every critical Xi zero is simple.
2. Arithmetic sharp equals the Hilbert adjoint on B.
3. P equals ordinary trace square on B.
4. The faithful reserve cone on the bounded source surface has RR.
5. The faithful reserve cone equals its ordinary degree cone.
6. Some complex-linear cohomological degree is strictly positive on the sharp
   square of every nonprincipal bounded-carrier source.
7. Some complex-linear cohomological degree represents `P(g)` on every
   bounded-carrier sharp square as `Re d([g*g#])`.

For assertion 6, necessity uses the same multiple critical highest jet: its
sharp square is principal, so every descended linear degree reads zero.
Under critical simplicity, choose the ordinary trace degree. On B its square
reading equals the faithful reserve, which is strictly positive off genuine
boundaries. Positivity is required only on B; no claim is made about the
chosen degree on sources outside B.

Assertion 7 implies 6 because the reserve is nonnegative and vanishes precisely
on genuine boundaries. Under critical simplicity, assertion 3 makes the ordinary
trace degree a witness for 7. Thus exact linear-degree representation also has
the bounded carrier's RR criterion, with no condition on off-line zeros.
These implications are included as actual Lean proof candidates, still unverified.
Corpus search found the bounded faithful-degree criterion and the full-carrier
reserve-representation candidate, but no exact bounded reserve-representation result.

No assertion concerns jets outside B. On the full source carrier the analogous
criterion is RH together with simplicity. This domain distinction prevents
incorrectly transferring the full-carrier equivalence between reserve-flow
invariance and RR to a restricted carrier.

## Exact dependencies and pending work

- `MeyerBoundedCenteredOrbits`: exact carrier classification; Lean certified.
- `MeyerCriticalTopAlgebra`: sharp stability, quotient subspace and highest critical source witness; Lean certified.
- `BoundedMeyerSourceSurface`: original restricted surface and ordinary cone; draft unchecked.
- `FaithfulHilbertSchmidtSourceReserves`: actual reserve, exact adjoint defect and faithfulness; Lean certified.
- `MeyerHilbertReserveFlowRigidity`: reserve-flow invariance and its exact locus; Lean certified by direct check 35848 and seven standard axiom audits.
- `MeyerHilbertSchmidtSource` and HT `HilbertSchmidtTraceDefect`: actual-file certified foundations.

The diagonal argument uses actual rows and the existing l2 inner-product sum,
without a new source realization or infinite norm expansion premise. Lean must
formalize the seven equivalent assertions and preserve the unconditional reserve
invariance separately. Lean draft: `/tmp/QIIBoundedMeyerFaithfulReserveDraft.lean`; unchecked.
External novelty unverified.

Actual candidate: `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/BoundedMeyerFaithfulReserve.lean`; unverified and unwired, with thirteen audit endpoints. The actual module includes the explicit positive-adjoint-defect witness, `exists_meyerBoundedHilbertReserve_linear_degree_iff` and `meyerBoundedHilbertSourceCone_riemannRoch_iff_linear_degree`; its older scratch copy lacks these additions and the later proof corrections.
