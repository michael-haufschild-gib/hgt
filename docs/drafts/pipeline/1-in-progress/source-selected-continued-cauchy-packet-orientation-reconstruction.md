# Source-selected continued-Cauchy packet orientation reconstruction

- **ID:** source-selected-continued-cauchy-packet-orientation-reconstruction
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]` / TOP-DOWN VALUE-RELATION TARGET
- **Scientific status:** `[OPEN CORE] [NOVELTY UNVERIFIED]`
- **Statement:** Construct from the analytically continued prime--Gamma source, without selecting Xi zeros, one collision-free sequence of finite Cauchy packets whose evaluation vectors converge to the Xi--Hurwitz orientation vector and whose explicit divided-difference values converge to minus the orientation energy.

## Exact target

Let `T` denote `continuedPrimeArchSourceRelativeTrace`.  Construct finite sets `S_n` and
coefficients `c_n : Complex -> Complex` such that every point of `S_n` lies in the continued
prime--Gamma Cauchy domain and

```text
z != conjugate(w)  for all z,w in S_n.                    (1)
```

Put

```text
F_n(u)=sum_(z in S_n) c_n(z)/(u-z),                       (2)
V_n=(F_n(alpha_q))_q.                                     (3)
```

The required value relations are

```text
V_n -> v_Xi in ell^2,                                     (4)

W(V_n)
 = Re sum_(z,w in S_n) c_n(z) conjugate(c_n(w))
     * (T(conjugate(w))-T(z))/(z-conjugate(w)),            (5)

W(V_n) -> -E_Xi.                                          (6)
```

Equation `(5)` is already available for each collision-free finite packet through
`xiWeilPolarization_cauchyPacket_eq_continuedPrimeArchSource`.  Equations `(4)` and `(6)` are
available for abstract algebraic-span vectors through
`xiHurwitzOrientationEnergy_continuedCauchy_reconstruction`.  The bridge is now closed in
`XiContinuedCauchyPacketDensity.lean` and
`XiHurwitzOrientationSeparatedSourceReconstruction.lean`: Lean constructs an actual sequence of
finite packets satisfying `(1)`, proves `(4)`, identifies every energy by `(5)`, and proves `(6)`.
The surviving gap is no longer representation or collision avoidance; it is source-pure selection
and sign.

## Source-purity firewall

A merely target-fed extraction is not the final producer.  The existing closure proof moves a
pole horizontally from each exact Xi spectral fibre, so its choice depends on the divisor it is
meant to constrain.  That proves unconditional membership but does not make the selected sequence
source-defined.

The proof must therefore do one of the following:

1. define `S_n,c_n` deterministically from finite values or jets of `T` and prove `(4)` as a new
   source--divisor value relation; or
2. prove a source inequality for a packet class characterized independently of the Xi divisor,
   with the extracted sequence shown to lie in that strictly smaller class.

Universal positivity on every continued Cauchy packet is not accepted as progress: the corpus
already proves that universal condition equivalent to RH.

## Best current feeder

The prime--polar moving-tent series in
`prime-gamma-rectangular-boundary-tomography.md` is source-selected and is conjectured to recover
the complete right off-critical divisor as its pole set with exact residues.  If that tomography
is formalized, contour extraction from the source series could select the packet poles and
coefficients without taking an Xi-zero enumeration as input.  The new phase--energy bridge then
identifies the recovered pole displacement with both its energy contribution and the sharp
rectangular power exponent.

## Two technical routes

1. **Collision-free density.** Finite Cauchy packets with `(1)` are now proved dense in the
   continued Cauchy algebraic span.  Norm continuity handles the divisor-valued evaluations, and
   one common vanishing `1+i` perturbation simultaneously excludes every equation
   `z=conjugate(w)`.  The indexed packet formula then identifies the finite prime--Gamma energies
   exactly.  This closes `(4)`--`(6)` mechanically but remains target-fed unless combined with the
   source firewall.
2. **Diagonal kernel extension.** Extend `(5)` continuously across `z=conjugate(w)` with diagonal
   value `-T'(z)`.  This removes collision avoidance but requires a termwise/analytic theorem
   identifying the diagonal Cauchy polarization with the derivative of the continued relative
   trace.  It again closes the value formula, not source selection by itself.

## Gates

- [x] continued-source closure membership proved
- [x] abstract finite-span sequence and quadratic-value limit proved
- [x] off-diagonal finite-packet divided-difference formula proved
- [x] phase-energy-growth witness bridge proved
- [x] norm continuity of the Xi-divisor Cauchy evaluation map
- [x] self-conjugate pole deletion preserves the continued Cauchy Hilbert closure
- [x] pairwise collision-free finite-packet density
- [x] explicit packet representation for one reconstructing sequence
- [ ] packet selection independent of Xi divisor input
- [x] exact source formula `(5)` and limit `(6)` assembled in one Lean theorem
- [ ] independent source sign theorem or source-positive value collision

## Log

- 2026-07-12 — isolated from the full-corpus top-down sweep after the continued-source closure and principal-phase growth additions.
- 2026-07-12 — formalized Cauchy `ell^2` norm continuity and proved that removing all real poles
  preserves the continued source Hilbert closure; only pairwise finite-packet collision avoidance
  remains in the mechanical value-formula layer.
- 2026-07-12 — closed pairwise collision avoidance by a simultaneous vanishing complex
  perturbation; extracted actual finite separated packets from every algebraic-span vector and
  composed their exact prime--Gamma energies into a sequence converging to `-E_Xi`.  The remaining
  target is exclusively source-pure packet selection or eventual sign.
