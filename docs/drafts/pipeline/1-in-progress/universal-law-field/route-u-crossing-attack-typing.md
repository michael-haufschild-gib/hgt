# Route U crossing law — reconnaissance and attack typing

- **ID:** ULF-FIELD-6
- **Stage:** 1-in-progress
- **Type:** TYPED ATTACK ANALYSIS on a named frontier source theorem (map §10, chain 4)
- **Parents:** rh-current-frontier-map.md (Route U dossier); in-tree anchors read this
  session: `XiShiftedHankelFirstCrossing.lean`, `XiShiftedHankelBoundaryHilbertChargeFlow.lean`
  (through line ~1075), `XiShiftedHankelBoundaryExtensionClass.lean`,
  `XiShiftedHankelAdmittedGammaLorentzLanding.lean` headers
- **Status:** [RECON COMPLETE] [ONE TYPED NO-GO DERIVED] [NOT RH] [NO LEAN — directive]

## The open core, read from the tree (exact)

For y in the window 0 < y < 41/2, at a right-hand first crossing with null datum c
(head block PosDef, face singular, c ≠ 0, last coordinate ≠ 0), with
P = finiteHankelNullMonicPolynomial c (real simple roots, flat quadrature — in-tree):

    OBLIGATION:  0 < momentInner (k ↦ (primeArchShiftedReciprocalMoment y k).re) P (X·P),

i.e. L_y(X·P²) > 0 for the prime–arch shifted reciprocal moment functional. The consumer is
formalized: `not_xiShiftedHankelFirstCrossing_of_primeArchPair_pos` — this single positivity
at every crossing excludes all right-half first crossings, which is the route's RH handoff.
The equivalent source form is projective archimedean dominance over the oriented prime
discrepancy (`xiShiftedHankelNull_sourceSlope_neg_iff_projectiveSourceDominance`).

Structural reading (from the flat-quadrature layer): at a first crossing the truncated moment
sequence has a unique flat finitely-atomic representing quadrature with atoms at the roots of
P; X·P² vanishes at every atom; so L_y(X·P²) is exactly the FIRST UNSEEN moment discrepancy —
the true source sequence's next odd moment minus the value forced by its own degenerate
quadrature. The obligation says: the actual prime–Gamma source always outruns its flat shadow,
in the oriented direction, at every hypothetical degeneration.

## Typed no-go (derived this session): the unrestricted strengthening is group-3

**Claim.** The statement "L_y(X·P²) > 0 for EVERY nonzero real polynomial P, for every y in
the window" is equivalent to RH — hence inadmissible as a proof target.

*Derivation.* (⇐) RH gives the route's shifted-Hankel positivity (far-right positivity
extends; no crossing exists), and a strictly positive-definite Stieltjes-type functional has
L(X·P²) > 0 for all P. (⇒) Unrestricted odd-block positivity over the window excludes every
right-hand first crossing for every face dimension (the consumer theorem applied at each
crossing needs only its null P, a special case); by the route's Lean-closed architecture
("excluding every right-half first crossing proves required shifted-Hankel positivity and
RH"), RH follows. ∎

**Consequence (the typing).** Any admissible attack must consume the first-crossing
constraint ESSENTIALLY — the constraint that P is the null polynomial of an actual singular
face of the same functional (equivalently: the statement to be proven is vacuous under RH and
must be established as a self-destruction law for impossible configurations, from the
unconditional source side). Approaches that prove dominance for a P-class defined without
reference to the functional's own degeneration (all real-rooted P, all P with roots in a
fixed set, fixed corona/reporter classes) either prove group-3 statements or fall into the
route's recorded dead subclasses — which this typing now explains uniformly: every listed
dead subclass (generic moment positivity, positive atoms, tied-power sectors, root location,
stochastic order, factorial carriers, fixed corona reporters, Gamma lifetime, three-point
positivity, reflection aggregation) is a fixed-face or unrestricted-class mechanism.

Field consilience (recorded, no claim of novelty): this is the Θ2/Θ4 pattern at the U face —
fixed proper faces are blind; the crossing datum is the "future-sensitive reporter" the
frontier map's design survivor demands; U's obligation has exactly the admissible shape.

## What a viable attack must therefore look like (open directions, honestly unproven)

1. **Self-referential moment identity:** express L_y(X·P²) at a singular face through the
   face's own quadrature data (nodes = roots of P, weights from the head block) plus the
   source-side tail — seek an identity in which the prime discrepancy's pairing against X·P²
   is constrained BY the degeneration itself (the crossing forces exact relations among
   moments up to 2n+2; the discrepancy at 2n+3 may inherit a sign from the source's
   completed structure, e.g. the complete-monotonicity layer `SquaredXiCompleteMonotonicity`
   imported by the Landing module — read next).
2. **Window structure:** the constant 41/2 bounds the shift window — locate its origin in
   `XiShiftedHankelBoundaryQuadratureSource` (likely tied to the first Xi zero's scale or the
   negative-binomial parameter) before any estimate; an attack valid only in a sub-window is
   still a typed contribution if the consumer accepts it.
3. **Route T cross-check (secondary target, recorded):** T's open core (cofinal cancellation
   of centered von Mangoldt atoms via exact joint pairing before norms) is E1-class
   oscillatory transport; the corpus's formalized modulus-first cap bars norm-first
   approaches; this program has no mechanism for T beyond what the corpus records — T stays
   secondary with no claim.

## Log

- 2026-08-09 — recon of U anchors executed; open core stated exactly from the tree; the
  unrestricted-strengthening group-3 no-go derived and recorded (the cycle's typed
  contribution); admissible-attack shape typed; next reads named
  (`SquaredXiCompleteMonotonicity`, `XiShiftedHankelBoundaryQuadratureSource`). No Lean.
- 2026-08-09 — heavy conjecture loop exposed and paper-proved the higher-contact replacement:
  `../../2-fully-proven/mass-shifted-pade-contact-parity-law.md`. A full right-positive crossing
  has an earliest nonzero flat-quadrature Padé defect `delta_(2n+d)` with forced sign
  `(-1)^d delta_(2n+d)>0`. The current flux is only `d=1`; stationary contacts require the new
  alternating hierarchy. Frozen source target `(U-Pade)` asks the completed prime--Gamma source
  for the opposite sign at the adaptively selected first defect.
