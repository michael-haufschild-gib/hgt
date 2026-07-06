# 106 — Band-edge pairing and the two-coloring front

**Register: SEARCH.** Conjectures are labelled. Banked Lean is cited by file/name.
No computation is used here.

**Grade split.**
- The finite parity consumer below is **BRIDGE**: it is pure finite bookkeeping, now
  formalized as `RHTower/BandEdgePairing.lean`.
- The model-pencil two-coloring is **BRIDGE/model**: `MirrorPencil.lean` and
  `CountingSubstitute.lean` prove the FE-paired pencil algebra and the pinning lemma,
  but the model pencil is not the Euler endpoint.
- The open W4 statement is **[CONJECTURE, native candidate]**: the Euler + FE weld
  should supply the pairing interface `BandEdgePairing` consumed by W3. The conjecture
  is not promoted here.

Companions: `105-constraint-front-plan.md`, `15-conservation-program.md`,
`16-pinning-and-emission.md`, `14-parity-stratum.md`.

---

## 1. The exact W4 interface

Fix an upper-quadrant box `B`, a piecewise-generic family path `F_u`, and rung `k = 1`.
The conservation ledger has already reduced the burden to boundary flux. Split the
boundary events into:

1. **band-edge events**: off-seam transversal crossings of the lateral/top band edges;
2. **seam events**: crossings absorbed on the critical-line edge, handled by W1/W2;
3. **anchor events**: endpoint cleanliness, handled by W3/W5;
4. **interior events**: collisions or annihilations inside `B`, mod-2 silent by the
   banked additivity ledger.

The W4 interface is the first item only.

> **`BandEdgePairing(B,F)` [CONJECTURE/interface].**  
> Let `E_B(F)` be the finite set of transversal, off-seam band-edge crossing events
> of `B` along `F_u`, counted with multiplicity mod 2. A band-edge pairing is a
> fixed-point-free involution
>
> `τ : E_B(F) → E_B(F)`
>
> such that each event and its mate have the same box, the same local multiplicity
> mod 2, and opposite normal crossing orientation. At `k = 1` the orientation sign is
> irrelevant after reduction mod 2; what matters is that every unit crossing event
> belongs to a two-element orbit.

The formal consumer is now machine-checked:

> **[PROVED, Lean]** `bandEdgeUnitFlux_zmod_two_eq_zero`
> (`RHTower/BandEdgePairing.lean`): if a finite event type carries a fixed-point-free
> involutive pairing, then the unit crossing flux
> `∑ e, (1 : ZMod 2)` is `0`.

This is deliberately thinner than W3's eventual `Prop`: W3 may define `E_B(F)` however
its ledger reduction needs. W4 supplies the theorem shape: once the event set is paired
freely, the band-edge contribution to `(P-flux)` vanishes mod 2.

---

## 2. What is already proved on the model pencil

Doc 16 banked the local model:

1. **Pinning.** In an FE-real family, a simple on-line zero cannot leave the line under
   an FE-preserving deformation. The Lean form is `pinned_zero_re_eq_half` in
   `CountingSubstitute.lean`; it is a Rouché-free deck-counting substitute.
2. **Mirror pencil.** For a paired two-character pencil
   `G_{c,d}=cΛ(s,χ)+dΛ(s,χ̄)`, reflection `s ↦ 1-s` acts by the parameter involution
   `(c,d) ↦ (dε',cε)`. The Lean form is `pencil_mirror_zero_iff` and the incidence
   map `incidence` in `MirrorPencil.lean`.
3. **Two-coloring in the FE-breaking model.** A simple on-line zero at the FE fiber,
   when detuned through the model `k`-pencil, is right-defective on exactly one side
   of the FE fiber; the color is the sign of the transverse velocity.

This proves the model phenomenon, but it does **not** prove the W4 interface for the
Euler endpoint. It says which event class may be paired: simple FE-fiber unpinnings
are colored by transverse direction. It also says which class must not be counted as
an unpinning event.

---

## 3. Attack-as-false: box 84

The designated counterexample candidate is the banked box-84 zero near `t ≈ 85.7`.

### False statement killed

The following tempting statement is false:

> "Every box that is defective on both sides of the FE fiber violates two-coloring."

Box 84 kills it. Its zero is already off-line at the FE member. Under small detuning it
continues as an off-line trajectory and can occupy a right-band box on both sides. This
is an **occupied-box** fact, not a **band-edge crossing-event** fact.

### Surviving statement

The statement that survives is event-based:

> **[PROVED on the model pencil]** A zero branch born from a simple on-line zero at the
> FE fiber has one transverse color. It is right-defective on only one side.  
> A pre-existing off-line zero is not an FE-fiber unpinning event and is outside this
> event set.

So box 84 does not refute `BandEdgePairing`; it forces the interface to count **events**
rather than **occupied boxes**. Any W3 version of `BandEdgePairing` that quantifies over
defective boxes instead of transversal crossing events is too weakly typed and should be
rejected.

---

## 4. Other failure modes the interface must route away

### Degenerate velocity

[CONJECTURE / attack target] If an on-line branch has first transverse velocity zero,
then either the first nonzero transverse term is even, producing no one-sided band-edge
unpinning, or the parameter is a multiple on-line point. The latter is an emission port
and belongs to W1/W2 seam accounting, not W4 band-edge pairing.

This is the first stress point for the Euler endpoint: an odd failure of `(P-flux)`
should appear as an odd emission-port count, not as an unpaired transversal band-edge
event.

### Tangency to the band edge

A tangent contact with a lateral edge is not a transversal event. After a generic
path refinement it splits into either zero or two transversal crossings unless it
coincides with a singular zero event. The regular split is even mod 2; the singular
case is again routed to the seam/emission interface.

### Endpoint grazing

Crossings at the anchored endpoint are not W4 data. They are part of `AnchoredEnd`.
This is why `BandEdgePairing` is stated for the interior transversal event set of the
path, after endpoint cleanliness has been supplied.

---

## 5. The W4 conjecture, sharpened

> **[CONJECTURE] Euler-FE band-edge pairing.**  
> For every upper-quadrant box `B` and every piecewise-generic FE-compatible path from
> an anchored end to an Euler endpoint, the finite set of off-seam transversal band-edge
> crossing events admits a fixed-point-free pairing as in §1. Therefore the band-edge
> contribution to `(P-flux)` is even.

Equivalent operational form:

> Any odd flux obstruction cannot live on the lateral band edges. It must route to one
> of the named non-W4 cells: seam/emission parity, endpoint anchoring, or a failure of
> piecewise-genericity that resolves into one of those cells after refinement.

This is the exact statement W3 should consume as `BandEdgePairing`.

---

## 6. Exhaustion pass: no geometric involution remains

Doc 19 §4a is decisive for the next attack. Inside a line-centered window at height
`T > 0`, the FE/reality symmetry group leaves only

`id` and `s ↦ 1 - conj(s)`

as window-preserving maps. The nontrivial one is exactly the mirror pairing already
consumed by `(ID)`. FE alone and conjugation move the window to height `-T`; they do
not pair regular same-window band-edge events.

This height-line filter is now machine-checked:

> **[PROVED, Lean]** `FESymmetry.preserves_height_line_iff`
> (`RHTower/WindowSymmetryNoGo.lean`): for nonzero height `T`, the FE/reality
> symmetries preserving the height line `Im(s)=T` are exactly `id` and
> `lineReflect`.

Therefore the following stronger W4 route is **closed**:

> "The Euler endpoint has a second visible FE/reality involution that freely pairs
> off-seam band-edge crossing events."

No such geometric involution remains after `(ID)`. This does **not** refute
`BandEdgePairing`; it refines its source. If the pairing exists at the Euler endpoint,
it must be arithmetic: a pairing forced by the Euler constraint on the finite/window
value, not a new motion of the zero configuration in the `s`-plane.

The Lean consumer now includes the contrapositive diagnostic:

> **[PROVED, Lean]** `not_bandEdgePairing_of_unitFlux_ne_zero`
> (`RHTower/BandEdgePairing.lean`): nonzero unit mod-two event flux rules out the
> `BandEdgePairing` interface.

So W4 has no hidden slack: a single regular unpaired event is not a nuisance case; it
is exactly the obstruction and must be routed to W1/W2/W5 or to a static arithmetic
identity that proves the flux zero.

---

## 7. Retyping W4 as the dynamic face of `WR_1`

For a swept window, regular lateral band-edge crossings are the dynamic presentation
of the change in the right-half order sum `N(W)` modulo `2`, after W1/W2 remove seam
events and W5 removes endpoint events. Thus:

> **[CONJECTURE / equivalence after W1-W3 typing]**  
> `BandEdgePairing` for all regular lateral event sets is the pathwise certificate of
> the static bridge identity `(WR_1)`, i.e. `D(W) ≡ L(W) (mod 4)`, or equivalently
> vanishing of the square class `ε(Ξ₁)` on the corresponding window.

This explains why the model-pencil two-coloring is real but insufficient. The model
proves what a local FE-fiber unpinning event looks like. The Euler endpoint must prove
that the total event parity is zero. After the symmetry exhaustion in §6, that zero
can only come from one of the later arithmetic/static coordinates:

1. **Window/square class** (`WindowRelation.lean`, `SquareLadder.lean`): prove
   `WR_1` directly. Then any odd regular lateral flux is impossible after the
   W1/W2/W5 exclusions.
2. **Finite carrier census** (`AnnealWindowRelation.lean`, `DiscCensus.lean`): transport
   the window `ZMod 2` value to `completedGN` and certify the finite-side census.
   This supplies the parity value, not a geometric zero-motion.
3. **Arithmetic germ / continuation** (`GermExtension.lean`, doc 21): package the
   Euler product root germ and prove its continuation. The explicit-formula pairing
   alone is incomplete by type: it outputs real/smooth data, while W4 needs a
   `ZMod 2` class.

The DISC section reader of docs 20 and 23-42 is therefore an instrument, not the
definition of W4. It may certify finite-side values, but doc 75's audit keeps the
main chain on Rouché/transport and finite census data.

Consequently W4 is exhausted to the following exact frontier:

> **Frontier.** Construct an arithmetic/static proof that the regular lateral event
> flux has zero `ZMod 2` class. A visible FE/reality two-coloring cannot supply it.
> A pure smooth explicit-formula pairing cannot supply it. Box-level occupied counts
> cannot supply it. The remaining candidates are `WR_1`, finite-carrier census
> certification, or germ continuation.

---

## 8. Pre-registered predictions without new computation

1. Counting occupied defective boxes across the FE-breaking model will keep seeing
   box 84 as both-sided. Counting transversal unpinning events will not: box 84 is
   absent from the unpinning event set.
2. Any Euler-endpoint counterexample to `BandEdgePairing` should localize to a multiple
   on-line zero or endpoint-grazing event after path refinement; it should not remain
   as a lone regular lateral crossing.
3. In the two-character model, the incidence map `r(s)=-Λ(s,χ̄)/Λ(s,χ)` is the carrier
   for event orientation. For the Euler endpoint, the missing object is the analogue
   of this incidence carrier constrained by the Euler structure; an odd failure should
   show up as ramification of that carrier on the FE fixed locus.

These are predictions for later verification. None is used as proof here.

---

## 9. What W4 hands to the other packages

- To **W3**: define `BandEdgePairing` as a `Prop` whose payload is a finite event set
  plus a fixed-point-free involution; consume `bandEdgeUnitFlux_zmod_two_eq_zero`.
- To **W1/W2**: all multiple on-line emission-port and seam-absorption cases are
  explicitly excluded from W4's event set and routed to seam parity.
- To **W5**: endpoint grazing and non-clean anchor cases are excluded from W4 and routed
  to anchoring.

The W4 reduction is therefore not "two-color every defective box." It is:

> **pair regular lateral crossing events; route every non-regular event to the named
> seam or anchor interfaces.**
