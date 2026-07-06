# 107 — The Euler incidence carrier

**Register: SEARCH.** Conjectures labelled; banked Lean cited by file/name.
Executes doc 106 §8 prediction 3: construct the Euler analogue of the model pencil's
incidence carrier `r(s) = −Λ(s,χ̄)/Λ(s,χ)` and make its ramification on the FE fixed
locus the orientation datum of the band-edge pairing.
Companions: `106-band-edge-pairing-two-coloring.md`, `105-constraint-front-plan.md`,
`15-conservation-program.md`, `16-pinning-and-emission.md`.

---

## 1. The object

For an anchored ledger pencil — anchor `Λ₁ = P̂` (a completed/mollified partial Euler
product, **nonvanishing** on the box: the canonical `AnchoredLedger` start) and target
`Λ₂ = ξ` — the incidence carrier is the single meromorphic function

> **ι(s) := incidence P̂ ξ (s) = −ξ(s)/P̂(s).**

The banked fiber dictionary (`pencil_eq_zero_iff_incidence`, MirrorPencil.lean) turns
the entire family's zero dynamics into level-set geometry of ι: the member with
parameter ratio `r` vanishes exactly on the fiber `ι = r`. The affine ledger path
`u ↦ (1−u)·P̂ + u·ξ` has ratio `(1−u)/u` sweeping `(0,∞)` as `u` runs over `(0,1)`, so

> **the band-edge crossing events of the anchored sweep are the real-positive fibers
> of ι** — the family is gone; one object remains, fixed by the two constraints that
> built it (Euler product in `P̂`, FE in `ξ`).

The anchor and target pin the exceptional values: `ι = ∞` never occurs on the box
(`P̂ ≠ 0`), and `ι = 0` occurs exactly on `Z(ξ)` (`incidence_eq_zero_iff`).

## 2. Banked this construction (IncidenceCarrier.lean, axiom-clean)

- **`incidence_mirror`** — the FE pair acts on incidence values as the Möbius
  involution `r ↦ (ε'/ε)/r`: the parameter-space form of the mirror identity. The
  model pencil's two-coloring is the two components exchanged by this involution;
  its fixed values are the FE-fiber members.
- **`incidence_im_eq_zero_on_line`** — for real-FE carriers **the critical line lies
  inside the real locus of ι**: every seam point is a degenerate (non-transversal)
  point of the event structure. This is prediction 3's first half made exact: the
  seam is where the incidence sheets meet, and seam accounting (W1/W2) is precisely
  the ledger of that degeneration.
- **`real_pencil_ne_zero_of_im_incidence_ne`** — the quiet-edge certificate: where
  `Im ι ≠ 0`, **no member of any real deformation path vanishes** — one pointwise
  inequality silences every crossing event of every real sweep at once.
- **`bandSign`** + **`bandSign_pos_of_im_ne_zero`** + 
  **`exists_real_member_zero_of_bandSign_neg`** — the band-edge analogue of W1's
  `seamSign`: two endpoint evaluations of `Im ι` on an edge certify quiet (positive
  product) or force a transversal event (negative product). Band-edge flux data is
  boundary data, same engine as the seam.

## 3. The pairing, restated on ι

`BandEdgePairing` for the anchored sweep becomes: **per lateral edge, the count of
real-positive ι-fibers is even.** Two observations restructure the burden:

1. **The order pairing evades the §6 no-go.** Doc 106 §6 closed geometric involutions
   of the s-plane. But events on an edge are linearly ordered, and when the edge's
   `bandSign` data agrees at the endpoints, consecutive crossings pair by the
   intermediate value theorem — a pairing by *order and boundary data*, not by any
   motion of the zero configuration. The involution payload for
   `LedgerFluxPaired`/`FixedPointFreePairing` is consecutive-crossing pairing.
2. **The residual gap is exact.** `bandSign` reads the parity of *all* real fibers;
   the events are the *positive*-real fibers. The difference is the parity of
   negative-real hits — crossings of the backward pencil members (`u ∉ [0,1]`).
   `[CONJECTURE — closed-sweep telescope]` Over the full real projective sweep the
   box ledger telescopes to zero (the sweep returns to its start), so the
   `(0,∞)`-fiber parity equals the `(−∞,0)`-fiber parity plus the ledger's own
   endpoint data; the negative-real class is not a new burden but the mirror image
   of the positive one under the banked Möbius action.

`[CONJECTURE — ports as ramification]` The emission ports (multiple on-line zeros,
doc 106 §4) are exactly the critical points of the real-analytic restriction
`ι|seam`: where `(ι|seam)' = 0`, two event branches merge and the two-coloring
degenerates. Next Lean target: `ι|seam` is real-analytic (same rotated-cofactor move
as SeamParity's `G`), and simple ports ⟺ simple critical points.

## 4. Where the Euler constraint must act

The arithmetic frontier of doc 106 §7, translated to ι: prove that `Im ι` on lateral
edges oscillates with even crossing parity. The Euler input available: `log(−ι)` on
`Re s > 1` has the explicit nonneg-coefficient Dirichlet expansion
`log ξ − log P̂` = the *tail* of the Euler log (primes > X) plus the archimedean
completion — the anchor subtracts the head of the constraint, and ι's phase is the
tail's imaginary part. The pairing question becomes: **can the tail of a
positive-coefficient Dirichlet series wind oddly across a lateral edge?** — a
question about `Im Σ_{p>X} p^{−s}`-type sums, where the banked frozen-lane
instruments (winding floors, BC budgets) apply verbatim to a DIFFERENT carrier.

## 5. Wild layer (rng draw: phyllotaxis, sourdough-fermentation)

- `[CONJECTURE — parastichy interleaving]` Phyllotaxis: successive primordia placed
  by a repulsion constraint with irrational divergence angle produce exactly two
  visible spiral families with three-gap interleaving rigidity. Collision: the real
  fibers of ι along the seam are placed by the equidistribution of `{τ·log p}`
  (the Euler tail's phases — ℚ-independent log-frequencies = the "most irrational"
  divergence data). Conjecture: consecutive real fibers of ι interleave with a
  three-gap-type rigidity, and the two colors of doc 16's two-coloring are the two
  parastichy families. Prediction against banked data (no new compute): the R3c
  disjoint defect populations, sorted by height, should show the two-family
  interleaving pattern of a rotation sequence, not an i.i.d. pattern.
- `[CONJECTURE — self-restoring ratio]` Sourdough: a two-population culture holds a
  stable ratio that feeding perturbs and metabolism restores. Collision: ι IS the
  two-population ratio, and the banked Euler moat (open basin, R5 measurements) is
  the stable culture. Conjecture: between consecutive events on an edge the
  orientation must alternate — the Euler basin restores `sign(Im ι)` after each
  crossing, so two same-orientation events cannot occur without an intervening port.
  Prediction: the banked per-zero crossing parameters `u*`, sorted along any edge,
  alternate in orientation except at ports.

## 6. Next objects

1. `ι|seam` real-analytic + ports = critical points (Lean; the ramification half of
   prediction 3).
2. The closed-projective-sweep telescope (Lean target on `LedgerChainE`: a chain
   returning to its start has even total flux — trivially flux 0; the content is the
   decomposition of the closed sweep into the `[0,1]` window and its complement).
3. The Euler-tail winding question of §4 as a stated analytic lemma, fed to the
   frozen-lane instruments.
