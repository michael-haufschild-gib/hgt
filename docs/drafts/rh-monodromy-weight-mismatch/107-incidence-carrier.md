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

---

## Addendum (2026-07-06, night): the three next-object targets delivered in Lean

All three §6 "next objects" are now machine-checked (axiom-clean, lint green, MainTheorems builds).

**Target 1 — ramification (`IncidenceRamification.lean`).** `seamIncidence` (the real seam
restriction of ι) is real-analytic where the anchor is nonvanishing. The full ramification
classification: `seam_critical_iff_port` — a critical point of ι|seam is exactly a PORT (the
on-line member has a multiple zero); `seam_simple_port_iff` — a nondegenerate critical point
(member Hessian ≠ 0) is exactly a SIMPLE port (order exactly two). §3's "ports = critical
points" and "simple ports ⟺ simple critical points" are both theorems. The transversal event
structure degenerates precisely on the ramification locus of ι.

**Target 2 — closed-sweep telescope (`LedgerTelescope.lean`).** The §3 telescope conjecture
is discharged: `ledgerChain_closed_flux_eq_zero_of_enclosed` proves a deformation loop crosses
zero net multiplicity (unconditionally for factored members, via the banked simply-connected
annular charts), and `ledgerChain_window_back_two_dvd` / `ledgerChainE_window_back_two_dvd`
prove the window flux ≡ back-sweep flux mod 2 — the positive-fiber event class and its complement
are ONE. The two band-edge event classes collapse to a single class; the (0,∞)-fiber refinement
gap of §3 is closed.

**Target 3 — Euler-tail winding (`EulerTailWinding.lean`).** The §4 frontier is realized as a
winding lemma: `incidence_phase_of_factor_phases` proves the incidence phase IS the Euler tail
(θ_ξ − θ_P̂), and `exists_bandEvent_of_euler_tail` proves that when the tail winds by ≥ π across
an edge a transversal band event is forced. `windingPhase_ge_pi_of_long` feeds the banked
archimedean winding floor in the exact form consumed. The one remaining analytic input — an
off-line winding floor for the archimedean factor (bounding arg ξ'/ξ away from the line) — is now
the isolated open core for firing the lemma on a concrete lateral edge; it is a growth-estimate
project, not a structural gap.

**What this opens.** The band-edge pairing (W4) now has: its orientation datum located
(ramification of ι, Target 1), its two classes reduced to one (Target 2), and its forcing
mechanism built (Target 3). The next object is the off-line archimedean winding floor — the
single analytic estimate that turns the winding lemma into concrete forced events, feeding the
mirror-reduced single event class into `LedgerFluxPaired`.

---

## Addendum 2 (2026-07-06, late night): the off-line archimedean winding floor delivered

The Addendum's one remaining analytic input — the off-line winding floor for the archimedean
factor — is now machine-checked (`LateralWindingFloor.lean`, 18 endpoints, axiom-clean, lint
green, MainTheorems builds). It is NOT a structural module but the growth-estimate instrument,
and it came out fully explicit:

**The floor.** `stripWindingRate_ge`: at every abscissa `0 < σ ≤ 1` and height `τ > 0`,

> Re(archFactor′/archFactor)(σ+iτ) ≥ stripFloor σ τ = (log(τ/2π) − 4/τ² − π/τ)/2 − (1−σ)/τ².

The digamma vertical bound was never a line phenomenon (`re_digamma_ge` holds at every
abscissa); the only thing that pays for leaving the line is the rational term
`1/s + 1/(s−1)`, and its price is the explicit `(1−σ)/τ²`. The abscissa dichotomy:
for σ ≥ 1 the price is ZERO (`stripWindingRate_ge_of_one_le`) — the full line floor holds
verbatim to the right of the strip. A matching ceiling (`stripWindingRate_le`) makes the
off-line control of arg ξ_arch′/ξ_arch two-sided. The floor is positive from the absolute
height 12 on, at every abscissa (`stripFloor_pos`), monotone in both variables, and welds to
the banked line instrument at σ = 1/2 (`stripWindingPhase_one_half`).

**The polar engine.** The presentation the Euler-tail lemma consumes is produced, not
assumed: a nonvanishing path with `G′ = G·ω` transports as `G(a)·exp(∫ω)`
(`path_transport_exp_logDeriv` — no zero appears, no phase slips), hence IS a real modulus
times a unimodular phase with phase advance `∫ Im ω` (`polar_presentation_of_logDeriv`).
Applied to the envelope on a vertical edge: `archFactor_lateral_polar`, with phase advance
exactly the lateral winding phase `stripWindingPhase σ a τ ≥ (b−a)·stripFloor σ a`.

**The firing.** `exists_bandEvent_of_long_lateral_edge`: on a lateral edge at abscissa
`0 < σ ≤ 1`, height `a ≥ 12`, of length at least `(π + C₁ + C_D)/stripFloor σ a`, a
real-ratio member of the anchored pencil `(P̂, completedGN)` is forced to vanish — the
transversal band-edge event of §4, produced by winding. Every archimedean quantity is
explicit and unconditional. The Euler-tail winding question of §4 is now conditioned on
exactly two named finite objects, both Dirichlet-side:

1. **C₁** — the anchor's phase advance along the edge (a nonvanishing finite Euler head:
   its log-derivative is a finite prime sum; its phase budget is a finite estimate);
2. **C_D** — the Dirichlet part `gN`'s phase budget on the edge (equivalently a polar
   presentation of `gN` there — supplied by the same banked polar engine wherever `gN` is
   edge-nonvanishing, e.g. from the quiet-edge certificate `Im ι ≠ 0` or a mollified
   nonvanishing window).

**What this opens.** The forcing mechanism (Target 3) is no longer waiting on any
archimedean estimate. The next object is Dirichlet: a concrete edge-family where `C₁ + C_D`
grows slower than `(b−a)·log a` — e.g. mollified anchors on windows where the banked
second-moment/BC budgets already control `log gN` — which would make forced band events
unconditional on those edges and feed the mirror-reduced single event class of Target 2
into `LedgerFluxPaired` with events supplied, not hypothesized.
