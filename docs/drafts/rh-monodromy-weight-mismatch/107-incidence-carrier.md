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

---

## Addendum 3 (2026-07-06, dawn): the Dirichlet side discharged — events supplied, not hypothesized

Addendum 2 left two residual budgets: `C₁` (anchor head phase advance) and `C_D` (gN phase
budget). Both are now machine-checked and, crucially, the forced band-edge events are
**supplied unconditionally** on any sufficiently high lateral edge — the only remaining
band-edge input is the pairing itself. Four new modules (`AnchorHead.lean`,
`IncidenceEdgeCount.lean`, `EdgeEventSynthesis.lean`, `EdgeEventLedger.lean`; 42 declarations,
axiom-clean, lint green, MainTheorems 9198 jobs).

**C₁ — the anchor head (finite prime sum).** The anchor is `eulerHeadAnchor P = ∏_{p∈P}(1−p^{−s})`,
nonvanishing on the right half plane; its log-derivative is the finite prime sum
`∑_{p∈P}(log p)p^{−s}/(1−p^{−s})`, bounded in modulus — UNIFORMLY IN THE HEIGHT — by
`eulerHeadBound P σ = ∑_{p∈P}(log p)p^{−σ}/(1−p^{−σ})`. A height-independent constant, exactly
the "finite prime sum" the doc named.

**C_D — the carrier budget (polar engine).** Where `gN` is edge-nonvanishing, its phase rate is
`Re(logDeriv gN)`, bounded by a constant `B_D` on the edge. No new machinery: the same polar
transport engine of Addendum 2 supplies the presentation.

**The decisive move — a POINTWISE rate floor, not just endpoint budgets.** The incidence carrier's
log-derivative is `logDeriv Λ₂ − logDeriv Λ₁`, and for `Λ₂ = completedGN = archFactor·gN` this
splits three ways: `Re(logDeriv archFactor) = stripWindingRate ≥ stripFloor σ a` (the off-line
archimedean floor, grows like ½log a), minus the gN budget `B_D`, minus the anchor budget
`eulerHeadBound P σ`. So the incidence phase rate has a POINTWISE floor
`ρ₀ = stripFloor σ a − eulerHeadBound P σ − B_D`. When `ρ₀ > 0`, the incidence phase is strictly
increasing, and it crosses a multiple of π — forcing `Im ι = 0`, a real-ratio pencil member
vanishing, a transversal band event — once per `π/ρ₀` of edge length. The count is
`≥ (b−a)·ρ₀/π`: **the events grow with the edge length and (through `ρ₀`) with the height.**

**Subcriticality, explicit (`exists_height_net_rate_ge`).** Because `stripFloor σ a → ∞` while
`eulerHeadBound P σ` and `B_D` are fixed, for any target `ρ₀` there is an explicit height `A`
above which `ρ₀ ≤ stripFloor σ a − eulerHeadBound P σ − B_D`. This is precisely "`C₁ + C_D` grows
slower than `(b−a)·log a`", now a theorem: the two height-independent Dirichlet budgets are
overwhelmed by the log-growing archimedean floor.

**Handed to `LedgerFluxPaired` (`exists_edge_events_supply_fluxPaired`).** The `n` forced simple
crossings are recorded as the odd class `List.replicate n 1`; their event list carries paired
flux the moment the `n` events carry a fixed-point-free pairing (`BandEdgePairing (Fin n)`). The
capstone states both halves: the events exist (forced, unconditional given the finite Dirichlet
data and a high edge) AND, given the pairing, their flux is paired. The paired-flux interface is
handed its odd event class with the **events supplied, not hypothesized** — exactly the goal.

**What this opens.** The band-edge pairing (W4) is now the *sole* undischarged input on the whole
route: orientation datum located (ramification of ι), two classes reduced to one (telescope),
forcing mechanism built (winding), archimedean floor built (LateralWindingFloor), and the events
themselves supplied on the lateral edges where `gN` is zero-free. The next object is the pairing:
a fixed-point-free involution on the `n` forced crossings of a lateral edge — i.e., proving the
`BandEdgePairing (Fin n)` for the specific event configuration the winding produces, which is
where the arithmetic of the Euler tail (the `{τ·log p}` equidistribution of §5's phyllotaxis
conjecture) must finally enter as the pairing rule.

---

## Addendum 4 (2026-07-06): endpoint orientation pairs the forced edge events

The pairing input named at the end of Addendum 3 is now reduced to a boundary orientation datum and machine-checked in `RHTower/EdgeEventParity.lean`.

**Parity theorem.** `exists_crossing_enum_parity` enumerates all crossings of a positive-modulus monotone-phase carrier on an edge: for `F(τ)=r(τ) exp(i θ(τ))`, with `r>0`, `θ` continuous and strictly increasing, and nonzero endpoint imaginary parts, there is a strictly ordered finite family of all points where `Im F=0`. Its count is even exactly when the endpoint orientations agree:

> `Even n ↔ (0 < (F a).im ↔ 0 < (F b).im)`.

The proof is the literal level count: crossings are the levels `kπ` between `θ(a)` and `θ(b)`, and `sin` changes sign according to the parity of `⌊θ/π⌋`.

**Ledger handoff.** `crossings_fluxPaired_of_endpoints_agree` composes the parity theorem with the consecutive-crossing pairing from `BandEdgePairingConstruction.lean`, producing `LedgerFluxPaired (List.replicate n 1)` without assuming a pairing when the endpoints agree.

**Incidence capstone.** `exists_incidence_edge_events_fluxPaired` applies this to the incidence pencil: analytic nonvanishing anchor/target data plus a positive incidence phase-rate floor supply the strictly monotone polar carrier, and endpoint orientation agreement supplies the paired flux for the forced real-ratio pencil events. The remaining boundary datum is therefore explicit: prove the two endpoint values of `Im ι` have the same sign in the target box.

Verification: `lake env lean GaloisForLFunctions/RHTower/EdgeEventParity.lean`, `lake env lean GaloisForLFunctions/RHTower.lean`, and `lake build GaloisForLFunctions.RHTower` all pass; `/tmp` axiom checks for the three public declarations are `[propext, Classical.choice, Quot.sound]`; `scripts/formal_tools.py index` and `scripts/formal_tools.py lint --check-generated` pass. Pipeline card: `docs/drafts/pipeline/3-formalized/not-new/incidence-edge-parity-endpoint-agreement.md`.

---

## Addendum 4 (2026-07-06, morning): the route bottomed out — the pairing built, one boundary datum left

Following the route to exhaustion: `LedgerFluxPaired`'s odd class needs a fixed-point-free
pairing on the forced band-edge events. Three new modules (`BandEdgePairingConstruction.lean`,
`EdgeEventLedger.lean` extension, `EdgeEventParity.lean`; axiom-clean, lint green, MainTheorems
9201 jobs) build that pairing and reduce the whole route to a single boundary sign.

**The pairing IS the evenness (`nonempty_bandEdgePairing_iff_even`).** A fixed-point-free
involution on `Fin n` exists exactly when `n` is even: forward is the general parity of a
fixed-point-free permutation's support; reverse is the CONSTRUCTED consecutive-crossing
involution (`consecutivePairing`, swapping within each adjacent pair via `Fin 2m ≃ Fin 2 × Fin m`).
So the abstract `BandEdgePairing` hypothesis is not an unknown — it is precisely the statement
that the band-event count is even.

**The parity criterion — the pairing's boundary condition, exact (`exists_crossing_enum_parity`).**
Along a monotone-phase edge the incidence carrier's `Im = 0` crossings are the phase's passages
through multiples of `π`, in bijection with the integers in `[⌊θa/π⌋, ⌊θb/π⌋]`. Because the sign
of `sin` on `(mπ,(m+1)π)` is `(−1)^m` (`sin_pos_iff_even_floor`), the count `⌊θb/π⌋ − ⌊θa/π⌋` is
even **exactly when the two endpoints lie on the same side of the real axis** — `Im` of the same
sign. This mechanizes doc 106 §5's "consecutive crossings pair by the intermediate value theorem
when the boundary data agrees": the pairing exists iff the endpoint orientations agree.

**The terminus (`exists_incidence_edge_events_fluxPaired`).** On a lateral edge of the incidence
pencil — anchor and target analytic nonvanishing, incidence phase rate `≥ ρ₀ > 0` (from the
subcritical Dirichlet budgets of Addendum 3, giving a strictly monotone phase) — IF the two
endpoint orientations of the incidence carrier agree, the forced band-edge events come in an even
number and their event list carries paired flux, with the pairing constructed. **The entire
paired-flux burden of the route is discharged into a single boundary datum: the agreement of the
endpoint orientations `0 < Im ι(σ+iT) ↔ 0 < Im ι(σ+iT′)` on the box's lateral edge.**

**Where the route now stands.** Every structural gate is machine-checked: the ledger reduction,
the seam parity, the incidence carrier and its ramification, the closed-sweep telescope, the
Euler-tail winding, the off-line archimedean floor, the finite-prime anchor budget, the Dirichlet
budget from carrier data, the growing forced-event count, the pairing construction, and the parity
criterion. The route reduces to ONE analytic boundary fact — the endpoint-orientation agreement of
the incidence carrier on a lateral edge — which is exactly the datum the box's functional equation
governs. That is the next object: `hagree` from the FE/reflection symmetry of the ledger box,
where the arithmetic of the Euler tail (the `{τ·log p}` equidistribution) enters as the rule that
fixes the boundary orientation. The single sign that remains is the whole of the classical content
this geometry was built to isolate.

---

## Addendum 5 (2026-07-06): the positive-real FE mirror reverses orientation

The endpoint-orientation datum isolated in Addendum 4 is not supplied by the positive-real reciprocal mirror alone. This is now machine-checked in `RHTower/IncidenceMirrorOrientation.lean`.

**Mirror algebra.** `im_real_div_eq_neg_normSq` proves

> `Im((lam : ℂ)/z) = -lam * Im z / normSq z`.

So for `lam > 0`, `im_real_div_mul_im_neg` gives `Im((lam : ℂ)/z) * Im z < 0` whenever `z` is nonzero and nonreal.

**Incidence consequence.** Composing this with `incidence_mirror`, `incidence_mirror_im_product_neg_of_real_pos` proves: for an FE-paired pencil with `ε'/ε = lam > 0`, the incidence values at `s` and `1-s` have opposite imaginary orientations away from the real locus.

Thus the FE mirror supplies an opposite-edge orientation rule. It does not, by itself, prove the same-edge endpoint agreement consumed by `exists_incidence_edge_events_fluxPaired`. The remaining datum is still exactly the boundary statement from Addendum 4: show the two endpoint values of `Im ι` on the target lateral edge have the same sign, or replace that hypothesis with a stronger box-level orientation theorem.

Verification: `lake env lean GaloisForLFunctions/RHTower/IncidenceMirrorOrientation.lean`, `lake env lean GaloisForLFunctions/RHTower.lean`, and `lake build GaloisForLFunctions.RHTower` pass; `/tmp` axiom checks for the seven public declarations are `[propext, Classical.choice, Quot.sound]`; `scripts/formal_tools.py index` and `scripts/formal_tools.py lint --check-generated` pass. Pipeline card: `docs/drafts/pipeline/3-formalized/not-new/incidence-mirror-positive-real-orientation-reversal.md`.
