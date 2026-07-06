# 104 — Checkpoint: dead ends, open routes, research targets

**Register: SEARCH** (orientation page; every claim below carries its verdict-doc or Lean anchor;
nothing new is asserted here). Purpose: one page a fresh session reads *before* choosing an attack,
so no refuted branch is re-walked and every open core is named with its entry point. Supersedes
nothing; companions: `00-approach.md` (thesis), `05-task-board.md`, `lean_updates_codex.md` /
`lean_updates_codex2.md` (the formal change ledgers).

---

## 1. Machine-checked dead ends — Lean verdicts, do not re-attempt

- **[REFUTED, Lean] Weight-mismatch parity invariant** (doc 90; `WeightMismatchRefutation.lean`).
  The FE and Schwarz involutions on the zero-quadruple generate `V₄ ⊂ A₄` — every element even, no
  4-cycle on or off the line — and the quadruple carries total weight `4·ord(ρ)`, ℤ₂-trivial always
  (`quadruple_weight_parity_refuted`). The doc-89 route-b moonshot in its original ℤ₂ form is dead
  at theorem grade.

- **[REFUTED, Lean] Sharp MV-anchored pinning certificates beyond depth 3**
  (`RHTower/ShortWindowNoGo.lean`, 2026-07-06). Two global facts collide:
  the pinning geometry (quadratic containment + radii chain) forces every anchor window to length
  `U < 1` (`pinning_geometry_short_window`); and at `U ≤ 1` the sharp-carrier mean-value energy
  face is false for every `N ≥ 4` — the adjacent pairs alone put `N − 1` into the off-diagonal
  (`sharp_offDiagonal_ge`) against a diagonal supply capped at `U(1 + log N)`
  (`harmonic_Icc_le_one_add_log`). Capstone `sharp_pinning_certificate_depth_lt_four`: **any**
  window certificate carrying both faces has `N ≤ 3`, for every zero, height, and parameter
  assignment. The entire decoupled-ledger endpoint family is vacuous in its sharp MV
  instantiation. Redirect: anchors must come from designed coefficients with controlled
  off-diagonal (§3, window lane) or from non-mean-value sources (ball floors / minimum modulus).

## 2. Paper-grade verdicts — derivation- or measurement-backed (docs 79–85)

- **[REFUTED] Route C-direct** (doc 82): the registration gap — shallow creation events of the
  sharp carrier do not register at any fixed threshold; the honestly patched chain fails by
  `≥ 3–13×` at every threshold and height (exponential registration cost vs polynomially-walled
  certification). Links C-1..C-4 (ladder, window relation, domination, thick-dip counting) are
  sound, Lean-banked, and remain in service of other lanes.
- **[REFUTED as typed] Route B** (doc 85): the `V = O(1)` fixed-variance premise is false —
  `V(N) ≍ loglog N`, with a derivation-backed lower bound (singleton windows,
  `RouteBSupport.singleton_window_coeff`) and the corrected seed identity Lean-banked
  (`RouteBSeedGap.lean`). The heir **Route B′** (normalized program) survives with one analytic
  gate (§3).
- **[SUPERSEDED] Spur/DISC reader** (doc 79): replaced by the Rouché + Euler–Maclaurin counting
  island; `(S-mono)` survives only as a standalone conjecture.

## 3. Open routes and their named cores

- **Route A — GAF universality** (docs 55, 88). Bridge decomposed: a conditional-CLT part
  (provable-shaped, upward martingale over the prime filtration) × the **scalar-mixture identity**
  (the true residue: the conditional variance carries an `Θ(1)` relative fluctuation — the same
  mixture law as doc 87 §3, so Routes A and B′ share one open object). Entry: doc 88 §§1–2.

- **Route B′ — normalized mollified program** (docs 86, 87, 103). Open analytic gate
  **(SMOOTH-LOW)**: small-ball / 2D density of the smooth multiplicative packet with row masses
  `M_q ≍ e^{−γ}/2q`. Doc 103 built the missing brick class — the single-phase harmonic engine and
  its degradation law for non-isolated small primes. Open core: compose the engine across the
  packet (small primes enter every multiple's coefficient; the isolated-prime bricks do not
  apply). Entry: doc 103; consumer chain is machine-checked and waits on this gate alone.

- **Window-certificate / ladder lane** (docs 89, 91–101 + the formal spine). Status after this
  session: the sign face of the per-zero certificates is closed-form **except the anchor** — the
  short-interval second-moment face `S_b` is no longer independent data (point-to-mass converter,
  `CarrierMassFloor.lean`), envelope/first-moment/line-sup constants are theorems
  (`WindingFloor/WindingAmplitude/WindingCurvature/ResonanceClosedForm/EnvelopeDerivBound/
  CarrierLineSup`), and the whole arc is carrier-abstract (`MollifiedCarrier.lean`,
  `AnchorSupply.lean`: arbitrary real coefficients `b`, sharp = `b ≡ 1`). §1's no-go then pins the
  open core exactly where doc 89 put it: **the on-line anchor at short windows**, now as a global
  design constraint on the carrier as a whole —
  `offDiagonal(b) + orthogonal-correction < U·diagonal(b)` at `U < 1` —
  which the sharp carrier provably violates and a designed `b` must satisfy *jointly with the
  Jensen/engine/EM faces*. Either exhibiting such a `b` or proving a second no-go for a coefficient
  class is global knowledge.

- **Rung 1 of the ladder — `RHLadder 1`** (docs 91–93) — **NOT a shortcut route; RH-hard, with a
  mechanism-level obstruction to any forcing.** Statement: *no odd-order ξ-zero right of the line*,
  equivalently ξ has an analytic square root on `Re > ½` (`rhLadder_one_iff_even_order`,
  `rhLadder_iff_root`). The obstruction, sharper than doc 91's "no owned lever":
  - Every off-line zero `ρ` (`Re > ½`, order `m`) has its conjugate `ρ̄` **also** in the right half
    (same `Re > ½`) with `ord(ρ̄) = m` (Schwarz). Every structural input that could constrain the
    order is conjugation-symmetric and so factors through the **pair-sum `2m`**: symmetry orbits
    (FE+Schwarz), the deck cocycle on any conjugation-symmetric loop, and the Weil explicit formula
    (the one multiplicity-counting handle) all group `{ρ,ρ̄}` into `2m` — even for every `m`, hence
    blind to `m mod 2`. The only object isolating one `ρ` (a small loop's deck class `= m mod 2`)
    is Rung 1 itself, not a constraint on it.
  - The symmetry class **permits** odd `m`: a real even order-1 entire function — the shape of
    `Ξ(t)=ξ(½+it)` — can have *simple* off-line zeros (the real even quartic with roots `±(a±bi)`
    gives a simple quadruple `{ρ,1−ρ,ρ̄,1−ρ̄}`). So reality+FE+order-1 does not force even order;
    only ζ-specific arithmetic could, and all of it is blind to individual multiplicity parity
    (value-independence is jet-blind, doc 10 §7.1; the explicit formula is conjugate-paired).
  - **Terminal, no conjecture.** *Forcing* `RHLadder 1` as a strict intermediate (without assuming
    RH) has no handle — the obstruction above is a mechanism-level no-go — and it cannot be refuted
    either (an odd-order off-line zero requires disproving RH). But as a *consequence* it is already
    settled in Lean: `RiemannHypothesis → ∀ k, RHLadder k` is the forward half of
    `rh_iff_forall_ladder` (RiemannTower.lean — vacuous: RH leaves no right-half zeros), and
    `(R1)–(R7) → RiemannHypothesis` is `riemannHypothesis_of_residual_faces` (ResidualFaces.lean);
    composing, **`RHLadder 1 ⟸ (R1)–(R7)` is a proven corollary of the complete route.** There is
    thus no independent Rung-1 target: the standalone forcing is a mechanism no-go, and the corollary
    is already machine-checked.

- **Valuation-measure lane** (docs 98–101; `ValuationProfile/ValLimit/ValDefect` modules): the
  limit valuation measure, its Stieltjes form, mean-valuation density, and the density–depth
  defect are built; each doc names its next objects in its closing section (doc 101 §5 is the
  current tip).

- **Static skeleton — rank–codimension law** (doc 102): the value-orbit dimension equals the
  prime-exponent rank (finite case, promotion-grade proof + Lean brick); its honest boundary and
  the (XLD) connection are §4 of that doc.

## 4. The formal spine — route-free layering (pivot principle)

Three layers, enforced so that pivoting between routes replaces only the top one:

1. **Instruments** (route- and carrier-free): point-to-mass converter
   (`sq_integral_floor_of_anchor_slope`), moment-gap sign engine (`HardySignChange`), oscillation
   engines (`FirstMoment`), the archimedean envelope/winding calculus (digamma/trigamma verticals,
   winding floor/amplitude/curvature — properties of ξ's Γ-factor, shared by every route), phase
   collapse + energy split for any `w + χ·conj w` (`AnchorSupply` §1), generic MV floor, the
   general-coefficient mean-value theory (`SecondMoment`).
2. **Carrier families**: `completedMollG b N` for arbitrary real coefficients; the sharp carrier
   is the instance `b ≡ 1` (`completedMollG_one`).
3. **Endpoints / gates** (thin, route-specific): the pinning gates and ledger endpoints — the only
   layer a pivot rewrites, and the layer §1's no-go acts on.

A route candidate is an assignment of carrier + witnesses to the named faces; the closed forms make
failed assignments cheaply falsifiable (that is how the sharp instantiation died) and the face
vocabulary is how a **new** route enters without new infrastructure.

## 5. Research targets, ranked

1. **(SMOOTH-LOW) composition** — the single gate between Route B′ and its machine-checked
   consumer chain (doc 103's engine → full-packet small-ball bound).
2. **The mixture identity** — the shared residue of Routes A and B′ (docs 87 §3, 88 §2); one
   object, two routes pay.
3. **Designed-carrier anchor, settled globally** — exhibit a coefficient class satisfying the §3
   design constraint jointly with the remaining certificate faces, or prove the second no-go.
   Both outcomes are statements about the constraint system as a whole.
4. ~~**Rung 1 forcing**~~ — **removed from ranked targets** (§3): standalone forcing is a
   mechanism-level no-go (all structural inputs are conjugation-paired `→ 2m`, blind to `m mod 2`),
   and `RHLadder 1` is anyway a proven corollary of the complete route
   (`rh_iff_forall_ladder` ∘ `riemannHypothesis_of_residual_faces`). No independent target remains.
5. **Residual enumeration** — substitute the banked closed forms into the surviving gate once,
   globally, and exhibit `RH ⟸ ⟨short list of named ∀-statements⟩`: the formal answer to "what
   exactly does this constraint still ask of the world?"

The constraint-not-flow discipline for all five: each target is a *global* statement about the
system (a gate, an identity, a design law, a forcing, an enumeration) — per-window witnesses and
satisfiability examples are not progress and are not accepted as such.

---

## Addendum (same day): target 5 delivered

**[PROVED HERE]** `RHTower/ResidualFaces.lean : riemannHypothesis_of_residual_faces` — the
residual enumeration exists as a single axiom-clean theorem. RH follows from per-zero
certificates whose only non-formula content is carrier data: (R1) a line anchor
`m_J ≤ ‖g_N‖` at some height of the window, (R3a) a `g_N` sphere sup, (R5) a completed-carrier
sphere sup, (R7) EM closeness on spheres — plus four scalar comparisons among named closed-form
quantities ((R2) the sign-face budget inequality, (R3b/c) Jensen quotient and engine, (R6) the
outer cross/EM budget) and (R4) the archimedean floor. Every other estimate in the sign face is
internal. Ranked target 5 is closed; targets 1–4 stand, and target 3 (the designed-carrier
anchor) is now precisely "supply (R1) jointly with (R2)/(R3) at short windows" — the question
the no-go of §1 sharpened.

---

## Addendum 2: Rung 1 verdict — target 4 struck

**[VERDICT, verified against the tree]** `RHLadder 1` is not an independent target. (i) The
standalone forcing has a mechanism-level no-go: every conjugation-symmetric input (FE+Schwarz
orbits, symmetric-loop deck classes, the explicit formula) sees only the pair-sum `2m` of
`{ρ, ρ̄}` — even for every `m`, blind to parity — and the sole parity-separating object (the
non-symmetric small-loop deck class) *is* Rung 1, not a constraint on it. (ii) The symmetry
class permits odd order: a real even order-`≤1` function with a simple off-line quadruple
(quartic shape) satisfies every abstract constraint, so only parity-blind arithmetic could
force it. (iii) It cannot be refuted without disproving RH. (iv) As a consequence it is
subsumed: `(R1)–(R7) ⟹ ∀ k, RHLadder k` typechecks as
`rh_iff_forall_ladder.mp (riemannHypothesis_of_residual_faces hwin)` — verified in scratch,
not banked (pure composition, no quantifier moved). §3's Rung-1 bullet and ranked target 4
are hereby struck; the remaining ranked targets are (SMOOTH-LOW) composition, the mixture
identity, and the designed-carrier anchor — now sharpened by the anchor-disc coupling laws
(`AnchorZeroBudget.lean`, `WindingRigidity.lean`): any (R1) supplier must certify at radii
below the carrier's sign-change spacing, whose rate floor is the banked winding floor.

---

## Addendum 3: (R7) located — the AFE reflected block is the sole irreducible core

**[REDUCTION, Lean]** `RHTower/EMRemainderReduction.lean` (axiom-clean, in the umbrella).
The face **(R7)** — carrier-closeness `‖emCarrier M z − gN N z‖ ≤ δ` on window spheres — is now
pinned to a single classical object, not left as opaque "R–S debt".

- **Exact remainder identity** (`zeta_sub_gN_eq`, needs only the Euler–Maclaurin representation of
  ζ at depth `N`, *no* functional equation):
  `ζ z − gN N z = emPole N z − z·emTail N z − zetaChi z · dirichletPoly N (1 − z)`.
- **Tight reduction** (`norm_emCarrier_sub_gN_le_afe`):
  `‖emCarrier M z − gN N z‖ ≤ ‖z‖·M^(−re z)/re z + ‖ζ z − gN N z‖`.
  So the whole of (R7) beyond the elementary EM remainder `ε₁` is the **approximate
  functional-equation remainder** `‖ζ − gN N‖`. Equivalence is two-sided: this is the converse of
  `EMCarrier.afeAccurateOn_of_emCarrier_close` (closeness ⟺ AFE accuracy up to `ε₁`), packaged as
  `emCarrier_gN_close_on_of_afe` (an AFE budget supplies the (R7) face directly).

- **Where the smallness lives, exactly.** Of the three exact terms, `emPole N z = N^(1−z)/(z−1)` and
  the EM tail `z·emTail N z` are elementarily `o(1)` at the matched depth. The **reflected Dirichlet
  block** `zetaChi z · dirichletPoly N(1−z) = χ(z)·Σ_{n≤N} n^(z−1)` is the only oscillatory term. For
  `z = ½+it` and `N ≈ √(t/2π)` its phase `t·log n` has derivative `t/n ∈ [√t, t] ≫ 1` across the whole
  block, so its `O(t^{−1/4})` size is exactly **van der Corput first-derivative cancellation** — i.e.
  the Hardy–Littlewood approximate functional equation / Riemann–Siegel formula. `‖χ‖ = 1` on the line
  (`zetaChi_norm_on_line`) contributes nothing; the cancellation is entirely in the sum.

- **Why no elementary bound closes it** (and why the existing tree bound is not enough). The banked
  `EMCarrier.emCarrier_gN_norm_le_of_components` splits `emCarrier M − gN N` into its three visible
  pieces and bounds each **termwise**: `δD ~ Σ_{N<n≤M} n^(−(½−RJ))`, `δP ~ M^(½+RJ)`,
  `δχ ~ Σ_{n≤N} n^(−(½−RJ))` — each polynomial in the height, so `δ` is polynomially large, never the
  `o(1)` the certificate's outer budget (R6) demands. The identity above shows *why*: the summand
  `n^(z−1)` itself oscillates at frequency `t`, so termwise, Abel-summation, and first-order
  Euler–Maclaurin bounds all reproduce the polynomial size — the gain is only from `n^(it)`
  cancellation, which those methods discard. This is a structural fact about the object, not a missing
  trick.

- **Classification.** (R7) with a certificate-closing `δ` is **not dead** — it is a true classical
  theorem (the AFE, `O(t^{−1/4})`). It is **not dischargeable by the tree's elementary machinery** —
  its core is the reflected-block exponential-sum cancellation, whose foundations (van der Corput
  first-derivative test / stationary-phase integral bound) are absent from mathlib.

- **The lane this opens.** The one missing mathlib-grade foundation, now named and isolated: the
  first-derivative exponential-integral bound `|∫_a^b e^{i g}| ≤ 2/λ` for `|g'| ≥ λ` with `1/g'`
  monotone, then summation-by-parts to `Σ_{n≤N} n^{z−1}`, then disc-uniformisation to the window
  spheres against the (R6) budget. Every other (R7) input is now an elementary consequence of the
  banked reduction. This is the entry point for the reflected-block program — the sole analytic
  input the whole window-certificate route still asks of the world at Rung level, made precise.

**Lean anchor for the isolation.** `EMRemainderReduction.emCarrier_gN_close_on_of_reflected_budget`:
on any set, `‖emCarrier M z − gN N z‖ ≤ ε₁ + (δP + δT + Rχ)` where `ε₁` is the depth-`M` EM remainder,
`δP`/`δT` the depth-`N` pole/tail budgets (all elementary), and `Rχ` any bound on
`‖zetaChi z · dirichletPoly N (1 − z)‖`. So the (R7) face is a proven consequence of one reflected-block
budget `Rχ`; supplying `Rχ = O(t^{−1/4})` (the van der Corput input above) discharges it outright.

---

## Addendum 4: the van der Corput foundation is built (the missing mathlib piece)

**[PROVED HERE, Lean]** `RHTower/VanDerCorput.lean` (axiom-clean, in the umbrella). The first-derivative
test that Addendum 3 named as the sole missing foundation is now formalized:

- `norm_integral_cexp_ofReal_mul_I_le_mono` / `_anti`: for a real phase `g` with derivative `g'`
  bounded below by `lam > 0` and monotone (either direction) on `[a,b]`,
  `‖∫_a^b exp(i·g)‖ ≤ 2/lam`. Proof: one integration by parts — `exp(i·g)=(i·g')⁻¹ d/dx exp(i·g)` —
  the boundary term has modulus `1/g'`, the remainder is `∫ |g''|/g'²`, and monotonicity telescopes
  it to `|1/g'(a) − 1/g'(b)|`; the two combine to `2/g'` at the endpoint where `g'` is smallest.
- `norm_integral_cexp_logPhase_le`: the corollary at the reflected-block phase — for `0 < a ≤ b`,
  `c > 0`, `‖∫_a^b exp(i·c·log x) dx‖ ≤ 2b/c`. (Phase derivative `c/x`, decreasing, minimum `c/b`.)

This is the exponential-integral heart of the approximate functional equation: `x^(z−1)` has phase
`τ·log x` (`z = σ + iτ`), and the corollary gives `O(b/τ)` cancellation for its integral — the first
genuine cancellation gain over any termwise/Abel bound, which the identity of Addendum 3 proved were
all polynomially large.

**What remains to discharge `Rχ` (hence (R7)).** Two bricks, both now resting on an existing
foundation: (i) **Abel summation** — reduce the reflected block `Σ_{n≤N} n^(z−1) = Σ n^(σ−1)·e^(iτ log n)`
to its pure phase partial sums `B_k = Σ_{n≤k} e^(iτ log n)` (the decreasing real amplitude
`n^(σ−1)` telescopes, giving `‖Σ n^(z−1)‖ ≤ max_{k≤N} ‖B_k‖`); (ii) **discrete → continuous** —
bound `‖B_k‖` by the integral bound of `norm_integral_cexp_logPhase_le` plus the sum-to-integral
comparison (van der Corput's lemma / Euler–Maclaurin against the banked `emTerm` sawtooth). These are
well-posed engineering bricks now, not a foundational gap.

---

## Addendum 5: discrete van der Corput — the Dirichlet-test bridge built, core located at stationary phase

**[PROVED HERE, Lean]** `RHTower/DiscreteVanDerCorput.lean` (axiom-clean, in the umbrella).
`norm_sum_amplitude_phase_le`: the finite Dirichlet-test bound
`‖Σ_{m<K} a(m)·b(m)‖ ≤ a(0)·M` for an antitone nonnegative amplitude `a` and a complex `b` with
partial sums `≤ M` — the discrete companion of the integral van der Corput bound. It generalises the
tree's own `CascadeGeometric.abel_geom_bound` off the geometric special case. Applied with
`a(n)=n^(σ−1)`, `b(n)=n^(iτ)`, it reduces the reflected block `Σ_{n≤N} n^(z−1)` to the pure-phase
partial sums `max_k ‖Σ_{n≤k} exp(iτ·log n)‖`.

**The phase-sum core, located exactly.** Every route to bound `Σ_{n≤k} exp(iτ·log n)` reduces to the
same object. Via the tree's exact Euler–Maclaurin identity (`EMCarrier.finite_em_identity` at
`s = −iτ`, valid since `s ≠ 0, 1`):
`Σ_{n≤k} n^(−s) = 1 + (k^(1−s) − 1)/(1−s) − s·Σ_j emTerm(1+j)(s)`.
The main term `(k^(1+iτ)−1)/(1+iτ)` has modulus `≤ (k+1)/τ` (the integral, small — `norm_integral_cexp_logPhase_le`);
the remainder `s·Σ emTerm` is the mean-zero sawtooth integral `iτ·∫_1^k (ψ(x)/x)·exp(iτ log x) dx`
(`ψ = {x}−½`). Its Fourier expansion has phases `τ log x ± 2πm x` with derivative `τ/x ± 2πm`, which
**vanishes at the saddles `x = τ/(2πm)`** (present for `m ≥ √(τ/2π)`). Those saddles are the
stationary-phase / **Riemann–Siegel heart**: each contributes `~ √τ/(2π²m²)`, summing to `O(1)` bounded
but not `o(1)`. The termwise / first-derivative bounds all reproduce the polynomial size `~τ·log k`;
only the second-derivative (stationary-phase) analysis extracts the `O(t^{−1/4})` cancellation.

**State of (R7), fully mapped.** The chain is now Lean-real end to end down to one object:
(R7) `⟸` reflected-block budget `Rχ` (`EMRemainderReduction`) `⟸` phase partial sums (`DiscreteVanDerCorput`
+ the integral bound `VanDerCorput`) `⟸` the stationary-phase bound on the oscillatory `emTerm` remainder
(the sole remaining piece). mathlib has Poisson summation (`Real.tsum_eq_tsum_fourierIntegral`) and
interval IBP but no stationary-phase / second-derivative van der Corput — that is the one genuinely
missing foundation, now isolated to a single named integral with explicit saddles.

---

## Addendum 6 (2026-07-06): the no-flow-in-disguise pivot — pinning/carrier lane frozen

**Verdict.** The pinning/carrier lane (window certificates, mollifier hunt, residual gate) is a
flow in disguise, measured against the charter's own criterion (00-approach: "the object is fixed
by a constraint, not propagated by a flow"). Three flow signatures, all present:

1. **A clock.** Certificates are indexed by height; windows `[T, T+U]` march up the line; the
   lane's sharpest theorem is a clock rate (`rz ≲ 1/log T`). The charter's Wheeler–DeWitt
   orientation forbids exactly this: `T` is a reintroduced time variable.
2. **A generative handle.** "Which `b` makes all faces satisfiable" searches for a finite
   surrogate whose propagated sign changes certify the infinite object. 00-approach §4.1 states
   the counter-principle verbatim: strip zeros are *emergent* — present at no finite level. The
   open face (R7)/AFE is precisely the finite→emergent transfer that §4.1 prices as never cheap.
3. **Quantifier shape.** The gate is `∀ zero ∃ (T, U, rz, …)` with height-coupled budgets —
   positions along the flow. The charter's mechanism is `∀ weight-bound ∃ symmetry` — the
   constraint's symmetry data, height-free.

**The decisive internal evidence.** The residual face ledger sorted itself: every face that
closed (geometry, Jensen, zero budget, winding rigidity, phase lock, Borel–Carathéodory, the
segment-length laws, the radius-scale forcing) is a consequence of FE + analyticity — constraint
content. The two faces that stayed open — (R1) anchor recurrence and (R7) AFE/exponential sums —
are exactly the propagation statements, and both sit in the value-distribution register that the
wall's four independent derivations (00-approach §12) already price. The lane's residue IS its
flow content. `ShortWindowNoGo` replicated the message internally: the sharp handle fails at
`N ≥ 4`; widening the handle family (mollified `b`) is the flow program's characteristic
surrogate-escalation move and can iterate forever without touching the constraint.

**Lane status: FROZEN.** Closing artifact banked: `residual_faces_force_radius_scale`
(RadiusScaleForcing.lean) — the gate's own faces force `rz·windingFloor(T−rz) ≤ π + BC-budget`,
so the `1/log T` scale is a theorem *about* the certificate scheme, not an extra face. No scaled
endpoint was added (the forcing theorem makes one redundant). The endpoints stay as layer-3 thin
targets per the pivot architecture (§4); nothing is deleted; no further face-grinding.

**Salvage map — the flow lane built constraint instruments.** The load-bearing lemma of the
argument-variation chain is "Im ∈ πℤ, continuous, hence constant" — a discrete monodromy datum,
the same move as the deck cocycle. The toolkit {analytic log on zero-free discs,
Borel–Carathéodory, πℤ/2πℤ integrality gluing, winding rigidity/phase lock, anchored-disc zero
budget, segment-length laws} is local deck-class calculus on the seam, route-free by
construction.

**What this opens (the redirect).** The conservation program's located residual core is boundary
flux (15-conservation-program: at k = 1 the entire burden of (L) is boundary flux; open cells
OC1 band-edge crossings, OC2 seam crossings). `[CONJECTURE]` The frozen lane's instruments are
the OC2 toolkit: seam-crossing control is on-line behavior, and winding rigidity + the segment
laws govern exactly the on-line sign-change spacing and phase advance a charge crossing the seam
must respect — consumed per box annulus, homotopy-invariantly, with the per-height certificate
quantifier deleted. The next object to construct is the seam-crossing parity functional as a
formal object, checked against `WindingRigidity` + `ArgumentVariation` + `AnchorZeroBudget` for
its local half. Plan: doc 105.

---

## Addendum 6: the stationary-phase (second-derivative) van der Corput test is built

**[PROVED HERE, Lean]** `RHTower/VanDerCorputSecond.lean` (axiom-clean, in the umbrella). The deepest
missing foundation — the test that survives a stationary point, where the first-derivative bound
`2/|g'|` blows up — is now formalized:

- `norm_integral_cexp_secondDeriv`: for any real phase with `g'' ≥ λ > 0` on `[a,b]`,
  `‖∫_a^b exp(i·g)‖ ≤ 6/√λ`, uniform in the length. Mechanism: split at the zero of `g'` (unique by
  monotonicity of `g'`); within a window of length `≤ 2μ/λ` around it the trivial length bound
  applies, outside it `|g'| ≥ μ = √λ` and the first-derivative test (`VanDerCorput`) applies; the two
  balance at `3/√λ` per side.
- `norm_integral_cexp_secondDeriv_oneside` / `_oneside_neg`: the one-sided cores (`g' ≥ 0` at the
  near-stationary endpoint, and its reflection `x ↦ a+b−x` for `g' ≤ 0`), each `≤ 3/√λ`.

This is exactly the estimate the reflected-block Fourier modes need: `Σ_{n≤k} exp(iτ·log n)`'s
sawtooth remainder expands (Poisson) into phases `τ·log x ± 2πm·x` with second derivative `∓τ/x²`, so
each mode's oscillatory integral is now bounded by `norm_integral_cexp_secondDeriv` (after the trivial
conjugation `g ↦ −g` for the `−` modes) with `λ ≍ τ/x²`, giving `√x²/τ = x/√τ` per mode — the
`O(t^{−1/4})` cancellation the AFE requires. The one remaining assembly step (task #186) is the Poisson
expansion of the sawtooth and the sum over `m` against these per-mode second-derivative bounds — now
resting entirely on banked estimates (mathlib supplies Poisson summation).

**The (R7) chain, foundations complete.** (R7) `⟸` reflected budget `Rχ` (`EMRemainderReduction`)
`⟸` phase sums (`DiscreteVanDerCorput` Dirichlet test) `⟸` per-mode integrals, bounded by the
first-derivative test (`VanDerCorput`, non-saddle modes) and the **second-derivative test**
(`VanDerCorputSecond`, saddle modes). Every analytic foundation the approximate functional equation
needs for this route is now formalized and axiom-clean; what remains is the Poisson bookkeeping that
assembles them.
