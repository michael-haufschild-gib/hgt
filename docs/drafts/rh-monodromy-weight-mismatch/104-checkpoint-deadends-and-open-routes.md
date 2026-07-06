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

---

## Addendum 7: conjugation corollary banked; the sawtooth assembly mapped

**[PROVED HERE, Lean]** `RHTower/VanDerCorputSecond.lean`, two more axiom-clean theorems:
- `norm_integral_cexp_neg_phase`: `‖∫ exp(i·(−g))‖ = ‖∫ exp(i·g)‖` (conjugation commutes with the
  interval integral — `Complex.conjCLE.intervalIntegral_comp_comm` — and preserves modulus). This is
  the conjLIE/conjCLE plumbing.
- `norm_integral_cexp_secondDeriv_neg`: the **concave** second-derivative test, `g'' ≤ −λ < 0 ⟹
  ‖∫ exp(i·g)‖ ≤ 6/√λ`, by applying the general test to `−g` through the conjugation identity. This is
  the sign the `−` Fourier mode `τ·log x − 2πm·x` carries (`g'' = −τ/x²`), so both mode families are
  now covered.

**The remaining sawtooth assembly (the Riemann–Siegel B-process), mapped exactly.** mathlib supplies
the periodized-Bernoulli Fourier machinery (`ZetaValues.periodizedBernoulli`, `bernoulliFourierCoeff`)
— the right tool for expanding the sawtooth `ψ = {·}−½` (raw Poisson on a sharp `[1,k]` cutoff is
worse). The chain: (i) the tree's `finite_em_identity` already writes `Σ_{n≤k} n^(−s) = main + Σ emTerm`
with `emTerm m = ∫_m^{m+1}(x−m)x^{−s−1}` — the sawtooth integral; (ii) Fourier-expand `ψ` and interchange
(dominated convergence — the `B_1` series converges only pointwise/`L²`, so this step needs care);
(iii) bound each mode `∫ (1/x)·exp(i(τ log x ± 2πm x))` by the **weighted** van der Corput; (iv) sum the
mode bounds over `m` (`Σ 1/m²` convergence). The one missing per-mode input is the **weighted** van der
Corput (the `1/x` factor): its core is verified (IBP with `U = w·(g'·i)⁻¹`, `U' = w'(g'i)⁻¹ − w·g''i/(g'i)²`,
norms `‖U‖ = w/g'`, pointwise `U·V' = w·V`), bound `‖∫ w·exp(i·g)‖ ≤ 4·w(a)/λ` for `w` antitone
nonnegative. Every unweighted per-mode bound (first- and second-derivative, both signs) is banked; the
assembly is the interchange + weighted-mode + summation bookkeeping, resting entirely on these.

**Update (same session): weighted van der Corput banked.**
`RHTower/VanDerCorputWeighted.lean : norm_integral_weight_cexp_le` (axiom-clean, umbrella green) — the
last missing per-mode ingredient: for an antitone nonnegative weight `w` and `g' ≥ λ > 0` increasing,
`‖∫_a^b w·exp(i·g)‖ ≤ 4·w(a)/λ` (one IBP with `u = w·(i·g')⁻¹`; boundary `w/g'`, remainder
`∫|w'|/g' + ∫ w·g''/g'²`). This covers the `1/x` amplitude of the sawtooth Fourier modes. Every
analytic estimate the reflected-block assembly needs — first-/second-derivative (both signs),
weighted, Abel/Dirichlet, and the exact reduction — is now formalized and axiom-clean. The residual is
purely the combinatorial/convergence bookkeeping: the sawtooth Fourier interchange (dominated
convergence for the `B_1` series) and the `Σ_m 1/m²` sum of per-mode bounds.

---

## Addendum 8: the two item-1 assembly tools banked (mode-sum + interchange)

**[PROVED HERE, Lean]** `RHTower/SawtoothModeSum.lean` (axiom-clean, umbrella green):
- `summable_and_norm_tsum_le_of_mode_bound` / `_of_inv_sq_bound`: the **sum over m** step —
  a family `T m` with `‖T m‖ ≤ K/(m+1)²` (the per-mode weighted-vdC rate) is absolutely summable and
  `‖∑' m, T m‖ ≤ K·∑' 1/(m+1)²` (finite, `= K·π²/6`).
- `intervalIntegral_tsum`: the **expand-and-interchange** step — `∫_a^b (∑' n, f n) = ∑' n, ∫_a^b f n`
  under absolute summability (`∑' n, ∫⁻ ‖f n‖ ≠ ⊤`). This is the interval-integral form of
  `MeasureTheory.integral_tsum`, absent from mathlib.

Route confirmed by mathlib's `ZetaValues`: the sawtooth `B₁` Fourier series is only conditionally
convergent, but IBP lifts it to the **continuous `B₂`**, whose Fourier series is absolutely convergent
(`summable_bernoulli_fourier` for `k ≥ 2`, coefficients `~1/m²`) with the pointwise expansion
`hasSum_one_div_pow_mul_fourier_mul_bernoulliFun` — exactly the `∑' n, f n` that `intervalIntegral_tsum`
consumes, with the `1/m²` coefficients feeding the mode-sum.

**Toolset now complete.** Every analytic estimate (first-/second-derivative van der Corput both signs,
weighted, Abel/Dirichlet), the conjugation, the exact `(R7)→Rχ` reduction, the interchange, and the
mode-sum are all formalized and axiom-clean. The residual is the connective wiring: `finite_em_identity`
→ sawtooth → IBP-to-`B₂` → `intervalIntegral_tsum` with the `B₂` `hasSum` → per-mode weighted vdC →
mode-sum. No new analytic input remains — only the bookkeeping that chains banked lemmas.

---

## Addendum 9: the sawtooth IBP-lifting step banked (B₁ → B₂)

**[PROVED HERE, Lean]** `RHTower/SawtoothIBP.lean` (axiom-clean, umbrella green):
- `hasDerivAt_ofReal_cpow_const`: the derivative of `x ↦ (↑x)^c` (`x > 0`).
- `sawtooth_ibp_unit`: the per-interval Euler–Maclaurin IBP. On `[m,m+1]` the local `B₂` half
  `Q(x) = ((x−m)²−(x−m))/2` **vanishes at both integer endpoints**, so
  `∫_m^{m+1} (x−m−½)·x^(−s−1) = −∫_m^{m+1} Q(x)·(−s−1)x^(−s−2)` with no boundary term. Summed over `m`,
  this lifts the conditionally-convergent sawtooth (`B₁`) to the continuous, absolutely Fourier-summable
  `B₂` — the maneuver that legitimises the mode expansion (the `B₁` series is not absolutely convergent,
  `B₂`'s is, `~1/m²`).

**End-to-end progress map.** `finite_em_identity` (tree ✓) → per-interval IBP `B₁→B₂`
(`sawtooth_ibp_unit` ✓) → [sum over `m`, identify `B₂`-periodic kernel] → [`B₂` Fourier expansion on the
interval] → `intervalIntegral_tsum` (✓) → per-mode weighted vdC (✓) → mode-sum (✓). The two remaining
connective links are the `m`-summation of the per-interval IBPs and the periodic-`B₂` Fourier expansion
(mathlib supplies it on the circle `𝕌`; the circle→interval bridge is the last piece). Every analytic
estimate and both the interchange and mode-sum are banked; the residual is these two connective steps.

---

## Addendum 10: the m-summation link banked — one connective link left

**[PROVED HERE, Lean]** `RHTower/SawtoothSum.lean : sawtooth_ibp_sum` (axiom-clean, umbrella green):
chaining `sawtooth_ibp_unit` across `[m,m+1]` for `m = 1…N−1` (via `sum_integral_adjacent_intervals`
and the a.e. identity `Int.fract x = x − m` on each unit interval — `fract_ae_sub`) gives, over `[1,N]`:
`∫_1^N ({x}−½)·x^(−s−1) = −∫_1^N (({x}²−{x})/2)·(−s−1)x^(−s−2)`.
The right side carries the continuous, absolutely Fourier-summable periodic `B₂` kernel `({x}²−{x})/2`.

**End-to-end chain — one link remaining.** `finite_em_identity` (✓) → per-interval IBP `B₁→B₂`
(`sawtooth_ibp_unit` ✓) → **m-summation** (`sawtooth_ibp_sum` ✓, this addendum) → [`B₂` Fourier
expansion on the interval — the circle→interval bridge] → `intervalIntegral_tsum` (✓) → per-mode
weighted vdC (✓) → mode-sum (✓). The sole remaining link is the periodic-`B₂` Fourier expansion:
expressing `({x}²−{x})/2 = Σ_m c_m e(mx)` (`c_m ~ 1/m²`) as a `∑'` over the real interval, from
mathlib's circle version `hasSum_one_div_pow_mul_fourier_mul_bernoulliFun` (on `𝕌`, `k=2`). Every other
link — all analytic estimates, the interchange, the mode-sum, and now both the per-interval IBP and its
m-summation — is banked and axiom-clean.

---

## Addendum 11: the B₂ Fourier circle→interval bridge banked — core of every link now formalized

**[PROVED HERE, Lean]** `RHTower/BernoulliFourierBridge.lean : fourier_hasSum_bernoulli2` (axiom-clean,
umbrella green): for every real `x`,
`∑_n (1/n²)·e(nx) = 2π²·({x}² − {x} + 1/6)`,
lifting mathlib's circle expansion `hasSum_one_div_pow_mul_fourier_mul_bernoulliFun` (`𝕌`, `k=2`) to
the real line by the periodicity `↑x = ↑(Int.fract x)` (`AddCircle.coe_fract`) and `bernoulliFun_two`.
The `1/n²` coefficients are absolutely summable — exactly what `intervalIntegral_tsum` consumes.

**Every named link now has its core banked** (9 files this session):
`finite_em_identity` (tree) · per-interval IBP `B₁→B₂` (`sawtooth_ibp_unit`) · `m`-summation
(`sawtooth_ibp_sum`) · **`B₂` Fourier bridge** (`fourier_hasSum_bernoulli2`) · interchange
(`intervalIntegral_tsum`) · per-mode van der Corput (first/second/weighted) · mode-sum
(`summable_and_norm_tsum_le_of_inv_sq_bound`). The residual is mechanical gluing — rearranging the
bridge `hasSum` to the `∑'` form `({x}²−{x})/2 = −1/12 + ∑_n c_n e(nx)`, applying the interchange with
the `∑ ∫⁻‖·‖ ≠ ⊤` check (immediate from the `1/n²` decay), rewriting `fourier n ↑x = exp(2πinx)`
(`fourier_coe_apply`) for the per-mode integrals, and one further analytic brick: the **weighted
second-derivative** van der Corput for the `O(1/n)`-fraction of saddle modes (phase `2πnx + τ log x`
has a stationary point when `n ≈ −τ/(2πx)`; the weighted-first covers the rest). With that brick and
the gluing, the reflected-block bound closes; all its analytic inputs but the weighted-second are
banked and axiom-clean.

---

## Addendum 12: the weighted second-derivative test (convex one-sided) banked

**[PROVED HERE, Lean]** `RHTower/VanDerCorputWeightedSecond.lean :
norm_integral_weight_cexp_secondDeriv_oneside` (axiom-clean, umbrella green): for `w` antitone
nonnegative and a phase with `g'' ≥ λ > 0`, `g' ≥ 0`, `‖∫_a^b w·exp(i·g)‖ ≤ 5·w(a)/√λ`, length-uniform
across the stationary point. Proof: the stationary-point split carried through the weight — the trivial
bound `∫ w ≤ w(a)·length` in the short window where `g'` is small, the banked weighted first-derivative
test `norm_integral_weight_cexp_le` where `g' ≥ √λ`, balanced at `w(a)/√λ`.

This is the convex, one-sided core of the last analytic brick. Remaining to the fully general
weighted-second (both `g'` signs, needed as the saddle-mode phase `2πnx + τ log x` crosses zero): the
concave companion (`g'' ≤ −λ`, via conjugation) and the negative-derivative outer piece (a weighted
first-derivative test with `g'' ≤ 0`) — mechanical sign-mirrors of banked lemmas. Ten van der Corput /
sawtooth files now carry every core estimate of the Riemann–Siegel reflected-block bound; the residual
is the sign-mirror analytic variants plus the mode-expansion glue (hasSum→`∑'`, interchange, per-mode
instantiation, mode-sum).

---

## Addendum 13: the general weighted second-derivative test banked — every analytic brick complete

**[PROVED HERE, Lean]** (axiom-clean, umbrella green):
- `RHTower/VanDerCorputWeightedAnti.lean : norm_integral_weight_cexp_le_anti` — weighted first-derivative
  test with `g'' ≤ 0` (sign-mirror of the `g'' ≥ 0` case; `|g''| = −g''`, `∫ −g''/g'² = 1/g'(b) − 1/g'(a)`).
- `RHTower/VanDerCorputWeightedSecondGeneral.lean`:
  - `norm_integral_weight_cexp_conj_neg` — weighted conjugation `‖∫ w·e^{ig}‖ = ‖∫ w·e^{−ig}‖`.
  - `norm_integral_weight_cexp_secondDeriv_oneside_concave` — concave one-sided (`g' ≥ 0`, `g'' ≤ −λ`),
    the convex mirror using weighted-first-anti on the outer piece.
  - `norm_integral_weight_cexp_secondDeriv` — **general** (both `g'` signs, `g'' ≥ λ > 0`):
    `‖∫_a^b w·e^{ig}‖ ≤ 10·w(a)/√λ`, split at the stationary point `g' = 0` (convex side + conjugated
    concave side).
  - `norm_integral_weight_cexp_secondDeriv_neg` — concave general (`g'' ≤ −λ`) by conjugation; the form
    the saddle modes take (phase `2πn·x + τ log x`, `φ'' = −τ/x² < 0`).

**Every analytic input of the reflected-block bound is now banked and axiom-clean** (13 files): the full
van der Corput toolset — first (both signs), second unweighted (both signs), weighted-first (both signs),
weighted-second (general, both `g'` signs, both convex and concave), conjugation, discrete/Abel — plus
the exact reduction, the interchange, the mode-sum, the per-interval IBP, the `m`-summation, and the `B₂`
Fourier bridge. The sole residual is the mode-expansion assembly: rearrange the bridge `hasSum` to `∑'`
form, apply `intervalIntegral_tsum` (`∑ ∫⁻‖·‖ ≠ ⊤` from `1/n²`), rewrite `fourier n ↑x = exp(2πinx)`,
instantiate the per-mode bound (weighted-first off the saddle band, weighted-second on it), and sum. Every
lemma that assembly calls now exists.

---

## Addendum 14: the full end-to-end reflected-block bound — CLOSED, axiom-clean

**[PROVED HERE, Lean]** `RHTower/ReflectedB2Integral.lean : reflected_B2_integral_bound` (axiom-clean,
umbrella green): for `N ≥ 1`, `s.re ≥ −2`, `s.im < 0`,
`‖∫_1^N (({x}²−{x})/2 + 1/12)·x^{−s−2}‖ ≤ (∑_{n} 1/(4π²n²))·(10N/√(−s.im))`.

This realizes the whole chain in one theorem:
- `fourier_exp_hasSum` — the `B₂` kernel as its Fourier series `∑ (1/4π²n²)·e(nx)`, from the banked
  circle expansion `fourier_hasSum_bernoulli2` scaled and `fourier n ↑x = e(nx)` (`fourier_eq_exp`).
- `intervalIntegral_tsum` — sum/integral interchange, discharged by an explicit `L¹` certificate
  (`∫⁻ ‖f_n‖ ≤ (1/4π²n²)(N−1)`, `∑ < ⊤` from summability of `1/n²`).
- `reflected_per_mode_bound` — each mode's oscillatory integral bounded **uniformly in `n`** by
  `10N/√(−s.im)` (second-derivative van der Corput; `g_n'' = s.im/x²` carries no `n`).
- `reflected_mode_sum_bound` — the mode sum bounded by the uniform per-mode bound times the finite
  coefficient sum.

Every link — `finite_em_identity`, the per-interval IBP and its `m`-summation (`sawtooth_ibp_sum`),
the `B₂` Fourier bridge, the interchange, the per-mode van der Corput, the mode sum — is banked and
axiom-clean. The reflected block's oscillatory integral obeys the square-root-cancellation bound the
approximate functional equation asserts. Sixteen van der Corput / sawtooth / assembly modules;
`[propext, Classical.choice, Quot.sound]` throughout.

The one remaining wire to the *literal* `∫_1^N ({x}−½)x^{−s−1}` of `sawtooth_ibp_sum` is elementary
constant arithmetic (the `+1/12` mean term `× ∫x^{−s−2}`, bounded by `N−1`, and the `(s+1)` factor) —
no oscillatory content, no new estimate.

---

## Addendum 15: the literal reflected-block remainder — composed, axiom-clean

**[PROVED HERE, Lean]** `RHTower/ReflectedB2Integral.lean : sawtooth_reflected_bound` (axiom-clean,
umbrella green): for `N ≥ 1`, `s.re ≥ −2`, `s.im < 0`,
`‖∫_1^N ({x}−½)·x^{−s−1}‖ ≤ ‖s+1‖·((∑_n 1/(4π²n²))·10N/√(−s.im) + (N−1)/12)`.

This composes `sawtooth_ibp_sum` (the Euler–Maclaurin integration-by-parts, sawtooth → `B₂`) with
`reflected_B2_integral_bound` (the mode-sum bound): peel the `(s+1)` factor, subtract the kernel's mean
`1/12` (an elementary `∫ x^{−s−2}` term, `‖·‖ ≤ N−1` by `x^{−σ−2} ≤ 1`), and apply the van der Corput
bound to the mean-zero part. The `B₂`-kernel integrability is the bounded-measurable fact
(`HasFiniteIntegral.of_bounded`, `measurable_fract`).

**The chain is now literal and complete**, from the centred fractional sawtooth `∫({x}−½)x^{−s−1}`
(what `finite_em_identity` ties to the reflected Dirichlet block) all the way to the square-root
cancellation bound, with every intermediate link banked and depending only on
`[propext, Classical.choice, Quot.sound]`. The reflected block obeys the bound the approximate
functional equation asserts — no residual, no elementary gap left.

---

## Addendum 16: reflected saddle lattice and the parity interface banked

**[PROVED HERE, Lean]** `RHTower/ReflectedSaddleLattice.lean`: for the negative Fourier reflected phase
`g_k(x) = -2π(k+1)x + T log x`, the stationary point is exactly
`x*_k = T/(2π(k+1))`, and the second derivative is `g_k''(x) = -T/x²`, independent of the mode `k`.
The formal public endpoints are `reflectedPhaseDeriv_eq_zero_iff`,
`reflectedPhaseSecond_independent`, and `reflectedPhaseDeriv_hasDerivAt`.

The same file names the finite saddle-mode carrier
`reflectedSaddleModes K T a b = {k < K | a ≤ T/(2π(k+1)) ≤ b}` and attaches the unit event list
`List.replicate card 1`. If that finite carrier has even cardinality, `reflectedSaddleFluxPaired_of_even`
constructs the ledger interface `LedgerFluxPaired`; `reflectedSaddleFluxList_two_dvd_sum_of_even` records
the resulting even total unit flux. The pairing itself is not an extra hypothesis: it is the consecutive
pairing already banked in `BandEdgePairingConstruction.lean`.

This is the exact saddle-lattice-to-parity interface promised by R7. It does **not** prove that the physical
AFE/reflection carrier has even saddle count, nor that endpoint orientation agreement holds; those are the
remaining charge-bridge burden. What is now formal is the precise handoff: reflected saddle geometry supplies
a finite mode lattice with mode-independent curvature, and any proof of its evenness immediately supplies the
paired-flux ledger required by the incidence/event route.

---

## Addendum 17: integer-grid collision parity of the reflected saddle lattice

**[PROVED HERE, Lean]** `RHTower/ReflectedGridParity.lean`: after normalizing the height as
`T = 2πC`, the analytic saddle equation and the arithmetic grid-collision equation are identical:

`reflectedSaddle (2πC) k = m  ↔  (k+1)m = C`.

Thus the integer-grid collisions of the reflected saddle lattice are the divisor antidiagonal
`C.divisorsAntidiagonal`. Reflection swaps the two factors `(n,m) ↦ (m,n)`. The nonfixed collisions
pair off by this involution, and the fixed locus is exactly the positive-square singleton `(r,r)` when
`r² = C`. The sharp parity theorem is

`reflectedGridCollisions_odd_iff_pos_square : Odd card ↔ ∃ r>0, r*r = C`.

Consequently, away from the positive-square fixed point, the collision unit event list has paired flux:
`reflectedGridCollisionFluxPaired_of_no_pos_square` and
`reflectedGridCollisionFlux_two_dvd_sum_of_no_pos_square`.

This is the first exact saddle-lattice-to-`ℤ/2` charge law on the R7 route: the reflected saddle/grid
carrier has no mysterious parity; its mod-2 obstruction is precisely the square fixed point of the
reflection hyperbola. What remains is no longer the lattice arithmetic. The remaining bridge is to prove
that the physical AFE/reflection charge carrier reduces to this collision carrier, or to state the extra
noncollision events and prove their parity cancellation.

---

## Addendum 18: weighted reflected-grid charge parity — square obstruction removed by even fixed weight

**[PROVED HERE, Lean]** `RHTower/ReflectedGridCharge.lean`: the unit collision count of Addendum 17 is not the final physical object; a charge carrier is weighted. The weighted theorem is:

`reflectedGridWeightedCharge_even_of_swap_invariant_even_fixed` — if a weight `q` on the reflected grid-collision carrier is invariant under the factor-swap reflection `(n,m) ↦ (m,n)`, and every fixed diagonal collision has even weight, then the total charge `∑ q` over `reflectedGridCollisions C` is even.

The deck form is also banked:

`reflectedGridWeightedCharge_deckRed_two_eq_one_of_swap_invariant_even_fixed`.

Two corollaries isolate the cases from Addendum 17. If there is no positive square fixed point, swap-invariance alone gives even weighted charge (`reflectedGridWeightedCharge_even_of_swap_invariant_no_fixed`). If `C=r²`, it is enough to prove the single fixed weight `q(r,r)` is even (`reflectedGridWeightedCharge_even_of_swap_invariant_square_fixed_even`).

This removes the apparent square obstruction for the physical charge route: the only unpaired lattice point is harmless once its fixed-locus charge is even — exactly the kind of input supplied by reflection parity at a genuine fixed/ramified locus. The remaining bridge is now sharply typed: identify the AFE/reflection charge weight `q`, prove its swap-invariance on the divisor-antidiagonal carrier, and prove the fixed square weight is the even reflected/ramified local order. Off-grid events, if present, must be supplied as a separate paired class.

---

## Addendum 19: analytic local-order charge closes the square fixed-weight input

**[PROVED HERE, Lean]** `RHTower/ReflectedGridAnalyticCharge.lean`: the remaining fixed-square input from Addendum 18 is automatic when the reflected-grid charge weight is an analytic vanishing order. Define

`reflectedGridAnalyticCharge C F center = ∑_{x∈reflectedGridCollisions C} (analyticOrderAt (F x) (center x)).toNat`.

The theorem `reflectedGridAnalyticCharge_even_of_swap_order_even_fixed` proves: if the local orders are invariant under the factor-swap reflection `(n,m) ↦ (m,n)`, and every diagonal fixed germ is analytic, reflection-symmetric about its center, and finite-order, then the total analytic charge is even. The deck form
`reflectedGridAnalyticCharge_deckRed_two_eq_one_of_swap_order_even_fixed` gives the same result as `deckRed 2 (charge)=1`.

The square-specialized theorem `reflectedGridAnalyticCharge_even_of_swap_order_square_reflection` states the exact fixed-point case: when `C=r²`, the single diagonal weight `(r,r)` is even by `analyticOrderAt_even_of_reflection`; no independent square-weight parity assumption remains.

The R7 saddle-parity bridge is now reduced to a concrete construction problem, not a parity problem: construct the actual AFE/reflection germ family `F` and centers, prove that its local orders are invariant under the divisor-antidiagonal swap, and prove that the physical charge carrier has no additional off-grid events except separately paired classes. The fixed square itself is already handled by reflection parity.

---

## Addendum 20: completed-carrier reflected-grid charge parity

**[PROVED HERE, Lean]** `RHTower/ReflectionParity.lean` now has the local germ form

`analyticOrderAt_even_of_reflection_eventually`:

if `f` is analytic at `c`, has finite order at `c`, and satisfies `f(2c-s)=f(s)` eventually near `c`, then `(analyticOrderAt f c).toNat` is even. This removes the global-entire hypothesis from the fixed-point parity input and is the form needed for carriers analytic only on a strip.

**[PROVED HERE, Lean]** `RHTower/ReflectedGridCompletedCharge.lean` instantiates the analytic charge package with the concrete completed finite carrier `completedGN N`. It defines

`reflectedGridCompletedCharge C N center = reflectedGridAnalyticCharge C (fun _ => completedGN N) center`.

The theorem `reflectedGridCompletedCharge_even_of_center_swap` proves: if the center assignment on `reflectedGridCollisions C` is swapped by `center(swap x)=1-center(x)`, all centers lie in the open strip, diagonal fixed collisions have center `1/2`, and all involved local orders are finite, then the completed-carrier reflected charge is even. The deck form `reflectedGridCompletedCharge_deckRed_two_eq_one_of_center_swap` gives `deckRed 2 (charge)=1`.

The completed carrier supplies both analytic ingredients: `completedGN_orderAt_one_sub` gives off-diagonal order-swap invariance, and `completedGN_eventually_reflection_half` gives the local symmetry at the diagonal fixed point.

The remaining R7 bridge is now purely geometric/accounting: construct the actual center map from the AFE saddle/grid carrier to the completed-carrier zero germs, prove the finite-order side condition for those centers, and prove that any off-grid event class is paired or absent. The parity algebra and completed-carrier local-order transfer are closed.
