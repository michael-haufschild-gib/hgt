# ALT ROUTE — the foldon-frustration route (if the parity front is right-idea/wrong-constraint)

**Register: SEARCH.** All claims `[CONJECTURE]`. Origin: wild-analogy collision (seed
2937278250865098734) of the RH constraint object with **ant-foraging** and **protein-folding**,
method **revisualise**. Written to be *unexplored by us and by the literature*, and honestly:
it may be wrong. The value is that it fails or bridges in a place nothing else touches.

## 0. The object, revisualised
Λ = Γ·ζ is fixed by TWO simultaneous constraints that coincide only on Re = 1/2:
(R) reflection self-duality (functional equation s↔1−s), and (E) multiplicative positivity
(the Euler product). The parity/conservation front makes the *saturating* constraint a discrete
mod-2 winding (a topological invariant of R). The Weil thread showed that is the mod-2 shadow of an
integer index whose true saturation is infinitary (E). So: right idea (a discrete/rigid saturation),
possibly wrong constraint (monodromy parity).

## 1. The collision
- **Ant-foraging.** A *global* optimum (shortest path) crystallises from a *local* balance of
  reinforcement vs. decay on a marker field — no agent knows the global structure. Symmetry between
  two paths is broken by fluctuation + positive feedback on a *decaying* field. The optimum is a
  THRESHOLD (deposition = evaporation), not a flow to a minimum.
- **Protein-folding.** A 1D sequence folds to a unique 3D native state that a blind search could never
  find (Levinthal). It works because the sequence is **minimally frustrated**: local constraints are
  mutually consistent, so the landscape is a FUNNEL. Folding is LOCAL and SEQUENTIAL (foldons nucleate
  and propagate). Anfinsen: the *constraint is the sequence*; the fold is its unique satisfier.

**Shared shape.** A global configuration (path / fold / zero-locus) is selected not by a generative
flow but by a **minimal-frustration** condition on many *local* constraints — the configuration that
satisfies the most local constraints simultaneously, revealed by a *local, sequential* nucleation.

## 2. The route
`[CONJECTURE]` **RH = the primes are a minimally-frustrated sequence for folding Λ onto the critical
line.** A generic Dirichlet series (Davenport–Heilbronn) is FRUSTRATED — it folds wrong, zeros scatter
off the line. The Euler product (multiplicativity) is the *foldability* property that removes the
gross frustration. RH is the statement that the *residual* frustration also vanishes: at every height
the local prime foldon is consistent with R, so zeros nucleate ON the line.

Three concrete objects to build:

1. **A local frustration functional `F_N(T)`** — the incompatibility, in a height-`T` window, between
   the forward fold (primes ≤ N) and its reflected (FE) image. Zero frustration ⟺ the finite fold is a
   reflection eigen-configuration in that window ⟺ zeros nucleate on the line there.
2. **The frustration decomposition** `F = F_mult + F_res`: `F_mult` is killed by the Euler product
   (the part that separates the primes from Davenport–Heilbronn); `F_res` is the residual — the RH
   core, now a *local, per-height* object rather than a global quadratic form.
3. **The foldon recursion** — the genuinely distinguishing structure. By the approximate functional
   equation, zeros up to `T` are folded by primes up to `√(T/2π)`; doubling `T` adds only the primes in
   `(√T, √2T)`. So `F(2T)` should be expressible from `F(T)` plus a *local prime increment*. RH = this
   recursion has zero-frustration as a **stable/contractive fixed point** (no frustrated foldon ever
   nucleates an off-line zero).

## 3. Why this is not "constraint→flow" backsliding
The foldon recursion is NOT a generative rule for Λ (still hypertranscendental — no algebraic
differential equation). It is the *folding pathway*: a sequential revelation of the global constraint,
the way a protein's foldon order reveals a structure that is itself fixed by global energy, not grown.
The object stays constraint-fixed; the recursion books how local consistency propagates. That is a new
sense of "constraint, not flow" — the flow is on the *consistency measure*, whose fixed point is the
constraint.

## 4. The sharp fork that decides new-vs-reduces-to-known
The danger: `F` collapses to the Weil quadratic form (global) or to the log-gas/Coulomb-gas ensemble
(known statistical-mechanics analogy). The distinguishing feature is **LOCALITY**:
- Log-gas has LONG-RANGE (logarithmic) interactions — no folding locality.
- Folding has SHORT-RANGE frustration and a contractive recursion.

`[CONJECTURE, with teeth]` The AFE is *itself a locality statement*: a zero at height `T` does not
need primes `≫ √T`. Locality is the folding-funnel signature. So the decisive question is whether the
frustration recursion across `√T`-scales is **contractive** (short-range, funnel ⟹ RH) or only
marginally so (long-range ⟹ reduces to the log-gas, route dead). This is a genuine, decidable fork
no current lane poses.

## 5. Connection to banked machinery (the route is not disconnected)
The winding-rigidity identity `gN_line_winding_rigidity` says that on a sign-constant segment the
completed carrier's phase EXACTLY anti-rotates the archimedean winding — a **zero-frustration fold**
(the fold is locally perfect). A sign change (a seam crossing) is where the fold "clicks" a zero into
place — a **foldon nucleation**. The winding FLOOR (`windingRate_ge`) forces a crossing every ~`1/log T`
— the **foldon spacing** (`SeamCrossingRigidity.lean`). So the frustration route re-reads our own
machinery as folding kinetics; the genuinely NEW content is (2) the frustration DECOMPOSITION and (3)
the foldon RECURSION — neither of which the winding/parity work builds.

## 6. First concrete step (not theatre)
Define `F_N(T)` precisely as the windowed mismatch between the finite carrier and its FE image, and
ask whether `F(2T) ⩽ κ·F(T) + (increment from primes in (√T,√2T))` holds with `κ < 1` — a contractive
foldon recursion. Pre-register: **the multiplicative structure makes the increment small (foldable)
but κ is NOT `< 1` from multiplicativity alone** (else Euler ⟹ RH, false); the residual `κ`-gap is the
RH core. Testing the recursion's contractivity — locality vs long-range — is the decisive experiment,
and it uses the banked winding/crossing objects as the frustration meter. If contractive: a new,
literature-unseen mechanism. If not: the route reduces to the log-gas and dies cleanly — which is
itself worth knowing.

## 7. Novelty gate
"Would a competent literature search produce this?" Searching *RH + spin glass* → Coulomb/log-gas
equilibrium statistics; *RH + protein folding* → essentially nothing; *RH + frustration* → RMT
spin-glass analogies, but not the folding-funnel SELECTION (primes as an evolved-foldable sequence),
not the frustration DECOMPOSITION, not the foldon RECURSION / locality fork. The bridge is to the
*kinetics of disordered self-assembly*, in a non-standard direction. Verdict: BRIDGE, not
reduce-to-known — keep it as a moonshot.

## 8. Formalization outcome (route followed to its provable core)

`RHTower/FoldonFrustration.lean` (axiom-clean) formalizes the route's provable content and locates its
open frontier precisely:

- **Frustration = off-line index.** `foldonFrustration s m = Σ mᵢ`, the integer total order of the
  off-line zeros — the same index whose mod-2^k reduction is the deck class. So the route's central
  object reduces to the signature/deck work; it is not a new object.
- **The genuinely new, formalized content — symmetry-depth blindness.** Built the mathlib-gap tool
  `card_group_dvd_weighted_sum` (free finite-group action ⟹ `|G| ∣ Σ mᵢ`). Crown
  `frustration_invisible_below_reflection_depth`: a free reflection symmetry of order `2^k` hides the
  frustration from the first `k` rungs of the parity ladder; a pure `2^k`-orbit first appears at rung
  `k+1` (deck class `−1`). The deeper the reflection symmetry of the buckling, the higher the ladder
  must climb — a precise quantification the parity front alone never states.
- **The three-module picture.** With W2 `SeamCrossingRigidity` (the winding floor FORCES on-line
  nucleations — the clean folds) and `SignatureParity` (the index→parity discard), the route's entire
  PROVABLE half is formalized: forced clean folds + the off-line frustration is the deck index whose
  ladder-blindness is set by its symmetry depth.
- **The open frontier (named, not an effort gap).** The route's contractivity / locality fork — is the
  frustration recursion short-range (folding funnel ⟹ RH) or long-range (log-gas)? — needs the
  approximate functional equation, and the contractivity step is itself RH-adjacent open mathematics.
  There is no theorem to prove there; it is the frontier. Building the AFE would only let one STATE the
  recursion, whose contractivity remains open.

**Verdict.** The route BRIDGES (reframes RH as folding kinetics and exposes exactly what the parity
ladder discards — the reflection-symmetric frustration, up to its 2-adic depth) and its provable
content is now formalized; its open half coincides with the analytic RH-grade core, reached cleanly.

## 9. Attack on the contraction fork — verdict: critical log-gas (Mertens-marginal)

`[CONJECTURE / heuristic, labelled]` The decisive fork (§4, §6) is settled by the cross-scale
correlation of the foldon increment.

**The increment decays at the critical harmonic rate.** Decompose `log|carrier|` by dyadic prime
blocks. Primes in different ranges are multiplicatively independent (phases `p^{-it}` equidistribute
independently — Bohr/Selberg), so block contributions are ≈independent, and the variance added by the
block `(Y,2Y]` is `½ Σ_{Y<p≤2Y} 1/p ∼ 1/(2 log Y)` (Mertens). Per foldon `N→2N` (height `T→4T`) the
increment variance is `∼ 1/log N → 0` — it vanishes. But the totals `Σ_{blocks≤√T} 1/log Y ∼
log log T → ∞`. The increments decay at exactly the **harmonic borderline** — `1/log Y` summing to
`log log T` (matching Selberg's variance `½ log log T` and the FHK log-correlated / critical-GMC
picture). The fold ALMOST converges but marginally fails, logarithmically.

**Why the folding-specific hope fails.** Multiplicative independence is double-edged: independent
per-scale contributions ACCUMULATE (log-correlation), they do not contract. The funnel would need
ALIGNMENT (increments cohering toward the on-line state), which must come from the reflection — but
individual primes do NOT satisfy the functional equation (only the completed product does), so no
finite prime block is FE-consistent and there is no per-foldon funnel. Same verdict as the Weil-form
thread (infinitary alignment), now kinetic.

**Verdict.** The `√T`-foldon increment is NOT a self-contained contraction; the route sits at the
CRITICAL point — increments decay at the Mertens rate `1/log N`, summing to `log log T`, the
critical-log-correlated borderline. The folding route does not beat the log-gas; it IS the critical
log-gas, and the marginality (harmonic divergence, not convergence) is exactly why RH is hard — and,
from the folding side, why the de Bruijn–Newman constant is exactly `0` (tuned to criticality). The
partial contraction that exists is the classical zero-density estimate `N(σ,T) ≪ T^{c(1−σ)}`; the gap
to zero is the critical fluctuation multiplicativity produces. Reduces to known (FHK/GMC +
zero-density), reached cleanly — the pre-registered "dies at the fork" branch, sharply located.

**What survives (the split).**
- Analytic / magnitude side → critical log-gas (Mertens-marginal). No folding win. Dead.
- Discrete / symmetry side → the AFE causal cone's DISCRETE shadow is the parity ladder's
  symmetry-depth blindness (`FoldonFrustration.lean`), a theorem the log-gas does not see. Alive.

Forward move: not the analytic contraction (provably critical). Ask whether the discrete causal cone
yields a FOLDING-IMPROVED zero-density statement — reflection-symmetry depth of a would-be off-line
cluster forcing it below a resolvable threshold. A concrete sub-RH target living entirely on the
discrete side, where the folding picture still has what the log-gas lacks.

## 10. Test: does the discrete causal cone give a folding-improved zero-density bound? — No

`[reasoning, labelled]` Target: a magnitude bound on the off-line index that, combined with the ladder
residue `RH_{2^k}` (banked: `2^k ∣ every off-line box index`), closes RH via
`2^k ∣ index ∧ 0 ≤ index < 2^k ⟹ index = 0`.

**Finding — density is NOT the bottleneck.** In a unit-height box at height `T` the TOTAL zero count is
`∼ (log T)/2π` (Riemann–von Mangoldt), so the off-line index is `< log T`, already `< 2^k` for any
`k > log₂(log T/2π) ∼ log log T`. The magnitude half is free locally — no hard density theorem needed.
The entire difficulty is the RESIDUE half (`RH_{2^k}` to rung `∼ log log T`). So the causal cone cannot
improve zero-density: density is the wrong target. What the cone does is LOCALIZE the residue — by the
AFE the deck class at height `T` is fixed by primes `≤ √T`, so `RH_{2^k}` up to `T` is finite on primes
`≤ √T` (effectivity/finiteness, known); it does not make the residue easier.

**The two sides meet at `log log T`.** Ladder depth to certify RH up to `T` on unit boxes is
`k ∼ log log T`; the analytic field is critical at the SAME scale (Selberg variance `½ log log T`, the
log-correlated/GMC scale from §9). Discrete resolution depth = analytic critical scale = `log log T`.
That coincidence — not a bound — is the route's genuine contribution.

**Verdict.** No folding-improved zero-density statement (density is locally free; the bottleneck is the
deck-class residue). The folding route's discrete side reduces to the existing MWM conservation program
(deck-class-from-boundary) + AFE finiteness — both in hand. The wild-analogy route, tested to
exhaustion, CONVERGES BACK to the main MWM lane. That convergence is the result: an independent route
(ant-foraging × protein-folding) lands on the deck-class-residue localization, evidence the MWM lane is
the structurally load-bearing object.

**Net yield of the folding exploration (tallied honestly).**
- Analytic side → critical log-gas, Mertens-marginal. Dead, sharply located (§9).
- Discrete side → converges to MWM deck-class localization + AFE finiteness. Existing.
- New & kept → the symmetry-depth blindness theorem (`FoldonFrustration.lean`) + the `log log T`
  unification of ladder resolution depth with the analytic critical scale.

**Forward move implied.** Not a density bound, not the analytic contraction (both closed). The residue
is the sole bottleneck and is already localized to finite prime data — so the productive target is the
MWM lane itself: prove `RH_{2^k}` for growing `k` from causally-local boundary data (W1/W3). The
folding detour's payoff is confirming, from an independent direction, that THAT is the load-bearing
object — handing it one new tool (symmetry-depth blindness) and one calibration (depth `∼ log log T`).
