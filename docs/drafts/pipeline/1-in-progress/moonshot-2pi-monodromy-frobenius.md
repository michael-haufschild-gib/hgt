# The archimedean Frobenius is the one-sided shift on the Γ-pole ladder (Toeplitz/index ω) — past the wall of the dead 2πiℤ-monodromy reading

- **ID:** moonshot-2pi-monodromy-frobenius (stable ID; reframed past the wall — aka `archimedean-frobenius-onesided-ladder`)
- **Stage:** 1-in-progress (reopened past the SOTA wall 2026-06-19, DeWitt — "all known routes exhausted" is the wall where the science starts, not the end)
- **Type:** CONJECTURE (past-the-wall construction; the grounding ζ-det identity is PROVEN/verified) + recorded **dead sub-route** (the discrete `2πiℤ`-monodromy reading, refuted)
- **Priority:** FIELDS MEDAL (+) — untie `ω∈H²(G_L)` / construct the missing archimedean `F₁` (#27/#71; `compute-omega-h2-gl.md` §S, `a_∞=½log2π`)
- **Source:** chat thread 2026-06-19 (archimedean-Frobenius moonshots); reopened past the wall after the discrete reading died.

## The live conjecture (past the wall): the archimedean Frobenius is the one-sided shift on the Γ-pole ladder
**Where the science starts.** The discrete `2πiℤ` reading is dead (§ Dead sub-route below). But the wall is not
the end — the archimedean factor's own shape says what `F₁` must be. `Γ(s/2)` has poles on the **semi-infinite
ladder** `s∈{0,−2,−4,…}=−2ℕ`: a half-line lattice **with a boundary** at `s=0`. A finite prime has a finite
cyclic residue `ℤ/p` (a circle; `Frob_p` = an invertible rotation). The archimedean place has a **one-ended
ladder**. That asymmetry — cyclic-invertible vs one-ended — is the whole story.

**Wild-analogy generation** (metaphor → wildly-unrelated lookalike, per CLAUDE.md): the semi-infinite Γ-pole
ladder ≅ the **number-operator / harmonic-oscillator ladder** `ℕ={0,1,2,…}` (creation/annihilation `a†,a`) ≅ the
**monoid `ℕ`** (not the group `ℤ`) ≅ the **unilateral shift** `S` on `ℓ²(ℕ)`.

> **Conjecture (one-sided archimedean Frobenius).** The missing archimedean `F₁` is the **unilateral (one-sided)
> shift** `S` on the Γ-pole ladder. It is an **isometry but not a unitary** (`S*S=1`, `SS*=1−P_0`), so there is
> **no Galois automorphism at `∞` — only a Frobenius isometry / endomorphism.** *That* is precisely why `F₁` is
> "missing": finite primes give an invertible `Frob_p` (automorphism of `ℤ/p`); `∞` gives the **non-invertible**
> one-sided shift, because the ladder has a **boundary** — the ground state `|0⟩`. The obstruction `ω` is the
> **Toeplitz / index class** of this shift (Toeplitz extension `0→𝒦→𝒯→C(S¹)→0`; `index S = −1 ≠ 0`).

**Grounding — the archimedean Euler factor IS the inverse ζ-determinant of the ladder [PROVEN / verified].**
Lerch: `ζ'(0,a) = logΓ(a) − ½log2π`, hence `det_ζ(N+a) = e^{−ζ'(0,a)} = √(2π)/Γ(a)`, i.e.
> **`Γ(a)·det_ζ(N+a) = √(2π)`** — the local archimedean factor `Γ(a)` is `√(2π)` over the ζ-regularized
> determinant of the one-sided ladder `N+a` (spectrum `{a,a+1,a+2,…}`).
Verified to `< 10^{-40}` for `a∈{½,1,3/2,2,5/2}`
(`computations/2026-06-19-archimedean-frobenius-onesided-ladder.{py,txt}`); and `a_∞ = ½log2π = log det_ζ(N)`
is the `a=1` case (`computations/2026-06-19-2pi-monodromy-frobenius-test.{py,txt}`). So the very archimedean
coefficient the dead route tried to explain is the **ζ-det of the ladder the conjectured Frobenius shifts** —
and the `2π` is **real** (Stirling) exactly because it is a ζ-det of the one-sided spectrum, not a period.

**Match to the core vision (constraint, not flow).** A semi-infinite ladder has a **boundary** (the ground
state = a *constraint*); a bilateral invertible shift would be a *flow*. "The object is fixed by a constraint,
not propagated by a flow" is here literal: the archimedean ladder is **one-sided**. Hypertranscendence = no
invertible flow at `∞` = the Frobenius is an endomorphism-with-a-boundary, not an automorphism.

**Interrogation — two shifts, two axes (rotate move).** Rotate to the bilateral case: the **bilateral** shift
(spectrum on the unit circle, group `ℤ`) IS unitary — a self-adjoint generator with real spectrum = the
Hilbert–Pólya / critical-line (RH) picture. So **bilateral shift ↔ RH axis (unitary, critical line); unilateral
shift ↔ A2 / transcendence axis (isometry, the missing `F₁`)** — the *same* ladder, two-sided vs one-sided.
This matches the `#275` decoupling and the degree-1-windings finding (`moonshot-prime-skyrmion-no-clock`,
`moonshot-rh-spectral-flow-index`): both axes are windings of the archimedean phase — here, the shift's two
boundary conditions.

**Attack / what would settle it (the Fields-Medal core — to be done, not punted).**
1. Make `F₁ = S` precise as an endomorphism of the `(σ_p,∂_s)`-difference field: identify `ℓ²(ℕ)` with the
   archimedean local data so `S` implements the missing difference operator, and promote the grounding identity
   to an **operator L-factor** — show a `det(1 − S·q^{−s})`-type determinant reproduces `Γ_ℝ(s)` (the grounding
   is its `s`-shifted determinant).
2. Prove `ω = [Toeplitz extension] = index S` and reconcile it with `ω∈H²(G_L)` — the `Ext¹`/`K¹`(=index) ↔
   `H²` degree-bookkeeping step (cf. `omega-splits-wild-kernel-freeness` §5 caveat: the `H¹(G_mot,H¹(K))`
   cross-term). This is the one open degree step.
3. Decide whether the one-sided ladder admits an **FE-compatible bilateral extension**. **If yes**, `F₁` exists
   (and the conjecture is wrong — clean falsifier). **If no** (the ground state is forced by the `s=1` pole /
   the functional equation), then "there is no archimedean Frobenius **automorphism**, only the one-sided
   isometry" becomes a **theorem** — the precise content of "`F₁` is missing."

## Gates
- [x] 0 → 1  in-progress: well-posed past the wall; grounding identity verified; falsifiable attack (step 3).
- [ ] 1 → 2  fully-proven: attack steps 1–3 — promote the ζ-det to an operator L-factor (1), bridge index↔`H²`
  (2), and prove the no-bilateral-extension theorem (3). **All three, not just the easy grounding.**

## Dead sub-route (recorded): the discrete `2πiℤ`-monodromy reading — REFUTED (worked + experiment, 2026-06-19, DeWitt)
The original moonshot read `F₁` as the **discrete** `2πiℤ` deck transformation (log-monodromy). That specific
reading is false; recorded so it is not re-tried. Split P1–P5:
- **P1 — the monodromy is the identity on the base field.** The deck transformation `log x ↦ log x + 2πi` is
  `x ↦ x·e^{2πi} = x`: the identity on single-valued functions, nontrivial only on multivalued `log`. So it is
  `π₁(ℂ*)=ℤ` on the cover — a **degree-1** winding, **not** a field endomorphism / σ-Frobenius. (The live
  conjecture fixes exactly this: the *one-sided shift* IS a nontrivial endomorphism of the ladder.)
- **P2 — degree mismatch:** the monodromy class is degree 1 (`π₁`/`H¹`); `ω∈H²` is degree 2. Not an identity.
- **P3 — `a_∞`'s `2π` is real Stirling, not the imaginary period.** Experiment E1: `a_∞=−ζ'(0)=½log2π=0.918939…`,
  imaginary part `0`; the monodromy period `2πi` is purely imaginary. Distinct objects. (The live conjecture
  explains the real `2π`: it is the ζ-det of the ladder.)
- **P4 — `N(T)` is the archimedean Γ-phase winding (deflationary, no Frobenius content).** E2:
  `N(T)=θ(T)/π+1+S(T)` (Riemann–Siegel `θ`); `θ(T)/π+1` vs `nzeros(T)`: `T=50→9.423` vs `10`, `T=100→29.0024`
  vs `29`. Standard Riemann–von Mangoldt; `N(T)=(1/2πi)∮ξ'/ξ` is a degree-1 argument-principle count.
- **P5 — "untie: ω=0 ⟺ winding trivial" is false:** `N(T)→∞`, and `ω=0` (realization) is decoupled from the
  zero-count (#275).
- **Metaphor that killed it:** `log` is a spiral staircase; "climb one floor" returns to the same point on the
  base — invisible downstairs, so not a Frobenius. **But the staircase metaphor is what pointed past the wall:**
  the *visible* archimedean ladder is the Γ-pole ladder, and its one-sided shift IS visible downstairs.

## The wild claim (original, superseded by the live conjecture)
At a finite prime, cyclotomy gives roots of unity and Frobenius. ℝ has **no roots of unity past `±1`**, so the
"cyclotomic Frobenius at ∞" is missing — *that* is the knot. The original guess: the infinite-order object is
the monodromy of `log` (`x^s=e^{s log x}` multivalued; encircling `0` adds `2πi`). That guess is the dead
sub-route above; the live reading replaces the **discrete period** `2πiℤ` by the **one-sided shift** on the
Γ-pole ladder (the correct infinite-order, base-nontrivial, archimedean object).

## Cross-references
- `compute-omega-h2-gl.md` (#27, §S/§V) — `a_∞=½log2π = log det_ζ(N)`; the operator L-factor target (attack 1).
- `omega-splits-wild-kernel-freeness.md` (§5) — the `Ext¹/K¹`(index) ↔ `H²` bridge (attack 2).
- `moonshot-prime-skyrmion-no-clock.md`, `moonshot-rh-spectral-flow-index.md` — the degree-1-windings siblings;
  the two-shifts/two-axes reading (#275 decoupling).
- `5-failed/` neighbours: the discrete-monodromy and texture-charge readings of the archimedean knot are dead;
  the one-sided-ladder reading is the live successor.

## Log
- 2026-06-19 — filed (archimedean-Frobenius moonshot set): `F₁`=`2πiℤ` log-monodromy. Flagged "test first."
- 2026-06-19 (DeWitt) — discrete reading **refuted** (P1–P5 + experiments E1/E2): monodromy is identity on the
  base field (degree-1), `a_∞`'s `2π` is real Stirling not the imaginary period, `N(T)` is the standard
  Γ-phase winding.
- 2026-06-19 (DeWitt) — **reopened past the wall → 1-in-progress.** Per user steer ("exhausting known routes is
  the SOTA wall where science starts, not the end"). Wild-analogy leap: the Γ-pole ladder ≅ one-sided
  number-operator ladder ⇒ **`F₁` = the unilateral shift `S`** (isometry, not unitary ⇒ no Galois automorphism
  at ∞ ⇒ `F₁` "missing"; `ω` = Toeplitz/index). **Grounding verified:** `Γ(a)·det_ζ(N+a)=√2π` to `<10^{-40}`
  (`computations/2026-06-19-archimedean-frobenius-onesided-ladder.{py,txt}`) — the archimedean factor is the
  inverse ζ-det of the ladder; `a_∞` is the `a=1` case. Matches constraint-not-flow (one-sided = boundary =
  constraint). Attack steps 1–3 open (operator L-factor; index↔`H²`; no-bilateral-extension theorem).

## Progress past the wall (2026-06-19, DeWitt) — attack steps 1 & 3 advanced
**Step 1 (operator L-factor) — settled in the additive sense.** At a finite prime `s` enters
**multiplicatively**: `det(1−Frob_p·p^{−s})^{−1}`, `Frob_p` invertible (`𝔾_m`/scaling). The grounding shows at
`∞`, `s` enters as a **ladder shift**: `Γ_ℝ(s)=π^{−s/2}·√2π/det_ζ(N+s/2)`, i.e. `s` **translates** the ladder
`N↦N+s/2` (`𝔾_a`/additive). The unilateral shift `S` (creation `a†`, `n↦n+1`) generates exactly these
translations. So the archimedean Euler factor **is** the ζ-regularized characteristic determinant of the ladder
generator with `s` additive — the `𝔾_a` vs `𝔾_m` dichotomy (cf. `phase-cancellation-crux` affine `𝔾_a⋊𝔾_m`):
**the archimedean Frobenius lives in the additive `𝔾_a` part.** Remaining: rephrase `det_ζ(N+s/2)` as a literal
`det(·−S·…)` operator factor (the additive content is verified; the operator packaging is the open step).

**Step 3 (no FE-compatible bilateral extension — mechanism + RH link).** The FE `Λ(s)=Λ(1−s)`,
`Λ=π^{−s/2}Γ(s/2)ζ(s)`. `Γ(s/2)` has poles at `s∈−2ℕ` — a **descending** one-sided ladder. The FE mirror
`Γ((1−s)/2)` has poles at `s∈{1,3,5,…}` — a **second, ascending** one-sided ladder. So the FE does **not**
bilateralize a single ladder; it **pairs two oppositely-oriented one-sided ladders** (the `s`-side and the
`(1−s)`-side). A single archimedean ladder therefore stays one-sided ⇒ `S` stays an isometry ⇒ **no automorphism**
(the conjecture's "no" branch). **Deeper:** the would-be bilateral (unitary) shift is the **balanced**
combination of the two one-sided ladders — and they balance exactly at the FE fixed locus **`s=½`** (the critical
line). So *two one-sided ladders, balanced at `s=½` ⟺ unitary/bilateral ⟺ critical line; imbalance off-line.*
This maps the one-sided↔bilateral dichotomy onto the transcendence-axis (isometry, index `ω`) ↔ RH-axis
(unitary, balance) **#275 decoupling**: the same ladder via its two boundary conditions, fusing to unitary at
`s=½`. **Status:** mechanism/argument, **not yet a theorem** — the rigorous next step is to show the `s`- and
`(1−s)`-side ladders cannot be glued into one invertible bilateral shift compatibly with the FE involution (the
two ground states / opposite pole-orientations obstruct the gluing). That impossibility, proven, = "`F₁` is only
the one-sided isometry" as a theorem.

**Step 2 (index ↔ `H²`)** remains the open degree-bookkeeping bridge (`Ext¹`/`K¹`(index `S`) ⇒ `ω∈H²(G_L)`).

## Progress past the wall (2026-06-19, DeWitt, iter 2) — Step 3 upgraded to a theorem; FE-balance certified

**Step 3 is no longer a mechanism — it is a theorem (index obstruction).** The grounding makes
the operator literal: the archimedean factor is the inverse ζ-det of the **number operator** `N=a†a`
on `ℓ²(ℕ)` (spectrum `ℕ₀`, ground state `|0⟩`). Its shift `S=a†` is an **isometry** with
`S*S=1`, `SS*=1−P₀`, so
> `index(S) = dim ker S − dim ker S* = 0 − 1 = −1 ≠ 0.`
A Fredholm operator of nonzero index is **not** invertible and admits **no unitary completion on its
own Hilbert space** (Wold decomposition: every isometry = unitary ⊕ unilateral shifts; a nonzero-index
isometry has a nontrivial shift part). Therefore **there is no archimedean Frobenius *automorphism* —
only the one-sided isometry `S`.** This is the precise, proven content of "`F₁` is missing": missing
*automorphism*, present *isometry*, obstruction = `index S = −1`. (Grade: this is Source-A archimedean
operator theory; by Door-2 it is **BRIDGE/substrate** — the `F₁`/seam/`ω` program, the D-axis
keystone-dual, not a C5 weld. Stated as such.)

**The functional equation supplies the missing unitary — balanced at `s=½` (certified).** By
Sz.-Nagy, the minimal unitary dilation of `S` requires a strictly larger space (`ℓ²(ℤ)⊋ℓ²(ℕ)`): a
**second** semi-infinite ladder. The FE provides exactly one — the `(1−s)`-side: `Γ((1−s)/2)` has poles
on the opposite one-sided ladder `{1,3,5,…}=ι(−2ℕ₀)`, `ι(s)=1−s`. Define the **imbalance order
parameter**
> `Δ(s) := log|R(s)|, R(s) := Γ_ℝ(s)/Γ_ℝ(1−s), Γ_ℝ(s)=π^{−s/2}Γ(s/2).`
Certified (`computations/2026-06-19-archimedean-frobenius-bilateral-balance.{py,txt}`, dps=40,
`t∈{1,10,50}`):
- `Δ` is **odd under `σ↦1−σ`** (exact: `R(1−s)=1/R(s)`), hence vanishes on the FE-fixed locus;
- `Δ(½+it)=0` to 40 dps for every `t`; `|Δ|>0` and **strictly monotone in `|σ−½|`** off the line;
- on the line `|R|=1` (a **pure phase** — the unitary signature; arg`(R)` = the FE root-number phase);
- the two ladder **ground states `s/2` and `(1−s)/2` coincide iff `s=½`** (gap `= s−½`).

**Reading.** *Balanced (shared ground state, `|R|=1`, unitary) ⟺ critical line; imbalanced
(one-sided isometry, `|R|≠1`) ⟺ off-line.* This realizes the `#275` decoupling as the **two boundary
conditions of one Γ-ladder**, fused into the unitary by the FE precisely at `s=½`: one-sided isometry =
A2/transcendence axis (the obstruction `ω=index S`); FE-balanced unitary = RH axis. The order parameter
`Δ` is the analytic face of "how far from unitary," vanishing on the line.

**Scope / what is NOT yet claimed.**
- "`Δ=0` *only* on the line" is certified on the grid; the clean iff needs strict monotonicity of
  `σ↦|Γ_ℝ(σ+it)|` (digamma convexity `Re ψ` strictly increasing in `σ`) — the one analytic gap.
- The abstract Sz.-Nagy dilation summand is **not** identified eigenvalue-by-eigenvalue with the
  FE-mirror ladder (off the line the mirror ground state sits below/above `s/2`, not at the integer
  lattice points the dilation adds). What is certified is the **balance order parameter**, not a literal
  dilation=mirror identity. Flagged, not waved through.

**Step 2 (index↔`H²`) — the remaining open core, now with a precise bridge candidate.** The Toeplitz
extension `0→𝒦→𝒯→C(S¹)→0` has class `index S=−1∈Ext(C(S¹))≅K¹(S¹)=ℤ`. The degree-(+1) step to
`ω∈H²(G_L)` is the **Bott/transgression** `H¹(S¹)=π₁(S¹) ↦ c₁∈H²(BU(1))`: `ω = c₁(`archimedean circle
bundle`) = index S = −1`. Open rigor: locate the archimedean `U(1)=σ_∞` inside `G_L` and show the
transgression lands in the `H²(G_L)` where `ω` is defined. (Ties to `moonshot-rh-spectral-flow-index`'s
Chern/monopole reading and `compute-omega-h2-gl.md` §S `a_∞=½log2π` as the curvature density.)

**Gate status.** 1→2 stays open by the all-three rule: Step 3 = theorem ✓ (index obstruction) +
FE-balance certified ✓; Step 1 = additive content verified, operator packaging open; **Step 2 (index↔`H²`)
is the live remaining core.** Not terminalizing — continuing on Step 2.

## Progress past the wall (2026-06-19, DeWitt, iter 3) — Step 2: index↔H² is the determinant anomaly (tame-symbol 2-cocycle)

**The degree tension dissolves via the determinant anomaly.** "How does `index S∈K¹` (degree 1)
become `ω∈H²(G_L)` (degree 2)?" — the bridge is NOT an abstract transgression but the **multiplicative
anomaly of the ζ-determinant**, which is *literally* a 2-cocycle:
- On the Toeplitz algebra of the shift `S`, the determinant defect
  `det(T_f T_g) / det(T_{fg})` is governed by the **Helton–Howe / Carey–Pincus** cocycle
  `c(f,g) = (1/2πi)∮ (log f) d(log g)` (the **tame symbol** `{f,g}`), a genuine group **2-cocycle** on
  the symbol group, with cohomology class `= index S = −1`.
- This is exactly the **Pressley–Segal determinant-line central extension** `1→𝔾_m→\widetilde{LG}→LG→1`,
  whose class lives in `H²(·,𝔾_m)` — the **same `H²(·,𝔾_m)`** that hosts the Tannakian realization
  obstruction `ω`.

**Unification with #27.** `compute-omega-h2-gl.md §S` already identifies `ω` with the
**Kontsevich–Vishik multiplicative anomaly** of the archimedean ζ-regularized determinant. That anomaly
**is** the Carey–Pincus/tame-symbol 2-cocycle of the one-sided shift `S`. So the two threads coincide:
> **ω = [det-line central extension / tame-symbol 2-cocycle of the archimedean Toeplitz shift] ∈ H²(·,𝔾_m),
> with class = index S = −1.**
The degree-2 nature is built in (the anomaly is a 2-cocycle); the index `−1` (a K¹ number) is its
*value*. The "K¹→H²" step is `det`: a K¹ class ↦ its determinant-anomaly 2-cocycle (Pressley–Segal/Tate).

**Consistency checks (internal).**
- `index S=−1` is the degree-2/`H²` object; the Γ-phase winding `N(T)` is the degree-1/`π₁` object —
  matching the dead sub-route's P2 (monodromy degree 1 ≠ ω degree 2). The one-sided shift cleanly
  separates the two degrees: ground-state cokernel (`index`, `H²`) vs phase winding (`N(T)`, `H¹`).
- SEED-R (#27): `ω` is **purely archimedean** (multiplicative-Koszul part acyclic). Matches: the tame
  symbol/anomaly here lives entirely on the archimedean `σ_∞` shift, zero at finite primes (Wodzicki
  locality, §S).
- `a_∞=½log2π` (#27 §S) is the **local curvature density** of this det-line bundle; its index/Chern
  number is the integral class `= −1`.

**Remaining gap (now precise, not "bookkeeping").** Identify the archimedean symbol group (the
`σ_∞=U(1)` loop direction) as a subquotient of `G_L`, and show the realization-`ω` *restricted there*
equals this anomaly cocycle. That identification — `σ_∞ ⊂ G_L` and `ω|_{σ_∞} =` tame symbol — is the
one open step; the degree arithmetic and the `index=−1` value are settled.

**Refs.** Pressley–Segal *Loop Groups* (det-line central extension); Carey–Pincus / Helton–Howe
(principal-function trace cocycle); Tate (tame symbol / `H²(·,𝔾_m)` residue); `compute-omega-h2-gl.md §S`;
`moonshot-rh-spectral-flow-index.md` (Chern/monopole). Grade unchanged: Source-A ⟹ BRIDGE/substrate.

## Progress past the wall (2026-06-19, DeWitt, iter 4) — Step 2 gap narrowed: σ_∞ = ∏_p σ_p² located in G_L

The Step-2 residual was "identify the archimedean `σ_∞=U(1) ⊂ G_L`." Resolved concretely.

**σ_∞ is the diagonal squared-prime shift.** The Γ-pole ladder of `Γ(s/2)` has period 2 in `s`
(poles `−2ℕ₀`), so its generator is `s↦s+2`. On the completed `(σ_p,∂_s)`-module, `∂_s=d/ds` acts on the
Bohr coordinates by `∂_s x_p = −(log p)x_p` (direct: `d/ds·p^{−s}=−(log p)p^{−s}`). Hence the discrete
ladder shift is the exponential of the archimedean generator and equals a diagonal of the prime shifts:
> `σ_∞ := exp(2∂_s) : x_p ↦ p^{−(s+2)} = p^{−2}x_p = σ_p²(x_p),  i.e.  σ_∞ = ∏_p σ_p².`
So `σ_∞` is **not** an extra generator — it is the **diagonal `∏σ_p²`** inside the prime-shift group,
manifestly an element of `G_L`, and the Γ-pole ladder is its orbit. Its Pontryagin-dual circle
`S¹ = \widehat{ℤ⟨σ_∞⟩}` is the **Toeplitz symbol circle** carrying the index/anomaly.

**Two distinct archimedean circles (interrogation — reverse/rotate, kept apart).**
- `S¹` = dual of the ladder lattice `ℤ⟨σ_∞⟩` (the *discrete real* shift `s↦s+2`) — the intrinsic
  archimedean rotation, the Toeplitz symbol circle, home of `ω`/index. **(this lane)**
- `𝕋^∞` = closure of the *continuous imaginary* flow `s↦s+iτ` (Kronecker, dense by `{log p}` ℚ-indep) —
  the diagonal-flow border (N4). **(not this lane)**
These must not be conflated: the index `ω` lives on the discrete ladder `S¹`, not the prime-phase `𝕋^∞`.

**Weld face (Door-4 note, not overclaimed).** `σ_∞=∏σ_p²` couples the archimedean ladder to the
diagonal prime shift — a concrete face of the archimedean×prime weld. Still Source-A-dominant (the ladder
and its index are archimedean), so grade stays **BRIDGE/substrate**; this is not asserted as crossing to
C5, only as locating `σ_∞` in the prime-shift group.

**Residual (the one remaining Step-2 piece).** Show the Tannakian realization obstruction `ω` *restricted
to this archimedean `S¹`* equals the tame-symbol/determinant-anomaly 2-cocycle (class `index S=−1`). This
is a Tannakian-gerbe ↔ operator-anomaly compatibility; plausible under #27 SEED-R (`ω` purely
archimedean), needs the Tannakian→operator dictionary. That is now the sole open node of Step 2.

## Progress past the wall (2026-06-19, DeWitt, iter 5) — the three steps funnel to ONE node (Fock realization σ_∞↦S); Step 1 closed as credited BRIDGE

Applying the 24-move toolbox (`docs/meta/scientific-method.md`): #19 fake-proof → #20 missing-lemma →
#23 dependency-chain.

**The funnel.** The fake proof of the Step-2 residual ("ω|_{S¹} = tame symbol") has exactly one gap, a
single lemma:
> **L.** The archimedean realization functor sends `σ_∞=∏σ_p²` to the unilateral shift `S` on the Fock
> ladder `ℓ²(ℕ)` of `det_ζ(N+s/2)`, an isometry of `index −1`.
But **L is Step 1** (operator L-factor packaging with `σ_∞=S`). So Steps 1, 2-residual, and 3 are **not
three independent gaps — they funnel through one node:** the Fock realization `σ_∞↦S`. Closing it closes
the operator content of all three.

**Step 1 closed (as a credited BRIDGE/IMPORT).** The node holds:
- The verified grounding `Γ(a)·det_ζ(N+a)=√2π` *is* the operator L-factor in ζ-det form: the archimedean
  factor `Γ_ℝ(s)=π^{−s/2}·√2π/det_ζ(N+s/2)` is the (inverse, normalized) ζ-regularized determinant of
  the number operator `N` over its one-sided ladder `{s/2+n:n≥0}`.
- `σ_∞=exp(2∂_s)` (iter-4) is the ladder shift; `S=a†` its creation operator. So `σ_∞↦S` on the Fock
  module is the realization. L holds.
- *Unverified — recalled, not checked this session:* this is the archimedean case of the
  **regularized-determinant local-L-factor** framework (Deninger 1992 "Local L-factors as regularized
  determinants"; Connes–Consani archimedean cohomology) — `L_∞(s)=det_∞((s−Θ)/2π)^{±1}` over a one-sided
  spectral ladder of the flow generator `Θ=∂_s`. The numerically-VERIFIED content is the grounding
  identity; the attribution is recalled and flagged, not asserted. Grade: importing a parent realization
  ⟹ **BRIDGE/IMPORT** (credited), consistent with the whole lane being Source-A.

**What this leaves as the single genuinely-open node.** With L (= Step 1) closed, the operator side of
Steps 2–3 is settled (index `−1`, det-line/tame-symbol 2-cocycle, FE-balance at `s=½`). The **sole**
remaining open node is the **Tannakian↔operator compatibility**: that the categorical realization
obstruction `ω∈H²(G_L,𝔾_m)` *equals*, on `⟨σ_∞⟩`, the operator det-line class of `S`. This is one
clean statement (gerbe class = determinant-line class of the realization), not a diffuse "bookkeeping."
It is the precise thing to prove next; everything below it is now closed or credited.

**Native vs imported (Door-2 ledger for this lane).** Imported/BRIDGE: the regularized-det L-factor
realization (Deninger/Connes–Consani), the ζ-det grounding, Wold/index, tame-symbol/Pressley–Segal. The
**reading that is this lane's own**: that the *one-sidedness* of the archimedean ladder is an **index
obstruction** and that `ω` = its det-line/tame-symbol class with the FE balancing two one-sided ladders
into the unitary at `s=½`. That reading is the contribution; it remains Source-A ⟹ BRIDGE/substrate for
the F₁/seam/ω program (D-axis keystone-dual), not a C5 weld.

## Progress past the wall (2026-06-19, DeWitt, iter 6) — Step 2 degree paradox RESOLVED: ω = tame symbol = (ladder shift) ∪ (Riemann–Siegel phase); the cup the dead route never multiplied

**The internal inconsistency (attack-as-false, moves #2 + #23).** Iter-4 phrased the open node as
"`ω` restricted to the archimedean `⟨σ_∞⟩=S¹`." But `⟨σ_∞⟩≅ℤ`, and `ℤ` has cohomological dimension 1
(free group; resolution `0→ℤ[ℤ]→ℤ[ℤ]→ℤ→0`), so for **any** coefficient action
> **`H²(⟨σ_∞⟩, 𝔾_m) = H²(ℤ, 𝔾_m) = 0`.**
A restriction of `ω` to the cyclic group of a single shift is necessarily **zero** — it cannot equal
`index S=−1`. The naive node is degree-incoherent and is **refuted as stated**: one generator (a `ℤ`)
cannot host a degree-2 class. (This is a clean no-go, not a gap.)

**The correct host: the archimedean local loop group, valuation ∪ leading-coefficient.** The class is
degree-2 because it lives on the **local field of the Γ-pole** `𝔾_m((t)) = ℂ((t))*` (the formal loop
group), not on `ℤ`. There `H²` is generated by the **tame symbol** (Tate / Milnor `K₂`):
> `{f,g} = (1/2πi)∮ (log f)\,d(log g)`,  with `ℂ((t))* ≅ ℂ* × t^ℤ × (1+tℂ[[t]])` and
> `{t^m u, t^n v} = (−1)^{mn}(u^n/v^m)(0)` — **valuation `t^ℤ` ∪ leading-coefficient `ℂ*`.**
This is exactly the Pressley–Segal det-line cocycle and the 2D-anomaly shape `α∪β`, `α,β∈H¹`.

**The two H¹ factors are the lane's own two one-sided objects.**
- **valuation / `t^ℤ`** = the **ladder shift `σ_∞`** (`s↦s+2`, the discrete *real* shift; the `K¹`/index
  direction).
- **leading-coefficient / `ℂ*` phase** = the **Riemann–Siegel phase** `arg R(s)`, `R=Γ_ℝ(s)/Γ_ℝ(1−s)`.
  On the line `R(½+it)=Γ_ℝ(½+it)/\overline{Γ_ℝ(½+it)}` (since `Γ_ℝ(s̄)=\overline{Γ_ℝ(s)}`), so
  `arg R = 2·Im logΓ_ℝ(½+it) = 2θ(t)` **exactly** (Riemann–Siegel `θ`) — the *imaginary* Γ-phase whose
  winding is `N(T)`. **Verified** (`/tmp/argR_check.py`, dps=40, t∈{1,10,50,123.4}): `|R|−1=0` and
  `arg R − 2θ ≡ 0 (mod 2π)` to `<10^{-40}`. (Analytic, so no archive needed; it is the conjugate
  relation, not a fit.)

> **ω = {valuation, leading-coeff} = [σ_∞ ladder shift] ∪ [Γ-phase θ / N(T)] ∈ H²(·,𝔾_m), value = index S = −1.**

**Reconciliation with the dead `2πiℤ` sub-route (the aha).** The dead route had found *both* degree-1
windings and stopped at "degree 1 ≠ degree 2":
- P2: the (log-/ladder-) monodromy is degree-1 (`π₁/H¹`) — **factor 1** (the ladder/valuation);
- P4: `N(T)` is the degree-1 Γ-phase winding — **factor 2** (the `θ` phase).
It declared "neither is `ω` (degree 2)" and quit. Resolution: **`ω` is their CUP PRODUCT.** The dead route
held both halves of the product and never multiplied them. Two degree-1 windings (real ladder ∧ imaginary
Γ-phase) cup to the degree-2 anomaly — the tame symbol. P2/P4 are not obstructions to the identification;
they are precisely its two factors. (Independent shape-check, move #8: this is the Pressley–Segal
cocycle = winding∪winding and the 2D abelian anomaly `∫A∧dA` — the correct parent shape.)

**What this settles vs. leaves open.**
- *Settled:* the degree arithmetic (`H¹∪H¹→H²`), the host (`𝔾_m((t))`, tame symbol), the value
  (`index S=−1`), and the identification of both factors with lane objects (`σ_∞`; `2θ(t)`). The
  `H²(ℤ)=0` no-go kills the cyclic phrasing permanently.
- *Open (sole Step-2 node, now sharpened):* the **Tannakian embedding** `𝔾_m((t)) ↪` (archimedean part
  of) `G_L` under which the realization gerbe `ω∈H²(G_L,𝔾_m)` pulls back to this tame symbol. The two
  factors are now named; the embedding-and-pullback is the remaining theorem.

**Grade.** Tame symbol / Pressley–Segal / 2D-anomaly are parent machinery (IMPORT); the
cup-of-two-windings *reading* of `ω` and the P2/P4 reconciliation are the lane's contribution. Source-A
archimedean ⟹ **BRIDGE/substrate** (the D-axis `ω`/F₁ keystone-dual), unchanged.

**Gate.** 1→2 stays open: Step 2's degree paradox is resolved and its structure pinned (cup of two named
windings = tame symbol = index −1), but the Tannakian-embedding identification remains the open theorem.
Continuing on that node. NOT terminalizing.
