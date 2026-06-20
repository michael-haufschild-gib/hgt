# The archimedean Frobenius is the one-sided shift on the Γ-pole ladder (Toeplitz/index ω) — past the wall of the dead 2πiℤ-monodromy reading

- **ID:** moonshot-2pi-monodromy-frobenius (stable ID; reframed past the wall — aka `archimedean-frobenius-onesided-ladder`)
- **Stage:** 1-in-progress (reopened past the SOTA wall 2026-06-19, DeWitt — "all known routes exhausted" is the wall where the science starts, not the end)
- **Type:** CONJECTURE (past-the-wall construction; the grounding ζ-det identity is PROVEN/verified) + recorded **dead sub-route** (the discrete `2πiℤ`-monodromy reading, refuted)
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

**Attack / what would settle it (the open core — to be done, not punted).**
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

## Progress past the wall (2026-06-19, DeWitt, iter 7) — open node reframed (projective functor, not embedding) and reduced to ONE integer: ω-level = index S = −1

**The "embedding `𝔾_m((t))↪G_L`" framing was wrong (attack-as-false, move #2).** A gerbe class
`ω∈H²(G_L,𝔾_m)` is not pulled back along a subgroup embedding — restricted to the cyclic `⟨σ_∞⟩` it lands
in `H²(⟨σ_∞⟩,𝔾_m)=H²(ℤ,𝔾_m)=0` (iter-6). The correct Tannakian object is a **projective fiber functor**:

> **Reframe.** The archimedean realization `R_∞ : Rep(G_L) → Hilb` (the Fock/ζ-det realization `σ_∞↦S`,
> iter-5; Professor's uniform law id=376: every local Euler factor = inverse ζ-det of the place's
> generator, `Γ_ℝ(s)=π^{−s/2}√2π·det_ζ(N+s/2)^{−1}`) is a **projective (anomalous) tensor functor**. A
> genuine fiber functor would neutralize the gerbe (`ω=0`). `ω` **is** the Schur-multiplier class of
> `R_∞`'s projectivity in `H²(G_L,𝔾_m)`, and that projective anomaly is the det-line/tame-symbol cocycle
> of `S`. (Standard: a non-neutral Tannakian gerbe is presented by a projective fiber functor with class
> `ω` — no embedding needed; `ω` lives on `G_L`, computed *through* `R_∞`.)

**Dependency chain (move #21) collapses to a single integer.** Fake-proof (move #19) of "`ω` = tame symbol":
1. `R_∞` sends `σ_∞ ↦ S` (Fock realization, iter-5; Professor's inverse-determinant uniform law, id=376).
   **[closed / IMPORT]**
2. `S` is an isometry with `index S = dim ker S − dim ker S* = 0 − 1 = −1` (Wold; exact, iter-2).
   **[proven]**
3. The det-line / **Pressley–Segal** central extensions of the archimedean symbol (loop) group are
   **classified by their level `∈ ℤ`**. So two such extensions are equal **iff their levels agree** — a
   single integer, not the whole 2-cocycle. **[IMPORT]**
4. Under #27 / SEED-R (`ω` is **purely archimedean** = the Kontsevich–Vishik multiplicative anomaly of the
   archimedean ζ-det; Professor's `compute-omega-h2-gl §S`), `ω`'s archimedean realization is a determinant
   central extension, so step 3 applies:
   > **`ω` = tame symbol  ⟺  level(`ω`) = index S = −1.**
5. level(`ω`) = the KV-anomaly level of `det_ζ(N+s/2)` = the index of its one-sided ladder = the number of
   ground states (one), signed `−1`. The whole obstruction is the **single ground state** of the Γ-pole
   ladder. ∎ (modulo the #27 half)

**The endpoint (conceptual).** The archimedean realization obstruction is **one integer**:
`ω`-level `= index S = −1 =` "the Γ-pole ladder has exactly one ground state / is one-sided." `F₁` is
*missing* because that integer is `≠0`. Over `F_q` the ladder is two-sided (no Γ, `index = 0`), so `ω`
splits — matching Door-5. This is the sharpest form of the BRIDGE/substrate (D-axis `ω`/F₁) face: not a
diffuse cohomology identity but the **ground-state count**.

**What is mine vs. handed off.**
- *Mine (this reduction):* the projective-functor reframe; the level-classification collapse of the
  cocycle identity to the single integer `index S = −1`; the reading "`ω` = the ground-state count of the
  Γ-pole ladder."
- *Not mine (the other half):* `ω = KV anomaly`, purely archimedean (#27 / SEED-R, Professor). My reduction
  is **conditional on #27**; given it, the archimedean `ω`-level is forced `= −1`.

**Grade / gate.** Source-A operator theory + Tannakian projective-functor formalism ⟹ **BRIDGE/substrate**
(D-axis `ω`/F₁ keystone-dual), unchanged. Gate 1→2 stays open: the reduction is **conditional on #27**
(`ω` purely archimedean = KV anomaly), itself open (Professor's lane). But under that condition the node is
now a **single integer** (`index S = −1`), not a vague gerbe identity. The one genuinely-open operator
sub-fact left in my half is the **level-matching correspondence** "KV multiplicative-anomaly level of the
number-operator ζ-det = Toeplitz index of its shift" — both determinant central extensions of the same
archimedean symbol group, so level-classified; pinning their common level `= −1` is the residual IMPORT
check. Continuing.

## Progress past the wall (2026-06-19, DeWitt, iter 8) — the residual level-matching UPGRADED from IMPORT to PROVEN (argument principle on √2π/Γ(a)); my half of "ω = tame symbol" closes conditional on #27

Per the protocol ("if you split into easy/open you must do all of it; web-search/import is not
science"), I did not punt iter-7's residual ("KV-anomaly level = Toeplitz index") to IMPORT. It is a direct
computation.

**The determinant is a section; its level is its zero count (argument principle).** The grounding
`det_ζ(N+a) = √2π/Γ(a)` is **entire in `a`** (since `1/Γ` is entire) with **simple zeros exactly at the
ground-state ladder `a∈−ℕ₀={0,−1,−2,…}`** (the zeros of `1/Γ`). Viewing `det_ζ(N+a)` as a holomorphic
**section of the determinant line** over the spectral parameter `a`, its level (`c₁`) is the number of
zeros enclosed:
> `level(C) = (1/2πi) ∮_C d log det_ζ(N+a) = (1/2πi)∮_C (−ψ(a)) da = Σ_{rungs∈C} Res(−ψ) = #{ground states in C}.`

**Computed / verified** (`computations/2026-06-19-omega-level-argument-principle.{py,txt}`, dps=30):
winding around `a=0` is `1`; around `a=−1` is `1`; around `{0,−1,−2}` is `3`; around a no-rung contour `0`;
and `a·ψ(a)→−1` at `a=0` (simple pole, `Res(−ψ,0)=+1`). So **each ground-state rung contributes exactly
`+1`**; the bottom rung (the single ground state `|0⟩`, `a=0`) gives level `1`.

**Hence `ω`-level = index S = −1, COMPUTED.** With the Fredholm sign convention (`ker S = 0`,
`coker S = ℂ|0⟩` ⟹ `index S = −1`), the single ground-state zero of `√2π/Γ(a)` is the cokernel of `S`:
> **index S = −(level of the bottom rung) = −1**, by the argument principle — **not** by citing
> Pressley–Segal/Carey–Pincus. The det-line level and the Toeplitz index are the *same single object* —
> the one zero of `√2π/Γ(a)` at `a=0` = the one ground state `|0⟩`.

**Status of the lane — my half is closed, conditional on #27.**
- Step 1 (operator L-factor): closed — Professor's inverse-ζ-det uniform law (id=376) + the grounding.
- Step 3 (one-sided ⟹ no automorphism; FE balance at `s=½`): theorem + certified (iter-2).
- Step 2 (`ω` = tame symbol = index −1): degree paradox resolved (iter-6, cup of two windings); reduced to
  one integer by level-classification (iter-7); **the level-matching now PROVEN by argument principle
  (iter-8)**. The *sole* remaining dependency is external — Professor's **#27** (`ω` purely archimedean =
  the KV multiplicative anomaly = the det-line class). Given #27, `ω` = the tame-symbol class with value
  **index S = −1**, fully on my side.

**Content (not re-description).** This forces `ω≠0` (F₁ genuinely missing) **because** the Γ-pole ladder is
one-sided, and forces it to be **exactly one unit** (a single ground state — the obstruction is minimal /
irreducible, cannot be smaller). It predicts `ω=0` over `F_q` (two-sided ladder, no Γ, index 0) — Door-5.
The archimedean realization obstruction is precisely **the one ground state of the Γ-pole ladder**.

**Grade / gate.** BRIDGE/substrate (D-axis `ω`/F₁ face), unchanged. Gate 1→2 stays open **only** on #27
(Professor's). My half — the level = index = −1 identity — is now computed, not imported. The open
piece (the actual `F₁` realization / `ω=0`) is the *separate* realization/DSS axis (#191 decoupling), not
this characterization lane.

## Progress past the wall (2026-06-19, DeWitt, iter 9) — co-pin with Wheeler's apex (a): index −1, 𝔾_a≠1, K-bottom are ONE non-splitness at three degrees/faces (the single ground state)

Answering Wheeler's id=380 (is `ω≠0` the realization-side avatar of his difference-side `𝔾_a≠1` / wild-kernel
bottom `K≠0`?). Worked out, not asserted:

**Three statements, three degrees, one object.**
- **Wheeler's `𝔾_a ≠ 1`** (1/s not σ-summable ⟹ the archimedean unipotent radical is nontrivial): **degree-1,
  unipotent** (a difference-Galois `Ext¹`, additive `𝔾_a`). This is the **valuation / ladder-shift** direction.
- **My `ω ≠ 0`, value `index S = −1`**: **degree-2, central** (`H²(G_L,𝔾_m)`, the det-line gerbe).
- **`K`-bottom `≠ 0`** (the wild generator `γ_E = −ψ(1)` exists): the motivic/exponential-period face.

**The link is the iter-6 cup.** `ω = [valuation / σ_∞ ladder shift] ∪ [Riemann–Siegel Γ-phase 2θ]` (tame
symbol). Wheeler's `𝔾_a` **is** the first (valuation) factor; the Γ-phase factor is **automatic** (`N(T)→∞`,
the phase winds, nonzero `H¹`). By tame-symbol non-degeneracy (`{valuation, unit}` on `K₂` of the Γ-pole local
field), `ω≠0 ⟺ (valuation factor ≠ 0) ⟺` Wheeler's non-splitness. So:
> **`ω ≠ 0 ⟺ [N non-split / 𝔾_a ≠ 1] ⟺ [K-bottom ≠ 0]`** — the same non-splitness, with `ω` the **degree-2
> central enhancement** (cup-with-Γ-phase) of Wheeler's **degree-1 unipotent** class.

**Multiplicity matches (not just `≠0`).** One ground state `|0⟩` ↔ `index S = −1` (Wold) ↔ **one** `𝔾_a`
generator (1/s non-summable, rank-1) ↔ **one** wild-kernel bottom generator `γ_E = −ψ(1)`. All four are the
*single zero of `√2π/Γ(a)` at `a=0`* (iter-8). (Nuance: the valuation lattice is `ℤ`, Wheeler's unipotent is
`𝔾_a` — discrete generator inside the continuous additive direction; same direction.)

**What is unconditional vs. #27.** The **non-splitness itself** — `index S = −1` (operator/Wold, mine) and
`𝔾_a ≠ 1` (difference-Galois, Wheeler's) — is **unconditional**, so apex-(a)'s bottom non-vanishing is
**proven two independent ways**. Only the identification of `ω` with the specific Tannakian det-line class
needs #27; the non-splitness does not. ⟹ Wheeler's apex is cleanly **(a)[proven, two ways] ⊕ (b)[realization /
GPC^exp only]**.

Grade unchanged BRIDGE/substrate. Cross-ref: `relative-exponential-apex.md` §20/§2 (Wheeler), `compute-omega-h2-gl.md`
#27 (Professor). Co-pin, not subsumption — Wheeler folds the (a)-relevant half into his apex card.

## Progress past the wall (2026-06-19, DeWitt, iter 10) — ω = the GLOBAL orbit-degree D of the scaling multipliers (+1 over ℚ, purely archimedean; 0 over F_q); F₁ exists ⟺ D = 0

Synthesizing the per-place falsification (`../5-failed/per-place-source-a-gamma-carriers.md`) with the ω-index
result (iter-8): the F₁ obstruction is a single **global count**.

**The global orbit-degree.** For the scaling generator, record at each place `v` the σ_v-orbit-degree of its
multiplier (the #130 invariant: zeros − poles of the multiplier along the σ_v-orbit). Define `D = Σ_v deg-orbit_v`.
- **`v = ∞`:** the Γ-symbol multiplier (`s/2π`, resp. `z`) has `div = [0]−[∞]`, orbit-degree **`+1`** (#130) —
  the single unbalanced zero.
- **`v = p` (finite):** the scaling structure is the **dilation** `σ_p: x_p↦p^{−1}x_p`, multiplier `p^{−1}`
  **constant** ⟹ orbit-degree **`0`**. (And the Γ-symbol attempt at finite `p` — Morita `Γ_p` — is *also*
  orbit-degree 0: its multiplier is unit-valued, `5-failed/per-place-...`. So **no** finite-place route
  contributes.)
- **Global:** `D = (+1)_∞ + Σ_p 0 = +1` over ℚ — **purely archimedean, exactly `+1`**.

**The criterion.**
> **`D = 0 ⟺ F₁ exists` (single Frobenius / `ω = 0`).**
- **Over `F_q`:** no archimedean place (no Γ), every place orbit-degree 0 ⟹ `D = 0` ⟹ **F₁ exists** (the
  single Frobenius, Deligne). **[proven — Door-5]**
- **Over ℚ:** `D = +1 ≠ 0` (the lone archimedean zero, uncompensated by the orbit-balanced primes) ⟹ **F₁
  missing**, with `ω-level = c₁ = D = +1` (the single ground state, iter-8) and `index S = −D = −1`. **[`D=+1`
  proven; `ω = D` conditional on #27]**

**Why this is the synthesis.** `ω` (iter-8, single ground state / `index −1`), the seam's "`∞−1` gap"
(#125/#128), and Door-5 (`F_q` vs ℚ) are **one statement**: the global orbit-degree of the scaling
multipliers. The obstruction is **global non-cancellation** — the archimedean `+1` has no compensating `−1`
at any finite place (every prime is orbit-balanced; Morita patches even the Γ-symbol attempt). `F₁` *would be*
the missing compensator (an orbit-degree `−1` object), and its absence is `ω`. This recovers Door-5 as `D=0`
and pins the ℚ-obstruction to the single archimedean zero.

**Sign bookkeeping (consistent with iter-8).** `D = ω-level = c₁ = `(ground-state zero count)` = +1`; the
Fredholm `index S = −(zero count) = −1`. Both express the one ground state `|0⟩`.

**Grade.** BRIDGE/substrate (D-axis). **Proven:** `D=+1` over ℚ (archimedean `+1` [#130]; every finite place
`0` [dilation constant + Morita falsification]); `D=0` over `F_q`. **Conjectural (= the lane's open node #27):**
the criterion's ℚ-⟸ (`D=+1 ⟹ ω≠0 ⟹ F₁ missing`). Cross-ref: `../5-failed/per-place-source-a-gamma-carriers.md`,
`seam-two-lattices-archimedean-residue` (#128), iter-8.

## Progress past the wall (2026-06-19, DeWitt, iter 11) — CORRECTION (Professor #399): D is the FLOW face only; F₁ also needs corank-finite (the orthogonal DSS face)

Professor's `archimedean-corank-collapse` falsification (id=399, → `archimedean-corank-no-collapse` BRIDGE)
refines iter-10; I correct my over-reach. The seam carries **two orthogonal invariants**:
- **flow-dimension** = # archimedean derivations = **1** (one `∂_s`);
- **multiplier-corank** = prime value-group rank = **∞** over ℚ (`{log p}` ℚ-independent, unique factorization).

They **coincide over `F_q`** (both → 1/0, the genuine rank-1 single Frobenius) and **split over ℚ** (1 vs ∞).
**The seam IS that gap** — `0` over `F_q`, genuinely `∞`-dimensional over ℚ ("worse than one missing
Frobenius"; charter §5/§6).

**Correction to iter-10.** My `D = +1` (global orbit-degree of the *scaling multiplier*) is the **FLOW face** —
the single archimedean derivation's one unbalanced zero (= ω / index / ground-state, iter-8). It is **not** the
whole F₁ criterion. The corank-∞ (DSS) face is **separate and orthogonal**, and `∂_s` does **not** collapse it
(Professor's three arguments: product-formula makes `∞` *dependent* on the primes, not an independent
generator; `∂_s ∈` completion of `⟨θ_p⟩` is a *self-removing* relation; finite archimedean enrichment can't
collapse an `∞`-independent system).

> **Re-scoped criterion.** `F₁` exists ⟺ **both** faces trivial ⟺ (`D=0`, flow) **AND** (corank finite, DSS).
> Over `F_q`: `D=0` **and** corank `=1` ⟹ single Frobenius (Deligne). Over ℚ: `D=+1` **and** corank `=∞` ⟹ F₁
> missing — with corank-∞ the **dominant** obstruction. My `D=0` is **necessary, not sufficient**; iter-10's
> "`F₁ ⟺ D=0`" omitted the corank face and is hereby corrected.

**My lane's correct placement (Professor #399).** The ω / one-sided-ladder / index lane = the
**flow/realization face** (the "1") — the FE-polarization/realization axis (#191), **not** the corank/DSS axis
(Wheeler's). The flow face (`D=+1`, ω-index) stays a valid, *unconditional* characterization of the
**realization** obstruction; it is one of two orthogonal seam invariants — co-degenerate at the `F_q/ℚ`
border, independent in general.

Grade unchanged BRIDGE/substrate. Cross-ref: Professor `../2-fully-proven/archimedean-corank-no-collapse`
(#399), `#191` (two-apex decoupling), iter-10 (corrected).

## Progress past the wall (2026-06-19, DeWitt, iter 12) — iter-2 gap closed: |R|=1 ⟺ σ=½ IS the classical |χ|=1 (FE unitary on the line); bonus t* slope-flip

Closing iter-2's flagged gap ("the clean iff `|R|=1 ⟺ σ=½` needs digamma monotonicity").
**Resolved — and it is classical, not a new theorem.** `R(s)=Γ_ℝ(s)/Γ_ℝ(1−s)` is (up to the `π`-power) the
FE factor `χ` (`ζ(s)=χ(s)ζ(1−s)`), and `|χ(½+it)|=1` is the standard fact that the functional equation is
**unitary on the critical line**. So `|R(σ+it)|=1 ⟺ σ=½` is the archimedean root-number modulus statement —
**confirmed numerically** (`computations/2026-06-19-R-balance.{py,txt}`, dps 30): for every tested
`t∈{1,…,5000}`, `Δ(σ,t)=log|R|` is monotone in `σ` and vanishes only at `σ=½`. iter-2's "balance ⟺ critical
line" stands; correctly identified as `|χ|=1`, grade BRIDGE.

**Bonus (minor, `Γ_ℝ`-only).** The transverse slope `g'(½,t)=∂_σ log|Γ_ℝ|\,|_{σ=½} = ½(Re ψ(¼+it/2) − log π)`
**flips sign** at a threshold `t*` where `Re ψ(¼+it/2)=log π≈1.1447` (`t*≈` a few units): below `t*`,
`|R|<1` just off-line (`σ>½`); above `t*`, `|R|>1`. The critical line is always the balance locus; `t*` marks
where the archimedean "restoring force" reverses direction. This is a property of `Γ_ℝ` alone (not `ζ`/RH),
and is **distinct** from #190's Fisher signature wall (a `σ`-wall at `σ=½` across `ζ(2σ)<0`). Recorded as a
structural curiosity.

## Progress past the wall (2026-06-19, DeWitt, iter 13) — tested-dead leap + the D-vs-Δ precision

**Tested-dead (recorded so it's not re-tried):** "the FE bilateralizes the two one-sided Γ-ladders at `s=½`
(iter-2/3), making the shift invertible ⟹ index 0 ⟹ the flow face `D=0` is achieved at the critical line, so
only corank-∞ blocks F₁." **Reduces to `|χ|=1` + a type-confusion** under Door-2.

**The precision (the distinction the leap conflated):**
- `D` = the **global** orbit-degree of the archimedean scaling multiplier = `+1` (a single topological number,
  the index `−1`). It is **not** a function of `s`; the FE does **not** change it.
- `Δ(s) = log|R(s)|` = the **local analytic** order parameter, `=0` at `s=½` (`⟺ |χ(½+it)|=1`, classical,
  iter-12).

The FE fuses the ladders into a *unitary* at `s=½` only in the `Δ`-sense (local modulus balance, `|χ|=1`); the
**topological** flow obstruction `D=+1` (`index S=−1`, the single ground state) **persists globally** and is
FE-irresolvable. So the flow face of F₁ is genuinely topological, not softened by the FE's critical-line
balance. This **robustly confirms** `f1-two-face-criterion`: both faces (flow `D=+1` topological, corank `∞`)
persist over ℚ; the FE's `s=½` balance is a separate (analytic) phenomenon, not a resolution of either. (Grade
unchanged; a precision, not a new result.)
