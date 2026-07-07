# 123 — Constraint-not-flow reframes: the un-killed targets and a theatre test

**Register: SEARCH.** Everything below is `[TARGET]` / `[REFRAME]` / `[CONJECTURE]` / `[OPEN]`
unless marked `[KNOWN]` or `[PROVED HERE]` with an anchor. Nothing is promoted here.
Companions: `104-checkpoint-deadends-and-open-routes.md` (dead ends), `105-constraint-front-plan.md`
(the constraint front), `121-gate4-no-go-and-forcing-criterion.md` (the forcing criterion),
`00-approach.md` (the lane thesis). Parent anchors: `docs/where_we_stand/proof_shape.md`,
`object_x.md`; door buckets `bucket-time-and-non-holonomic-time`, `bucket-the-no-margin`,
`bucket-the-seam-archimedean-obstruction`.

---

## 0. Why this document

Two lanes of this repo hit no-gos this arc, both for the same reason. The pinning/carrier lane
froze (`104` Add. 6) as *a flow in disguise*: a height clock `T`, a generative handle hunting a
surrogate coefficient `b`, a `∀zero ∃(T,U,…)` quantifier. The conservation × parity lane then hit
Gate 4 (`121`): its deck/winding machinery **computes** `Even(order)` but never **forces** it — the
fork is that every banked invariant is either order-linked-but-steerable or structurally-pinned-but-
order-decoupled, and none lives on both prongs.

A cross-corpus sweep (this repo + the parent `docs/rh`, `docs/where_we_stand`) converges on one
diagnosis, derived independently a dozen ways:

- **Symmetry is free; definiteness is the wall.** The functional equation makes the natural operator
  self-adjoint w.r.t. the *indefinite* Weil/Krein form for free, on or off RH (`proof_shape §1`:
  `D* = 𝔉 D 𝔉⁻¹` **is** the FE). Reality of conjugate pairs is free; RH is `κ₋ = 0`, definiteness of
  a transverse index. `[KNOWN, parent ledger]`
- **The Euler product, not the FE, is the missing ingredient.** Davenport–Heilbronn has ζ's FE and
  reality yet off-line zeros; multiplicativity supplies the codim-2 non-crossing the FE (codim-1)
  cannot (`opus_euler_product_is_the_RH_ingredient`; Hamburger rigidity, `00-approach §4.2`). `[KNOWN]`
- **Every analytic positivity route is self-referential** (SOS/Gram/spectral-measure/entropy
  positivity ⟺ `Q_W ≥ 0` ⟺ RH); the only escape is *external* geometric positivity, which needs an
  object that does not yet exist — the archimedean–prime **weld `ω`** / the complex structure `J`
  integralizing `{log p}` / the F₁ self-product `Spec ℤ ×_{F₁} Spec ℤ` (`proof_shape §6`,
  `rh_reduction_lattice §3b`). And `ω = 0 ⇏ RH`: the branch's native object is **decoupled** from RH.

So RH-*forcing* from any single side is structurally blocked (orthogonality meta-theorem, door `#137`:
prime-side content is RH-positivity-free). This document does two things a forcing lane cannot:

1. **§1** catalogs the three un-killed **constraint-side** targets (what survives the sweep).
2. **§2–4** gives a **theatre test** separating a genuine constraint reframe of a stuck route from a
   wording relabel, and works it on six SOTA routes — Hilbert–Pólya as the flagship (§4).

---

## 1. The three un-killed constraint-side targets

All three are fixed-by-a-constraint objects (D-axis), not propagated-by-a-flow objects. They differ
in *what counts as progress* — a genuine fork, not three names for one thing.

### T1 — The Euler-vs-FE discriminator (the seam separator) `[TARGET — most buildable]`

**Object.** A native invariant of the *constraint class* `{FE ∧ Euler-positivity}` that provably
differs on the FE-only class (Davenport–Heilbronn). The in-house candidate is the higher-cumulant
seam datum `Q_3`: measured `|Q_3|/|Q_1|` grows `0.20→0.25` for ζ and stays flat `~0.07` for DH
(parent, un-killed). **Progress = a theorem** that multiplicativity *forces* this signature (or its
structural cause, the codim-2 Hermitian non-crossing), stopping short of the `⟹ RH` wall.

**Why non-flow and non-RH-equivalent.** It asks what the constraint *admits*, not how anything
propagates; and it stops at the discriminator, so it does not collapse to zero-location. This is the
hgt Goldilocks/family question (`00-approach §7`, `§11 §5.3`) and the parent's un-killed target,
seen from both sides.

**Boundary.** The `Q_3` number is *measured*, not yet theorem-grade, and the parent's own no-margin
number was once retracted as a basis artifact — so step 0 is re-certifying `Q_3` is not a truncation
artifact (pre-register the prediction; anti-theatre gate) before theorem-izing.

### T2 — The weld `ω` / complex structure `J` (the D4 keystone) `[TARGET — deepest, hardest]`

**Object.** The archimedean–prime obstruction `ω ∈ H²(G_L)`, equivalently the complex structure `J`
(`J² = −1`, `Q(J·,J·) = Q`) that integralizes `{log p}` and polarizes the FE form, equivalently the
missing Frobenius dimension of the F₁ self-product (door D4; `proof_shape §6`; parent
`program_intrinsic_polarization_J_worklog`). "Visible in every parent, computable by none."

**Progress = locate/construct the obstruction**, not force RH. This is the branch's actual keystone
and the most "not-in-training-data" object.

**Boundary.** Flagged *RH-strength itself* (`proof_shape` C9). Working it is laying foundations, not
finishing a theorem — the correct posture is to *locate* `ω` more precisely, not to expect it to fall.

### T3 — The transverse index `κ₋` / type-III₁ (the operator-spectral face) `[TARGET]`

**Object.** RH ⟺ `κ₋ = τ(P₋) =` the type-II₁ index of the scaling flow's transverse current `= 0`;
the transverse Kähler form exists (phase space `dx ∧ dξ`), the obstruction is `S → ∞` uniformity
(per-prime `σ_p` is mean-zero, no definite finite-`S` Hodge index). The parent's other un-killed
construction target is the type-III₁ Connes–Marcolli GL2 modular-weight positivity (`object_x`,
transverse-current face). **Progress = an index computation / a uniform-in-`S` definiteness input.**

**Boundary.** Operator-theoretic rather than Galois-theoretic; the `S → ∞` uniformity is the live core.

---

## 2. The theatre test for a "constraint not flow" reframe

Reframing a stuck route from flow-language to constraint-language is the lab's founding move — and
its most seductive way to fool itself. A reframe is **REAL** iff **all four** hold:

- **(R1) Deletes a search.** You stop hunting for an object to construct or propagate. The flow
  version's existential (`∃ operator / ∃ flow / ∃ approximating sequence`) is *removed*, not renamed.
- **(R2) Points at a forced object.** The object the constraint speaks about *already exists* / is
  forced by the given data (FE, Euler product, explicit formula) — nothing is built from scratch.
- **(R3) Changes the tool type.** The property to verify is of a different *kind* — index /
  definiteness / polarization / rigidity — than the flow version's (spectrum / dynamics / limit /
  estimate). Different kind ⟹ different, un-exhausted tools apply.
- **(R4) Opens a concrete move** the flow version cannot even express.

It is **THEATRE** iff it merely rewrites "`∃ X with property P`" as "the constraint `P` holds,"
deleting no search, forcing no object, changing no tool. *Test to catch theatre:* name the tool the
constraint version uses that the flow version cannot. If you can't, it is a relabel.

---

## 3. Six SOTA routes, reframed and graded

Format: **flow form → why stuck → constraint reframe → theatre verdict → the move it opens.**

### 3.1 Hilbert–Pólya — flagship, developed in §4. Verdict: **REAL.**

### 3.2 Berry–Keating `xp` / quantum chaos
- **Flow.** Find the classical chaotic Hamiltonian (`xp`) whose quantization has spectrum `{γ_n}`; the
  *dynamics* generates the zeros.
- **Stuck.** No such operator is known self-adjoint on any identified space (graveyard); GUE
  statistics are transverse-blind (invariant under `ρ ↦ β + iγ`, so blind to off-line drift).
- **Reframe.** The zeros are a fixed configuration; the constraint is that they are the fixed locus of
  the FE involution lifted to phase space, and RH = *that locus is Lagrangian / real* — equivalently
  the prime scattering system is **reflectionless** (critical line = purely a.c. spectrum; an off-line
  zero = a localized bound state, a reflection). Reflectionlessness is a **rigidity of scattering
  data**, not a dynamics.
- **Verdict.** REAL modulo one caveat: (R1)✓ deletes the operator hunt, (R2)✓ scattering data is
  forced, (R3)✓ inverse-spectral/rigidity tools ≠ chaotic-dynamics tools, (R4)✓ the move is below.
  Caveat: the *static* reflectionless form is de Branges/Krein, RH-equivalent and dead; only the
  **dynamical** form is live.
- **Move.** A Calogero–Moser Hermitian Lax pencil `X₀ + t L₀` whose Helton–Vinnikov real-zero
  determinant is the ξ-datum (parent, un-killed). Reflection coefficient `= 0` is the constraint.

### 3.3 Weil positivity
- **Flow.** *Prove* `Q_W ≥ 0` on a widening test basis (add tests, chase positivity).
- **Stuck.** `Q_W ≥ 0` ⟺ RH; every manifestly-positive representation is logically equivalent to the
  conclusion (self-referential). The widening-basis chase is the flow signature (its own no-margin
  number grew ~11 orders as the basis widened to reach the zeros — a basis artifact).
- **Reframe.** `Q_W = A_arch − P_prime` is a **difference**; RH ⟺ **domination** `A_arch ⪰ P_prime`
  in the Loewner order — a comparison of two forced operators, not the positivity of one
  (`domination_not_positivity`).
- **Verdict.** REAL. (R3) is the crux: domination admits operator-monotone functions, majorization,
  interlacing, contraction — tools that a single-form positivity proof cannot invoke.
- **Move.** Find an operator-monotone / interlacing certificate for `A_arch ⪰ P_prime` (not an SOS
  certificate for `A_arch − P_prime ≥ 0` — that route is the self-referential one).

### 3.4 de Bruijn–Newman heat flow
- **Flow.** Evolve the zeros by the dBN heat flow `Λ(t)`; RH ⟺ `Λ ≤ 0`.
- **Stuck.** Rodgers–Tao proved `Λ ≥ 0` (one-sided); the `Λ ≤ 0` half is blocked because a flow cannot
  constrain its own `t = 0` initial condition (the arithmetic data it starts from).
- **Reframe.** Drop the flow; ask what **constraint at `t = 0`** (the arithmetic initial datum) forces
  `Λ = 0` exactly. The flow is structurally blind to its own initial data; a constraint framing asks
  for that initial-data rigidity directly.
- **Verdict.** BORDERLINE. (R1)✓, but (R3) is weak: "what fixes the `t=0` data" re-lands on "the
  Euler product constraint" — it relocates to T1/T2 rather than opening a new tool. Keep only as a
  *pointer* into T1.
- **Move.** None new on its own; folds into T1 (the Euler datum is the `t=0` rigidity).

### 3.5 GUE / random-matrix (Montgomery–Odlyzko)
- **Flow.** The zeros are eigenvalues of a random-matrix *ensemble*; statistical dynamics generate the
  spacings.
- **Stuck.** Transverse-blind; the Gaussian-exact model has *strictly positive* off-line zero density
  (Edelman–Kostlan `~1/(π(2σ−1)²)`) — the zero functional is discontinuous under Gaussian convergence.
- **Reframe.** Not an ensemble average (flow) but the **single deterministic realization** satisfying a
  rigid constraint; the arithmetic content is *exactly the gap* between the Euler-random model (a.s. no
  off-line zeros) and the marginal-exact Gaussian model (positive off-line density). RH = the zero
  functional follows the model *with* the Euler product (`00-approach §4.3`).
- **Verdict.** REAL as a *diagnostic* (it names where the content lives), not yet a route: the gap is
  carried by the multiplicative cumulants — which is precisely **T1** (`Q_3`).
- **Move.** Isolate the cumulant that separates the two models = T1's object. This is why the GUE
  frame and the discriminator are the same content.

### 3.6 Nyman–Beurling
- **Flow.** Approximate `1` by dilations `{ρ(θ/x)}` — an approximation *process*, add terms and close
  the gap.
- **Stuck.** Burnol: the distance decays only `~1/log N`; no monotone structure, no trust radius.
- **Reframe.** RH ⟺ `1` lies in a closed subspace — a **closure/membership constraint**. But this is
  already RH-equivalent with no rigidity handle attached.
- **Verdict.** THEATRE unless a rigidity handle is supplied: it renames the process as a membership
  question but changes no tool (R3 fails). Listed to mark the boundary — *not every constraint phrasing
  is a real reframe.*
- **Move.** None, as stated. A real version would need an external rigidity forcing membership (again
  T2).

**Reading of the table.** REAL reframes (HP, Berry–Keating-dynamical, Weil→domination, GUE→cumulant)
all route into T1/T2/T3 — they are the *entrances* to the un-killed targets, phrased so different
tools apply. THEATRE reframes (Nyman–Beurling as bare membership, dBN as bare initial-data) relabel
without changing tools. The test earns its keep by drawing that line.

---

## 4. Flagship: Hilbert–Pólya as a polarization / index constraint

**Flow form.** `∃` self-adjoint `H` (a Hamiltonian generating `e^{iHt}`) with `spec(H) = {γ_n}`; then
reality of the spectrum ⟹ RH. The search hunts the space of operators.

**Why it is stuck.** No candidate (`xp`, Bender–Brody–Müller) is self-adjoint on an identified space;
worse, *self-adjointness is reality is RH* — the search target's defining property **is** the
conclusion. The route is circular by construction (graveyard: "reality assumed in disguise").

**Constraint reframe, level 1 — index, not operator** (corpus `#138`/`#139`/object_x, sharpened).
The FE *already* forces a self-adjoint operator `D` w.r.t. the **indefinite** Weil/Krein form
(`D* = 𝔉 D 𝔉⁻¹` is the FE, holds off RH). So the operator is **free** — there is nothing to hunt. RH
is not "`H` exists / is self-adjoint" but the **Pontryagin negative index `κ₋ = 0`**: the FE-forced
indefinite form is definite on the relevant subspace. `κ₋` is a *deformation-invariant integer*, so
**index-theory tools apply** (APS boundary index, spectral flow) that reality-of-spectrum cannot use.

- (R1)✓ deletes the operator hunt. (R2)✓ `D` and the Krein form are FE-forced. (R3)✓ index ≠ spectral
  reality. (R4)✓ move below. **Verdict: REAL.**

**Constraint reframe, level 2 — polarization, not operator** (the sharper, less-walked form).
Making the indefinite FE-form definite = choosing a compatible complex structure `J` (a
**polarization**) — a point of the infinite Siegel period domain `D_∞ = Sp_∞(ℝ)/U(∞)` (object_x's
face `J ≡ H_{HP} ≡ D_∞`). So HP's missing ingredient is *not the operator* (forced) but the
**polarization `J`**, and a polarization is a **Hodge structure — a constraint-satisfying point, not a
flow.** HP becomes: *does the arithmetic (FE ∧ Euler) fix a polarization point?* The route opens
period-domain rigidity / Rosati positivity — where the object is fixed by a constraint. This is
exactly **T2** (`J` = the weld). HP and the branch's keystone are the *same object*, and the reframe
makes that operational: attack `J`-existence (a polarization constraint with Hodge tools), not
`H`-existence (an operator construction).

**Why this is not theatre, sharply — the `121 §5` connection.** Doc `121 §5` states the *forcing
criterion*: a forcing is **one invariant with two computations — one order-linked, one structurally
pinned — agreeing non-vacuously.** The index reframe **supplies exactly that shape** for `κ₋`:
- computation (a): `κ₋ = ` the off-line count — *order-linked* (it is the order data);
- computation (b): `κ₋ = ` spectral flow of the FE involution `s ↦ 1−s` across the critical line / an
  APS boundary index — *structurally pinned* (a deformation-invariant integer).

So the HP-index reframe is a **principled source** of the pinned second computation that `121 §5`
demands — replacing the ad-hoc hunt for forcing invariants (all fork-dead) with index theory. The
open content is precisely whether (b) is *non-vacuously* pinned: whether the FE spectral-flow index is
forced to `0` by geometry, rather than merely re-counting (a). That non-vacuity is the `J`/F₁
existence question (T2) — the same wall, now as an **index/polarization** problem with tools the
spectral-reality frame never reached. `[OPEN — the route worth exploring]`

**Redirection of this session's salvaged instruments.** The winding/deck toolkit built and frozen
this arc — `im ∈ πℤ` continuous-hence-constant, Borel–Carathéodory, `πℤ/2πℤ` integrality gluing,
winding rigidity, anchored-disc zero budgets (`WindingRigidity`, `ArgumentVariation`,
`SeamCocycle`) — is **local spectral-flow / index calculus**. It was the wrong tool for
parity-*forcing* (Gate 4) but is the *right* tool for the `κ₋`-index computation (b): local winding of
the FE-forced section across the seam **is** local spectral flow. The instruments are not waste;
they were pointed at the forcing prong when they belong on the index prong.

**Statement to attempt (constraint form of HP)** `[CONJECTURE — Arc]`:
> The FE-forced Krein operator `D` admits a compatible polarization `J` (a point of `D_∞`) ⟺
> its spectral-flow index across the critical line vanishes ⟺ `κ₋ = 0` ⟺ RH; and the spectral-flow
> index is computable, homotopy-invariantly, from local winding data of the FE section on box
> annuli — the same deck/winding calculus, read as index rather than parity.

The load-bearing open input is the non-vacuity of the pinned computation (that the local winding
data integrate to a *geometrically forced* zero, not a re-count) — i.e., the polarization `J` /
weld `ω` of T2. HP therefore does not bypass the keystone; it **relocates** RH onto the keystone
through index/Hodge tools, which is where the un-exhausted mathematics is.

---

## 5. Forward moves (ranked, non-terminal)

1. **T1 step 0 — re-certify `Q_3`.** Pre-register the prediction; confirm the ζ-vs-DH cumulant
   separator is not a truncation/basis artifact (the anti-theatre gate). If it survives, it is the
   most buildable genuinely-new theorem: multiplicativity forces the seam signature.
2. **HP-index Arc — the `κ₋` spectral-flow object.** Formalize `κ₋` as the FE spectral-flow index and
   re-point the salvaged winding/deck instruments at it (index, not parity). Deliverable: a Lean
   object `seamSpectralFlow` with `κ₋ = ` (order-linked count) `= ` (winding index) as a *reduction*,
   exposing the non-vacuity question as the single open clause — the constraint-front analogue of
   `riemannHypothesis_of_residual_faces`, but on the index prong.
3. **T2 — locate `ω`/`J` one notch more precisely** via the polarization framing (period-domain
   `D_∞`), treating HP-as-polarization and the weld as one object.
4. **Collide T1 and the HP-index Arc:** the cumulant `Q_3` (T1) and the transverse index `κ₋` (T3) are
   both the Euler-vs-FE content; test whether the discriminator *is* the local obstruction to the
   spectral-flow index vanishing — one object, two fronts.

The reframe method is the standing instrument: before building any route, run §2 on it. If it is
theatre, it relabels a dead flow; if it is real, it names the tool the flow could not use and points
into T1/T2/T3.
