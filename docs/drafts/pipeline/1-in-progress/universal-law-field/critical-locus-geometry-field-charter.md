# Critical-locus geometry of the explicit-formula moduli — the field charter

- **ID:** ULF-FIELD-1
- **Stage:** 1-in-progress
- **Type:** FIELD DEFINITION + FIRST THEOREMS (paper)
- **Source:** consolidation of the whole session — the inverse theory (N1–N8), the gas layer,
  the FORK-1 death, the DESC-1 route-collapse — after the user's correction that route-solving
  (window extension, one lane) is precisely the ancestral failure
- **Status:** [FIELD DEFINED] [Θ1 PROVED] [Θ2 CORE COMPUTED, CLASSIFICATION FROZEN]
  [Θ3 NAMED] [NO LEAN UNTIL THE FIELD DELIVERS] [NOT RH]

## What the field is

The corpus is not a list of failed routes; it is a chart of one geometric situation. The field
that organizes it:

**Objects.** Zero configurations: multisets Z in the open strip 0 < Re s < 1, invariant under
the reflection group R = ⟨s ↦ 1−s, s ↦ s̄⟩, with Riemann–von Mangoldt-compatible counting.
These form the explicit-formula moduli 𝕄 (pseudo-configurations allowed; the arithmetic-side
constraint defines a distinguished sub-locus, see Θ3). The RH locus 𝕄⁺ ⊂ 𝕄 is Re s = 1/2.

**Coordinates transverse to 𝕄⁺.** An off-line quadruple q = {1/2 ± t ± iγ} has displacement
coordinate t. Key structural fact: the quadruple is invariant AS A MULTISET under t ↦ −t.

**Criteria as functions.** Every RH criterion the corpus catalogues (384 producers; Weil
forms; Li coefficients; Nyman–Beurling distances; envelopes; moments; amplifiers) is a
function on 𝕄 or on a quotient of it. The field studies the geometry of 𝕄 at 𝕄⁺ and the
induced calculus of all such functions at once.

## Θ1 — the universal criticality theorem (PROVED)

> **Theorem.** Every function Φ on 𝕄 — any value space, no regularity assumed — is even in
> each off-line displacement coordinate: Φ(Z(t)) = Φ(Z(−t)). Consequently every smooth
> criterion has identically vanishing first derivative transverse to the RH locus: **𝕄⁺ is a
> critical locus of every criterion simultaneously.**

*Proof.* Z(t) = Z(−t) as multisets, because {1/2 ± t ± iγ} is t ↦ −t invariant and the rest
of Z is untouched. Any function of the configuration takes equal values. ∎

Remarks. (i) R-equivariance is not a hypothesis — any function OF the configuration is
automatically R-invariant; there is no escape by "breaking the symmetry" while remaining a
function of the zeros. (ii) This subsumes, as instances: the corpus's conjugation-no-sign
counterexample ({i, −i}); "Weil carrier = Σ squares — RH = reality of the g_ρ" (the criteria
see only g_q² ~ t_q²); the equidistributed-phase extremal degeneracy; and the Rodgers–Tao
result Λ_DB ≥ 0 ("RH, if true, is barely true") is the criticality statement in the single
heat-flow direction — the theorem says the true point is critical in EVERY direction.
(iii) The uniform explanation of the wall: no linear-response method can separate; every
route's discriminating information starts at second order. "Five lanes, one wall" is Θ1: the
wall is the degeneracy of the first-order theory, shared by construction, not by coincidence.

## Θ2 — the Hessian classification (CORE COMPUTED; CLASSIFICATION FROZEN)

Since first derivatives vanish identically, criteria are governed by their Hessians at 𝕄⁺.

**Computation (spectral type).** Call Φ_F spectral-type if Φ_F(Z) = Σ_{ρ∈Z} F(ρ) with F
holomorphic on the strip (R-symmetrized WLOG). Along one quadruple at ordinate γ:

    φ(t) = F(1/2+t+iγ) + F(1/2−t+iγ) + F(1/2+t−iγ) + F(1/2−t−iγ)
    φ'(0) = 0,   φ''(0) = 4 Re F''(1/2 + iγ) =: w_F(γ).

Additivity over zeros kills all cross terms between distinct quadruples. Hence:

> **The Hessian of every spectral-type criterion is DIAGONAL in quadruple coordinates, with
> weight function w_F(γ) = 4 Re F''(1/2+iγ):  D²Φ_F = Σ_q w_F(γ_q) · t_q².**

Instances: Weil forms (F = transform of the test; w = second derivative of the test transform
at the ordinate), Li coefficients (F_n(s) = 1 − (1−1/s)^n; w_n rational in γ), Báez-Duarte
distances (additive over zeros in the squared sense). Composite criteria (smooth functions of
finitely many spectral functionals, e.g. log-products/Jensen-type) acquire only a
finite-rank correction: Hessian = diagonal + finite rank, by the chain rule.

**Frozen classification theorem (the field's first substantial target).**

> (a) *Necessity is per-zero:* if Φ_F ≥ 0 near 𝕄⁺ with equality on 𝕄⁺ (the shape of every
> positivity criterion), then w_F(γ) ≥ 0 for every ordinate γ, because single-quadruple
> deformations are admissible configurations. This proves the corpus's empirical law
> "nonnegative-sum criteria are never weaker than RH-per-zero" as a general theorem.
> (b) *The cone has one extreme structure:* at second order every such criterion is a positive
> mixture Σ w(γ_q) t_q² of the per-zero reality tests t_q² ≥ 0; the extreme rays are the
> single-ordinate tests. The corpus's producer collapse (~96 producers = one identity; the
> criterion re-encoding template) is the canonicity of this mixture representation.
> (c) *Trichotomy = Morse data:* group 1 (weaker-than-RH) = criteria with w_F ≡ 0 on a
> co-infinite set (degenerate directions); group 2 (RH-per-zero) = diagonal-dominant
> nondegenerate; group 3 (exactly-RH) = criteria requiring uniform control of the FULL
> infinite diagonal form. The corpus's trichotomy card is the Morse-theoretic classification
> of functions at a degenerate critical locus.

Verdict discipline: (a) and the diagonality are proved above at the computation level; the
frozen part is the precise axiomatization (admissible configuration class, regularity of F,
the composite tier) and the hostile collision pass. Until that pass this is
[CANDIDATE NEW]: no classification over the SPACE of criteria is known to us in the
literature (single equivalences Li ⟺ RH etc. are points of the space, not its geometry;
Rodgers–Tao is one direction; the evenness folklore "zeros move in pairs" was never, to our
knowledge, promoted to the universal criticality + Hessian calculus).

## The escape map (leverage on all routes at once)

Θ1+Θ2 are proved for everything that factors through the zero multiset. The ONLY exits are
now theorems, not hunches:

- **E1 — don't factor through zeros.** Work on the arithmetic/coefficient side, where
  positivity EXISTS unconditionally (Λ(n) ≥ 0) instead of needing creation. Corpus's live
  arithmetic lanes (MR/short-interval, the gas/KMS layer, NB coefficient side) are exactly
  here — the field derives the corpus's live/dead lane map instead of tabulating it.
- **E2 — one-sided structure before second order.** Exploit cones-with-corners: mechanisms of
  Lee–Yang type that transport arithmetic-side positivity to spectral reality directly,
  bypassing the degenerate smooth calculus. (The gas layer's KMS positivity is the corpus's
  native candidate carrier.)
- **E3 — constraints (arithmetic rigidity).** Single-quadruple moves are admissible in 𝕄 but
  NOT tangent to the lattice-supported locus: moving one quadruple changes the arithmetic
  side by a continuous-support density, while the true system's deformations must keep the
  arithmetic measure supported on {log n}. The field's central open geometric question (Θ3):
  **compute the tangent cone of the lattice-supported (crystalline) locus at ζ and its angle
  against the off-line directions.** RH is the statement that no off-line deformation current
  has a lattice-supported arithmetic shadow — a crystalline-measure / Fourier-quasicrystal
  rigidity question (Meyer; Kurasov–Sarnak; Lev–Olevskii adjacency), where the corpus's
  completed-time-torus and gas layers live.

Every corpus no-go now reads as: the route worked inside the zero-functorial smooth calculus,
where Θ1 kills first order and Θ2 says second order is per-zero-or-nothing; the caps
(amplifier width, envelope, moments, coefficient-blind Perron, character-blind reciprocity)
are finite-block truncations of the one diagonal Hessian. The live lanes are exactly E1–E3.

## Make-or-die (next, in order)

1. **Hostile collision pass on Θ1/Θ2** — deformation/linear-response literature for zeros
   (De Bruijn–Newman/Rodgers–Tao; Polya–Jensen hyperbolicity; any "space of criteria"
   treatment; crystalline-measure rigidity for Θ3). Mandatory before any promotion.
2. **Θ2 axiomatization + proof to stage-2 standard** — the admissible configuration class,
   both tiers (spectral, composite), the extreme-ray argument written dependency-closed.
3. **Θ3 first computation** — the arithmetic shadow of a single-quadruple move, exactly:
   Δν_t(x) = −(4/√x)(cosh(t log x) − 1) cos(γ log x) dx/x-normalized form; verify
   continuous support; formulate the rigidity pairing precisely.
4. Only then: which E1–E3 mechanism the field's theorems select as forced, and whether the
   corpus's caps are recomputable as Hessian block norms (quantitative unification).

## Relation to prior cards

- Supersedes ULF-DESC-1 as the field carrier; DESC-1's audit table is inherited as data; its
  T1/T2 window targets are ROUTE-LEVEL and out of scope for this program (recorded as the
  route-collapse failure mode, 2026-08-09).
- The inverse theory (ULF-INV-0, N1–N8) becomes the field's necessity layer: N-axioms are
  consequences of Θ1/Θ2 for their respective functor classes.
- ULF-FORK-1's local-cone computation survives as E2's concrete local carrier.

## Log

- 2026-08-09 — field defined after the route-collapse correction. Θ1 proved (multiset
  evenness ⟹ universal criticality; R-equivariance shown structural, not assumed). Θ2 core
  computed (diagonal Hessian, weight 4Re F''(1/2+iγ); per-zero necessity; trichotomy as
  Morse data); classification frozen pending collision pass. Θ3 (lattice tangency /
  crystalline rigidity) named with its first computation specified. No Lean.

## Status update (2026-08-09, second pass)

- Collision pass EXECUTED (Bombieri–Lagarias arbitrary-multiset framing = nearest ancestor of
  Θ2, no space-of-criteria classification found; FQ field active but opposite direction;
  Rodgers–Tao = heat-flow instance of Θ1). Verdicts recorded per-theorem in the stage-2 card.
- Θ1, Θ2(i)–(v), Θ3.1–3.2 PROVED dependency-closed and PROMOTED:
  docs/drafts/pipeline/2-fully-proven/universal-law-field/
  critical-locus-hessian-classification-and-crystalline-transversality-law.md (ULF-FIELD-2).
- Refinement discovered in the write-up: simple line zeros admit no continuous R-invariant
  exit — off-line motion emanates only from multiple zeros. Consilience with the corpus's
  simplicity layer (Cauchy core density = zero simplicity; eigen-span positivity ⟺ RH ∧
  simplicity): the moduli's singular points are the multiple zeros.
- OPEN ATTACKS the classification leaves possible (the field's forward program):
  1. The infinite tangency calculus: quantify Θ3.2's cancellation obstruction for INFINITE
     off-line families against the positivity Λ(n) ≥ 0 — classical ZFRs are its first
     estimates; the target is a tangency estimate not passing through the classical routes.
  2. The E2 transport mechanism: one-sided (Lee–Yang-type) transport of arithmetic-side
     positivity acting before second order; the gas/KMS layer is the corpus's native carrier.

## First application: classification audit of the corpus's live lanes (2026-08-09)

Sources read: rh-lane-elimination-map (full audit §§1–43 + Lee–Yang closure),
weil-polarization-layer-state, root-adjunction-isolated-route-alive, mr-path-gap-status.
Verdicts under Θ1–Θ4:

| Live lane (corpus state) | Θ-classification | Typed consequence |
|---|---|---|
| UV model (only live object; wall = `archimedeanPrimeEulerQuadraticCorner_not_isCompactOperator`) | E1/E2 — arithmetic-side operator construction, does not factor through the zero multiset | **UV = E2 locus identification:** any trace-class/compact comparison closing the UV gate would land the final gate back in the classified smooth calculus (Θ2 ⟹ per-zero or group 3). The proved noncompactness is therefore not an accident but the lane's protection: the missing UV model MUST carry one-sided, non-trace-class (type III) positivity transport. This types Connes's named gap, the corpus's UV wall, and FORK-1's divergent vacuum ledger as ONE locus. |
| Weil polarization layer (full-test-algebra gate; eigen-span positivity ⟺ RH ∧ simplicity) | Group 3 by Θ2(v) — the eigen-span form IS the full infinite diagonal Hessian | The layer's own antidiagonal Gram law is the field's diagonality (Θ2(i)) in eigen coordinates. No finite extension of the test algebra can close it (Θ4). The gate is a presentation of the limit class; work on it is group-3 maintenance, not leverage. |
| MR / Route E corridor (real frontier = Halász analytic half: δ lower bound, exceptional frequency) | E1 — sign-class density statistics, not a zero-multiset functional | Untouched by the classification; remains genuinely live. The field adds: this lane's outputs (zero-density-type upper bounds) are exactly the count-direction exception (§§32–43 consilience) — the only engine family bounding N_off from above. |
| Root adjunction / Deninger–Baumslag mixing | E1 — group-theoretic, no zero-multiset factorization | Outside the classification's scope; alive on its own terms. |
| Lee–Yang / prime Ising tree lane (CLOSED 2026-07-31: central-mass floor m(T) ≥ log 2; only the factored E·XiC form survives, E paying ≥ log 2/2) | E2 instance, already capped by the corpus | **Constraint imported into the field's E2 attack:** any transport realizing XiC as a Lee–Yang-type limit must use the factored form and pay the normalizer mass floor. The gas/KMS E2 carrier must be checked against this cap BEFORE construction — it is the E2 analogue of a collision pass. |

Net effect on the two open attacks:
1. The E2 attack inherits a hard corpus cap (mass floor) and a positive typing (the UV locus
   is where E2 must act, in non-trace-class form). The attack's make-or-die: exhibit a
   one-sided positivity transport at the noncompact Euler corner that is NOT a trace-class
   comparison and does NOT present XiC as an unfactored Lee–Yang limit.
2. The infinite tangency calculus is now bounded on both sides: Θ4 (spectral side has no
   finite subcover) vs Connes–Consani semilocal positivity (arithmetic side has all finite
   subcovers); the limit class is squeezed between a theorem and a theorem. Its quantitative
   layer coincides with the classical Θ-invariant/zero-density theory — route-collapse
   hazard recorded: do NOT attack it by re-deriving zero-density estimates; the open
   non-classical invariant is the phase-locking of off-line shadows (cos(γ_j x) phases tied
   to ordinates), which no classical engine uses.
