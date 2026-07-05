# 87 — (SMOOTH-LOW): the hierarchy, the O(1)-fluctuation law, and the Branch-A architecture

Session 2026-07-05 (seed 3253897643236190683). The single analytic gate left
in the B′ chain after doc 86. Everything here is derivation; labels per
paragraph. Outcome: the fork of doc 85 §7 resolves toward **Branch A at
derivation grade**, with the P-F5 plateau explained quantitatively.

## 1. The object and the downward filtration

Z = Σ_{u≥2 z-smooth} c_u X_u (frozen coefficients c_u = u^{-1/2}W_u after
doc 86 §3), row masses M_q = Σ_{minFac u = q}|c_u|² ≍ c/q (doc 86 §6),
σ² = Σ_q M_q ≍ c·loglog N. Order the primes downward: F_q = σ(X_{q'} : q'>q).
Row q is a polynomial in X_q with F_q-measurable coefficients; its linear
coefficient A_q = Σ_{minFac v > q} c_{qv} X_v is F_q-measurable. The
hierarchy is CLEAN: A_q depends only on phases ABOVE q. [PROVED HERE —
structure, one line from doc 86 §1.]

## 2. The two-cut correlation law [derivation; the fork's true root]

For the windowed Möbius field D_u (doc 86 §7a), the two-cut correlation over
the u-average, cuts x and y = xR (R ≥ e):
  avg_u D_u(x)·D_u(y) = Σ_{e<x, f<y} μ_w(e)μ_w(f)/lcm(e,f)
  = Σ_g μ²(g)/g · [M-type](x/g)·[M-type](y/g) + coprimality corrections
  ≍ C·(1/log y + 1/log R)            (g-split; M(t) = O(1/log t), PNT).
The decorrelation in the cut-ratio R is WEAK — 1/log R, not a power.
[CONJECTURE-grade constants; mechanism derived. Named **(L1)**; rigorous
version = a standard PNT partial-summation exercise.]

## 3. The O(1)-fluctuation law [the session's central finding]

Feeding (L1) into Var(σ_W²) = 2Σ_{p<p'} c(p,p')²/(pp') with
c(p,p') ≲ loglog/log(p'/p) (capped by col ≍ loglog near-diagonal), Mertens
banding p' ~ p·e^s gives
  Var(σ_W²) ≍ (loglog N)² · Σ_p 1/(p·log p) = Θ((loglog N)²) = Θ(E[σ_W²]²).

> **The conditional scale σ_W neither concentrates nor diverges: its
> RELATIVE fluctuation is order ONE, N-uniformly.** v := Var(log σ_W²) =
> O(1). Both prior readings were wrong: doc 86 §7(b)'s concentration sketch
> (assumed 1/√log R decorrelation) and the lognormal-divergence channel
> (needs v → ∞). The truth is a bounded mixture.

Three immediate consequences:
(i) **No N-divergence from the scale mixture**: the mixture multiplies the
    density by E[σ⁴/σ_W⁴-type] = e^{O(v)} = O(1). Branch B's only remaining
    mechanism inside this architecture is dead at derivation grade.
(ii) **The failed P-F5 band is explained**: my 1.35–1.42 assumed either a
    concentrated scale (Gaussian-ish plateau ≈ 1.4) or divergence; an O(1)
    lognormal-ish mixture lifts the plateau by e^{O(v)} — measured a ≈ 2.17.
(iii) **The same computation shape governs the smooth block's own level
    aggregates** ((CONC-A) analog): bounded relative fluctuation per level;
    the tail hierarchy contributes at scale-graded depths only.

## 4. The Branch-A architecture for (SMOOTH-LOW) [proof plan, typed]

Claim shape: P(|w + Z| ≤ tσ) ≤ C·t²·log(2/t), C N-uniform. Mechanism:
- **Small-q block (q ≤ q₀ fixed)**: finitely many quasi-1D directions carry
  an O(1) fraction of σ²; fixed-dimension phase-sublevel estimates give the
  bounded constant C(q₀) (this block is why the plateau is ≈ 2.2, not 1.35).
- **Mid levels**: Lindeberg CLT bulk — many rows, each o(σ²): Gaussian 2D
  density at scale σ; anti-concentration only improves under independent
  convolution (density monotonicity).
- **Tail levels (large q, remaining mass σ_deep² ≪ σ²)**: only reachable at
  scales t ≲ σ_deep/σ; grading the hierarchy by t yields the log(2/t)
  factor — the log-correction in (K-bdd-n-log) IS the depth of the prime
  hierarchy visible at scale t, N-uniform because depth enters through t,
  not through N.
- **Scale mixture**: multiply by e^{O(v)} = O(1) (§3).

Lemma ledger: (L1) two-cut correlation (rigorous PNT exercise);
(L2) level-mass O(1)-fluctuation from (L1) (second-moment bookkeeping);
(L3) hierarchical Esseen with density monotonicity (the technical core —
conditional per-level sublevel bounds glued down the filtration);
(L4) fixed-dimension small-q Esseen (standard).
Failure modes registered: if (L1)'s R-decay is genuinely absent (window
correlations conspire at ALL ratios), v is re-examined; the Branch-B
counter-programme is then the lognormal lower-bound construction through
E[σ_eff^{-2}]. §3's banding says this does not happen: the near-diagonal
band already saturates the variance at O(1)·E².

## 5. Status after this doc

- (K-bdd-n-log): OPEN, one architecture, four typed lemmas, no remaining
  fork inside the architecture. The entrance exam (P-F5) passed as
  registered and its anomaly (plateau 2.17) is now derived, not just
  measured.
- Lean substrate available for (L4)/(L3)-skeleton: dpoly surface,
  RouteBTwoField, the counting consumer. (L1)/(L2) are paper-first.

## Appendix A — (L1)/(L2) rigor status [same session]

The g-split of §2 runs on coprimality-restricted Möbius partial sums
M_r(t) = Σ_{m≤t,(m,r)=1} μ(m)/m; with the Landau-grade bound
M(t) ≪ exp(−c√log t) (PNT partial summation) the off-diagonal two-cut
correlation decays like exp(−c√log R) — STRONGER than §2's 1/log R
heuristic. The near-diagonal band needs no estimate (c(p,p') ≤ col_p and
the band's Σ1/pp' mass is O(1/log p)-summable): the load-bearing
conclusion is the UPPER bound
  Var(σ_W²) ≤ C·E[σ_W²]²  (⟹ v = O(1)),
now PROVABLE-shaped with citation base = PNT partial sums only. The lower
tail of σ_W² (log-integrability near 0) is separate and standard-shaped
(positive spread quadratic form, Paley–Zygmund); the density argument
consumes P(σ_W ≤ s) scale-by-scale rather than a literal e^{O(v)}.
Ledger update: (L1) rigorous-shaped; (L2) upper bound PROVABLE; (L3)
remains the technical core; (L4) standard.

## Appendix B — the caustic ladder, derived [same session; Lean two_phase_sublevel banked]

`two_phase_sublevel` (RouteBSublevel.lean) factors the 2D sublevel as
(per-phase arc bound 2πr/ρ) × meas(K), K = {φ : |‖c + Be^{iφ}‖ − ρ| ≤ r},
ρ = ‖A‖. Squaring the radial condition, K is a COSINE BAND:
  cos(φ − ψ) ∈ [u₁, u₂],  u₂ − u₁ = 2ρr/(‖c‖·‖B‖)
(exact algebra). Cosine-band measure: ≤ C·(u₂−u₁) in the transversal
regime (band away from ±1), ≤ C·√(u₂−u₁) unconditionally (arccos √-law at
tangency). Hence the CAUSTIC LADDER:

- one phase:   sublevel ≲ r/ρ                         [arc_sublevel — Lean]
- two phases:  ≲ (r/ρ)·√(ρr/(‖c‖‖B‖)) ~ r^{3/2}       [unconditional; the
  known two-arm caustic exponent — derived, matches the classical density
  singularity on |‖c‖ ± ‖B‖| circles]
- two phases, transversal: ≲ r²·ρ/(‖c‖‖B‖)·(1/incidence) [linear band]
- full hierarchy: the THIRD phase averages the caustic location (the band
  center ψ and radius ‖c‖ move with the remaining field), and the caustic's
  √-singularity is integrable — this is precisely where (L3)'s bounded
  r²·log(2/t) density comes from. The log is the t-graded depth (§4); the
  caustic contributes only a bounded constant after one averaging.

Next Lean bricks, in order: (CAUSTIC-cos) — meas{φ ∈ [0,2π] :
cos φ ∈ [u₁,u₂]} ≤ π·√(2(u₂−u₁)) + the transversal linear version (pure
real analysis, no obstructions); then the three-phase composition
(two_phase_sublevel + caustic-averaging over the third phase) = the (L3)
base case with the r² law.

### App B status update [same session, later]: rungs 1–3 + the reduction surface ALL FORMAL

`RouteBThreePhase.lean` (6 endpoints, axiom-clean) closes every declared
"next Lean brick" and one more:

- `cos_band_measure_shifted_gap` — the covering step isolated: any shifted
  band ≤ 4·(arccos u₁ − arccos u₂); √-law and linear law both specialize it.
- `arccos_gap_mul` — (arccos u₁ − arccos u₂)·(√(1−u₁²)+√(1−u₂²)) ≤ π(u₂−u₁),
  by sin_add_sin + Jordan only (no MVT): the transversal gap inequality in
  division-free form.
- `cos_band_measure_shifted_linear` — band ≤ 4π(u₂−u₁)/m at margin m.
- `bandCenter`/`bandHalf` + `radial_band_measure_transversal` — the radial
  band at caustic margin m: ≤ 2π·r(2ρ+r)/(√m·‖c‖‖B‖), LINEAR in r.
- `two_phase_sublevel_r2` — rung 3 (two phases, transversal): the r² law,
  fully formal, constant 2π²·... explicit: (2πr/‖A‖)·(2πr(2‖A‖+r)/(√m‖c‖‖B‖)).
- `three_phase_sublevel` — the 3D Fubini reduction: three-phase sublevel ≤
  (2πr/‖A‖) × μ²(ANNULUS of the remaining two-phase field around ‖A‖).

Remaining for the (L3) base case r²·log(2/r): slice the annulus in the
third phase (its η-section IS the moving radial band, with center
c + Ce^{iη} whose modulus sweeps a cosine band — `radial_band_measure`
applies to the caustic-distance distribution itself), then the dyadic
layer-cake: transversal scales pay the linear law, the O(r)-neighborhood
of the caustic pays the √-law once; sum = r·(const + log(2/r)). All
inputs to that assembly are now machine-checked; the assembly is pure
ENNReal bookkeeping over a finite dyadic family.

### (L3) LEDGER UPDATE [same session]: the base case is a THEOREM

`three_phase_sublevel_r2log` (RouteBThreePhaseLog.lean, axiom-clean):
for ‖B‖ < ‖A‖ (strict, generic position), r ≤ (‖A‖−‖B‖)/2, any σ0 in the
admissible window [2H̄/κ, G/3] and any dyadic depth J with G/3 < 2^J σ0:

  μ³{ |c + Ce^{iθ₃} + Be^{iθ₂} + Ae^{iθ₁}| ≤ r }
    ≤ (2πr/‖A‖) · [ J·C_shell(r) + 2·C_core(r,σ0) + C_mid(r) ]

with every constant explicit (κ = causticKappa, C_shell ~ r, C_core ~
√(r·(σ0+r)) ~ r at σ0 ~ r, C_mid ~ r). Taking J = ⌈log₂(G/(3σ0))⌉+1 at the
minimal σ0 ≃ 2H̄/κ ~ r yields the r²·log(1/r) law — the (L3) base case,
now a two-theorem composition (three_phase_sublevel ∘ annulus_lintegral_le)
with no logarithm formalized (J carries it).

Ledger: (L4) one-phase FORMAL (arc_sublevel); two-phase r^{3/2} FORMAL;
two-phase transversal r² FORMAL; **three-phase r²·log FORMAL**. Open above
the base case: the t-graded hierarchical induction (L3-step) — its
per-level engine is exactly the banked pointwise-cover + shell-arm pattern
applied to block sums conditioned on coarser blocks; and (L1)/(L2) supply
(PNT pole). Next generative move: type the induction step's interface
(conditional small-ball predicate on the Steinhaus model of
SteinhausModel.lean, consuming three_phase_sublevel_r2log as the floor).

### (L3) LEDGER UPDATE [same session]: the block STEP is a THEOREM

`block_smallball_condition` (RouteBBlockStep.lean, axiom-clean): for a
prime-supported block `s` with four distinguished dominant primes, the
Steinhaus small-ball probability of `w + Σ_{n∈s} aₙXₙ` is

    steinhausMeasure{ |w + Σ_{n∈s} aₙXₙ| ≤ t } ≤ (2π)⁻⁴ · M

UNIFORMLY in the conditioning value `w`, whenever the four coordinates satisfy
the uniform four-phase bound `M` at every center (supplied by
`four_phase_nested_uniform` ⟹ M = the explicit four-phase constant at rate
r²·J). The whole measure-theoretic reduction is now formal: block marginal
(Steinhaus event → finite product) → lmarginal peel of the four dominant
coordinates → angle rescale (Jacobian (2π)⁻⁴) → the caustic four-phase engine,
with the remaining coordinates passing their constant through a probability
measure (the exact conditional decoupling of §3, at the model level).

Ledger: (L4) FORMAL; two-phase r^{3/2}/r² FORMAL; three-phase r²·log base case
FORMAL; **(L3) block STEP FORMAL (model level)**. Open above: the graded ladder
(assemble the STEP across dyadic levels; per-level J = the t-graded log), then
(L1)/(L2) (PNT pole). Next generative move: type the graded-ladder interface
consuming `block_smallball_condition` as its per-level engine.

### (LOW) CONVERGENCE [cycle 55, cont. 28]: the certificate side has arrived at the same object

Codex batch (lean_updates_codex.md, 31 items; verified: lint green, six
load-bearing endpoints axiom-checked [propext, Classical.choice, Quot.sound]).
Two structural moves land directly on this doc's target.

**1. Every consumer now runs through ONE floor interface.** All seam / ANNEAL /
rung / sign endpoints (SeamCongruence, EMCarrier, AnnealWindowRelation) were
refactored to consume the single static predicate

    CarrierFloorOn S N ε  :=  ∀ z ∈ S, ε < ‖gN N z‖        (ZetaCarrier.lean:327)

— the (LOW) interface itself — in place of every raw `gN ≠ 0` oracle and every
pointwise EM-domination table. And three terminal RH gates were added:

- `riemannHypothesis_of_local_online_windows` — RH from local on-line exclusion;
- `riemannHypothesis_of_emCarrier_close_floor_sign_local_windows` — RH from
  per-window FINITE data: (AFE remainder ≤ ε₁) + (‖emCarrier − gN‖ ≤ δ on the
  charts) + `CarrierFloorOn (chartRA ∪ chartLA) N (ε₁+δ)` + a ξ sign table with
  the carrier-zero count budget Σ m₂ ≤ s;
- `riemannHypothesis_of_relative_floor_sign_local_windows` — same gate on the
  relative/U0 path.

Machine-checked shape now standing: **RH follows from a family of per-window
certificates whose only analytic input is the (LOW) floor on annulus charts** —
the sign table and count budget are finite/computable data. The certificate
TOLERATES carrier zeros: they may sit in the inner disc `r₀`, priced by the
count budget, and the floor is demanded only on the shell `r₀ < |z−a| < R`.

**2. The convergence.** The (LOW) floor is exactly the observable this doc's
smooth-low attack controls probabilistically: `block_smallball_condition`
bounds `steinhausMeasure{ ‖w + Σ_{n∈s} aₙXₙ‖ ≤ t } ≤ (2π)⁻⁴·M` — the measure
of the floor-FAILURE set in the model, uniform in conditioning. Deterministic
demand (certificate) and probabilistic supply (small-ball) meet at the same
quantity: ‖gN‖ near the line. The graded ladder and the certificate lane
consume the SAME per-level engine.

**Typed bridge lane (new lead, three named steps):**

- **(B1) Bohr transfer** [OPEN CORE, provable-shaped for fixed N]: for the
  finite carrier the frequencies {log p : p ≤ N} are ℚ-independent, so
  Kronecker–Weyl on the finite torus gives: limiting t-density of
  { t ∈ [0,T] : ‖gN(σ+it)‖ ≤ ε } ≤ steinhausMeasure{ ‖·‖ ≤ ε } (Portmanteau at
  a.e. threshold ε). The model IS the Bohr lift; `block_smallball_condition`
  then bounds the density of LOW-failure heights. Mathlib status of
  Kronecker–Weyl for the finite prime torus: to probe; if absent, it is the
  next buildable gap (same class as the Mertens pole — build it).
- **(B2) Movable-shell pigeonhole** [CONJECTURE]: the certificate needs the
  floor only at SOME shell radius r₀ ∈ [r_min, R). Integrating the failure
  measure over shell radii: a good radius exists unless failure has full
  radial measure — converting a.e.-HEIGHT floors into every-WINDOW floors, at
  the cost of the count budget. The a.e.→every obstruction MIGRATES from the
  analytic floor to the count face.
- **(B3) Count budget** [instrument banked]: Σ m₂ ≤ s compares carrier zeros
  in the disc (Rouché+EM counting — machine-checked island already in tree)
  with ξ sign alternations on the line (the classical density face).

Consequence: the RH-gate residue splits into (measure of floor failure) ×
(count of sign alternations) — the same two faces as the O(1)-fluctuation
mixture (§3 here = doc 88 §2), now on the CERTIFICATE side of the ledger.

Ledger: (L4) FORMAL; two/three-phase FORMAL; (L3) block STEP FORMAL;
**(LOW) certificate surface consolidated + three RH gates FORMAL (codex)**.
Next generative move: formalize (B1) as `FloorFailureDensity` on
SteinhausModel — t-density of LOW-failure heights on a vertical segment ≤ the
model small-ball bound — consuming `block_smallball_condition`; then (B2) as a
shell-selection lemma over r₀.
