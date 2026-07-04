# 79 — SPUR-R Route Verdict: Superseded, Sound-Not-False, Open Core Isolated

**Register: LEDGER for §1 (machine-checked) and §2 (measured); SEARCH for §4.**
Tasks #135 (SPUR-R), #138 (AMP-mono (iii) / (S-mono)), #139 (Lemma R): driven to a
terminal verdict. Method: establish the load-bearing status by the Lean import graph and
axioms (not by assertion); attack the algebraic core and the target as false; isolate what
remains. Result: the DISC/SPUR-R **reader** is a non-load-bearing, dominated instrument —
retired as a route to #130; sound, not false; its one open analytic hypothesis isolated as
a standalone entire-function conjecture.

## 1. Not load-bearing for #130 — machine-checked

The live #130 counting/transport spine
(`enclosed_count_eq_of_close`, `pinned_zero_re_eq_half`,
`anneal_deck_transport_of_emCarrier_close`, `anneal_seam_L_transport_of_emCarrier_close`,
`completed_domination_of_em`, `zeta_sub_emCarrier_norm_le`,
`xi_rung_of_finite_side_of_domination`) is:

- **axiom-clean** — every one depends only on `[propext, Classical.choice, Quot.sound]`;
- a **transitive-import island** — none of these, nor any of their transitive
  RHTower imports (checked over the full `import` closure), touches ANY of the 23
  `Spur*.lean` modules. The only non-`Spur` importer of `Spur*` is `CoefficientTail.lean`
  (itself a Spur-cluster leaf) and the umbrella.

So exact enclosed-multiplicity counting under domination (the Rouché substitute, #128) plus
on-line pinning is delivered UNCONDITIONALLY in Lean — modulo the single finite inequality
(EM-CLOSE) (doc 78) — with no DISC/section-stability reader anywhere in the chain. The
counting role SPUR-R was built to fill is filled, by a different and unconditional route.

## 2. Dominated instrument — the reader needs strictly more than Rouché

| | needs, to count off-line pairs in a window |
|---|---|
| **Rouché + EM** (live) | **domination** only: `‖f − g‖ < ‖g‖` on the annulus charts — a SIZE estimate, unconditional via `EMCarrier.lean` |
| **DISC / SPUR-R** (retired) | (S-mono) outer single-crossing (analytic, still outline) **+** (F1)–(F3) zero-geometry of the recentered Ξ₁ carrier (one-sidedness, nondecreasing gaps, regularity — doc 31 §4, MEASURED-only) |

The reader reads the pair count from the section-zero configuration, so it must control that
configuration on the actual carrier — a zero-geometry input. Rouché reads it from a size
comparison, which the EM carrier supplies with zero unformalized analysis. An instrument that
requires zero-geometry to deliver an output the size estimate already delivers is dominated.

## 3. Sound, not false — verified; Lean form is honest-complete

Attack-as-false on the algebraic core (`computations/mwm/winding_check.py`,
`smono_check.py`):

- **Winding formula** `Z_c((D−τ)(D−τ̄)Â) = 2·wind(F_B(ℝ),τ)`, `B=(D−τ̄)Â`, `F_B=B′/B`:
  magnitude matches in every simple-rooted case (2↔1.92, 2↔1.96, 0↔0, 8-root 2↔1.92);
  the two-cluster no-go reproduces `Z_c=4`; the multiple-root configuration correctly breaks
  the winding integral (min Im of B-roots = 0), matching the doc 28 §2a correction. Core
  identity `Ĵ = Â″ − 2aÂ′ + |τ|²Â` holds.
- **Target `Z_c=2`**: on a genuine one-sided-far LP×pair section carrier, `Z_c ∈ {0,2}`
  across `d = 6…60` and six `(a,b)` — **never > 2**; `Z_c` climbs 0→2 exactly at the
  visibility threshold (e.g. `(a,b)=(3,0.5)` at `d=40`), matching `d ≥ d₀(g,τ)`. No spurious
  pair ever appears: reader-exactness is empirically robust.

Lean form (codex #143) is complete to its honest floor: the open analytic core is
**hypothesis-typed** (`SpurCapstone.AMPReaderInput` — the single-crossing premise), and
everything below it is PROVED and axiom-clean — the corrected counting lemma
(`amp_reader_exact_pair_of_input`), UHP-stability (`uhp_of_pair_shift_root`), Lemma W
(`hermite_energy_eq_charge`), the cumulant/(E5) bounds (`SpurRescale.*`). SPUR-R is therefore
a valid CONDITIONAL theorem; discharging its hypothesis is exactly proving (S-mono) on real
fields.

## 4. The isolated open core (standalone, not resolved)

> **(S-mono)** [CONJECTURE — proved in outline on abstract fields, docs 29–31; NOT
> promotable]. For a finite one-sided log-field of section zeros with nondecreasing gaps,
> the reduced energy `S_i = d + ¼Σ csch²((t*_i − t_k)/2)` is increasing along the outer
> equilibria. Equivalently: the margin `q_d(c)/(c⁴ℰ(c))` crosses 1 exactly once, so
> `Z_c(J^d_{Pg}) = 2`. Corroborated numerically (§3, and doc 24 §4); the constant-δ lattice
> case has a five-step outline (doc 29); the general-field (χ1),(χ2) chases are elementary
> coth/csch comparisons (doc 31 §5). Companion: **Lemma R** (#139) — Hermite cluster
> splitting for multiplicity `m ≥ 4` (doc 34), proof-shaped, probe-certified, needed only
> for multiplicity-uniform generality (every live finite instance has simple zeros, doc 31
> §6; `m ≤ 3` is unconditional via `SpurRescale`).

This is a pure statement about non-real zeros of `(D−τ)(D−τ̄)` applied to Jensen sections of a
Laguerre–Pólya carrier — a native hgt object (section-zero configuration fixed by the pair
constraint). It survives as an independent question; it is not a blocker of #130 and is not
claimed proved.

## 5. Task dispositions and the forward move

- **#135, #138, #139 → retired** (route superseded; §1–§3). #130's `blocked by #135`
  edge is stale and removed: the bridge identity's counting side is the Rouché+EM spine,
  whose true open core is **(XLD)** cross-level decorrelation (doc 75 §5, doc 76-xld), not
  reader-exactness.
- The SPUR-R Lean stack stays as a self-contained conditional island (`AMPReaderInput`
  hypothesis-typed); no sorries, no axioms, nothing to unwind.

Forward: the counting side of #130 being unconditional (Rouché+EM) puts the whole remaining
load on **(XLD)₂** — the two-level persistence increment `P(C_{n+1}|C_n) = P_null·(1+o(1))`
of doc 76-xld §3, whose survival channel is measured phase-neutral to ≤6% and whose relay
channel is the sub/super-critical discriminant against D–H. That increment — one added
Dirichlet term `(n+1)^{−s}` + mirror — is the next object, and it is size/phase arithmetic,
not zero-geometry: the same reason the reader was retired points at where to push.
