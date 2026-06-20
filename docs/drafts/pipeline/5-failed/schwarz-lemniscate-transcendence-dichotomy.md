# Λ-lemniscates and the Schwarz-function transcendence dichotomy — a candidate native invariant from quadrature-domain theory

- **ID:** schwarz-lemniscate-transcendence-dichotomy
- **Stage:** 5-failed
- **Type:** CONJECTURE (native-object candidate) → **FALSIFIED** (validated against the known, it fails)
- **Owner:** Wheeler
- **Door grade:** **EMBASSY (falsified)** — the central claim is false; the invariant is blind to
  hypertranscendence.

> **FALSIFIED (2026-06-20, same-author validation pass).** The central conjecture §3 is **false**. The
> harmonic-moment Hankel rank `μ` tracks the **number of enclosed zeros**, *not* the differential-algebraic
> type. Mechanism: for `Ω_r(F)`, `M_k = (1/2i)∮ z^k S(z)\,dz`, and the singularities of `S` inside `Ω` sit at
> the **zeros of `F`** (where `r²/F→∞`), so the quadrature nodes **are** the zeros and `μ = #zeros enclosed`.
> **Killer counterexample `F = sin z`:** differentially algebraic (`y''+y=0`, the *opposite* of
> hypertranscendental) yet infinitely many zeros (`nπ`) ⟹ infinite quadrature nodes ⟹ `τ=transcendental`,
> `μ=∞`. So `transcendental/∞` does **not** imply hypertranscendence. (Confirmed numerically: `sin`-window of 7
> zeros → full power-sum/Hankel structure of rank = #nodes; `F=z` → rank 1.) Moreover the §2 "finite-moment
> `F_q` border" was an **artifact of the rational `u`-variable**: in the native `s`-variable `ζ_C` is periodic
> with infinitely many zeros too, so there is no finite/∞ dichotomy mirroring corank. **Deep reason:**
> hypertranscendence is a *differential-algebraic* property (the `∂_s` structure); the Schwarz/level-set
> construction sees only **zero geometry and growth**, which is orthogonal to differential type. Geometric
> `|F|`-level-set invariants are structurally blind to hypertranscendence. → moved 1-in-progress → 5-failed.
- **Source / method:** wild-analogy collision under method **revisualise** — recast the FE-involution
  `s↦1−s` as Schwarz reflection across a curve; collide with **coral / Laplacian-growth** (the Schwarz
  function governs free-boundary growth) and **immune-system** (form fixed by a negative constraint). Entropy
  seed 3050780354571332636. Quadrature-domain / Laplacian-growth theory is **absent from this corpus** (no
  Schwarz function, harmonic moments, or quadrature domains anywhere in the ledger/door buckets).

---

## §0 The leap in one line
The field's `F_q ↔ ℚ` border (algebraic/holonomic ↔ hypertranscendental) **is** the
**quadrature ↔ non-quadrature** border of the free-boundary domain associated to `Λ` by Schwarz reflection;
the **Schwarz-transcendence type / harmonic-moment rank** of `Λ`-lemniscates is a candidate **new native
invariant** that imports an entirely foreign toolkit (Laplacian growth, conserved harmonic moments).

## §1 The object
For an entire/meromorphic `F` and a regular value `r>0`, the **lemniscate domain**
`Ω_r(F) = { z : |F(z)| < r }`, with boundary `∂Ω_r = {|F|=r}`. Its **Schwarz function** `S_r` is the analytic
function with `S_r(z) = z̄` on `∂Ω_r`. On the boundary `F(z)·\overline{F(z)} = r²`, and
`\overline{F(z)} = \bar F(\bar z) = \bar F(S_r(z))` (with `\bar F` = `F` with conjugated coefficients). Hence
```
        \bar F( S_r(z) ) = r² / F(z)          (the defining relation of the Schwarz function).
```
Define the **Schwarz-transcendence type** `τ(F) ∈ {algebraic, transcendental(-with-natural-boundary)}` of
`S_r`, and the **harmonic-moment rank** `μ(F)` (the rank of the exterior harmonic moment sequence of `Ω_r`,
the Laplacian-growth invariant).

## §2 Border anchor — `F_q` / rational `F` ⟹ algebraic Schwarz, finite moments `[PROVED HERE / IMPORT]`
If `F` is **rational** in a uniformizer (the function-field zeta `ζ_C(u) = P(u)/((1-u)(1-qu))`, `u=q^{-s}`,
`P∈ℤ[u]`), then `\bar F(S) = r²/F(z)` is an **algebraic equation** in `S` over `ℚ̄(z)`, so `S_r` is an
**algebraic function** — `Ω_r` is an **algebraic / quadrature domain**, with **finitely many** independent
exterior harmonic moments. (Elementary from the boundary identity; the quadrature-domain framework is the
classical Aharonov–Shapiro / Sakai theory — IMPORT.) Confirmed: for `F=z²−1`, the boundary identity
`\bar F(\bar z)=r²/F(z)` holds on `{|F|=r}` to scan tolerance.
**Reading:** over `F_q`, `τ = algebraic`, `μ < ∞` — the holonomic / single-Frobenius border.

## §3 The central conjecture `[CONJECTURE]`
> `Λ(s) = Γ(s/2)π^{-s/2}ζ(s)` (equivalently `ξ`) is hypertranscendental (Hölder/Li–Ye); then its lemniscate
> Schwarz function `S_r` is **transcendental with a natural boundary** (non-quadrature), and the exterior
> harmonic-moment sequence is **infinite-rank**. So `τ(Λ) = transcendental`, `μ(Λ) = ∞`.

Combined with §2: the map `F ↦ (τ(F), μ(F))` is a transcendence invariant that reads **algebraic/finite over
`F_q`** and **transcendental/∞ over `ℚ`**, mirroring `corank` (`1` vs `∞`) through the Schwarz function rather
than the difference-Galois lattice. The hypertranscendence of `Λ` would be **the non-integrability of an
associated free-boundary (Laplacian-growth) problem** — "constraint, not flow," now read as: the boundary is
pinned by a transcendental Schwarz constraint admitting no finite quadrature (no finite generative rule).

## §4 Why it might be NATIVE, and why it might be EMBASSY — the honest viability gate (Door-2)
**Possibly native.** Harmonic moments are neither a difference-Galois invariant (`G_L`, corank) nor a standard
analytic-number-theory invariant; they would be a genuinely new handle, and the quadrature↔transcendental
dichotomy is itself a transcendence dichotomy matching the field's. Laplacian growth carries an *integrable*
structure (conserved harmonic moments, a τ-function) that could give new conserved quantities for `Λ`.

**Possibly EMBASSY / BRIDGE (the real risks, stated plainly):**
- **(a) Geometry mismatch.** `Λ`-lemniscates are **disconnected** (for small `r`, droplets around each of the
  infinitely many zeros) and **unbounded** (`Λ→∞`). Classical quadrature theory is for *bounded* domains; the
  global object may not be a quadrature domain in any usable sense, making §3 ill-posed as stated.
- **(b) Re-encoding, not new information.** The harmonic moments of `Ω_r(Λ)` may merely **re-encode** `Λ`'s
  Taylor coefficients / zero set — in which case `μ` is a renaming of known data and the item fails **Door-2**
  (BRIDGE, not native). To be native, `μ` must compute something **not** recoverable from the zeros.
- **(c) Trivial dichotomy.** "`S` algebraic ⟺ `F` rational" might be the entire content, so
  "quadrature ↔ non-quadrature" is just "rational ↔ transcendental" relabelled — a re-description.

**The viability test (the open crux this card owes):** *does the harmonic-moment data of `Ω_r(Λ)` carry
information beyond `Λ`'s zeros/coefficients?* If yes → candidate NATIVE invariant, promote and compute it on
the `F_q` border to check it equals `corank`. If no → grade EMBASSY/BRIDGE and retire. **Until answered this
stays a SEARCH-register conjecture; nothing here is promoted.**

## §5 Door passport (provisional)
- **Door-5 ✓ (border):** rational `F` (function field) ⟹ algebraic Schwarz / quadrature / finite moments —
  recovers the algebraic/holonomic border. Proven (§2).
- **Door-2 OPEN:** the viability test (§4). This is the difference between a new native invariant and a
  gorgeous re-description.
- **Grade:** EMBASSY-aspiring-NATIVE. The novelty is the **bridge proposal** (quadrature-domain / Laplacian
  growth ↔ hypertranscendence), validated only at the border so far.

## Gates
- [x] 0 → 1: object defined (`Ω_r`, `S_r`, `τ`, `μ`); border anchor proved (§2, rational ⟹ algebraic Schwarz);
  central conjecture stated (§3); the EMBASSY-risk / Door-2 viability test stated honestly (§4).
- [ ] 1 → 2: **BLOCKED** on the viability test (§4). Sub-steps owed: (i) make §3 well-posed for the
  disconnected/unbounded `Λ`-lemniscate (per-droplet quadrature + a global moment bookkeeping, or restrict to a
  single fundamental component); (ii) decide whether `μ` exceeds the zero/coefficient data (native vs BRIDGE);
  (iii) compute `μ` on a finite-Euler / `F_q` truncation and test `μ = corank`.
- [ ] 2 → 3: n/a until promoted.

## Notes / risk
- Only the **elementary algebraic-Schwarz border** (§2) is proven, and it is IMPORT-level. The contribution is
  the **wild bridge** and a sharp, falsifiable viability test — explicitly *not* a theorem about `Λ`.
- Honesty: this is exactly the kind of generated leap the method calls for (induction over deduction), and
  exactly the kind that must be guarded against EMBASSY. The guard is §4; I am not claiming native status.
- Prior-research check: no Schwarz-function / quadrature-domain / Laplacian-growth content found in the ledger,
  door buckets, or my lane memory — the import is fresh to this project.

## Log
- 2026-06-20 — Wheeler. Created in 1-in-progress (SEARCH register). revisualise + coral/Laplacian-growth +
  immune collision recast the FE-involution as Schwarz reflection and imported quadrature-domain theory.
  Proved the rational-`F` algebraic-Schwarz border (§2, numerically corroborated); stated the
  hypertranscendence ⟹ transcendental-Schwarz / infinite-moment conjecture (§3) and the honest Door-2
  viability test (§4). Grade EMBASSY-aspiring-NATIVE; not promoted.
- 2026-06-20 — Wheeler. **FALSIFIED same tick** by running the viability test (extreme-cases / minimal-
  counterexample). Moment-Hankel rank = #enclosed zeros (nodes = zeros of `F`), so `τ/μ` tracks zero-count, not
  differential type; `sin z` (diff-algebraic, ∞ zeros) breaks the mirror. The `F_q` border was a `u`-variable
  artifact. Net lesson banked: geometric `|F|`-level-set / Schwarz-function invariants are blind to
  hypertranscendence (a differential-algebraic notion) — a guardrail against the whole "growth-geometry"
  class of approaches. → 5-failed. Generate-then-validate worked as intended; the EMBASSY-risk flag fired.
