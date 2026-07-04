# 59 — Cofinality of Self-Dominated p-Central Windows: the Littlewood Mean Closes the Measure Clause

**Register: SEARCH**, carrying one [PROVED HERE (paper-sketch)] mean bound and a
typed residue. Target: doc 43 §9(2) — the p-central window family must supply,
cofinally in T, windows with min_{∂W}|g_N| > E*(T) (parity transport needs the
boundary clause only, doc 43 §8). g = g_N is the exact-FE matched truncation,
E*(T) = O(T^{−1/4}).

## 1. (C1) The mean-Littlewood bound [PROVED HERE (paper-sketch)]

**Claim.** Per unit t-length, at every fixed σ ∈ [1/2, 1]:
meas{ t : |g(σ+it)| ≤ E*(T) } ≤ C·(log log T)/(log T).

*Proof sketch.* (i) Littlewood's lemma on the rectangle [σ, 3] × [T, T+U]:
mean_t log|g(σ+it)| = mean_t log|g(3+it)| + (2π/U)·Σ_{zeros in rect}(β−σ)
+ O(edge/U). At σ = 3 the sum is 1 + O(2^{−3}·ζ(3)-tail): log|g(3+it)| ≥ −C₀
pointwise. The zero-sum is ≥ 0. Hence mean_t log|g(σ+it)| ≥ −C₁. (ii) Jensen
against the second moment (MV): mean_t (log|g|)⁺ ≤ ½·log mean|g|² =
O(log log T). (iii) Therefore mean_t (−log|g|)⁺ = mean(log)⁺ − mean(log) =
O(log log T), and Markov at the threshold −log E* = ¼·log T gives the claim. ∎

Consequences, immediate:
- **Vertical-edge threading:** a vertical boundary segment at clean σ avoids
  {|g| ≤ E*} for all but a (log log T/log T)-fraction of edge placements —
  cofinal good placements exist with density → 1.
- **Test points in almost all gaps:** the bad measure per unit is
  o(1/log T · log T) spread over ~log T gaps: the average gap carries bad
  measure ≪ its length 2π/log T. (Parity transport does not need every gap —
  doc 43 §8(i).)
- This retires the doc 12 (D′) small-ball import for the measure clause: plain
  Littlewood + Jensen suffice. No CLT, no chaos technology.

## 2. (C2) The residue: horizontal-edge threading — the union-bound gap

A horizontal edge spans σ-width w (≍ the stratum depth, up to 1/4): a σ-grid of
~w·log T points, each bad on a (log log/log)-measure of heights — the union
bound loses by w·log log T. Typed routes, in force order:

1. **Short-width strata:** run the parity ladder on σ-width ≤ A/log T windows
   (O(1) grid points — union closes with (C1) alone). The deep strata
   (w ≫ 1/log T) are exactly where Ingham's density theorem already thins the
   zeros — the doc 06 quantified reduction (R_k^θ) carries them; only the
   near-line strata need windows, and there w ~ c/log T. **[REDUCTION-shape:
   check that the doc 06 grading and the window strata can be matched at the
   seam w ≍ 1/log T — if yes, (C2) DISSOLVES and cofinality is closed by (C1).]**
2. **Deformation with local Jensen:** deform horizontal edges around the
   O(log log)-many bad discs met per crossing; each deformation changes the
   enclosed count by the disc's zero count (local Jensen O(1) from (C1)'s
   anchor grade); parity bookkeeping absorbs an explicitly-counted correction.
3. **Defect second moment:** mean((−log|g|)⁺)² = O((log log)²) would give
   per-σ measure ≤ (log log/log)² and the union closes for w ≤ 1. This is a
   Littlewood-squared/variance object — Selberg-CLT-adjacent, priced
   accordingly (frontier; do not attack first).

## 3. Status after this document

Cofinality = (C1) [closed, paper-sketch grade — Lean: the Littlewood rectangle
is `SecondMoment.dpoly`-adjacent plumbing plus mathlib's Jensen] × (C2)
[route 1 is a matching audit, not new analysis — next executable]. The
p-central family's EXISTENCE clause (60% of heights, survivor-free measured)
was never in doubt; the burden was always the domination certificate, and (C1)
prices it.

What this opens: route 1's seam-matching (deep strata to Ingham, shallow to
windows) is the same split doc 57 §3(a) found from the transport side — the
bridge is converging on a single architecture: **density theorems govern
w ≫ 1/log T, windows govern w ≍ 1/log T, and (CR-density)/Route A/B governs
creation inside the window scale.** Doc 60 (chain audit) should draw this as
the master diagram.

## 4. CORRECTION (same lane, cycle 33): §1's Littlewood sketch has a sign/arg gap; the convexity-tangent repair is stronger

Attack-as-false, fired on our own claim while mining Selberg's method. §1's
step (i) treated the horizontal/argument terms of the Littlewood rectangle as
O(edge/U). That is wrong at scale: the vertical-argument integral carries
O(U·density)·(σ-width) — the SAME order as the zero-sum — and the two cancel
only to fluctuation order. As sketched, step (i) does not prove the mean
lower bound. (§1's conclusion survives; the proof is replaced.)

**Repair [PROVED HERE (sketch) — convexity + tangent, no zero data at all].**
Φ(σ) := (1/U)∫ log|g(σ+it)| dt is CONVEX in σ (∂²_σ Φ = (2π/U)·(zero measure
on the line) ≥ 0 distributionally; window-end corrections O(log N/U)). At
σ = 3: Φ(3) ≥ log(1 − (ζ(3)−1)) ≥ −0.23 pointwise, and |Φ′(3)| =
|mean Re(g′/g)(3)| ≤ Σ_{n≥2} n^{−3}log n / (1 − Σ_{n≥2} n^{−3}) ≤ 0.45.
A convex function lies above every tangent: for σ ∈ [½, 3],

> Φ(σ) ≥ Φ(3) + Φ′(3)(σ − 3) ≥ −0.23 − 0.45·2.5 ≥ −1.36.

Zeros only increase convexity; they cannot break the tangent bound. All §1
consequences (vertical threading, almost-all-gap test points) survive with
the constant −1.36 in place of the broken step. The same repair applies
verbatim to any Dirichlet polynomial with leading coefficient 1 — consumed
at scale in doc 67.
