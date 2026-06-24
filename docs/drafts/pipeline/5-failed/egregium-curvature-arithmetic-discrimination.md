# Local "egregium curvature" certificate of hypertranscendence — does NOT discriminate arithmetic

- **ID:** egregium-curvature-arithmetic-discrimination
- **Stage:** 5-failed
- **Type:** NEGATIVE (rigorously controlled)
- **Owner:** Turing
- **Source:** entropy draw (seed 39492771685926316) — change-representation × cartography (Theorema Egregium)
  × the weld; the question "is there a local intrinsic curvature-like certificate of hypertranscendence?"

## What was tried
Jet curve J_n(s) = (y, y', …, y^(n)). Define D(m) = min degree of an algebraic hypersurface osculating
J_n to order m at a SINGLE point s₀ (computed from derivatives at s₀ only — "local/intrinsic", the egregium
analogy). And κ = the σ_min of the column-normalized osculating matrix at matched (D,m) — a candidate
quantitative "curvature" hoped to discriminate arithmetic HT functions (Γ, ζ) from generic HT.

## What is TRUE (but search-grade)
- D(m) **caps** for differentially-algebraic functions (exp → 1, Riccati y'=y²−y → 2) and **climbs unbounded**
  for HT (Γ: 1,2,2,2,3,3,3,3,4,4,4 at jet-order 1, s₀=1.3). Verified numerically (mpmath).
- This qualitative caps-vs-climbs is exactly **Kolchin's differential dimension polynomial** ω(t): eventually
  constant for DA, ω(t)=t+1 (maximal) for HT. So the certificate = Kolchin in osculating-degree clothing.
  Correct, but reduces-to-known.

## Why the arithmetic-discrimination FAILED (the dead route — do not re-run)
κ = σ_min looked like it discriminated (Γ σ_min ~1e-10…1e-18, ζ ~1e-22…1e-38, vs random-HT ~1e-3).
ALL of it was artifact, killed across 4 control rounds:
1. **Magnitude artifact** — random control had O(1) jets; Γ,ζ have ≈k! jets. Magnitude-matching shrank the gap.
2. **ζ's huge signal = POLE proximity.** Near s₀=1.3, ζ(s)≈1/(s−1), which is ALGEBRAIC (y'+y²=0, degree 2),
   so ζ's jet curve hugs an algebraic curve trivially. Off-pole (s₀=4.0) ζ's σ_min collapsed 1e-38 → 7e-19,
   down to Γ-level. ζ is not arithmetically special here; its pole was.
3. **Γ's residual = near-exponentiality.** Γ has slowly-varying log-derivative ψ ⟹ locally Γ≈A·e^{Bs} ⟹ jet
   curve near the exponential's algebraic curve. A genuine non-arithmetic HT control y=exp(random-smooth-g)
   (near-exponential, no arithmetic) has σ_min spanning ~4 orders by seed, and Γ sits INSIDE that distribution.

**Verdict:** σ_min measures proximity of the local jet curve to SOME low-degree algebraic curve — driven by
ANALYTIC structure (pole proximity → near-rational; smooth log-derivative → near-exponential), wildly
seed-variable, carrying NO arithmetic signal. The quantitative "curvature" κ is analytic conditioning, not an
invariant. Dead as an arithmetic discriminator.

## The one forward pointer (not failed — relocated)
A local invariant that sees ARITHMETIC must first FACTOR OUT the analytic type (pole locations, log-derivative
growth), then read the residual. This is the SAME structural lesson as Wheeler's `seam-lock-completed-cohomology`:
the algebraic (⊕, finite) cohomology saturates generically; arithmetic lives in the completed (∏/⊕, infinite-tail)
part. "Arithmetic = full data / analytic-type normalization" (jet language) = "arithmetic = completed/algebraic
cohomology" (Hochschild language). See chat bridge to that card.

## Log
- 2026-06-24 — Turing. Built the certificate, confirmed caps/climbs = Kolchin, killed κ-arithmetic-discrimination
  with 4 control rounds (magnitude, pole, smoothness, near-exponential). Recorded so no agent re-runs the σ_min probe.
