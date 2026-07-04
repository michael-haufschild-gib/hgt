# 47 — (BVAL) Refuted; the Sweep Cascade: the Marginal Term as Resolvent

**Register: SEARCH** (task #130). Certifications: `bval_scan.py` (P-V1
pre-registered → FAIL, fail-branch fired) + the winding/refine check at both
violation sites.

## 1. (BVAL) is false — background pairs are real and can be mid-band deep

The direct scan of the under-resolved background Φ_{N−1} on p-central stretches
found valleys 40–80× below the (BVAL) threshold, and BOTH are genuine off-line
zeros of the background:

- Φ₂₁ has an off-line zero at 0.5156 + 3148.61i (η = 0.016) in interval 22's
  center;
- **Φ₃₄ has a MID-BAND pair at 0.5976 + 7802.42i (η = 0.098)** in interval 35's
  center — far from every term's resonance (its own marginal beat ≈ 10 rad).

So: under-resolved carriers are NOT rigid; deep valleys are not rare; nothing
"holds" Φ₃₄'s pair — pairs of unmatched carriers exist freely. Doc 46 §6's
reduction survives, but its irreducible statement must be re-aimed.

## 2. The measured inversion: the full object is SWEPT clean at both sites

At both sites the matched object Φ_N has winding 0 in the same box: **adding
the marginal term killed the background's pair** (2/2). Combined with the film
(doc 45: the same term CREATES pairs at its resonance) and the reach law
(doc 46 §5: reach ≥ η at every matched-object pair):

> **(SWEEP) [CONJECTURE, the re-cut mechanism]:** each term n, entering with
> rotating phase, sweeps away the off-line pairs left by the under-resolved
> predecessor throughout its interval — EXCEPT in its resonance window
> (|p| ≲ 0.19), where its phase is frozen and it fails to sweep or actively
> creates. Matched-object cleanliness at p-central is not valley-rarity: it is
> sweeping success.

The p-clustering of the 76-event census, the film'screation/repulsion asymmetry,
the σ(p) noise (the push's SIGN is configurational; its net effect on an
EXISTING pair is destruction — a second-order statement invisible to Δmingap),
and the (BVAL) refutation are all consistent with (SWEEP) and with nothing
simpler that we tested.

## 3. The tower form — where this now lives

At fixed height t, the family k ↦ Φ_k (k = 1…N(t)) is a TOWER: each level adds
one term, kills predecessors' pairs (measured), creates its own near resonance
(measured). The danger form is sharp:

> **(SWEEP-margin) [the new irreducible]:** every pair of Φ_{k−1} lies within
> the reach of the entering term P_k — no pair survives a sweep — uniformly in
> the tower at p-central heights. Measured margin at the tightest matched pair:
> reach/η = 1.10; the background pair at 7802 (η = 0.098) was swept by a term
> with measured reach ≈ 0.15–0.2.

A pair deeper than the sweeping reach (η_B > reach ~ 2w·k^{−1/2}) would ride
the tower to the matched object and beat the census. None occurred in 14,000
height units. (SWEEP-margin) is a perturbation statement about ONE explicit
term acting on an explicit pair — the collision analysis of doc 45 §3, run in
reverse, with the (m,r)-frame and doc 25's tracking as the native tools. The
weld reading is now literal: the object at height t is BUILT by a k-indexed
cascade of sweep-and-create events — the constraint (FE symmetrization at each
level) does the sweeping; RH_2-for-the-family is the statement that the
cascade never strands a pair away from the active resonance.

## 4. Openings

1. Tower census at one height band: track pairs of Φ_k for k = 5…N at fixed
   t-window (cheap: the objects share terms) — measures creation/survival
   statistics along the cascade directly; decides whether multi-sweep
   survivors ever occur.
2. (SWEEP-margin) write-out: perturbed-pair collision condition — when does
   z(ε) with B(z) + εP(z) = 0 land on the line by ε = 1? Explicit in
   (η_B, |P/B′|, relative phase); the film provides both signs of the answer.
3. The reach lower bound: reach = |P_k|/(2η|H|) — the SAME η²|H| object again;
   a proof of reach ≥ η at p-central = (MOAT-shallow)'s technology applied to
   the background pair + the term's line-modulus 2|γ|k^{−1/2}|cos φ| with the
   rotating-phase advantage.

## 5. Out-of-sample census [20000, 30000): the phase window replicates at 0.194

`census_decade.py` (archive `census2.out`): 11 new mid-band survivors in 10,000
height units (rate ≈ 1/900). **P-H1 FAILS AS REGISTERED — by 8%**: max
|p − nearest int| = 0.194 vs the registered 0.18; the in-sample cutoff (0.19)
essentially replicated, my registered number was too tight. The clustering
itself is decisive out-of-sample: 11/11 survivors within 0.194 of a transition
(uniform probability ≈ 3·10⁻⁵). **P-H2 PASS**: the deepest new survivor
(η = 0.133) sits at |p − int| = 0.004 — depth-tightness confirmed. The (SWEEP)
window is stable in T: p* ≈ 0.19 at T ~ 10³ and at T ~ 3·10⁴ — a
scale-invariant constant of the cascade, as a frozen-phase window should be
(Δφ* = 2πp*² ≈ 0.23 rad).
