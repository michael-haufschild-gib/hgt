# R2b — D–H defect-recurrence statistics (2026-07-03, partial through t≈4330; final at t=5002)

Engine: engine2.py parallel sweep (30 workers, dps 18), boxes σ ∈ (0.55, 1.2), height 2,
t ∈ [2, 5002). Raw: pod /root/mwm/sweep-par-0202-5002.out (+ serial chunks [2,202)).

## Pre-registered

Positive empirical defect density with structured (recurrent) gap statistics; early fail for
mechanism M2's residue if defects were isolated / of vanishing density.

## Observed (207 defects through t ≈ 4330)

- **Parity: every defect odd (winding +1)** across the whole range — 207/207. The R2a
  prediction extends over the full survey: the no-positivity family realizes exclusively
  simple (level-1) off-line defects at this resolution.
- **Density positive and ~linear in T**: counts per 500-height block:
  10, 17, 22, 31, 23, 24, 24, 33, 23 — after the initial ramp (t < 1000), a stationary
  ~23–33 per 500, i.e. off-line count ≈ T/20.
- **Gaps**: mean 20.6, median 18, min 2, max 90 — the large gaps (>50) all sit in the sparse
  initial range; from t ≈ 1000 the gaps are bounded by ~45 at sample scale. Histogram
  (10-wide bins): 0–10: 37, 10–20: 96, 20–30: 27, 30–40: 25, 40–50: 12, tail 5.

## Reading

- **Prediction confirmed** (encouragement): the FE-without-positivity object's defects recur
  robustly — positive density, bounded-gap phenomenology, no lone non-recurrent defect. In an
  FE family the ambient structure does force recurrence of off-line charge; what ζ needs from
  the Euler cut is not recurrence but EMPTINESS.
- **DH-test separation, quantified**: the Reduction (00-approach §5) kills recurring defects
  for ζ via Ingham's N(σ,T) = o(T); D–H's measured off-line count ≈ T/20 is exactly the ≫o(T)
  regime where no contradiction arises. The named failing step of the DH-test now carries a
  measured number.
- Check #8 (literature: known theorems on D–H off-line density) still to verify before any
  promoted claim; the ≈T/20 figure is empirical, one σ-band (0.55–1.2), one height (2).

## Final (survey complete, t = 5002)

- 2400 boxes over [202, 5002): 236 defect boxes = 235 × w=1 + 1 × w=2.
- The single w=2 box [4146,4148) was bisected at dps 30: TWO SIMPLE zeros
  (t ∈ [4146,4146.5) and [4147,4147.5), each w=1). No multiple zero anywhere.
- **Full-survey parity record: 237/237 off-line zeros simple (odd)** over t ≤ 5002
  (including the 4 zeros below t=202 from the serial chunks).
- Full-range count ≈ 237 defects / 5000 height ⟹ ≈ T/21, matching the partial read.
