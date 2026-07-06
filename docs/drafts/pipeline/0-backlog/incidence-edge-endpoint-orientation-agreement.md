# Incidence Edge Endpoint Orientation Agreement

- **ID:** incidence-edge-endpoint-orientation-agreement
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../rh-monodromy-weight-mismatch/107-incidence-carrier.md
- **Statement:** [CONJECTURE] On the target lateral incidence edge, the two endpoint values of `Im ι` have the same sign, supplying the endpoint-agreement hypothesis of `RHTower.exists_incidence_edge_events_fluxPaired`.

## Goal

Close the last boundary datum left by the forced band-edge parity route. The theorem would turn the parity criterion and forced-event count into paired flux without carrying endpoint agreement as an external hypothesis.

## Gates

- [ ] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, axiom check at project baseline
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Do not use the positive-real reciprocal FE mirror as the proof: `RHTower.incidence_mirror_im_product_neg_of_real_pos` proves that this mirror reverses orientation across `s ↦ 1-s`. The needed datum is same-edge agreement, so it must come from a box-level orientation theorem, a stronger boundary transport statement, or a replacement of the endpoint hypothesis by a global edge-pairing argument.

## Log

- 2026-07-06 — opened after `RHTower.EdgeEventParity` reduced pairing to endpoint agreement and `RHTower.IncidenceMirrorOrientation` proved the positive-real mirror gives opposite-edge sign reversal instead.
