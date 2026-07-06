# Incidence Mirror Positive Real Orientation Reversal

- **ID:** incidence-mirror-positive-real-orientation-reversal
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../rh-monodromy-weight-mismatch/107-incidence-carrier.md
- **Statement:** For an FE-paired incidence carrier whose mirror constant `ε'/ε` is positive real, the reciprocal mirror `z ↦ (ε'/ε)/z` reverses the sign of the imaginary orientation away from the real locus.

## Goal

Separate the FE mirror datum from the endpoint-agreement datum required by the band-edge parity theorem. The mirror gives an opposite-edge orientation rule; it does not by itself prove same-edge endpoint agreement.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, doc 107 endpoint-orientation question
- [x] 1 → 2  fully-proven: elementary complex reciprocal algebra plus the banked `incidence_mirror`
- [x] 2 → 3  formalized: Lean theorems `RHTower.im_real_div_mul_im_neg` and `RHTower.incidence_mirror_im_product_neg_of_real_pos`; `lake build GaloisForLFunctions.RHTower` green; `/tmp` axiom check at project baseline
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Compute `Im((lam : ℂ)/z) = -lam * Im z / normSq z`. For `lam > 0` and `z` nonzero/nonreal, the product of the source and mirrored imaginary parts is negative. Composing this identity with `incidence_mirror` gives the FE-paired incidence result.

## Log

- 2026-07-06 — formalized in `formal/GaloisForLFunctions/RHTower/IncidenceMirrorOrientation.lean`; umbrella import and generated API/overview updated.
