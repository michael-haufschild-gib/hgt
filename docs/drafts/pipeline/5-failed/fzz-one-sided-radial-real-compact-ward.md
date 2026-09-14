# FZZ one-sided radial/real-compact Ward route

- **ID:** fzz-one-sided-radial-real-compact-ward
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `FZZCigarMarkedRadialReplicaResponse`; Halder--Jafferis prescription
- **Statement:** A real compact Hessian can cancel the physical one-sided radial mixed receiver.

## Goal

Test subroute
`one-sided radial + real compact Ward zero → p=0 → passivity → Mellin completeness → RH`.

## No-go closure

- **Exact killing theorem/mechanism:** `fzzOneSidedRadialRealCompactWardRouteKilled`; radial derivative
  has strictly negative imaginary part at every momentum, while every real compact correction has zero imaginary part.
- **Strongest positive survivor:** cancellation forces strictly positive compact imaginary response,
  `compact_im_pos_of_fzzOneSidedRadialMixedResponse_add_eq_zero`.
- **New insight:** reflected pairing erases precisely the phase obstruction present in the physical prescription.
- **Status:** Lean theorem dependency-closed; audit details on formalized card.

## Scope

Kills every real-compact factorization, including the full depth-one annular Hessian. Genuinely complex
all-depth source-fixed phase completion remains live.
