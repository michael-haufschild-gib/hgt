# HB completed balanced spin-two first live jet

- **ID:** HB-FIRST-LIVE-JET
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** HB-AMP-ORDER positive survivor
- **Statement:** At actual repeated Eisenstein leg `s=2` (`u=3/2`), the completed balanced spin-two projecting-leg jet of grade `2m` is nonzero for every Xi copy of support multiplicity `m`.

## Goal
Discharge HB angular source existence at the unique first possible amputation grade. Proof chain: nonzero grade-`2m` jet → literal radial/left-QNM coefficient is sole remaining factor → compare fixed coefficient with forced `-AIME` → critical-line selector/RH.

## Frontier
- **[CORPUS]** External Xi square has exact order `2m`; grade-`2m` vertex is nonzero iff Bochner/two-shifted-Xi side factor is nonzero.
- **[CORPUS]** Every Xi spectral point has `|Im z|<1/2`; `XiC` is zero-free for `|Im z|≥1/2`.
- **[LITERATURE]** Regularized triple-Eisenstein formulas, AdS4 Plebanski cubic vertex, AIME, and QNM bilinear residues exist separately; audit found no Xi-multiplicity/first-live-jet weld.

## Proof
At `u=3/2`, side Xi arguments are `z−3I` and `−z−3I`; `|Im z|<1/2` puts both below `Im=-1/2`, so both Xi factors are nonzero. Direct expansion gives Bochner coefficient `(4z²+1)(4z²+25)/32`; its roots `±I/2, ±5I/2` lie outside the strict Xi strip. The exact corpus grade-`2m` factorization then makes the jet nonzero.

## Hostile verdict
**SURVIVES PRELIMINARY ATTACK.** Signs were expanded from definitions; strict strip excludes boundary roots. **[PAPER-PROVED]**

## Lean
`iteratedDeriv_thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_actualRepeated_at_twiceMultiplicity_ne_zero`; full incidence iff explicit radial scale in `ThetaCuspHawkingBMCompletedBalancedSpinTwoFirstLiveJet.lean`. Build `13205/13205`; standard axioms only. **[LEAN-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]**
