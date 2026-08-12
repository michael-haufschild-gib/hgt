# Mass-shifted all-contact arithmetic source + norm residue (2026-08-13)

Formalized module: formal/GaloisForLFunctions/RHTower/XiShiftedStrictFrontierAllContactArithmeticSource.lean
Umbrella: formal/GaloisForLFunctions/RHTower.lean
Report: docs/reports/mass-shifted-spectral-trace-route.md §9.3, equations 9.3.708–713
Card: docs/drafts/pipeline/3-formalized/mass-shifted-strict-frontier-finite-contact-arithmetic-capitalization.md

New knowledge:
1. Strict terminal frontier does NOT force odd contact. Even isolated singular contact can be terminal because failure set is non-PosDef, with positive-definite punctured sides.
2. Infinite local flatness is impossible. Every occupied physical strict frontier has finite first Padé contact d>0, lower defects zero, and (-1)^d δ_(2m+d)>0.
3. d=1 is exact negative first omitted remainder. Every d>=2 is exact admission-sensitive source-first bilinear completed arithmetic producer:
   A^sharp_bil(sqrt y; P X^(d-2),P)=(2m+d)δ_(2m+d), with alternating source sign positive.
4. Exact Schur factorization:
   det H_(m+1)(v)=det H_m(v)*N_m(v).
   Therefore moving admission contributes no hidden leading correction.
5. Exact all-order newborn norm residue:
   N_m(y+u)/u^d -> (-1)^d choose(2m+d,d) δ_(2m+d)>0.
6. False RH iff cofinal finite adaptive arithmetic-contact phase; this is phase equivalence, not RH proof.
7. Remaining global obstruction is cofinal contact-degree/source-price escape or failure of explicit finite prices to accumulate against nonintegrable Christoffel wall action. Next local step: quotient all-order norm residue by continuous positive wall numerator; next genuine core: exclude degree escape via cumulative price/action.

Key Lean theorems:
- xiShiftedStrictFrontier_finiteArithmeticContactLaw
- det_xiShiftedMomentHankelMatrix_succ_eq_head_mul_admissionNorm
- tendsto_div_pow_right_of_hasFPowerSeriesAt_of_coeff_zero_before
- tendsto_xiShiftedCanonicalAdmissionNorm_div_pow_at_firstPadeContact
- tendsto_xiShiftedStrictFrontierAdmissionNorm_div_pow_at_contact
- xiShiftedCofinalFiniteArithmeticContactPhase_of_not_riemannHypothesis
- riemannHypothesis_iff_not_xiShiftedCofinalFiniteArithmeticContactPhase

Verification:
- direct lake env lean passed
- targeted lake build module passed
- #print axioms: only propext, Classical.choice, Quot.sound
- scripts/formal_tools.py lint passed
- no stale Lean process
- no computations used

Novelty remains [NOVELTY UNVERIFIED]. Broad arXiv audit found classical Hankel determinant/product-norm, singular Padé, and Toda bridge theory but no shifted-Xi admission-selected rational–Gamma-minus-von-Mangoldt all-contact source law.