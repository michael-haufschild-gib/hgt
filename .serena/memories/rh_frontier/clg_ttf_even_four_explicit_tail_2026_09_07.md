# CLG/TTF: explicit complete-source even rank-four outer margin

ACTIVE GOAL: unconditional RH proof/falsification. RH remains UNPROVED; do not mark complete or blocked merely because difficult. No subagents authorized/spawned. Goal turn delivered PROGRESS: explicit outer endpoint, replacing existential R for canonical/rational even-four family.

## Closed exact results

q=π exp(2x), φ=first theta atom, j_n=full reflection jets, m_k=(-1)^k j_(2k). Actual head A=[m_(i+j)]_(i,j<3) is already PD for all x≥0. S=m6-bᵀA⁻¹b, G=3Φ²+2xΦΦ′. Canonical C* already satisfies 1e12<C*<3e12.

New six checked modules:
- formal/GaloisForLFunctions/HTGeometry/HankelFourPerturbation.lean (namespace GaloisForLFunctions.HTGeometry): hankelFourDet_error_le gives absolute determinant error≤96M³δ if both seven-entry Hankel data bounded by M≥0 and entry errors by δ≥0. Symbolic quartic telescoping; no computational premises.
- HTGeometry/FirstAtomEvenTailReserve.lean (namespace HTGeometry): exact firstAtomEvenTailProfile Fin7 includes new p6 numerator (43599790080, -239798845440, 886529064960, -1280916848640, 603009318912, -75547148288, 1408303104, -491520) over D=(4-6u)^2. All p0..5 reuse exact old profiles. Balanced entries p_k/32^k - [k=6]*1e8/32^6. firstAtomEvenTailBalancedDet_lower ≥1/10000 on 0≤u≤1/30; exact common numerator degree14, positive expansion of 10000*N-32^12D^4 in z=1-30u. firstAtomEvenTailBalanced_abs_le ≤4.
- RHTower/ThetaCuspEvenFourEffectiveErrors.lean: pow_six_mul_regimeOneLikelihoodScale_le_of_thirty_le gives q6ε≤3/1e29. abs_thetaCuspNativeScaledEvenJet_sub_first_le_ten_neg_ten_six gives errors≤1e-10 for all k≤6 on q≥30, retaining complete source.
- RHTower/ThetaCuspEvenFourEffectiveReserve.lean: all seven literal first-atom normalized jets equal rational profiles; actual balanced entries same reserve; thetaCuspNativeEvenTailBalancedDet_lower ≥1/20000 via M=5 perturbation.
- RHTower/ThetaCuspEvenFourEffectiveSchur.lean: thetaCuspNativeEvenTailBalancedDet_eq_reserved_ratio is exact (detE0-1e8 φ²q6 detA)/(32^12 φ8 q12). Actual detE0=detA*S, detA>0; thetaCuspNativeEvenFourSchur_effective_normalized_lower proves S/(φ²q6)>1e8 for q≥30.
- RHTower/ThetaCuspEvenFourExplicitTail.lean: full G/(φ²q6)≥-2/30^4 from existing q5 correction bound. thetaCuspNativeEvenFourCompensated_effective_normalized_lower gives (S+C G)/(φ²q6)>9e7 for0≤C≤3e12,q≥30. Native PD on q≥30, hence x≥6/5 using existing x≥6/5⇒q≥30 (do NOT reverse this implication). Canonical actual C* tail covered. Weighted actual matrix PD for all a>0,r≥12/5. Canonical capstone thetaCuspCenterCorrectedEvenFourCanonical_posDef_on_explicit_tail. exists_thetaCuspEvenCompensation_rationalFamily_explicit_outer_gap gives ∃δ>0,δ≤6/5 with every rational-band C native PD on x≥0 outside [δ,6/5].

## What remains

Inner threshold δ remains existential. Need quantitative small-center even-four comparison and positive compact interior comparison below6/5, or direct actual rank-seven successor integral sign. Previous full two-atom derivative/reflected/correction errors through12 remain available on x≥8/95; finite lower quadratic expression not proved positive throughout interior. Full rank-seven/all-order positivity and RH remain OPEN. No implication from fixed rank to all orders.

## Verification / discipline

All six checked in /tmp scratch using ONE foreground lake env lean process at a time; only needed oleans emitted; checked source bytes copied exactly; imports wired uniquely into HTGeometry/RHTower umbrellas. NO full builds, umbrella builds, cascade builds, or background Lean processes. Final six new-only axiom capstones audited ONCE: generic perturbation, exact first reserve, seven complete errors, actual Schur margin, canonical weighted tail, explicit rational-family gap. Only propext, Classical.choice, Quot.sound. Do not repeat these old audits.

Single scripts/formal_tools.py lint run failed with exactly one unrelated repository-wide error: owned module RHTower.MobiusDivisorTwoChannelPrimeBlocks unreachable from its theorem-area umbrella. Did not edit that unrelated module/import. All SIX new modules uniquely wired and checked. Paper records this limitation; no global lint pass claimed. Targeted diff whitespace check passes after removing surplus trailing blank from touched STATUS. No Lean processes running; owned scratch prefix /tmp/clg_even_outer* is to be removed at final cleanup, preserving corpus and emitted oleans.

## Docs

New dependency-closed paper: docs/drafts/pipeline/3-formalized/clg-ttf-even-four-explicit-tail.md, including exact positive polynomial coefficient certificate, actual cofactor normalization, full error and correction. Updated active card clg-ttf-center-integration-compensation.md, current frontier CLG section, STATUS route-independent normalization/interior requirements, and three related formalized cards to link explicit endpoint. Frontier remains current state, no diary. 

Next work must reuse checked oleans, avoid full/umbrella builds, audit only newly created capstones, clean owned scratch/processes. Corpus research before new code. Prior memory mem:rh_frontier/clg_ttf_even_four_complete_error_twelve_2026_09_07 has complete two-atom error APIs; mem:rh_frontier/clg_ttf_even_compensation_rational_band_2026_09_07 has exact coefficient and seam recurrence.