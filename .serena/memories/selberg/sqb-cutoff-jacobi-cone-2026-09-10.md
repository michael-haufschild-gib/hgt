# SQB76: actual cutoff coefficient cone, verified

Active unbudgeted RH goal remains OPEN. Full chain: complete theta source → signed rank-seven cutoff norm nonnegative → all-rank positivity → critical-line criterion → RH. Neither rank seven, global compensation coefficient compatibility, nor all-rank propagation is proved. Frontier map is READ ONLY; universal ledger was not edited. No computations/numerics, Runpod, git, launch.sh, subagents, full/umbrella builds. All owned Lean/Lake and search sessions are terminal.

## Verified new source
`formal/GaloisForLFunctions/RHTower/ThetaCuspCutoffJacobiCone.lean`, wired once into RHTower.lean after ThetaCuspCenterMixedCutoffPolynomial.

For m_a=thetaCuspCenterMixedSignedJet a, 0<a<1/2, set b_j=HTGeometry.monicOrthoBeta m_a j (j=1..5). Existing actual rank-six positivity implies all five b_j>0. Vanishing odd moments makes all relevant Jacobi diagonal coefficients zero. Finite recurrence gives
Q(t)=t^6-S t^4+E t^2-F,
S=b1+b2+b3+b4+b5,
E=b1*b3+b1*b4+b2*b4+b1*b5+b2*b5+b3*b5,
F=b1*b3*b5.
All S,E,F>0. Q is even. Q(i*d)=-(d^6+S*d^4+E*d^2+F), and this positive symbol squared is >=(d^6+F)^2. This retains a positive geometric mixed-jet square; it is NOT an actual mixed-atom remainder bound.

Exact actual cutoff norm in raw derivatives d_n=iteratedDeriv n (thetaCuspCenterMixedDensity a) 0:
d12+2*S*d10+(S^2+2*E)*d8+2*(S*E+F)*d6+(E^2+2*S*F)*d4+2*E*F*d2+F^2*d0.
Its sign is OPEN.

Public theorem lines: eq_jacobi 132; coefficients_pos 143; even 160; eval_imaginary 174; square_lower 189; norm_eq_raw_jacobi 201.
Private helpers in ThetaCuspCutoffJacobiAlgebra prove moment-functional reflection invariance by polynomial induction, then alpha=0, then explicitly unroll finite Jacobi recurrence. Avoid reproving this.

## Validation
- Generic scratch /tmp/sqb76_cutoff_cone.lean passed.
- Actual scratch /tmp/sqb76_actual_cutoff.lean passed, five capstone axiom checks standard only.
- Final narrow leaf `lake build GaloisForLFunctions.RHTower.ThetaCuspCutoffJacobiCone` in /tmp/sqb76-cutoff-jacobi-leaf-audit PASSED (48s/2jobs), using actual source and existing symlinked compiled dependencies.
- `lake env lean /tmp/sqb76_final_audit.lean` from formal PASSED all SIX public theorem axioms: propext, Classical.choice, Quot.sound. No added axiom/holes/numeric certificates.
- Global formal lint PASSED /tmp/sqb76_formal_lint.txt. Initial lint hit concurrent other-agent FrobeniusGaloisObservation umbrella wiring, then the import appeared; rerun passed. No unrelated edit was made.
- No owned Lean processes remain. No full umbrella build performed.

## Analytical next target: exact atom pair operator
Documented in docs/drafts/pipeline/1-in-progress/sqb-native-spectral-source-comparison.md, section Cutoff coefficient cone and mixed-atom retention. Previous sentence about cutoff evenness being unformalized was updated.

For q=pi*n^2*exp(2x), r=pi*m^2*exp(2x), c=4qr, z(t)=q exp(2t)+r exp(-2t):
Phi_n(x+t)Phi_m(x-t)=4qr exp(x)*(c+9-6z(t))*exp(-z(t)).
z''=4z; (z')^2=4(z^2-c).
R_c P=(z^2-c)(P''-2P'+P)+z(P'-P).
D_t^2[exp(-z(t))*P(z(t))]=4exp(-z(t))*(R_c P)(z(t)).
Raw even pair jet 2j =4qr exp(x-q-r)*4^j*(R_c^j(c+9-6X))(q+r).
Exact cutoff-square pair expression is therefore this common positive prefactor times
(64 R_c^3+16 S R_c^2+4 E R_c+F)^2 (c+9-6X), evaluated q+r.
These pair identities are PAPER algebra only, not yet Lean declarations. No positivity of R_c or its iterates is asserted. Hard next step: retain positive geometric square and bound actual high-order remainder for actual coefficients after complete atom summation. Do not replace hard sign by new generic receivers or lower-order no-go results.

Analytical checks: pairwise even Hankel PSD is not valid as a general mechanism; cutoff cone is more restrictive. Positive leading rank-one alone cannot control lower-order terms. Raw pair derivative2 /common factor =4[(P0+12)*(q-r)^2-(q+r)*(P0+6)], P0=c+9-6(q+r)>0. High derivatives not shown nonnegative; no standalone low-order module was created.

## Searches / papers
SQB76 searches /tmp/sqb76_{inertia,determinant,highorder,parity,pairflow}_search.json all terminal and all result views inspected (declarations/candidate_lemmas/source_arguments/proof_ideas/ingredient_sets). Broad OR with all retrieval views, deep300s, no-refresh. Coverage partial/stale compiler (roughly 722k declarations; 43.8k compiler pending); some interrupted retrieval/deadline/broken-pipe stages. No absence claim. Relevant existing lemma X_mul_monicOrtho_below and monicOrthoBeta_pos_below verified in Lean. Generic positivity retrievals keep unmatched source/Gram/evolution premises.
Own broad recent arXiv terms screening and pinning. Read 2609.07326v1 Exact Cancellation of Horizon Modes in Kerr Ringdown: retain full frequency zero factor before near-horizon integral, no theta transfer. Read analytical core 2609.06730v1 A dot-product bound from separate growth-minimizing bases: product of independent minimizing subsets supports both growth operators; no source sign transfer. Card links both; neither imported as Lean premise.

## Lean pitfalls verified
Nat.even_or_odd (not unqualified). Polynomial.induction_on', monomial_comp, C_mul_X_pow_eq_monomial exist. comp_neg_X / coeff_comp_neg_X / comp_smul do not. Use mul_comp/add_comp/sub_comp/pow_comp/C_comp/X_comp and ring.
`0<monicOrthoBeta` mislexes (Matroid notation); space as `0 < monicOrthoBeta`.
When specializing numeric signed jet equalities, create hj 0..6 and norm_num at those hypotheses; do not rewrite numeric zero/two globally (dependent-instance motives fail).
I^6=-1 needs explicit I^6=(I^2)^3 and norm_num; norm_num alone left I^6.

Previous verified cost/gain state remains in mem:selberg/sqb-modular-barrier-cost-gain-2026-09-10. Do not rerun its builds.
