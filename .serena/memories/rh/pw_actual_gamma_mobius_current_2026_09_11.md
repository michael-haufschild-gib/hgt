# PW-B actual Gamma/Möbius current (2026-09-11)

Goal remains an unconditional closed Lean proof of RH via PW-B. RH is not proved; no source-forced fixed-grade balance or Xi occurrence is constructed. Proof chain: literal PW Borel partner imbalance -> positive Deninger Ward transmutation -> independently source-forced fixed-grade balance -> RH. Universal fixed-grade balance is still equivalent to RH.

Completed leaf: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusCurrent.lean` (namespace `RHTower`), importing the previous `ThetaCuspHawkingParikhWilczekReflectedSourceForcing`. Umbrella import wired beside that parent. All 15 public theorems passed scratch, direct leaf check, target-only final build, and axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. Formal lint passed. Index regenerated API/GAPS/OVERVIEW. Name collisions checked. No numerical experiments, full/umbrella builds or additional axioms. Owned Lean processes finished.

Definitions:
- `pwGammaRaySource y := (expShift (1/2) 0 (log y) : Complex)`; for y>0 equals sqrt(y)*exp(-y).
- `pwGammaMobiusPreimage x := sum mu(n)*Q(n*x)`.
- `pwGammaMobiusLogCurrent x := -sum mu(n)*log(n)*Q(n*x)`.
Zero-index coefficients vanish, so the auxiliary Q(0) is irrelevant.

Explicit tangent-bound proof: for c>0, `c*u-exp(u) <= c*log(c)-c`. At c=5/2, `|Q(y)| <= C/y^2`, C=exp((5/2)*log(5/2)-5/2)>0. This is enough for the literal source even though q(t)=exp(t/2-exp(t)) fails the old two-sided DeningerExpSchwartz class (proved in parent leaf).

Private shared two-variable majorant: b(0)=0 and sum |b(m)|/m^2 summable imply `b(m)*mu(n)*Q(m*n*x)` summable for x>0. Apply to unit weights on positive integers and to Lambda. Existing `deningerProductFibre_tsum`, `deningerMobiusDivisorSum` and `deningerVonMangoldtMoebiusDivisorSum` prove reconstruction and Euler connection. Separate bound using `Sieve.summable_log_div_sq` proves the full Mobius-log series converges.

Public outcomes:
- `pwGammaMobiusPreimage_halfDensity`: M(x)=sqrt(x)*sum mu(n)*sqrt(n)*exp(-n*x), x>0. This is NOT the ordinary Mobius-Laplace sum; retain sqrt(n).
- `pwGammaMobiusPreimage_summable`, `pwGammaMobiusEulerCurrent_summable`, `pwGammaMobiusLogCurrent_summable`.
- `pwGammaMobius_rightInverse`: deningerRaySum M x=Q(x) for x>0.
- `pwGammaMobiusPreimage_nontrivial`: exists x>0 with M(x)!=0.
- `pwGammaMobius_connection`: sum Lambda(m)*M(m*x)=E(x).
- closed capstone `pwGammaMobius_source_current_closed` packages nontriviality, reconstruction, both summabilities and the full identity without an RH premise.
- `pwGammaMobius_log_connection` and its summability variant.
- `pwGammaMobius_reflected_connection`: for F=M o exp and positive-gain T f=a*f(-t), the complete inverse-dilation current K(TF)(t)=a(t)*E(exp(-t)); `pwGammaMobius_reflected_current_summable` proves admission. This uses the actual Gamma source, unlike the parent result restricted to ExpSchwartz. It does not say outgoing J(TF) converges.

Critical scope: E is not asserted to vanish. This arithmetic current is NOT identified with the differential forcing of q or M, or with a physical operator/domain/Xi occurrence. No Mellin continuation is proved. The new result removes an actual source-admission gap but does not produce PW balance.

Files: stage-3 card `docs/drafts/pipeline/3-formalized/pw-b-gamma-mobius-current.md`; attack log `docs/drafts/pipeline/1-in-progress/pw-b-source-orientation-attack.md` iteration 8 and next-attack section; frontier PW-B and route-independent STATUS updated. Three deep searches (Gamma bound, arithmetic fibres, coercivity/kernel methods), with partial coverage, saved in `pw-b-gamma-current-searches.json`. Stored methods/ingredient sets inspected. Gapped pseudo-inverse requires unproved symmetry/kernel/coercivity; polynomial classification needs entire growth bounds, so neither is a Ward producer. Broad arXiv polymer/resetting/coercivity/pinning searches found July/August 2026 primary papers 2607.12482, 2607.19283, 2607.19732; hypotheses not identified with PW, no external theorem imported.

Scratch/logs `/tmp/pwb-gamma-current.lean`, `/tmp/pwb-gamma-current-axioms.lean`, `/tmp/pwb-gamma-current-{scratch,direct,build,axioms,lint,index}.txt`. Informational ring_nf hint remains but all checks pass. Mathlib `abs_moebius_le_one` has implicit n; use a typed `show |moebius n| <= 1 from abs_moebius_le_one`. Broad push_cast can rewrite real log casts into complex log; use Complex.norm_real and Real.norm_eq_abs to bound real coefficients. Explicit f/g arguments to Summable.mul_of_nonneg plus `set_option backward.isDefEq.respectTransparency false` avoid an elaboration timeout. `Summable.prod_factor`, `.prod`, `.tsum_prod`, `.tsum_eq_zero_add` verified in current toolchain.

Next mathematical attacks (paper deductions, NOT yet Lean theorems):
1. Inverse homogeneous fminus_z(u)=exp(-phi(u)+z*u) has full outgoing Lambda current summable at every complex z, not just prime-power decay. Put A=Re z+1/2, c=|A+2|+1, kappa=exp(t)/2. For n>=1, n^2*|fminus_z(t+log n)|=exp(A*t+(A+2)*log n-kappa*n+exp(-t)/(2*n)) <= exp(A*t+exp(-t)/2+c*log c-c-c*log kappa). Thus sum Lambda(n)/n^2 admits every shift. Formalize and do not transfer positive-connection forced uniqueness to this inverse connection. No closed-domain spectrum or Xi realization follows.
2. Actual-source second-end bound: summing Q's majorant should prove uniform |M(x)| <= B/x^2, B=C*sum 1/n^2. Inverse homogeneous modes grow faster than every inverse power as x->0, so this additional source-derived condition can restore uniqueness; matching full reflected forcing is still separate and missing.
3. More direct forcing test: use that uniform M bound to justify Z(J M)=J(Z M). Since Z M=Q and J M=E, get exact positive survivor `Z E=J Q`. RHS is strictly positive for every x>0 (Lambda>=0, Q>0 and a prime term>0). This would prove E is not identically zero without claiming individual-point positivity of E. The uniform bound, double-current interchange and positivity are still pending Lean audits, not claims of the completed leaf. A positive aggregate is not individual PW balance.
