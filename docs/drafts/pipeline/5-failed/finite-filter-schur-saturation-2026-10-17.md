# Finite-filter Schur saturation fails for nonzero compact sources

- **ID:** finite-filter-schur-saturation
- **Stage:** 5-failed
- **Type:** FALSIFIED (Lean); positive survivor and full capstone formalized
- **Source:** ../1-in-progress/hyperbolic-multiplier-lifting-2026-10-17.md
- **Statement tested:** A nonzero compact continuous source can saturate the
  finite hyperbolic filter's Cauchy--Schwarz price.

## Exact obstruction

Write q=(cosh(u)-mu)f, Q=||q||², A for the finite symmetric hyperbolic
filter, r=A-(kappa/R)f, H=||r||² and beta=<q,A>=<q,r>.
The saturation equation beta²=QH is impossible for f!=0.

Let M=sup support(f), d=log2, and L>=1 the constructed filter cutoff.
Choose u in support(f) with M-d<u. At v=u+Ld, all filter translates except
the outermost one vanish. Thus f(v)=0 but
A(v)=f(u)/(2cosh(Ld/2))!=0. No source-supported linear combination can
remove this escaped value. The argument permits arbitrary signs and disconnected support.

## Strongest positive survivor

The actual compact residual e=r-(beta/Q)q is orthogonal to f and q and obeys
E=||e||²=H-beta²/Q and Q E=QH-beta², including zero-source totalization.
The escaped value gives E>0 iff f!=0. This is a constructed positive energy,
not merely a renamed failure of equality.

The residual correction
g_res=Q E/(sqrt(QH)+beta)=sqrt(QH)-beta
is nonnegative and positive exactly for nonzero f. For every canonical odd F,
I_opt+R_plastic-2(log2)C_local+2(log2)g_res<=P(F).
The increment is strict exactly when the original input is not even.

## New insight and route boundary

The finite filter necessarily contains a component outside both source
directions. Its norm price is never attained by a nonzero compact source;
that lost energy has an exact positive correction in the plastic bound.
The finite-filter method survives and improves. Only nonzero saturation is retired.
No universal plastic positivity, uniform positive gap or global optimality follows.

## Proof status

- [x] Well-posed source-pure saturation question.
- [x] Dependency-closed paper proof in the owned master card; prior source
  rigidity supplies Q>0 for f!=0.
- [x] Positive survivor and full capstone audited in Lean.

Module: `formal/GaloisForLFunctions/BiScaleUncertainty/FiniteFilterSchurResidual.lean`.
Key declarations: `sourceFilter_escape_iff`, `schurResidualEnergy_pos_iff`,
`schur_defect_identity`, `strict_schur_iff`, `schurResidualGain_eq`,
`odd_plastic_residual_gain_certificate` in namespace `FiniteFilterSchurResidual`.
Local corpus audit found no predecessor; no external novelty claim.

Final actual-source audit6502 and all13 public theorem axiom audits15226 exited0
without warnings. Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
Source SHA256 `6f119308bd255012affd90d0eeaac906b40a35147aec5298f5cc23a7cac90119`.
Umbrella wired; all17 public declarations indexed. Global lint independently
reports unrelated modules and concurrent generated drift; exact snapshot is on
the master card. No repository-wide clean gate or external priority is claimed.
