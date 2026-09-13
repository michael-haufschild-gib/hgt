# Frozen family C1: arithmetic-specificity controls for source interactions

Question: is the mixed-deformation collision effect specific to the zeta completion, or does the same constrained construction show comparable effects for primitive completed Dirichlet L-functions? This changes the object and tests transfer; it does not repeat the failed affine scalar-mean scan.

Objects: real primitive characters chi4=(0,1,0,-1), chi5=(0,1,-1,-1,1). Standard completion Fq(t)=(q/pi)^((s+a)/2)*Gamma((s+a)/2)*L(s,chi), s=1/2+i*t, parity a=1 for q4 and a=0 for q5. Root number is +1 for both; verify Gauss sums and functional equation before root experiments. The corpus conductor-four carrier differs from this normalization by a constant sqrt(q), which does not change zeros or the normalized moment-annihilator coefficients. No HB physics transfers to these controls. The positivity of a source multiplier does not establish positivity of an unidentified Dirichlet Fourier kernel.

Direct evaluation uses L=q^(-s)*sum chi(r)*HurwitzZeta(s,r/q), with analytically differentiated factors. DLMF 25.15.3, 25.15.5 and 25.15.6 were opened; local SymmetricShiftDirichletExample and DirichletCharacterTwoAdicPrimitive were inspected. Character tables, parity and finite multiplicativity checks recorded. No new formal theorem asserted for these controls.

Multiple experiments: both conductors; four signed axes and four diagonal directions; additive versus moment-compensated product for diagonals; first four gaps between critical-line roots located by a quarter-step sign scan on [0,45]. These are numerically located roots, not a certified enumeration or GRH claim. Recompute moment annihilators separately for each completed carrier using the same frequency sets and two constraints as D1. Record all solver failures and any root leaving its seed gap. Compare smallest located positive-lambda collisions and mixed/additive ratios by direction, alongside zeta D1's first-four-gap results.

Prediction attempt: evenness and two constrained moments alone cannot ensure zero confinement, already known. No theorem fixes these quantitative threshold ratios or responsible gaps across these three arithmetic sources. A similar response in controls weakens any claim of zeta-specific interaction; different behavior is a candidate needing independent validation, not proof of arithmetic specificity.

Method transfer: discriminant viewpoint from arXiv:2605.27342v1, finite-source/coupling caution from arXiv:2606.14486v1. Only mathematical setup and control design transferred; no mechanical/electromagnetic theorem used.

Budget: preparation and all root searches share 285 seconds plus <=10 cleanup. Pilot first gap, then gaps 2–4 if it fits; 14 workers, one BLAS thread. Initial 50-digit calculations with 70-digit coefficients. Validate any noteworthy difference at 100/160 digits and independent formulas before facts-ledger admission.
