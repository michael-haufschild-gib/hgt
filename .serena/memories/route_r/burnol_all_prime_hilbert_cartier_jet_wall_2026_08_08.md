# Route R: all-prime Burnol Hilbert Cartier jet wall (2026-08-08)

Paper theorem: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/burnol/burnol-all-prime-window-hilbert-cartier-jet-wall.md`.

For each prime p, let G_p be Burnol co-Poisson vector from seed x^-1 1_[p^-1,1], and A_p=1/(p log p). Exact bounds:
2(p-1)^2/p <= ||G_p||_2^2 <= 8p.
Therefore X=(A_p G_p)_p is an honest vector in the all-prime Hilbert direct sum.

At Xi zero rho of multiplicity m, finite multiplicity-divided Mellin jets of X are truncations of
U_{rho,p}=A_p c_rho/C_p(rho),
C_p(w)=w^2(w-1)/(2(p^w-1)).
Equivalent:
sup over finite P of sum_{p in P}|U_{rho,p}|^2 < infinity
<=> U_rho in ell2
<=> V_rho=(A_p c_rho) in ran(diag C_p(rho))
<=> Re rho <= 1/2.
The diagonal completion is bounded, injective, compact, dense nonclosed range; inverse is closed on its range.

Correction to prior card: ordinary ell2 valuation-range landing is false. Unique potential Q_p=-(p+1)/(p log^2 p) is not ell2, though A=DQ is ell2 and is in closure of range. Do not invoke ordinary closed range.

New reciprocal Stokes source:
nu_p=(p delta_p-delta_1)/(p-1), Mellin multiplier m_p(w)=(p^(1-w)-1)/(p-1).
Sewn factor S_p(w)=(p^w-1)(p^(1-w)-1)/(p-1) is reflection symmetric and |S_p(w)|<=6 on 0<=Re w<=1. Thus Y_{rho,p}=m_p(rho)U_{rho,p} is unconditionally ell2 throughout strip. Sewing is coordinatewise nonzero but diag(m_p(rho)) is compact with dense nonclosed range. Exact unsewing wall:
Y_rho in Dom(diag(m_p(rho))^-1) <=> Re rho<=1/2.

Remaining RH-bearing producer:
uniform all-prime Cartier jet estimate for this fixed source X at every Xi divisor, equivalently source-derived admission of Y_rho to domain of fixed-physical unsewing. This excludes right-half zeros; FE symmetry closes endpoint. Not proved.

Lean was read-only; no Lean files or builds due ongoing RHTower->HTGeometry refactor.