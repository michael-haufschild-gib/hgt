# Return-shell replica coarea frontier (2026-08-07)

User target: quenched incidence-normalized coarea mass after return removal, retaining source fibre sheets and occupied endpoint image.

Conjecturing loop:
- C0 raw coarea formula: circular; disintegration preserves multiplicity but gives no upper bound.
- C1 unweighted occupied Veronese projection: already proved, loses approximate-return residual norm.
- C2 one global residual radius: valid but too lossy; one transverse target forces radius 1.
- C3 survivor, proved: finite residual-norm shells. For shell b, target residuals satisfy ||z||^2 <= rho_b, occupied replica span S_(b,r)=span{z^tensor r}, q_(b,r)(x)=||Proj_S psi(x)^tensor r||^2, Q_r=sum_b rho_b^r q_(b,r). Complete capture E_a obeys pointwise 1_E a^r <= Q_r and mu(E_a) <= a^(-r) integral Q_r dmu. Source integration retains all fibre sheets; occupied spans erase duplicate circuit labels; zero residuals cost zero.

Static-Choi exact bridge: for normalized target phi and normalized orbit anchor Phi_H(u), residual phi_perp=phi-<Phi_H(u),phi> Phi_H(u) satisfies ||phi_perp||^2 = 1-|<Phi_H(u),phi>|^2.

Lean:
- HTGeometry/ReplicaReturnShellCoareaIncidenceLaw.lean
- RHTower/StaticChoiReturnShellCoareaIncidenceLaw.lean
- card docs/drafts/pipeline/3-formalized/return-shell-replica-coarea-incidence-law.md
Direct lake env lean passed for both; final capstone module build passed; capstone axiom audit only propext, Classical.choice, Quot.sound; no forbidden tokens.

Honest remaining core: genuinely transverse rho=1 occupied shells. Need ordinary fixed-q Gaussian static local-Hamiltonian growing-replica decay for radius-weighted occupied-shell pair actions, beating occupied Hilbert number without circuit-label union. Brown–Susskind not closed.

Repo audit caveat: both modules wired into umbrellas, imported modules build, but final HTGeometry aggregation currently fails on unrelated duplicate coverBase; final RHTower aggregation fails on unrelated duplicate deriv_zero_of_even. Global lint red only for unrelated concurrently added unwired modules.

Novelty label: APPLICATION NOVELTY UNVERIFIED. Generic ingredients classical; assembled return-shell/occupied-Veronese/quenched-incidence law not found in audited literature.