# Route R: cofinite Cartier wall trace / complete-jet horizon (2026-08-08)

Paper theorem:
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/burnol/burnol-cofinite-cartier-wall-trace-horizon.md`

Status: Stage 2 paper-proved, source-pure, novelty unverified, NOT RH. Lean intentionally untouched during HTGeometry/RHTower refactor.

For `C_p(s)=s^2(s-1)/(2(p^s-1))` and reflected `C_p^vee(s)=C_p(1-s)`:

- zero wall:
  `-2 log p * d/ds[C_p(s)u_p]|_{s=0}=u_p`;
  `2 log p * d/ds[C_p^vee(s)u_p]|_{s=1}=u_p`.
- nonzero dilation pole `lambda_{p,k}=2 pi i k/log p`:
  normalized residues in each orientation recover exactly `u_p`.
- for `rho=sigma+it`, forward cofinite pole radius tends exactly `sigma`; reflected tends `1-sigma`.
- diagonal maps into full maximal compact-open `ell2`-valued germ spaces in either orientation, and their joint product, are continuous injective with nonclosed range. Standard coordinates `e_p` map to zero in every compact-open seminorm.
- adjoining normalized wall derivative/residue trace supplies an explicit coefficientwise left inverse and closed graph topology.
- horizon gap is `2 sigma-1`; existing Route R transgression becomes
  `E_{1/2}(U_rho f0)-E_{1/2}(f0) = (h_+(rho)-h_-(rho)) J_rho`.

Conjecture loop outcomes:
1 finite jets fail;
2 complete compact-open germ fails;
3 both orientations jointly fail;
4 FE reflection changes fibres, so same-fibre radius equality would launder RH;
5 singular wall trace exists and is exact;
6 equality of normalized traces holds for all coefficient fields and does NOT sign physical quadrature;
7 horizon gap is detector, not producer.

Exact remaining producer: construct pre-divisor Stokes boundary form on this singular trace graph and prove its reflection-odd zero-wall marginal on actual zero-divided Burnol section is nonpositive; existing landing identifies it with `J_rho <= 0`. Any theorem factoring only through completed L2 vectors or ordinary/complete interior analytic jets is categorically insufficient.

Related memories: `mem:route_r/burnol_all_prime_hilbert_cartier_jet_wall_2026_08_08`, `mem:route_r/general_reciprocal_seed_landing_2026_08_07`.
