# Four Stage-2 card formalization, 2026-09-02 (updated)

Active /goal remains incomplete. Do not promote any of the four cards yet.

Differential variational card advanced materially:
- `DifferentialVariationalOreModule.lean` proves `variationalOreModule_finite` and `exists_fin_basis_variationalOreModule`; finite differential generation now supplies an actual finite DiffOp basis with no supplied rank/basis.
- Canonical transition matrices and canonical semilinear matrices are units over arbitrary rings; exact row-coordinate basis law is `A_new * B = σ(B) * A_old`, equivalently `A_new = σ(B) A_old B⁻¹`.
- Completed embedding commutes with coefficient transport.
- `DifferentialFieldAut C K` bundles base-fixing derivation-preserving automorphisms as a group (chronological multiplication).
- Canonical operator/completed matrix units satisfy identity and cocycle laws.
- Projective completed-lattice actions are genuine equivalences, compose functorially, and actions in different bases are conjugate by completed transition units.
- Finite differential generation supplies completed matrix unit and operator-row-lattice degree-balance existentially.
- Direct checks and targeted leaf builds passed. All new declarations axiom-audited with only propext, Classical.choice, Quot.sound (some bundle declarations use fewer).
- Card docs updated truthfully. Remaining exact gap: completed-building Cartan decomposition/apartment coverage, relative position/metric and comparison to operator invariants, CAT(0) completeness/semisimplicity/no parabolic, boundary flags, free-field reconstruction. Stage remains 2.

Other three cards remain at prior frontiers:
- centralizer: exact all-energy atom exclusion needs noncommutative inner-rank/Strong-Atiyah bridge.
- cascade: compatible nested height-one Wiman place/branch flag plus place-specific RatIn/response bounds.
- Schanuel: projective compactification/normalization plus scheme analytification/complex-point path production.

Important workflow: always run `scripts/formal_tools.py research` before Lean corpus work; no rg for Lean corpus. Use foreground `lake env lean`; targeted leaf `lake build` only; no umbrella/full builds. Preserve dirty shared worktree. A concurrent external commit b73ba599 included the generic semilinear matrix/compatibility files during this turn; remaining visible worktree changes are the Ore module and differential card.