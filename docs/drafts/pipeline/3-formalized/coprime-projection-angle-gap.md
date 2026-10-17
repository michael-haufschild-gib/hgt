# Sharp angle gap for arithmetic tent projections

- **ID:** coprime-projection-angle-gap
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Exact product and commutator norms, norm-attaining velocities,
  and alternating-projection errors are classified by arithmetic tent adjacency.

For spacings m,n≥2, let P_m,P_n be the actual infinite tent projections and
R=P_lcm(m,n). Proved sharp laws for gcd(m,n)=1:

    ‖P_m P_n − R‖ = 1/2       if m,n≥3,
    ‖P_m P_n − R‖ = 1/√2      if min(m,n)=2,
    ‖P_m P_n − P_n P_m‖ = √3/4 if m,n≥3,
    ‖P_m P_n − P_n P_m‖ = 1/2  if min(m,n)=2.

For gcd(m,n)≥2, package 10 supplies zero for both differences. Both norm
classifiers, including this zero case, are formalized unconditionally.

Mechanism: remove coincident centers. Cross-normalized-tent pairings
are −1/2 at adjacent centers. Spacings at least three give isolated
edges; spacing two gives two-edge stars. Exact analysis coefficients prove each
projection action. The actual convergent series extends these to T²=cT for
T=P_mP_n−R, with c=0, 1/4, or 1/2. The C*-identity gives both exact norms and
nonzero attaining velocities. Every k≥1 satisfies (P_mP_n)^k−R=c^(k−1)T
and squared error norm c^(2k−1). No sampled matrix or admitted decomposition.

Corpus audit: `coprime tent projection principal angle commutator operator norm
adjacent star`, hybrid search, 60-second budget, all 20 candidate lemmas and all
20 source arguments inspected. Hits include package 9 and current package 10
source declarations, generic Gram identities and unrelated collar results;
no exact coprime angle or operator-norm classification found. No partial stages
or errors. Coverage snapshot older than current index, semantic coverage
unmeasured, background refresh incomplete. Current source hits alone are not
certification evidence. Check classical two-subspace theory and fresh corpus
coverage before writing a paper proof or Lean.

This is a quantitative successor to arithmetic commutation, not a claim about
unitary affine representations or closed SourceGraph operators.

Completed plan: (1) prove the arithmetic block classification and exact norm laws
on paper; (2) formalize single/two-neighbor projection actions and the reduced
product polynomial; (3) derive both unconditional squared-norm classifiers and
the alternating-product law; (4) serial leaf, axiom, signature, import/index and
lint audits. Four leaves, 45 public declarations, twelve main signatures.
Certified count is 11/100; this entire package counts once.

Fresh query `coprime projection angle norm squared product adjacent center`
returned all 20 candidate lemmas and 20 source arguments, inspected. Current
projection classifier and generic Gram tools found, no angle classifier. Search
was partial without execution errors; refresh incomplete and semantic coverage
not supplied. Primary alternating-projection source checked: Badea–Grivaux–Müller,
https://users.math.cas.cz/~muller/BGM_cras.pdf. Classical angle theory is parent
theory, not an external novelty claim. The arithmetic constants follow from
the actual tent geometry.

The arithmetic constants are now proved in
`docs/reports/BiScaleUncertainty/CoprimeProjectionAngleGap.md` and four Lean
leaves: `CoprimeProjectionNeighbors`, `CoprimeProjectionAnglePolynomial`,
`CoprimeProjectionAngleNorm`, `CoprimeAlternatingProjectionRate`.
All final direct checks and the complete public-declaration axiom audit pass
without diagnostics; only standard axioms. All 45 generated API entries checked
at current source lines, all imports unique, all compiled outputs current.
Repository-wide lint limitations are recorded in the fact ledger.

The relocated field README remains read-only. No numerical experiment, added
axiom, unproved analytic premise, heartbeat increase, full or umbrella build.
Next conjecture: `../0-backlog/two-grid-coprime-trace-extension.md`; actual
joint interpolation and sharp Dirichlet stability remain unproved and uncounted.
