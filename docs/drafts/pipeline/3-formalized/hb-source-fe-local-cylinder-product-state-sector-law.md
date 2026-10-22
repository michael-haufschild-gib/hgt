# HB source-FE local-cylinder product-state sector law

- **ID:** HC84
- **Stage:** 3-formalized
- **Type:** THEOREM / EXTENDED-SECTOR LOCAL-STATE CLASSIFICATION + ROUTE ENDPOINT
- **Source:** read-only `rh-current-frontier-map.md` · HC83 orthogonality catastrophe

## Goal

Attack the hardest survivor after HC83. Off-wall normalized cutoff vacua have no reference-Fock
norm limit, but their vector states may still possess a consistent limit on every finite cylinder
of diagonal occupation observables. Construct that state exactly and decide whether the disjoint
sector hides the source-FE wall defect from local observations.

For `r : ℂ`, cutoff `N`, cylinder size `K`, and arbitrary real reporter `f` on subsets of
`range K`, define the cutoff Born expectation by summing the squared coefficients of HC83's
`finitePairFockVacuum r N`, with `f` evaluated on the occupied modes below `K`. Prove that for
`K ≤ N` this expectation is independent of `N` and equals the product Bernoulli expectation with

`p(r) = ‖r‖² / (1 + ‖r‖²)`.

Thus the off-wall vectors escape globally while their full finite-cylinder state stabilizes
exactly. Prove also that the one-mode occupation is `p(r)` and vanishes exactly when `r=0`.
Specialize to the literal Xi source-FE ratio: the extended local state is vacuum on one/every mode
exactly on the critical wall; universally this is RH and transfers to route receivers.

## Gates

- [x] 0 → 1 in-progress: corpus audit; exact conjecture frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and bounded primary-literature audit
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical/physical review and broader novelty search

## Corpus audit

- `[CORPUS]` HC83 supplies one common `BosonicFock Nat`, exact subset coefficients, unit norm,
  coefficientwise escape, and Cauchy iff-zero classification.
- `[CORPUS]` `ConstraintFrameRelativity.BernoulliBooleanGibbs` supplies the abstract finite product
  Bernoulli weight, normalization, product-observable law, and occupation marginals.
- `[CORPUS]` `BooleanPrimeDiagonalWeakConvergence` supplies finite-cylinder product-measure and weak
  convergence machinery in a different prime-replica problem, but no source-FE Fock vector-state
  identification.
- `[CORPUS]` `PrimeWalshStoneReconstruction` and tail-cylinder modules confirm the corpus distinction
  between finite-cylinder observables and genuinely tail-sensitive quotient data.
- `[CORPUS NEGATIVE]` mandatory searches found no theorem identifying HC83's vector Born law with a
  projectively consistent product state, nor its exact local-vacuum/source-FE/RH classification.

## Theorem HC84-A: exact cutoff Born law

For every `S ⊆ range N`, prove

`‖Psi_N(r)(pairOccupation S)‖²
  = p(r)^|S| (1-p(r))^(N-|S|)`.

This is a theorem about actual coefficients of the common-Fock vector, not a separately postulated
probability model. Summing over all subsets gives total mass one.

## Theorem HC84-B: projective cylinder stabilization

For every `K ≤ N` and every reporter `f : Finset ℕ → ℝ` supported through intersection with
`range K`, prove the exact identity

`E_N[f(S ∩ range K)] = E_K[f]`.

Consequently every fixed cylinder expectation is eventually constant and converges, for every
`r`, including every nonzero ratio for which HC83 proves the vectors are not Cauchy. This is the
precise positive survivor exposed by the orthogonality obstruction: an extended product state
exists locally even though no representing vector survives in reference Fock.

## Theorem HC84-C: local occupation still detects the wall

The expectation of the first-mode occupation indicator is exactly `p(r)`, and

`p(r)=0 ↔ r=0`.

For the literal source-FE ratio, local pair occupation vanishes iff source pair amplitude vanishes,
iff partner number vanishes, iff `Re(q)=1/2`. Universal local vacuum is therefore equivalent to RH,
with exact HB, Deninger/FZZ-P, PW-B, and canonical-copy RBH receiver equivalences.

## Hostile checks

- Do not confuse coefficientwise convergence of vectors with convergence of their quadratic Born
  states; HC83 shows the former is zero while norm stays one.
- Derive every Born weight from `finitePairFockVacuum_apply_pairOccupation`; do not postulate an
  unrelated Bernoulli law.
- Prove stabilization for arbitrary real finite-cylinder reporters, not only one occupation moment.
- Separate two claims: cylinder convergence holds for every ratio, but cylinder *vacuum* holds only
  at zero ratio. The first cannot prove RH; the second remains a genuine producer obligation.
- Do not claim construction of a full CCR state or quasi-equivalence theorem beyond the proved
  diagonal cylinder algebra.
- No RH hypothesis, computation, finite numerical cutoff, external representation theorem, or new
  axiom.

## Expected route impact

HC84 settles the extended-sector ambiguity at the exact level supported by the corpus. Merely
requiring thermodynamic/local-state existence is a dead producer: it holds off wall. But the
disjoint state cannot hide pair production—its one-mode occupation is positive off wall. Remaining
physical burden becomes sharper: prove HB/QNM equilibrium imposes local vacuum (or an equivalent
zero-occupation law), rather than merely existence of an extended state.

## Bounded primary-literature audit (2026-08-28)

- `[LITERATURE]` von Neumann,
  [*On Infinite Direct Products*](https://www.numdam.org/article/CM_1939__6__1_0.pdf), develops
  incomplete infinite products and sector decomposition, not this finite-cylinder source-FE law.
- `[LITERATURE]` Lill,
  [*Bogoliubov Transformations Beyond Shale--Stinespring: Generic v* v for bosons*](https://arxiv.org/abs/2208.03487),
  constructs extended implementations beyond ordinary Fock without this common-Fock Born
  projective system or RH endpoint.
- `[LITERATURE]` Fogarty--Deffner--Busch--Campbell,
  [*Orthogonality Catastrophe as a Consequence of the Quantum Speed Limit*](https://doi.org/10.1103/PhysRevLett.124.110601),
  studies many-body overlap loss, not exact cylinder stabilization for a repeated bosonic pair
  product.
- `[NOVELTY CLAIM, BOUNDED]` Targeted primary-source and exact corpus searches found no theorem
  combining actual common-Fock cutoff coefficients, arbitrary complex pair ratio, exact
  all-reporter projective stabilization, and literal source-FE/RH receiver endpoints. This is a
  bounded audit, not an exhaustive literature claim.

## Formalization result

Formalized in
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFELocalCylinderProductState`.

- `finitePairFockBornWeight_eq_bernoulli` derives the exact Bernoulli product weight from actual
  common-Fock coefficients; the cutoff mass is exactly one.
- `finitePairFockCylinderExpectation_eq_cutoff` proves projective stabilization for every real
  reporter, and `tendsto_finitePairFockCylinderExpectation` gives its thermodynamic limit.
- `finitePairFockCylinder_tendsto_and_not_cauchy_of_ne` proves the sharp coexistence: every local
  cylinder state converges although the unit-vector family is not Cauchy for nonzero ratio.
- `finitePairFockOccupationDensity_eq_div` identifies the local density as
  `‖r‖²/(1+‖r‖²)`, while `finitePairFockOccupationDensity_eq_zero_iff` classifies local vacuum.
- Literal source-FE specializations prove unconditional global cylinder convergence, local vacuum
  iff wall, universal local vacuum iff RH, and HB/Deninger-FZZ-P/PW-B/RBH receiver equivalences.

Audit: direct `lake env lean` passed; targeted
`lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFELocalCylinderProductState`
passed all 12,191 jobs; representative `#print axioms` outputs contain only `propext`,
`Classical.choice`, and `Quot.sound`. Formal lint reports only pre-existing unreachable modules and
no HC84 finding.

## Open core after HC84

Local thermodynamic-state existence is now a proven dead producer: it holds unconditionally and
even off wall. Extended-sector pair production nevertheless remains locally visible and vanishes
exactly at RH. Hardest surviving producer is no longer representation existence; it is a physical
selection theorem deriving local vacuum from HB/QNM modular or KMS equilibrium without assuming
wall placement. If equilibrium permits the nonzero Bernoulli density, that producer route must be
retired; if it forbids it, the resulting theorem closes the source-to-RH burden.
