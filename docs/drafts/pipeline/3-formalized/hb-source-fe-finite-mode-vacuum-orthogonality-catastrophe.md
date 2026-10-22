# HB source-FE finite-mode vacuum orthogonality catastrophe

- **ID:** HC83
- **Stage:** 3-formalized
- **Type:** THEOREM / FINITE-MODE LIMIT NO-GO + REPRESENTATION-SELECTION ENDPOINT
- **Source:** read-only `rh-current-frontier-map.md` · HC82 regular-Fock obstruction

## Goal

Attack the sole survivor after HC82: finite-mode Bogoliubov vacua may exist at every cutoff even
when no infinite regular-Fock vacuum exists. Decide whether those cutoff vacua can nevertheless be
recovered as a norm/Cauchy limit inside the corpus occupation Hilbert space.

Construct, for every complex ratio `r` and cutoff `N`, the normalized pair-product vector in
`BosonicFock Nat`

`Psi_N(r) = c(r)^N sum_{S subset {0,...,N-1}} r^{|S|} e_{2 1_S}`,

where `c(r)=(1+‖r‖²)^(-1/2)`. Prove each vector has norm one and the sequence `N ↦ Psi_N(r)` is
Cauchy exactly when `r=0`. Thus a nontrivial repeated pair ratio forces finite vacua into a
different incomplete infinite-product sector rather than an ordinary Fock norm limit.

Specialize `r` to HC82's literal source-FE ratio. The cutoff-vacuum sequence is Cauchy exactly on
the critical wall; universally over all Xi copies this is equivalent to RH and to every route
receiver.

## Gates

- [x] 0 → 1 in-progress: corpus audit; exact conjecture frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and bounded primary-literature audit
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical/physical review and broader novelty search

## Corpus audit

- `[CORPUS]` HC82 proves arbitrary diagonal empty-mode recurrence necessity and rules out every
  nonzero constant-ratio regular occupation-Hilbert vacuum.
- `[CORPUS]` `HTGeometry.OccupationVacuumAnomalyReciprocity` constructs normalized finite
  occupation half-densities and exact finite-product vacuum amplitudes, but its cutoff carriers vary
  with the finite mode type and it gives no common-Fock Cauchy classification.
- `[CORPUS]` `GoldstoneFabriPicassoCorpusApplications` proves one fixed pair of finite vacua becomes
  orthogonal under tensor powers, but has no arbitrary ratio, common occupation embedding,
  source-FE coefficient, or RH endpoint.
- `[CORPUS]` `LpReindexCompactDichotomy.norm_sq_sum_single` gives exact Pythagoras for finite
  injective coordinate packets; `Finset.prod_one_add` supplies the subset-product normalization.
- `[CORPUS]` `cauchySeq_tendsto_of_complete` and continuous `lp` coordinate evaluation allow a
  Cauchy sequence to be tested against every fixed occupation coefficient.
- `[CORPUS NEGATIVE]` mandatory searches found no theorem constructing this common-Fock pair-product
  family or classifying its Cauchy behavior exactly by the literal Xi source-FE ratio.

## Theorem HC83-A: normalized common-Fock pair products

Let `pairOccupation(S)=sum_{n in S} 2 e_n`. The map from finite mode sets to occupations is
injective. Define the raw and normalized vectors above. Prove

`‖Psi_N(r)‖² = 1`

for every `N` and `r`, and prove the exact coefficient law: coefficients vanish away from pair
occupations, while at `pairOccupation(S)` they equal `c(r)^N r^{|S|}` once `S` lies below the
cutoff.

## Theorem HC83-B: Cauchy iff trivial ratio

If `r ≠ 0`, then `0 < c(r) < 1`. For every fixed occupation, the coefficient of `Psi_N(r)` tends to
zero: it is either identically zero or eventually a fixed power of `r` times `c(r)^N`. If the
normalized sequence were Cauchy, completeness would give a norm limit. Continuous coordinate
evaluation makes every coefficient of that limit zero, hence the limit vector is zero. Norm
continuity simultaneously gives limit norm one, contradiction. If `r=0`, every cutoff vector is
the ordinary vacuum. Therefore

`CauchySeq (Psi_.(r)) ↔ r=0`.

## Theorem HC83-C: source-FE and RH endpoints

For HC82's normalized source-FE ratio `r(q)`, prove

`CauchySeq (Psi_.(r(q))) ↔ Re(q)=1/2`,

universal Cauchy convergence iff RH, plus exact HB, Deninger/FZZ-P, PW-B, and canonical-copy RBH
receiver equivalences.

## Hostile checks

- Do not infer convergence merely from existence of every finite cutoff.
- All `Psi_N` must live in one concrete `BosonicFock Nat`; varying finite-dimensional carriers do
  not state a Cauchy problem.
- Do not assume the vacuum coefficient detects the whole norm limit. Prove every fixed occupation
  coefficient tends to zero, then use extensionality.
- Do not claim nonexistence of the von Neumann incomplete tensor product sector. The conclusion is
  precisely that off-wall vacua leave the reference Fock sector.
- This is a qualitative representation-selection theorem, not an optimized decay bound.
- No RH hypothesis, computation, finite numerical cutoff, external Shale theorem, or new axiom.

## Expected route impact

HC83 kills the last ordinary-Fock approximation escape: off-wall finite-mode vacua are
perfectly normalized at every cutoff but cannot even be Cauchy in the reference occupation Hilbert
space. Extended Fock is then not a harmless completion of the same representation; it is a
different sector. Remaining physical producer becomes exact and unavoidable: prove HB/QNM states
are selected in the reference regular sector, or define all route receivers on the disjoint sector
and prove their equilibrium law there.

## Bounded primary-literature audit (2026-08-28)

- `[LITERATURE]` von Neumann,
  [*On Infinite Direct Products*](https://www.numdam.org/article/CM_1939__6__1_0.pdf), develops
  infinite direct/tensor products and their sector decomposition, but no Xi source-FE pair products
  or iff-RH Cauchy classification.
- `[LITERATURE]` Shale,
  [*Linear Symmetries of Free Boson Fields*](https://doi.org/10.1090/S0002-9947-1962-0137504-6),
  classifies regular bosonic implementability abstractly; HC83 instead constructs the cutoff family
  and proves its common-Fock limit failure internally.
- `[LITERATURE]` Lill,
  [*Bogoliubov Transformations Beyond Shale--Stinespring: Generic v* v for bosons*](https://arxiv.org/abs/2208.03487),
  constructs extended implementations beyond ordinary Fock and confirms the surviving sector
  interpretation, without this source-specific cutoff sequence or RH endpoint.
- `[LITERATURE]` Anderson,
  [*Infrared Catastrophe in Fermi Gases with Local Scattering Potentials*](https://doi.org/10.1103/PhysRevLett.18.1049),
  proves thermodynamic ground-state overlap loss in a fermionic scattering problem, not this bosonic
  pair-product Cauchy iff law.
- `[NOVELTY CLAIM, BOUNDED]` Targeted primary-source and exact corpus searches found no theorem
  combining an explicit common occupation-Hilbert cutoff family, arbitrary complex pair ratio,
  exact Cauchy iff-zero classification, and the literal source-FE/RH receiver endpoints. This is a
  bounded audit, not an exhaustive literature claim.

## Formalization result

Formalized in
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFEFiniteModeFockVacuumOrthogonality`.

- `pairOccupation` is injective, and `finitePairFockRaw` has the exact subset coefficient law and
  norm square `(1 + ‖r‖²)^N`.
- `finitePairFockVacuum` has norm one at every cutoff and satisfies the exact finite-mode pair
  recurrence.
- `cauchySeq_finitePairFockVacuum_iff` proves Cauchy convergence exactly when `r = 0`; for every
  nonzero ratio every fixed occupation coefficient tends to zero despite unit norm.
- Source-FE specializations prove Cauchy iff partner zero iff critical wall, globally iff RH, and
  transfer this exact endpoint to HB, Deninger/FZZ-P, PW-B, and canonical-copy RBH receivers.

Audit: direct `lake env lean` passed; targeted
`lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFEFiniteModeFockVacuumOrthogonality`
passed all 12,189 jobs; representative `#print axioms` outputs contain only `propext`,
`Classical.choice`, and `Quot.sound`. Formal lint reports only pre-existing unreachable modules and
no HC83 finding.

## Open core after HC83

Reference-Fock approximation escape is dead. Off-wall normalized cutoff vacua leave every fixed
occupation coefficient while remaining unit norm, so any extended realization is genuinely
disjoint rather than a missing norm completion. Hardest survivor: construct its local/cylinder
observable state and decide whether HB/QNM route receivers are sector-sensitive. Either prove
reference-sector selection, or prove local receiver equilibrium cannot distinguish the disjoint
sector and therefore cannot force RH without a new tail-sensitive hypothesis.
