# HB charged double-KMS sector-swap no-go

- **ID:** HC86
- **Stage:** 3-formalized
- **Type:** THEOREM / HARTLE--HAWKING PURITY NO-GO + CHARGE-SECTOR CLASSIFICATION
- **Source:** read-only `rh-current-frontier-map.md` · HC85 KMS no-go · existing aligned double-KMS endpoint

## Goal

Attack the hardest survivor after HC85: perhaps Hartle--Hawking purity and wedge reflection force
the visible and partner arithmetic KMS ratios into the same occupation sector, recovering the
existing aligned-purification iff-RH endpoint. Test the known charged-sector escape constructively,
inside the corpus Hilbert-space thermofield machinery.

For one theta backreaction resonance and prime, let `q₊` and `q₋` be the visible and reflected
geometric KMS ratios. Construct two normalized geometric half-densities and their tensor product

`V(k,l)=sqrt((1-q₊)q₊^k) sqrt((1-q₋)q₋^l)`.

Construct the charge-conjugate partner with factors reversed. Prove both are unit vectors and their
squared Schmidt coefficients agree exactly after the charge swap `(k,l)↦(l,k)`, for every horizon
charge. Prove coefficient agreement without that swap holds exactly when `q₊=q₋`, hence exactly
when horizon charge is zero. Globally, swap-compatible double-KMS completion is unconditional,
while occupation-preserving alignment is equivalent to RH.

## Gates

- [x] 0 → 1 in-progress: corpus audit; exact conjecture frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and bounded primary-literature audit
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical/physical review and broader novelty search

## Corpus audit

- `[CORPUS]` `ThetaCuspHawkingHartleHawkingDoubleKMSEndpoint` proves same-occupation Schmidt
  alignment iff horizon charge zero and globally iff RH, but explicitly labels derivation of that
  alignment as open and cites charged-sector factorization as the escape.
- `[CORPUS]` `HTGeometry.WoldThermofieldStandardForm` constructs normalized geometric occupation
  half-densities, square-summable tensor-product vectors, exact tensor norm multiplication, and
  coefficient laws.
- `[CORPUS]` the visible and reflected source ratios are already proved in `(0,1)` for every
  resonance and prime.
- `[CORPUS NEGATIVE]` mandatory searches found no explicit source-ratio charge-sector tensor vector,
  no charge-swap isospectrality theorem, and no exact classification of unswapped alignment by
  horizon charge/RH.

## Theorem HC86-A: explicit charged thermofield double

Define visible and partner vectors in `lp (fun _ : ℕ×ℕ => ℂ) 2` by tensoring the two geometric
half-densities in opposite orders. Prove both have norm square one and derive the exact coefficient
mass formulas from the actual `lp` vectors.

## Theorem HC86-B: swap isospectrality is unconditional

For all occupations `k,l`, prove

`‖V(k,l)‖² = ‖P(l,k)‖²`.

This is the precise charge-conjugate Schmidt matching allowed by a pure charged thermofield double.
It must hold at every resonance and prime, with no wall or RH assumption.

## Theorem HC86-C: no-swap alignment iff neutral

Define occupation-preserving alignment by

`∀k l, ‖V(k,l)‖² = ‖P(k,l)‖²`.

Prove this iff `q₊=q₋`, iff horizon charge zero. The forward proof must extract the ratio equality
from actual coefficients, e.g. occupations `(1,0)`, and use positivity of both geometric vacuum
masses. Universal no-swap alignment is then RH; universal charge-swap alignment is unconditional.

## Hostile checks

- Use normalized `lp` half-density vectors, not a structure whose existence is tautological.
- Prove coefficient identities and unit norms through corpus thermofield machinery.
- Distinguish charge-swap spectrum matching from occupation-preserving matching; only the latter is
  RH-bearing.
- Do not claim every Hartle--Hawking theory contains a charged scalar. Conclusion is conditional
  and exact: purity/wedge reflection alone cannot exclude this mathematically consistent escape.
- Do not claim full interacting QFT construction or type-III density matrices.
- No RH hypothesis, computation, numerical cutoff, or new axiom.

## Expected route impact

HC86 kills abstract Hartle--Hawking purity/wedge reflection as the missing HB producer.
A completely normalized charged double exists with unequal local ratios and exact Schmidt matching
after charge conjugation. The only surviving alignment producer must prove from real theta-mirror
dynamics that charge sectors are absent, identified without swapping, or coupled by an additional
source-faithful phase/Ward law. This prevents spending effort treating general double-KMS purity as
if it already selected RH.

## Bounded primary-literature audit (2026-08-28)

- `[LITERATURE]` Higuchi--Lima,
  [*Hartle--Hawking State in the Real-Time Formalism*](https://doi.org/10.1103/PhysRevD.105.045002),
  establishes Hartle--Hawking/double-KMS equivalence under static-horizon hypotheses, not
  source-specific occupation-sector alignment.
- `[LITERATURE]` Chapman--Chen,
  [*Charged Complexity and the Thermofield Double State*](https://doi.org/10.1007/JHEP02(2021)187),
  shows charged complex-scalar TFD factorization into positive and negative charge modes with
  shifted thermal parameters. It does not give this Xi/source-ratio Lean classification.
- `[LITERATURE]` Araki--Shiraishi,
  [*On Quasifree States of the Canonical Commutation Relations (I)*](https://doi.org/10.2977/prims/1195193785),
  develops doubled Fock-type realizations of quasifree CCR states, without this charge-swap/RH law.
- `[NOVELTY CLAIM, BOUNDED]` Targeted primary-source and exact corpus searches found no theorem
  combining explicit normalized source-ratio tensor half-densities, charge-swap isospectrality,
  unswapped neutrality classification, and global iff-RH endpoint. This is a bounded audit, not an
  exhaustive literature claim.

## Formalization result

Formalized in
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingChargedDoubleKMSSectorSwapNoGo`.

- Explicit visible and partner vectors tensor the corpus normalized geometric half-densities in
  opposite charge orders; both have norm square one.
- Exact coefficient theorems identify their squared Schmidt masses as products of the two source
  geometric KMS laws.
- `thetaCuspHawkingPrimeChargedDoubleKMS_chargeSwap_isospectral` proves unconditional coefficient
  matching after `(k,l) ↦ (l,k)`.
- No-swap matching is classified exactly by equality of the two ratios, hence by zero horizon
  charge. The forward implication extracts equality from the actual `(1,0)` coefficients and
  cancels strictly positive vacuum factors.
- Universal charge-swap completion is unconditional; universal occupation-preserving alignment is
  equivalent to RH.

Audit: direct `lake env lean` passed; targeted
`lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingChargedDoubleKMSSectorSwapNoGo`
passed all 10,998 jobs; representative `#print axioms` outputs contain only `propext`,
`Classical.choice`, and `Quot.sound`. Formal lint reports only pre-existing unreachable modules and
no HC86 finding.

## Open core after HC86

Abstract double-KMS purity and wedge reflection are dead as alignment producers: normalized charged
sectors evade them exactly. Remaining HB producer must derive a no-charge-sector theorem from the
real theta source—e.g. self-conjugacy of the quantized source algebra, a superselection rule that
forbids the swap, or a phase-sensitive Ward coupling between charges. Hardest next audit is whether
existing source/modular certificates already force charge-sector irreducibility; if not, construct
an explicit algebraic two-sector model satisfying them and retire that mechanism too.
