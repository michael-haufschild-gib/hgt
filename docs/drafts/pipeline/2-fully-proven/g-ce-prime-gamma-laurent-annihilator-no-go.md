# G-CE prime–Gamma Laurent annihilator no-go

- **ID:** GCE-LAURENT-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md`, G-CE; hard lock `rh-research-status.md`
- **Statement:** Evaluation of the unit-clock prime–Gamma determinant Laurent algebra on all ordinary primes is injective; hence no nonzero finite Laurent law annihilates every local transgression.

## Goal

Kill a full candidate class for G-CE's remaining RH edge. Exact chain:

`prime/Gamma source law` → non-erasing annihilation of
`continuedXiAntiCausalWardResponse (1/2)` → zero singular-graph debt → fixed-four G-CE
positivity → RH.

The affine zero-clock producer, finite-head landing, and graph completion already exist. This
theorem rules out obtaining the missing first arrow from any fixed finite algebraic expression in
one prime's forward/reflected unit-clock rotation determinants.

## Gates

- [x] 0 → 1 in-progress: source-pure, exact route edge, proof frozen, internal/external audit done
- [x] 1 → 2 fully-proven: complete paper proof below, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem and exact module build
- [ ] 3 → 4 publication-ready

## Audits

- **Corpus:** `PrimeGammaCofinalBocksteinDeterminantTransgression` proves the exact determinant
  transgression and only common-factor/determinant-one no-gos. `EulerPrimitiveJointDepthFiniteClockJetGaugeNoGo`
  kills finite clock jets. `MobiusGammaXiPreScalarAffinePrimePolarGammaProducer` and
  `MobiusGammaXiPreScalarAffineBoundaryRenormalization` already solve charge occurrence and
  coefficient-faithful landing. Corpus search found no all-prime Laurent faithfulness theorem for
  these physical determinants.
- **Literature through 2026-08:** targeted arXiv search found operator/semi-local RH frameworks,
  including Connes–Consani, *The Scaling Hamiltonian*, but no classification of finite Laurent
  annihilators for this prime–Gamma determinant family. Underlying infinite-root and Laurent
  localization lemmas are standard; route-specific theorem and consequence are new.

## Proof [PROVED HERE]

For prime `p`, unit-clock physical determinant is `aₚ = -p`. Reflected determinant is
`aₚ⁻¹ = -p⁻¹`; thus every finite polynomial expression in both orientations reduces to a Laurent
polynomial `F(T) ∈ ℂ[T,T⁻¹]`.

The points `aₚ` are nonzero and pairwise distinct, and primes form an infinite set. Suppose
`F(aₚ)=0` for every prime. Choose `n ≥ 0` and `P ∈ ℂ[T]` with
`F(T)Tⁿ = P(T)`. Then `P(aₚ)=aₚⁿF(aₚ)=0` for infinitely many distinct `aₚ`, so `P=0` by the
polynomial root bound. Therefore `F(T)Tⁿ=0`; since `Tⁿ` is a unit in the Laurent algebra, `F=0`.

Equivalently, simultaneous evaluation

`ℂ[T,T⁻¹] → ∏ₚ ℂ,  F ↦ (F(-p))ₚ`

is injective.

## No-go closure

- **Exact killing mechanism:** infinite ordinary-prime spectrum makes the unit-clock Laurent
  evaluation faithful. A finite algebraic law cannot vanish locally at every prime unless it erases
  its entire Laurent symbol.
- **Strongest positive survivor:** after quotienting the tautological reciprocal relation between
  forward/reflected determinants, the full local finite algebra is faithfully detected by primes.
- **New insight:** G-CE annihilation cannot be prime-local finite algebra. It must be genuinely
  cross-prime, infinite/singular, or non-algebraic before scalarization.
- **Status:** paper proof dependency-closed; Lean formalization next.

## Log

- 2026-09-02 — frozen after corpus and literature audit; paper proof closed.
