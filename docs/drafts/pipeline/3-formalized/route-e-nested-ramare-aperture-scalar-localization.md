# Nested Ramaré aperture scalar localization

- **ID:** E-IMC-SCALAR-LOCALIZATION
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `rh-current-frontier-map.md` · Route E Ramaré inter-modulus alternative
- **Statement:** For nested designated-prime apertures `P ⊆ Q`, the difference of their exact Ramaré incidence-complement forms contains no scalar mass from integers already active at `P`; it is exactly the new-activation seam plus old minus new normalized prime-load energy.

## Goal
Close Route E's structural inter-modulus premise without centering or changing source coefficients. Chain: exact Ramaré integer incidence → nested-aperture scalar cancellation → control only activation seam and prime-load variation in moving Gallagher assembly → half-power Möbius cancellation → Littlewood/RH endpoint.

## Gates
- [x] 0 → 1  in-progress: corpus-derived, source-pure, exact attack identified
- [x] 1 → 2  fully-proven: complete paper proof and external novelty audit
- [x] 2 → 3  formalized: Lean theorem, target build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone theorem/proof/Lean certificate

## Approach
Apply the proved identity `complement form = normSq(total source) - normalized prime-load energy` at both apertures. Split the larger active set into old plus newly active integers and polarize `normSq(old + new) - normSq(old)`. Specialize to `primeFactorsIn P`, `primeFactorsIn Q`, and the literal Möbius phase. This must produce the exact pointwise moving seam before any absolute-value estimate.

## Proof
Let `S_P ⊆ S_Q` be the active integer sets.  At aperture `R`, exact incidence recombination gives
`Q_R(c) = |∑_{S_R} c|^2 - ∑_{r∈R}|L_{R,r}(c)|^2`.  Write
`∑_{S_Q}c = ∑_{S_P}c + ∑_{S_Q\S_P}c` and polarize.  Subtracting `Q_P` cancels
`|∑_{S_P}c|^2` exactly, leaving
`2 Re(A_P conjugate(B)) + |B|^2 + ∑_{p∈P}|L_{P,p}|^2 - ∑_{q∈Q}|L_{Q,q}|^2`.
Monotonicity `P ⊆ Q ⇒ S_P ⊆ S_Q` follows directly from divisibility.  Substitution of the
literal Möbius phase and the established prime-pair/integer-incidence identity proves the pointwise
law; continuity of the finite Dirichlet sums gives its integrated Gallagher form.

## Novelty audit
Corpus search found single-aperture Gram decomposition, conditional negativity, disjoint double
Ramaré weights, and antiscale recurrence, but no nested-aperture difference law.  Primary-source
audit through August 2026 found no such law in Matomäki–Teräväinen (arXiv:1911.09076),
Ramaré–Zuniga Alterman (arXiv:2312.05138), or their 2026 Möbius double-sum paper
(arXiv:2603.25961).

## Lean certificate
`GaloisForLFunctions.RHTower.Sieve.RouteERamareNestedApertureScalarLocalization` proves the generic,
arithmetic, literal Möbius pointwise, and integrated identities.  Target build passed.  Axiom audit:
only `propext`, `Classical.choice`, `Quot.sound`; no project axiom.

## Log
- 2026-09-01 — frozen after corpus audit found decomposition, conditional negativity, double Ramaré weight, and antiscale results but no nested-aperture difference law.
- 2026-09-01 — paper proof, Lean formalization, target build, and axiom audit completed.
