# Route U first-contact boundary roughness

- **ID:** route-u-first-contact-boundary-roughness
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY AUDITED—NO EXACT COLLISION FOUND] [NO RH CLAIM]`
- **Source:** `rh-current-frontier-map.md`, Route U (read-only source map)
- **Statement:** Either RH holds, or the continuous restricted-Weil ground-energy path has a least zero aperture with a genuine completed null ground vector that no strict smooth interior source represents.

## Goal

Replace the failed smooth-interior positivity attack by a closed localization of the false-RH
obstruction at the aperture boundary.  This does not prove RH.  It identifies the exact
completion/trace channel that a successful Route-U strictness theorem must eliminate.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack identified
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: closed Lean capstone, exact leaf build, axiom audit
- [ ] 3 → 4 publication-ready: standalone exposition and independent priority review

## Conjecture loop

1. **U-NK1 — root quotients create an infinite null kernel.** Failed: simple-root quotients are
   terminal channels; only repeated nonterminal descendants are forced null.
2. **U-EP1 — hard-edge endpoint invisibility is odd-specific.** Failed: endpoint orthogonality is
   parity-blind.
3. **U-EP2 — a prime jump can create a negative even state.** Failed: the exact even prime-jump
   response vanishes on the admitted endpoint band.
4. **U-LP1 — compact Fourier support plus Laguerre–Pólya structure forces fixed-chamber
   positivity.** Failed as an independent route: the needed total-positivity sign is RH-equivalent
   in this corpus.
5. **U-BR1 — first-contact nullity is necessarily aperture-boundary rough.** Proved on paper and
   in Lean.

## Exact theorem

Lean module:
`GaloisForLFunctions.RHTower.Suzuki.SuzukiFirstContactBoundaryRoughness`

Capstone:

```lean
theorem riemannHypothesis_or_ccmFirstContactBoundaryRoughness :
    RiemannHypothesis ∨ CCMFirstContactBoundaryRoughness
```

Here `CCMFirstContactBoundaryRoughness` supplies an aperture `a` and form-domain vector `q` with:

- `ccmRestrictedWeilGroundEnergy a = 0`;
- every positive `b < a` has strictly positive ground energy;
- the physical image of `q` is nonzero;
- the restricted-Weil energy of `q` is zero;
- no `CCMComplexSmoothInteriorSource a` maps to `q`.

Supporting new theorems:

- `exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis`;
- `ccmSmoothInteriorSource_source_pos_of_smaller_groundEnergy_pos`.

## Paper proof

1. `¬RH` negates Suzuki's exact smooth-test criterion.  Hence some compact smooth zero-mean test
   has negative screw energy.
2. Enlarge its aperture strictly, restrict it to interval `L²`, and use its zero mean to form a
   Suzuki derivative coordinate.  The primitive CCM vector has exactly the same energy by the
   screw/Weil/Friedrichs bridges.  The ground lower bound therefore forces a negative ground value.
3. Choose a smaller aperture with positive ground energy using unconditional small-aperture
   coercivity.  Antitonicity orders the positive and negative apertures.
4. Extend the ground-energy path continuously to a real interval by clamping at the positive
   aperture.  The infimum of the closed nonpositive-contact set belongs to that set.  Continuity
   and the intermediate value theorem rule out a strictly negative value at the infimum, so this
   value is zero.  Minimality plus antitonicity gives strict positivity at every smaller aperture.
5. The attained-ground theorem supplies a nonzero completed null vector at first contact.
6. Any strict smooth interior source has compact support inside a genuinely smaller aperture and
   descends there without changing its form vector, norm, or source energy.  The smaller ground is
   positive, so every nonzero such source has positive energy.  It therefore cannot equal the null
   ground vector.

## Big-picture reinterpretation

Prime walls are spectrally invisible on both parity sectors.  False RH cannot first enter through
an arithmetic jump or through a literal smooth source.  It must enter through loss of compact
containment in the completed form domain.  Route U's remaining target is therefore a boundary
trace/quotient exclusion theorem, not another interior Gram estimate.

## Novelty audit

- Suzuki's 2026 paper already states the qualitative precursor: continuity, small-aperture
  positivity, and false RH imply degeneracy at some aperture.
- The paper also identifies the Friedrichs completion and the strict inclusion of the minimal
  `H₀¹` domain in the completed form domain.
- Searches of Suzuki 2022/2023/2026, Connes--Consani, and related restricted-Weil literature found
  no exact statement selecting the least contact and proving its attained null vector is absent
  from the literal strict smooth-interior core.
- No priority claim is made without independent review.

## Verification

- Scratch: `lake env lean /tmp/RouteUFirstContact.lean` — PASS.
- Production direct check: `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiFirstContactBoundaryRoughness.lean` — PASS.
- Exact leaf build:
  `lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiFirstContactBoundaryRoughness` — PASS
  (`10492/10492`; missing prerequisite `.olean`s rebuilt as required).
- Closed axiom audit for all three public theorems — PASS; dependencies are exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan of the leaf (`sorry`, `admit`, `axiom`, `opaque`, `unsafe`) — clean.
- Umbrella wired; umbrella itself deliberately not built.
- No numerical computation used.

## Log

- 2026-08-16 — created in 1-in-progress after parity-complete prime-wall closure.
- 2026-08-16 — qualitative degeneracy collision found in Suzuki 2026; pivoted to least-contact
  boundary exclusion.
- 2026-08-16 — paper proof and closed Lean capstone completed; promoted to 3-formalized.
