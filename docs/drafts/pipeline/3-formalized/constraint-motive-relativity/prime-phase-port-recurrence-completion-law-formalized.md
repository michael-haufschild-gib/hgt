# Prime phase-port recurrence and completion law — Lean certificate

- **ID:** `cmr-prime-phase-port-recurrence-completion-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `prime-phase-port-recurrence-completion-law.md` (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean module

`formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/PrimePhasePortRecurrence.lean`,
namespace `HTGeometry.ConstraintMotiveRelativity`, imported by `GaloisForLFunctions.HTGeometry`.

It instantiates two layers already in the tree rather than rebuilding them:

- the weighted-port symplectic and completion layer of the parent card
  (`PrimeAugmentationSymplectic.lean`, `PrimeAugmentationCompletion.lean`), which is stated for an
  arbitrary nowhere-vanishing / unimodular covector `c`;
- the finite diagonal phase-orbit layer of the parent prime-orbit card
  (`GaloisForLFunctions/HTGeometry/EulerPrimeOrbitFourOrganLaw.lean`), which owns Kronecker
  approximation, the Vandermonde jet family, the phase-blind energy and the lift length, together
  with `KroneckerWeylDensity.lean` and `ArchimedeanCorank.lean`.

The port-orbit recurrence machinery of `PortRecurrenceJets.lean` supplies the finite-aperture
recurrence and the coordinate derivative.

## Formal statement chain

### §1 — the arithmetic phase family and the algebraic port

1. `phaseCovec`, `phaseCovec_eq`, **`phaseCovec_eq_cpow`**, `norm_phaseCovec`,
   `phaseCovec_ne_zero`, `phaseCovec_zero` — `(PR.1)`: `λ_t = (p^{-it})`, a unimodular covector,
   written both as `exp(-i t log p)` and as the arithmetic power `p^{-it}`.
2. **`dualAnnihilator_phaseIdeal`** — `(PR.2)`: `I_t^⊥ = ℂ λ_t`.
3. **`phase_coisotropic_reduction`** — `(PR.2)`: the reduction `(x, a λ_t) ↦ (ε_t x, a)` maps the
   symplectic orthogonal of `I_t` onto `ℂ × ℂ`, has kernel exactly `I_t` there, and carries the
   cotangent form to the hyperbolic form; so `ℍ(K₀)//I_t ≅ ℍ(ℂ)`.
4. **`phaseIdeal_quotient_equiv`** — `K₀/I_t ≅ ℂ` through `ε_t`.

### §1 — `(PR.3)`, the finite phase orbit

5. **`phase_orbit_approx`** — density: every prescribed phase vector on a finite prime aperture is
   approximated by the orbit.  Unique factorization makes `{log p : p ∈ F}` rationally independent
   (`primeLogFiniteSlice_linearIndependent`), so Kronecker's theorem
   (`finiteDiagonalPhaseOrbit_approx`) applies.
6. **`phase_orbit_recurrent`** — recurrence: for every `ε > 0` and every `T` there is `t > T` with
   all coordinates within `ε` of one.  Obtained from `portOrbit_recurrent` on the finite aperture,
   i.e. from total boundedness plus the isometry of the flow.

### §2 — `(PR.4)`–`(PR.5)`, the completion phase is uniform in time

7. **`phaseCLM`** and **`closure_image_phaseIdeal_one`** — `(PR.4)`: `ε_t` extends continuously to
   `ℓ¹` with norm at most one and `closure I_t = ker ε_t`.
8. **`phaseCLM_surjective`** and **`eq_smul_phaseCLM_of_vanishing`** — that kernel is closed of
   codimension one and its continuous annihilator is `ℂ λ_t`.
9. **`closure_image_phaseIdeal_lp`** and **`closure_image_phaseIdeal_top`** — `(PR.5)`: in `ℓ^p`
   for `1 < p < ∞` and in `c₀` the constraint `I_t` is dense; the spread vector `(PR.6)` is the
   generic small vector of port value one.
10. **`phase_separation_defect_erasure`**, **`phase_separation_defect_erasure_top`** — `(PR.5)`:
    the continuous annihilator is zero and Hausdorff reduction of the port vanishes.
11. **`phase_separation_defect_one`** — `(PR.4)`: the `ℓ¹` separation defect is zero at every time.

Items 7–11 hold for every `t` with the same proof, which is the card's "uniform in time" claim.

### §3 — `(PR.7)`–`(PR.10)`, the infinite recurrent observer

12. `phaseVec`, `phaseVec_apply` — `(PR.7)`: `λ_t` as a point of the unit torus inside `ℓ^∞`.
13. **`norm_phaseVec`** — `(PR.10)`: `‖λ_t‖_∞ = 1` for every `t`; the positive observer is
    phase-blind.
14. **`phaseLiftEnergy_eq`** — `(PR.9)`: the squared Euclidean lift length is
    `A_F(t) = t² ∑_{p ∈ F} (log p)²`.
15. **`phaseLiftEnergy_unbounded`** — `(PR.8)`–`(PR.9)`: on every nonempty aperture the lift length
    is unbounded, while by item 6 the orbit itself recurs.

### §3.1 — `(PR.9a)`–`(PR.9b)`, finite jets and the generator wall

16. `jetNode_injective` and **`phaseJet_linearIndependent`** — `(PR.9a)`: the nodes `-i log p` are
    pairwise distinct, so on an aperture of `N` primes the first `N` jet covectors form a
    Vandermonde family and are linearly independent, hence a basis of the finite cotangent space.
17. **`phaseJet_span_ne_top`** — `(PR.9a)`: a fixed jet order `r` cannot span an aperture with
    `r + 1 < N`, so a common invisible subspace survives.
18. `hasDerivAt_phaseCovec` — the time derivative of one phase coordinate is `-i log p` times the
    coordinate.
19. **`continuous_weakStar_pairing`** — the orbit is weak-star continuous: pairing against a fixed
    `ℓ¹` vector is continuous in time, by dominated summation.
20. **`no_weakStar_derivative`** — the wall: no `v ∈ ℓ^∞` is the weak-star derivative at zero, since
    the coordinate tests force `v_p = -i log p` and `log p` is unbounded on the primes.
21. **`weighted_predual_bound`** — `(PR.9b)`: on the weighted predual `ℓ¹_{log^n}` the `n`-th jet
    coefficient functional is summable and bounded by the weighted norm.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/PrimePhasePortRecurrence.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PrimePhasePortRecurrence
```

Green with no warnings.  `#print axioms` on `phaseCovec_eq_cpow`, `dualAnnihilator_phaseIdeal`,
`phase_coisotropic_reduction`, `phaseIdeal_quotient_equiv`, `phase_orbit_approx`,
`phase_orbit_recurrent`, `closure_image_phaseIdeal_one`, `phaseCLM_surjective`,
`eq_smul_phaseCLM_of_vanishing`, `closure_image_phaseIdeal_lp`, `closure_image_phaseIdeal_top`,
`phase_separation_defect_one`, `phase_separation_defect_erasure`,
`phase_separation_defect_erasure_top`, `norm_phaseVec`, `phaseLiftEnergy_eq`,
`phaseLiftEnergy_unbounded`, `phaseJet_linearIndependent`, `phaseJet_span_ne_top`,
`continuous_weakStar_pairing`, `no_weakStar_derivative` and `weighted_predual_bound` reports only
`propext`, `Classical.choice`, `Quot.sound`.

## Scope notes

The card's Theorem 4 asserts that on the bounded torus the product topology and the weak-star
topology of `ℓ^∞ = (ℓ¹)'` coincide, and derives density and relative compactness from that.  The
Lean development records the two statements that carry the content: the finite-cylinder density
`phase_orbit_approx` (which *is* density for the product topology, since cylinders are a basis) and
the weak-star continuity `continuous_weakStar_pairing`.  Relative compactness of the orbit is then
Tychonoff for the ambient torus and adds no arithmetic content; the recurrence the card uses is
proved directly in `phase_orbit_recurrent`.

`(PR.9a)` is stated through the corpus Krylov/Vandermonde family
`finiteDiagonalKrylovVector node 1 k` with `node p = -i log p`; this is literally the jet covector
matrix `((-i log p)^n)` of the card.  Its "invisible subspace of dimension at least `N - r - 1`" is
recorded as the non-spanning statement `phaseJet_span_ne_top`, which is the form the corpus lemma
proves and the form the card's conclusion uses.

The card's exact isometric conjugacy `I_t = U_t^{-1} I_0` is realized structurally rather than as a
separate theorem: the whole symplectic and completion layer is stated for an arbitrary unimodular
covector, so every time-`t` statement is one instantiation of the same lemma, which is precisely
the hostile-review observation that the time-dependent phase law is a compatibility bridge.

§4–§9 are programme scope, nonimplication commentary and no-go bookkeeping; the specific
nonimplications they name (constant norm versus unbounded lift length; finite recurrence versus
global Hilbert port; weak-star continuity versus admitted derivative) are items 13/15, 6/10 and
19/20 above.
