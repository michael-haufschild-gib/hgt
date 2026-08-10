# Projective amplitude, Fisher–phase coupling, hidden history — Lean certification

- **ID:** ULF-PAFP-1
- **Paper card:** `projective-amplitude-fisher-phase-and-hidden-history-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutivePolarAmplitudeFisherPhase`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

### §1 — the polar projective chart (boxed equation (1))

`FullAmp N`, `projSetoid`, `ProjAmp N`; `OpenSimplex N`; `phaseSetoid`, `PhaseClass N`.
`ampNormSq_pos`, `ampProb`, `ampProb_pos`, `ampProb_sum`, `ampPhase`, `ampPhase_coe`;
`ampNormSq_smul`, `ampProb_of_equiv`, `ampPhase_of_equiv`; `ofPolarData`,
`ampNormSq_ofPolarData`, `ampProb_ofPolarData`, `ampPhase_ofPolarData`.

**`polarEquiv : ProjAmp N ≃ OpenSimplex N × PhaseClass N`** is the boxed bijection itself — the
quotients are constructed and the two round trips are proved, not just the two maps.
`polarEquiv_fst` says the probability observer is the first projection, so its fibre over any
probability is exactly the relative-phase torus.

### §2 — the Fubini–Study decomposition (boxed equation (2))

`ampNormSq`, `ampInner`, `fsSpeedSq`, `polarAmp`, `polarTangent`; `norm_exp_I_mul_ofReal`,
`normSq_ofReal_add_I_mul`, `normSq_polarTangent`, `ampNormSq_polarTangent`;
`ampInner_polarAmp_polarTangent` (the Berry connection value `i ∑ pᵢ dφᵢ`, which uses
`∑ dpᵢ = 0`); **`fsSpeedSq_polar`** is equation (2).

`hasDerivAt_polarAmp` proves `polarTangent` *is* the derivative of the polar curve, so (2) is an
identity about a genuine line element rather than a chosen algebraic expression.

### §3 — constant positive shadow, nontrivial projective history

`phaseLoop` (3), `normSq_phaseLoop` (the observer is constant), `phaseLoop_two_pi` (the loop
closes), `phaseLoopVelocity`, `hasDerivAt_phaseLoop`; `velMean`, `velVar`;
**`fsSpeedSq_phaseLoop`** (4), **`length_phaseLoop`** (5), `velVar_eq_sum` and
`velVar_eq_zero_iff` (the length is nonzero exactly when the integer velocities differ);
**`berryConnection_phaseLoop`**, `berryHolonomy`, `berryHolonomy_eq_exp_integral` (6);
`twoLevelProb`, `twoLevelVel`, `velMean_twoLevel`, `velVar_twoLevel`, and `twoLevel_example` —
the card's `N = 2` instance with stationary observer, projective length `π` and Berry holonomy `−1`.

### §4 — the phase-genesis no-go

`probObserver` and `probObserver_not_injective`: `(1,1)` and `(1,−1)` share a probability vector and
are not proportional.  Combined with `polarEquiv`, this is the exact fibre statement: probability
determines neither relative phase nor projective history.

`polar_amplitude_fisher_phase_law` bundles §3.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutivePolarAmplitudeFisherPhase.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both pass with no warnings; the umbrella build completed 11,436 jobs.  `#print axioms` on the eleven
declarations audited reports only `propext`, `Classical.choice`, and `Quot.sound`.  No project
axiom, placeholder, hypothesis interface, or computation proof is used.

## Exact field consequence

The smallest finite single producer is the projective complex amplitude: it determines both the
probability and the relative phase, while the probability determines neither.  Equation (2) is the
exact local weld between the two polar shadows — one quarter of the Fisher–Rao metric plus the
weighted phase variance — and §3 exhibits a loop on which the positive shadow is *completely*
stationary while the projective length is `2π√Var` and the Berry holonomy is nontrivial.  A modular
path-law geometry therefore cannot obtain phase from its positive law by functorial inference.
