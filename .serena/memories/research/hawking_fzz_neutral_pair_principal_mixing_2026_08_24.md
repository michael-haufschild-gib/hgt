# Hawking/FZZ neutral-pair principal mixing no-go (2026-08-24)

## Result

New module:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingFZZNeutralPairPrincipalMixingNoGo.lean`

Import wired into:
`formal/GaloisForLFunctions/RHTower.lean`

Torus monodromy neutrality forces physical pair coordinate `lambda = mu^2`. Exact screening rewrite:
`mu^(2n)/(n!)^2 = lambda^n/(n!)^2`.

Depth-one FZZ/Parikh-Wilczek response:
`thetaCuspHawkingFZZNeutralPairResponse lambda s =
  lambda * schwarzschildParikhWilczekMellinJet 1 s`.

Main theorem:
`thetaCuspHawking_fzzNeutralPairPrincipalMixing`

It proves unconditional mixing at every Xi divisor copy and every nonzero neutral-pair coupling. Also:
- exact coefficient de-ramification and recurrence;
- nonzero principal derivative at every Xi divisor;
- exact depth-zero dark -> first-neutral-pair bright transition.

## Research meaning

Quadratic onset in bare FZZ condensate `mu` is mandated by torus neutrality and becomes unit onset in canonical neutral-pair coordinate `lambda=mu^2`. Thus generic quadratic KMS countermodels partly reflect wrong coupling coordinate.

But principal mixing/nonvanishing is RH-blind: it holds for all Xi divisor sectors, including hypothetical off-critical ones. Remaining RH producer must use coefficient phase/sign or prove incidence with target-space canonical energy / canonical Schur-Cayley backreaction edge. It cannot use onset/nonvanishing alone.

Physical caveat inherited from `ThetaCuspHawkingFZZNeutralScreeningRecoilEndpoint`: same-depth FZZ/4d Parikh-Wilczek identification remains conjectural cross-regime bridge.

## External source audit

- Ashok-Troost arXiv:1101.1059: full cigar elliptic genus is signed supertrace over momentum-winding wedges; nonholomorphic continuum term is linear boson-fermion spectral asymmetry derived from reflection phase, not positive optical energy.
- Halder-Jafferis arXiv:2402.00932v3: fractional-winding derivative gives nonlocal area operator; torus one-point only expected/open.
- Ma-Yang arXiv:2401.15516 and Fransen-Pereniguez-Redondo-Yuste arXiv:2509.03598: nonlinear Teukolsky couplings have genuine selection rules and some vanishing channels, killing blanket overlap nonvanishing assumptions.

## Verification

- Direct targeted Lean check passed.
- `#print axioms` for all 12 new theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- Targeted generated olean and /tmp scratches removed.
- Formal lint ran; only pre-existing unrelated umbrella reachability errors:
  - `RHTower.XiShiftEulerDenseFiniteSection`
  - `HTGeometry.FiniteBlaschkeProduct`
  - `HTGeometry.SecondOrderConstraintDescent`
- No git used.

Related: `mem:hawking_fzz_neutral_screening_recoil_2026_08_24`, `mem:research/hawking_schwarzschild_jost_ekg_incidence_2026_08_24`.