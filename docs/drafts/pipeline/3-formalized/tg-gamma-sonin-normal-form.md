# TG C9.11e — literal Gamma differential on Sonin carriers

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** TG; joint prime–Gamma source construction.

## Exact target

For the existing physical operator
`LΓ = ccmArchimedeanGeometricScatteringLogDifferential`, prove
`LΓ = A₁ + R₁ - 1`, where A and R are the existing even physical and Fourier cutoffs.
Consequently `LΓ Q_b = Q_b LΓ = -Q_b` for `b ≥ 1`.

The source is the literal Gamma scattering multiplier and its Mellin conjugate,
already constructed in `CCMArchimedeanMellinTransport` and
`CCMArchimedeanGeometricSpectralBridge`. Transport is not an open gap.

## Dependency-closed paper proof [PROVED HERE]

The logarithmic cutoff theorem transports A₁ to the negative half-line. The normalized
Mellin transform then gives `M A₁ = (1-P) M`. Fourier–Mellin scattering gives
`M F_even = J UΓ M`. Reflection exchanges the two Hardy halves, so
`M R₁ = UΓ* P UΓ M`. The existing logarithmic differential identity is exactly
`UΓ* P UΓ - P`, hence the claimed normal form. Boundary points have zero Lebesgue measure.
Both cutoffs annihilate every Sonin carrier with aperture at least one.

For `1 ≤ a ≤ b`, the lost layer E=Q_a-Q_b satisfies `E LΓ Q_b=0`.
Thus adding any scalar multiple of the bare Gamma differential to a coherent source
cannot change its lost transition or its retained/lost cubic channel. This tests only
the bare additive proposal, not a product of Gamma and prime scattering phases.

## Strongest positive survivor [PROVED HERE]

For every Schwartz logarithmic kernel g and b≥1,
`A_g LΓ Q_b = -A_g Q_b`, with `A_g = ccmIntegratedScaling (ccmSchwartzLogKernel g)`.
The existing tested Gamma trace-class theorem therefore establishes trace class
of the actual continuum dilation source compressed on the right by Q_b. This exposes
the nontrivial tested Gamma action without replacing it by a scalar trace remainder.

## Log

- 2026-10-02: corpus search and exact source inspection distinguish the already-built
  Mellin transport from the missing joint source construction. New normal-form proof
  is the next test; no numerical computation or RH premise.
- 2026-10-02: `CCMGammaSoninNormalForm.lean` passes the final foreground leaf audit:
  `lake --old env lean GaloisForLFunctions/RHTower/CCM/CCMGammaSoninNormalForm.lean -o
  .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCM/CCMGammaSoninNormalForm.olean`.
  Ten public theorems prove the Hardy reflection, both Mellin cutoff identities,
  Gamma normal form, both Sonin reductions, bare-counterterm invisibility and the
  exact tested continuum trace-class survivor. Wired into RHTower; no umbrella build.
  Separate `/tmp` axiom audit passes for all ten public theorems, with exactly
  `propext`, `Classical.choice`, `Quot.sound`. Formal lint reports eleven unrelated
  unwired modules (the previous ten plus `RoutePTerminalModularPowerSaving`), no
  failure in this new module. No increased heartbeat limit or numerical computation.

## Boundary and next conjecture

The bare additive correction is closed, not route TG. The literal finite spherical
scattering unitary already retains Gamma times every Euler ratio. Its joint
projection differential should transport to `V_S* R₁ V_S + A₁ - 1`, where V_S is
the physical finite Euler-ratio unitary. This comparison is now proved in
`tg-finite-scattering-sonin-normal-form.md`; cofinal ideal control, Hardy cyclic-index
comparison and the sub-unit law remain open.
