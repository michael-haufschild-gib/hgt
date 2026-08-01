# CCM–Julia scale-four innovation tower

- **ID:** CJS4-1
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM (Lean)
- **Source:** whole-corpus synthesis of HTGeometry Julia/Gamma/Fourier theory, critical
  successor/log-Beta Dirichlet generator, and RHTower CCM block-subdivision source
- **Statement:** critical centered Dirichlet Lévy density is an exact positive scale-four tower of
  Julia innovations, and is exactly the two-sector completion of CCM odd block-Fock Gamma density.

## Goal

Expose unused joint structure across independent HTGeometry mechanisms before testing it against
RHTower's exact first-clock obstruction. This theorem supplies a positive multiscale resolution of
the complete CCM continuous Gamma density. It does not assume or prove RH.

## Theorem

For `x>0`, define

```text
D(x) = 1/(2 sinh x),
J(x) = D(x)-4D(4x),
rho(t) = 1/(2t sinh(pi t/4))-2/(t sinh(pi t)),
A(h) = exp(-h/2)/(1-exp(-2h)).
```

Here `D` is the critical centered symmetric log-Beta/Dirichlet radial Lévy density, `rho` is the
Gamma–Julia compression Lévy density, and `A` is the literal CCM archimedean density. Then:

```text
J(pi t/4) = t rho(t) > 0                                      (CJS4.1)

D(x) = sum_(0<=j<n) 4^j J(4^j x) + 4^n D(4^n x)              (CJS4.2)

D(x) = (1+exp(-2x)) A(2x)                                    (CJS4.3)

J(x) = (1+exp(-2x))A(2x)-4(1+exp(-8x))A(8x) > 0.             (CJS4.4)
```

If `O(r)=sum_(j>=0)r^(4j+1)=r/(1-r^4)` is the CCM odd block-Fock radial sum, then

```text
D(x)=(1+exp(-2x))O(exp(-x)).                                  (CJS4.5)
```

Thus `D` is exactly the union of the `1 mod 4` and `3 mod 4` odd Gamma sectors, while `J` is its
strict scale-four innovation.

Finally, for `L,h>0`, the complete first-clock continuous reflection gap has exact coordinate

```text
G_L(h)
 = D(h/2)/(1+exp(-h))
   -D((h+L/2)/2)/(1+exp(-(h+L/2)))
   +2[cosh((h+L/2)/2)-cosh(h/2)].                             (CJS4.6)
```

Applying `(CJS4.2)` separately to both `D` terms gives a finite Julia-innovation resolution at
every scale with an exact tail, not an asymptotic heuristic.

## Complete paper proof

Put `v=pi t/4`. Direct substitution gives

```text
t rho(t)=1/(2sinh v)-2/sinh(4v)=D(v)-4D(4v)=J(v).
```

The already proved hyperbolic identity

```text
sinh(4v)=4 sinh(v) cosh(v) cosh(2v)>4 sinh(v),  v>0,
```

implies `rho(t)>0`; hence `(CJS4.1)`.

For `(CJS4.2)`, the case `n=0` is tautological. If the identity holds at `n`, substitute

```text
D(4^n x)=J(4^n x)+4D(4^(n+1)x).
```

Multiplication by `4^n` adds the `j=n` innovation and gives the `n+1` identity. This proves the
finite telescope without any limit interchange.

Using `2sinh x=exp(x)-exp(-x)` gives

```text
D(x)=exp(-x)/(1-exp(-2x)).
```

Since `(1-exp(-4x))=(1-exp(-2x))(1+exp(-2x))`,

```text
(1+exp(-2x))A(2x)
 =(1+exp(-2x))exp(-x)/(1-exp(-4x))
 =D(x),
```

which proves `(CJS4.3)`. Substitution at `x` and `4x` proves `(CJS4.4)`. Existing block-Fock
identity `O(exp(-x))=A(2x)` proves `(CJS4.5)`. Solving `(CJS4.3)` for `A(h)` and substituting in
the definition of CCM Gamma–polar reflection gives `(CJS4.6)`.

## Hostile RH test and no-go closure

The theorem resolves the continuous Gamma side only. Literal CCM first-clock source is

```text
continuous half-wave budget + aligned prime mass - counter-phased prime mass.
```

Neither `(CJS4.1)` nor `(CJS4.2)` changes von Mangoldt atoms or their sine phases. Moreover, the
reflected term is a difference of two normalized innovation towers; positivity of every
innovation value does not sign the difference of its two translated values. Therefore no
termwise argument from Julia innovation positivity can dominate counter-phased prime mass.

- **Exact killing mechanism:** positive scale-four decomposition is confined to continuous
  Gamma density; first-clock arithmetic obstruction is a separate signed prime-power functional.
- **Strongest positive survivor:** exact positive multiscale resolution `(CJS4.2)` of the full
  critical Dirichlet/CCM Gamma density and exact source coordinate `(CJS4.6)`.
- **New insight:** Julia equilibrium law is not an auxiliary damping factor. It is the canonical
  innovation generated when the complete odd critical Gamma ladder is subdivided by four. CCM's
  `1 mod 4` Fock grading is one sector of that same ladder.
- **Remaining open core:** a source-specific cross-term or comparison theorem coupling the
  innovation-resolved continuous budget to the actual counter-phased von Mangoldt functional.

## Novelty audit

Parent mathematics includes hyperbolic selfdecomposable laws and positive-definite/infinitely
divisible hyperbolic kernels:

- Jurek–Yor, *Selfdecomposable Laws Associated with Hyperbolic Functions*,
  <https://arxiv.org/abs/1009.3542>.
- Hiai–Kosaki–Petz–Ruskai, *Families of completely positive maps associated with monotone
  metrics*, <https://arxiv.org/abs/1212.1337>.

Exact-form searches found no indexed source for the corpus-specific triple identification
`Dirichlet scale-four innovation = Gamma–Julia Lévy density = weighted CCM block-Fock residue`, or
for the resulting first-clock coordinate `(CJS4.6)`. This is a noncollision report, not a priority
claim. External expert audit remains required.

## Lean certificate

Unconditional modules:

```text
formal/GaloisForLFunctions/HTGeometry/JuliaDefectSpectralEquilibrium.lean
formal/GaloisForLFunctions/RHTower/CCMFirstClockJuliaScaleFourTransfer.lean
```

Formalized capstones:

- `juliaScaleFourInnovationDensity_eq_rescaledLevy`
- `juliaScaleFourInnovationDensity_pos`
- `criticalDirichletLevyRadialDensity_scaleFour_telescope`
- `criticalDirichletLevyRadialDensity_eq_ccmArchimedean`
- `criticalDirichletLevyRadialDensity_eq_oddBlockFock`
- `juliaScaleFourInnovationDensity_eq_ccmResidue`
- `ccmArchimedean_scaleFour_strictContraction`
- `ccmArchimedean_scaleFour_innovation_telescope`
- `ccmFirstClockContinuousReflectionGap_eq_dirichletPolar`

Both umbrellas are wired. Direct Lean checks and final module build are green. All eight capstones
have axiom set exactly `[propext, Classical.choice, Quot.sound]`. Global lint reaches this work but
fails on unrelated umbrella gap
`GaloisForLFunctions.HTGeometry.ProjectiveHorizonActualSchwarzianDiamond`; no forbidden declaration
occurs in either new module.

## Gates

- [x] 0 → 1: exact source objects, falsifiable transfer, no RH premise
- [x] 1 → 2: dependency-closed proof above
- [x] 2 → 3: direct checks and final build green; axiom-clean; umbrellas wired
- [ ] 3 → 4: external novelty review and standalone exposition

## Log

- 2026-08-01 — Derived theorem from whole HT reservoir; hostile test separated continuous
  innovation positivity from signed prime-power obstruction; formalized HT and RHT identities.
- 2026-08-01 — Final `lake build` green at 9285/9285. Eight capstone axiom audits return only
  standard mathlib axioms. Global lint blocked by unrelated HT umbrella reachability gap recorded
  above.
