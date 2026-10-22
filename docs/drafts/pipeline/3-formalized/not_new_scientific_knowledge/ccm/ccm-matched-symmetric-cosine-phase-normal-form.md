# Matched CCM symmetric cells have an exact cosine-phase normal form

- **ID:** `ccm-matched-symmetric-cosine-phase-normal-form`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [INTERNAL NOVELTY] [BRIDGE] [NOT AN RH PROOF]`
- **Source:** `rh-current-frontier-map.md`, Route O; corpus declarations
  `ccmActualHeadMatchedSymmetricCellResidual`,
  `ccmRestrictedWeilDangerousSubspace_eq_negativeSourceRemainder`, and
  `sourceHead_prime_overcompensation_of_nonpositive`
- **Statement:** Every mass-matched symmetric prime--polar residual is exactly a negative cosine
  phase average against a nonnegative radial defect profile. The surviving sign is orientation,
  not the difference of two unrelated nonnegative budgets.

## Goal

Expose the exact sign carrier left by the corpus's mass-matched prime--polar decomposition, without
discarding phase. This is a source-pure bridge: it uses the same actual Gamma head, literal
von-Mangoldt atom, literal matched polar cell, and unitary Fourier density already present in Route
O. It does not assume restricted-Weil positivity, RH, a zero-free region, or a spectral model of
the zeros.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, exact corpus parents, complete attack
- [x] internal novelty audit: no declaration or card gives this residual normal form
- [x] external falsity/prior-art audit: Suzuki 2022/2026 and CCM 2025 do not contain the
  mass-matched cell construction or this identity
- [x] paper proof dependency-closed
- [x] 1 → 2 fully-proven: hostile sign/constant audit recorded
- [x] 2 → 3 formalized: Lean theorem, targeted compile, axiom audit, umbrella import

Next research target: connect finite source-head overcompensation to the aggregated phase profile
on the exact one-sided dangerous sector.

## Definitions

For one actual head `f`, put

```text
g(xi)   = (fourierUnitary f)(xi),
E_f(h)  = integral_xi (2 - 2 cos(2 pi h xi)) |g(xi)|^2 dxi,
J_f(s,r)= integral_xi (2 - 2 cos(2 pi s xi))
                         (2 - 2 cos(2 pi r xi)) |g(xi)|^2 dxi.
```

For a natural label `n`, write

```text
s_n   = log n,
A_n   = exp(s_n/2),
rho_n = 2 arsinh(criticalMellinAtomWeight(n)/(4 A_n)).
```

The existing matched symmetric residual is

```text
R_n(f)=integral_[0,rho_n] A_n cosh(r/2) (J_f(s_n,r)-2E_f(r)) dr.       (1)
```

Define the nonnegative radial phase profile

```text
P_n(xi)=integral_[0,rho_n]
          A_n cosh(r/2) (2-2 cos(2 pi r xi)) dr >= 0.                 (2)
```

## Theorem A — nested cosine-phase normal form

For every `n` and `f`,

```text
R_n(f)=integral_[0,rho_n] A_n cosh(r/2)
          integral_xi [-2 cos(2 pi s_n xi)
                        (2-2 cos(2 pi r xi))] |g(xi)|^2 dxi dr.       (3)
```

### Proof

The Fourier formula for `E_f(r)` and the definition of `J_f(s,r)` have integrable densities.
Therefore linearity of the Lebesgue integral gives

```text
J_f(s,r)-2E_f(r)
 =integral_xi {[(2-2cos S)-2](2-2cos R)} |g|^2 dxi
 =integral_xi [-2cos S (2-2cos R)] |g|^2 dxi,                        (4)
```

where `S=2 pi s xi` and `R=2 pi r xi`. Substitute `(4)` into `(1)` pointwise in `r` and use
congruence of the finite interval integral. No Fubini interchange is used. `QED`

## Theorem B — single spectral-average normal form

For every `n` and `f`,

```text
R_n(f)=-2 integral_xi cos(2 pi s_n xi) P_n(xi) |g(xi)|^2 dxi.        (5)
```

Moreover `P_n(xi)>=0`, `P_n(-xi)=P_n(xi)`, and `P_n(0)=0`.

### Proof

The integrand before exchanging order is jointly measurable. On `0<=r<=rho_n`,

```text
| -2 A_n cosh(r/2) cos(2 pi s_n xi)
      (2-2cos(2 pi r xi)) |g(xi)|^2 |
 <= 8 A_n cosh(r/2) |g(xi)|^2.                                    (6)
```

The first factor is integrable on the finite interval because it is continuous; the second is
integrable because `g` is an `L2` vector. Product domination proves joint integrability. Fubini
applied to `(3)` gives `(5)` after pulling the `xi`-constant cosine and density through the `r`
integral. Nonnegativity follows from `A_n>0`, `cosh>=0`, and `2-2cos>=0`. Evenness follows from
evenness of cosine in `xi`; the value at zero follows from `2-2cos 0=0`. `QED`

## Theorem C — finite-block phase interference law

For a finite label set `F`, define the signed symbol

```text
S_F(xi)=sum_(n in F) cos(2 pi log(n) xi) P_n(xi).
```

Then

```text
sum_(n in F) R_n(f) = -2 integral_xi S_F(xi) |g(xi)|^2 dxi.          (7)
```

The density in `(7)` is integrable, `S_F(-xi)=S_F(xi)`, and `S_F(0)=0`.  The proof applies
Theorem B atomwise, proves each phase-profile density integrable from the same product majorant,
and exchanges only a finite sum with the integral.  Thus finite-head sign is phase interference
between arithmetic labels, not any atomwise sign. `QED`

## Hostile audit

1. **Factor audit.** `[(2-2c_s)-2](2-2c_r)=-2c_s(2-2c_r)`; coefficient is `-2`, not `-4`.
2. **Sign audit.** Profile is nonnegative, but `cos(2 pi log(n) xi)` changes sign. Thus `(5)` does
   not assert `R_n(f)>=0` or `R_n(f)<=0`.
3. **Degenerate labels.** For `criticalMellinAtomWeight(n)=0`, `rho_n=0`, so both sides vanish.
   No prime-power premise is required.
4. **No hidden point evaluation.** Only the `L1` density `|g|^2` occurs; no representative value of
   an `L2` class is asserted outside an integral.
5. **No scalarization.** The cosine phase is retained. Replacing it by its absolute value would
   recreate the failed coherent-square route.

## New insight

The coherent Gamma-square no-go and the matched signed survivor are two faces of one universal
principle:

```text
positive radial defect magnitude × arithmetic cosine orientation
```

is the irreducible local carrier. Completion by separate squares deletes the cosine orientation
and therefore cannot see the one-sided source-remainder eigenspace. Route O's next exact task is not
another nonnegative norm estimate; it is an arithmetic phase-order theorem for the aggregated
profiles `P_n` on finite source heads forced by nonpositive restricted-Weil directions.

## Novelty audit

### Internal

`scripts/formal_tools.py research` found the residual definition and its signed split, but no
Fourier/cosine normal form for `ccmActualHeadMatchedSymmetricCellResidual`. Existing code explicitly
warns that the cosine cancellation must remain intact. This card supplies that missing exact form.

### External primary sources

- Suzuki, *Aspects of the screw function corresponding to the Riemann zeta function*,
  arXiv:2206.03682: screw-kernel positivity criteria and unconditional local results, but no
  mass-matched prime--polar cells.
- Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096: continuous-kernel and
  restricted-form operator framework, but no matched-cell cosine profile.
- Connes--Consani--Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755: finite-prime spectral
  triples and conjectural convergence, but no identity `(3)` or `(5)`.

Verdict: internal exact bridge appears new to project and absent from audited primary literature.
It is classified `[BRIDGE]`, not headline scientific novelty, because its proof is an exact
Fourier-algebra/Fubini reduction once the project-specific matched cell has been constructed.

## Lean certificate

Formalized in
`formal/GaloisForLFunctions/RHTower/CCM/CCMActualHeadMatchedCosinePhaseNormalForm.lean`:

- `ccmActualHeadSymmetricTransportRebate_sub_two_translationDefect_eq_cosinePhase`;
- `ccmActualHeadMatchedSymmetricCellResidual_eq_nestedCosinePhase`;
- `ccmActualHeadMatchedCosinePhaseProfile_nonneg`;
- `ccmActualHeadMatchedCosinePhaseProfile_neg`;
- `ccmActualHeadMatchedCosinePhaseProfile_zero`;
- `integrable_ccmActualHeadMatchedCosinePhase_prod`;
- `ccmActualHeadMatchedSymmetricCellResidual_eq_cosinePhaseProfile`;
- `integrable_ccmActualHeadMatchedCosinePhaseProfile_mul_density`;
- `ccmActualHeadMatchedCosinePhaseFiniteSymbol`;
- `integrable_ccmActualHeadMatchedCosinePhaseFiniteSymbol_mul_density`;
- `ccmActualHeadMatchedCosinePhaseFiniteSymbol_neg`;
- `ccmActualHeadMatchedCosinePhaseFiniteSymbol_zero`;
- `ccmActualHeadMatchedSymmetricFiniteBlock_eq_cosinePhaseFiniteSymbol`.

Verification on 2026-08-21:

- `lake env lean GaloisForLFunctions/RHTower/CCM/CCMActualHeadMatchedCosinePhaseNormalForm.lean` passed;
- targeted `lake build GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedCosinePhaseNormalForm`
  built only the required target and dependency cache; no umbrella build was run;
- `/tmp` `#print axioms` audit reports exactly `propext`, `Classical.choice`, and `Quot.sound`
  for every theorem;
- module contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration;
- imported by `formal/GaloisForLFunctions/RHTower.lean`, which was intentionally not built;
- repository lint found no defect in this module and confirms it is reachable; its global exit is
  nonzero only because five pre-existing unrelated modules are unreachable from their umbrellas.

## Log

- 2026-08-21 — created in Stage 1 after corpus search exposed stale Route O frontier and exact
  one-sided source-remainder reduction; paper proof and novelty audit completed.
- 2026-08-21 — promoted through Stages 2 and 3 after hostile audit, targeted Lean compile,
  target-only `.olean` build, axiom audit, forbidden-declaration scan, and umbrella wiring.
- 2026-08-21 — finite-block conjecture survived: formalized aggregate phase-interference law `(7)`
  and audited all added declarations against the same axiom and target-build gates.
