# Arithmetic Electrostatics of the Zero Divisor programme

- **ID:** aes
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2710/obstacles-summary.md §4 ("arithmetic electrostatics of the zero divisor")
- **Statement:** Potential theory of the zero divisor of `ξ` and of the torsion of the characteristic
  circle: energy, field, renormalized self-energy and reflection pairing of one logarithmic
  potential; equilibrium, quantization, adjunction, stability, and the inequalities that would turn
  detection into exclusion.

## Goal
Lean folder `formal/GaloisForLFunctions/ArithmeticElectrostatics/`, umbrella
`ArithmeticElectrostatics.lean` (wired into `MainTheorems.lean`), foundational README. Answer the
twelve questions of §4.4 by theorems, sharp equivalences or located gaps; build the tools of §4.5.

Territory: RHTower owns the transverse chain; ACP owns terminals, outward rays, `fieldAt`,
`xiTransverseField`, the source field; AET owns torsion orbits and energies; APol owns `W`, `D`, `Δ`;
CDG owns `heckeDefect`, `depthSecondMoment`. AES imports them. A second agent contributes the global
damped source-work modules (`ReflectedTransverseWork`, `TheSelbergWorkExhaustsTheTransverseEnergy`).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proofs for the pillars below
- [x] 2 → 3  pillars ES1–ES15 in Lean, each module audited with `lake --old env lean`

## Pillars and modules

| Pillar | Module | Status |
|---|---|---|
| ES1 virial laws | `TheVirialLawsOfAFiniteConfiguration` | Lean |
| ES2 equilibrium = critical line, quanta, gap, maximum principle | `TransverseEquilibriumIsTheCriticalLine` | Lean |
| ES3 energy of the divisor: `0` ⇔ RH ⇔ `< 1`; finite ⇔ finite off-line index; work = energy | `TheTransverseEnergyOfTheZeroDivisor` | Lean |
| ES4 global damped source work exhausts the energy | `ReflectedTransverseWork`, `TheSelbergWorkExhaustsTheTransverseEnergy` | Lean (other agent) |
| ES5 window selection | `QuantizationTurnsWindowsIntoPoints` | Lean |
| ES6 Hecke defect = moment of inertia | `TheHeckeDefectIsTheMomentOfInertia` | Lean |
| ES7 field threshold `1`, `√(2c log γ)` | `TheFieldLawHasAThreshold` | Lean |
| ES8 external field = prime sum; anti-alignment at zero ordinates | `TheExternalFieldIsAPrimeSum` | Lean |
| ES9 renormalized square, Selberg `Λ₂`, `L(Λ₂) = ζ″/ζ` | `TheRenormalizedSquareIsSelbergsSource` | Lean |
| ES10 torsion self-intersection, Leibniz, cover formula, conjugation | `TheSelfIntersectionOfATorsionOrbit` | Lean |
| ES11 counterterm `Θ(log N)` | `TheTorsionCountertermIsLogarithmic` | Lean |
| ES12 arithmetic point carries the divergence | `TheArithmeticPointCarriesTheDivergence` | Lean |
| ES13 power maps are similitudes of the Abel energy | `PowerMapsAreSimilitudesOfTheAbelEnergy` | Lean |
| ES14 Fekete stability of the circle | `TheTorsionIsTheStableEquilibriumOfTheCircle` | Lean |
| ES15 affine invariance; gauge twists of the source | `QuantizationTurnsWindowsIntoPoints` | Lean |
| ES16 energy of a zero `O(log γ)` | `TheEnergyOfAZeroIsLogarithmic` | Lean |
| ES17 large values / alignment law at zero ordinates | `LargeValuesAtZeroOrdinates` | Lean |
| ES18 stability law at atomic resolution | `TheStabilityLawAtAtomicResolution` | Lean |
| ES19 gauge margin of the source | `TheGaugeMarginOfTheRenormalizedSource` | Lean |
| ES11 (prime side) atomic Weil prime form `Θ(log N)` | `TheWeilPrimeFormOnAtomsIsLogarithmic` | Lean |
| ES20 power saving for aligned zero ordinates (higher moments) | `HigherMomentsAtZeroOrdinates` | Lean |
| ES21 gauge invisibility at atomic resolution; stability law for every sign twin | `TheGaugeIsInvisibleAtAtomicResolution` | Lean |

## Open (RH-strength or beyond the present inputs)
- Field law: arithmetic upper bound for the field below `max(1, √(2c log γ))`.
- Stability law at the spacing scale `w ≍ 1/N` (proved below `N^{−O(1)}`, ES18): RH in adjunction form.
- Aligned ordinates (power-sparse, ES20) against zero density at depth `δ`: the report's Q1 proper.
- Form-level gauge margins on spacing-scale tests (zero at atomic resolution, ES21).
- Alignment inside the strip (Q1 of the frontier); coupled class at the centre; fibre selection.

## Key paper facts
- Transverse virial: `Σ_j m_j (Re z_j − c) Re E_j = ½ Σ_{j≠k} m_j m_k (Re z_j − Re z_k)²/|z_j − z_k|²`.
- `f″/f = (f′/f)² + (f′/f)′`; at a zero of order `m`: double pole `m(m − 1)`, residue `2m R(ρ)`.
- `I(n, n) = φ(n) log n − (φ ⋆ Λ)(n)`; `φ ⋆ Λ = (φ ⋆ μ) ⋆ log` obeys the Leibniz rule on coprime orders.
- `T_r(μ_A, μ_B) = gcd(A, B) log 1/(1 − r^{lcm(A,B)})` (orthogonality of roots of unity).
- Fekete: `|det V(z)| ≤ N^{N/2}` by Hadamard for unimodular entries.
- `2cosh(ax) − 2 ≤ a²(2cosh x − 2)` for `a² ≤ 1` (termwise in the series).

## Log
- 2026-10-27 — created; README first draft; ES1–ES3, ES7, ES9–ES11 formalized.
- 2026-10-27 — ES5, ES6, ES8, ES12–ES15 formalized; README rewritten with answers to the twelve questions.
- 2026-10-27 — ES16–ES19 and the atomic Weil prime form formalized; README updated.
- 2026-10-27 — ES20, ES21 formalized; README updated.
