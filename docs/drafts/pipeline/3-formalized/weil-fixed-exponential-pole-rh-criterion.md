# Exact RH criterion from the two literal exponential poles

- **Stage:** 3-formalized
- **Lean:** `CCMRestrictedWeilPoleBoundaryBounds`, `CCMRestrictedWeilPoleDiagonalBounds`, `CCMRestrictedWeilPoleCompressionRHCriterion`; 23 public theorems and three definitions, wired into `RHTower`.
- **Closed chain:** literal prime–Gamma pole matrix → uniform boundary/diagonal bounds → integrated Chebyshev deficit at square-root scale → bounded actual unit-Riesz Chebyshev resolvent → analytic continuation → mathlib RH. The reverse direction follows from smooth actual-source positivity under RH and density in the complete Weil form domain.
- **Open mathematical obligation:** prove the explicit matrix inequality at every aperture. An RH equivalence is proved; RH itself is not proved or disproved.

## Corpus-driven conjecturing loop
1. **Candidate:** bound the boundary logarithms by their elementary local/tail estimates. The corpus already has a better admitted majorant: the screw-tail half moment, with exact integral `log 2+pi/2`.
2. **Conjecture:** scalar entropy controls each logarithmic endpoint by that moment. **Proved:** `x log x≥x-1`, applied to `1±u`, gives the needed bound. Translation into the physical aperture preserves its admitted integral.
3. **Conjecture:** the exact diagonal cancellation leaves only square-root-scale terms. **Proved for every positive aperture:** boundary mass, Mertens, Chebyshev, and elementary exponential bounds give one explicit uniform constant.
4. **Conjecture:** the unweighted integrated deficit controls the corpus's unit-Riesz resolvent. **Proved:** absolutely continuous integration by parts converts the primitive to the existing weighted Chebyshev ray integral. Its exact `2/3` past-tail correction survives the transfer.
5. **Candidate:** this proves only sufficiency of the fixed two-pole test. **Stronger survivor:** the existing smooth-source identity and dense form core also give the converse. The fixed physical family is exactly complete for RH.

The reused scalar inequality and unit-Riesz analytic theorem are not claimed as new mathematics. The proved identification, uniform admission, and exact landing concern the literal physical pole matrix, retaining every prime power and Gamma term.

## Uniform estimates
Use notation of [the exact matrix package](weil-two-pole-matrix-and-integrated-prime-error.md): `A=Q(p_+)`, `C=Re Q(p_+,p_-)`, `kappa=-EulerGamma-log(2pi)`, and boundary masses `B_0`, `B_1`. Set

`K_B=2log 2+pi+1`,

`K_A=|kappa|+K_B+4+2(log 4+5)+2(log 4+4)`,

`K_D=K_A+K_B+2(|kappa|+log 4+5)+1`.

All are explicit finite constants; `K_A,K_D>0`. For every `a>0`, unconditionally,

`0≤B_0(a)≤K_B`,

`0≤B_1(a)≤exp(a)B_0(a)≤K_B exp(a)`,

`|A(a)|≤K_A exp(a)`.

For the admitted physical deficit `D(a)=integral_[-a,a](exp(a-x)-psi(exp(a-x))) dx`,

`|C(a)|≤A(a)  =>  |D(a)|≤K_D exp(a)`.

The diagonal's exact cancellation is essential to this estimate; bounding the uncancelled radius terms separately would lose a factor of `a`.

## Exact arithmetic handoff
Define the ordinary logarithmic primitive

`P(T)=integral_0^T [exp(t)-psi(exp(t))] dt`.

The physical-coordinate identity is `D(a)=P(2a)`. Thus all-aperture pole positivity gives `|P(T)|≤K_D exp(T/2)` for every `T≥0`.

Let `J(T)` be the corpus's `unitRieszChebyshevRayIntegral`. The exact integration-by-parts identity is

`J(T)=-exp(T/2)P(T)+(1/2)integral_0^T exp(t/2)P(t)dt`.

The primitive is absolutely continuous because the Chebyshev deficit is interval-integrable. No derivative of the discontinuous prime-counting function is taken. If `|P(T)|≤B exp(T/2)` on `T≥0`, then

`|J(T)|≤(3/2)B exp(T)`.

The existing identity `J(T)=exp(T)C_res(T)+2/3` therefore gives

`|C_res(T)|≤(3/2)B+2/3`.

The corpus theorem `riemannHypothesis_of_bounded_criticalMellinChebyshevResolventSource` closes analytic continuation of the actual regularized critical Mellin defect and proves mathlib RH.

## Exact equivalences and witness
The leaf proves these premise-free equivalence statements:

- `RiemannHypothesis ↔ ∀ a>0, |C(a)|≤A(a)`.
- `RiemannHypothesis ↔` nonnegativity of both actual even and odd exponential-pole tests at every aperture.
- `RiemannHypothesis ↔ ∃ B≥0, ∀ T≥0, |P(T)|≤B exp(T/2)`.
- The same fixed-pole criterion with `A,C` fully expanded into their exact prime–Gamma expressions (`riemannHypothesis_iff_primeGammaPoleInequality`).

The converse uses the existing equality between the actual restricted-Weil quadratic on smooth sources and Suzuki's form of the derivative. RH makes the latter nonnegative. The continuous quadratic extends that sign through the proved dense smooth source core to every complete form vector, including the pole plane.

False RH therefore forces an actual aperture and one of the two literal parity poles with negative full Weil energy. This is an arithmetic source witness, not a generic Hermitian countermodel. Its existence under false RH does not determine the actual sign.

## Verification
- Foreground scratch checks passed with `lake env lean /tmp/hgt-pole-bounds.sy3Ahd/Boundary.lean`, then `Diagonal.lean`, then `Resolvent.lean`.
- Named final audits passed with `lake --old --log-level=error build GaloisForLFunctions.RHTower.<module>` for each of the three leaves. No full or umbrella build.
- `lake env lean /tmp/hgt-pole-bounds.sy3Ahd/Axioms.lean` audited all 23 public theorems and three definitions: exactly `[propext, Classical.choice, Quot.sound]`, with no extra axiom or oracle.
- The same scratch file checked the equivalence directly against `_root_.RiemannHypothesis` and printed its actual `riemannZeta` zero definition.
- `python3 scripts/formal_tools.py lint` passed, with existing large-file warnings. `git diff --check` passed; process inspection found no remaining Lean or Lake process.
- No numerical experiments, remote computation, background builds, or commits.

## Current frontier
Only the all-aperture explicit prime–Gamma sign remains in this fixed-family chain. Boundary integrability, uniform estimates, coordinate transport, resolvent normalization, and both directions of the RH equivalence are closed. The earlier constrained-ground and finite-head routes remain available; none is retired by this criterion.
