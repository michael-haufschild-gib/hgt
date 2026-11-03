# F2 — one source window determines Cauchy reflection

- **Stage:** 3-formalized
- **Result:** Actual Cauchy averaging of inputs supported in any positive-length logarithmic interval has dense physical Haar `L²` range. Bounded conjugate-linear compatibility on that interval extends globally and has the same sharp `Re s≥1/4` boundary.
- **Scope:** Actual source convolution and its physical core reflection. This does not identify the weighted Lewis metric or prove the signed Weil form positive.

## Proof

Write `A_s` for normalized Cauchy convolution, `a_s(t)=symbol(2s,it)/Γℝ(2s)`, and `J` for the arithmetic field antiunitary. For every `Re s>0`, the first Gamma factor in `a_s` satisfies

`|Γ(1/2+it/2)|≤sqrt(2π) exp(−π|t|/4)`.

The other factor is bounded by `Γ(Re s+1/2)`. Thus `|a_s(t)|≤C_s exp(−π|t|/4)`. The same bound holds for the conjugate symbol. For arbitrary Fourier `L²` input, Cauchy–Schwarz gives an absolute exponential moment of the output at every rate below `π²/2`. The Fourier–Laplace theorem therefore gives representatives of both `A_s f` and `A_s†f` holomorphic on `|Im z|<π/4`.

Let `P_I` multiply by the indicator of an interval `I=(a,b)`, with `a<b`. If `g` is orthogonal to `A_s P_I(L²)`, then `A_s†g` is orthogonal to every `L²` function supported in `I`. Testing its own interval restriction gives vanishing almost everywhere on `I`. Continuity upgrades this to pointwise vanishing, and the holomorphic identity theorem gives global vanishing. The already proved injectivity of the adjoint yields `g=0`. Hence `A_s P_I` has dense range. Its literal action is integration of the actual Cauchy kernel over `I`.

For a bounded complex-linear `S`, suppose `S A_s f=A_r†f` on interval-supported inputs. Each adjoint row `A_s†S†g−A_r g` has a holomorphic representative and is orthogonal to those inputs. The same local uniqueness argument makes every row zero. Testing against output differences gives `S A_s=A_r†` globally.

Now let bounded conjugate-linear `R` satisfy `R A_s f=A_(s♯)Jf` on interval-supported inputs. Set `S=J R`. The identity `J A_(s♯) J=A_(s♯)†` turns this into the preceding local linear factorization. It extends globally; applying `J` recovers global compatibility of `R`. This argument does not assume that `J` preserves interval support.

The audited global classification now gives existence iff `Re s≥1/4` and identifies every candidate with the unique constructed Cauchy reflection. Its exact norm, action on actual PM core columns, and critical-line antiunitarity remain those of the global theorem.

## Consequence

Shrinking the source interval cannot evade the fixed-Haar reflection obstruction. The positive survivor is dense physical range from every nonempty source interval and a unique global reflection determined by that local compatibility.

## Lean

Module: `RenormalizedIntersectionTheory/MayerScattering/CauchyWindowRangeDensity`.

Endpoints: `mayerCoreMellinFactor_exponential_bound`,
`mayerCauchyHaarOperator_analytic_representative`,
`adjoint_mayerCauchyHaarOperator_analytic_representative`,
`cauchyStripAnalytic_zero_of_local_orthogonality`,
`mayerCauchyWindowOperator_coeFn`, `denseRange_mayerCauchyWindowOperator`,
`mayerCauchy_compatible_on_window_iff_global`,
`mayerCauchy_bounded_window_reflection_iff`, `mayerCauchy_window_reflection_unique`.

Final plain `lake --old env lean` check passed, warning-free. All nine printed
transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
Umbrella import wired.

These interval-supported source inputs are not the paired WTZ `windowLogLift`.
Applying the result to that specific lift requires a separate argument.
