# Actual Maass directions and the nodal reversal obstruction

- **ID:** SELBERG-SOURCE-DIRECTIONS-NODAL-REVERSAL
- **Stage:** 3-formalized.
- **Parent:** [Selberg conjecturing loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 27.
- **Selberg status:** Unproved. No nonnegative lower bound for the combined core/Bessel form is obtained.

## Conjecture, failure, and replacement

Whole-corpus queries `weighted Poincare`, `variance mean`, `zero mean sign`, `normalized direction`, `cosine mean`, and `weighted derivative energy` suggested retaining the normalized congruence-family direction instead of the scalar norm alone. Source reads of `HedenmalmCriticalFeatureAliasVariancePhaseSaving` and `CesaroSignRecurrence` supplied signed-mean separation arguments. `OccupationVacuumAnomalyReciprocity` supplied a normalization mechanism retaining the raw norm. `CosinePolynomialPurchaseCap` supplied exact periodic cosine integrals for a symbolic test. These modules supplied ideas; their unrelated source assumptions and broad imports were not transferred.

**Conjecture tested:** a smooth nonzero periodic zero-mean profile must have positive integrated radial-subtracted derivative energy.

**Failure:** for a real differentiable profile `h`, define

`R_h(x) = (h'(x) - (h²)'(x)/(2 h(x)²) * h(x))²`.

Where `h(x) != 0`, the ordinary product rule makes `R_h(x)=0`. At a zero it equals `h'(x)²`. For `h(x)=cos(x)`, the nodal set is countable, so the residual is zero almost everywhere and genuinely Lebesgue integrable. It has integral zero on every compact interval, although `R_h(pi/2)=1`. Meanwhile cosine is smooth and period `2*pi`, has zero mean over that period, and squared mass `pi>0`. Its values at zero and pi have opposite signs.

This is a failure of the stated smooth periodic zero-mean shortcut. The toy is not claimed to be a Maass eigenform, cuspidal, or inversion invariant. It does not refute an estimate using those additional actual-source constraints.

## Exact actual-source survivor

Let `F_q(z)` be the actual finite congruence family from cycle 24, `D(z)=sum_q |F_q(z)|²`, `rho(z)=sqrt(D(z))`, and `u_q(z)=F_q(z)/rho(z)`, with zero division at common zeros. Then:

1. `rho*u_q=F_q` everywhere. At `D>0`, `sum_q |u_q|²=1`. For every integral modular matrix `A`, `u_q(A*z)=u_(q[A])(z)`; normalization preserves the actual permutation action, including the side and inversion transformations.
2. On `D>0`, the normalized components are differentiable and
   `rho*partial_v u_q = partial_v F_q - c_v F_q`, where `c_v=(partial_v D)/(2D)`.
   Consequently the previously retained residual is exactly
   `R_v(c_v)=D*sum_q |partial_v u_q|²`.
   No differentiability of `u` at common zeros is asserted.
3. For an actual exceptional Maass source, every component has zero complex mean on every horizontal interval of length `N+1`. Hence the exact normalized constraint is `integral rho*u_q=0`.
4. At every positive source point `z`, the amplitude integral on the centered level period at height `Im(z)` is strictly positive. The scalar amplitude therefore does not inherit the source's vanishing constant term.
5. Write `C(z,w)=Re sum_q F_q(w)*conj(F_q(z))`. For every `z` with `D(z)>0`, there is a point `w` at the same height and within the centered level period such that `C(z,w)<0`. Thus `D(w)>0` and
   `sum_q |u_q(w)-u_q(z)|² > 2`.
   Original nonvanishing supplies such a pair without an additional existence assumption.
6. Fix a positive source point `z` and write `d(z,w)²=sum_q |u_q(w)-u_q(z)|²`. The exact identity
   `rho(w)*d(z,w)² = 2*rho(w) - 2*C(z,w)/rho(z)`
   holds even when `D(w)=0`. The weighted squared-chord slice is consequently continuous across common zeros and integrable on compact intervals. On every horizontal level period,
   `integral rho(w)*d(z,w)² = 2*integral rho(w)`.

The last identity is an exact weighted oscillation invariant, rather than a lower bound for the integral of angular derivatives. It remains meaningful through the nodal reversals exposed by the failed conjecture.

## Dependency-closed paper proof

At a trace zero each nonnegative summand of `D` is zero. This proves componentwise vanishing and exact reconstruction at zeros. Elsewhere cancel the nonzero square root. Summing the normalized squared norms and using `rho²=D` proves unit normalization. Actual source pullback covariance permutes the numerators and modular trace invariance preserves the denominator.

On the positive-density locus, C² source regularity gives differentiability of `rho` and of division by it. Differentiate `F_q=rho*u_q`, use the established derivative `partial_v rho=(partial_v D)/(2*rho)`, and cancel `rho²=D`. Taking squared norms and summing gives the exact residual identity.

Apply the already proved actual exceptional constant-term theorem to each translated Maass source. Its level periodicity shifts the zero integral to every level period. Exact reconstruction gives the weighted direction mean without any regularity assumption on unweighted direction at zeros.

For fixed `z`, correlation is continuous along every positive-height slice, and finite summation plus real-part linearity shows its period integral is zero. Its value at `z` is `D(z)>0`. If correlation were nonnegative throughout the centered period, continuity and positivity at that interior point would force its integral to be strictly positive, a contradiction. At the resulting negative point, the source cannot vanish. Divide correlation by the two positive amplitudes, and apply the unit-vector identity `d²=2-2*Re sum u(w)*conj(u(z))`; this gives `d²>2`. Original nonvanishing supplies a positive initial point. The same continuous-positive-integral argument gives strict positivity of the amplitude mean.

Multiply the unit-vector chord identity by `rho(w)` and use exact reconstruction. At a common zero both sides vanish, so the formula extends there without differentiating the direction. Its right side is continuous in the horizontal coordinate. Integrate that formula and use the zero correlation mean; all terms are integrable by continuity. This proves the weighted squared-distance identity.

For the toy, differentiate `h²` to `2*h*h'`. Away from zeros the real residual cancels; at zeros its radial subtraction vanishes. The exact cosine-zero classification makes its nodal set the range of a map from the integers, hence countable and Lebesgue null. The residual is equal almost everywhere to zero, proving genuine integrability and zero integral. Exact cosine integrals give its zero mean and positive squared mass; its derivative at `pi/2` gives residual one there.

## Lean implementation and audit

Both complete scratch checks and direct source checks passed without warnings. Both narrow modules are wired into `RHTower` and indexed.

- `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.SelbergMaassTraceDirection` passed, rebuilding only its named target (7.1 seconds). Log: `/tmp/selberg_trace_direction_build.log`.
- `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.SelbergNodalAngularToy` passed, rebuilding only its named target (1.7 seconds). Log: `/tmp/selberg_nodal_angular_build.log`.
- All 35 public declarations passed `#print axioms` through `lake env lean /tmp/selberg_direction_nodal_axioms.lean`: no missing reports, no errors, and only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. Log: `/tmp/selberg_direction_nodal_axioms.log`.
- Index refresh passed. Latest authoritative repository lint failed only on the unrelated unwired `HTGeometry.FokasLenellsSobolevEnergy`; neither new Selberg module is named in an error. Logs: `/tmp/selberg_direction_nodal_index.log`, `/tmp/selberg_direction_nodal_lint.log`.
- All Lean invocations were serialized foreground runs. No full or umbrella build ran. Tracked and new task-file whitespace checks passed; indexed searches retrieve all three capstones. Every task-owned handle is terminal, and the final process scan found no Lean/Lake executable. This task made no commit or push.

## Wider corpus follow-up

The user's renewed instruction is to use wider searches and remember that multiple terms default to AND. Discovery now explicitly uses `--any`, with separate narrowing only after finding a concrete mechanism. The late-cycle OR batches were `nodal chord oscillation variance` (2,922 matches across 667 modules), `coarea Cheeger conductance resistance` (709 across 92), `permutation transport holonomy expansion` (11,622 across 3,251), and OR batches of the phrases `effective resistance`, `Dirichlet principle`, `Poincare`, then `spectral gap`, `boundary transport`, `zero mean`. Result counts describe the searched corpus; they do not claim every matching source was read.

Read proofs in `StokesCartanCoronaCapacity`, `WeightedGraphSpectralGap`, `GateCapacityDiscrepancy`, `FirstOrderConnectionIntervalClassification`, and `FiniteProjectivePlaneSpectralGap` expose candidate mechanisms: exact resistance square completion, mass-minus-averaging Dirichlet forms, construction of an actual minimizing response, endpoint transport retaining holonomy, and incidence identities proving rather than postulating a finite spectral gap. `ReciprocalCoareaEnergy` has an arithmetic shell mechanism whose source inputs do not directly identify a Maass core. `FormationStokesFolnerSelection` bounds bulk current by boundary capacity; `PathShellEdgeTail` uses a weakest-edge conductance and cannot be silently treated as a spectral gap.

The next conjecture must construct a comparison from the actual weighted chord identity and actual modular permutation data to physical core energy, with constants and any resistance divergence at common zeros explicit. Generic graph-gap assumptions, a projective-plane graph unrelated to the actual congruence action, or an unconstructed positive core inverse are not proofs of that comparison.

## Remaining proof obligation

The actual core-plus-cusp identity still needs a source-derived nonnegative lower bound for `Qcore+B`. Signed-mean separation alone does not provide that estimate. An angular-only argument cannot ignore common zeros. Subsequent attempts should keep the actual permutation constraints and use the continuous weighted chord expression or the original components through the zeros. No uniform inverse, congruence expansion estimate, or positive core response has been assumed.
