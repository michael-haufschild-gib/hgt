# Actual Maass core Stokes theorem and complete quarter form

- **ID:** SELBERG-MAASS-CORE-QUARTER
- **Stage:** 3-formalized
- **Parent:** [Selberg conjecturing loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 25.
- **Scope:** Actual C² principal-congruence Maass cusp source, finite congruence trace, standard planar measure on the modular core, and its previously proved physical cusp Bessel form.
- **Selberg status:** Unproved. No lower bound for the combined core and Bessel boundary form is asserted.

## Exact result

Let `w=N+1`, `Q=SL2(Z)/Gamma(w)`, `f_q` be the actual translated source, and

`D(z)=sum_q |f_q(z)|²`,

`G(z)=sum_q (|partial_x f_q(z)|²+|partial_y f_q(z)|²)`.

The actual real-chart Laplacian satisfies

`Delta D=2*(G-lambda*D/y²)`.

For `Y>=1`, let `Omega_Y` be the standard closed planar domain

`-1/2<=x<=1/2`, `sqrt(1-x²)<=y<=Y`.

All core integrals below use two-dimensional Lebesgue measure, not a new paired-integral definition. The exact source Green theorem is

`integral_Omega_Y Delta D = 2*sum_q J_q(Y)`.

Here `J_q` is the existing actual width-normalized physical cusp flux. If

`Mcore(Y)=integral_Omega_Y D/y²`,

`Qcore(Y)=integral_Omega_Y (G-D/(4*y²))`,

then

`Qcore(Y)=sum_q J_q(Y)+(lambda-1/4)*Mcore(Y)`.

For `0<lambda<1/4`, `Y=exp(T)`, and `T>=0`, adjoining the actual countable cusp Bessel decomposition yields

`Qcore(Y)+B(T)+S(T)=(lambda-1/4)*(Mcore(Y)+Mtail(Y))`.

`Mtail` is the literal unit-strip hyperbolic trace mass. `B` is the finite sum of the actual Bessel boundary forms; `S` is the complete convergent Fourier square remainder, already proved nonnegative. Consequently

`Qcore(Y)+B(T)<=(lambda-1/4)*(Mcore(Y)+Mtail(Y))`.

This is an **upper** bound. It does not supply the missing nonnegative lower bound. These are new formal results in this development; no claim of mathematical novelty in the literature is made.

## Corpus conjecture, proof, and pivot

The corpus search `Laplacian square` exposed `ThetaCuspHawkingBMSquareSourceDifferential.fullSquarePotential_laplacian`: its product-jet calculation retains the gradient forcing. Applying that mechanism to the actual Maass squared norm, then to its finite trace, proves the pointwise identity. Treating the trace as an eigenfunction would lose `G`; that shortcut is not used.

The earlier inspected `ThetaCuspHawkingBMEisensteinActualFirstStokesIntegral` supplied the idea of pairing inversion arcs and translation sides. For the actual Maass trace these cancellations are derived from the real Möbius differential, not borrowed as assumptions. The literal paired Stokes integral equals the actual cusp flux and the complete Bessel expression.

A new whole-corpus `Stokes` query found `ThetaCuspHawkingBMEisensteinActualFirstStokesFubini`. Reading its geometric source supplied the missing standard-area identification: represent the curved domain by an indicator, apply both Fubini orders, identify the lower horizontal side intervals, then substitute the circle height. This succeeds for the actual real Maass current. No old specialized Eisenstein, conformal-Laplacian, or broad research umbrella is imported.

The next question is a sign estimate for the now literal form `Qcore+B`. Searches `Dirichlet Neumann` and `Schur boundary`, followed by source inspection of `StokesCoronaSchurVanishing` and `SchurComplementKernel`, show exactly what elimination would require: an actual core response, an established invertible/positive eliminated block, and its coupling to the adverse Bessel channels. Those generic matrix identities do not construct these objects. No positivity or inverse is assumed, and no conditional Schur wrapper is advertised as Selberg.

## Dependency-closed paper proof

1. Differentiate `|F|²` twice as a real function. For each real direction `v`, the second derivative is `2*(|D_v F|²+Re(D_v² F*conj(F)))`. Add horizontal and vertical directions and substitute the actual Maass equation. The finite sum differentiates at C² regularity.
2. Differentiate the actual identity `D(A*z)=D(z)`. The complex-chart Jacobian is multiplication by `1/denom(A,z)²`. Translation preserves the current direction. At inversion, the radial vector maps to the negative radial vector at the image. On the unit circle the image of `(x,y)` is `(-x,y)`, giving the exact paired circular cancellation.
3. Real C² regularity supplies continuous first and second currents on every positive-height compact cell. Vertical and horizontal FTC therefore apply to actual derivatives. The paired-coordinate integral reduces to its top current. Reflection, addition of adjacent intervals, and period one identify this top with the unit-period current integral.
4. Differentiate the unit-period trace mass by the proved compact parametric-integral theorem, applied to its complex-valued real lift. Uniqueness of derivatives compares this with the already-proved `H'=2*sum_q J_q`. This identifies the top current with the actual normalized flux.
5. The geometric domain is compact and measurable. Its indicator is integrable for every actual second trace derivative. Product-measure Fubini gives vertical slices from `sqrt(1-x²)` to `Y` and horizontal slices. Between the lowest circle height and one, horizontal slices are exactly `[-1/2,-sqrt(1-y²)]` and `[sqrt(1-y²),1/2]`; their intersection is contained in a singleton. Above one the slice is the full unit interval.
6. Horizontal FTC cancels full-strip slices by translation and leaves the side-interval currents below one. The substitution `y=sqrt(1-x²)` has derivative `-x/sqrt(1-x²)` and transforms their integral to the paired arc current. Inversion makes this equal to the full lower vertical current. Vertical FTC gives top minus that same lower current. Adding the two standard area integrals therefore leaves only the top, proving the area Green theorem. It also identifies the earlier paired-coordinate integral with this standard area integral.
7. The actual pointwise quarter density equals half the trace Laplacian plus `(lambda-1/4)*D/y²`. Compact continuity proves mass integrability; integrate this equality and substitute step 6. Add the prior cusp identity `-sum_q J_q+(lambda-1/4)*Mtail=B+S`; the seam flux cancels exactly. No energy, boundary, or square term is discarded.

## Lean modules and audit

- `SelbergMaassTraceEnergy`: actual norm-square derivatives, finite trace Laplacian, and pointwise quarter density.
- `SelbergMaassTraceBoundary`: actual modular differential, radial inversion, arc/side cancellation, and current regularity.
- `SelbergMaassTraceStokes`: actual finite FTC, paired Stokes, unit-current flux normalization, and paired Bessel identity.
- `SelbergModularDomainSlices`: standard-area indicator Fubini in both orders, exact horizontal slice geometry and integrability.
- `SelbergMaassTraceArea`: actual standard-area Green theorem, area/paired equality, core mass and quarter integral, and full core-plus-cusp quarter identity.

Complete scratch checks and direct source checks passed without warnings for all five modules. Needed oleans were generated with `lake env lean -o ... <source>`; the final area source was checked directly with `lake env lean <source>`.

All five final targeted `LEAN_NUM_THREADS=1 lake build <module>` audits passed sequentially, each rebuilding only its named target. Dependency diagnostics were cached replay output. No full or umbrella build ran. Logs:

- `/tmp/selberg_trace_energy_build.log`
- `/tmp/selberg_trace_boundary_build.log`
- `/tmp/selberg_trace_stokes_build.log`
- `/tmp/selberg_domain_slices_build.log`
- `/tmp/selberg_trace_area_build.log`

All 94 public definitions and theorems were audited by `lake env lean /tmp/selberg_core_quarter_axioms.lean`. Every expected report is present, with only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. No extra axioms or admissions were added. Log: `/tmp/selberg_core_quarter_axioms.log`.

All five modules are wired into `GaloisForLFunctions.RHTower` and indexed. Corpus queries return the standard-area Green theorem and full quarter-form capstone. Tracked-file whitespace and explicit new-source trailing-whitespace checks passed.

**Latest repository-wide lint failed only on five unrelated untracked, unwired HTGeometry modules:** `FokasLenellsJumpGeometry`, `FokasLenellsSingularPhase`, `InwardPlaneDisplacementReturn`, `InwardPlanePrescribedStream`, and `PolyatomicSpectralRank`. None of the new Selberg modules is named. These concurrent files were not edited or wired by this task. Existing large-file warnings remain. The index was refreshed immediately before lint. Logs: `/tmp/selberg_core_quarter_index.log`, `/tmp/selberg_core_quarter_lint.log`.

All task-owned Lean/build handles reached terminal exit zero; the one-worker discipline was maintained. No commit or push was made by this task.

## Remaining work

The precise unproved target is a source-derived nonnegative lower bound for `Qcore+B` compatible with the congruence family. Strict positivity of total core-plus-tail mass has since been proved in [cycle 26](selberg-positive-mass-and-radial-defect.md), together with exact cutoff independence. The combined core/Bessel lower bound remains unproved. All-congruence Selberg remains active and unproved.
