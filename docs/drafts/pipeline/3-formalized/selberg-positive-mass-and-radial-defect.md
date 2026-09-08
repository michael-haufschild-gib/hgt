# Strict actual trace mass and the retained angular energy

- **ID:** SELBERG-POSITIVE-MASS-RADIAL-DEFECT
- **Stage:** 3-formalized
- **Parent:** [Selberg conjecturing loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 26.
- **Selberg status:** Unproved. Strict total mass positivity is now proved; the combined core/Bessel lower bound remains missing.

## Exact actual-source results

Use the actual finite congruence family `f_q`, density `D=sum_q |f_q|²`, and the physical core and tail masses from cycle 25. For `0<lambda<1/4` and every cutoff `Y>=1`,

`Mcore(Y)+Mtail(Y)=Mcore(1)+Mtail(1)>0`.

Together with the full quarter-form identity this proves, for every `T>=0`,

`Qcore(exp T)+B(T)<0`

for any actual exceptional Maass source. This is a necessary property of an exceptional source, not a proof that no such source exists.

For each real coordinate direction `v`, write

`E_v=sum_q |D_v f_q|²`, `C_v=D_v D`,

`R_v(c)=sum_q |D_v f_q-c*f_q|²`, with `c` real.

The actual derivative pairing gives the exact identities

`R_v(c)=E_v-c*C_v+c²*D`,

`R_v(c)=R_v(c_v)+D*(c-c_v)²`, where `c_v=C_v/(2D)` and `D>0`.

The canonical slope is the unique minimizer. The residual is zero exactly when every component derivative equals that same real slope times its component value. Let

`A=R_x(c_x)+R_y(c_y)>=0`.

At positive density, the literal scalar amplitude `rho=sqrt(D)` satisfies

`G=|partial_x rho|²+|partial_y rho|²+A`,

`G-D/(4y²)=(|partial_x rho|²+|partial_y rho|²-D/(4y²))+A`.

No smoothness of `rho` at trace zeros is asserted. Instead, the multiplied identity is proved at **every** point, including zeros:

`D*G=(C_x²+C_y²)/4+D*A`.

Combining it with the actual Maass trace equation gives

`D*Delta D=(C_x²+C_y²)/2+2D*A-2lambda*D²/y²`.

This retains the spectral term. Trace derivatives together with the known eigenvalue still determine the full gradient energy through cycle 25's source equation; no contrary claim is made.

## Corpus conjecture, test, and pivot

Searches `integral positive continuous` and `fundamental domain` led to the positive-support argument in `LevinsonLittlewoodZeroCount` and the definiteness proof in `PeterssonInnerProductLevelOne`. Its useful mechanism is continuity, actual modular reduction, and `fd=closure(fdo)`. Adapted to the actual finite Maass trace, it gives positive compact-core mass. The existing horizontal indicator-Fubini interface and integrable tail then prove cutoff independence and strict total mass.

Searches `Gram determinant`, `Fisher phase`, and `Lagrange identity` led to `ProjectiveQuantumFisherValue`, `ConstitutivePolarAmplitudeFisherPhase`, and the explicit two-coordinate square in `SymmetricPickSchur`. Their mechanism suggests separating a common radial derivative from the remaining complex family motion. The actual-source square completion above succeeds and classifies precisely when no residual remains.

The proposed shortcut “the scalar squared norm alone reconstructs full gradient energy for smooth periodic fields” fails. The explicit fields

`F_c(z)=exp(i*c*Re(z))`

all have squared norm one and scalar-amplitude derivative zero, while their actual horizontal derivative energy is `c²`. Choosing `c=0` and `c=2*pi` gives two smooth period-one fields with identical squared norms and strictly different energies at every point. This is a closed symbolic example; no numerical experiment is used.

**Scope of failure:** the toy fields are not claimed to be Maass eigenforms, cusp forms, or modular under inversion. The result rules out norm-only reconstruction for the stated smooth periodic class. It neither refutes Selberg nor proves a loss of information after retaining the actual Maass equation and eigenvalue. [Failed shortcut and positive survivor](../5-failed/selberg-scalar-norm-energy-reconstruction.md).

**Positive survivor:** actual nonnegative angular residual, its exact minimizing slope and zero classification, and the source Fisher identity retaining `lambda`. A subsequent lower-bound attempt must keep this term and the Bessel boundary form; it cannot insert an assumed positive core response.

## Dependency-closed paper proof

1. Original nonvanishing makes the finite trace positive somewhere. Move that point into the closed modular fundamental domain using the actual integral modular action. Invariance preserves positivity. The trace is continuous from its real C² chart. Its positive open set therefore meets the open modular domain because the closed domain is its closure.
2. At the resulting interior point, choose a cutoff above its height. Strict horizontal, circular, and upper-height inequalities give a neighborhood contained in the standard core. The positive continuous hyperbolic trace density has support containing a neighborhood there. Lebesgue measure is positive on neighborhoods, and compact source integrability therefore makes the core mass strictly positive.
3. Horizontal Fubini splits the core mass into the fixed lower circular part and the strip from height one to `Y`. Above one, period one identifies the full centered horizontal interval with the actual normalized unit-period mass slice. The improper-integral interval-plus-tail identity, with integrability already proved for the actual cusp, shows `Mcore(Y)+Mtail(Y)` is cutoff independent. Nonnegative tail mass and step 2 make this constant strictly positive.
4. Multiply positive total mass by the strictly negative factor `lambda-1/4` in the actual core/Bessel upper bound. This gives the strict signed-form conclusion without dropping the nonnegative Fourier remainder.
5. Differentiate each literal complex squared norm and sum. This gives `C_v=2 Re sum_q(D_v f_q*conj(f_q))`. Expand each actual squared residual in real and imaginary coordinates and sum, obtaining `R_v(c)=E_v-c*C_v+c²D`. Complete the square at `C_v/(2D)`. Positivity and unique minimization follow from a real square times positive mass. A finite sum of nonnegative squared norms is zero exactly when every component residual is zero.
6. At positive `D`, the actual square-root chain rule gives `D_v rho=C_v/(2sqrt(D))`, proving the exact radial/angular gradient and quarter decompositions. At a zero of `D`, the actual trace has a nonnegative local minimum, hence every current vanishes. Thus multiplication by `D` extends the identity to every source point without a differentiability assertion for the norm at zero. Substitute the already-proved actual trace Laplacian equation to retain the eigenvalue in the Fisher identity.
7. For the symbolic phase test, differentiate the literal complex exponential through the real-coordinate continuous linear map. Its norm is one and its horizontal energy is `c²`; integral frequencies give period one by the exact complex exponential period. The constant scalar amplitude has zero derivative. Frequencies zero and `2*pi` therefore yield the claimed closed counterexample.

## Lean audit

- `SelbergMaassTraceMass`: actual positive interior source, positive core, exact cutoff independence, strict total mass and signed core/Bessel form.
- `SelbergMaassTraceRadial`: actual derivative residual, exact minimization and equality classification, radial/angular source energy and Fisher identity.
- `SelbergScalarPhaseToy`: literal smooth periodic phase fields and the closed norm-only reconstruction counterexample.

All three complete scratch and direct source checks passed without warnings. Three final `LEAN_NUM_THREADS=1 lake build <single-module>` audits passed sequentially, each rebuilding only its named target. Cached dependency diagnostics were replayed; no full or umbrella build ran.

- `/tmp/selberg_trace_mass_build.log`: `SelbergMaassTraceMass` passed.
- `/tmp/selberg_trace_radial_build.log`: `SelbergMaassTraceRadial` passed.
- `/tmp/selberg_scalar_phase_build.log`: `SelbergScalarPhaseToy` passed.

All 46 public definitions and theorems passed `lake env lean /tmp/selberg_mass_radial_axioms.lean`. All expected reports are present with no errors or unexpected axioms: only `propext`, `Classical.choice`, and `Quot.sound`, or none. Log: `/tmp/selberg_mass_radial_axioms.log`.

All three modules are wired into the RHTower umbrella and indexed. Corpus queries retrieve `totalMass_pos` and `trace_fisher_identity`. Tracked-file whitespace and explicit new-source/document trailing-whitespace checks passed.

**Latest repository-wide lint failed only on unrelated untracked, unwired `HTGeometry.FokasLenellsUniformization`.** That concurrent source was not edited or wired by this task. No new Selberg module is named; existing large-file warnings remain. The index was refreshed immediately before lint. Logs: `/tmp/selberg_mass_radial_index.log` and `/tmp/selberg_mass_radial_lint.log`.

All task-owned Lean/build handles are terminal with exit zero; the one-worker discipline was maintained. No commit or push was made by this task.

## Remaining work

Construct and prove a nonnegative lower bound for the actual combined core and Bessel form, retaining the congruence component coupling and the angular residual. No such estimate or positive/invertible core operator has been supplied. The full Selberg goal remains active.
