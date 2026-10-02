# TG C9.11m.2 — original prime-square time-band nuclear convergence

- **Route:** TG, cofinal unsquared relative source admission
- **Parent:** `tg-unsquared-relative-source-assembly.md`
- **Predecessor:** `tg-unsquared-prime-square-monomial-convergence.md`
- **Stage:** 3-formalized
- **Status:** dependency-closed paper proof and final Lean audits pass.

## Exact source theorem

For every nonnegative aperture a and every input interval [c,d], the family

`p ↦ c_(p,0) (D_(p²)+D_(p⁻²)) K_([-a,a],[c,d])`

is unconditionally summable in the actual Schatten-one Banach space. K is the
corpus's literal finite time-band Fourier operator. The coefficient is the
original `soninLogPrimePowerCoefficient(p,0)=1/(2p)`, and both dilation legs
are preserved. Summation runs over all finite prime sets, not only an ordered
prime cutoff. The result asserts trace-norm convergence, not merely weak,
strong, operator-norm or squared-Gram convergence.

## Dependency-closed proof

The literal zero extension of the nth Fourier Taylor output equals its
factorial Fourier coefficient times the actual cutoff monomial f_n. The
existing tensor-operator identity therefore puts the range of the nth
Taylor operator A_n in `span(f_n)`.

The predecessor's uniform vector-tail estimate now gives
`||D_T A_n|| ≤ ε ||A_n||`, simultaneously for every n and every finite prime
tail T outside one finite exclusion. To prove this, write every A_n x as a
scalar multiple of f_n and apply the continuous-linear-map norm bound.
No nonvanishing coefficient or vector premise is needed.

The corpus's actual Fourier Taylor expansion satisfies
`Σ_n ||A_n|| < ∞` and `Σ_n A_n=K`. For fixed T, all `D_T A_n` have rank at
most one, and their norms have the preceding summable bound. Bundle these
operators in the genuine Schatten-one Banach space, where their trace norm
equals their operator norm. Absolute summation gives

`||D_T K||₁ ≤ Σ_n ||D_T A_n|| ≤ ε Σ_n ||A_n||`.

Choosing ε relative to this finite nuclear mass proves the finite-set
vanishing-tail criterion for the original prime source in trace norm. Every
source term has unconditional trace-class membership from the corpus's ideal
law. The proof does not exploit traceNorm's value outside that class.

## Lean

- `SoninTimeBandTaylorSourceDirection`: literal output identity, actual Taylor
  range direction, uniform relative Taylor-operator tails.
- `SoninPrimeSquareTimeBandNuclear`: original source bundled with trace-class
  membership and unconditional trace-norm summability.

Both final foreground `lake --old env lean <leaf>` audits pass. All five
public declarations have only `propext`, `Classical.choice` and `Quot.sound`
in their axiom audits. Both leaves are wired into RHTower. Together with the
predecessor this gives six audited leaves and eighteen public declarations.
No new axiom, hole, heartbeat setting, full build or umbrella build was used.
The final global lint run reports ten unrelated unwired modules and no error
in these six leaves (`/tmp/tg-c911m-timeband-lint.log`).

## Remaining frontier

Transport this actual time-band source through Fourier/reflection covariance
and the already verified right-factor identity for the Sonin correction. Then
retain the adjoint leg in the full correction response and add the unchanged
deeper prime-power modes. The full prime–Gamma admission, principal linear
prime source, Hardy cubic compatibility and strict sub-unit law remain open.
