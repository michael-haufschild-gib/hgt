# Original horizon cap's wave equation

Status: the original `capBoundaryField` satisfies the homogeneous reduced
weak wave equation in Lean. Subtracting it from the original future response
preserves the complete reduced bulk source. Full temporal/metric/left-QNM
matching and RH remain open.

[BRIDGE] The actual source-horizon limit commutes with the weak
wave equation on compact joint target tests. The resulting original
source-derived cap is a homogeneous weak solution.

Dependency-closed proof:

1. Set source time `s=v-y` and let original source radius `y` tend to
   minus infinity. The source vertex eventually leaves the compact test
   support, so the known full kernel weak source term is exactly zero.
2. The native invariant equals
   `(cosh(v-tau)+(sinh(v-tau)-sinh(x))*radialUnit(y))/cosh(x)`.
   For `y<0`, `radialUnit(y)` lies in `[0,1]`. The original circle mean
   therefore has a uniform bound on the product of this compact parameter
   interval and the compact test support. Both causal indicators remain.
3. Dominated convergence gives zero weak wave action for the actual
   direct-minus-image horizon kernel. This uses the proved pointwise
   source-horizon limit and does not differentiate the limiting kernel.
4. Express the original cap integral in its source ingoing-time variable.
   Original onset decay and horizon mean growth have the strict margin
   `g<alpha<2`. A compact target test then admits source-time/target Fubini.
5. Integrate the homogeneous horizon-kernel equation against the actual
   onset derivative, retaining the original lift coefficient and both arms.

Consequence: the exact cap cancels the ingoing field value
without adding a bulk source. A value-only cancellation does not imply this
claim; the weak equation supplies the missing distinction. Remaining
physical metric/current/QNM identification is not an assumed consequence.

Write `H_v(tau,x,z)` for the original direct-minus-image source-horizon
kernel with its half-factor, `b(v)=timeOnsetFirst(2*s,v)`, and `c` for the
original `liftTraceCoefficient`. The admitted representation is

`cap(tau,x,z) = -2*c * integral_(v>0) b(v)*H_v(tau,x,z)`.

For either arm, the product majorant is

`C*exp((g-alpha)*v)*exp(g*(-tau-x+abs(k)))*norm(phi(tau,x,z))`,

with `x` replaced by `-x` for the image. The source factor is integrable on
`v>0`; the target factor is integrable by compact support. Translation of
the actual delay integral retains the characteristic cutoff; the original
onset derivative vanishes at negative source time. Thus the source-time
representation and Fubini do not discard either arm or an onset term.

For every joint smooth compact `Phi` supported in `x<0`, Lean proves

`integral H_v * weakWaveTest(Phi) = 0`,

`integral cap * weakWaveTest(Phi) = 0`,

`integral (originalFutureResponse-cap) * weakWaveTest(Phi)
 = integral originalReducedSource * Phi`.

The last source integral is exactly EQ's weighted original forcing pair.
The cap pairing is absolutely convergent, proved separately from the zero
identity. No wave equation or convergence premise is supplied.

Proof:
[ThetaCuspHawkingBMOriginalCapWeakWave.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalCapWeakWave.lean),
namespace `D4BMOriginalCapWave`:

- `horizon_kernel_test_limit`, `horizon_kernel_weak_wave`;
- `boundaryArm_source_integral`, `capTestDensity_integrable`;
- `cap_test_integrable`, `cap_source_test_fubini`;
- `original_cap_weak_wave`, `original_future_sub_cap_weak_wave`.

Verification: scratch passed; exact isolated leaf audit passed in 11.59
seconds, two jobs, with two non-fatal tactic-sequencing style warnings.
EQ's existing `weakWaveTest_regular` is now public for reuse; its exact leaf
audit passed in 70.00 seconds. Each Lean/Lake check ran single-threaded in
the foreground with a 240-second hard timeout. Both leaves are wired into
the umbrella; no umbrella build ran.
Repository lint has one pre-existing unrelated error: unwired
`ThetaCuspHawkingBMOnsetTransgressionHorizon`. Neither changed leaf has a
lint error.

Whole-route boundary: the original cap's reduced bulk equation is closed.
The original lift already has a proved pointwise wave equation and exact
gradient absorption in `ThetaCuspHawkingBMJointSourceTimeField`:
`timeOriginalForcing_gradient_absorption`. The next missing identification
is its assembly with the proved weak response/cap in general joint tests,
followed by the physical metric/current/left-QNM action and required
boundary data. Neither field-value cancellation nor the homogeneous cap
equation alone proves that full identification or current extinction.

Search evidence: broad deep `lift cap` and `halfKernel` searches located
the actual cap definitions and existing time/normal trace results. The
compact-parameter method search returned dominated-convergence arguments
with partial coverage and predominantly source-only compiler metadata;
all mechanisms used here were verified in Lean. Broad arXiv searches for
`Darboux` and `transmutation` included
[Startsev's hyperbolic-equation transformations](https://arxiv.org/abs/2609.06217)
(posted September 2026, journal reference 2023) and
[Jin–Ma–Zuazua's transmutation algorithm](https://arxiv.org/abs/2601.03616).
No theorem from either paper is used in this cap proof.
