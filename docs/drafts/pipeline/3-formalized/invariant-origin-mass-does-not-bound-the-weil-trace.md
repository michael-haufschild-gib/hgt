# Invariant origin mass does not bound the Weil trace

- **ID:** qii-invariant-origin-mass
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Status:** FORMALIZED. Smooth witnesses and all origin-mass assertions passed direct actual-file checks and transitive audits with only `propext`, `Classical.choice`, and `Quot.sound`.
- **Source:** ../1-in-progress/q-ii-source-effectivity-and-linear-degree.md
- **Statement:** The strictly positive origin sharp-square mass is centered-flow invariant, but the original Weil trace is unbounded on its unit sphere, already among compact smooth sources in every positive aperture.

## Formalized proof

Centered source flow is `g_c(t)=exp(-c/2)g(t-c)`. Its Mellin character is
`exp(c(s-1/2))`. Arithmetic sharp reflects `s` to `1-conj(s)` and conjugates
the value. The two characters cancel at every complex `s`. Mellin injectivity
therefore gives the literal source identity `g_c * h_c^sharp = g * h^sharp`.
Every product reading is invariant. In particular the already certified
origin degree `N(g)=integral(exp(t)|g(t)|²)` is invariant and strictly positive
on nonzero actual sources.

The finite-kernel construction in `WeilEnergyIsUnboundedAtEveryAperture`
can be made smooth: choose the original nonzero compact bump with `ContDiff`
order infinity, instead of order two. Finitely many distinct translates are
linearly independent. One more translate than the dimension of a prescribed
finite reading gives a nonzero kernel vector, still smooth. Include the
low-frequency grid and pole moment in that reading. The same existing
near-radical and grid inequalities force its Weil Rayleigh quotient above
any chosen real threshold. Rescaling preserves smoothness and the kernel
while making its L² mass exactly one.

Embed such a real compact smooth source `f` into the genuine Meyer carrier
as `g(t)=exp(-t/2)f(t)`. The exact compact comparison gives
`trace(g,g)=Weil(f,f)`, while the origin identity gives `N(g)=integral(f²)=1`.
Hence `trace(g,g)` is unbounded on the unit-origin-mass sphere. No function `F : R -> R` of this mass can dominate the original mixed
trace: choose `g=h` with trace greater than `|F(1)|+1`. Its unit mass
fixes the proposed squared bound to `F(1)^2`, which is strictly smaller
than its squared trace. Scalar multiples are a special case.

## Insight and scope

Faithful positivity and centered-flow invariance exist on the original source
space without RH. They do not by themselves supply either quotient descent
or domination of the original intersection form. This is a positive source
mass with an explicit unbounded-trace obstruction, not a claim
that the induced Poisson quotient norm has been classified.

## Lean verification

- Smooth finite-kernel witnesses and their unit-mass Rayleigh strengthening: formalized.
- Exact origin mass of the compact Meyer embedding: formalized.
- Unit-origin-mass unboundedness and failure of every nonlinear mass-only mixed majorant: formalized.
- Origin invariance from the stronger literal product identity in the flow module: formalized.

Existing inputs are unconditional; no zero-location or simplicity premise is added.
All actual-file checks and transitive axiom audits passed. External novelty unverified.

`SmoothFiniteReadingKernels.lean` passed direct check **42458**, including
all three transitive audits with only `propext`, `Classical.choice`, and
`Quot.sound`. It retains infinite differentiability throughout the finite-kernel
construction. Certified endpoints:

- `exists_nonzero_smooth_realTestAt_in_ker`
- `exists_smooth_realTestAt_in_ker_weilPair_gt_mul_integral_sq`
- `exists_smooth_realTestAt_unit_mass_in_ker_weilPair_gt`

Temporary prints are removed; the smooth-kernel module is wired and documented.
`InvariantOriginMassDoesNotBoundTheWeilTrace.lean` passed direct check **73371**
with all seven standard axiom audits:

- `meyerOriginSquareMass_eq_integral`
- `meyerOriginSquareMass_nonneg`
- `meyerOriginSquareMass_eq_zero_iff`
- `meyerOriginSquareMass_centered_flow`
- `meyerOriginSquareMass_compact_real`
- `exists_meyer_compact_unit_originMass_trace_gt`
- `meyerOriginMass_function_not_trace_majorant`

The actual module is cleaned, wired and documented.
