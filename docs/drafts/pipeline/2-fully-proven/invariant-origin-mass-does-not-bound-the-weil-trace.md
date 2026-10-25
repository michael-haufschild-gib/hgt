# Invariant origin mass does not bound the Weil trace

- **ID:** qii-invariant-origin-mass
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/q-ii-source-effectivity-and-linear-degree.md
- **Statement:** The strictly positive origin sharp-square mass is centered-flow invariant, but the original Weil trace is unbounded on its unit sphere, already among compact smooth sources in every positive aperture.

## Paper proof [PROVED HERE]

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
Hilbert structure with an explicit unbounded-trace obstruction, not a claim
that the induced Poisson quotient norm has been classified.

## Lean obligations

- Smooth finite-kernel witnesses and their unit-mass Rayleigh strengthening.
- Exact origin mass of the compact Meyer embedding.
- Unit-origin-mass unboundedness and failure of every nonlinear mass-only mixed majorant.
- Origin invariance from the stronger literal product identity in the flow module.

Existing inputs are unconditional; no zero-location or simplicity premise is added.
Implementation and transitive axiom audits remain pending. External novelty unverified.

Complete proof attempts now exist in `/tmp/QIISmoothFiniteReadingKernelsDraft.lean`
and `/tmp/QIIInvariantOriginMassDraft.lean`. The finite-kernel proof explicitly
retains infinite differentiability. The origin draft contains the exact compact
mass identity, unit-mass unboundedness, and the stronger nonlinear mass-only
obstruction. All remain unchecked.

Actual candidate: `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/InvariantOriginMassDoesNotBoundTheWeilTrace.lean`; unverified and unwired. The scratch copy remains until actual-file verification succeeds.
