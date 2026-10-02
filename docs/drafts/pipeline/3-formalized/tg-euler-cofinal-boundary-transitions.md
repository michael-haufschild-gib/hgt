# TG C9.11l — actual Euler transitions and their infinite kernel shells

- **Stage:** 3-formalized
- **Type:** UNCONDITIONAL source theorem and exact obstruction
- **Route:** TG, source-defined graded admission with the full current return
- **RH status:** unproved; cofinal relative class, Hardy cubic and sub-unit law remain open

## Exact result

For every b>0 and genuine finite prime sets S⊆T, the original boundary maps
`B_S=R₁ A_S|K_b` force a unique bounded surjective transition τ_(S,T) with
`τ_(S,T)(B_T f)=B_S f`. These transitions satisfy identity and composition.
For b≥1 they retain the actual return:
`J_S f=−A_S* τ_(S,T)(B_T f)`.

The same source quotient defines a bounded spectral equivalence Φ_S from the
actual boundary annulus `(b/P_S,1)` onto the original Fourier annulus `(b,P_S)`.
Its source law is `Φ_S(B_S f)=R_(P_S)f`; the exact transition identity is
`Φ_S τ_(S,T)=R_(P_S) Φ_T`. No arbitrary annular isometry is substituted.

Restricting Φ_T yields the exact bounded equivalence

`ker τ_(S,T) ≃L {u : R_(max(b,P_S))u=0, R_(P_T)u=u}`.

If `max(b,P_S)<P_T`, this is an infinite-dimensional shell. The full-domain
partial map of τ_(S,T) is therefore not Fredholm. For every starting S and
b>0, a later T⊇S satisfies this strict inequality; consequently no finite
starting stage makes all later source-preserving transitions Fredholm.

## Dependency-closed paper proof

The exact C9.11k source kernels are `N_S=K_b∩ker R_(P_S)`. Genuine prime product
monotonicity gives N_T⊆N_S. Descend B_S through N_T and compose with the inverse
of the proved quotient equivalence at T. Its source law proves uniqueness,
surjectivity and composition. The existing current identity gives the retained
adjoint return.

Descend `R_(P_S)|K_b` through N_S instead. C9.11k's Sonin extension proves its
surjectivity onto the original Fourier band; its kernel is exactly N_S. This
constructs Φ_S. Cutoff nesting proves the displayed conjugacy. A vector of the
lost shell lies in the T-band, and Φ_T inverse takes it into ker τ; conversely,
the two lower-gap conditions combine into the max endpoint. The explicit
restriction/inverse construction is continuous in both directions.

The corpus's noncompact physical shell projection fixes an actual orthonormal
shell sequence. Conjugation by the even Fourier involution gives noncompactness
of the corresponding Fourier shell projection. Were its annular range finite
dimensional, the projection would factor through a locally compact space and
be compact. Transfer this contradiction through the actual kernel equivalence.
Finally, the existing unbounded genuine primes supply a later product above
both b and P_S, for every starting finite set S.

## Positive survivor and failed proposal

The failed proposal is a source-preserving **Fredholm transition system**, not
route TG. The positive survivor is the whole source-determined lost shell,
its exact bounded kernel equivalence, the Fourier restriction conjugacy, and
the actual Euler current return. Any relative completion must retain these
infinite channels; finite quotient isomorphisms alone provide no Hardy index.
See P5:tg-euler-fredholm-transition-system.

## Lean and validation

Four finished leaves, all wired into `RHTower.lean`:

- `CCMEulerBoundaryTransition`: prime-product monotonicity, actual transition,
  source law, uniqueness, surjectivity, identity/composition and current return.
- `CCMEulerBoundarySpectralChart`: actual spectral equivalence, source law,
  exact conjugacy and vanishing criterion.
- `CCMEulerBoundaryKernelShell`: full source-defined kernel-shell equivalence.
- `CCMEulerBoundaryNonFredholm`: Fourier-shell noncompactness, infinite kernel,
  non-Fredholm obstruction and a later obstructed transition from every stage.

All four final foreground `lake --old env lean <leaf> -o <leaf.olean>` audits
pass. All 29 public declarations (25 theorems, four definitions) were queried
in `/tmp/tg-c911l-axioms.lean`; every result has exactly
`[propext, Classical.choice, Quot.sound]`. No added axioms, holes, numerical
experiments, full builds, umbrella builds, heartbeat increases or subagents.

The first kernel implementation caused deterministic reduction timeouts.
Replacing repeated composed-map unfolding and redundant open-mapping inversion
with an explicit continuous restricted inverse resolved them. The final
finite-dimensional transfer supplies canonical submodule instances explicitly.
This changes proof elaboration, not the mathematical statement.

`scripts/formal_tools.py lint` reports ten unrelated unwired modules and no
error in these four leaves. The complete error set is recorded in
`/tmp/tg-c911l-lint.log`; all active-proof lint restrictions pass for this work.

## Search evidence and next conjecture

The documented transition deep search completed without an applicable existing
transition theorem. The shell search had partial coverage; candidate lemmas and
source arguments were inspected. Exact applicable source facts were read and
checked in Lean. Own in-progress source hits were not treated as proof evidence.

Subsequent step: P3:tg-unsquared-relative-source-assembly now constructs the coherent unsquared
relative operator response from its original common-carrier source, using the
actual time-band correction factorization. The full joint prime–Gamma
continuation, degree-three Hardy comparison and strict source sub-unit law are
still the hard RH gaps. C9.11l solves none of those by itself.
