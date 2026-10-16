# CHMD: compact primitive source projection

Date: 2026-10-16. Status: failed. Positive survivor: formalized; all owned audits passed.

Conjecture: the completed signed Doob graph has a compact source projection
on its primitive compact core, permitting a discrete first-mode argument.

The actual source projection is noncompact even on a bounded primitive
graph ball. This is proved by a concrete sequence, without assuming RH or
the sign of any Markov energy.

## Positive survivor and dependency-closed proof

Let g be `WeilOneSided.narrowBump 0` and
f = `evenShift g 4 - cosh(1) g`. Both hyperbolic half-moments vanish by the
existing exact shift laws. Since g is supported in [-1/4,1/4], f(0) = -cosh(1),
so f is nonzero. Every translate f_T(x) = f(x-T) stays primitive: its cosh
half-moment is cosh(T/2) times the original cosh moment plus sinh(T/2)
times the original sinh moment.

The full Weil autocorrelation is invariant under simultaneous translation
of its two entries. Hence the complete Markov energy of f_T equals that of
f, including every original prime term and the original archimedean source.

Lift f_T through the existing inverse Doob map v_T = f_T/Θ into the actual
complete graph. Its source norm squared is
M(T) = ∫ f_T(x)^2 cosh(x/2)/Θ(x) dx.
The inverse weight cosh(x/2)/Θ(x) tends to infinity because Θ tends to zero
and cosh is at least one. On the fixed compact support of f, this gives
M(T)→∞; positivity of ∫f² makes this a nontrivial escape.

Normalize by the source norm. The resulting p_T satisfy exactly:

- p_T belongs to the existing compact core and is mass-orthogonal to the
  constant ground, which is the actual primitive hyperplane.
- The source norm is one.
- Signed energy is markovEnergy(f)/M(T), hence tends to zero.
- Complete jump energy tends to one.
- Hilbert graph norm squared tends to two and is eventually at most four.

Choose T_n beyond that common bound and separated by more than the fixed
support diameter. Source coordinates then have disjoint supports, so they
are pairwise orthogonal unit vectors. Every pair has squared distance two;
no strictly increasing subsequence is Cauchy. Compactness would supply a
convergent subsequence, a contradiction.

Second-pass salvage retains this entire primitive sequence. It also proves
that no positive uniform signed margin can hold on the original primitive
compact core. This is a structural boundary of the proposed compactness
route, not a revised error estimate or an RH receiver.

## Formal status

- `formal/GaloisForLFunctions/RHTower/CHMDTranslatedPrimitiveSource.lean`:
  translation invariance, explicit double-primitive profile, mass escape.
- `formal/GaloisForLFunctions/RHTower/CHMDPrimitiveCuspEscape.lean`:
  `exists_primitive_escape`, `no_cauchy_subsequence`,
  `not_isCompact_primitiveBallImage`, `no_positive_primitive_margin`.

Both leaf builds and both final plain Lean source audits passed; the direct
audits had empty output. A separate 25-name toolchain probe passed. All 59
declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Index
refresh passed. Global lint reports six other unwired Deninger modules, listed
in `../3-formalized/chmd-primitive-cusp-escape-2026-10-16.md`. No CHMD error was
reported. All 12 owned scratch files were removed; absence verified. All owned processes
reached terminal exit.

## Limits and surviving frontier

This does not construct a selfadjoint generator, prove a Weyl residual,
identify an exact essential spectrum, or determine the sign of primitive
energies. In particular, a zero energy limit is compatible with RH and is
not a proof of RH. No equality of maximal and compact-core domains is used.
The missing CHMD positivity must work at this critical boundary; a strict
positive margin in the theta-cosh source norm is unavailable.
