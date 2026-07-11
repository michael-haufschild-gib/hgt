# Leaf-reflection Bohr projection catastrophe

- **ID:** `leaf-reflection-bohr-projection-catastrophe`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/rhtower_status_constraint_1107.md` · §3
- **Statement:** For an irrational two-base one-sided flank carrier, every nonzero transverse Bohr mode forces the corresponding exact-period Cesàro projectors to be nonnormal on every connected domain joining the two reflected flanks.

## Goal

Replace the unsupported continued-fraction guess in the leaf-intrinsic reflection-rigidity cell by
an exact obstruction.  The theorem must identify what fails when a bivariate power-series germ
continues only along the dense exponential leaf, without assuming a transverse torus extension or
installing a growth bound.

The result is not itself an RH route.  It is a constraint-side diagnostic for the independent
two-base weld problem.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, narrow build green, lint green
- [ ] 3 → 4 publication-ready: standalone theorem, proof, Lean certificate, literature verdict

## Exact setting

Let `α, β, w > 0` with `β/α ∉ ℚ`.  Let `G : ℂ → ℂ` be entire and even.  Suppose that on
`Im z ≤ -w`,

\[
G(z)=\sum_{m,n\ge 0} b_{m,n}e^{-iz(m\alpha+n\beta)},
\qquad
\sum_{m,n\ge0}|b_{m,n}|e^{-w(m\alpha+n\beta)}<\infty.
\]

Put `Tα = 2π/α` and `θ = 2πβ/α`.  For `r ≥ 0`, define the exact-period transverse projector

\[
P_{r,N}G(z)=\frac1N\sum_{k=0}^{N-1}e^{ikr\theta}G(z+kT_\alpha).
\]

This is a static spectral projection sequence.  Translation is used only to extract a boundary
character; no parameter propagates `G` or defines the carrier.

## Theorem candidate

`[PROVED HERE — paper, novelty unverified]` Fix `r ≥ 1`.  If the slice

\[
B_r(z)=\sum_{m\ge0}b_{m,r}e^{-iz(m\alpha+r\beta)}
\]

is nonzero, then `{P_{r,N}G}` is not locally bounded on any connected open set meeting both
`{Im z < -w}` and `{Im z > w}`.  Equivalently, the normality domains containing the two flanks
are distinct, and their complement is an intrinsic seam separator.

### Proof

On the lower flank, absolute convergence permits termwise Cesàro averaging.  The `(m,n)` term
acquires the factor

\[
\frac1N\sum_{k=0}^{N-1}e^{ik(r-n)\theta}.
\]

Because `θ/(2π)=β/α` is irrational, this tends to `1` for `n=r` and to `0` otherwise.  Dominated
convergence gives locally uniform convergence `P_{r,N}G → B_r` on `Im z < -w`.

On the upper flank, evenness gives

\[
G(z+kT_\alpha)=G(-z-kT_\alpha).
\]

The reflected point lies on the lower flank, and the `(m,n)` term now acquires

\[
\frac1N\sum_{k=0}^{N-1}e^{ik(r+n)\theta}.
\]

For `r ≥ 1` and `n ≥ 0`, irrationality makes every such mean tend to `0`.  Hence
`P_{r,N}G → 0` locally uniformly on `Im z > w`.

If the projector family were locally bounded on a connected open `U` meeting both flanks,
Montel plus the identity theorem would give a holomorphic subsequential limit on `U`.  Its lower
open piece would equal `B_r`, while its upper open piece would be zero.  The identity theorem would
force `B_r = 0`, contrary to the hypothesis.  Therefore the family is nonnormal across every such
`U`.  The slice is nonzero whenever some `b_{m,r}` is nonzero, by uniqueness of absolutely
convergent generalized Dirichlet coefficients.  ∎

## Consequences

1. `[PROVED HERE — paper]` Any hypothetical nonconstant two-base weld has a nonzero transverse
   slice.  If all `r ≥ 1` slices vanished, the spectrum would lie in `αℕ`, and the existing
   periodic-spectrum rigidity theorem would make `G` constant.
2. `[PROVED HERE — paper]` Analytic continuation along the leaf and transverse Bohr projection do
   not commute for a hypothetical counterexample.  The exact obstruction is nonnormality of the
   projection sequence, not failure of coefficient recovery on either flank.
3. `[PROVED HERE — paper]` The qualitative obstruction uses only irrationality.  Continued-fraction
   rates affect convergence speed but do not enter the existence of the seam separator.  The guess
   “rigid iff partial quotients are unbounded” has no support from return-time arguments alone.
4. `[CONJECTURE]` The nonnormality locus of a nonzero transverse projector contains a closed
   connected left-to-right seam wall.  This should follow from planar separation applied to the
   open normality set, but the exact unbounded-component statement still needs a careful topology
   proof.

## Attack and scientific verdict

- **Degenerate boundary:** if `β/α ∈ ℚ`, a common exact period exists and periodic-spectrum
  rigidity closes the carrier.  There is no projection mismatch.
- **Finite torus model:** transverse entire extension makes the projectors locally bounded, so the
  theorem kills every nonzero transverse slice, recovering the previously proved torus rigidity.
- **Loud leaf-only model:** arbitrary seam growth can support projector nonnormality, so the theorem
  does not by itself contradict a leaf-intrinsic weld.
- **Parent-theory reduction:** after erasing project language, the proof is geometric Cesàro
  orthogonality plus Montel and the identity theorem.  It is therefore a useful `[BRIDGE]`, not yet
  candidate new scientific knowledge under the scientific-novelty gate.
- **RH gate:** the obstruction neither distinguishes the zeta divisor nor supplies a source-pure RH
  localization mechanism.  It cannot be promoted as an RH route.

## Open core

`[OPEN CORE]` Prove or refute existence of an even entire two-base weld whose transverse projector
families possess the forced seam nonnormality.  Any rigidity proof must rule out this nonnormality
using the exact semigroup carrier; any counterexample must construct it.  Diophantine return times
without a carrier-derived transverse growth bound cannot close the core.

## Lean target

Formalize the algebraic/analytic core in a new isolated RHTower module:

1. finite geometric Cesàro character limits for irrational `β/α`;
2. lower-flank `r`-slice extraction and upper-flank annihilation;
3. a projection-compatibility no-go theorem under an explicit locally uniform analytic-limit
   hypothesis;
4. only then consider importing the in-tree Montel machinery for the full nonnormality statement.

## Literature audit

Primary-source audit is in progress across Bohr holomorphic almost-periodic functions,
Fourier–Borel/exponential-series theory, analytic continuation of absolutely convergent Dirichlet
series, and normal-family theory.  No scientific-novelty claim is made before that audit closes.

## Log

- 2026-07-11 — card created; exact projector mismatch and paper proof isolated; continued-fraction
  guess downgraded; full leaf-rigidity core remains open.
