# Exact theta-tail Fourier compensation

**Status:** Lean proof of the finite-cutoff boundary asymptotics and their exact restoration by the infinite theta tail. No all-degree Hankel positivity claim.

## Statement

Let `Phi` be the actual completed theta density, `P_N` its first `N≥1` positive integer shells, and

`C_f(t) = integral_0^infinity f(x) cos(t*x) dx`.

Then, with `s_N=P_N'(0)>0`,

`t² C_(P_N)(t) → −s_N`,

`t² C_(Phi)(t) → 0`,

`t² C_(Phi−P_N)(t) → s_N`.

Consequently the finite prefix's cosine transform is eventually negative, and the omitted tail's cosine transform is eventually positive. The tail carries the complete opposite leading term at every fixed shell cutoff.

## Dependency-closed paper proof

Every derivative of every positive-index shell is a polynomial times its Gaussian factor. The corpus proves half-line integrability and decay at infinity for these expressions; finite sums retain both properties. It also proves these properties for derivatives of the complete theta source.

For any of these profiles `f`, two justified half-line integrations by parts give the exact identity

`t² C_f(t) = −f'(0) − C_(f'')(t)`.

Since `f''` is integrable, Riemann–Lebesgue gives `C_(f'')(t)→0`. For a nonempty finite prefix, the existing exact shell-slope theorem gives `P_N'(0)>0`. For the complete source, reflection gives `Phi'(0)=0`. Subtracting the two integral identities proves the tail limit. Strict signs of the limits give the eventual signs.

All statements concern the literal source functions. No numerically evaluated integral or spectral datum enters this proof.

## Lean declarations

Module: `GaloisForLFunctions.RHTower.ThetaFiniteShellFourierBoundary`.

- `tendsto_thetaFiniteShellCosine_mul_sq`
- `eventually_thetaFiniteShellCosine_neg`
- `tendsto_thetaFullCosine_mul_sq_zero`
- `tendsto_thetaShellRemainderCosine_mul_sq`
- `eventually_thetaShellRemainderCosine_pos`

`thetaFiniteShellJet` supplies the exact finite-prefix derivatives. The source-specific conclusions have no unproved analytic or positivity assumptions.

Validation: scratch and source checks with `lake env lean` pass; the named leaf build and formal lint pass. All five conclusions have only `propext`, `Classical.choice`, and `Quot.sound` in their axiom audits. The module is imported by `RHTower.lean`; no umbrella build is used.

## Scope and surviving producer problem

This rules out treating the omitted tail as negligible relative to the leading Fourier term of a fixed prefix. It does **not** infer a Hankel failure from a negative cosine value, and it does not prove that all finite prefixes fail Hankel positivity.

The [independent Runpod experiment](../2-fully-proven/computations/theta-all-degree-source-2026-09-06/REPORT.md) supplies numerical Hankel failures for one and two shells. Their eigenvalue signs are not Lean theorems. The positive survivor established here is the exact compensation law for the complete arithmetic tail.

The remaining RH producer is positivity of every logarithmic Hankel form **after** all theta shells are combined. Reflection and the cancellation proved here do not supply that sign.
