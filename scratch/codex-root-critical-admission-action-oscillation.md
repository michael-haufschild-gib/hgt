# Critical admission action oscillation — paper proof, Lean open

Own scratch research note. The route map is read-only. This theorem is about the literal CCM-FU critical source, not about RH or a paid prime history. Exact literature priority has not been established.

## Theorem

Let `C(x)=criticalContinuousAbel x`, the corpus's real square-root Abel interpolation of the complete `ψ−x+2γ` source, and define

`A(R)=∫_1^R C(x)x^(-5/2) dx` for `R≥1`.

Then `A(R)→0` as `R→∞`, but `A` takes strictly positive and strictly negative values beyond **every** cutoff. In particular, the scalar cumulative admission action has no eventual sign. This is an unconditional two-sided sign theorem, not an estimate of the pointwise growing-core covariance.

## Proof audit

1. The corpus's strong `ψ` PNT gives `C(x)=O(x^(3/2)exp(-b√log x))` for some `b>0`, so `C(x)x^(-5/2)` is absolutely integrable on `[1,∞)`. The existing exact Abel–Mellin identity and zero-mass current gap give `∫_1^∞C(x)x^(-5/2)dx=0`; hence `A(R)=-∫_R^∞C(x)x^(-5/2)dx→0`. The first quotient-cell identity `C(x)=(√x−1)(2γ−1)>0` on `(1,2]` shows `A` is not identically zero.

2. For `Re z>0`, put `F(z)=∫_1^∞ A(R)R^(-z-1)dR`. Integration by parts, using `A(1)=0` and `A(R)→0`, yields `F(z)=J(z+3/2)/z`, where `J(w)=∫_1^∞C(x)x^(-w-1)dx`. The corpus's Mellin/current identities therefore continue `F` meromorphically as

   `F(z)=[T(1)-T(z+1)]/[2 z (z+1)(z+3/2)]`,

   with `T=centeredPrimeTailCurrentContinuation`. The corpus's finite-order current gap makes the apparent singularity at `z=0` removable. At every real `z∈[-1/2,0)`, the point `z+1` lies in `[1/2,1)`, where the corpus proves `ζ(z+1)≠0`; the other factors are nonzero. Thus `F` is holomorphic near every real point of `[-1/2,0]`.

3. The corpus proves existence of a nonreal zeta zero `ρ=1/2+iγ`. At `z=ρ−1`, the log-derivative contribution to `T(z+1)` has a genuine pole: if `ρ` has multiplicity `m`, its residue is `m`, while the ordinary zeta and regular slope terms cannot cancel it. Consequently `F` has a genuine nonreal pole with real part `−1/2`.

4. Suppose `A` is eventually nonnegative. Remove its finite initial segment, whose Mellin transform is entire; the remaining nonnegative tail has a finite abscissa of convergence `α`. Convergence for `Re z>0` gives `α≤0`; the nonreal pole at `ρ−1` gives `α≥−1/2`. Landau's theorem for Mellin/Laplace transforms of a nonnegative function says its transform must be singular at the **real** abscissa `α`. Step 2 says the meromorphic continuation is holomorphic at every possible `α∈[-1/2,0]`, a contradiction. Apply the same argument to `−A` to exclude eventual nonpositivity. Thus both signs recur arbitrarily late.

The Landau step is not a claim that the nonreal pole is the rightmost pole; it only supplies the lower bound `α≥−1/2`. Any hypothetical off-line zeros could move `α` rightward, but the entire real interval `[-1/2,0]` remains pole-free, so the contradiction is unconditional.

## Whole-route meaning

The first quotient cell charges every near-birth delay positively, but the complete cumulative action is unavoidably two-sided arbitrarily far out. A globally positive scalar admission potential is therefore false for the literal source. The **positive survivor** is an unlimited supply of both signs in the exact source; it may be used by a source-selected history, but gives no amplitude, packing, or pointwise covariance bound by itself. The next hard gate remains a quantitative signed, local-in-cutoff payment under exhaustive core growth.

Lean status: the source Mellin/current identities, nonflat jet, nonreal zero existence, real-strip zeta nonvanishing, and generic continuous Landau transfer are already formal in the corpus. Their composition for this specific cumulative `A`, including boundary absolute integrability and the genuine zero-pole argument, is **not** Lean-closed. No computations or full builds were run.
