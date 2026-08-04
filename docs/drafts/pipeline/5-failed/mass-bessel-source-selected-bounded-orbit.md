# Mass-Bessel source-selected bounded orbit

**Stage:** Failed / retired  
**Date frozen:** 2026-08-04  
**Label:** `[FALSIFIED]`  
**Parent route:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3

## 1. Exact claim, frozen before attack

Fix `a>1/2` and apply the critical gauge `e^{-y/2}` to the positive-frequency
Klein--Gordon representation of the mass-Bessel field.

> The completed prime--Gamma Cauchy datum belongs to a nonzero, closed,
> two-sided invariant subspace on which the critical-gauge Klein--Gordon orbit
> is uniformly bounded.  Boundary evaluation on that subspace then yields
> `P_a(\sigma+iu)=O(1)`.

Unlike the preceding positive-energy conjecture, this claim allowed the full
group to be nonnormal and asked positivity/boundedness only on a source-selected
subspace.

## 2. Hostile attack

For `a>\lambda>0`, let

\[
 \widehat{G_{a,\lambda}(u)f}(\xi)
 =e^{-iu(p(\xi)+iq(\xi))}\widehat f(\xi),
 \qquad
 p(\xi)+iq(\xi)=\sqrt{(\xi-i\lambda)^2+a^2}.
\]

The exact gauge calculation gives

\[
 q(\xi)>0\quad(\xi<0),\qquad
 q(\xi)<0\quad(\xi>0),\qquad q(0)=0.
\]

Let `f\ne0` in `L^2`.  At least one of the sets

\[
 E_+=\{\xi:q(\xi)>0,\ \widehat f(\xi)\ne0\},
 \qquad
 E_-=\{\xi:q(\xi)<0,\ \widehat f(\xi)\ne0\}
\]

has positive measure, because `{0}` is null.  If `E_+` has positive measure,
then for some integer `N\ge1` the set

\[
 E_{+,N}=\{\xi:q(\xi)\ge 1/N,\ |\widehat f(\xi)|\ge1/N\}
\]

has positive measure.  Hence

\[
 \|G_{a,\lambda}(u)f\|_2^2
 \ge e^{2u/N}N^{-2}\,|E_{+,N}|\longrightarrow\infty
 \qquad(u\to+\infty).
\]

If `E_-` has positive measure, the same argument with `u\to-\infty` applies.
Therefore

\[
 \sup_{u\in\mathbb R}\|G_{a,\lambda}(u)f\|_2=\infty
 \qquad\text{for every nonzero }f\in L^2(\mathbb R).
\]

The two-sided uniformly bounded orbit subspace is exactly `{0}`.  No special
prime--Gamma vector can evade this theorem while remaining a nonzero vector in
the critical-gauge `L^2` state space.

## 3. Verdict

`[FALSIFIED]`.  A source-selected **state** subspace cannot be the missing
mechanism.  The open core concerns a single scalar **observation** of an
internally growing orbit.

Any surviving formulation must therefore permit unbounded bulk state while
proving exact cancellation after boundary observation.  Calling that
cancellation a stable subspace merely hides the arithmetic premise.

## 4. Strongest positive survivor

The bounded-orbit rigidity theorem is dependency-closed and is recorded in
`docs/drafts/pipeline/2-fully-proven/mass-bessel-bounded-orbit-rigidity.md`.

It upgrades the earlier no-unitarization result: not only is there no global
positive conserved norm, there is no nonzero two-sided bounded vector at all in
the critical exponentially weighted `L^2` representation.

## 5. Higher universal principle

The mass-Bessel/RH problem is an output-stability problem for a nonnormal
transfer system:

\[
 \text{prime--Gamma input}
 \longrightarrow \text{exponentially growing internal KG orbit}
 \longrightarrow \text{bounded scalar trace?}
\]

RH-strength information must appear as a pole--zero/radiation cancellation in
the observation channel.  It cannot be recast as bounded internal dynamics.

## 6. Corpus collision

This conclusion matches the source-modular corpus's statement that common
Hilbert-positive invariant forms vanish away from neutrality and only
hyperbolic cross-pairings survive.  The new point is sharper for this route:
even a non-positive source-selected bounded `L^2` orbit is impossible.

## 7. Lean status

`[PAPER-PROVED]`, not yet `[LEAN-PROVED]`.  Formalization belongs to the
positive-survivor card.
