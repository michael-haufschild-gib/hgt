# Mass-Bessel critical-gauge positive energy

**Stage:** Failed / retired  
**Date frozen:** 2026-08-04  
**Label:** `[FALSIFIED]`  
**Parent route:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3

## 1. Exact claim, frozen before attack

Fix `a > 1/2`.  Write the mass-Bessel atom as

\[
 \kappa_{a,t}(x)
 =\frac{2at}{\sqrt{t^2+x^2}}
   K_1\!\left(a\sqrt{t^2+x^2}\right),
 \qquad \Re t>0.
\]

The conjecture was:

> After the critical spatial gauge `V(u,y)=e^{-y/2}U(u,y)`, the complex-time
> continuation `t=\sigma+iu` of the mass-Bessel prime field admits a positive,
> coercive, conserved Hilbert energy equivalent to its natural Cauchy-data norm.
> That energy uniformly controls the boundary observation `U(u,0)`.

This would have converted the open bound `P_a(\sigma+iu)=O_{a,\sigma}(1)` into
an energy estimate rather than another cancellation estimate.

## 2. Why the conjecture was plausible

For `\Re t>0`, Fourier inversion gives

\[
 \kappa_{a,t}(x)
 =\int_{\mathbb R}e^{-t\sqrt{\xi^2+a^2}}e^{i\xi x}\,d\xi
\]

under the corresponding Fourier normalization.  Hence every atom with
`t=\sigma+iu` solves

\[
 U_{uu}-U_{yy}+a^2U=0.
\]

Thus the apparently exotic vertical Bessel trace is a boundary observation of
ordinary `1+1` dimensional massive Klein--Gordon propagation.  The mass gap
made a coercive complex-time energy look possible.

## 3. Hostile attack

Use a general exponential gauge `V=e^{-\lambda y}U`, with
`0<\lambda<a`.  The gauged equation is

\[
 V_{uu}-V_{yy}-2\lambda V_y+(a^2-\lambda^2)V=0.
\]

One half-wave on standard `L^2(\mathbb R)` is the Fourier multiplier

\[
 \widehat{G_{a,\lambda}(u)f}(\xi)
 =\exp\!\left(-iu\sqrt{(\xi-i\lambda)^2+a^2}\right)\widehat f(\xi),
\]

with the principal square root.  Write

\[
 \sqrt{(\xi-i\lambda)^2+a^2}=p(\xi)+iq(\xi).
\]

Squaring gives

\[
 p^2-q^2=\xi^2+a^2-\lambda^2,
 \qquad pq=-\xi\lambda.
\]

Moreover

\[
 q(\xi)^2
 =\frac{\left|(\xi-i\lambda)^2+a^2\right|
       -(\xi^2+a^2-\lambda^2)}{2}.
\]

Since

\[
 (\xi^2+a^2+\lambda^2)^2
 -\left|(\xi-i\lambda)^2+a^2\right|^2
 =4a^2\lambda^2>0,
\]

we have `|q(\xi)|<\lambda` for every finite `\xi`.  Conjugation symmetry and
the sign of the imaginary part give

\[
 q(-\xi)=-q(\xi),\qquad
 \lim_{\xi\to-\infty}q(\xi)=\lambda,
 \qquad
 \lim_{\xi\to+\infty}q(\xi)=-\lambda.
\]

Therefore

\[
 \|G_{a,\lambda}(u)\|_{L^2\to L^2}=e^{\lambda|u|}.
\]

This is an exact equality, not an upper-bound artefact.  If an equivalent
Hilbert norm were conserved, norm equivalence would make
`\|G_{a,\lambda}(u)\|` uniformly bounded in `u`, contradicting the equality.
At the prime-critical gauge `\lambda=1/2`, the exact growth is
`e^{|u|/2}` for every `a>1/2`.

## 4. Verdict

`[FALSIFIED]`.  Mass changes dispersion but not exponential type selected by
the spatial gauge.  No positive coercive conserved energy equivalent to the
gauged `L^2` Cauchy norm can prove the required uniform boundary bound.

This also explains the already observed `e^{|u|/2}` barrier: it is the exact
spectral growth bound of the critical exponential gauge, not a weakness of
the Bessel asymptotics.

## 5. Strongest positive survivor

The exact multiplier norm and its no-unitarization corollary survive.  Complete
paper proof is recorded separately in
`docs/drafts/pipeline/2-fully-proven/mass-bessel-exponential-gauge-growth-law.md`.

The route may still use an indefinite/Krein pairing or a source-selected
stable graph, but positivity would then have to be proved on the completed
prime--Gamma source itself.  Global Klein--Gordon energy cannot supply it.

## 6. Universal principle exposed

The obstruction is a gauge law:

> In complex-time spectral traces, exponential source density fixes vertical
> growth.  A mass gap moves phase and localizes the real-time kernel, but it
> cannot reduce growth imposed by the source's exponential spatial gauge.

For the zeta source, prime density selects `\lambda=1/2`.  Any successful route
must cancel or select the unstable critical-gauge modes; it cannot coerce them
away with positive bulk energy.

## 7. Prior-art and corpus collision audit

- Weighted/non-positive Klein--Gordon spectral theory already allows Krein
  energies and non-real spectrum; see Georgescu--Gérard--Häfner,
  <https://doi.org/10.4171/JST/93>.  The elementary exact norm law here is a
  route-specific bridge, not a claim of a new Klein--Gordon theory.
- `docs/drafts/pipeline/1-in-progress/harmonic-invisibility-and-the-one-over-delta-law.md`
  independently found the same `1/2` exponential barrier by Bessel saddle
  analysis.  The gauge calculation identifies its operator-theoretic cause.
- `docs/drafts/pipeline/4-publication-ready/riemann-source-modular-superselection/`
  already proves that positive Hilbert invariant forms lose orientation.  The
  present counterexample is the mass-Bessel realization of that general
  obstruction.

## 8. Lean status

`[PAPER-PROVED]`, not yet `[LEAN-PROVED]`.  No Lean theorem is claimed on this
failed card.  Formalization belongs to the positive-survivor card.
