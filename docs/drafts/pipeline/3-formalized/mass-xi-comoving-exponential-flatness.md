# Mass-Xi co-moving exponential flatness

- **Stage:** 3 — formalized in Lean 4
- **Date opened:** 2026-08-05
- **Parent:** `mass-xi-comoving-prime-extinction`
- **Target:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3

## Frozen conjecture C18

Let `F` be an admissible abstract spectral family, `a >= 2`, `|u| <= a`, and
`sigma > 1/2`.  Define

\[
  \kappa_\sigma=\frac{2\sigma}{3}-\frac3{16}>0.
\]

Then

\[
 \|\Theta_F^{(a)}(\sigma+iu)\|
 \le e^{-\kappa_\sigma a}\Theta_F(\kappa_\sigma).
\]

For the Xi schedule `A(u)=|u|+2`, the complete Gamma channel obeys the
same rate after a fixed smaller-time comparison.  Consequently the literal
co-moving von-Mangoldt source, and hence the difference between the canonical
mass-semigroup high-pass and the fixed source, is bounded by

\[
 e^{-\kappa_\sigma(A(u)-1/2)} C_\sigma.
\]

## Numerical pre-certification

A high-precision hostile grid over masses and spectral heights spanning four
orders of magnitude, with displacement `0.499999999` and lines down to
`sigma=0.500001`, left strictly positive margin in

\[
 \sigma M-a|K|-\kappa_\sigma(a+R).
\]

Smallest sampled margin was greater than `0.1033` at the near-threshold line.
This is only pre-certification; proof below is exact.

## Exact proof plan

Write the mass root as `M+iK` and the original point as `R+iJ`.

1. From `M^2 >= R^2-J^2+a^2`, `|J|<1/2`, and `a>=2`, prove
   `2(a+R) <= 3M`.
2. Charge conservation gives `M|K|=R|J|<=R/2`.  Combining the first
   inequality with `4aR <= (a+R)^2` gives
   `a|K| <= 3(a+R)/16`.
3. Therefore
   `-sigma M+uK <= -kappa_sigma(a+R)`, yielding the termwise bound.
   Summation is against `exp(-kappa_sigma R)`, already summable by the
   abstract-family interface.
4. For the Gamma channel, split real time between mass and a fixed reference
   mass.  The centered root is at least both `a` and its reference root; the
   crossed-pole frequency is at least `a-1/2` and its reference frequency.
5. Insert both bounds into the exact Euler-source identity.

## Hostile significance test

If true, this is stronger than the existing `C_0` theorem and not a renamed
RH-equivalent bound: it is unconditional, source-side, and gives a positive
decay exponent uniformly as `sigma -> 1/2+`.  It also kills every polynomially
rescaled finite co-moving aperture response.  Thus the earlier pointwise
charge recovery `aK -> RJ` cannot survive summation at positive real time;
any recovery bridge must be exponentially renormalized or genuinely cofinal.

## Lean certificate

- Abstract module:
  `formal/GaloisForLFunctions/HTGeometry/AbstractSpectralComovingExponential.lean`.
- Xi module:
  `formal/GaloisForLFunctions/RHTower/XiMassComovingPrimeExponential.lean`.
- Both modules are wired into their umbrella imports.
- Direct `lake env lean` checks — PASS.
- `lake build GaloisForLFunctions.HTGeometry.AbstractSpectralComovingExponential`
  — PASS (`[2750/2750]`).
- `lake build GaloisForLFunctions.RHTower.XiMassComovingPrimeExponential`
  — PASS (`[9394/9394]`).
- Axiom audit of joint root geometry, transverse bound, abstract trace rate,
  Gamma mass-gap law, literal prime rate, and high-pass quotient — PASS; only
  `propext`, `Classical.choice`, and `Quot.sound` occur.

Principal declarations:

- `HTGeometry.AbstractSpectralFamily.two_mul_mass_add_re_le_three_mul_mass_re`;
- `HTGeometry.AbstractSpectralFamily.sixteen_mul_mass_mul_abs_im_le_three_mul_add_re`;
- `HTGeometry.AbstractSpectralFamily.norm_mass_traceC_le_comoving_exponential`;
- `RHTower.xiMassBottomArchUniformBound_le_exponential_gap`;
- `RHTower.norm_xiMassBottomPrimeIntegral_comoving_le_exponential`;
- `RHTower.norm_xiMassPrimeSemigroupHighPass_sub_fixedSource_le_exponential`.

## Verdict

`[LEAN-PROVED] [LOCAL-RESEARCH] [NOVELTY UNVERIFIED]`.  Co-moving correction
lies in an explicit exponentially weighted ideal, with rate greater than
`7/48` on every line `sigma>1/2`.  Pointwise charge recovery and source-level
recovery diverge categorically: all polynomially scaled adaptive source values
still vanish.  Any surviving bridge must use exponential renormalization or a
cofinal arithmetic observable.
