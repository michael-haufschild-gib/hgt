# Mass-shifted filtered Gamma transmutation

- **ID:** `mass-shifted-filtered-gamma-transmutation`
- **Stage:** 3-formalized
- **Route:** U, mass-shifted reciprocal-Hankel propagation
- **Scientific status:** `[LEAN FORMALIZED] [UNCONDITIONAL] [NOVELTY UNVERIFIED]`
- **Paper source:** `mass-shifted-parabolic-degree-horizon`, PDH.3--PDH.4; `mass-xi-finite-true-prime-cone`, C43-BA
- **Lean module:** `GaloisForLFunctions.RHTower.XiShiftedFilteredGammaTransmutation`

## Result

For `p(X)=sum_(i=0)^d c_i X^i`, positive `y`, and

\[
 Q_{p,d,y}(W)=\sum_{i=0}^d c_i(W+y)^{d-i},
\]

Lean proves the literal shifted-Xi identity

\[
 c^T H_{d+1}(y)c=
 \frac1{(2d)!}\int_0^\infty t^{2d}e^{-yt}
   \Re\mathcal H_{Q_{p,d,y}}(t)\,dt.
\]

The more general tail form with cutoff `M` is also formal:

\[
 \int_0^\infty t^{2M+2d}e^{-yt}\mathcal H_Q(t)\,dt
 =(2M+2d)!\sum_{i,j=0}^d c_i c_j\mu_{2M+i+j}(y).
\]

This is not an abstract theorem with analytic premises. Definitions are actual multiplicity-exact
Xi divisor, actual shifted reciprocal moments, and actual polynomial-square Xi heat trace.

## Conjecture loop and progress

**Conjecture.** Filter-before-average transmutation might require new coefficient-uniform heat
estimates merely to justify Fubini.

**Hostile test.** Evaluate shifted reversal at one squared Xi node before estimating it. Its
`(W+y)^d` factor cancels exactly against `2d` powers of shifted resolvent denominator. Remaining
majorant is constant times norm of existing shifted polynomial trace-Hankel atom.

**Survivor.** Absolute integral norms are summable by already-proved trace-Hankel summability.
Therefore integral--divisor interchange closes without RH, sign premise, coefficient norm, or
computational certification. This is significant infrastructure for actual parabolic theorem,
not fake abstraction: it proves load-bearing noncommutative order "filter, then average" on literal
source objects.

## Formal capstones

- `eval_xiShiftedReversedPolynomial_eq`
- `integral_xiShiftedFilteredGammaKernel_eq_traceHankel`
- `integral_xiShiftedFilteredGammaKernel_eq_momentSum`
- `integral_xiShiftedFilteredGammaKernelReal_eq_momentSum`
- `integral_xiShiftedFilteredGammaKernelReal_eq_hankelQuadratic`
- `xiShiftedReciprocalHankelQuadratic_eq_normalizedFilteredGamma`
- `xiShiftedReciprocalHankelQuadratic_one_eq_normalizedFilteredGamma` (premise-free)

## Exact limit

Identity supplies no sign. Full parabolic degree horizon still requires literal unconditional
coefficient-uniform ultraviolet lower bound, global lower envelope, and scalar Gamma-tail
comparison. An abstract hypothesis version would not close route and is not claimed.

## Verification

- direct `lake env lean GaloisForLFunctions/RHTower/XiShiftedFilteredGammaTransmutation.lean`
- forbidden-declaration scan
- `#print axioms` for seven public capstones: only `propext`, `Classical.choice`, `Quot.sound`
- targeted `lake build GaloisForLFunctions.RHTower.XiShiftedFilteredGammaTransmutation`:
  `Build completed successfully (9574 jobs).`
- imported by `GaloisForLFunctions.RHTower`
