# CLG/TTF strict rank-three theta mixture

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Target:** Strict positivity of the actual center-mixed reflected rank-three Hankel determinant at every physical aperture `0<a<1/2`.
- **Chain:** Global native theta D1 → strict rank-three positive mixture → finite five-point cusp → theta-specific all-packet positivity and cofinal no-escape → Weil criterion → RH. The last two steps remain independent obligations.

## Corpus basis

`ThetaCuspFullReflectionEighthGlobal` supplies source D1. `HedenmalmCenterMixedSixthHankelClosure` supplies the existing physical mixture and derivative-product integrability. `FourthCurvatureMixture.integral_twoByTwo_det_pos` supplies the lower minor of the integrated matrix.

## Paper mechanism

For a symmetric Hankel matrix with entries `p0,p2,p4,p6,p8`, let `d=p0*p4-p2²` and `D` be its determinant. Its quadratic form `Q(x,y,z)` satisfies

`p0*d*Q = d*(p0*x+p2*y+p4*z)² + (d*y+(p0*p6-p2*p4)*z)² + p0*D*z²`.

Thus positive first entry, second leading minor, and determinant imply `Q>0` whenever `z≠0`. For the integrated entries `A,B,C,D,E`, evaluate the pointwise form at `(B*D-C²,B*C-A*D,A*C-B²)`. Its integral is the integrated second minor times the integrated determinant. Strict positivity of the integral forces the latter determinant positive. No uniform pointwise eigenvalue gap is needed.

## Remaining formal work

1. Verify the generic division-free square identity and strict integration argument.
2. Supply every literal weighted theta jet and integrability input through order eight.
3. Connect the result to actual center derivatives; audit the exact theorem and wire all new modules.

No assumed D1, assumed mixture sign, numerical observation, or added axiom may remain in the source theorem.
