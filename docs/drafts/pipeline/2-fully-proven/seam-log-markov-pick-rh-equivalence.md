# Seam-Log Markov-Pick RH Equivalence

- **ID:** seam-log-markov-pick-rh-equivalence
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / analytic source-gate normalization
- **Source:** `seam-log-hankel-rh-equivalence.md`;
  `source-aware-q0-alone-reciprocal-positivity.md`
- **Statement:** RH is equivalent to the canonical seam-log generating function being
  a Markov transform of a positive measure on `R_+`. Equivalently, the source-built
  shifted tower is in the Stieltjes cone exactly when this seam-log transform has the
  corresponding Pick/Stieltjes positivity.

## Setup

Let

`Xi(w)=xi(1/2+w)`, `Phi(z)=Xi(sqrt(z))`,

and set

`L(z)=log(Phi(z)/Phi(0))`

near `z=0`. Define the source shifted moments by

`T_k^src=-2k(-1)^k [z^k]L(z)`, `k>=1`.

Define the seam-log Markov candidate

`G_src(x)=sum_{n>=0} T_{n+1}^src x^n`.

Equivalently,

`G_src(x)=2 L'(-x)`.

Indeed, if `L(z)=sum_{k>=1} ell_k z^k`, then

`2L'(-x)=sum_{k>=1} 2k ell_k (-x)^(k-1)
        =sum_{k>=1} -2k(-1)^k ell_k x^(k-1)
        =sum_{k>=1} T_k^src x^(k-1)`.

## Theorem

For the canonical completed Riemann `xi` function, the following are equivalent:

1. RH.
2. There exists a compactly supported finite positive Borel measure `nu` on `R_+`
   such that, in a neighborhood of `x=0`,

   `G_src(x)=int_{R_+} 1/(1-xy) dnu(y)`.

3. The shifted source tower satisfies

   `sum_{i,j} c_i c_j T_{i+j+1}^src >= 0`

   for every real polynomial `p(y)=sum_i c_i y^i`.

In this case the representing measure is the weighted reciprocal divisor measure

`nu=sum_y M_y y delta_y`,

with `y=-(rho-1/2)^(-2)` and FE-folded multiplicity `M_y`.

## Proof

By the FE quotient formula, the positive-degree logarithmic coefficients of `Phi`
give the bridge reciprocal moments:

`T_k^src=T_k=sum_y M_y y^k`.

Therefore

`G_src(x)=sum_{k>=1} T_k x^(k-1)
        =sum_y M_y y sum_{n>=0} (xy)^n
        =int 1/(1-xy) dnu(y)`

near `x=0`, with

`nu=sum_y M_y y delta_y`.

If RH holds, then every reciprocal atom `y` lies in `R_+`; the reciprocal atoms are
bounded and can only accumulate at `0`, so `nu` is a compactly supported positive
finite measure on `R_+`. This proves `1 -> 2`. A positive Markov representation
gives the Hankel positivity in `3`, since

`sum_{i,j} c_i c_j T_{i+j+1}^src
 = int p(y)^2 dnu(y) >= 0`.

The implication `3 -> 1` is exactly `seam-log-hankel-rh-equivalence.md`, or equivalently
`source-aware-q0-alone-reciprocal-positivity.md` after the coefficient dictionary
`T_k^src=T_k`.

Thus all three conditions are equivalent.

The Pick formulation is the same statement in analytic language. If `nu>=0` on
`R_+`, then `G_src` maps the upper half-plane to itself by

`Im 1/(1-zy) >= 0`

for `Im z>0` and `y>=0`, with the standard Markov-transform cut on the positive
real axis. Conversely, a Markov representation by a positive measure on `R_+`
recovers the positivity condition above by expansion at `0`.

## Consequence for the RH Route

This card gives the clean analytic target:

> prove that `G_src(x)=2 d/dz log(Phi(z)/Phi(0)) |_{z=-x}` is a Markov/Pick transform
> of a positive measure on `R_+`.

But it also gives the theatre-test warning. This target is exactly RH in analytic
source coordinates. A proof cannot simply assume Herglotz, Pick, Stieltjes, passive,
or positive-real behavior of `G_src`; those words name the positivity wall. A
non-mirror proof must derive the Markov positivity from independent source rigidity:
Euler product/local orientation, completed explicit formula plus a positivity
principle, geometric polarization, or another non-equivalent constraint.

## Source Boundary

This is a coordinate theorem, not a new RH result. It packages the all-order Hankel
wall as a Markov/Pick property of the canonical seam-log derivative. The representation
measure is positive exactly in the RH case.

## Gates

- [x] 0 -> 1 in-progress: analytic source gate isolated.
- [x] 1 -> 2 fully-proven: Markov-transform equivalence proved from the seam-log
  coefficient dictionary and source-aware `Q_0`.
- [ ] 2 -> 3 formalized: would require formal wrappers for the logarithmic coefficient
  dictionary and basic moment/Markov transform positivity.

## Log

- 2026-06-24 -- Professor: created under the RH-only goal. This identifies the exact
  Herglotz/Pick/Stieltjes property left after seam-log extraction and prevents treating
  that property as an independent assumption.

## 2026-06-24 coefficient-positive shadow is too weak

`seam-log-coefficient-positivity-insufficient.md` records the first weaker analytic shadow that fails: all Taylor coefficients of a candidate `G(x)=sum a_n x^n` may be positive while the first Hankel determinant is negative. Therefore the Markov/Pick target here cannot be replaced by coefficient positivity of `G_src`; the full square-test cone is essential.

## 2026-06-24 complete-monotone shadow is too weak

`seam-log-complete-monotonicity-insufficient.md` records a second weaker analytic shadow that fails. Complete monotonicity of `G(-s)` is necessary for a positive Markov representation, but it is not sufficient: `exp(-s)` is completely monotone while its coefficient sequence fails the first Stieltjes Hankel determinant. Therefore the target here cannot be weakened to alternating derivative signs on the positive real axis.

## 2026-06-24 preconditioned Markov tests

`continuous-preconditioner-q0-visible-rh.md` records the preconditioned version of the atom-isolation gate. A bounded conjugation-symmetric weight on the reciprocal support changes the Markov/Hankel square test only by multiplying each atom by `g(y)^2`. If the weight is nonzero on all atoms, the positivity target remains equivalent to RH; if the weight vanishes, the vanished atoms are no longer tested.

Thus a preconditioned Markov/Pick transform is not a weaker route unless the hidden atoms are controlled independently from source data.

## 2026-06-24 operator-image Markov tests

`test-space-closure-q0-visible-rh.md` gives the corresponding test-space version of the Markov/Pick warning. A preconditioned or operator-restricted Markov/Hankel positivity test is controlled by the uniform closure of its test functions on the reciprocal compact support. If that closure is dense, the test remains equivalent to RH; if it is not dense, the missing closed directions specify the hidden atoms or modes that need source control.

## 2026-06-24 finite Markov prefixes do not select the target

`finite-markov-prefix-nonselection.md` gives the finite-prefix version of this warning. Any finite coefficient prefix of the Markov candidate can be preserved while a later Hankel square test is forced to fail. If the prefix has a positive representing continuation, the same prefix still admits a bad continuation.

Thus finite Markov/Pick interpolation, finite Padé or continued-fraction data, and finite Hankel/Cholesky checks are calibration only. A proof must control the all-order Stieltjes cone from source data.

## 2026-06-24 divided log-derivative weld

`seam-log-derivative-weld-identity.md` proves the coordinate identity

`G_src(-w^2)=Xi'(w)/(w Xi(w))`.

Thus the Markov/Pick target here is the completed log-derivative after division by the seam coordinate and the square substitution `x=-w^2`. A carrier-based route must prove the Stieltjes cone condition for this divided even function. The identity itself is only normalization; it supplies no positivity.

## 2026-06-24 log-convex shadow is too weak

`all-order-log-convexity-does-not-imply-stieltjes.md` records a third weaker analytic shadow that fails. A positive sequence can satisfy every adjacent Turan/log-convex inequality while its degree-two Hankel determinant is negative.

Therefore the Markov/Pick target here cannot be weakened to all adjacent `2 x 2` Hankel minors. The proof must control arbitrary polynomial square tests, or supply a source theorem that upgrades the low-rank inequalities to the full Stieltjes cone.

## 2026-06-24 fixed-rank Hankel shadows are too weak

`fixed-rank-hankel-tests-do-not-imply-stieltjes.md` records the bounded-rank version of the Markov/Pick warning. For any fixed `r`, all shifted Hankel blocks up to size `r` can be positive definite while the next block is indefinite.

Therefore the Markov/Pick target here cannot be replaced by any fixed-size Hankel hierarchy. The source theorem must control arbitrary-degree polynomial square tests, or supply a genuine upgrade from bounded rank to the full Stieltjes cone.

## 2026-06-24 single-frequency Markov failure

`single-even-frequency-not-stieltjes.md` shows that the Markov/Pick target here cannot be proved frequency-by-frequency on FE-even Euler source atoms. A single positive germ `B(cosh(lambda w)-1)` gives an indefinite shifted Hankel block after the seam-square transform.

Thus the source theorem must prove positivity for the completed seam-log object, not for isolated positive frequencies.
