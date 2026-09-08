# HB: original QNM frequency continuation

- **Stage:** in progress.
- **Goal:** unconditional RH proof/falsification; open.
- **Frontier map:** read-only.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and physical left-QNM pairing → independent Hawking-clock
extinction → RH.

The complete-source original joint causal response and its operator-domain
Laplace identity are constructed. Its full physical continuation and left
pairing remain open. Energy-space inversion on the opposite frequency
half-plane does not establish the required causal continuation.

## Closed radial continuation

[Original radial Green germs at every Xi QNM](../3-formalized/hb-original-qnm-frequency-germs.md)
contains the original Gauss-family frequency holomorphy, including terminating
numerators, dressed solutions, connection coefficient, and pointwise normalized
source-integrand germs at every Xi QNM.

[Original endpoint Green response at fundamental Xi QNMs](../3-formalized/hb-original-fundamental-qnm-endpoint-continuation.md)
contains eight audited leaves and 22 new public theorems. Both actual endpoint
moments of the native radial source family are continued, with equality to the
original Green response in its convergence chamber. The horizon moment uses
first Taylor subtraction with its exact source coefficient restored; its
remainder is analytic for `Re w > -2`, off the real axis. The actual outer
endpoint integral is entire before connection/source-pole normalization.

The assembled original radial response is meromorphic on that larger nonreal
strip and at both fundamental QNM frequencies for every Xi copy. Physical power
factors, source amplitudes and angular coefficients, the full connection
normalization, and the fixed smooth-onset correction are retained. This does not
assert pole survival, identify a physical left residue, or establish extinction.
Higher overtones require further endpoint Taylor orders.

[Original continued forced radial master](../3-formalized/hb-original-continued-radial-master.md)
contains eight audited leaves and 31 new public theorems. The continued native
response satisfies the original forced radial equation with actual first and
second spatial derivatives as a frequency germ at both fundamental QNMs for
every Xi copy. The proof extends the exact physical Wronskian normalization
across both nonreal half-planes, differentiates the restored horizon moment and
the true outer moment, and derives punctured-neighborhood nonvanishing of the
original connection coefficient. No nonresonance premise is supplied to the
QNM germ theorem.

## Closed complete residual admission

[Complete continued cusp-source admission](../3-formalized/hb-complete-continued-cusp-source-admission.md)
contains ten audited leaves and 40 public theorems. The actual continued radial
response is transported through the tortoise chart into the original principal
differences, full-square lift, and all three cutoff commutators. The explicit
field has actual radial derivatives and its actual metric angular Laplacian.
It agrees with the original explicit field in the source convergence chamber.

Each principal difference satisfies its original forced ODE. The potential
and native source obey `|p(t)| ≤ A exp(2t)` and
`|f(t)| ≤ B exp((Re w+2)t)`. Weighted energy of the actual channels `U'±wU`
gives `|U(t)| ≤ C exp(Re w*t)` from one interior value. This retains the
Green/lift cancellation. Multiplication by the literal horizon coordinate
recovers two powers of decay. Thus all three cutoff coefficients belong to the
original radial L² space for nonreal `w` with `-2 < Re w ≤ 0`.

Together with the already admitted native reduced coefficient and the actual
angular L² bounds, this proves admission of the complete cusp residual in the
joint L² space. `continuedOriginalSource_allXi_fundamental_admitted_germ`
proves simultaneous admission and the full original source equation on one
punctured frequency neighborhood of both fundamental QNMs for every Xi copy.
No admission, endpoint, continuation, or nonresonance premise is supplied to
that all-Xi capstone. Admission concerns the residual after subtracting the
explicit field, not the unrenormalized original angular source.

## Current hard target

Construct the complete source as a meromorphic family with values in the actual
joint function space, then continue the original causal joint response in its
outgoing weighted domain and identify the physical advanced/adjoint left
residue. Pointwise meromorphy plus pointwise L² admission does not establish
function-space meromorphy or the original causal continuation.

The next concrete source argument uses the exact common denominators, not
independent pole orders chosen separately at each radius. For one principal
channel let `c_i(w)` be its original connection coefficient and
`S(w)=1+(w-2s)*onsetCorrection(2s,w)`. Away from the zeros, multiplying the
principal difference by `-(w-2s)c_i(w)` clears its two Green moments and its
lift. Define the resulting numerator by its explicit undivided formula; at a
pole this need not equal the pointwise product of the totalized quotient.
The two endpoint integrals and their interior spatial jets already have the
required local frequency holomorphy.

Apply the proved energy argument to that undivided numerator. Bound its value
and first spatial derivative at `t=-1` on a compact frequency disk. The forcing
profile is continuous jointly on that disk times the compact radius interval,
so it has a common bound. Choose the disk strictly inside `-2 < Re w < 0` and
away from zero, retaining one positive decay margin. The energy estimate should
then supply a common L² majorant for the cleared cutoff family. This uniform
parameter step and the resulting complex L²-valued holomorphy are not yet
proved. The corpus's `L2DominatedContinuity`, `L2DominatedDerivative`, and
`CauchyDominatedIntegralHolomorphy` provide nearby building blocks; the existing
L² derivative theorem is for a real parameter and does not itself give this
complex local result.

The energy inverse on the opposite frequency half-plane does not identify the
original causal joint continuation. Retain the original outgoing endpoint
condition while constructing that response; then identify the physical left
source projection of the complete residual, including all cutoff commutators
and the restored horizon contribution. Normalized scalar Green residues remain
comparison data rather than an identification of this physical projection.

Full joint angular/metric, spin-two/AIME identification, and independent
Hawking-clock extinction remain open. No numerical experiment is indicated:
the immediate unresolved assertions concern source/domain continuation and
physical pairing, not an uncertain numerical pattern.
