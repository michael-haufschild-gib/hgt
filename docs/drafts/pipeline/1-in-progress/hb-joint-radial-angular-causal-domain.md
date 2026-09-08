# HB joint radial–angular causal domain

- **Stage:** 1-in-progress
- **Goal:** unconditional closed Lean proof/falsification of RH; still open.
- **Frontier map:** read-only.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

The independent-frequency endpoint radial response is formalized in
[the radial card](../3-formalized/hb-independent-frequency-radial-inverse.md).
Its supplied scalar angular parameter does not assemble the actual angular
operator. The joint spatial domain and inverse are constructed in
[the joint spatial proof](../3-formalized/hb-joint-spatial-domain-and-wave-inverse.md).
The exact cusp-subtracted source and the differentiated explicit field are
constructed in [the source-admission proof](../3-formalized/hb-full-original-source-admission.md).
The current target is classical regularity and modular globalization of the
joint correction, followed by time-causal inversion of the actual source family.

## Constructed joint domain and inverse

Use original tortoise coordinate t<0 and invariant modular measure mu. The
scalar potential underlying the coexact stream has spatial expression
`P=-partial_t²-sech(t)²*Delta_modular`, obtained from the original normalized
wave and the actual coexact intertwining identity. This is a source-independent
operator on `L²((volume restricted to t<0) product mu)`.

Its energy domain is the closure of the actual value/derivative graph
of finite sums `f(t)*g(z)`, where f is smooth with compact support in t<0 and g
belongs to the corpus's full smooth compact modular core. Graph components are
`f*g`, `f'*g`, `sech(t)*f*D_1 g`, and `sech(t)*f*D_2 g`. The graph norm retains
all three spatial derivative terms. Density follows from the existing separated
L² product theorem and actual factor-core density. Proved local integration by
parts establishes graph closability and faithful scalar projection.

The Friedrichs-form construction provides the actual joint self-adjoint energy
operator A. Rotation of the wave form by conjugate w gives a bounded inverse
for every Re(w)>0, including positive real w. The response belongs to the
unbounded domain and solves `(A+w²-1)u=F`, with
`||u||_L² <= ||F||_L²/(Re(w)*|w|)`. Original tortoise radius and angular weight
identities are proved. Ten canonical leaves and forty public theorems cover
this construction; no angular eigenvalue is supplied.

For the literal source, coexact potentials retain both S² and its hyperbolic
gradient energy. Existing identity `D_ang J=2(s+1)(s+2)J+2K` must enter the
operator calculation. Principal cusp powers require explicit radial responses
and a global cusp cutoff; the residual forcing must be proved in the actual
joint Hilbert space with every cutoff derivative and native remainder retained.

## Constructed full-source admission

The exact identity `Delta Q=2(s+1)(s+2)Q+E` absorbs the complete gradient
source into an explicit radial multiple of Q. With `u=1/r`,
`R=exp(w*t)*a0²*(1+u)^(2s)*T`, and `b=-s(s-1)*R*u³/4`, actual differentiation
gives `F_original=W_w(bQ)+C(t)Q`. The original gradient potential remains E/2,
and the normalized-wave multiplier remains `-2*(r²-1)/r³`. The same reduction
is proved for the actual full covectors.

For the literal two-Weyl-leg principal square `Q0=P²/2`, retain all three
powers `y^(2rho)`, `y`, and `y^(2-2rho)`. Only these powers use scalar
parameters `chi_i=I*(k_i-1/2)`. Their actual endpoint Green responses g_i and
differences `d_i=g_i-b*J_i` are proved in radial L² on the entire tortoise
half-line, in a common nonempty right frequency half-plane. Endpoint limits
and exact exponential factorization supply these bounds.

For the smooth cusp cutoff eta, set
`U0=bQ+sum_i d_i*eta*y^k_i` and
`M_i=Delta(eta*y^k_i)-eta*k_i*(k_i-1)*y^k_i`.
Actual radial and angular derivatives give

`F_original-W_w U0=C*(Q-eta*Q0)+sum_i z*d_i*M_i`, `z=1-u²`.

The full native squared-scalar remainder and every actual cutoff commutator
are proved in angular L². Products with the proved radial coefficients admit
the complete residual in the joint space. Its L² vector agrees almost
everywhere with the original differential residual. The constructed joint
response solves the actual unbounded-domain equation and obeys the sharp
frequency bound. No separate gradient-tail L² premise is needed.

Seventeen new leaves in namespace `RHTower.D4BMJointSource` contain this
construction; `originalSource_response` is the combined theorem. See the
source-admission card for the exact coefficients, proof, and audit status.

## Required completion

- Prove a classical modular representative of the joint correction, including
  the cusp patch and radial boundary conditions. The smooth explicit field
  already has its actual derivative identity; the energy correction still
  needs this regularity and differential identification.
- Prove the original coexact wave equation for the assembled source response,
  using the proved coordinate, graph, and full-source identities.
- Identify the resulting full field and its time-causal inversion.
- Continue constrained Einstein reconstruction, left-QNM action pairing, and
  independent extinction; none follows from positive-operator existence alone.

No numerical experiment is planned. These are exact domain, coordinate, and
source-admission questions supported by existing corpus mathematics.
