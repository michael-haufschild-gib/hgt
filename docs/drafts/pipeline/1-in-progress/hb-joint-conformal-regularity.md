# HB joint conformal regularity

- **Stage:** 1-in-progress.
- **Goal:** unconditional formal RH proof/falsification; open.
- **Frontier map:** read-only.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

The [full original-source residual](../3-formalized/hb-full-original-source-admission.md)
is admitted and has a joint energy/operator-domain response. Its classical
representative and differential equation still require proof.

## Exact proposed coordinate reduction

For t<0 and y>0, put `u=-tanh(t)`, `a=sech(t)`, so `u²+a²=1`,
`u'=-a²`, and `a'=au`. Define

`Phi(t,x,y)=(X,Y,Z)=(yu,ya,x)`, `m(t,y)=sqrt(y/a)`.

The map takes the physical chart into X>0,Y>0. Its principal derivative
coefficients satisfy

`Phi_t Phi_t^T+a²y²(Phi_x Phi_x^T+Phi_y Phi_y^T)=Y² Id`.

For `L=partial_t²+a²y²(partial_x²+partial_y²)`, the actual proposed conjugation is

`L(m*(V o Phi))=m*[Y²*(Delta_E V) o Phi+(V o Phi)/4]`.

Paper calculation: `m_t/m=-u/2`, `m_tt/m=a²/2+u²/4`,
`m_y/m=1/(2y)`, `m_yy/m=-1/(4y²)`. The three first-derivative coefficients
cancel using `u²+a²=1`; the remaining zeroth-order coefficient is exactly 1/4.
Thus the original independent-frequency wave becomes

`(w²-L)(m*(V o Phi))=m*[(w²-1/4)*(V o Phi)-Y²*(Delta_E V) o Phi]`.

This gives a concrete route to local regularity: transfer the actual weak
equation and energy derivatives through this chart and nonzero weight, obtaining
a Euclidean three-dimensional Laplacian with smooth local potential and source.
The corpus's Fourier-normalized Sobolev gain can then be extended from the
plane to dimension three and iterated. It does not establish time-causal
inversion or the extinction pairing by itself.

## Current proof obligations

- Prove the coordinate and weight jets as actual derivatives; prove the
  displayed conjugation on actual twice differentiable fields.
- Construct the inverse chart and transfer the actual measure and weak tests.
- Identify the completed joint graph with the transformed weak equation,
  retaining localization derivatives.
- Prove the required Sobolev gain and bootstrap, then modular patching and
  radial boundary transfer for the actual response.

No numerical experiment is indicated: the reduction is an exact derivative
and coordinate identity whose outcome is decided by symbolic reasoning.
