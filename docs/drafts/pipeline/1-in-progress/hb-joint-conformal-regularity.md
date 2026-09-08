# HB joint conformal regularity

- **Stage:** 1-in-progress.
- **Goal:** unconditional formal RH proof/falsification; open.
- **Frontier map:** read-only.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

The [full original-source residual](../3-formalized/hb-full-original-source-admission.md)
is admitted and has a joint energy/operator-domain response. The
[original-wave conformal reduction](../3-formalized/hb-joint-original-wave-conformal-reduction.md)
now supplies actual coordinate derivatives, the exact conjugation, smooth
inverse, Jacobian, and density coefficient. Transferring the completed weak
response through this chart remains open; its classical representative and
differential equation are not yet established.

The [causal Laplace kernel](../3-formalized/hb-joint-causal-laplace-kernel.md)
independently identifies each fixed-forcing spatial response with one
time-causal Hilbert-valued kernel throughout the right half-plane. The
coordinate transfer below is still needed for classical field equations,
metric finite propagation and physical traces; it is not a prerequisite for
that proved time-support identity. Actual time-dependent source application
and left-QNM continuation remain open.

## Verified coordinate reduction

For t<0 and y>0, put `u=-tanh(t)`, `a=sech(t)`, so `u²+a²=1`,
`u'=-a²`, and `a'=au`. Define

`Phi(t,x,y)=(X,Y,Z)=(yu,ya,x)`, `m(t,y)=sqrt(y/a)`.

The map takes the physical chart into X>0,Y>0. Its principal derivative
coefficients satisfy

`Phi_t Phi_t^T+a²y²(Phi_x Phi_x^T+Phi_y Phi_y^T)=Y² Id`.

For `L=partial_t²+a²y²(partial_x²+partial_y²)`, the verified actual conjugation is

`L(m*(V o Phi))=m*[Y²*(Delta_E V) o Phi+(V o Phi)/4]`.

The actual Lean-checked weight derivatives give `m_t/m=-u/2`, `m_tt/m=a²/2+u²/4`,
`m_y/m=1/(2y)`, `m_yy/m=-1/(4y²)`. The three first-derivative coefficients
cancel using `u²+a²=1`; the remaining zeroth-order coefficient is exactly 1/4.
The coordinate expression is identified with the corpus's original metric
`fieldWave`, including the actual scalar Laplacian. Thus the original
independent-frequency wave becomes

`(w²-L)(m*(V o Phi))=m*[(w²-1/4)*(V o Phi)-Y²*(Delta_E V) o Phi]`.

This gives a concrete route to local regularity: transfer the actual weak
equation and energy derivatives through this chart and nonzero weight, obtaining
a Euclidean three-dimensional Laplacian with smooth local potential and source.
The Fourier-normalized Sobolev gain is now proved for every finite-dimensional
Euclidean space, including dimension three. Its application and iteration for
the actual response remain open. These identities do not establish time-causal
inversion or the extinction pairing by themselves.

The checked inverse is `(-arsinh(X/Y),Z,sqrt(X²+Y²))`; the actual Jacobian
determinant is `Y>0`. Also `norm(m)²=y/a`, so the mass-density coefficient is
`norm(m)²/(y² det D Phi)=1/Y²`. The integral change of variables and transfer
of weak tests have not yet been proved.

## Current proof obligations

The [nonseparated energy-test theorem](../3-formalized/hb-joint-nonseparated-energy-tests.md)
admits every smooth compact radial family in the actual angular energy domain
into the existing joint graph closure. Hilbert-basis truncations converge in
L² for the family, its actual radial derivative, and its angular-weighted
family; continuous assembly retains all four original graph components. The
constructed response obeys its original weak equation against these families,
and the completed radial gradient obeys the corresponding Green identity.
No test-density premise or substitute joint domain is supplied.

The next unresolved step is to identify arbitrary compact coordinate tests with
these families: prove smoothness of their actual angular L² value and derivative
slices in the angular graph norm, together with their representatives under the
canonical Bochner/product L² isometry. The family theorem does not itself
supply this coordinate-test identification.

- Transfer the actual measure and completed energy derivatives through the
  verified chart and nonzero weight.
- Admit arbitrary compact coordinate tests through the proved nonseparated
  family construction. L² density of test values alone is insufficient.
- Identify the resulting transformed weak equation, original source, and
  localization derivatives. Relate its `Fin 3 -> R` coordinate Laplacian to the
  Euclidean-space distributional Laplacian.
- Apply the proved Sobolev gain and bootstrap, then establish modular patching
  and radial boundary transfer for the actual response.

No numerical experiment is indicated: the reduction is an exact derivative
and coordinate identity whose outcome is decided by symbolic reasoning.
