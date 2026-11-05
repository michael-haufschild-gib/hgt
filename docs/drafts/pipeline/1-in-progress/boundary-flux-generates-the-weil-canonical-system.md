# Boundary flux generates the Weil canonical system

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Before first contact, the actual Fourier Riesz kernel satisfies the endpoint flux and support-variation identities below, yielding a canonical system from the explicit Weil form.

## Exact analytic targets

Let `K_a(w,z)` be the actual reproducing kernel and
`T±(z)=conj(lim_{t↓0}√log(1/t) u_z(±(a-t)))`. Prove

`∂ₐKₐ(w,z)=T₋(z)conj(T₋(w))+T₊(z)conj(T₊(w))`,

`i(z-conj(w))Kₐ(w,z)=T₊(z)conj(T₊(w))-T₋(z)conj(T₋(w))`.

The kernel, positivity before contact, entire Fourier coordinates and bounded
actual Riesz sources are formalized. The [normalized trace construction](../3-formalized/normalized-boundary-traces-of-weil-riesz-vectors.md)
is formalized for the unique continuous representative of every actual
precontact Riesz source, with both absolutely convergent renewal readouts.

[Sharp restriction](sharp-restriction-preserves-the-complete-complex-weil-domain.md)
should admit an exact interval/collar decomposition. Required analytic inputs
are the exterior response asymptotic and either uniform moving-endpoint traces
or the strong scaled collar-inverse limit. None of these is an assumed premise.

## Algebraic consequences to formalize

Reflection and real-conjugation symmetry give `T₊=T₋#` and real
`s(a)=T₋(0)`. Flux at zero and `Kₐ(0,0)>0` force `s(a)≠0`.
For the normalized even/odd pair, flux gives

`Bₐ(z)=z Kₐ(0,z)/2`,

`Aₐ(z)=((z+conj(w))Kₐ(-w,z)-(z-conj(w))Kₐ(w,z))/(4 conj(Bₐ(w)))`

for any fixed `w` with `Bₐ(w)≠0`. Thus the actual kernel recovers the entire
pair directly. Differentiating these identities and using parity should give

`∂ₐAₐ=-z s(a)⁻²Bₐ`, `∂ₐBₐ=z s(a)²Aₐ`.

## Remaining obligations

Prove the actual flux and variation identities, the origin normalization,
regularity of `s`, and the prime-entry expansion of its logarithmic derivative.
Prescribed coefficient singularities must be distinguished from breakdown of
the normalized fundamental solution. At finite contact the Weil form remains
nonnegative; strict nondegeneracy fails and an actual diagonal kernel diverges.
The construction must state this endpoint distinction exactly.
