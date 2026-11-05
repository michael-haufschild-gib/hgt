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

[Sharp restriction](../3-formalized/sharp-restriction-preserves-the-complete-complex-weil-domain.md)
admits an exact interval/collar decomposition. The exterior response and
the following variational bounds would give the support derivative.

## Collar variation by duality

Let `h≤1` be collar width and `L=log(1/h)`. For a source supported in one
interval of length `h`, translations by `t≥h` have disjoint supports.
Consequently its logarithmic form is at least
`(1+∫_h^∞exp(−t)/t dt)‖v‖²≥L‖v‖²`. The constant interval profile has exact
translation loss `2 min(t,h)`, hence energy at most `h(L+3)`. These two
bounds suffice; an operator dilation theorem is unnecessary.

Gamma, polar and finitely many prime corrections are bounded. The
old/collar crossing operator factors through the fixed bounded Gamma
Hankel operator. Completing the square against the old positive form
gives `Q(v)≥(L−C)‖v_collar‖²`. The two collars lie on opposite half-lines,
so their Gamma crossing factors through the same Hankel operator of norm
at most `2π`. Adding the bounded prime/polar remainder and using
`2xy≤x²+y²` gives the two-collar floor from the individual interval floors.

The [exact kernel increment](../3-formalized/growing-the-weil-window-adds-an-orthogonal-kernel.md)
is the Gram form of the Riesz component orthogonal to the old space.
Its intended collar equation is
`Q(δ,u)=⟨Fₕ,u_collar⟩`. If its dilated forcing divided by `√(hL)` tends
in L² to the two constant endpoint traces, Cauchy–Schwarz and the preceding
bound give the upper limit of `Q(δ)/h`. Testing with the constant collar
profile gives the matching lower limit, since its energy is `L‖v‖²+O(1)`.
The energy of the difference from that trial profile tends to zero after
division by `h`, giving the mixed kernel derivative as well. This avoids
constructing a strong inverse limit for the whole collar operator.

The full fixed-enclosure variational bound now has a Lean draft:
`(log(1/h)−C)‖v_{a+h,z}−ιv_{a,z}‖²≤‖1_(0,h]F₋‖²+‖1_(0,h]F₊‖²`.
It uses the actual residuals, exact three-interval decomposition and complete
Weil form. These drafts still require verification. Constant collar trials
and the mixed derivative remain to be formalized. Translation retains the
pole pairing because its two exponential characters are reciprocal.

Uniform boundedness of Riesz sources on compact precontact aperture ranges
would bound their localized forcings and renewal traces. Together with
kernel continuity, the resulting bounded right derivatives give local
absolute continuity. The flux identity then prevents the zero-frequency
trace from vanishing. Regularity of its logarithmic derivative is a further
requirement for the reflection function.

## Algebraic consequences to formalize

[Formalized reflection and conjugation](../3-formalized/reflection-exchanges-the-weil-endpoint-traces.md)
give `T₊=T₋#` and real `s(a)=T₋(0)`. Flux at zero and `Kₐ(0,0)>0` force `s(a)≠0`.
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
