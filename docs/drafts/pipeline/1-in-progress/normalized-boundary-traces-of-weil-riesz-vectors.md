# Normalized boundary traces of Weil Riesz vectors

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For every precontact aperture `a` and Fourier parameter `z`, the physical
  evaluation Riesz vector has a continuous representative `u` and finite limits
  `τ±(u)=lim_{t↓0} sqrt(log(1/t)) u(±(a-t))`.

## Analytic route

The local Weil operator is the compression of
`G-c-Kμ`, where `G=(1/2)log(1-D²)` and `μ` is a finite signed measure containing
every active prime atom and the polar kernel. Boundedness of the actual Riesz
vector makes its `G`-forcing bounded.

`evalVector_operator_domain_and_apply` now proves the actual restricted Weil
equation, with the bounded compact exponential image given by
`evaluationForcing_coeFn` and `evaluationForcing_bounded`.
The exact conversion to the positive logarithmic Dirichlet equation, including
the actual operator domain and bounded full forcing, is
[formalized](../3-formalized/the-weil-riesz-equation-is-a-logarithmic-dirichlet-equation.md).

Apply the fixed positive reference `H=1+G` with interior forcing `h=f+u`.
The proposed trace argument uses its half-line Green kernel
`G₊(x,y)=∫₀^{min(x,y)}v(x-s)v(y-s)ds`, where `v=V′` and
`V(x)~1/sqrt(log(1/x))`. For bounded interval forcing `h`, zero extension to the
half-line adds exterior forcing `g(y)=-∫₀^ℓ n(y-s)u(s)ds`, with
`n(t)=exp(-|t|)/(2|t|)`. This exterior forcing is integrable, with only a
logarithmic singularity at `ℓ` and an exponential tail.

A direct continuity argument should avoid a separate boundary regularity theorem.
Set `H(s)=∫_s^∞v(y-s)g(y)dy`. For small `s`, the contribution from `(s,ε)` is
bounded by `‖h‖∞V(ε)`. On `(ε,∞)`, decreasing `v` supplies the integrable
majorant `v(ε/2)|g(y)|`; thus `H(s)→H(0)` as `s↓0`.
Fubini gives `u(x)=∫₀ˣv(x-s)H(s)ds`. Dividing by `V(x)=∫₀ˣv(t)dt` makes
this a positive weighted average, so `u(x)/V(x)→H(0)`.
Local translation continuity of the integrable kernel `v` gives a continuous
representative. This argument still requires the actual Green representation.

## Removing the logarithmic singularity

For `r(t)=ω(t)-exp(-t)/(2t)`, the bounds
`1-exp(-2t)≤2t`, `exp(-t)≤exp(-t/2)`, and
`2ω(t)≤1/t+1/2` give `0≤r(t)≤3/4` for `t>0`.
The tail is dominated by `ω`, hence the even extension of `r` is integrable.
The Abel logarithmic identity then gives the exact symbol decomposition

`2θ′(ξ)=(1/2)log(1+ξ²)+c₀-2∫₀∞r(t)cos(ξt)dt`,

where `c₀=2θ′(0)+2∫₀∞r(t)dt`. The identity, positivity and integrability of
the even remainder, and its bounded self-adjoint convolution are
[formalized](../3-formalized/the-weil-symbol-has-an-integrable-logarithmic-remainder.md).

## Sources and proof obligations

[Boundary traces and support variation for localized Weil operators](https://rstation.ai/problems/riemann_hypothesis/papers/67)
gives this argument for bounded domain vectors and applies it to eigenfunctions.
Its renewal input is
[Grzywny–Ryznar](https://arxiv.org/abs/1107.0745v1); boundary continuity uses
[Hernández-Santamaría–López Ríos–Saldaña](https://arxiv.org/abs/2401.18033v2).
These are proof leads, not imported Lean assumptions.

Required formalization: half-line renewal
factorization and normalization; domain extension with its exterior forcing;
Green representation; continuity and the normalized convolution limit.
The reference factorization is isolated in
[the half-line logarithmic Green kernel](the-half-line-logarithmic-green-kernel.md). Riesz forcing must be derived from
the completed Weil equation. No numerical evidence enters these claims.

## Consequence sought

For `v_z` the evaluation vector, put `T±(z)=conj(τ±(v_z))`.
The required shape identities are

`∂ₐKₐ(w,z)=T₋(z)conj(T₋(w))+T₊(z)conj(T₊(w))`,

`i(z-conj(w))Kₐ(w,z)=T₊(z)conj(T₊(w))-T₋(z)conj(T₋(w))`.

The second should follow by translating the interval. With `Eₐ=T₋` and a
continuous real normalization at zero, these identities suggest
`∂ₐEₐ(z)=-izEₐ(z)+q(a)Eₐ♯(z)`, where `q=∂ₐlog|Eₐ(0)|`.
For `L=2a`, the corresponding Krein coefficient is `A(L)=-q(L/2)/2`.
All variation identities, differentiability, the initial normalization at zero,
and the prime-entry law remain unproved. Trace existence alone supplies none of them.
