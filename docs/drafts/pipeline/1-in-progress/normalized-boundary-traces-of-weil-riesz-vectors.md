# Normalized boundary traces of Weil Riesz vectors

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For every precontact aperture `a` and Fourier parameter `z`, the physical evaluation Riesz vector has a continuous representative `u` and finite limits `τ±(u)=lim_{t↓0} sqrt(log(1/t)) u(±(a-t))`.

## Proved inputs

Actual evaluation Riesz sources are bounded and satisfy the literal restricted
Weil equation. The Gamma multiplier is `(1/2)log(1+ξ²)+c₀` minus convolution
by an integrable bounded remainder. Thus the complete Weil equation becomes
the positive logarithmic Dirichlet equation with bounded full forcing;
all active prime atoms and both polar terms remain present.

- [Bounded completed sources](../3-formalized/the-completed-weil-riesz-vectors-are-bounded.md).
- [Exact logarithmic remainder](../3-formalized/the-weil-symbol-has-an-integrable-logarithmic-remainder.md).
- [Actual logarithmic Dirichlet equation](../3-formalized/the-weil-riesz-equation-is-a-logarithmic-dirichlet-equation.md).

For `Ψ(ξ)=1+(1/2)log(1+ξ²)`, the actual causal probability density `v` has
Fourier multiplier `κ(2πiξ)⁻¹`. Its cumulative mass satisfies
`V(x)√log(1/x)→1`. Causal convolution `W` has range exactly the finite-energy
half-line domain, and `WW*` is its unique variational inverse. Its literal
Green kernel is `∫₀^{min(x,y)}v(x-s)v(y-s)ds`, finite off the diagonal.

- [Half-line inverse and kernel](../3-formalized/the-half-line-logarithmic-green-kernel.md).
- [Actual inverse boundary limit](../3-formalized/the-half-line-logarithmic-green-solutions-have-boundary-values.md): for half-line L² forcing essentially bounded near zero, the measurable representative `u(x)=∫₀ˣv(t)(W*f)(x-t)dt` satisfies `u(x)√log(1/x)→∫₀∞v(y)f(y)dy`. The coefficient is absolutely convergent.

## Actual localization still to formalize

Translate the selected endpoint to zero and choose the overlapping cutoff
`χ_a(x)=min(max(3-2x/a,0),1)`. For `j(r)=exp(-|r|)/(2|r|)`, the literal
kernel `Kχ(x,y)=(χ(x)-χ(y))j(x-y)` has Schur and L∞ bounds `Lip(χ)`.
The complete-domain identity is

`q(v,χu)-q(χv,u)=⟨v,Kχu⟩`.

The following inputs are formalized:

- [Cutoff-domain preservation](../3-formalized/bounded-lipschitz-cutoffs-preserve-logarithmic-energy.md).
- [Mixed jump pairing and translation invariance](../3-formalized/the-logarithmic-form-has-its-mixed-jump-pairing.md).
- [Literal cutoff kernel bound](../3-formalized/the-logarithmic-cutoff-kernel-is-bounded.md).
- [Complete-domain cutoff identity](../3-formalized/the-complete-logarithmic-form-has-its-cutoff-identity.md).

The remaining application identifies the logarithmic domain with the actual
complete aperture domain, then converts the actual interior equation to the
half-line equation with bounded L² forcing `P_+(χg+Kχu)`. Green uniqueness
and the normalized readout apply to each endpoint localization. Continuous
Green representatives can be joined using the positive denominator
`χ_a(x+a)+χ_a(a-x)≥1`, giving one continuous actual Riesz representative.
These domain, application, and gluing steps have unchecked Lean drafts.

## Subsequent variation obligations

For the evaluation vector `v_z`, put `T±(z)=conj(τ±(v_z))`. The proposed
shape identities are

`∂ₐKₐ(w,z)=T₋(z)conj(T₋(w))+T₊(z)conj(T₊(w))`,

`i(z-conj(w))Kₐ(w,z)=T₊(z)conj(T₊(w))-T₋(z)conj(T₋(w))`.

With `Eₐ=T₋` and continuous real normalization at zero, these suggest
`∂ₐEₐ(z)=-izEₐ(z)+q(a)Eₐ♯(z)`, where `q=∂ₐlog|Eₐ(0)|`, and
`A(L)=-q(L/2)/2`. All variation identities, differentiability, initial
normalization, and prime-entry laws remain unproved. Trace existence alone
supplies none of them.

## External proof leads

[Boundary traces and support variation for localized Weil operators](https://rstation.ai/problems/riemann_hypothesis/papers/67),
[Grzywny–Ryznar](https://arxiv.org/abs/1107.0745v1), and
[Hernández-Santamaría–López Ríos–Saldaña](https://arxiv.org/abs/2401.18033v2)
are proof leads, not imported Lean assumptions.
