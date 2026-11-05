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

## Missing localization identity

Translate the selected endpoint to zero. Choose a real bounded Lipschitz
cutoff `χ`, equal to one near zero and zero before the opposite endpoint.
For `j(r)=exp(-|r|)/(2|r|)`, put `Kχ(x,y)=(χ(x)-χ(y))j(x-y)`.
Lipschitz cancellation gives
`|Kχ(x,y)|≤(Lip(χ)/2)exp(-|x-y|)`, so its Schur operator is bounded on L²
and preserves essential boundedness. The full-domain identity needed is

`q(v,χu)-q(χv,u)=⟨v,Kχu⟩`.

[Cutoff-domain preservation](../3-formalized/bounded-lipschitz-cutoffs-preserve-logarithmic-energy.md)
is formalized. The commutator identity would convert the actual
interior equation into the half-line equation with bounded L² forcing
`χg+Kχu`. Since `χu=u` near the selected endpoint, the formalized Green
boundary theorem would give the actual Weil trace. [The mixed jump pairing and translation invariance](../3-formalized/the-logarithmic-form-has-its-mixed-jump-pairing.md)
are formalized. Identification with the actual aperture domain, the commutator
identity, and this application remain unproved.

An independent sharp-extension route uses `CHMDSharpSpatialCut` and
`CCMRestrictedWeilGammaBoundaryPairing`.

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
