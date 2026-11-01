# Global transport of the literal odd-conductor model

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](parity-stabilizer-logarithmic-coalescent-calibration.md).

## Target

Sum the literal logarithmic pair kernel over odd bases, retaining the fixed
conductor cutoff, actual smooth taper, coalescent aperture and upper endpoint.
The primitive spatial correction cannot be dropped.

## Formalized local estimates

For each fixed smooth height profile, the
[literal logarithmic row](../3-formalized/literal-logarithmic-stabilizer-transport.md)
with `1/sqrt(m(m+2r))`, `1≤R` and `2R≤m` satisfies

`|logRow−[π spatialDual−Ωhat(0)O(Q)/m]|≤C O(Q)[T⁻¹+(m/(TR))³]`.

Every finite row is bounded by `C O(Q)`; its absolute logarithmic first moment
is at most `C O(Q)/T`. Constants depend only on the fixed profile, with no
derivative estimate left as a premise. All eight audits use standard axioms,
and both final direct leaf checks pass.

The [linear aperture bounds](../3-formalized/odd-stabilizer-aperture-and-fixed-base-renormalization.md)
also show fixed-base cancellation of the leading logarithmic diagonal. The
[Fourier transport estimates](../3-formalized/decay-preserving-cosine-transport.md)
retain decay and have no additive height loss on short rows.

## Actual smooth taper

The [actual standard taper transport](../3-formalized/actual-smooth-taper-stabilizer-transport.md)
is formalized: `g=autocorr(φ²)` satisfies `|g(x)−g(y)|≤2|x−y|`, uniformly
in length, collar and monotone transition profile. Endpoint variation costs
`C O(Q)/T` for each fixed smooth height profile. The three audits use standard
axioms and the final direct check passes. Compatibility with the separate
cosine-shaped taper remains open.

Keep this actual taper through the signed spatial/diagonal cancellation.
Its triangle bracket differs by at most `2w`, but a premature absolute
replacement can cost `O(wX log Q)`. After cancellation, the proposed error
is only `O(wT log²T)`.

## Aperture and boundary

Put `N=floor X` and `R_m=(min(N,floor(m exp θ))−m)/2`, using
natural subtraction and division. This directly retains both literal cutoffs.
The [exact ordered-pair identity](../3-formalized/literal-stabilizer-model-row-decomposition.md)
is formalized:
`model=(1/(4π))Σ_{odd 3≤m≤N}[2g(log m)logRow(m,R_m)+taperVariation(m,R_m)]`.
The global taper-anchoring error is at most `C floor(X) O(Q)/T` for fixed
smooth height profiles and `θ≤log 2`. All three audits use standard axioms;
the final direct leaf check passes.

For `θ≤log 2`, `2R_m≤m`. Bulk bases `m≤X exp(−θ)` see the full aperture;
if `mθ≥4`, its length is at least `mθ/4`. Short bases number `O(θ⁻¹)`.
The upper boundary has width `O(Xθ+1)` and each taper there is at most θ.
These aperture identities and their global sums remain unformalized.

At `X≤T²`, `θ=T^(−7/12)`, the proposed raw errors are

- phase and weight: `O(X log X log Q/T)`;
- taper variation: `O(X log Q/T)`;
- aperture tail: `O(X log X log Q/(T³θ³))`;
- short rows: `O(θ⁻¹ log X log Q)`;
- upper boundary: `O((Xθ²+θ)log Q)`.

All should be `o(T log³T)`. Global primitive-sample calibration and the
actual signed prime-minus-model bound remain separate open inputs.

## Primitive spatial quadrature

Existing right-endpoint Lipschitz quadrature suffices. For
`F(x)=g(log x)Ω(cx)`, x≥1, the proved taper Lipschitz bound and fixed-profile
bound `Lip(Ω)≤M/T` give `Lip(F)≤2+LMc/T`. At odd mesh two, with
`N=ceil(T/c)`, the error from half the integral is at most
`4T/c+(4+6M)L` when L≥1 and 0<c≤2T.

Only frequencies `c=πn/q≤2T` contribute. Summing `Tq/n+L` over these
frequencies and then over A(q)=μ²(q)/φ(q)² uses the existing arithmetic
first-moment bound and costs `O(T(1+L+log(QT))(1+log Q))`.
This gives the intended `O(T log²T)` at polynomial cutoff, without a global
bounded-variation extension. Support truncation, quadrature assembly and
weighted coprime-harmonic transport remain to be formalized.
