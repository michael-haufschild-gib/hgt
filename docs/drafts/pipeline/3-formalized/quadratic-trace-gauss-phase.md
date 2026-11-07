# Quadratic trace Gauss phase

- **ID:** quadratic-trace-gauss-phase
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [metaplectic Möbius descent](../1-in-progress/metaplectic-mobius-descent.md)
- **Statement:** For `c=a+bω≠0`, the quadratic trace Gauss sum divided by `|c|` equals `(1+i^(−b)+i^a+i^(b−a))/2`.

The character is `ψ_c(x)=exp(2πi Tr(x/(c(1+2ω))))`. Its analytic normalization
and primitivity are proved for every nonzero modulus.

The proof applies Poisson summation to a damped binary Gaussian with
the actual quadratic trace phase. Partitioning the original lattice modulo
`c` gives the Gauss sum in its Abel limit. The dual phase becomes periodic
modulo two; controlling the Gaussian-weighted phase error gives four residue
terms. Their values depend only on `a,b mod 4`.

## Proof

Put `q=a²−ab+b²=‖c‖²`, `δ=1+2ω`, and
`Sη=Σ_{z∈O} ψ_c(z²) exp(−πη‖z‖²)`. Each coset of `(c)` has Abel mass
`2/(√3 q)`, so `ηSη → 2G(c)/(√3 q)`.

The trace pairing is `Tr((x+yω)/(δc))=(ay−bx)/q`. Thus the binary Gaussian
Poisson formula applies with
`A=η+2ib/q`, `B=−η/2−2ia/q`, `D=η+2i(a−b)/q`.
Its determinant is `4/q+3η²/4`; its inverse form, with `r=1+3qη²/16`, is

`ηq(k²+kℓ+ℓ²)/(4r) + i((a−b)k²+2akℓ+bℓ²)/(2r)`.

The dual phase tends to `φ_c(y)=ψ_4(−cy²)`, under
`y=(k+ℓ)+kω`. This phase is periodic modulo two. Its four values sum to
`F=1+i^(−b)+i^a+i^(b−a)`. At scale `t=ηq/(4r)`, each residue class modulo two
has mass `2/(4√3)`. Therefore the fixed dual sum, multiplied by `η`, tends
to `2F/(√3 q)`.

Freezing the phase changes each summand by at most
`C_c η² Q(k,ℓ) exp(−πηq Q(k,ℓ)/8)` for small positive `η`, where
`Q=k²+kℓ+ℓ²`. The inequality `x exp(−x)≤2 exp(−x/2)` and the Gaussian mass
show that `η³ Σ Q exp(−KηQ)→0` for every `K>0`. Hence the normalized total
phase error vanishes. The Poisson prefactor tends to `√q/2`. Comparing the
two limits gives `G(c)/√q=F/2`.

In particular, `c≡1 mod 4` gives `F=2` and `G(c)=‖c‖`.

## Lean and scope

`MetaplecticMobiusDescent/TheQuadraticGaussPhaseLivesModuloFour.lean` proves:

- `fixed_phase_abel_limit`, `original_dual_abel_limit`;
- `normalizedQuadraticTraceGauss_formula`;
- `normalizedQuadraticTraceGauss_eq_of_mod_four`;
- `quadraticTraceGauss_eq_norm` on `c≡1 mod 4`.

The direct `lake --old env lean` audit passed. Five endpoint axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`. The original
residue mass, phase-error bound, dual scale, and Poisson prefactor are all
proved in the imported local modules; no analytic input remains a premise.

This closes the quadratic phase evaluation. The composite character bridge,
theta identification, and uniform mean-square estimate remain separate work.

Proof source: external OpenAI development, `Poisson/BinaryGaussian.lean`,
`Poisson/GaussianMoments.lean`, `Poisson/OscillatoryGaussian.lean`,
`GaussSum/{GaussianDualLimit,GaussianFiberMass,AbelPhaseLimit,ThetaLocalRows}.lean`.
