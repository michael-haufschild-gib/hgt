# Metaplectic conversion of Möbius coefficients

- **ID:** metaplectic-mobius-descent
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Sextic Poisson transformation converts ideal Möbius coefficients over the Eisenstein integers into cubic theta coefficients; a second transformation may close a contracting mean-square descent.

## Target

Prove an unconditional source estimate beyond absolute convergence. The candidate external estimate is
`Σ_{0<N(u)≤D^(1+θ)} |Σ_n μ_K(n)(u/n)_6 W(N(n)/D)|² ≪ D^(2+θ+ε)`
for every fixed `θ, ε > 0` and smooth compactly supported `W`. Sixth-power rows then give the `11/12` exponent. This is an external claim, not a theorem established in this corpus.

## Arithmetic mechanism to audit

1. Normalized cubic Gauss sums satisfy `γ₂(n)³ = μ_K(n) α(n)` on squarefree primary elements.
2. Hasse–Davenport converts `μ_K(n) γ₋₁(n)` to cubic theta coefficients, up to a fixed ray-class factor.
3. Theta completion adds cube indices. Möbius inversion removes them.
4. Two Poisson transformations, with a positive enlargement between them, produce a smaller row range. Regrouping divisor terms before absolute values forces `f′ | k′`.
5. Required transfer bounds must control transformed weights uniformly; scale contraction alone proves no estimate.

## Status and sources

The global mean-square estimate has no local dependency-closed proof. Corpus searches found no matching source estimate. External endpoints and their transitive analytic dependencies require audit before reuse.

The following arithmetic statements are formalized in
`MetaplecticMobiusDescent/`, with direct Lean checks and standard-axiom audits.

| Module | Exact result |
|---|---|
| `TheSexticCharacterBecomesQuadratic` | Full Gauss-product conversion; quadratic output, unit norm, and exceptional zero frequency. |
| `ThePrimaryCubicGaussSumFixesTheSign` | Canonical primary generator; `J(χ_p,χ_p)=−p` and `γ_p³=−p/‖p‖`. |
| `CubingTheCompositeGaussSumRecoversMobius` | Actual CRT factorization; `γ(I,ψ)³=μ(I)p/‖p‖` for every primitive `ψ`. |
| `MobiusBecomesACubicGaussCoefficient` | `μ(I) conjugate(G₁)=c(I,ψ)G₂`, with explicit `‖c(I,ψ)‖=1`. |
| `CubicReciprocityFromFrobenius` | Cubic reciprocity for primary generators at distinct residue characteristics. |
| `TheCubicPhaseLivesModuloTwo` | Product of sextic values at four is the fixed cubic character `(p/(2))₃`. |
| `TheDifferentNormalizesTheTraceCharacter` | Different `(1+2ω)`; primitive analytic character `exp(2πi Tr(x/[p(1+2ω)]))`; exact Möbius conversion for this character. |

`EisensteinCoordinates` proves the intrinsic coordinate trace and norm form.
The Gaussian transform, residue-class Abel mass, and vanishing dual-phase
error prove the exact quadratic trace Gauss evaluation
`G(a+bω)/‖a+bω‖=(1+i^(−b)+i^a+i^(b−a))/2` for every nonzero modulus.
See [quadratic phase](../3-formalized/quadratic-trace-gauss-phase.md).

`TheAnalyticConversionHasAFixedRayPhase` identifies the composite quadratic
sum with the actual trace square sum and proves
`μ(I) conjugate(G₁)=R(p)(‖p‖/p)G₂`, with `R` fixed modulo four, of unit norm,
and one on the principal class. Six endpoint audits use only standard axioms.

`CubicReciprocityAtACommonCharacteristic` closes prime cubic reciprocity:
primary factorization of `−(p+q)` handles primes above the same rational prime.
The prime-cover bound follows from the quadratic extension degree.

`CubicJacobiSymbols` constructs the composite symbol and proves reciprocity
with arbitrary multiplicities, including common factors.

The ramified supplementary laws now give `(ω/p)₃=ω^(2A−B)`,
`(λ/p)₃=ω^A`, and `(1+2ω/p)₃=ω^(−B)` for every primary
`p=1+3A+3Bω`. Denominator congruence modulo both nine and the numerator is
also proved.

`TheCubicKubotaMultiplier` constructs the actual nontrivial cubic character
on `Γ(3)`. Its image is all cubic roots; its kernel has relative index three
and finite index in `SL₂(O)`.

`TheCubicMultiplierExtendsOverRationalMatrices` extends the character
trivially across rational matrices and proves that the larger group normalizes
the finite-index metaplectic kernel.

The actual hyperbolic quotient and Bianchi reduction are constructed.
The cubic kernel quotient has a compact core and finitely many cusp tails;
this topological cover alone supplies no Sobolev estimate.

The actual cubic Eisenstein series is absolutely convergent and holomorphic
for `Re s>2`, with character automorphy. The cubic quotient now has a
measurable fundamental selector and positive finite invariant volume.
Its completed energy space has a closed gradient, faithful mass embedding,
and [compact mass restriction](../3-formalized/cubic-kernel-local-sobolev-compactness.md)
to every compact quotient set. Exterior coercivity is still open.

Cubic theta identification, cube removal, and uniform transfer estimates
remain open locally.
The arithmetic conversion alone proves no mean-square cancellation estimate.

- [OpenAI, The Quasi-Riemann Hypothesis, §§4–7 and Appendix A](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf).
- [Kontorovich development](https://github.com/AlexKontorovich/quasi-rh/tree/d26d846d6f3129017f06b6fd3f78dd72d361d60b): `ElevenTwelfths.Unconditional.riemannZeta_ne_zero_of_re_gt_elevenTwelfths` is an advertised unconditional endpoint; not locally checked.
- [Rubinstein's guide](https://www.math.uwaterloo.ca/~mrubinst/quasi_rh_notes/zeta_11_12_guide.pdf), §8, explicitly separates transfer estimates from the final induction.
