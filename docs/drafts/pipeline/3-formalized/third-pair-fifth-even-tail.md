# Gamma-reserve payment for theta atoms one and three

- **Stage:** 3-formalized
- **Wall:** Σ6
- **Scope:** Ordered pairs `(1,3)` and `(3,1)`, contributing to the
  [complete fifth even tail](theta-fifth-even-integrated-tail.md).

Let `E(q)=q^(3/2)exp(−2q)` and `A=M(0,1)>0`. The exact radial matrix

`R₁₃(q)ᵢⱼ = 18 ∫_(t>q) t^(3/2)exp(−10t) P_(i+j)(9t²;10t) dt`

satisfies `R₁₃(q)+E(q)·3/(8q)·A > 0` for every `q≥3`.

The rate-ten gamma mass lies between
`1/10+3/(200q)+3/(4000q²)−3/(80000q³)` and the same expression without
its cubic term. Also `exp(−8q)≤3²⁴/(20⁸q²⁴)` on this ray.

Clear `q²⁷`, set `q=3(1+y)`, and divide by `3²⁷`. The coefficient of
`y^d` is `binom(26,d)A/8` plus the exact signed pair coefficient. The
pair term vanishes above degree 21; the two gamma endpoints differ only
at degree zero. All 23 required fixed matrices have exact positive Schur
certificates. The higher coefficients are positive multiples of `A`.
Positive matrix sums and convexity cover the full radial, gamma, and
exponential-weight intervals. Integrating the exact radial polynomials
identifies this comparison with the literal tail.

Namespace `GaloisForLFunctions.ThetaCuspSections.FifthThirdTail`:
`coefficientMatrix_posDef`, `clearedMatrix_posDef`, `reserveModel_posDef`,
`third_radial_integrable`, `third_radial_tail_eq`,
`thirdRadialTailMatrix_reserve_posDef`.

Files: `FifthEvenThirdTailData.lean`, `FifthEvenThirdTailCoefficients.lean`,
`FifthEvenThirdTailModel.lean`, `FifthEvenThirdTail.lean`.
The capstones use only `propext`, `Classical.choice`, and `Quot.sound`.
