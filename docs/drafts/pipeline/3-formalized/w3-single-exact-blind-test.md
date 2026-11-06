# W3: one exact Xi-divisible blind test

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** There is a nonzero real exponentially decaying test `F` with Fourier transform `Φ=Ξg`, where `g` is holomorphic on a strip wider than the critical strip and has no real zeros, such that `F⋆F̃(log n)=0` for every `n≥2` and `archPoleEnergy(F)=0`.

## Construction and proof

1. The proved twisted-arc minimum principle supplies a probability measure `μ` annihilating all twisted integer moments. Define its weights `w_j=4sqrt(2)4^j m_j/(2j)!` from the weighted even moments. The corpus proves nonnegativity, `w_0>0`, weighted factorial summability, and
   `Σ_j w_j ∫ |Ξ(t)Q_j(t)|² cos(t log n)dt=0` for every `n≥2`.
2. Set `R(z)=Σ_j w_jQ_j(z)Q_j(−z)`. The [positive-strip theorem](w3-arc-multiplier-positive-strip.md) gives `Re R(z)>0` on `|Im z|≤501/1000`. Set `g(z)=sqrt(R(z))` using the principal branch, and `Φ(z)=Ξ(z)g(z)`. The square root is holomorphic wherever `Re R>0`; it is even and strictly positive on the real axis. Thus `Φ(−t)=conjugate(Φ(t))`. The factor `g` has no zeros anywhere in the proved strip, so Fourier inversion preserves Xi's zero set throughout its interior.
3. Write `S=Σ_j w_j(j!(3/2)^j)²`. On the strip the existing estimate gives `|R(z)|≤9S exp(log(3)|Re z|)`. The Xi bound gives `|Ξ(z)|≤C exp(−3|Re z|/4)`. Consequently `|Φ(z)|≤3C(S+1) exp(−ε|Re z|)`, where `ε=3/4−log(3)/2>0`.
4. On the real axis, `|Φ(t)|²=Σ_j w_j|Ξ(t)Q_j(t)|²`. The same factorial summability and exponential bound justify exchanging this series with every cosine integral. Step 1 therefore gives exact integer blindness for `Φ`.
5. Apply `xiDivisibleBlindTest_stripTest` to `F=stripTest Φ`. It supplies the real test, its required smoothness and exponential decay, and full Xi divisibility. Fourier inversion gives `F̂=Φ`. Since `Ξ(0)≠0` and `g(0)>0`, the test is nonzero. The existing exact-null receiver gives `archPoleEnergy(F)=0`.

No RH or prime-blind positivity premise enters the construction. This supplies the exact null object; positivity of the entire blind program remains a separate question. The square root is only claimed on the proved strip, not as an entire function.

## Lean

`BiScaleUncertainty/ExactExtremal/ExactBlindTest.lean`:

- `integral_arcSpectrum_cos`, `crossCorr_arcSpectrum`: exact scalarization of every positive arc mixture.
- `exactExtremalTest`: the named test selected from the unconditional annihilating measure.
- `paperFT_exactExtremalTest_zero_iff`: zero-faithfulness throughout the open strip.
- `xiDivisibleBlindTest_exactExtremalTest`, `exactExtremalTest_ne_zero`, `exactExtremalTest_null`.
- `exists_nonzero_xiDivisible_blind_null_test`: unconditional existence theorem.
