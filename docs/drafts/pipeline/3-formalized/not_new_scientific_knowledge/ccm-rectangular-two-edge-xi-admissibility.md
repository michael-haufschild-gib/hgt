# Explicit rectangular two-edge Xi admissibility

- **ID:** `ccm-rectangular-two-edge-xi-admissibility`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]` / unconditional CCM foundation
- **Novelty status:** not promoted as new scientific knowledge
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMRectangularTwoEdge.lean`

## Theorem

For real `L,a`, define

```text
A_L(w) = L                                      if w=0,
         (1-exp(-Lw))/w                         otherwise,

F_(a,L)(w) = exp(aw) A_L(w) + exp(-aw) A_L(-w).
```

The following statements are unconditional.

1. If `L>0` and `Re w>0`, then `A_L(w) != 0`.
2. For `w!=0`,

   ```text
   A_L(-w)=exp(Lw)A_L(w),
   F_(a,L)(w)=A_L(w)[exp(aw)+exp(-(a-L)w)],
   F_(a,L)(w)^2=A_L(w)^2[
       exp(2aw)+2exp(Lw)+exp(-2(a-L)w)].
   ```

3. `F_(a,L)` is even and Schwarz-compatible.  Therefore the corresponding
   function of the centered Xi spectral coordinate is fixed by `xiWeilSharp`.
4. On `|Re w|<=1/2`,

   ```text
   |A_L(w)| <= [1+exp(|L|/2)]/|w|,

   |F_(a,L)(w)| <=
     [1+exp(|L|/2)] [exp(|a|/2)+exp(|a-L|/2)]/|w|.
   ```

5. The resulting test is square-summable over every multiplicity copy of the
   actual Xi divisor.

## Exact formal surface

- `rectangularWindowAmplitude_ne_zero`
- `rectangularWindowAmplitude_neg`
- `rectangularWindowAmplitude_conj`
- `rectangularTwoEdgeTransform_conj`
- `rectangularTwoEdgeTransform_even`
- `xiWeilSharp_xiRectangularTwoEdgeTransform`
- `rectangularTwoEdgeTransform_eq`
- `rectangularTwoEdgeTransform_sq_decomposition`
- `norm_rectangularWindowAmplitude_le`
- `norm_rectangularTwoEdgeTransform_le`
- `I_mul_xiSpectralPoint`
- `abs_re_I_mul_xiSpectralPoint_le_half`
- `xiRectangularTwoEdgeTransform_square_le`
- `xiRectangularTwoEdgeTransform_squareSummable`

## Boundary

This card proves admissibility and the exact algebraic decomposition only.  It
does not prove negativity under false RH, a Landau boundary theorem, or RH.
Those are the named open steps in
`explicit-rectangular-two-edge-weil-completeness.md`.

## Verification

- exact module build: passed
- imported by `CCMUnconditionalFoundation.lean`: passed
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is introduced
