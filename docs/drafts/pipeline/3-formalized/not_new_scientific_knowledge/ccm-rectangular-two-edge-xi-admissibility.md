# Explicit rectangular two-edge Xi admissibility

- **ID:** `ccm-rectangular-two-edge-xi-admissibility`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]` / unconditional CCM foundation
- **Novelty status:** not promoted as new scientific knowledge
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCM/CCMRectangularTwoEdge.lean`

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
6. Functional-equation reflection preserves each test value, Schwarz
   conjugation conjugates it, and the four FE--Schwarz copies contribute
   exactly four times the real part of one squared value.  This last identity
   is pointwise on `XiZeroCopy`, so analytic multiplicity is retained.
7. There exists an unconditional `eta>0` such that every Xi-divisor point has
   `|Im rho|>=eta`.  The proof uses compact-disc zero finiteness and absence of
   real Xi zeros, with no numerical first-zero input.
8. For every `a>=L`, selecting the exponentially growing edge according to the
   sign of `Re(rho-1/2)` leaves a full Xi-divisor remainder whose norm is at
   most

   ```text
   R_L sum_q |z_q|^-2,
   R_L=[1+exp(|L|/2)]^2[2exp(|L|/2)+4],
   ```

   uniformly in `a`.

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
- `I_mul_xiSpectralPoint_copyConj`
- `xiRectangularTwoEdgeTransform_reflect`
- `xiRectangularTwoEdgeTransform_copyConj`
- `xiRectangularTwoEdgeTransform_lineConj`
- `xiRectangularTwoEdgeTransform_quartet_square`
- `exists_xiDivisorSupport_abs_im_lower_bound`
- `exists_xiZeroCopy_abs_im_lower_bound`
- `rectangularTwoEdgeDominant`
- `rectangularTwoEdgeTransform_sq_sub_dominant_of_pos`
- `rectangularTwoEdgeTransform_sq_sub_dominant_of_neg`
- `norm_rectangularTwoEdgeTransform_sq_sub_dominant_le`
- `xiRectangularTwoEdgeRemainderTerm_summable`
- `xiWeilPolarization_rectangular_sub_dominant_eq_tsum_remainder`
- `norm_xiWeilPolarization_rectangular_sub_dominant_le`

## Boundary

This card proves admissibility and the exact algebraic decomposition only.  It
does not prove negativity under false RH, a Landau boundary theorem, or RH.
Those are the named open steps in
`explicit-rectangular-two-edge-weil-completeness.md`.

## Verification

- exact module build: passed
- imported by `CCMUnconditionalFoundation.lean`: passed
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is introduced
