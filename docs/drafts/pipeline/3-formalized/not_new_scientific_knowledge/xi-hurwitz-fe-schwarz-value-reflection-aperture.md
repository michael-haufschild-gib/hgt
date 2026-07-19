# Xi Hurwitz FE--Schwarz value-reflection aperture

- **ID:** `xi-hurwitz-fe-schwarz-value-reflection-aperture`
- **Stage:** 3-formalized
- **Type:** exact cross-interface law / bridge
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/XiHurwitzFESchwarzValueReflectionAperture.lean`

## Statement

Fix `rho` in the open critical strip.  The following conditions are equivalent:

1. the continued-Hurwitz pair at the FE and Schwarz reflected exponents,
   `H_(1-rho)` and `H_(conj rho)`, is differentially dependent over the shift field;
2. the reflected rational-Hurwitz energy is summable after every positive prime-power damping;
3. for any integer `n > 1`, the complete normalized finite-value ray at the moduli `n^k` is
   bounded;
4. for any integers `n,k > 1`, the exact power-refinement law

   ```text
   H_(n^k)(rho) = k^2 H_n(rho)
   ```

   holds;
5. for any `1 < m < n`, the two normalized finite-value energies agree:

   ```text
   H_m(rho) = H_n(rho).
   ```

6. when `rho` is an actual Xi zero, all positive-order canonical Hurwitz anchor jets at the FE and
   Schwarz reflected exponents are proportional by one scalar.

After quantifying over the actual Xi divisor, the corresponding global propositions are likewise
equivalent.  In particular this gives direct, RH-free proofs that the FE--Schwarz differential
circuit is the same proposition as each finite-value refinement or cofinal damping interface.

## Proof

The existing differential-matroid theorem gives, throughout the open strip,

```text
H_(1-rho), H_(conj rho) dependent  iff  Re(rho)=1/2.        (1)
```

The damping-aperture theorem gives

```text
(forall theta>0, sum_p p^(-theta)|C_p(rho)|^2 < infinity)
  iff Re(rho)=1/2.                                          (2)
```

The normalized rational-Hurwitz reflection law is

```text
H_n(rho) = sinh((Re(rho)-1/2) log n)^2.                     (3)
```

For `n>1`, equation `(3)` makes the power ray `H_(n^k)` bounded exactly when its argument is zero.
The already proved positive-square refinement identity makes equality
`H_(n^k)=k^2 H_n` for `k>1` equivalent to the same equation.  Strict monotonicity of `(3)` in the
integer scale makes `H_m=H_n` for `1<m<n` equivalent to it as well.  Transitivity of these exact
equivalences proves the pointwise law.

For an actual Xi zero, the existing projective-jet theorem proves condition 6 implies
`Re(rho)=1/2`.  Conversely that critical-line equation identifies `1-rho` with `conj rho`; the
unconditional Schwarz law for every positive-order anchor jet then supplies condition 6 with
scalar one.  Thus the previously one-way projective interface is pointwise exact and is equivalent
to the rank-two differential circuit.

For the global law, each Xi divisor support point is an actual Xi zero and lies in the open strip;
conversely every Xi zero defines a support point.  Therefore the pointwise equivalences lift in
both directions without assuming RH and without changing any quantifier.  QED

## Significance boundary

This closes an interface gap rather than an arithmetic sign gap.  Differential dependence,
cofinal damping, bounded finite-value rays, nonlinear-refinement collapse, and two-scale equality
are not separate prospective RH inputs: they are exact coordinates on the same horizontal
FE--Schwarz defect.  A proof route must still produce one of them from the completed source; this
bridge does not do so and is not claimed as new scientific knowledge.

## Gates

- [x] 0 -> 1: exact interfaces and quantifiers identified
- [x] 1 -> 2: dependency-closed paper proof given above
- [x] 2 -> 3: nine damping/value pointwise/global equivalences formalized; exact leaf build passes;
  axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
- [x] projective extension: pointwise reverse implication and direct global equivalence with the
  FE--Schwarz pair circuit formalized; exact leaf build and baseline axiom audit pass
- [ ] 3 -> 4: not proposed; bridge classification
