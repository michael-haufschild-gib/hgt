# Complete-cell indices have an explicit capture stage

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Target:** Original obstacle A4: an explicit stage, in source bounds and a
  finite negative spectral margin, after which the literal complete-cell Gram
  matrix carries every negative direction of the source family.

## Paper argument

Let `f` vanish outside `(-R,log B-R)`, with `|f|≤C`, Lipschitz constant `K`,
total variation `V`, and Gamma jump energy `E`. Write

```text
J = integral_(0,infinity) t archLevyDensity(t) dt,
U+ = integral_[-R,log B-R] |cosh(u/2)| du,
U- = integral_[-R,log B-R] |sinh(u/2)| du,
W = sum_(1≤m≤B) 2 Lambda(m)/sqrt(m),
D = 8 K V J,
P = W [sqrt(B C²) sqrt(B² K²) + 2 B C K],
A = 2 sqrt(E) sqrt(D) + D + P
    + 4 |gammaHardyPhaseRate(0)| C K log B
    + 4 C K (U+²+U-²).
```

For `N≥1`, the actual complete-cell quadratic error is at most `A/sqrt(N)`.
Indeed, the cell sup error is `K/N`, its variation is at most `2V`, and
its jump energy is at most `D/N`. The jump-vector norm-square identity gives
energy error at most `2 sqrt(E D/N)+D/N`. Mass error is at most
`2 C K log B/N`; each weighted moment error is at most `K U±/N`, and both
moment magnitudes are at most `C U±`. The prime successor estimate gives
the first term in `P`; the divisibility spine is logarithmic quadrature
of a product with Lipschitz constant `2CK`, giving the second.

Apply this bound to every `f_i+f_j` and `f_i-f_j`. Polarization yields
entry constants `A_ij=(A(f_i+f_j)+A(f_i-f_j))/4`. For the actual negative
spectral compression `S`, dimension `r`, and margin `δ>0`, set

```text
T = sum_(i,j<r) sum_(a,b<n) |S_ai| A_ab |S_bj|,
N0 = 1 + ceil((2(r²+1) T/δ)²).
```

Every `N≥N0` retains all `r` negative directions: each compressed error
is at most `T/sqrt(N)≤δ/[2(r²+1)]`. Use the canonical source bounds
`C=|f(0)|+Var(f)` and `K=|f'(0)|+Var(f')`; compact `C²` regularity makes
both variations finite, and the derivative bound gives the stated Lipschitz
constant. The finite Hermitian spectral theorem supplies `S` and `δ`.
No convergence modulus is assumed. The stage depends on the finite source
family and its negative spectral margin, not merely on its dimension.

## Lean result

The explicit coefficients and capture stage are formalized in:

- `ArithmeticCastelnuovoSeveri/QuantitativeCompleteCellMoments.lean`:
  mass and squared pole-moment rates.
- `ArithmeticCastelnuovoSeveri/QuantitativeCompletePrimeSource.lean`:
  the complete prime-source rate.
- `ArithmeticCastelnuovoSeveri/QuantitativeCompleteWeilSourceTransfer.lean`:
  `abs_completeCellWeil_sub_le_canonical`, including the Gamma jump energy.
- `ArithmeticIndexDescent/CompleteCellIndicesHaveAnExplicitCaptureStage.lean`:
  `norm_completeCellSourceGram_sub_le`, `completeCell_index_capture_at_stage`,
  `exists_completeCell_explicit_index_capture`, and
  `exists_completeCell_explicit_weilGram_capture`.

The existential conclusions apply to every finite family of compact `C²`
real tests. Their source bounds, common support window and negative spectral
compression are supplied by proved theorems.

Five changed source files passed direct `lake --old env lean` audits.
All thirteen printed transitive axiom checks contain only `propext`,
`Classical.choice`, and `Quot.sound`. New leaves are wired into their umbrellas.
