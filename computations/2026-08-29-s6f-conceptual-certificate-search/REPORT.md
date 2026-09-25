# S6F conceptual-certificate and sharp-cone search

## Questions

1. Does reversing physical danger coordinates turn normalized drift into a short positive monomial
   decomposition?
2. Is clock-ratio wedge alone enough, before retaining physical amplitude constraints?
3. Does sharper formal clock cone restore direct monotonicity in ratio coordinate `y`?

Diagnostic only. No coefficient, witness, table, or numerical output here is admissible in Lean.

## Computation

Reconstructed literal source-positive projective drift exactly from source Lie recursion. Used up to
seven RunPod worker processes. Tested sparse rational coefficient transport, exact tensor-Bernstein
signs, intrinsic source wedge, and an independently implemented exact verifier.

Sharp cone coordinates were

```text
X = 191/10 + S,
z = (3/10) T,
y = 13/32 + (1/32) Y.
```

## Outcomes

- **Simple danger-slack decomposition is false.** In
  `s=X-191/10`, `w=9/100-z²`, `h=y-13/32`, `C` retains 2,303 negative ordinary
  coefficients. Both endpoint-wall coefficient matrices have full rank 14. Monomial/low-rank
  shortcut is not supported.
- **Intrinsic ratio-only wedge is false.** Even after mandatory factor `B`, source drift has mixed
  signs. Exact simple state `B=1`, `Q=1`, `U=5/2` lies strictly inside `2B<U<3B` and has drift
  `-2321249416704`. Therefore physical amplitude/scale cap cannot be discarded.
- **Direct `y` monotonicity revives on sharp cone.** All 10,206 hybrid power/Bernstein coefficients
  of `C_y` are strictly positive. This was false on previous wider cone.
- On sharp half-cone, all 10,584 coefficients of `C` and all 9,828 coefficients of `C_X` are
  strictly positive. All 10,192 coefficients of `-C_z` are nonnegative (392 zero).
- `-C_yy` remains nonnegative. Both `y` endpoint walls remain strictly positive.
- Consequently diagnostic sign problem reduces to one exact corner:

```text
C(191/10, 3/10, 13/32) > 0.
```

Independent exact verifier reconstructed drift, used separate direct multi-index Bernstein
conversion, reproduced sharp-cone sign counts, and verified intrinsic rational counterexample.

## Interpretation

New formal clock cone is decisive, not cosmetic: it changes false `y`-monotonicity into strict
positive derivative. Remaining paper task is independent conceptual proof of three half-cone signs
`C_X>0`, `C_z<=0`, `C_y>0`, then exact rational corner positivity. Computed coefficient tables are
forbidden as proof input. Physical scale/amplitude relation must remain explicit; ratio-only source
cones are terminal.
