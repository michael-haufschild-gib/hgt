# The real width field and the location of conjugation

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Questions:** Ordinary conjugation; global width reversal; source width equations.

Write `w_q=t_q+iδ_q`, with `t_q∈K`, for the complete-fibre source field `K`.
Let `L=ℚ(all w)`, `M=L(i)`, `F=K(all δ)`, and `E=K(all δ_qδ_r)`.
The [Gaussian extension](../3-formalized/galois-zero-gaussian-extension.md)
and [maximal real subfield](../3-formalized/galois-zero-maximal-real-subfield.md)
are formalized. In particular `E=L∩ℝ` is normal over `K`; for a nonzero
anchor, `L=E(iδ₀)` is quadratic, `F=E(δ₀)`, and `F=E ⇔ i∈L`.

## Remaining targets

1. `M=F(i)`, `F=M∩ℝ`, and `F/K` is algebraic and normal.
2. Unconditionally `Gal(M/K) ≅ Gal(F/K) × C₂`, with ordinary conjugation
   at `(id,−1)`.
3. Simultaneous width negation extends over `K` iff functional-equation
   reflection lifts. Equivalently `i∉L`; for a nonzero anchor, `δ₀∉E`.
   The global width reversal is unique when it exists.
4. If `δ₀∉E`, the full extension `M/E` is biquadratic, with quadratic
   subfields `E(i)`, `E(δ₀)`, and `E(iδ₀)`. Identify them as the fixed
   fields of the three geometric involutions.
5. Construct monic source-field polynomials for all widths in each fibre,
   retaining analytic multiplicity, and identify `F` as their full compositum
   of splitting fields.

## Proof

The identities `δ_q=−i(w_q−t_q)` and `w_q=t_q+iδ_q` give `M=F(i)`.
Every element is uniquely `a+ib`, with `a,b∈F⊆ℝ`, so `F=M∩ℝ`.
Centrality of ordinary conjugation makes this fixed field normal over `K`.
Restriction to `F` and sign on `i` are jointly injective. Normality extends
any automorphism of `F` to `M`; composing with conjugation adjusts its Gaussian
sign independently, giving the direct product.

Since `ρ_q=1/2−δ_q+it_q`, functional-equation reflection requires simultaneous
width negation and Gaussian sign `−1`. Conversely those actions provide the
lift. Widths generate `F`, so their negating action is unique. The proved
Gaussian obstruction and anchor criterion give the stated equivalences.

When `δ₀∉E`, adjoining `δ₀` has degree two; adjoining `i` to that real field
has degree two again. The resulting degree-four field contains the displayed
three distinct quadratic subfields. To exclude a fourth, write any element
`r` with `r²∈E` first as `a+ib`, then write its real coordinates in the basis
`1,δ₀`. Realness of `r²` forces `ab=0`; squaring `x+yδ₀` and using
`δ₀∉E` forces `xy=0`. Thus `r` lies in one of `E`, `Eδ₀`, `Ei`, or
`Eiδ₀`. Every quadratic subfield has a nonbase square-root generator:
complete the square in a degree-two minimal polynomial. Its generated field
is therefore one of the displayed three. This classification remains a Lean
obligation.

In this regime let `ν` negate every width and fix `i`. Ordinary conjugation
`c` fixes widths and reverses `i`; functional-equation reflection is `νc`.
Since `E/K` is normal and `[F:E]=2`, the width involution is central in
`Gal(F/K)`. Thus these generate a central Klein four subgroup of `Gal(M/K)`.
Their fixed fields are respectively `E(i)`, `F`, and `L`, with common fixed
field `E`. The two geometric permutations remain distinct whenever a width
is nonzero; centrality does not make them equal.

For a nonempty fibre of mass `n`, put `Q(X)=P_t(X+t)` over `K`. Then

```
Q(iX) = i^n ∏_q (X−δ_q).
```

The product after division by `i^n` has real coefficients. Its coefficient
of degree `j` is `i^(j−n) Q_j`. Gaussian phases are `±1` or `±i`; in the latter
case realness forces that coefficient to vanish. Every coefficient therefore
lies in `K`. The resulting monic polynomial is hyperbolic and retains the
complete divisor. Their root sets exhaust all widths, giving the infinite
splitting-field compositum. This supplies no reason for the widths to vanish.

## Formalization

Targets 1–3 and 5 have unverified Lean drafts. The biquadratic
subfield classification is not yet drafted. No result on this remaining list
is claimed formalized.
