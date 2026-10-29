# Absolute convergence of Garland's affine A₁ Weyl sum over ℚ

- **ID:** garland-affine-a1-weyl-sum
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), BRIDGE
- **Parent:** [Full loop-group Eisenstein programme](../1-in-progress/garland-loop-eisenstein-over-q.md)
- **Scientific status:** Established mathematics, now formalized. No novelty claim.
- **Scope:** The genuine infinite affine Weyl expansion with rational completed-zeta
  coefficients. Construction of the arithmetic loop-group coset series and identification
  of its unipotent integral with this expansion remain open.

## Exact theorem

Let `λ₀,λ₁∈ℂ` satisfy `Re λ_i>1`, let `κ=λ₀+λ₁`, and extend the weight by
`λ(D)=0`. For arbitrary real torus coordinates `t,z` and positive rotation `R`, put
`H=t h₁+z c-RD`, and let `ρ(c)=2`, `ρ(h₁)=1`, `ρ(D)=0`.
Write `W` for the infinite dihedral affine Weyl group of `A₁`, and
`I(w)={β>0 : wβ<0}`. Then

\[
 \sum_{w\in W}\left|
 e^{(-wλ-ρ)(H)}
 \prod_{β\in I(w)}\frac{ξ(λ(β^\vee))}{ξ(λ(β^\vee)+1)}
 \right|<\infty,
 \qquad ξ(s)=π^{-s/2}Γ(s/2)ζ(s).
\]

Every denominator and every summand is nonzero. The sum equals the sum of its
translation and reflection series, both absolutely convergent.

The Lean theorem has no assumed analytic premise:

```lean
theorem summable_norm_weylTerm (p : ℂ × ℂ) (t z r : ℝ) :
    Summable (fun w : Weyl => ‖weylTerm p t z r w‖)
```

Here `λ_i=1+exp(Re p_i)+i Im p_i` and `R=exp r`. The theorem
`range_godementParameter` proves that the parameterization covers the entire
Godement chamber. The inverse coordinates are `log(Re λ_i-1)+i Im λ_i`; every
positive `R` is `exp(log R)`. This parameterization restricts no part of the stated
chamber and carries no proof field or unproved hypothesis.

## Complete proof

**Roots and inversions.** Write the real roots as `plus n=α+nδ` and
`minus n=-α+nδ`. Positivity means `n≥0` and `n>0`, respectively. The actual
infinite dihedral group acts by

\[
\begin{array}{c|cc}
 & α+nδ & -α+nδ\\ \hline
r_m & α+(n-2m)δ & -α+(n+2m)δ\\
sr_m & -α+(n-2m)δ & α+(n+2m)δ.
\end{array}
\]

Substitution verifies its four multiplication laws. The image of `α` determines
the group element, so the action is faithful. The simple reflections are `sr 0`
and `sr (-1)`; their product is `r 1`, whose integer powers give every translation.
The inversion condition is therefore exactly

\[
\begin{aligned}
I(r_m)&=\{α+nδ:0≤n<2m\}\sqcup\{-α+nδ:0<n≤-2m\},\\
I(sr_m)&=\{α+nδ:0≤n≤2m\}\sqcup\{-α+nδ:0<n<-2m\}.
\end{aligned}
\]

Empty intervals cover negative endpoints. Their cardinalities are `|2m|` and
`|2m+1|`.

**Denominators.** The coroot arguments in the two root strings are
`nλ₀+(n+1)λ₁` and `nλ₀+(n-1)λ₁`. For positive roots they have real part at least
`σ=min(Re λ₀,Re λ₁)>1`. Euler-product nonvanishing of ζ and the identity
`ζ(s)=ξ(s)/Γℝ(s)` exclude zeros of ξ on this half-plane. Thus every numerator,
denominator, and finite coefficient product is nonzero.

**Coefficient growth.** Put `d=σ-1>0` and `L=2/d`. For the entire completion
`Ξ(s)=s(s-1)ξ(s)/2`, the already-formalized unit-shift modulus theorem gives
`|Ξ(s)/Ξ(s+1)|≤1` when `Re s>1`. Restoring the polynomial factors gives

\[
 \left|\frac{ξ(s)}{ξ(s+1)}\right|
 \le\left|\frac{s+1}{s-1}\right|
 \le 1+\frac2{|s-1|}\le1+\frac2d\le e^L.
\]

The second inequality uses `s+1=(s-1)+2`; the third uses
`|s-1|≥Re s-1≥d`. Consequently `|c_w(λ)|≤exp(L #I(w))`.
The imported modulus theorem has no RH premise. Its transitive axiom audit is
included in the parent programme's evidence.

**Degree term.** An affine weight has coordinates `(κ,b,d)`. Direct substitution
proves the Weyl action

\[
 r_m(κ,b,d)=(κ,b+2mκ,d-mb-m^2κ),\qquad
 sr_m(κ,b,d)=(κ,-b-2mκ,d-mb-m^2κ).
\]

It is dual to the real-coroot action above and preserves `b²+4κd`. With
`b=λ₁,d=0`, evaluation of `-wλ-ρ` at `H` gives

\[
\begin{aligned}
r_m &: -(b+1)t-(κ+2)z+(-2κt-Rb)m-Rκm^2,\\
sr_m &: (b-1)t-(κ+2)z+(2κt-Rb)m-Rκm^2.
\end{aligned}
\]

Taking real parts yields a real quadratic `C+Bm-am²` in either family, with
the same `a=R Re κ>0`. Combining with `#I(w)≤2|m|+1` bounds each full summand
by `exp(C+L+(2L+|B|)|m|-am²)`.

**Summability.** For any `a>0` and real `B,C`, expand
`(2a|x|-(B+1))²≥0` to obtain

\[
 C+B|x|-ax^2\le C+\frac{(B+1)^2}{4a}-|x|.
\]

Hence the exponential is bounded on `ℤ` by a fixed constant times `exp(-|m|)`.
Its two tails are geometric, so both Weyl families are absolutely summable.
The equivalence `W≃ℤ⊕ℤ` joins them and identifies their sums. This completes the
proof without an assumed convergence theorem or constant-term identity.

## Lean declarations

All declarations below lie in namespace
`GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1`.

| Module | Main declarations |
| --- | --- |
| `AffineA1Roots` | `act_mul`, `act_plus_zero_injective`, `translation_eq_simple_zpow`, `reflection_eq_simple_zpow`, `mem_inversions` |
| `AffineA1XiCoefficients` | `range_godementParameter`, `rootArgument_re_ge_min`, `xiDenominator_ne_zero`, `xiCoefficient_mul_denominator`, `xiCoefficient_translation`, `xiCoefficient_reflection`, both inversion-cardinality formulas |
| `AffineA1XiEstimates` | `xiCoefficient_norm_le_exp`, `xiCoefficient_translation_norm_le`, `xiCoefficient_reflection_norm_le` |
| `AffineA1Weights` | `weightAct_mul`, `weightAct_quadratic`, `rootArgument_weightAct`, both exact exponents and Gaussian norm formulas |
| `AffineA1WeylSum` | `weylTerm_ne_zero`, `summable_norm_weylTerm`, `hasSum_weylTerm`, `weylSum_eq_two_series` |

Files reside in `formal/GaloisForLFunctions/HTGeometry/LoopEisenstein/`.
They are imported by `HTGeometry/LoopEisenstein.lean`, itself imported by
`HTGeometry.lean`. No umbrella build is needed.

## Validation

- Kernel compilation and transitive axiom audit passed.
- [Saved theorem signatures and axiom output](garland-affine-a1-weyl-sum-audit.txt):
  only `propext`, `Classical.choice`, and `Quot.sound`.
- No added axioms, placeholders, trusted computation shortcuts, or raised proof limits.
- Final per-file command: `lake --old env lean GaloisForLFunctions/HTGeometry/LoopEisenstein/<Module>.lean`.
- Final per-file audit completion is recorded in the parent programme's work log.

## External audit

- Garland, [*Eisenstein series on arithmetic quotients of loop groups*](https://intlpress.com/api/bgcloud-front/resource/pdf/volume/1806606802735230978-1806606802735230978-6ac9bbce4cb59ca80211107a5db9f4c4.pdf),
  Theorem 4.2: the ξ normalization and affine Weyl expansion.
- Lagarias–Suzuki, [*The Riemann hypothesis for certain integrals of Eisenstein series*](https://arxiv.org/abs/math/0412039):
  the parent shift-modulus theory used by the existing Lean bound.

**Anti-theatre assessment:** This closes an analytic prerequisite for the requested
construction. It proves no new theorem beyond the literature and supplies no arithmetic
loop-group quotient, Iwasawa decomposition, or unipotent unfolding. Those are the next
core obligations, not assumptions that may be inserted into a wrapper theorem.
