# The logarithmic de Rham complex and the Poincaré residue, as sheaves

- **ID:** `log-de-rham-residue-sheaf`
- **Stage:** 1-in-progress
- **Type:** INFRASTRUCTURE
- **Parents:** `deninger-pro-log-stein-kummer-residue-square`,
  `deninger-strict-pro-log-collar-trace-kernel`

## Why

Both analytic deninger cards record the same three obstructions: "no Stein theory, no coherent-sheaf
cohomology and no logarithmic de Rham complex".  Two of the three are stale.  The corpus now proves
**Cartan's theorem B** on `ℂ^n` and on `(ℂ^×)^n` (`deningerHolomorphic_ext_eq_zero`,
`_punctured`), and for free analytic sheaves of finite rank (`deningerFree_ext_eq_zero_punctured`);
it has sheaf cohomology as `Ext` out of the free abelian sheaf on an open set, acyclic resolutions,
fine sheaves and partitions of unity; and it has the acyclicity and filtered passage that
`(12)`--`(14)` of the residue-square card asks for, in the form
`deningerAcyclicOn_of_filtration`, `deningerFiltration_sections_surjective` and the three
direct-limit exactness theorems.

What is genuinely missing is the third: the logarithmic de Rham complex of a chart with a smooth
divisor, and the Poincaré residue as a morphism of sheaves.

## What is to be built

On the split chart of the residue-square card, `W × ℂ` with divisor `D = W × {0}`, a logarithmic
`k`-form is uniquely `α + (dz/z) ∧ β` with `α` a holomorphic `k`-form and `β` a holomorphic
`(k-1)`-form, and the Poincaré residue is `β|_{z=0}`.

1. The presheaf of logarithmic forms on the chart, and its sheaf condition, by the corpus's local
   predicate machinery.
2. The residue as a morphism of sheaves onto the pushforward of the forms of the divisor.
3. The residue sequence `0 → Ω^k → Ω^k(log D) → i_* Ω^{k-1}_D → 0` and its exactness.
4. Acyclicity of the terms, from Cartan's theorem B for free sheaves already proved, and the
   filtered passage already proved.

## Status

Not started.  The card exists so that the two analytic cards' remaining obstruction is a named
object with a plan rather than a sentence.
