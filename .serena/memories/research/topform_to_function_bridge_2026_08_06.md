# The bridge from top forms to rational functions (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Extension of module 34,
`CoframeEigenvolumeNonzero.lean`.  See
[[research/coframe_eigenvolume_nonzero_step1_2026_08_06]].

## Added

- **`eq_smul_topWedge`** — every element of `⋀^(card ι) M` is
  `(b.exteriorPower _).repr x default • (b.exteriorPower _) default`.  Proof: `Basis.sum_repr`
  plus `Fintype.sum_unique`, using the corpus's `uniqueTopCombination` instance.
- **`exists_ne_zero_smul_eq_of_ne_zero`** — over a field, a nonzero top form is a **nonzero**
  scalar times the wedge of the basis.

## Why it matters

The card writes `div(Ω)` for a rational top form, but the horizon theorem in this corpus is stated
for the divisor of a rational **function** (`formOrder a b P`, `ordAt g z`).  These lemmas are the
bridge: fixing a reference top form, every other top form is a rational-function multiple of it,
so `div(Ω)` is the divisor of that function.  Without this the two formulations were only
informally identified.

## Lean note

Declaring `[AddCommGroup M]` locally when the section already provides it triggers the
`overlappingInstances` linter (which fails the gate).  Declare only the *new* structure
(`[Field K] [Module K M]`) and let `M`'s additive structure come from the section.

## Remaining for Theorem A

1. Different exponent `e − 1` for a general tame extension.
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
