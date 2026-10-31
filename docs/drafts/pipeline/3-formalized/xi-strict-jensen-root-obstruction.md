# Strict Xi Jensen root obstruction

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** A repeated real root of any reversed finite Jensen section of Xi falsifies RH.

## Proof

For a split real polynomial, `D-a` lowers inherited root multiplicities by one;
strict Laguerre positivity makes newly created roots simple. After `d` nonzero real
shifts, every real root of a nonzero polynomial of degree at most `d` is simple.

Under RH, Xi is Laguerre–Pólya. Its infinitely many positive real zeros exist
unconditionally (`infinite_positive_real_XiC_zeros`). Extract `d` factors by
`laguerrePolya_dslope`: the quotient remains Laguerre–Pólya and Schwarz-real,
is nonzero at zero, and retains infinitely many positive real zeros.

Multiplication by `z-a` becomes `D-a` on reversed Jensen sections. The quotient's
section splits and has degree at most `d`; its leading coefficient is its nonzero
value at zero. Applying the extracted factors proves root multiplicity at most one.

## Distinction

Repeated real roots can occur in a splitting polynomial. This obstruction strengthens
nonsplitting tests; it does not assume simplicity of Xi zeros.

## Lean statements

`arithmetic-positivity-theory/Jensen/XiStrictRoots.lean`:

- `JensenStrict.rootMultiplicity_shiftChain_le_one`: enough nonzero real shifts remove repeated roots.
- `JensenStrict.jensenReverse_linear_mul`: real linear factors become Laguerre shifts.
- `JensenStrict.exists_realFactorChain`: extraction preserves the required quotient properties.
- `RHTower.xiJensenReverse_rootMultiplicity_le_one_of_rh`: every real root is simple under RH.
- `RHTower.not_riemannHypothesis_of_xiJensenReverse_multiple_root`:
  `(∃ d x, 1 < (jensenReverse (realTaylorCoeff XiC) d).rootMultiplicity x) → ¬ RiemannHypothesis`.

## Verification

Standalone `lake --old env lean` source audit passed without warnings. All six
`#print axioms` checks report only `propext`, `Classical.choice`, and `Quot.sound`.
Imported by `ArithmeticPositivityTheory.lean`; no umbrella build or added proof limits.
