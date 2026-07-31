# Finite Anderson localization-tail law

- **Status:** formalized deterministic bridge
- **Lean module:** `GaloisForLFunctions.RHTower.FiniteAndersonLocalizationTailLaw`
- **Claim class:** `[BRIDGE]`, not a model-specific Anderson-localization theorem

## Result

Let \(p_k\ge0\) be normalized spectral weights, let \(r_k\in\mathbb N\)
record the distance from an observer site to the centre assigned to mode
\(k\), and assume
\[
  p_k\le C e^{-2\mu r_k},\qquad
  \#\{k:r_k=m\}\le A B^m,\qquad
  B e^{-2\mu}<1.
\]
Then the spectral weight outside radius \(R\),
\[
  \alpha_R=\sum_{r_k>R}p_k,
\]
satisfies
\[
  0\le\alpha_R\le
  \min\!\left\{
    1,\,
    AC\frac{(B e^{-2\mu})^{R+1}}{1-B e^{-2\mu}}
  \right\}.
\]
Constants are independent of ambient mode count whenever \(A,B,C,\mu\)
are volume-uniform.

## Formal declarations

- `finiteLocalizedSpectralTail`
- `finiteLocalizationShell`
- `finiteLocalizationExponentialEnvelope`
- `finiteLocalizedSpectralTail_le_exponentialEnvelope`
- `finite_sum_pow_le_geometric_tail`
- `finiteLocalizedSpectralTail_le_shellGeometric`
- `finiteLocalizedSpectralTail_le_shellExponential`
- `finiteLocalizedSpectralTail_mem_unitInterval`
- `finiteAndersonLocalizationTailLaw`

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/FiniteAndersonLocalizationTailLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/FiniteAndersonLocalizationTailLaw.olean
```

passed. Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Boundary

No theorem here proves that a standard random Anderson Hamiltonian supplies
a site-labelled eigenbasis, exponential eigenfunction decay, or
volume-uniform constants. Existing project results prove only finite-horizon
weak-hopping transition suppression. The manuscript may use this result as
the deterministic interface from a localization estimate to recurrence,
but may not call it a new proof of Anderson localization.
