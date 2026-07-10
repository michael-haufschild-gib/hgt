# Completed-flux quadratic Laguerre reader

- **ID:** completed-flux-laguerre-reader
- **Stage:** 3-formalized
- **Type:** BRIDGE THEOREM (Lean) — formalized, not new scientific knowledge
- **Source:** `CompletedFluxCrossOrderReflection.lean`,
  `CompletedFluxPrimeArchDecomposition.lean`, and `XiLaguerrePolya.lean`
- **Statement:** `[PROVED, BRIDGE]` At every `t` with `Xi t ≠ 0`,
  \[
  (\Xi'(t))^2-\Xi(t)\Xi''(t)
  =-\Xi(t)^2\,c_2(\tfrac12+it),
  \]
  where `c₂(ρ) = completedFluxTaylorCoeff ρ 2`.  Hence
  `Re c₂(1/2+it) > 0` is exactly the strict first-Laguerre failure and refutes RH.  Moreover `c₂`
  is exactly the sum of the fixed continued-prime and archimedean/boundary coefficients.

## Goal

Attach the already-formalized strict Laguerre refutation theorem to the project's genuine
constraint-side object.  The reader uses the single removable completed-flux germ and its fixed
all-order coefficient sequence; it introduces no cutoff, finite carrier, limiting normalization,
flow, or spectral model.

This bridge does not make the Laguerre-positivity lane into the research route.  It makes the
quadratic coefficient a falsification port for the Euler--Gamma constraint program:

- a source proof that the prime-plus-archimedean coefficient is positive at one nonzero line point
  proves `¬RH`;
- a source proof that it is nonpositive everywhere only passes the first necessary RH gate and does
  not prove RH;
- an unconditional proof of RH still requires a genuinely stronger constraint mechanism, not the
  first Laguerre inequality alone.

## Exact identities

For `xi ρ ≠ 0`, the removable germ is `x ↦ x·(-xi'/xi)(ρ+x)`.  Therefore

\[
c_2(ρ)=\left(-\frac{\xi'}{\xi}\right)'(ρ).
\]

Under the critical-line rotation `s=1/2+it`, the first derivative contributes one factor of `i`
and the second derivative contributes `i²=-1`.  Quotient differentiation then gives the
division-free identity

\[
(\Xi')^2-\Xi\Xi''=-\Xi^2 c_2.
\]

The existing fixed source decomposition specializes at order two to

\[
c_2(\tfrac12+it)=c_{2,\mathrm{prime}}(\tfrac12+it)
 +c_{2,\infty+\partial}(\tfrac12+it).
\]

## Main declarations

- `completedFluxTaylorCoeff_two_of_ne_zero`
- `xi_laguerre_margin_eq_neg_sq_mul_completedFluxTaylorCoeff_two`
- `completedFluxTaylorCoeff_two_line_re_pos_iff_laguerre_failure`
- `exists_completedFluxTaylorCoeff_two_line_re_pos_iff_laguerre_failure`
- `completedFluxTaylorCoeff_two_line_re_pos_not_RH`
- `completedFluxTaylorCoeff_two_line_eq_prime_add_archimedean`
- `prime_archimedean_second_coeff_line_re_pos_not_RH`

## Scientific status

`[BRIDGE]` The logarithmic-curvature identity and the first Laguerre criterion are classical.  Lean
verification is not evidence of scientific novelty.  The new research question isolated by this
bridge is the following exact source problem:

`[OPEN CORE]` Determine, from the actual Euler multiplicativity plus the archimedean translation and
reflection constraints, the sign of

\[
\operatorname{Re}\bigl(c_{2,\mathrm{prime}}(\tfrac12+it)
 +c_{2,\infty+\partial}(\tfrac12+it)\bigr)
\]

without replacing the fixed continued prime source by a cutoff or a flow.  Positive sign at one
nonzero `Xi` value disproves RH.  Nonpositive sign alone is not sufficient for RH and must be lifted
to a non-affine all-order constraint reader.

## Gates

- [x] 0 → 1: the exact coefficient and its relation to the supplied RH detector were identified
- [x] 1 → 2: the coefficient, critical-line rotation, quotient derivative, and source split were
  proved without an analytic side hypothesis beyond `Xi t ≠ 0`
- [x] 2 → 3: Lean module `CompletedFluxLaguerreReader.lean`; exact-file check green
- [ ] 3 → 4: independent mathematical audit and integration into a publication containing the
  genuinely new source-sign theorem, if that open core is solved

