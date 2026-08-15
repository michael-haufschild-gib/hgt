# CCM bounded-variation Muntz graph-domain extension

- **ID:** `ccm-bv-muntz-graph-domain-extension`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent sources:** the classical Muntz formula; Connes--Consani, *Spectral triples and
  zeta-cycles*, Lemma 6.1 and the proof of Theorem 6.4; Baez-Duarte and Burnol on `L2` Muntz
  operators
- **Statement:** The global CCM summation vector of a compactly supported bounded-variation source
  with zero integral belongs to `L2(d*u)` and to the maximal zeta-multiplier graph domain, even
  when the source has the endpoint jump created by zero extension. Its Mellin transform vanishes
  at every nontrivial zeta zero.

## Theorem

Let `f:[0,infinity)->C` have compact support in `[0,L]`, let its zero extension have bounded
variation, and suppose

```text
integral_0^infinity f(x) dx=0.                         (1)
```

For `u>0` define the finite sum

```text
E(f)(u)=u^(1/2) sum_(n>=1) f(nu).                     (2)
```

Then, writing `V=Var(f)`,

```text
|E(f)(u)| <= V u^(1/2),
supp E(f) subset (0,L],
||E(f)||_(L2(d*u)) <= V sqrt(L).                      (3)
```

For `Im z>-1/2`, put

```text
Psi_f(z)=integral_0^infinity f(x)x^(1/2-iz)d*x.       (4)
```

Both sides below are holomorphic in that half-plane, after removing the singularity at `z=i/2`,
and

```text
integral_0^infinity E(f)(u)u^(-iz)d*u
  =zeta(1/2-iz) Psi_f(z).                             (5)
```

Consequently `f` lies in the maximal zeta-multiplier graph domain and the Mellin transform of
`E(f)` vanishes at every spectral point

```text
z_rho=i(rho-1/2),   zeta(rho)=0,   0<Re rho<1.        (6)
```

## Proof

Partition the positive half-line into the intervals `((n-1)u,nu]`. On each interval, comparison
with the right-endpoint Riemann sum gives

```text
|u f(nu)-integral_((n-1)u)^(nu) f(x)dx|
  <=u Var_((n-1)u,nu](f).
```

Summing the finite nonzero terms and using `(1)` yields

```text
|sum_(n>=1) f(nu)| <= V.                              (7)
```

Equation `(3)` follows immediately from `(2)`, from the support condition, and from

```text
integral_0^L V^2 u d*u=V^2 L.
```

The bound `(3)` makes the left side of `(5)` holomorphic for `Im z>-1/2`. The same is true of
`Psi_f`: near zero its integrand is bounded by a constant times `x^(-1/2+Im z)dx`, and at infinity
the source is compactly supported. If `Im z>1/2`, absolute convergence permits interchange of the
sum and integral, followed by `x=nu`:

```text
integral E(f)(u)u^(-iz)d*u
 =sum_(n>=1) n^(-1/2+iz)
    integral f(x)x^(1/2-iz)d*x
 =zeta(1/2-iz)Psi_f(z).                               (8)
```

The only pole of the right side in `Im z>-1/2` is the apparent pole at `z=i/2`. But

```text
Psi_f(i/2)=integral_0^infinity f(x)dx=0,
```

so the pole is removable. Analytic continuation proves `(5)` throughout the half-plane.
Equation `(3)` and Mellin--Plancherel show on the real axis that

```text
integral_R |zeta(1/2-it)|^2 |Psi_f(t)|^2 dt<infinity,
```

which is exactly maximal multiplier graph-domain membership. Finally `z_rho` lies in
`-1/2<Im z<1/2`, and substituting it into `(5)` proves `(6)`.

## Application to the CCM prolate source

The CCM seed source `h_lambda` is a linear combination of two smooth prolate eigenfunctions on
`[-lambda,lambda]`, extended by zero outside, and is chosen to have zero integral. Its restriction
to the positive half-line satisfies the theorem. Resetting its value at the single point zero, as
in `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-restricted-summation-aperture-gauge.md`,
changes neither its `L2` class nor `E(h_lambda)`
almost everywhere.

Thus the endpoint jump does **not** invalidate the global Muntz vector, the zeta-multiplier identity,
or divisor-radical membership. In the zero-side Weil sampling realization, `E(h_lambda)` vanishes
at every nontrivial zeta zero, including hypothetical off-line zeros. Whenever the cut vector and
its exterior tail lie in a common extension of the Weil form domain, the quotient identity in
`ccm-weil-exterior-tail-quotient-gate.md` therefore applies to the genuine prolate source rather
than only to a Schwartz surrogate.

The theorem supplies membership, not the cofinal estimate required by CCM. Its crude lower-tail
bound is only

```text
||1_(0,lambda^(-1)) E(h_lambda)||_2
  <=Var(h_lambda)/sqrt(lambda),                        (9)
```

whereas identification of the true Weil ground vector must be measured relative to the extremely
small constrained spectral gaps. The missing theorem is still a source-specific quantitative
Weil-form/sampling estimate, not mere finiteness of the graph norm.

## Route consequence

- `[CLOSED DOMAIN OBJECTION]` Zero extension of a prolate eigenfunction leaves the Schwartz class,
  but it does not leave the natural `L2` zeta-multiplier domain.
- `[OPEN]` Prove a cofinal rate for its exterior tail in the closed Weil form or discrete sampling
  topology, relative to the fixed-mode gap ladder.
- `[OPEN]` Transfer that rate to the projective ground-vector estimate needed for locally uniform
  determinant convergence.

## Novelty and significance verdict

The proof is a bounded-variation Riemann-sum estimate followed by the classical Muntz identity and
analytic continuation. More decisively, Connes--Consani Lemma 6.1 already proves the same
`O(u^(1/2))` estimate for bounded-variation zero-mean sources satisfying `f(u)=O(u^2)` at zero, and
their proof of Theorem 6.4 supplies the zeta multiplier continuation. The invisible central gauge
in `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-restricted-summation-aperture-gauge.md`
produces exactly such a representative for the CCM
aperture vector. The present statement only observes that bounded behavior at zero is already
enough if one works with the ungauged source. Baez-Duarte and Burnol also develop substantially more
general `L2` Muntz frameworks. This is a useful route reconciliation, not new scientific knowledge.

## References

- A. Connes, C. Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715.
- L. Baez-Duarte, *A general strong Nyman--Beurling criterion for the Riemann hypothesis*,
  arXiv:math/0505453.
- J.-F. Burnol, *On Fourier and zeta(s)*, Forum Math. 16 (2004), 789--840.

## Lean status

**Superseded, 2026-08-04.**  Formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCMBVMuntzSummation.lean`.  The previous decision said the tree has
no Mellin--Plancherel interface, so only the Riemann-sum inequality could be certified and that would
be "a wrapper".  That undersells the estimate: `(7)` is the only place the bounded-variation hypothesis
does any work, and it is what makes the endpoint jump harmless — which is the whole point of the card.

Proved so far, all unconditional (`#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`):

- **`abs_cell_discrepancy_le`** — the one-cell estimate: the right-endpoint Riemann value differs from
  the cell mean by at most the length times the variation on that cell.  Uses mathlib's
  `eVariationOn` and `BoundedVariationOn.dist_le`.
- **`sum_variation_cells_le`** — the variations over a uniform partition add up to at most the total
  variation, from mathlib's `eVariationOn.sum'`.
- **`abs_sum_riemann_sub_integral_le`** — the discrepancy bound in the form that carries no hypothesis
  on the support or the integral:

  ```text
  | u sum_(n<=N) f(nu) - int_0^(Nu) f | <= u Var(f).
  ```

  Isolating it this way is what makes the support and zero-integral hypotheses of the card enter only
  once, at the very end.
- `integral_trunc_eq_zero` — for a source supported in `(0, L]` with vanishing integral, the truncated
  integral past `L` still vanishes.
- **`abs_sum_le_variation`** — equation `(7)`: `|∑_{n ≥ 1} f(nu)| ≤ Var(f)`, uniformly in the sampling
  scale.
- `summationVector`, `summationVector_eq_finset`, `summable_summand` — equation `(2)`.  The vector is
  defined by an unconditional `tsum`; for every scale only finitely many terms are nonzero, so the
  `tsum` equals the truncated finite sum, and no summability hypothesis is needed anywhere.
- **`summationVector_eq_zero_of_lt`**, `summationVector_eq_zero_of_nonpos` — the support statement of
  `(3)`: `E(f)` vanishes past `L`, and on the nonpositive half-line.
- **`abs_summationVector_le`** — the pointwise bound of `(3)`: `|E(f)(u)| ≤ Var(f) √u`.
- **`measurable_summationVector`** — measurability of `E(f)`, obtained from the partial sums: for every
  scale the summand family is finitely supported, hence summable, hence the `tsum` is the pointwise
  limit of measurable partial sums.
- **`integral_sq_summationVector_le`**, **`integral_Ioi_sq_summationVector_le`** — the `L²(d*u)` bound
  of `(3)`, truncated and on the whole half-line: `∫_0^∞ |E(f)(u)|² d*u ≤ Var(f)² L`.  The
  multiplicative measure makes the pointwise bound `|E(f)(u)|² ≤ Var(f)² u` integrate to a constant, so
  the estimate needs no Minkowski inequality.
- `arithmeticSum`, `measurable_arithmeticSum`, `arithmeticSum_eq_zero_of_lt`,
  **`abs_arithmeticSum_le`** — the unnormalized vector `∑_{n ≥ 1} f(nu)`, bounded by `Var(f)` by `(7)`
  and vanishing past `L`.  These are exactly the hypotheses the Mellin differentiability criterion
  consumes.
- `integrableOn_rpow_mul_abs`, `mellinConvergent_source`, `integral_rpow_mul_abs_comp_mul`,
  **`mellin_arithmeticSum_eq_zeta_mul`** — equations `(4)`, `(8)`: the Müntz identity on the half-plane
  of absolute convergence `1 < Re s`, which in the card's variable is `Im z > 1/2`.  The interchange is
  `hasSum_integral_of_summable_integral_norm`; the substitution `x = nu` is mathlib's
  `mellin_comp_mul_left`, and the dilation law for the *norm* integrals is proved separately from
  `integral_comp_mul_left_Ioi`.
- `locallyIntegrable_ofReal_of_bound`, `isBigO_atTop_of_support`, `isBigO_zero_of_bound`,
  **`differentiableAt_mellin_of_bound_support`** — both Mellin transforms are holomorphic on the whole
  right half-plane.  A bounded compactly supported source is `O(t^{-a})` at infinity for every `a`
  (it is eventually zero) and `O(1)` at the origin, so the criterion applies with `b = 0`, and
  `0 < Re s` is the only constraint.
- **`eqOn_mellin_arithmeticSum_zeta`** — equation `(5)`, the continuation.  Stated for an arbitrary open
  convex region of the right half-plane that avoids `s = 1` and meets `Re s > 1`.  The card removes the
  apparent pole at `z = i/2` using `Ψ_f(i/2) = 0`; that is not needed, because a convex region avoiding
  the pole altogether already reaches every point of the critical strip once one uses that a zeta zero
  in the strip is off the real axis.
- **`mellin_arithmeticSum_eq_zero_of_zeta_eq_zero`** — equation `(6)`: the Mellin transform of the
  summation vector vanishes at every zeta zero of the open critical strip, including any hypothetical
  off-line zero.  The two quadrants `{Re s > 0, Im s > 0}` and `{Re s > 0, Im s < 0}` are convex and
  avoid `s = 1`, and every strip zero lies in one of them because zeta has no real zero in `(0,1)` —
  the corpus theorem `RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo`.

Nothing the card proves is left unformalized.  The remaining gates below are its own open research
items.

## Gates

- [x] exact bounded-variation Riemann-sum discrepancy proved
- [x] Lean: one-cell and partition variation estimates unconditional
- [x] Lean: Riemann-sum discrepancy `(7)` unconditional
- [x] Lean: summation vector `(2)`, its support and pointwise bound `(3)` unconditional
- [x] Lean: measurability and the `L²(d*u)` bound of `(3)` unconditional
- [x] Lean: Muntz zeta-multiplier identity `(4)`--`(5)` unconditional, in the convergence region and by
      convex continuation
- [x] Lean: vanishing at every nontrivial zeta zero `(6)` unconditional
- [x] global `L2(d*u)` membership of the zero-extended prolate summation vector proved
- [x] maximal zeta-multiplier graph-domain membership proved
- [x] vanishing at every nontrivial zeta zero proved
- [ ] cofinal exterior-tail estimate in the closed Weil/sampling topology
- [ ] relative true-Weil ground-vector transfer
- [ ] locally uniform normalized determinant convergence to `Xi`
