# Finite-cutoff certificate for the zeta(2z)-inverse carrier

- **ID:** `sqrt-carrier-finite-cutoff-certificate`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[SEARCH] [FORMALIZATION] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** On `re z >= 1/2 + eps` the square-dilated Möbius carrier at cutoff `N`
  approximates `zeta(2z)^(-1)` within the explicit, height-uniform radius
  `(sqrt N)^(-2 eps)/(2 eps)`, so the carrier limit becomes a finite-cutoff certificate
  that feeds the off-line floor machinery `dpoly2_chart_floor` directly.

## Exact relations

```text
dpoly2 sqrtMoebiusCoeff (Icc 1 N) z = dpoly2 moebiusCoeff (Icc 1 sqrt(N)) (2z)         (1)
sum_{k>M} k^(-c) <= M^(1-c)/(c-1)                          for c > 1, M >= 1           (2)
|L(a,w) - dpoly2 a (Icc 1 M) w| <= M^(1-re w)/(re w - 1)   for |a_n| <= 1, re w > 1    (3)
|zeta(w)^(-1) - dpoly2 moebiusCoeff (Icc 1 M) w| <= M^(1-re w)/(re w - 1)              (4)
|zeta(2z)^(-1) - dpoly2 sqrtMoebiusCoeff (Icc 1 N) z|
    <= (sqrt N)^(-2 eps)/(2 eps)                 uniform on re z >= 1/2 + eps          (5)
t0 + (sqrt N)^(-2 eps)/(2 eps) < |zeta(2z)^(-1)|
    ==>  t0 < |dpoly2 sqrtMoebiusCoeff (Icc 1 N) z|                                    (6)
```

## Proof

`(1)` the square-dilated coefficients vanish off squares; reindexing the carrier sum along
`k -> k*k` (with `Nat.sqrt` as inverse on the square support, and `k^2 <= N` iff
`k <= sqrt N`) turns each summand `mu(k)·(k^2)^(-z)` into `mu(k)·k^(-2z)` — the analytic
dilation law at every finite level.  `(2)` integral test: the tail partial sums are
dominated by `∫_M^{M+n} x^(-c) dx`, evaluated in closed form and bounded by dropping the
negative endpoint term; the tsum bound follows from the partial-sum bounds.  `(3)` the
truncation error is the shifted term tail (`Summable.sum_add_tsum_nat_add`), its norm is
dominated termwise by `n^(-re w)` since the coefficients are mollifier-grade, and `(2)`
applies at `c = re w`.  `(4)` is `(3)` at the Möbius coefficients with
`L(mu, w) = zeta(w)^(-1)`.  `(5)` is `(4)` at `w = 2z`, `M = sqrt N` through `(1)`,
followed by monotonicity in the exponent and the denominator on the shifted half-plane —
the radius is independent of the height.  `(6)` is the reverse triangle inequality; its
conclusion is verbatim the `hline` premise of `dpoly2_chart_floor` and
`chart_floor_cofinal_of_line_cofinal`.

## Parent classification

`[SEARCH]` Effective truncation of a Dirichlet series in its half-plane of absolute
convergence by the integral test is classical elementary analysis (Apostol, *Introduction
to Analytic Number Theory*, ch. 12 techniques).  Not new scientific knowledge; new to the
tree is the wiring: the finite dilation identity `(1)` and the certificate emitted in the
exact interface shape the chart-floor machinery consumes.

## Prior-state audit

Absent from mathlib: any effective truncation bound for L-series (mathlib's `LSeries` API
is qualitative), the integral-test tail bound in the form `(2)`, and the finite dilation
identity.  Absent from the tree: `DpolyOffline.lean` bounds `dpoly2` variation between
real parts but had no link from `dpoly2` to any L-series value; the bridge of
`MFreeLadder` was a limit statement without rate.

## Reuse audit

- `MFreeLadder.lean`: `dpoly2_Icc_eq_sum_range_term` (extracted there from the bridge in
  this work), `sqrtMoebiusCoeff`, `moebiusCoeff_complex`, `natCast_sq_cpow`,
  `LSeries_moebius_eq_inv_riemannZeta`;
- `SquarefreeMoebiusNormalization.lean`: `sqrtPart_apply_mul_self`,
  `sqrtPart_apply_of_not_isSquare`;
- `Mollifier.lean`: `moebiusCoeff`, `abs_moebiusCoeff_le_one`;
- `DpolyOffline.lean`: `dpoly2` and the floor interface the certificate targets;
- mathlib: `AntitoneOn.sum_le_integral`, `integral_rpow`, `Real.tsum_le_of_sum_range_le`,
  `Summable.sum_add_tsum_nat_add`, `norm_tsum_le_tsum_norm`,
  `LSeriesSummable_of_bounded_of_one_lt_re`.

## Lean certificate

File: `formal/GaloisForLFunctions/RHTower/SqrtCarrierCertificate.lean`.

- `antitoneOn_rpow_neg`, `sum_range_add_rpow_neg_le`, `tsum_add_rpow_neg_le`: bound `(2)`;
- `norm_LSeries_sub_dpoly2_le`: bound `(3)` for arbitrary mollifier-grade coefficients;
- `norm_inv_riemannZeta_sub_dpoly2_moebiusCoeff_le`: instance `(4)`;
- `dpoly2_sqrtMoebiusCoeff_eq_moebius_sqrt`: identity `(1)`;
- `sqrtCarrier_certificate`, `sqrtCarrier_certificate_uniform`: certificate `(5)` in
  exact-rate and height-uniform forms;
- `sqrtCarrier_floor_of_inv_zeta_floor`: floor transfer `(6)`.

The module is imported by `GaloisForLFunctions.RHTower` and `GaloisForLFunctions`.

## Gates

- [x] all bounds explicit and unconditional (half-plane hypotheses only)
- [x] certificate radius height-uniform on the shifted half-plane
- [x] floor conclusion emitted in the exact `dpoly2_chart_floor` premise shape
- [x] targeted module build passes
- [x] generated indexes, axiom audit, and formal lint gate pass

The umbrella build reaches and accepts `SqrtCarrierCertificate`; the independent existing
failure is `SummableEulerCalkinInjectivity.lean`.  All nine public theorems use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Opens

Relation `(6)` reduces a chart floor for the finite carrier to a lower bound for
`|zeta(2z)^(-1)| = 1/|zeta(2z)|` on `re z >= 1/2 + eps`, i.e. to an upper bound for
`|zeta|` on `re w >= 1 + 2 eps`; the elementary bound `|zeta(w)| <= zeta(1 + 2 eps)` from
the termwise triangle inequality would close the loop and make the chart floor fully
explicit — the next brick is that upper bound as a tree lemma, then a numeric
instantiation `(eps, N, t0)` producing the first concrete certified chart floor.
