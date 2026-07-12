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
|zeta(w)| <= 1 + 1/eps'                                    on re w >= 1 + eps'         (7)
eps'/(1+eps') <= |zeta(w)^(-1)|                            on re w >= 1 + eps'         (8)
t0 + (sqrt N)^(-2 eps)/(2 eps) < 2 eps/(1+2 eps)
    ==>  t0 < |dpoly2 sqrtMoebiusCoeff (Icc 1 N) z|        on re z >= 1/2 + eps        (9)
1/8 < |dpoly2 sqrtMoebiusCoeff (Icc 1 16) z|               on re z >= 1               (10)
```

Relations `(9)`–`(10)` are the closed loop: `(9)` is a certified chart floor whose only
hypothesis is a numeric gap condition in `(eps, N, t0)`; `(10)` is its one numeric
witness (`eps = 1/2`, `N = 16`, `t0 = 1/8`, gap `3/8 < 1/2`).

The rpow bracketing brick unlocks non-integer exponents:

```text
1 <= r^b · x^a  ==>  x^(-(a/b)) <= r        (pure-power certificate, norm_num-checkable) (11)
1/10 < |dpoly2 sqrtMoebiusCoeff (Icc 1 10000) z|          on re z >= 3/4                (12)
```

`(12)` instantiates `(9)` at `eps = 1/4` through `(11)` with `a/b = 1/2`, `x = 100`,
`r = 1/10` (bracket `(1/10)²·100 = 1`; gap `3/10 < 1/3`) — the certified floor now
emits witnesses at any rational `eps`, and `(12)` sits inside `re z < 1`.

The window-bridge module re-emits the floor in every consumer shape of the tree's
machinery: the vertical-line form, the `FloorFailureCofinal` good-heights form, the
σ-weighted one-dimensional `dpoly` form of the detection/second-moment stack
(mollified-carrier nondegeneracy at every height), the sub-abscissa strip extension
through `dpoly2_chart_floor` (real parts below `1/2 + eps` on a variation budget), and
the closed-ball/chart form through `dpoly2_ball_floor` (log-Lipschitz budget).

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
- `sqrtCarrier_floor_of_inv_zeta_floor`: floor transfer `(6)`;
- `norm_riemannZeta_le`: elementary zeta bound `(7)` (triangle inequality + tail `(2)`);
- `inv_zeta_floor`: inverse floor `(8)`;
- `sqrtCarrier_certified_floor`: the certified chart floor `(9)`;
- `sqrtCarrier_floor_witness`: the numeric witness `(10)`;
- `rpow_neg_div_le_of_one_le_pow`, `sqrtCarrier_certified_floor_of_le`: bracketing `(11)`;
- `sqrtCarrier_floor_witness_strip`: the strip witness `(12)`.

Bridge file: `formal/GaloisForLFunctions/RHTower/SqrtCarrierWindowBridge.lean`.

- `sqrtCarrier_certified_floor_line`: the floor on the whole vertical line `re = σ`;
- `sqrtCarrier_good_height_cofinal`: `FloorFailureCofinal`-format good heights;
- `sqrtCarrier_weighted_dpoly_floor`: detection-native σ-weighted `dpoly` nondegeneracy
  at every height;
- `sqrtCarrier_strip_floor`: sub-abscissa extension via `dpoly2_chart_floor`;
- `sqrtCarrier_ball_floor`: chart/ball spreading via `dpoly2_ball_floor`.

The module is imported by `GaloisForLFunctions.RHTower` and `GaloisForLFunctions`.

## Gates

- [x] all bounds explicit and unconditional (half-plane hypotheses only)
- [x] certificate radius height-uniform on the shifted half-plane
- [x] floor conclusion emitted in the exact `dpoly2_chart_floor` premise shape
- [x] targeted module build passes
- [x] generated indexes, axiom audit, and formal lint gate pass

The umbrella build reaches and accepts `SqrtCarrierCertificate` and
`SqrtCarrierWindowBridge`; the independent existing failure is
`SummableEulerCalkinInjectivity.lean`.  All twenty-one public theorems across the two
files use only `propext`, `Classical.choice`, and `Quot.sound`.

## Opens

Two placements are now one budget check away.  (i) In `sqrtCarrier_strip_floor`, the
variation budget `∑ |a_n|·|n^(-σ₁) - n^(-(1/2+eps))|` at the strip witness's parameters
is a finite sum of `norm_num`-accessible rpow differences once `(11)` is extended to
two-sided brackets (`r₁ <= x^(-q) <= r₂`); a numeric budget evaluation would yield the
first certified floor at a real part strictly below the carrier's abscissa `1/2 + eps` —
a floor certificate inside the region where the infinite series no longer converges.
(ii) `sqrtCarrier_weighted_dpoly_floor` and `detection_secondMoment` now speak the same
`dpoly`-coefficient dialect; the forward object is a window inequality combining the
carrier floor with the detection polynomial's small second moment on a common window
`[T, T+U]` — carrier mass bounded below while detection mass is small, the quantitative
separation the density argument runs on.
