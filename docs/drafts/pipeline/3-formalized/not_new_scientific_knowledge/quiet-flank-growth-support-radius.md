# Quiet flank growth gives an exact arithmetic support bound

- **ID:** quiet-flank-growth-support-radius
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), `[PROVED HERE]`
- **Date:** 2026-07-10
- **Source:** abstraction and correction of the Q-COC proposal in
  `../../1-in-progress/cocycle-shape-rigidity-gamma-extremality.md`.
- **Lean endgame:** `formal/GaloisForLFunctions/RHTower/QuietFlankGrowth.lean`.

## Statement

Let `F` be entire and agree on `Re(s)>=c`, with `c>=1/2`, with an absolutely convergent ordinary
Dirichlet series

`L(s)=sum_{n>=1} a_n n^{-s}`.

Assume the quiet-crossing hypothesis used by `quiet_crossing_rigidity`: there are heights
`T_k -> infinity` and bounds `q_k=o(T_k^2)` such that

`|F(sigma +/- i T_k)| <= q_k` for `1-c <= sigma <= c`.

Suppose a nonnegative flank envelope `H(M)` satisfies, for every sufficiently large integer `M`,

`|F(s)| <= H(M)` whenever `-M <= Re(s) <= 1-c`.                    (F_M)

With the fixed knots `n+1/2,n,n-1/2`, for every `n>=1` and every sufficiently large `M`,

`|a_n/2| <= 2 H(M) (n-1/2)^(1-M)`.                              (1)

Consequently, at fixed knot width:

1. if `H(M)(n-1/2)^(1-M) -> 0`, then `a_n=0`;
2. if eventually `H(M) <= C R^M` with `C>=0`, `R>=0`, then
   `R<n-1/2` implies `a_n=0`;
3. equivalently, every nonzero coefficient obeys the preliminary bound

   `n <= R+1/2`.                                                  (2)

Now replace `1/2` by any real `delta` with `0<delta<1`. The same contour proof gives

`|delta a_n| <= 2 H(M) (n-delta)^(1-M)`.                       (3)

If `H(M)<=C R^M` and `R<n`, choose

`0<delta<=min(1/2,(n-R)/2)`.

Then `R<n-delta`, so (3) forces `a_n=0`. Therefore the exact support conclusion is

`a_n != 0  ==>  n <= R`.                                        (4)

Thus exponential flank growth gives an exact upper bound for arithmetic support; the half-unit in
(2) is only an artifact of freezing the Perron knots.

## Correction to the proposed equality

The in-progress card proposed

`support radius = limsup H(M)^(1/(M-1))`.

That equality is not theorem-grade. Any valid `H` may be replaced by a larger envelope, and the zero
carrier has empty support while satisfying envelopes of arbitrary rate. The invariant conclusion is
the one-sided implication (2).

One can make the right side canonical by defining the intrinsic quiet-flank radius of `F` as the
infimum of bases `R` for which some admissible envelope `C R^M` satisfies `(F_M)`. The theorem then
gives

`a_n != 0  ==>  n <= intrinsic quiet-flank radius`.

No reverse inequality is asserted.

## Proof

Fix `n` and write

`E_n(s)=K_n(s)/(s(s+1))`,

where `K_n` is the three-knot Perron numerator already used in
`QuietCrossingRigidity.lean`. The banked Perron identity is

`a_n/2 = (1/(2 pi)) integral_R F(c+it) E_n(c+it) dt`.             (3)

For a fixed integer depth `M>=max(2,c)`, move the contour in (3) to the rectangle with vertical
sides `Re(s)=c` and `Re(s)=-M` and horizontal sides at `+/- T_k`. The integrand is entire.

### Horizontal edges

On the part with `Re(s)<=1-c`, hypothesis `(F_M)` bounds `F` by `H(M)`. On the critical strip the
quiet hypothesis bounds it by `q_k`. The Perron numerator is bounded by a constant depending on
`n,c`, while

`|s(s+1)|^{-1} <= T_k^{-2}`.

Hence each horizontal integral is

`O_{n,c,M}((H(M)+q_k)T_k^{-2})`,

which tends to zero as `k->infinity`.

### Left edge

On `s=-M+iy`, the three-knot numerator satisfies

`|K_n(s)| <= 4 (n-1/2)^(1-M)`,

and

`|s(s+1)|^{-1} <= ((M-1)^2+y^2)^{-1}`.

Therefore

`integral_R |F(-M+iy)E_n(-M+iy)| dy`

`<= 4 H(M)(n-1/2)^(1-M)
    integral_R ((M-1)^2+y^2)^{-1}dy`

`<= 4 pi H(M)(n-1/2)^(1-M)`.                                   (4)

Letting `k->infinity` in the rectangle identity, then combining (3) and (4), gives (1).

If `H(M)(n-1/2)^(1-M)->0`, the fixed nonnegative number `|a_n/2|` is at most a sequence tending to
zero, so `a_n=0`. Under `H(M)<=C R^M`, the right side is a constant times

`(R/(n-1/2))^M`,

which tends to zero exactly when `R<n-1/2`. This proves (2).

For the variable-knot strengthening, apply the same smoothed Perron formula at
`x_+=n+delta`, `x_0=n`, and `x_-=n-delta`, where `0<delta<1`. For an integer index `m<n`, the
second difference of `max(x-m,0)` vanishes because all three arguments lie in its affine region.
For `m=n`, the three weights are `delta,0,0`; for `m>n`, all are zero because `delta<1`. Hence the
second difference is exactly `delta a_n`. The numerator still vanishes at `s=0,-1`, while its
negative-exponent bound is

`|K_{n,delta}(-M+iy)| <= 4(n-delta)^(1-M)`.

This proves (3). If `R<n`, the displayed choice of `delta` has `R<n-delta`, so the same ratio test
forces `a_n=0`. Contraposition gives the exact bound (4).

## Three consistency tests

1. **Exact reflection.** A constant flank envelope has geometric radius `R=1`. Then (4) says a
   nonzero positive-index coefficient has `n<=1`; this recovers degree zero without rounding.
2. **Conductor datum.** The banked conductor equation gives
   `H(M)=C_J B Q_0^(1+2M)`, whose geometric radius is `Q_0^2`. Formula (2) gives
   `n<=Q_0^2`, exactly the existing conductor support theorem.
3. **Gamma flank.** Gamma growth has the form `exp(c M log M+O(M))`, with infinite geometric
   radius. The theorem gives no finite support conclusion, as required for completed L-functions.

## Attack and scope

- `[PROVED]` The contour machine consumes only a uniform left-rectangle flank envelope; it does not
  need the finite conductor polynomial after that envelope is supplied.
- `[PROVED]` The proposed equality with an arbitrary `H` is false; only the upper support bound
  survives.
- `[PROVED]` Variable knots `n+/-delta` remove the fixed-knot half-unit for every real radius; the
  exact support bound is (4).
- `[OPEN CORE]` This theorem is conditional on a quiet height sequence. It does not manufacture
  quiet crossings from divisor sparsity or from the functional equation.
- `[OPEN CORE]` The RH-facing problem is now precise: prove a quiet sequence or an equivalent
  contour-smallness statement for the target completed carrier, or prove that every non-Gamma
  cocycle has finite intrinsic quiet-flank radius.

## Novelty and significance gates

- **NOVEL:** the project had the constant-flank and finite-conductor endpoints separately. The
  theorem extracts their common invariant, corrects the proposed equality, and supplies the exact
  growth-to-support inequality for an arbitrary flank envelope.
- **SIGNIFICANT:** this identifies the gate between cocycle geometry and arithmetic support. It
  explains in one theorem why conductor data collapse to Dirichlet polynomials while Gamma data do
  not, without assuming a Selberg degree classification.

## Formal status

The reusable endgame is formalized in `QuietFlankGrowth.lean`:

- `HasQuietFlankCoefficientBound` packages (1), with fixed constants absorbed into `H`;
- `tendsto_flank_product_of_geometric_envelope` proves the ratio-test limit;
- `coefficient_eq_zero_of_geometric_quiet_flank` forces vanishing;
- `coefficient_index_le_flank_radius` proves the fixed-knot estimate (2);
- `HasVariableQuietFlankCoefficientBound` packages the variable-knot family;
- `coefficient_index_le_exact_flank_radius` proves the exact support bound (4).

The variable Perron source is formalized separately in `VariablePerronKink.lean`:

- `perronKinkAt_second_difference` proves exact extraction of `delta*a_n`;
- `perronEAt_differentiable` removes the two kernel poles;
- `perronKinkAt_norm_le` exposes the `n-delta` left-edge scale;
- the fixed kernel and regularization are recovered definitionally at `delta=1/2`.

The more general boundary-only producer is formalized in `PerronBoundaryCharge.lean`, and the
coefficient-independent carrier interfaces in `PerronCarrierFlankMass.lean`.  The direct
uniform-flank wrapper for `(F_M)` is now formalized as well, in `PerronUniformFlankProducer.lean`
(see `## Lean formalization`), so the card's hypotheses are consumed literally.

## Gates

- [x] 0 -> 1: arbitrary flank envelope and exact surviving inequality isolated.
- [x] 1 -> 2: contour proof and three endpoint checks complete.
- [x] 2 -> 3: numeric growth-to-support capstone formalized; the generic analytic contour producer
  is now factored out (`PerronUniformFlankProducer.lean`, see `## Lean formalization`).
- [ ] 3 -> 4: requires integration into a standalone cocycle-shape paper and an independent
  novelty audit.

## Lean formalization

Module `formal/GaloisForLFunctions/RHTower/PerronUniformFlankProducer.lean`, wired into
`RHTower.lean`.  Unconditional; axiom profile `[propext, Classical.choice, Quot.sound]`.

It closes the last gap in the chain by discharging the two carrier interfaces of
`PerronCarrierFlankMass.lean` from the card's own hypotheses.

**Left line.**  `hasPerronCarrierFlankMassAt_of_uniform_flank` — a uniform bound
`‖F(-M+iy)‖ ≤ A` gives `HasPerronCarrierFlankMassAt F M (π A)`, because the coefficient-independent
Cauchy weight integrates to exactly `π` (`integral_univ_inv_one_add_sq`).  With the corpus
normalization `HasPerronCarrierFlankMass F H ↔ mass ≤ (π/2)·H(M)`, this gives
`hasPerronCarrierFlankMass_of_uniform_flank : HasPerronCarrierFlankMass F (fun M => 2 * H M)`,
i.e. exactly the factor `2` of the card's estimate `|a_n/2| ≤ 2 H(M)(n-1/2)^(1-M)`.

**Horizontal edges.**  `hasPerronHorizontalEscapeAt_of_quiet_heights` — if the carrier is bounded
by `Q k` across the whole width `-M ≤ x ≤ c` at heights `±T k` and `Q k/(1+T k²) → 0`, both
horizontal edge integrals vanish.  The kernel input is the corpus's
`perronEAt_strip_high_norm_le` (quadratic strip decay above unit height); the sequence is shifted
to `T(·+k₀)` internally so that `1 ≤ T k` holds on the nose, which is why no extra hypothesis on
the exhaustion is needed.

**Assembly.**  `hasVariablePerronHorizontalEscape_of_quiet_uniform_flank` splits the width at
`Re s = 1-c`: on `[-M, 1-c]` the flank envelope applies, on `[1-c, c]` the quiet bound does, so
`Q k = H(M) + q k` works, and `c ≥ 1/2` is exactly what makes the two regions cover the width and
forces `q k ≥ 0`.

**Capstone** `coefficient_index_le_exact_flank_radius_of_quiet_uniform_flank`:

```text
c ≥ 1/2, F entire, F = L(a) on Re s ≥ c, a summable there, 1 ≤ n,
T k → ∞,  ‖F(σ ± i T k)‖ ≤ q k on 1-c ≤ σ ≤ c,  q k / (T k)² → 0,
‖F s‖ ≤ H M whenever -M ≤ Re s ≤ 1-c,  H M ≤ C R^M eventually,  0 ≤ R,
a n ≠ 0
⟹ (n : ℝ) ≤ R
```

which is the card's exact support conclusion (4).  No positivity hypothesis on `H` is needed: it
follows from the flank bound itself.  The half-unit-free form comes for free because the corpus
capstone already runs over all Perron knot widths `0 < δ < 1`.
