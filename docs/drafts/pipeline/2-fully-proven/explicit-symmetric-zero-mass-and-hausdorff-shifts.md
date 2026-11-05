# Explicit zero-mass and Hausdorff thresholds

- **ID:** explicit-symmetric-zero-mass-and-hausdorff-shifts
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Source:** review-0511, A18.
- **Lean status:** formalization in progress.

## Statement

For `ε>0`, set

`A(ε)=max(max(4,exp(20/ε)),200/ε)`,

`Z(ε)=max(max(A(ε/2)+1,6/(πε)+3),8)`.

For every `T≥Z(ε)`, the symmetric ξ-zero mass satisfies

`|M(T)−T log(T)/π|≤εT log(T)`.

For Hausdorff order `k`, put `K=10(k+1)+20` and

`H=max(Z(1/500),max(500,42(k+1)+44K))`.

Every shift `r≥ceil(20K)+ceil(KH²)+1` has nonnegative
endpoint-calibrated Hausdorff difference. All constants are explicit; no
threshold is selected from a convergence theorem.

## Proof

1. The existing Jensen bound for the real trace of ζ has central modulus at
   least `2−π²/6≥1/4` and boundary modulus at most `12T` for `T≥4`.
   Thus its logarithmic numerator is at most `4log T`.
   Since `log(7/6)≥1/7`, its divisor mass is at most `28log T`.
   The sign-change argument gives horizontal ζ argument at most `29πlog T`.
   Adding the elementary ξ factors gives horizontal ξ argument at most
   `100log T`.
2. On `0≤t≤2`, shift ψ from `1+it` to `2+it`. The existing modulus estimate
   `|ψ(z)−log z|≤3/|z|`, with `2≤|2+it|≤3`, gives
   `|Re ψ(1+it)|≤5`. Hence `|Φ₁(2)|≤10` and the Stirling remainder at `2`
   is at most `12`. Its derivative is at most `8/t²≤2` for `t≥2`.
   Consequently `|Φ₁(t)−(t log t−t)|≤6t` for `t≥2`.
   The exact vertical ξ decomposition and its two bounds by π imply
   `|V(T)−T log(T)/2|≤10T` for `T≥4`.
3. The quarter-contour identity and `2/π≤1` give
   `|M(T)−T log(T)/π|≤10T+100log T` at admissible heights.
   The two defining inequalities for `A(ε)` bound these terms separately by
   `εT log(T)/2`. Monotonicity and admissible heights in `(T−1,T)` and
   `(T,T+1)` transfer error `ε/2` to error `ε` at `Z(ε)`, using the existing
   bounds for `(T±1)log(T±1)`.
4. Substitute `Z(1/500)` in the existing Hausdorff band proof. The endpoint
   radius satisfies `0<R<1`, so `ceil(KH²)` dominates the required
   `ceil(KRH²)`. The original atom and band-count inequalities then apply.

Jensen horizons and two-grid degrees are separate unresolved A18 obligations.
