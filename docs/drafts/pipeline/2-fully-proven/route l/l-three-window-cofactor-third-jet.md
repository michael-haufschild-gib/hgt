# Route L: three-window third-jet extraction of a literal Möbius sector

- **ID:** L-THREE-WINDOW-COFACTOR-THIRD-JET
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM
- **Source:** The corpus's unconditional every-base theta-mass and odd-squarefree harmonic theorems, applied to the literal cubic Gamma–Hankel source
- **Lean status:** The arithmetic supply and cubic source identity are closed in Lean. Both constant- and variable-weight literal `0/1` floor selectors, their prefix discrepancies, weighted monotone-moment bounds, and exact integer-total count are closed in [MobiusOrderedMomentRounding.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusOrderedMomentRounding.lean). The simplex-interior selector, prime-window assembly, and Hilbert estimates below remain paper-level.

## Theorem

Let `f_x(t)=x² exp(-xt)` and use the normalized cubic Gamma norm

```text
||F||_delta² = Gamma(5+delta)^(-1) integral_(0,infinity) t^(4+delta)|F(t)|² dt,
0 <= delta <= 1.
```

For every sufficiently large real `R`, there are disjoint finite sets `A_R,B_R` of positive integers in `[2R,4R)` such that:

1. Every `a in A_R` has the unique form `2qr` with `q` odd squarefree, `q<=floor(R^(2/5))`, and `r` prime exceeding `R/q`. Every `b in B_R` has the unique form `qp` with the same cofactor restriction and `p` prime exceeding `2R/q`.
2. `|A_R|=|B_R|>=cR` for an absolute `c>0`; `mu(a)=mu(q)` and `mu(b)=-mu(q)` for each selected cofactor packet.
3. If `P_R` denotes the sum of the selected atoms with their **literal** Möbius signs, then uniformly in `0<=delta<=1`,

```text
||P_R||_delta <= C [R^(-1/10-delta/2)
                     + R^(-137/500-delta/2)
                     + R^(-11/500-delta/2)/log R].          (1)
```

Consequently `sum_j sup_(0<=delta<=1) ||P_(2^j)||_delta < infinity`. Removing these disjoint packets from the finite cubic Möbius source along the dyadic cutoffs `N_J=2^(J+2)` changes its norm by a uniformly bounded amount. Thus Route L's bounded-return source condition is equivalent for the full source and the residual source. This does **not** prove that condition for the residual.

## Finite three-window moment selector

The geometric lemma behind the extraction is unconditional and uses no distributional assumption. Fix `t_1=1/4`, `t_2=1/2`, `t_3=3/4` and `v_0=(1/2,7/24)`. There is `epsilon_0>0` with this property: if each of six finite sets `A_i,B_i` has at least `m` points in `[t_i,t_i+epsilon_0]`, then one can select exactly `m` points from their union on each side so that

```text
|sum_(a selected) a - sum_(b selected) b| <= 10,
|sum_(a selected) a² - sum_(b selected) b²| <= 10.       (2)
```

Here points are counted as distinct labelled atoms, even if two real positions happen to coincide. In the application the positive and negative integer atoms are distinct by parity.

**Proof.** Shrink `epsilon_0` below `1/8`. Choose exactly `m` candidate points from each `A_i,B_i`. For each side `s` and window `i`, let `v_(s,i)` be the average of `(u,u²)` over its `m` candidates. The three nominal vertices `(t_i,t_i²)` are affinely independent: their affine determinant is `(t_2-t_1)(t_3-t_1)(t_3-t_2)=1/32`. Their barycenter is `v_0`, with all three barycentric coefficients `1/3`. The vertices `v_(s,i)` converge uniformly to their nominal values as `epsilon_0 -> 0`; continuity of the inverse affine matrix therefore lets us fix `epsilon_0` so that `v_0` has barycentric coefficients `lambda_(s,i) in [1/4,1/2]` for **every** permitted triple, independently on both sides.

Give every one of the `m` candidates in window `i` on side `s` the fractional weight `lambda_(s,i)`. Each side then has fractional cardinality exactly `m`, and its first two fractional moments are exactly `m*v_0`.

There is a direct **ordered rounding** with constant error. Sort the `m` candidate positions in each group as `u_1<=...<=u_m`, put `lambda=lambda_(s,i)`, and select index `j` precisely when

```text
floor(j*lambda)-floor((j-1)*lambda)=1.
```

This is a `0/1` coefficient because `0<=lambda<=1`. Its discrepancy on the first `k` entries is `D_k=floor(k*lambda)-k*lambda`, so `-1<D_k<=0`. For either increasing function `g(u)=u` or `g(u)=u²`, summation by parts yields

```text
sum_(j=1)^m (selected_j-lambda)*g(u_j)
  = D_m*g(u_m)+sum_(j=1)^(m-1) D_j*(g(u_j)-g(u_(j+1))).
```

The first term is in `[-1,0]`, the second in `[0,1]`, since `0<=g(u_j)<=1` and `g` is increasing. Hence the absolute moment error per group is at most `1`. The selected count in that group is `floor(m*lambda)`. Because the three `lambda` values on one side sum to `1`, their selected counts total `m-d_s` for an integer `d_s in {0,1,2}`. Add any `d_s` still-unused candidates on that side. This restores its cardinality to exactly `m` and costs at most `2` in either moment. Each side is therefore within `5` of its common fractional moment `m*v_0`; subtracting the sides gives (2). Every coefficient is literal `0` or `1`.

## Prime realization and norm bound

Put `alpha=71/100`, `Y=floor(R^(2/5))`, and fix the `epsilon_0` above. For every odd squarefree `q<=Y`, let

```text
H_q = q*(4R/q)^alpha = (4R)^alpha q^(1-alpha),
L_q = C_0 H_q,
J_q = floor(2R/L_q),
m_q = floor((R/q)^alpha/(32768 log(5R))),
```

where the fixed constant `C_0` is large enough that `H_q<=epsilon_0 L_q` and the three windows `[X_j+t_i L_q, X_j+(t_i+epsilon_0)L_q]` are disjoint and lie inside each full block `[X_j,X_j+L_q)`, `X_j=2R+jL_q`. Uniformly for `q<=R^(2/5)`, `L_q=O(R^(413/500))=o(R)`, `J_q asymp R/L_q`, and `m_q asymp (R/q)^alpha/log R`.

The closed corpus theorem `RHTower.Sieve.eventually_routeT_detectorPacking_theta_mass_every_base` gives, at every sufficiently large base `z`,

```text
theta(z+z^alpha/2)-theta(z) > z^alpha/16384.             (3)
```

Applied at each physical window start divided by `q` (for `qp`) and by `2q` (for `2qr`), (3) supplies at least `m_q` actual prime atoms of **each** sign in **each** of the three windows. The physical lengths of the theorem windows are at most `H_q/2` and `H_q`, respectively, so they fit in the chosen `epsilon_0 L_q` windows. All bases are at least `R/q>=R^(3/5)` and tend uniformly to infinity. Normalize each candidate's physical position `x` to `u=(x-X_j)/L_q` and apply the finite selector. It chooses exactly `m_q` literal atoms of each sign in the block, with physical first- and second-centered-moment discrepancies at most `10L_q` and `10L_q²`.

The Möbius signs are correct because every selected variable prime exceeds `R/q>q`, so it is coprime to `q`, while `q` is odd and squarefree. Within a fixed `q`, blocks are disjoint. Between distinct `q`, no atom repeats: its unique prime factor larger than `R^(3/5)` is `r` or `p`, and the remaining odd cofactor is `q`; parity separates `2qr` from `qp`.

For `x>=R`, direct differentiation and the change of variable `u=xt` in the Gamma integral give, uniformly for `0<=delta<=1`,

```text
||f'_x||_delta <= C R^(-(3+delta)/2),
||f''_x||_delta <= C R^(-(5+delta)/2),
||f'''_x||_delta <= C R^(-(7+delta)/2).                    (4)
```

Third-order Taylor expansion at each block's left endpoint, (2), and the triangle inequality give

```text
||P_(R,q)||_delta
 <= C J_q [L_q R^(-(3+delta)/2)
             + L_q² R^(-(5+delta)/2)
             + m_q L_q³ R^(-(7+delta)/2)]
 <= C [R^(-(1+delta)/2)
       + R^(alpha-3/2-delta/2) q^(1-alpha)
       + R^(3alpha-5/2-delta/2) q^(2-3alpha)/log R].      (5)
```

The selected count per `q` is `J_q m_q >= c R/(q log R)`. The closed corpus theorem `RHTower.Sieve.sum_inv_coprime_squarefree_ge` with `Q=2` yields

```text
sum_(q<=Y, q odd squarefree) 1/q >= (log Y)/8-7/8,
```

so the combined positive and negative selected counts are each at least `cR`. Summing (5) over `q<=Y`, using `sum_(q<=Y)q^(1-alpha)<=CY^(2-alpha)` and `sum_(q<=Y)q^(2-3alpha)<=CY^(3-3alpha)`, gives

```text
Y R^(-(1+delta)/2) = O(R^(-1/10-delta/2)),
R^(alpha-3/2-delta/2) Y^(2-alpha)
    = O(R^(-137/500-delta/2)),
R^(3alpha-5/2-delta/2)Y^(3-3alpha)/log R
    = O(R^(-11/500-delta/2)/log R).
```

This proves (1), and its dyadic sum converges. The source-reduction assertion follows by the norm triangle inequality, as in the [two-jet predecessor](../../3-formalized/route%20l/l-balanced-prime-semiprime-two-jet-extraction.md).

## Global rounding across a dyadic cofactor layer

Rounding separately for each cofactor incurs one bounded moment error per `q`, forcing the preceding elementary cofactor sum to stop below `R^(1/2)`. That loss is avoidable. For **varying** fractional weights `lambda_j in [0,1]` on atoms sorted by physical position, put `S_k=sum_(j<=k)lambda_j` and choose atom `j` when `floor(S_j)-floor(S_(j-1))=1`. The cumulative error is always `floor(S_k)-S_k in (-1,0]`. Summation by parts again gives error at most `1` against every nondecreasing weight in `[0,1]`. If `S_N` is an integer, the final selected count is exactly `S_N`. These statements are closed in Lean in the module cited above.

Fix an integer `d>=1` and `0<eta<1` with

```text
(d+1)*(1-alpha)*(1-eta) > 1/2,     alpha=71/100.       (6)
```

Partition admissible cofactors `q<=R^eta` into dyadic ranges `Q<=q<2Q`. Here *admissible* means `q` is odd squarefree and every prime factor of `q` is strictly below `R/q`. All odd squarefree `q<=R^beta`, for any fixed `0<beta<min(eta,1/2)`, are admissible, so their harmonic sum is `Omega(log R)` by the closed corpus theorem.

For one layer use a common physical block length `L_Q=C_d R^alpha Q^(1-alpha)` and `J_Q=floor(2R/L_Q)` blocks. Since `eta<1`, `L_Q=o(R)`. Choose `d+1` separated normalized windows inside each block. The uniform prime theta-mass theorem supplies `m_q=floor((R/q)^alpha/(32768 log(5R)))` actual atoms of each parity orientation in **each** window, for every cofactor in the layer. The Vandermonde simplex argument, applied separately to each actual Möbius sign and each `q`, assigns fractional weights in `(0,1)` whose mass is `m_q` and whose first `d` normalized moments are `m_q` times the same nominal barycenter. Möbius parity merely swaps which orientation belongs to which actual sign.

Pool **all** candidate atoms of one actual sign from **all** cofactors in the layer, sort them by normalized physical position, and use the varying-weight floor selector once. The fractional mass on each actual sign is the same integer `M_Q=sum_q m_q`, so the two selected counts are exactly `M_Q`, with no count repair. For each `1<=j<=d`, the signed `j`th centered moment differs by at most `2L_Q^j`. This bound is independent of the number of cofactors. Selected atoms from different cofactors cannot coincide: the variable prime exceeds every prime factor of its cofactor and hence is its unique largest prime; parity distinguishes the two orientations.

Direct differentiation gives

```text
partial_x^r f_x(t)
 = exp(-xt) [x²(-t)^r + 2r*x*(-t)^(r-1)
                + r(r-1)*(-t)^(r-2)],
||partial_x^r f_x||_delta <= C_r R^(-r-1/2-delta/2),    x>=R,
```

with negative powers omitted when `r<2`. The trivial upper bound `M_Q<=C R^alpha Q^(1-alpha)/log R <= C_d L_Q/log R` and Taylor expansion through order `d` show that the selected layer has norm at most

```text
C_d J_Q [sum_(j=1)^d L_Q^j R^(-j-1/2-delta/2)
            + M_Q L_Q^(d+1) R^(-d-3/2-delta/2)]
 <= C_d [R^(-1/2-delta/2)
       + R^(1/2-(d+1)*(1-alpha)*(1-eta)-delta/2)/log R].
```

There are `O(log R)` layers, so their union has norm

```text
O_d(R^(-1/2-delta/2) log R
   + R^(1/2-(d+1)*(1-alpha)*(1-eta)-delta/2)),         (7)
```

which is dyadically summable by (6). The selected count per sign is at least `c_(d,eta)R`: in each eligible layer `J_Q m_q >= c_d R/(q log R)`, and the admissible `q<=R^beta` give harmonic mass `Omega(log R)`. Thus **for every fixed `eta<1`**, choosing a sufficiently large fixed `d` yields a linear-density literal Möbius subpacket with summable cubic Gamma norm, including admissible cofactors far above `sqrt(R)`. For `d=3`, the threshold is `eta<33/58`.

## Remaining mathematical obstruction

This extraction reaches unique-largest-prime atoms with cofactors as large as `R^(1-epsilon)` for any fixed `epsilon>0`. It still selects only a controlled subpacket: in each cofactor packet the simplex weights select `m_q` atoms per sign from `(d+1)m_q` chosen candidates, so increasing `d` improves the allowable cofactor range while reducing the selected fraction. Other atoms of the treated sector and integers with no eligible largest-prime/cofactor split remain. The cutoff-uniform energy of the **residual** remains unproved. Global rounding removes cofactor-by-cofactor rounding as an obstacle; the next mathematical target is a source-derived law that controls the residual's signed covariance across all physical blocks.
