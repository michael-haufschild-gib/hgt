# Route L: balanced cofactor two-jet extraction

- **ID:** L-BALANCED-PRIME-SEMIPRIME-TWO-JET
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM
- **Source:** Literal cubic Gamma–Hankel atoms and the corpus's unconditional every-base theta-mass theorem
- **Lean status:** The arithmetic inputs `RHTower.Sieve.eventually_routeT_detectorPacking_theta_mass_every_base` and `RHTower.Sieve.sum_inv_coprime_squarefree_ge`, the cubic source identity, and the finite unit-coefficient first-moment selector `RHTower.exists_balanced_two_orientations` are closed in Lean. The prime-window assembly, analytic two-jet Hilbert bound, and cofactor summation remain paper-level.

## Theorem

Let `f_x(t)=x² exp(-xt)` and

```text
||F||_delta² = Gamma(5+delta)^(-1) integral_(0,infinity) t^(4+delta)|F(t)|² dt,
0 <= delta <= 1.
```

There are constants `c,C,R_0>0` such that for every real `R>=R_0` one can select disjoint sets

```text
A_R subset {2r : R<r<2R, r odd prime},
B_R subset {p : 2R<p<4R, p prime},
|A_R|=|B_R|,       |A_R| >= c R/log R,
P_R = sum_(a in A_R) f_a - sum_(b in B_R) f_b,
```

for which, uniformly in `0<=delta<=1`,

```text
||P_R||_delta <= C (R^(-(1+delta)/2)
                       + R^(-2/25-delta/2)/log R).             (1)
```

The coefficients of `P_R` are the **literal** Möbius values: `mu(2r)=+1` and `mu(p)=-1`. No repeated or fractional source coefficient is used. In particular `||P_R||_delta -> 0` uniformly in `delta`. For `R=2^j`, the packets have disjoint integer supports and

```text
sum_(j>=j_0) sup_(0<=delta<=1) ||P_(2^j)||_delta < infinity.  (2)
```

Hence, along cutoffs `N_J=2^(J+2)`, subtracting all completed `P_(2^j)` from the finite literal cubic Möbius source changes its Gamma–Hankel norm by a uniformly bounded amount. The cutoff-uniform Route L receiver holds for that source if and only if it holds for this residual source. This is a reduction, not an RH bound: covariance with the unselected remainder is still uncontrolled.

## Proof

Set `alpha=71/100` and `H=(4R)^alpha`, `L=8H`. The already proved closed Lean theorem
`RHTower.Sieve.eventually_routeT_detectorPacking_theta_mass_every_base` applies because
`701299/1000000 < alpha < 1`. For every sufficiently large real `z`,

```text
theta(z+z^alpha/2)-theta(z) > z^alpha/16384.              (3)
```

Since each contributing prime is at most `5R` in the windows below, (3) supplies at least
`z^alpha/(16384 log(5R))` primes in each such window. In particular, every required prime family has at least

```text
m=floor(R^alpha/(32768 log(5R)))
```

members for all large `R`, and `m >= c_0 H/log R` for an absolute `c_0>0`.

Partition the physical interval `[2R,4R)` into `J=floor(2R/L)` full blocks
`I_j=[X_j,X_j+L)`, `X_j=2R+jL`. Then `J` is between positive constant multiples of `R/H` for large `R`. Let `I_j^-=[X_j,X_j+L/4)` and `I_j^+=[X_j+3L/4,X_j+L)`. Apply (3) at the left endpoint of each of these quarters to obtain at least `m` primes `p` in each quarter. Apply it again at **half** each left endpoint to obtain at least `m` primes `r` whose doubled values `2r` lie in each quarter. Indeed the doubled theorem-window length is `(X/2)^alpha <= H`, whereas each physical quarter has length `2H`; the prime theorem-window length is `X^alpha/2 <= H/2`. All bases tend uniformly to infinity with `R`.

In each block choose `m` distinct doubled-prime atoms `a_i^-` in `I_j^-` and `m` distinct prime atoms `b_i^+` in `I_j^+`. They yield `m` negative displacement pairs `(a_i^-,b_i^+)` with `a_i^- - b_i^+ in [-L,-L/2]`. Likewise choose `m` prime atoms `b_i^-` in `I_j^-` and `m` doubled-prime atoms `a_i^+` in `I_j^+`; these yield `m` positive displacement pairs `(a_i^+,b_i^-)` with `a_i^+ - b_i^- in [L/2,L]`. The four atom families are disjoint: physical quarters are disjoint, primes are odd, and doubled odd primes are even.

Select all `m` pairs from the orientation with the smaller total absolute displacement. Add pairs from the other orientation in any fixed order until its running total first reaches or exceeds the smaller total. Every increment is between `0` and `L`, so the overshoot is at most `L`. This uses all `m` pairs of one orientation and at most `m` of the other. In particular the selected number `M_j` satisfies `m<=M_j<=2m` and

```text
|sum_(selected pairs in I_j) (a-b)| <= L.                  (4)
```

The finite overshoot statement is formalized in `MobiusBalancedTwoJetSelection.lean` as `exists_prefix_sum_between` and `exists_balanced_two_orientations`. The module is wired into `RHTower.lean` and passed `lake env lean` plus targeted `lake --old build GaloisForLFunctions.RHTower.MobiusBalancedTwoJetSelection`.

Summing over blocks gives `Jm<=|A_R|=|B_R|<=2Jm`; hence the cardinality claim.

The parameter derivatives of the source atom are

```text
f'_x(t)=(2x-x²t)exp(-xt),
f''_x(t)=(2-4xt+x²t²)exp(-xt).
```

Changing variables `u=xt` in the defining Gamma norm shows, uniformly for `0<=delta<=1` and `x>=R`,

```text
||f'_x||_delta <= C_1 R^(-(3+delta)/2),
||f''_x||_delta <= C_2 R^(-(5+delta)/2).                     (5)
```

The constants are uniform because the resulting polynomial–exponential Gamma integrals and `Gamma(5+delta)^(-1)` are continuous on the compact delta interval. Taylor's formula with integral remainder in this Hilbert space, expanded at the block's left endpoint `X_j`, gives for `a,b in I_j`

```text
||f_a-f_b-(a-b)f'_(X_j)||_delta
    <= C_2 L² R^(-(5+delta)/2).                             (6)
```

Using (4)–(6), then the triangle inequality over the `J` blocks,

```text
||P_R||_delta
 <= C J [L R^(-(3+delta)/2) + 2m L² R^(-(5+delta)/2)]
 <= C [R^(-(1+delta)/2)
         + R^(2alpha-3/2-delta/2)/log R].                    (7)
```

Since `2alpha-3/2=-2/25`, (7) is (1). Summing (1) at dyadic `R=2^j` proves (2). The physical supports `[2R,4R)` of successive dyadic packets are disjoint. Each packet consists of distinct literal Möbius atoms, so their cumulative sum is an actual subpacket of every sufficiently large finite source. The norm triangle inequality gives the equivalence with its residual source along the stated cutoffs.

## Cofactor amplification: a linear-density extraction

The preceding construction extends to every odd squarefree cofactor `q<=Y=floor(R^(1/10))` and yields a stronger result. There are disjoint literal Möbius subpackets `P_(R,q)` such that

```text
P_(R,q) = mu(q) [sum_(selected r) f_(2qr) - sum_(selected p) f_(qp)],
R<qr<2R,   2R<qp<4R,
|selected r|=|selected p| >= c R/(q log R),
||P_(R,q)||_delta
  <= C [R^(-(1+delta)/2)
        + R^(-2/25-delta/2) q^(-21/50)/log R].             (8)
```

For each `q`, partition the same physical shell `[2R,4R)` into blocks of length
`L_q=8q(4R/q)^alpha`, with `alpha=71/100`. The physical prime windows for `qp` and `2qr` have lengths at most `L_q/4`, by applying (3) respectively at bases `X/q` and `X/(2q)`. The previous four-family, opposite-orientation greedy selection therefore applies verbatim. Its window count is `J_q ≍ R/L_q` and its available prime count per family is `m_q ≍ (R/q)^alpha/log R`, uniformly for `q<=R^(1/10)`. The same Taylor argument gives

```text
||P_(R,q)||_delta
 <= C [J_q L_q R^(-(3+delta)/2)
        + J_q m_q L_q² R^(-(5+delta)/2)],
```

which simplifies to (8). The key cofactor exponent is `1-2alpha=-21/50`, **negative**: the smaller prime range reduces the count enough to offset the larger physical window. All prime variables exceed `R/q>=R^(9/10)>q`, so they are coprime to `q`. The Möbius coefficients are exactly `mu(2qr)=mu(q)` and `mu(qp)=-mu(q)`. Different cofactors cannot produce the same atom: each selected integer has exactly one prime factor larger than `R^(9/10)`, namely `r` or `p`, and its remaining odd squarefree cofactor is `q`; parity separates the two atom types.

Let `P_R^all=sum_(q<=Y, q odd squarefree) P_(R,q)`. The closed Lean theorem `RHTower.Sieve.sum_inv_coprime_squarefree_ge` with `Q=2` gives

```text
sum_(q<=Y, q odd squarefree) 1/q >= (log Y)/8 - 7/8.       (9)
```

Summing the selected-pair lower bounds and using `log Y=(log R)/10+o(1)` gives, for large `R`,

```text
number of selected positive Möbius atoms
  = number of selected negative Möbius atoms >= c_1 R.   (10)
```

Thus a positive proportion of all integers in `[2R,4R)` occurs in a balanced, source-compatible subpacket. For its Hilbert cost, summing (8) over at most `Y` cofactors and using `sum_(q<=Y) q^(-21/50) <= C Y^(29/50)` gives

```text
||P_R^all||_delta
 <= C [R^(-2/5-delta/2)
        + R^(-11/500-delta/2)/log R].                      (11)
```

The exponent `-11/500` is strictly negative, so the **linear-density** extraction has summable Gamma–Hankel norm over dyadic shells. The same disjoint-support and cofinal-cutoff argument following (2) applies to `P_R^all`. More generally, `Y=floor(R^eta)` works for every fixed `0<eta<4/29`, since the second exponent is `-2/25+(29/50)eta<0`; `eta=1/10` fixes explicit room.

## Mathematical consequence and boundary

The new ingredient is **two-jet balance**: every-base prime supply above exponent `0.701299` allows both dipole orientations in each block, and their first moments can be balanced with no coefficient outside `{+1,-1}`. The second-order cost is summable exactly when the supply exponent is below `3/4`; the corpus exponent `0.71` lies inside this aperture. Pairing only one orientation would cost `R^(alpha-1/2)/log R` and would not yield (1).

The cofactor extraction removes at least `cR` positive and `cR` negative actual Möbius atoms per dyadic shell with a summable norm correction. This is a genuine linear-density reduction of the full source. It does **not** control the residual Möbius source: the remaining atoms and their cross-covariance still carry the RH obstruction. The next mathematical target is an iterated, disjoint cofactor partition covering the remaining squarefree classes while preserving the summable two-jet cost, or a signed covariance estimate for that residual.

The immediate conjecture loop is to upgrade the block selector from one moment to two. A common physical block of width `L≈R^alpha Y^(1-alpha)` for all `q<=Y=R^eta` can pack `≈L/[q(R/q)^alpha]` disjoint prime-supply windows for each `q`; the summed available source count is `≫L`, by the odd-squarefree harmonic bound. A unit-coefficient selection of `≫L` atoms per common block with zeroth moment exactly zero, first moment `O(L)`, and second moment `O(L²)` would make the third-order Taylor remainder contribute `O(R^(3beta-5/2))` per dyadic shell, where `beta=alpha+eta*(1-alpha)`. With `alpha=0.71`, this would permit `eta<37/87≈0.425`, far beyond the present `eta<4/29≈0.138`. The corpus `prouhet_alternating_annihilation` gives exact polynomial moment cancellation at prescribed nodes; the hard new step is to realize enough such balanced configurations using the actual prime and doubled-prime positions while keeping literal unit coefficients. A single fixed-size Prouhet packet is insufficient, since its count per block would not be linear in `L`.
