# The centered Möbius Schur boundary has a canonical weighted-Mertens limit

- **ID:** `mobius-schur-centered-boundary-limit-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [SEARCH] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** the classical zero-free line for zeta, reciprocal-zeta bounds on `Re s>=1`,
  and the Paley--Wiener theorem for the Laplace transform
- **Statement:** The centered boundary difference quotient of the signed Möbius Schur transfer has
  a strong `H2` limit at the critical source. Its inverse Laplace vector is the weighted Mertens
  function `sum_(n<=e^t)mu(n)/n`, which belongs unconditionally to `L2(0,infinity)`. Hence the
  constant-channel graph-domain problem is solved on the Euler boundary; only the subsequent
  orbit-sensitive contour transfer remains RH-bearing.

## 1. Centered Schur boundary vector

Use

```text
sigma=1+2omega,
Z_omega=zeta(sigma)/zeta(2sigma),
c_omega=1/(1+omega),                                    (1)
```

and the signed Schur multiplier

```text
tau_omega(z)=1/(Z_omega zeta(sigma+z)).                  (2)
```

The centered term in `mobius-signed-coisometry-schur-transfer-law.md` becomes, after restoring the
unnormalized arithmetic coefficient,

```text
G_omega(z)
 :=Z_omega c_omega
    (tau_omega(z)-tau_omega(0))/z

 =c_omega/z
    (1/zeta(1+2omega+z)-1/zeta(1+2omega)).               (3)
```

The apparent singularity at `z=0` is removable.

## 2. Critical Hardy limit

Define

```text
G_0(z)=1/(z zeta(1+z)),                                   (4)
```

with its removable value `G_0(0)=1`. Then

```text
G_omega ->G_0 in H2(Re z>0)                              (5)
```

as `omega` decreases to zero. Equivalently, their boundary values converge in `L2(R)`.

### Proof

For every fixed `z` with `Re z>0`, `(3)` converges to `(4)` because

```text
1/zeta(1+2omega)->0,
c_omega->1.                                              (6)
```

It remains to dominate the boundary values. Choose a fixed small `r>0`. Since `1/zeta(s)` is
holomorphic near `s=1` with a simple zero there, its derivative is bounded on a closed disk about
`1`. Hence, uniformly for small `omega` and `|t|<=r`,

```text
|1/zeta(1+2omega+it)-1/zeta(1+2omega)|<=C|t|,            (7)
```

so

```text
|G_omega(it)|<=C.                                        (8)
```

For `|t|>=r`, the classical reciprocal-zeta estimate on the zero-free line gives, uniformly for
`sigma>=1`,

```text
|1/zeta(sigma+it)|<=C log(2+|t|).                        (9)
```

The real value `1/zeta(1+2omega)` is bounded, so

```text
|G_omega(it)|
 <=C log(2+|t|)/|t|.                                     (10)
```

The square of the right side is integrable on `|t|>=r`. Equations `(8)`--`(10)` and dominated
convergence prove boundary `L2` convergence. Paley--Wiener identifies this with `(5)`.

No zero-density or RH input is used; the zero-free line `Re s=1` suffices.

## 3. Time-domain identification

For `Re z>0`, absolute convergence gives

```text
G_0(z)
 =1/z sum_(n>=1)mu(n)n^(-1-z).                           (11)
```

Since

```text
e^(-z log n)/z
 =integral_(log n)^infinity e^(-zt)dt,                   (12)
```

the inverse Laplace vector is

```text
m_0(t)=sum_(n<=e^t)mu(n)/n.                              (13)
```

Equation `(5)` therefore proves unconditionally

```text
m_0 in L2(0,infinity),                                   (14)

integral_0^infinity |sum_(n<=e^t)mu(n)/n|^2dt
 =1/(2pi) integral_R
    |1/(it zeta(1+it))|^2dt
 <infinity,                                              (15)
```

where the value at `t=0` on the Fourier side is interpreted removably.

The prelimit inverse vector can be written directly as

```text
m_omega(t)
 =c_omega(
    sum_(n<=e^t)mu(n)n^(-1-2omega)
    -1/zeta(1+2omega)
  )                                                       (16)
```

after choosing the equivalent lower-tail representative. Equation `(5)` says

```text
m_omega->m_0 in L2(0,infinity).                          (17)
```

## 4. Positive continuation consequence

The signed-channel boundary decomposition is

```text
F_omega
 =Z_omega T_omega k_omega+m_omega.                       (18)
```

Equation `(17)` closes the graph-domain problem for the centered constant channel. The critical
boundary vector is not an unspecified distribution and does not require RH to belong to `L2`; it
is the canonical weighted-Mertens vector `(13)`.

Thus the remaining source theorem has the sharper form

```text
weighted-Mertens boundary vector m_0
  + the renormalized floor-remainder channel
  -> orbit-sensitive cross-line continuation
  -> pole-to-divisor energy at most four.                 (19)
```

Any route that continues to treat the constant-channel domain as the main obstruction is now
overstating the open problem. The unsolved operation is the contour shift through the possible
zeta-zero poles and the resulting residue covariance.

## 5. Boundary and attacks

1. Equation `(14)` is a causal Euler-line statement. It does not say that the anti-causal
   contour-jump profile has finite energy.
2. Strong `L2` convergence in `(17)` does not commute with meromorphic contour translation across
   poles.
3. Multiplication by a symmetric orbit polynomial leaves `(13)` unchanged while changing the
   residue seam. The continuation must therefore retain the pointed source--divisor marking.
4. The remaining floor-remainder term in `(18)` still needs its own critical graph-limit theorem;
   no claim about that term is made here.

## 6. Scientific classification and Lean decision

The proof is classical reciprocal-zeta boundary analysis and Laplace inversion. It is a useful
route reduction but not new scientific knowledge.

The Lean tree does not contain the analytic reciprocal-zeta estimate `(9)`, the Laplace Hardy
space, or the weighted-Mertens `L2` interface. Formalizing only the Dirichlet-series identity
`(11)` would not certify strong convergence `(5)`, so no Lean file is added.

## Gates

- [x] centered Schur quotient defined
- [x] uniform local removable bound proved
- [x] reciprocal-zeta tail majorant proved
- [x] strong Hardy convergence proved
- [x] weighted-Mertens inverse vector identified
- [x] constant-channel graph-domain membership solved
- [ ] critical graph limit of the floor-remainder term
- [ ] orbit-sensitive contour continuation
- [ ] four-unit boundary energy
- [ ] RH
