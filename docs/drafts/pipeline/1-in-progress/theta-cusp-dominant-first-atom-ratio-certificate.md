# Theta-cusp dominant first-atom ratio certificate

- **ID:** `theta-cusp-dominant-first-atom-ratio-certificate`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Scientific status:** `[CONJECTURE]`
- **Statement:** The `n=1` theta-cusp atom has enough explicit ratio margin, and the `n>=2`
  atom tail is small enough, to prove the two quadratic source inequalities forcing the first
  nonconstant prime--Gamma Hankel block.

## Goal

Prove the first genuinely nonconstant slice of the countable prime--Gamma source Hankel cone from
the explicit theta source, without Xi zero locations, real-rootedness, a limiting positive measure,
or an RH-equivalent sign assumption.

## Source decomposition

For

\[
m_j=2\int_0^\infty x^{2j}\thetaCuspFullSource(x)\,dx,
\]

write

\[
m_j=a_j+r_j,
\]

where `a_j` is the contribution of `thetaCuspSourceTerm x 1` and `r_j` is the sum of all terms
with `n>=2`.  Every atom is positive on `x>0`, hence `a_j,r_j>=0`.

Under the substitution `t=n^2e^{2x}`, the contribution of the `n`th atom is

\[
a_{j,n}=
2\pi\,4^{-j}n^{-1/2}
\int_{n^2}^{\infty}
  \left(\log\frac{t}{n^2}\right)^{2j}
  \left(2\pi t^{5/4}-3t^{1/4}\right)e^{-\pi t}\,dt.       \tag{1}
\]

The integrand is positive for `n>=1`.  For `n=1`, `(1)` is a finite combination of even
parameter derivatives of

\[
I(s)=\pi^{-s-1}\Gamma(s+1,\pi).
\]

For `n>=2`, the lower endpoint `t>=n^2` exposes the factor `e^{-\pi n^2}` and gives a rapidly
summable explicit tail majorant.

## Target certificate

Prove rational bounds `R_0,R_2>=0` such that

\[
r_0\le R_0,\qquad r_2\le R_2,                            \tag{2}
\]

together with the two finite first-atom inequalities

\[
14(a_2+R_2)^2\le9a_1a_3,                                \tag{3}
\]

and

\[
16(a_0+R_0)(a_2+R_2)\le45a_1^2.                         \tag{4}
\]

Then positivity of all tail moments gives

\[
14m_2^2\le9m_1m_3,
\qquad
16m_0m_2\le45m_1^2.
\]

The formal two-ratio gate therefore yields every linear-polynomial source Hankel inequality.

## Numerical pre-certification

High-precision quadrature gives

```text
                         a_0                    a_1
n=1      4.969490382416646e-1     2.297141874217970e-2
n=2      1.717398877415948e-4     5.255729295068555e-7

                         a_2                    a_3
n=1      2.962841018448894e-3     5.992957351379432e-4
n=2      7.415238622609523e-9     2.114596358483180e-10
```

The `n>=3` contributions are already below `6e-11` at level zero and decay faster at the higher
levels.  The full-source ratios are

\[
\frac{m_1m_3}{m_2^2}\approx1.56826779548>\frac{14}{9},
\qquad
\frac{m_0m_2}{m_1^2}\approx2.79110285817<\frac{45}{16}.
\]

These computations select the constants and certify feasibility; they are not the proof.

## Positive chain

```text
explicit incomplete-Gamma bounds for the n=1 atom
  + explicit e^(-pi*n^2) bounds for the n>=2 tail
  -> two theta-cusp quadratic ratio inequalities
  -> first nonconstant theta-cumulant Hankel determinant
  -> all real linear-polynomial prime--Gamma source tests are nonnegative.
```

## Gates

- [x] source-pure atom decomposition identified
- [x] exact incomplete-Gamma integral representation derived
- [x] viable rational ratio window identified numerically
- [ ] prove the sum-integral atom decomposition
- [ ] prove explicit rational enclosures for `a_0,a_1,a_2,a_3`
- [ ] prove explicit tail bounds `(2)`
- [ ] prove inequalities `(3)` and `(4)`
- [ ] formalize the complete first-atom certificate in Lean
- [ ] extend the dominant-atom mechanism beyond the first Hankel block
