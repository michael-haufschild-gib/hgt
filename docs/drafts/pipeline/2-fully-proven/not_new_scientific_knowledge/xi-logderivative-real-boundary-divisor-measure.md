# The Xi logarithmic derivative has a canonical positive real-boundary divisor measure

- **ID:** `xi-logderivative-real-boundary-divisor-measure`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Route-A boundary construction
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** the theta-source entire function `XiC` and the distributional boundary value of a
  meromorphic logarithmic derivative
- **Statement:** The upper boundary value of `-Im(XiC'/XiC)/pi` converges locally as a distribution
  to the positive atomic measure on the real Xi zeros, with each atom weighted by its analytic
  multiplicity.  Nonreal conjugate zero pairs contribute no boundary atom.

## General boundary identity

Let `F` be a nonzero entire function satisfying

```text
F(conj(z))=conj(F(z)).                                  (1)
```

Its zeros are locally finite and stable under conjugation.  Near a real zero `gamma` of
multiplicity `m_gamma`,

```text
F'(z)/F(z)=m_gamma/(z-gamma)+h_gamma(z),                (2)
```

where `h_gamma` is holomorphic and real on the real axis near `gamma`.

For `epsilon>0`, define locally away from horizontal zero hits

```text
d nu_epsilon(t)
  =-(1/pi) Im(F'(t+i epsilon)/F(t+i epsilon)) dt.        (3)
```

The singular term in (2) gives

```text
-(1/pi) Im(m_gamma/(t-gamma+i epsilon))
  =(m_gamma/pi)
    epsilon/((t-gamma)^2+epsilon^2).                    (4)
```

The right side is the Poisson approximation to `m_gamma delta_gamma`.  The holomorphic remainder
has imaginary part tending locally uniformly to zero on the real axis.

A nonreal pair `rho,conj(rho)` contributes

```text
1/(t-rho)+1/(t-conj(rho))
```

in the boundary limit.  This is real for real `t`, so its contribution to (3) tends to zero.
Applying this on each compact set, which meets only finitely many zeros, proves the local
distributional convergence

```text
nu_epsilon
  -> sum_(gamma in R, F(gamma)=0)
       m_gamma delta_gamma.                             (5)
```

Equivalently, (5) is the jump of `F'/F` across the real axis.

## Xi specialization

Take

```text
F=XiC,
XiC(z)=xi(1/2+i z).
```

`XiC` is entire and real on the real axis, so (1) holds.  Equation (5) gives the canonical positive
real-boundary divisor measure

```text
nu_Xi
  =sum_(gamma in R, XiC(gamma)=0)
      ord_gamma(XiC) delta_gamma.                       (6)
```

Definition (3) uses only the theta-source function and its logarithmic derivative; it does not list
or assume the locations of the zeros.  Formula (6) is the resulting boundary theorem.

## Positive semisimple Hilbert space

On finitely supported real-zero data define

```text
||c||_Xi^2
  =integral |c(t)|^2 d nu_Xi(t)
  =sum_gamma m_gamma |c_gamma|^2.                       (7)
```

Its completion is positive.  Real translation acts on the atom at `gamma` by
`exp(-i a gamma)`, so it is unitary.  Multiplicity is retained as the positive atom weight while
nilpotent local jets are not inserted into the Hilbert space.

Thus (6)--(7) construct, unconditionally, the positive semisimple defect carried by the real part of
the Xi divisor.

## Exact limitation

The analytic divisor current contains every complex zero, whereas (6) contains only real zeros.
A nonreal conjugate pair is visible in the meromorphic function `XiC'/XiC` but has no jump across
the real axis.  Therefore the assertion

```text
analytic Xi defect is exhausted by nu_Xi                           (8)
```

is equivalent to all Xi zeros being real, namely RH.

The theorem constructs the target positive boundary object but does not prove (8).

## Gates

- [x] multiplicity-safe Poisson boundary identity proved
- [x] nonreal conjugate-pair cancellation proved
- [x] Xi positive real-boundary measure constructed without zero input
- [x] positive semisimple Hilbert completion and unitary action constructed
- [ ] analytic-to-real exhaustion remains the RH-bearing theorem
