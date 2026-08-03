# Reflected-Gaussian two-sided prime--Gamma Cauchy landing

- **ID:** `deninger-meyer-reflected-gaussian-prime-gamma-cauchy-landing`
- **Stage:** 3-formalized
- **Type:** SOURCE CONSTRUCTION / NONLOCAL RANGE LANDING
- **Status:** `[LOCAL-RESEARCH] [PAPER PROVED] [LEAN FORMALIZED]`
- **Parents:**
  `deninger-meyer-gaussian-green-resolvent.md`,
  `ccm-four-unit-source-codiagonal-attack.md`
- **Publication context:**
  `../4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`
- **Intended Lean module:**
  `../../../../formal/GaloisForLFunctions/RHTower/DeningerMeyerReflectedGaussianPrimeGammaCauchyLanding.lean`

## 1. Exact source object

Put

```text
tau = 1/(4*pi),
g_tau(z) = exp(-tau*z^2),
b = 1.
```

Every centered Xi spectral point `lambda_q` lies in `|Im lambda_q| < 1/2`; therefore the two
horizontal lines `z=x-i` and `z=x+i` lie strictly in the lower and upper absolute-Euler
prime--Gamma Cauchy sectors.  Define the two-sided nonlocal boundary source

```text
B_tau(x)(a)
  = (2*pi*i)^(-1)
      [ g_tau(x+i)  /(a-(x+i))
        - g_tau(x-i)/(a-(x-i)) ].                       (1)
```

The variable `a` has not been restricted to the Xi divisor in this definition.  Both summands are
literal prime--Gamma Cauchy atoms with source-defined Gaussian boundary coefficients.

## 2. Frozen conjecture

The Bochner integral of `(1)` exists in the multiplicity-exact Xi Hilbert carrier and satisfies

```text
integral_R B_tau(x) dx = reflectedGaussianHorizonGradeL2. (2)
```

Equivalently, for every divisor copy `q`,

```text
(2*pi*i)^(-1) *
  [ integral_R g_tau(x+i)  /(lambda_q-(x+i)) dx
    - integral_R g_tau(x-i)/(lambda_q-(x-i)) dx ]
  = exp(-tau*lambda_q^2).                                (3)
```

The right side is already proved equal to the Mellin value of the fixed Paugam-reflection-invariant
Meyer Gaussian.  Thus `(2)` is an unconditional source-to-Xi landing theorem and an explicit
nonlocal completion of the finite prime--Gamma packet source.  It is not a divisor-indexed weight,
a pulled-back norm, or a post-divisor interpolation.

## 3. Dependency-closed paper proof

Fix `a` with `|Im a|<1/2`.  Apply Cauchy's integral formula to `g_tau(z)/(z-a)` on the rectangle
with vertices `+-R+-i`.  Since

```text
|g_tau(x+iy)| = exp(-tau*(x^2-y^2)),
```

the two vertical edges tend to zero as `R -> infinity`.  The horizontal edges converge absolutely.
After respecting their opposite orientations,

```text
g_tau(a)
  = (2*pi*i)^(-1)
      [ integral_R g_tau(x+i)/(a-(x+i)) dx
        - integral_R g_tau(x-i)/(a-(x-i)) dx ],
```

which is `(3)`.

It remains to justify the vector-valued integral without smuggling divisor topology into the
source.  Let `delta=b-1/2=1/2` and `S=sum_q |lambda_q|^(-2)<infinity`, already proved from the Xi
Hadamard divisor.  For `z=x+-i`, split copies according to `|lambda_q|>=2|z|`.  On the outer part,

```text
|lambda_q-z|^(-2) <= 4 |lambda_q|^(-2).
```

On the inner part, vertical separation gives `|lambda_q-z|>=delta`, while
`1 <= 4|z|^2/|lambda_q|^2`; hence

```text
|lambda_q-z|^(-2)
  <= 4 delta^(-2)|z|^2 |lambda_q|^(-2).
```

Therefore the complete Cauchy column obeys the explicit source-line bound

```text
||C_z||_ell2 <= 2 sqrt(S) max(1,|z|/delta).              (4)
```

The Gaussian coefficient on either boundary has norm `exp(tau)*exp(-tau*x^2)`.  Equations `(4)`
and Gaussian first-moment integrability prove Bochner integrability of `(1)`.  Continuous
coordinate evaluation commutes with the integral, and `(3)` then proves `(2)` by extensionality.

## 4. Formal theorem

`DeningerMeyerReflectedGaussianPrimeGammaCauchyLanding.lean` constructs both regular source lines,
proves scalar integrability and the two-line rectangle limit, derives a complete-divisor Cauchy
column bound from the unconditional reciprocal-square Xi mass, proves norm continuity and Bochner
integrability of the vector boundary, and establishes

```text
integral_reflectedGaussianPrimeGammaCauchyBoundary_eq_horizonGradeL2
```

without additional assumptions.

## 5. Scientific consequence and remaining frontier

This closes two forced arrows exposed by the compact-source range wall:

```text
finite prime--Gamma packets
  -> explicit two-sided Gaussian Cauchy L1 completion
  -> reflected-Gaussian Xi-divisor vector.
```

It does not prove RH.  First remaining arithmetic theorem is no longer existence of a nonlocal
source primitive or source-to-divisor landing.  It is exact compatibility of this two-sided
prime--Gamma boundary source with the closed adaptive Möbius--theta prime-normal range, preserving
the resolved Green antidiagonal and the one-corner four-unit energy.

## 6. Anti-theatre audit

- Cauchy's formula itself is classical infrastructure; novelty claimed is the exact placement of
  the fixed reflected Meyer grade in the completed two-sided *absolute-Euler prime--Gamma source
  range*, with a global Xi-Hilbert Bochner bound.
- No zero is selected, normalized, or interpolated.
- No RH premise, positivity premise, divisor weight, or target norm pullback occurs.
- Existing corpus proves finite Cauchy packets land in Xi `ell^2`, and separately that the reflected
  Gaussian grade lies in Xi `ell^2`; it does not identify the latter as one explicit completed
  prime--Gamma boundary packet.
