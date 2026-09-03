# Prime--Hodge singular-gauge Riesz charge

- **ID:** ULF-PHSGRC-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor fusion and joint-reconstruction theorem
- **Parent:** ULF-PHSTH-001
- **Lean core:** `RHTower.PrimeHodgeHistoryIntegralNuclearHomotopyDefect`,
  `RHTower.PrimeHodgeHistoryFirstExitTransgression`,
  `RHTower.PrimeHodgeHistorySurvivalFredholmColligation`
- **Status:** `[PAPER-PROVED] [LEAN CORE PROVED] [BRIDGE] [NOT RH SELECTION]`

## 1. Higher-law interpretation

The object nobody asked for is not a zero operator, divisor ledger, or post-divisor projection.
It is the **Riesz charge of the singular similarity between pure open history and arithmetic
survival**. One object simultaneously carries:

```text
additive theta curvature -> multiplicative survival -> first-exit flux
                         -> prime-mixed Stokes packet -> integral nuclear charge.
```

Its integer is a boundary index; its nuclearity comes from singular metric regularization; its
all-prime matrix is formed before any trace; its signed wall parameter exists before any zero is
supplied.

## 2. Checked corpus locks

Required corpus searches were run for:

```text
Riesz decomposition excessive superharmonic potential harmonic operator
Martin boundary Poisson boundary Doob transform
Stein potential harmonic decomposition shift history
Q adjoint I minus C adjoint C Q singular gauge defect factorization
singular intertwiner Hilbert Schmidt gauge first exit defect Gramian
prime Hodge survival gauge Stein defect Q star Q
```

They show:

- the signed pre-divisor prime-mixed Schatten-one object and its integral trace are Lean-proved;
- relative curvature reconstructs its literal first-exit weights;
- the survival shift has Fredholm index `-1` and exact unit exit flux;
- the prime Stokes kernel preserves unsquared coefficients and every ordered cross-prime entry;
- the shift displacement and Toeplitz-horizon classification are paper-proved in ULF-PHSTH-001;
- Poisson/Martin-boundary naming does not provide the missing Xi boundary landing.

Abstract potential-plus-harmonic Riesz decomposition is classical; for example it appears for
weighted graph Schrödinger operators in <https://arxiv.org/abs/1905.12474>. No novelty is claimed
for that abstraction. Corpus-specific content is the exact theta-survival singular gauge, the
coefficient-faithful all-prime charge, and the conservation/reconstruction web below.

## 3. Construction

Let `H=ell2(Nat)`, `K=ell2(Primes)`, and

```text
U e_n=e_(n+1),
m_n=105/((2n+3)(2n+5)(2n+7)),
r_n=m_(n+1)/m_n=(2n+3)/(2n+9),
w_n=m_n-m_(n+1),
C e_n=sqrt(r_n)e_(n+1),
Q e_n=sqrt(m_n)e_n,
D=I-C* C.
```

For `d>0`, let `A_d` be the normalized positive prime Stokes operator whose kernel is
`normalizedStokesPrimeKernel d`. It has trace one, preserves every ordered cross-prime entry, and
uses unsquared Euler coefficients. Put

```text
Phi=Q D Q,
G_d=Q^2 tensor A_d,
T_d=Phi tensor A_d.                                      (SGRC.1)
```

For a signed wall parameter `t`, define

```text
T(t)=0                                      if t=0,
T(t)=sign(t) T_|t|                         if t!=0.       (SGRC.2)
```

This is exactly Lean's `primeHodgeHistoryIntegralNuclearHomotopyDefect t`.

## 4. Singular-gauge factorization

**Theorem SGRC-A.** On `H`,

```text
C Q=Q U,
Phi=Q(I-C*C)Q=Q^2-U*Q^2U=diag(w_n).                     (SGRC.3)
```

Hence on `H tensor K`, with `mathcal U=U tensor I_K`,

```text
T_d=G_d-mathcal U*G_d mathcal U.                         (SGRC.4)
```

**Proof.** On `e_n`, `CQ` has coefficient `sqrt(m_n r_n)=sqrt(m_(n+1))`, proving the
intertwining. Also `C*C e_n=r_n e_n`; therefore

```text
Q(I-C*C)Q e_n=m_n(1-r_n)e_n=(m_n-m_(n+1))e_n=w_n e_n.
```

The last expression is also `(Q^2-U*Q^2U)e_n`. Tensoring with `A_d` proves `(SGRC.4)`. QED.

The unsandwiched metric defect `D` has diagonal `6/(2n+9)` and is not trace class. The compact
singular gauge has `Tr(Q^2)=sum_n m_n=7/4`; its sandwich converts the non-nuclear local anomaly
into the nuclear unit charge `Phi`, because `sum_n w_n=1`.

## 5. Integral--nuclear and prime-mixed laws

**Theorem SGRC-B.** For `t!=0`,

```text
T(t) is Schatten-one,
Tr T(t)=sign(t),
||T(t)||_1=1,
T(-t)=-T(t).                                             (SGRC.5)
```

Every same-history entry indexed by ordered primes `(p,q)` is nonzero. Its diagonal is exactly
theta's Mellin-six boundary flux times the unsquared transported prime density. No divisor, zero,
ordinate, or RH premise occurs.

**Proof.** This is the closed Lean theorem
`primeHodgeHistoryIntegralNuclearHomotopyDefect_closed`, together with
`primeHodgeHistoryIntegralNuclearHomotopyDefectKernel_diagonal_eq_thetaFlux`. QED.

## 6. Joint reconstruction

Let `Tr_H` and `Tr_K` denote positive partial traces. Then

```text
Tr_H(T_d)=A_d,                    because sum_n w_n=1;    (SGRC.6)
Tr_K(T_d)=diag(w_n),              because Tr(A_d)=1.      (SGRC.7)
```

Moreover the Riesz potential of `T_d` under the pure history shift is

```text
P_U(T_d)=sum_(j>=0) mathcal U*^j T_d mathcal U^j
        =G_d                                                   (SGRC.8)
```

in trace norm. Consequently one operator reconstructs both organs:

```text
prime formation: A_d=Tr_H(T_d),
theta history:   m_n=Tr_K((G_d)_(n,n)),
survival:        r_n=m_(n+1)/m_n,
curvature/exit:  w_n=m_n-m_(n+1).                         (SGRC.9)
```

**Proof.** Positive partial trace commutes with the diagonal tensor decomposition, proving
`(SGRC.6-7)`. Grade `n` of the series in `(SGRC.8)` is
`sum_(j>=0) w_(n+j) A_d=m_n A_d`. Its trace norms sum to
`(sum_j m_j)Tr(A_d)=7/4`, so convergence is trace-norm. Taking the prime partial trace gives
`m_n`; the last two formulas are definitions already reconstructed from relative curvature in
`PrimeHodgeHistoryFirstExitTransgression`. QED.

## 7. Exact conservation web

For positive aperture,

```text
-index(C)
= total first-exit flux
= theta Hodge flux
= Tr(T_d)
= ||T_d||_1
= 1.                                                        (SGRC.10)
```

The first four equalities are Lean-proved by
`primeHodgeHistory_index_exitFlux_integralNuclear_conservation`; positivity supplies the trace
norm equality. Thus integrality, topology, theta formation, and nuclear analysis are readings of
one pre-divisor charge rather than independent coincidences.

## 8. Hostile boundary: what this does not prove

`T_d` uniquely reconstructs its finite-trace potential `G_d`; every other bounded solution of
the same Stein equation is `G_d+R` with shift-harmonic Toeplitz `R`. Finite trace kills `R`.

This does **not** prove that a strict-right completed Xi horizon is such an `R`. Corpus formation
instead gives its finite first-exit lift. Identifying the Xi relation horizon with the harmonic
part of this same pre-divisor Riesz decomposition would be exactly the missing boundary-operation
theorem. It must be derived from literal completion, not selected to manufacture divergence.

## 9. Formal status

Lean already closes the construction, signed symmetry, Schatten-one property, integral trace,
unit trace norm, all-cross-prime nonvanishing, theta diagonal, curvature-to-first-exit identity,
Fredholm index, and four-organ conservation. `(SGRC.3-9)` are dependency-closed paper consequences
of those modules and ULF-PHSTH-001; they are queued for a later Lean formalization pass.
