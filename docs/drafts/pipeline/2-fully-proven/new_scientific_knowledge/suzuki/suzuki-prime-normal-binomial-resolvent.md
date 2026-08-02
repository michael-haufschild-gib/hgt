# The complete Suzuki prime normal flow is an exact binomial resolvent

- **ID:** `suzuki-prime-normal-binomial-resolvent`
- **Stage:** 2-fully-proven
- **Type:** EXACT OPERATOR SOLUTION / ALL-GRADE PRIME TRANSPORT
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Inputs:** `suzuki-support-pruned-selfadjoint-seam-carrier.md`,
  `suzuki-physical-log-grade-nuclear-summability.md`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes

## 1. Result

Let \(X\) be a complex Hilbert space and \(T=T^*\in\mathcal B(X)\).  The prime-only differentiated
physical boundary normal equation is

```text
(2L I-T)F'(L)+F(L)=0.                                   (1)
```

For every \(L>\|T\|/2\) and every half-log trace vector \(\beta\in X\), define

```text
F_beta(L)
 =L^(-1/2)(I-T/(2L))^(-1/2) beta
 =(L I-T/2)^(-1/2)beta.                                 (2)
```

Then:

1. \(F_\beta\) is the unique strong solution of `(1)` with

   ```text
   lim_(L->infinity) sqrt(L)F_beta(L)=beta;              (3)
   ```

2. its norm-convergent expansion is

   ```text
   F_beta(L)
    =sum_(k>=0)
      [binom(2k,k)/8^k]
      L^(-k-1/2) T^k beta;                              (4)
   ```

3. every length-\(k\) prime word is therefore present with universal coefficient

   ```text
   theta_k=binom(2k,k)/8^k;                              (5)
   ```

4. if \(T\) is Suzuki's convolution adjacency on an \(\ell^1\) valuation carrier and
   \(\|T\|_{\ell^1\to\ell^1}\le M_a\), then `(4)` converges absolutely in \(\ell^1\) whenever

   ```text
   L>M_a/2,                                              (6)
   ```

   and

   ```text
   ||F_beta(L)||_1
   <=L^(-1/2)(1-M_a/(2L))^(-1/2)||beta||_1.             (7)
   ```

Thus complete dense prime-seam breadth is exactly summable in one operator formula.  No finite
grade truncation, physical seam separation, or inverse-Fourier \(dr/r\) upgrade is needed for the
prime normal system.

For the source-faithful support-pruned carrier, take

```text
T=T_a^Gamma=-T_a.                                       (8)
```

The sign is load-bearing and agrees with the Gamma equation convention `scalar - T`.

## 2. Functional-calculus proof

For \(L>\|T\|/2\), the self-adjoint operator

```text
A_L=L I-T/2                                             (9)
```

has spectrum in \((0,\infty)\).  Continuous functional calculus defines
\(A_L^{-1/2}\).  Since every \(A_L\) is a function of the same operator \(T\), the family commutes,
and the spectral theorem permits differentiation pointwise in the spectral variable:

```text
d/dL A_L^(-1/2)=-(1/2)A_L^(-3/2).                       (10)
```

Therefore

```text
(2L I-T)F_beta'
 =2A_L[-(1/2)A_L^(-3/2)beta]
 =-A_L^(-1/2)beta
 =-F_beta.                                              (11)
```

This proves `(1)`.  Also

```text
sqrt(L)F_beta(L)
 =(I-T/(2L))^(-1/2)beta ->beta                          (12)
```

in norm, proving `(3)`.

If \(F\) is another strong solution with the same trace, apply the spectral theorem.  For almost
every spectral value \(t\), its component solves

```text
(2L-t)f_t'+f_t=0,
```

so \((L-t/2)^{1/2}f_t(L)\) is constant.  Trace `(3)` fixes that constant, hence \(F=F_\beta\).
`QED`

## 3. Exact all-grade expansion

For \(\|T\|/(2L)<1\), the scalar binomial series converges uniformly on the spectrum:

```text
(1-z)^(-1/2)
 =sum_(k>=0) binom(2k,k)z^k/4^k.                        (13)
```

Functional calculus and \(z=T/(2L)\) give `(4)`.  Its coefficients obey

```text
theta_(k+1)/theta_k=(2k+1)/(4k+4),                      (14)
theta_0=1.
```

This is exactly the Volterra grade recurrence

```text
alpha/(2alpha+1),       alpha=k+1/2,                    (15)
```

found independently from the trace-zero inverse formula.  In particular:

```text
theta_1=1/4,
theta_k>0,
theta_k<=2^(-k).                                        (16)
```

The equality of `(14)` and `(15)` is an internal normalization audit: the operator solution and
the local Volterra calculation fix the same first-seam coefficient.

## 4. Literal valuation word expansion

Let

```text
T=sum_s w_s U_s,       w_s>=0,       sum_s w_s=M_a,     (17)
```

where the \(U_s\) are Suzuki's oriented prime shifts.  Expanding \(T^k\) gives every length-\(k\)
word with product weight.  The coefficientwise absolute mass is \(M_a^k\).  Equations `(4)` and
`(5)` give total grade mass

```text
theta_k M_a^k<= (M_a/2)^k.                              (18)
```

Summing `(4)` in \(\ell^1\) yields:

```text
sum_(k>=0) theta_k (M_a/L)^k
 =(1-M_a/(2L))^(-1/2),                                  (19)
```

which proves `(6)`--`(7)`.

For a compressed self-adjoint adjacency \(PTP\), \(T^k\) counts exactly paths whose every
intermediate vertex survives the compression.  For the full adjacency it counts all exterior
excursions.  Compression and elimination must still not be confused: replacing the full system
by \(PTP\) omits the positive Feshbach return already classified in
`suzuki-exterior-feshbach-pruning-law.md`.

## 5. Physical \(L^2\) consequence

The grade-zero term is \(\beta L^{-1/2}\), the unique non-\(L^2(dL)\) prime-normal channel.  Every
descendant \(k\ge1\) is physical \(L^2\), and Section 4 of
`suzuki-physical-log-grade-nuclear-summability.md` gives

```text
sum_(k>=1,words)
 ||F_(k,word)||_(L2(dL))<infinity
```

on every tail \(L_0>M_a/2\).

If the matched half-log trace vanishes, \(\beta=0\), equation `(2)` gives \(F_\beta=0\): the
prime-only normal system has no hidden inverse-log-flat homogeneous state.  For the complete Gamma
normal equation, zero trace can retain the upper-strip glued homogeneous state, but it is already
\(L^2(dL)\) and is controlled by the exact Gamma scattering theorem.

## 6. Exact frontier movement

The difficult source components now separate:

```text
bounded self-adjoint prime breadth:
  exact all-grade solution (2), nuclear on L>M_a/2;      [CLOSED]

literal Gamma jump R:
  exact frequency propagator and zero-trace strip;       [CLOSED HOMOGENEOUSLY]

full completed Suzuki source:
  prove one physical normal carrier where prime binomial
  flow, Gamma jump, low counterterms, and exterior/Feshbach
  forcing satisfy the same cutoff equation.              [OPEN CONNECTOR]   (20)
```

Thus the open theorem is no longer “sum dense prime seams.”  Prime breadth has an exact resolvent.
It is the source-faithful **Duhamel coupling of this resolvent to the Gamma jump and corrected
exterior forcing**.

## 7. Hostile audit

1. **No commutation fiction with \(L\).**  Only \(T\) commutes with its own functional calculus;
   `(10)` differentiates a scalar spectral family.
2. **No Gamma deletion in the final route.**  This theorem is explicitly the prime normal block;
   \(R\) remains in open connector `(20)`.
3. **No pruning/inverse confusion.**  Feshbach return is retained when exterior coordinates are
   eliminated.
4. **No collision assumption.**  Powers \(T^k\) sum colliding words algebraically; the absolute
   bound counts all of them.
5. **No RH claim.**  Full source coupling and two-ended return remain open.

## 8. Lean certificate

`SuzukiVolterraLogGradeRecurrence.lean` formalizes:

```text
suzukiVolterraRaisedCoefficient;
suzukiVolterraRaisedCoefficient_recurrence;
suzukiVolterraRaisedCoefficient_ne_zero;
norm_suzukiVolterraRaisedCoefficient_le_half;
suzukiPrimeNormalGradeFactor;
suzukiPrimeNormalGradeFactor_pos;
suzukiPrimeNormalGradeFactor_le_half_pow.
```

This kernel-checks the exact all-grade recurrence, positivity, and uniform \(2^{-k}\) majorant.
Formalizing `(2)` itself requires the unbounded-in-parameter continuous functional calculus
derivative for \(A_L^{-1/2}\); the paper proof uses the spectral theorem directly.  An abstract
axiom for that derivative would be rejected.

## 9. Novelty boundary

Solutions of commuting operator ODEs and the central-binomial generating function are classical.
Candidate-new source knowledge is their exact identification with Suzuki's physical prime-seam
normal flow:

```text
all prime valuation grades
 = one positive binomial resolvent
 = exact coefficient theta_k
 = physical nuclear threshold M_a/2.                    (21)
```

No prior corpus card or targeted source search contained `(2)`--`(21)`.  Priority remains
unverified.

## Gates

- [x] solve prime-only vector normal equation exactly
- [x] prove uniqueness from half-log trace
- [x] derive norm-convergent central-binomial expansion
- [x] identify every valuation word and collision
- [x] prove \(\ell^1\) convergence at \(L>M_a/2\)
- [x] prove descendant nuclear physical \(L^2\)
- [x] formalize recurrence, positivity, and \(2^{-k}\) majorant in Lean
- [ ] couple exact prime resolvent to Gamma jump by a physical Duhamel theorem
- [ ] insert low-frequency counterterms and exterior/Feshbach source
- [ ] realize every completed zero mode in resulting physical carrier
- [ ] prove two-ended return and raw Evans injectivity
- [ ] RH
