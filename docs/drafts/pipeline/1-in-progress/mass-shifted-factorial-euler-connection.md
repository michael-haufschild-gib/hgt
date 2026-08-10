# Mass-shifted factorial Euler connection

- **ID:** `mass-shifted-factorial-euler-connection`
- **Stage:** 1-in-progress
- **Type:** THEOREM / POSITIVE SURVIVOR / SOURCE-FIRST CONNECTION
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 adaptive `P^sharp` open core
- **Claim:** Consecutive factorial-diagonal transforms of one adaptive coefficient vector form an
  injective parallel ladder for the square of a shifted Euler connection.

## Exact theorem

For finite real coefficients `c_j`, define

```text
P_r(T) = sum_j c_j T^j / ((r+j)!)^2,
E_a(P) = T P'(T) + a P(T).
```

Then, for every natural `r`,

```text
P_r = E_(r+1)(E_(r+1)(P_(r+1))).                 (1)
```

Moreover

```text
coeff_j(E_a(P)) = (j+a) coeff_j(P).               (2)
```

Thus `E_a` is injective whenever `a>0`, and every lower carrier polynomial is determined by every
higher carrier polynomial. The adaptive source flag is one discrete connection orbit, not a list
of unrelated root polynomials.

## Completed mixed-amplitude source law

Write

```text
m_k(y) = Re xiShiftedReciprocalMoment(y,k),
S_(r,c)(y) = sum_j c_j m_(r+j)(y),
(M_r c)_j = (r+j+1)c_j,
Q_(r,c)(T) = sum_j c_j T^j / ((r+j)!(r+j+1)!).
```

Then the middle amplitude is simultaneously

```text
Q_(r,c) = E_(r+1)(P_(r+1,c)) = P_(r+1,M_r c),          (3)
P_(r,c) = E_(r+1)(Q_(r,c)),                             (4)
```

and the actual completed source flow is

```text
d/dy S_(r,c)(y) = -S_(r+1,M_r c)(y).                   (5)
```

At `y=w^2`, `w>1/2`, the right side of `(5)` is the completed prime--Gamma aggregate

```text
-sum_j (M_r c)_j normalizedCompletedSourceMoment(r+1+j,w),
```

which splits before reflection or scalar reporting into its archimedean term and its
Lebesgue-minus-Chebyshev radial discrepancy.  The latter is the existing positive Gamma carrier
integral with the *mixed* adaptive amplitude `Q_(r,c)`, by `(3)` and the reverse-Bessel carrier
law.  Thus `(3)--(5)` are an admission-sensitive source landing: source differentiation chooses
the coefficient adaptation, and the chosen adaptation is exactly one unsquared Euler step of
`P^sharp`.  No fixed observer, orientation map, or post-aggregation sign choice occurs.

### Paper proof of `(3)--(5)` `[PAPER-PROVED]`

On `T^j`, `E_(r+1)` multiplies by `r+j+1`.  Hence the `j`th coefficient after one step is

```text
(r+j+1)c_j / ((r+j+1)!)^2
  = c_j / ((r+j)!(r+j+1)!),
```

which proves both equalities in `(3)`.  Applying the same multiplier again gives

```text
(r+j+1)c_j / ((r+j)!(r+j+1)!)
  = c_j / ((r+j)!)^2,
```

proving `(4)`.  Corpus moment transport gives

```text
m_k'(y)=-(k+1)m_(k+1)(y).
```

Finite differentiation therefore yields

```text
S_(r,c)'(y)
 = -sum_j (r+j+1)c_j m_(r+j+1)(y)
 = -S_(r+1,M_r c)(y),
```

which is `(5)`.  The source split follows termwise from the normalized completed-source identity;
the finite sum is formed before either arithmetic integral, so adaptive cancellation is retained.

## Fourth-cumulant reserve circularity theorem

The apparent degree-one source target in the current frontier is the contact-locus cap

```text
t^3 K4 <= 3 A (1-e)(1-2e^2).                           (6)
```

This is not a weaker arithmetic reserve.  Put `y=t^2`, `m_k=m_k(y)`,
`A=t m_0`, and `e=1-2y m_1/m_0`.  On contact `m_0 m_2=m_1^2`, direct substitution into `(6)`
gives exactly

```text
m_1 m_3 >= m_2^2.                                      (7)
```

Since `m_1>0`, contact also gives null root `a=m_1/m_0=m_2/m_1`, and

```text
L_y(X(X-a)^2) = m_3-m_2^2/m_1.
```

Consequently `(6)`, `(7)`, nonnegative terminal flux, and positivity of the adjacent shifted
`2 x 2` Hankel minor are equivalent on the actual contact locus.  Calling `(6)` an independent
fourth-cumulant producer is circular: it is the desired terminal sign in cumulant coordinates.
The positive survivor is precise.  Any new arithmetic theorem must act before this compression,
and `(3)--(5)` identify the canonical pre-compression mixed amplitude on which it must act.

## Paper proof `[PAPER-PROVED]`

On the monomial `T^j`, Euler differentiation gives

```text
E_a(T^j) = (j+a) T^j.
```

Taking `a=r+1` twice multiplies the `j`th coefficient of `P_(r+1)` by `(r+j+1)^2`. Since

```text
(r+j+1)! = (r+j+1)(r+j)!,
```

the resulting coefficient is

```text
(r+j+1)^2 c_j / ((r+j+1)!)^2 = c_j / ((r+j)!)^2,
```

which proves (1) coefficientwise. Formula (2) follows from
`coeff_j(T P')=j coeff_j(P)`. If `a>0`, then `j+a>0` for every natural `j`; therefore
`E_a(P)=0` forces every coefficient of `P` to vanish, proving injectivity.

Hostile audit: no positivity, RH, root geometry, source inequality, or computation is used. This
does not sign terminal holonomy. It proves only that any successful source law must act on the
whole connection orbit and cannot assign independent signs to successive `P^sharp` levels.

## Conjecture failures that exposed theorem

1. **One-cut Γ--Xi response signs adaptive aggregate — FAIL.** Its semilocal depth spectral measure
   is not the completed Chebyshev--Gamma source measure tested by `P^sharp`; no typed equality
   exists.
2. **Hypertranscendence propagates finite null flag — FAIL.** Finite jet annihilation at one point
   does not create a global algebraic differential equation.
3. **Positive survivor — (1)--(2).** Factorial normalization carries a hidden discrete connection
   that couples every visible null rung to first omitted rung.
4. **C60-A, source derivative lands on one-Euler midpoint — PROVED.** Equations `(3)--(5)` give
   exact adaptive source execution before completed arithmetic aggregation.
5. **C60-B, fourth-cumulant reserve is a weaker source bound — FAILS BY EQUIVALENCE.** On contact
   it is exactly the adjacent shifted minor/terminal-flux sign `(7)`.
6. **C60-C, prime--Gamma mixed-current orientation — OPEN.** Prove a source-admission law on the
   mixed amplitude `Q_(r,c)` before its archimedean and Chebyshev discrepancy channels are
   compressed.  A restatement of `(6)` or a fixed linear reporter does not qualify.
7. **C60-D, the midpoint packet has no intrinsic bilinear null-face landing — FAILS.**  For every
   polynomial `p`, Euler--Leibniz gives

   ```text
   X E_1(p Xp) = 2 (Xp)(X E_1p).
   ```

   Therefore source transport forces the exact odd-to-even shear

   ```text
   d/dy L_y(p Xp) = -2 L_y((Xp)(X E_1p)).
   ```

   If `c(p)` is the coefficient packet of `p^2`, then `L_y(p Xp)=S_(1,c(p))(y)` and the landing is
   `S_(2,M_1c(p))`.  Its completed radial carrier is exactly
   `P_(2,M_1c(p))=Q_(1,c(p))`.  On the Euler ray it splits before reflection aggregation into
   twice the archimedean and Chebyshev-discrepancy pairings of `(Xp,X E_1p)`.  This is the missing
   source-first bilinear landing; only its strict arithmetic orientation remains open.

## External frontier

Classical Bessel/reverse-Bessel recurrences explain factorial coefficients, but current source
search found no statement identifying this exact adaptive squared-factorial ladder as a squared
Euler connection inside a shifted-Xi null flag. Novelty remains unverified.

## Status

`[PAPER-PROVED] [LEAN-TARGET-BUILT] [AXIOM-AUDITED] [NOVELTY UNVERIFIED]`.  The Euler connection,
completed source split, fourth-cumulant circularity, and odd-to-even adaptive mixed-source shear
are all formalized unconditionally.  Exact shear theorem is recorded at Stage 3 in
`mass-shifted-adaptive-mixed-source-shear.md`; this card remains open only for C60-C's strict
prime--Gamma channel orientation.

## Log

- 2026-08-09 — identity conjectured from actual `P^sharp` normalization; coefficient proof and
  injectivity audit closed without computation.
- 2026-08-10 — source transport forced the unsquared one-Euler midpoint `Q`, yielding exact
  completed mixed-amplitude law `(3)--(5)`.  Hostile audit proved the advertised fourth-cumulant
  reserve is exactly the original shifted-minor sign on contact, so it cannot be used as an
  independent producer.
- 2026-08-10 — Euler--Leibniz lifted the source connection from arbitrary linear packets to the
  actual marked crossing current: odd `L_y(pXp)` lands on even adaptive shear
  `-2L_y((Xp)(XE_1p))`.  The successor completed packet has mixed carrier `Q_(1,c(p))` and retains
  archimedean/Chebyshev channels before reflection aggregation.
