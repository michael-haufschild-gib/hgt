# Prime-trace critical energy bounds the off-line divisor budget

- **ID:** prime-trace-critical-energy-divisor-budget
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) -- scientifically non-new
- **Source:** `euler-support-energy-position-uncertainty.md`; boundary saturation of the
  prime-trace uncertainty law
- **Statement:** `[PROVED HERE; NOT NEW SCIENTIFIC KNOWLEDGE]` Let two
  tempered bounded-degree completed Euler products have prime-trace discrepancy `c_1(p)`. Suppose
  the prime discrepancy Dirichlet series converges absolutely in `Re s>beta`, where `beta>1/2`.
  If their quotient divisor has distinct points `rho_j=beta+i gamma_j` of signed orders `m_j`, then

  ```text
  liminf_(epsilon->0+) epsilon
    sum_p |c_1(p)|^2 log(p) / p^(2(beta-1/2)+epsilon)
  >= sum_j m_j^2.
  ```

## Goal

Strengthen the exponent-only non-entry barrier at its boundary. A boundary off-line zero should not
merely force energy divergence; it should consume a quantized amount of the unnormalized critical
Euler energy. This supplies a faithful integer budget, rather than a normalized density that is
blind to finitely many off-line zeros.

## Gates

- [x] 0 -> 1: boundary hypothesis, energy, and multiplicity budget stated.
- [x] 1 -> 2: complete paper proof below.
- [x] 2 -> 3: formalize the finite-set Cauchy--Schwarz skeleton and asymptotic implication in Lean.
- [x] novelty audit: fails scientific-newness gate; it is a shifted one-prime specialization of
  Farmer--Pitale--Ryan--Schmidt's edge-of-convergence lemma.

## Setup

Let

```text
H(s)=L_1(s)/L_2(s),
R(s)=Lambda_1(s)/Lambda_2(s),
c_1(p)=sum_r alpha_(1,p,r)-sum_r alpha_(2,p,r).
```

Assume the local factors are tempered (`|alpha_(j,p,r)|<=1`) and of degree at most `d`. Define the
prime-trace logarithmic-derivative series

```text
P(s)=sum_p c_1(p) log(p) p^(-s).
```

Assume `P` converges absolutely for `Re s>beta`, with `beta>1/2`. Let

```text
rho_j=beta+i gamma_j,     j=1,...,J,
```

be distinct points in the nontrivial divisor of `R`, and let `m_j` be their signed orders (positive
for a zero, negative for a pole). Put `a=beta-1/2` and

```text
E_a(epsilon)=sum_p |c_1(p)|^2 log(p) p^(-2a-epsilon).
```

## Theorem

For every finite set of distinct divisor points on `Re s=beta`,

```text
liminf_(epsilon->0+) epsilon E_a(epsilon) >= sum_(j=1)^J m_j^2.   (B)
```

Consequently, if the left side is a finite number `C`, the quotient divisor has at most `floor(C)`
distinct points on that vertical line, counted with the stronger squared-multiplicity budget. If
the critical energy residue is `<1`, the line contains no divisor point at all.

## Paper proof

`[PROVED HERE; NOT NEW SCIENTIFIC KNOWLEDGE]`

The logarithmic Euler expansion gives

```text
-H'(s)/H(s)=P(s)+Q(s),
Q(s)=sum_p sum_(k>=2)c(p,k)log(p)p^(-ks).
```

Temperedness and bounded degree give `|c(p,k)|<=2d`, so `Q` converges absolutely and is holomorphic
in `Re s>1/2`. The archimedean logarithmic derivative of `R/H` is also holomorphic at every
nontrivial point. Since `R` has signed order `m_j` at `rho_j`, it follows that the analytic
continuation of `P` has the local expansion

```text
P(s)=-m_j/(s-rho_j)+O(1)                 as s->rho_j.            (1)
```

The assumed absolute convergence in `Re s>beta` identifies this continuation with the prime series
there. Hence

```text
P(beta+epsilon+i gamma_j)=-m_j/epsilon+O(1).                    (2)
```

Let `M=sum_j m_j^2` and form

```text
K(epsilon)=sum_j m_j P(beta+epsilon+i gamma_j).
```

Equation (2) gives

```text
K(epsilon)=-M/epsilon+O(1).                                    (3)
```

On the prime side,

```text
K(epsilon)=sum_p c_1(p)log(p)p^(-beta-epsilon)
             sum_j m_j p^(-i gamma_j).
```

Split `p^(-beta-epsilon)=p^(-a-epsilon/2)p^(-1/2-epsilon/2)` and apply Cauchy--Schwarz:

```text
|K(epsilon)|^2 <= E_a(epsilon) B_J(epsilon),                   (4)

B_J(epsilon)=sum_p log(p)p^(-1-epsilon)
               |sum_j m_j p^(-i gamma_j)|^2.
```

Expanding the square,

```text
B_J(epsilon)=sum_(j,k)m_j m_k
  sum_p log(p)p^(-1-epsilon-i(gamma_j-gamma_k)).               (5)
```

For `j=k`, the prime number theorem gives

```text
sum_p log(p)p^(-1-epsilon)=1/epsilon+O(1).                     (6)
```

For `j!=k`, the inner sum remains bounded as `epsilon->0+`: subtracting the absolutely convergent
prime-power terms with exponent `>=2` identifies it with `-zeta'/zeta` at
`1+epsilon+i(gamma_j-gamma_k)`, and zeta has no zero on `Re s=1`. Therefore

```text
B_J(epsilon)=M/epsilon+O(1).                                  (7)
```

If `E_a(epsilon)` is infinite along a sequence, `(B)` is automatic there; otherwise apply (4).
Using (3) and (7),

```text
liminf_(epsilon->0+) epsilon E_a(epsilon)
 >= lim_(epsilon->0+) epsilon |K(epsilon)|^2/B_J(epsilon)
 = M.
```

This proves `(B)`. Applying it to every finite subset of divisor points proves the global counting
consequence.

## Entry interpretation

At a saturated entry event, one simple off-line zero consumes at least one unit of critical
prime-trace energy residue. Distinct entries add by squares of their multiplicities. Thus the source
constraint is an unnormalized integer budget:

```text
critical Euler energy residue >= faithful off-line divisor count.
```

If a source-side theorem can bound the residue by a number `<1`, no off-line zero can enter at that
horizontal displacement.

## Known-parent and novelty verdict

- Farmer--Pitale--Ryan--Schmidt's edge-of-convergence lemma already uses the same weighted sum of
  divisor orders, the same prime-kernel orthogonality, and the same squared-multiplicity bound on
  `Re s=1`.
- Put `z=s+beta-1` and `A(p)=c_1(p)p^(1-beta)`. Their `j=1` energy at `Re s=1+epsilon`
  becomes exactly

  ```text
  sum_p |c_1(p)|^2 log(p) p^(-2(beta-1/2)-epsilon).
  ```

  The arbitrary `beta` statement is therefore a change of variables, while temperedness merely
  makes the higher prime powers holomorphic at that boundary. Neither clears the novelty gate.
- The theorem remains useful as the exact source-side interpretation of the known lemma, but it is
  not new scientific knowledge and must not be advertised as such.

## Log

- 2026-07-10 -- generated from the saturated `q=2` uncertainty law; complete paper proof written.
- 2026-07-10 -- novelty audit failed: exact coefficient shift reduces it to the known
  Farmer--Pitale--Ryan--Schmidt edge-of-convergence lemma; reclassified as scientifically non-new.

## 2026-08-19 — unconditional Lean formalization (stage 3)

`formal/GaloisForLFunctions/RHTower/PrimeTraceCriticalEnergyBudget.lean`; every declaration
axiom-clean (`propext, Classical.choice, Quot.sound`).

| Card item | Lean declaration |
|---|---|
| the prime-trace source `P(s)` | `primeTraceSource` |
| the unnormalized critical energy `E_a(epsilon)` | `primeTraceEnergyReal`, `primeTraceEnergy` (extended, divergence read as `⊤`) |
| the mixed current `K(epsilon)` | `primeDivisorCurrent`, `primeDivisorCurrent_eq_tsum` |
| the unimodular divisor phase `sum_j m_j p^{-i gamma_j}` | `divisorPhase`, `norm_divisorPhase_le`, `normSq_divisorPhase` |
| the test energy `B_J(epsilon)` | `divisorTestEnergy`, `summable_divisorTestEnergyTerm` |
| **the expansion `(5)`** of the test energy into ordinate pairs | `divisorTestEnergy_term_eq`, `divisorTestEnergy_eq` |
| **`(6)`: the prime-log sum has residue one at the Euler pole** | `tendsto_primeGradeSource_sub_pole`, `tendsto_mul_primeGradeSource_pole` |
| **`(7)`: mixed ordinate pairs stay bounded** — `zeta` has no zero on `Re s = 1` | `tendsto_primeGradeSource_shift`, `tendsto_mul_primeGradeSource_shift` |
| **`B_J(epsilon) = M/epsilon + O(1)`** | `tendsto_mul_divisorTestEnergy` |
| **the Cauchy--Schwarz step `(4)`** | `norm_primeDivisorCurrent_sq_le` |
| **the budget `(B)`** | `primeTraceCriticalEnergyBudget`, `primeTraceCriticalEnergyBudget_extended` |

The prime-only source is the corpus's grade-one current `primeGradeSource`
(`RHTower/GradeMonodromyInversion.lean`), identified on `Re s > 1` with
`xiPrimeLogDirichletContinuation`; the pole residue comes from
`tendsto_LSeries_vonMangoldt_sub_pole` and the off-pole boundedness from
`differentiableAt_neg_logDeriv_riemannZeta` together with
`riemannZeta_ne_zero_of_one_le_re`, so the higher prime powers never have to be estimated
separately — they are exactly the holomorphic `xiPrimeLogHigherValuation` tail.

The local expansion `(2)` enters as the hypothesis `hres`: for each ordinate,
`epsilon * P(beta + epsilon + i gamma_j) -> -m_j` along the horizontal approach.  That is the exact
analytic content the card derives from the completed Euler quotient in its first proof paragraph,
and the theorem then delivers `(B)` from it unconditionally.  The extended form reads a divergent
energy as `⊤`, which is the card's own convention for the divergent case.

## Gates update

- [x] 2 -> 3: the finite-set Cauchy--Schwarz skeleton and asymptotic implication are formalized.
