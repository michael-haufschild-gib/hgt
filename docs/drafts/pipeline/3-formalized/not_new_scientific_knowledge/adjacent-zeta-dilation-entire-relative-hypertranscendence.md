# Adjacent zeta-dilation entire relative hypertranscendence

- **ID:** `adjacent-zeta-dilation-entire-relative-hypertranscendence`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / `[BRIDGE]`
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NEW APPLICATION] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Parents:** the publication-ready Omega-leading-echelon criterion; zeta--shell differential
  freeness; rational base-gauge invariance; high-exponent adjacent-dilation zero-freeness.
- **Statement:** The pole-cancelled entire adjacent direct-dilation differences
  `A_m(s)=(ms-1)((m+1)s-1)(zeta(ms)-zeta((m+1)s))`, `m>=2`, are jointly differentially
  algebraically independent over `C(s)<zeta>`.

## Purpose and boundary

This closes one unchecked gate in
`../../1-in-progress/xi-entire-high-shell-bipolar-completion-graph.md`.  Scalar entireization does
not erase the finite differential rank of the high-shell family.  It does erase the original
positive, pairwise-disjoint shell coefficient section, so the completion multiplication graph
remains relevant for source positivity, not for hypertranscendence.

The theorem supplies no orientation, order, contraction, or zero-location law.  At an Xi zero
`rho`, the cofinal quotient still only reports

```text
lim_m A_(m+1)(rho) A_m(1-rho) /
      (A_m(rho) A_(m+1)(1-rho)) = 2^(1-2 rho).
```

Nothing below forces this character to have modulus one.  Treating maximal rank as a reason for
that equality would contradict the corpus's finite-jet universality and unpolarized-completion
no-go theorems.

## Coefficient source

For `m>=2`, define the bounded arithmetic function

```text
c_m(n)=1_{there exists a>=1 with n=a^m}
       -1_{there exists b>=1 with n=b^(m+1)}.             (1)
```

On a common half-plane of absolute convergence its Dirichlet transform is

```text
C_m(s)=sum_(n>=1)c_m(n)n^(-s)
      =zeta(ms)-zeta((m+1)s).                            (2)
```

The equality follows because positive integer `m`-th roots are unique and the two indicator
series are respectively `zeta(ms)` and `zeta((m+1)s)`.  The coefficient at `n=1` cancels.

## Exact Omega-leading layer

### Lemma 1

If `c_m(n)!=0`, then `Omega(n)>=m`.  If equality holds, then `n=q^m` for a unique prime `q` and
`c_m(n)=1`.

### Proof

Nonvanishing of `(1)` says that exactly one of the two perfect-power conditions holds.

If `n=a^m`, then

```text
Omega(n)=m Omega(a).
```

The value `n=1` cannot contribute because both indicators then equal one.  Hence `a>1`,
`Omega(a)>=1`, and `Omega(n)>=m`.  Equality forces `Omega(a)=1`, so `a=q` is prime and
`n=q^m`.  The exponent `m` is not divisible by `m+1`, so `q^m` is not an `(m+1)`-st power and
`c_m(q^m)=1`.

If instead `n=b^(m+1)`, then `b>1` and

```text
Omega(n)=(m+1)Omega(b)>=m+1.
```

This cannot occur in the equality case.  Unique factorization gives uniqueness of `q`. `QED`

Let `L^k f(n)=(-log n)^k f(n)` and let the prime derivation be

```text
partial_q f(n)=v_q(nq)f(nq).
```

### Lemma 2

For every prime `q` and `k,n>=0`,

```text
Omega(n)<m-1
  -> partial_q(L^k c_m)(n)=0,                            (3)

Omega(n)=m-1
  -> partial_q(L^k c_m)(n)
     =m(-m log q)^k 1_{n=q^(m-1)}.                      (4)
```

### Proof

If the left side is nonzero, then `c_m(nq)!=0`.  Lemma 1 gives

```text
m<=Omega(nq)=Omega(n)+1,
```

which proves `(3)`.  Under `Omega(n)=m-1`, nonvanishing gives `Omega(nq)=m`; Lemma 1 therefore
gives `nq=p^m` for a prime `p`.  Since `q` divides `p^m`, unique factorization gives `p=q` and
`n=q^(m-1)`.  At that point

```text
v_q(q^m)(-log(q^m))^k c_m(q^m)=m(-m log q)^k.
```

This proves `(4)`. `QED`

## Differential independence

### Theorem 1

The countable family

```text
{zeta} union {C_m:m>=2}
```

is jointly differentially algebraically independent over `C(s)`.

### Proof

Take any finite subfamily and assign level one to the zeta coefficient source `1(n)=1` and level
`m` to `c_m`.  These positive levels are distinct.  The zeta source has the canonical level-one
prime-ray leading layer.  Lemma 2 gives the required lower-layer vanishing and canonical leading
point mass for every `c_m`.  Every source has a finite abscissa of absolute convergence.  The
publication-ready Omega-leading-echelon criterion therefore proves algebraic independence of
every finite jet rectangle over `C(s)`.  Finite character proves the countable differential
statement. `QED`

Put

```text
K_zeta=C(s)<zeta>.
```

Base adjunction applied to Theorem 1 gives:

### Corollary 2

The family `{C_m:m>=2}` is jointly differentially algebraically independent over `K_zeta`.

For each `m>=2`, put

```text
p_m(s)=(ms-1)((m+1)s-1),
A_m(s)=p_m(s)C_m(s).                                    (5)
```

Each `p_m` is a nonzero element of `C(s)`, hence of `K_zeta`.  For every finite jet order, the
change from the jets of `C_m` to the jets of `A_m` is triangular over `K_zeta`, with diagonal
entry `p_m!=0`.  Applying this invertible change independently in each label gives:

### Theorem 3

The countable family

```text
{A_m:m>=2}
```

is jointly differentially algebraically independent over `K_zeta`.

The function `A_m` is entire: the factor `ms-1` cancels the pole of `zeta(ms)` at `s=1/m`, and
the factor `(m+1)s-1` cancels the pole of `zeta((m+1)s)` at `s=1/(m+1)`; the other summand is
holomorphic at each respective point.  Existing corpus zero-freeness additionally gives

```text
A_m(s)!=0    when m>=12 and Re(s)>1/2.                  (6)
```

## Hostile audit

- The proof is a direct application of the existing Omega-leading-echelon theorem plus ordinary
  base adjunction and rational gauge invariance.  It is not a new general HT mechanism.
- Shapiro--Sparer and Pong are parent sources for arithmetic-function Jacobian methods; the local
  literature audit found no exact adjacent direct-dilation statement, but formula-level
  noncollision is not scientific novelty.
- The result changes one route assertion: retaining the graph is not necessary to preserve
  maximal differential rank.  The graph is still necessary if one wants the original positive
  shell section and its label orthogonality.
- Differential independence does not compare `A_m(rho)` with `A_m(1-rho)` and does not constrain
  the FE-odd boundary character.  Therefore no Lean investment is justified solely by this
  bridge.

## Open RH core after the correction

`[OPEN CORE]` Construct, before zero specialization, a source-effective polarized completion
which retains the positive shell section and whose induced Hermitian law on the scalar entire
normal family forces the FE-odd boundary character to be neutral on the Xi divisor.  Existing
corpus proves that reflection, finite differential rank, unpolarized completion, and a local
rank-one conormal map cannot supply this law.

## Gates

- [x] exact coefficient source and Dirichlet transform
- [x] exact Omega-leading layer
- [x] joint zeta/direct-dilation differential independence
- [x] base adjunction over `K_zeta`
- [x] coordinatewise polynomial gauge transfer
- [x] entireness and inherited strict-right zero-freeness
- [x] hostile significance downgrade
- [ ] external specialist priority review, unnecessary unless theorem is used in a larger result
- [x] Lean formalization complete (2026-08-18); see below

## Log

- 2026-07-28 — proved the scalar entire relative-HT gate and downgraded it after hostile audit.

## Formalization (2026-08-18)

Two modules, both unconditional and axiom-clean (`#print axioms` reports only `propext`,
`Classical.choice`, `Quot.sound`), wired into `GaloisForLFunctions.RHTower`.

`formal/GaloisForLFunctions/RHTower/AdjacentDilationDifferentialFreeness.lean`
(namespace `RHTower.AdjacentDilation`):

| Card step | Lean name |
|---|---|
| the coefficient source `(1)` | `adjacentDilationCoeff` |
| **Lemma 1**, grade bound | `adjacentDilationCoeff_cardFactors_lower` |
| **Lemma 1**, equality case | `adjacentDilationCoeff_eq_prime_pow_of_cardFactors_eq`, `adjacentDilationCoeff_prime_pow` |
| **Lemma 2**, `(3)` lower-layer vanishing | `primeDeriv_rotatedAdjacentJet_eq_zero_of_cardFactors_lt` |
| **Lemma 2**, `(4)` leading point mass | `primeDeriv_rotatedAdjacentJet_eq_pointMass_of_cardFactors_eq` |
| the unified zeta/adjacent family | `zetaAdjacentArithmetic` |
| **Theorem 1**, jet rectangle | `zetaAdjacentJets_algebraicIndependent` |
| **Theorem 1**, formal Dirichlet algebra | `zetaAdjacentArithmetic_differentialIndependent` |
| **Theorem 1**, actual meromorphic carriers | `zetaAdjacentUpperEndCarrier_differentialIndependent`, `..._of_injective` |
| **Theorem 1** for the card's family `{zeta} ∪ {C_m : m ≥ 2}` | `zetaAdjacentDilationUpperEnd_differentialIndependent` |

`formal/GaloisForLFunctions/RHTower/AdjacentDilationZetaBase.lean` (same namespace):

| Card step | Lean name |
|---|---|
| the base `K_zeta = C(s)<zeta>` | `zetaAdjoinField` |
| **Corollary 2** | `adjacentDilationUpperEndCarrier_differentialIndependent_over_zeta` |
| **Theorem 3**, coordinatewise nonzero base gauge | `adjacentDilationGauge_differentialIndependent_over_zeta` |
| `(2)` the Dirichlet transform `C_m(s) = zeta(ms) - zeta((m+1)s)` | `lseries_adjacentDilationCoeff` (with `lseries_perfectPowerArith`) |
| `(5)` the pole-cancelled entire representative and its entireness | `adjacentDilationEntire`, `differentiable_adjacentDilationEntire` |
| the product formula away from the two cancelled poles | `adjacentDilationEntire_eq_product` |

Three notes on the formal route.

* Theorem 1 is an instance of the corpus's Ω-leading-echelon criterion
  `RHTower.omegaLeadingJets_algebraicIndependent`: assigning level `m` to `c_m` and level one to
  the zeta stream, Lemma 2 is exactly the criterion's lower-layer and leading-point-mass
  hypotheses.  No new independence mechanism is introduced, which is what the card's hostile audit
  already recorded.
* Corollary 2 is the corpus's `differentialIndependent_sum_right_over_left_differentialAdjoin`, and
  Theorem 3 is `differentialIndependent_mulBase_iff`; the card's triangular-jet argument is exactly
  that lemma's proof, so it is cited rather than repeated.
* Entireness is proved from `riemannZeta w = (w-1)⁻¹ + riemannZeta₀ w` with `riemannZeta₀` entire:
  `A_m` is exhibited directly in the manifestly entire form
  `((m+1)s-1)(1 + (ms-1) zeta₀(ms)) - (ms-1)(1 + ((m+1)s-1) zeta₀((m+1)s))`, and
  `adjacentDilationEntire_eq_product` identifies it with the displayed product wherever both
  factors are nonzero.

Equation `(6)`, the strict-right zero-freeness for `m ≥ 12`, is **not** proved on this card — the
card states it as inherited from the parent high-exponent adjacent-dilation zero-freeness result
("Existing corpus zero-freeness additionally gives"), and the corresponding Lean provider is not
present in the tree.  It is therefore recorded here as a citation, not as a formalized claim of
this card, exactly as the paper card presents it.
