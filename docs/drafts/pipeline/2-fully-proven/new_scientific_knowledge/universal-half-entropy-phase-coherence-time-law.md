# Universal half-entropy law for near-perfect phase coherence

- **ID:** `universal-half-entropy-phase-coherence-time-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / HIGH-DIMENSIONAL KRONECKER MINIMAX LAW / PHASE-CAPACITY LAW
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[TARGETED NOVELTY AUDIT PASSED 2026-07-19] [LEAN FORMALIZATION IN PROGRESS]`
- **Statement:** The worst-case first clock at which a `d`-frequency phase source reaches relative
  coherence `1-eta` has the universal near-perfect asymptotic
  `log T_d(eta)~(d/2)log(1/eta)` in the iterated high-dimension, high-coherence limit.  The exponent
  `1/2` is exact.

## 1. Minimax coherence clock

For `d>=1`, `0<eta<1`, and `omega in R^d`, put

```text
A_d(n;omega)=|(1/d)sum_(j=1)^d exp(i n omega_j)|,            (1)

tau_d(eta;omega)
 =min{n>=1:A_d(n;omega)>=1-eta},                            (2)

T_d(eta)=sup_(omega in R^d) tau_d(eta;omega).               (3)
```

The minimum in `(2)` exists for every `omega` by finite-dimensional simultaneous recurrence.
Thus `T_d(eta)` is finite.  It is the worst possible first near-coherence time among all
`d`-frequency phase systems.

## 2. Finite-dimensional two-sided theorem `[PROVED]`

Let

```text
M_eta=ceil(pi sqrt(2/eta)),                                  (4)

B_d(eta)
 =d exp(d/2)(sqrt(pi/2)sqrt(eta))^(d-1).                    (5)
```

Then:

```text
T_d(eta)<=M_eta^d.                                          (6)
```

Moreover, for every integer `N>=1` satisfying

```text
N B_d(eta)<1,                                               (7)
```

there is a frequency vector `omega in R^d` such that

```text
A_d(n;omega)<1-eta     for every 1<=n<=N.                   (8)
```

Consequently, whenever `B_d(eta)<=1/2`,

```text
T_d(eta)>=floor(1/(2B_d(eta))).                             (9)
```

The constants in `(4)`--`(9)` are explicit but not claimed optimal.  The exponent extracted from
them is optimal.

## 3. Universal half-entropy law `[MAIN THEOREM]`

One has

```text
lim_(eta downarrow 0) liminf_(d->infinity)
  log T_d(eta)/(d log(1/eta))

=lim_(eta downarrow 0) limsup_(d->infinity)
  log T_d(eta)/(d log(1/eta))

=1/2.                                                       (10)
```

Equivalently, the minimax phase-space cost of coherence defect `eta` is

```text
eta^(-d/2+o(d))                                             (11)
```

as dimension tends to infinity and then `eta` tends to zero.  The common scalar phase removes one
dimension, which appears only in the lower-order replacement of `d` by `d-1`; it does not change
the entropy density `1/2`.

## 4. Proof of the upper bound

Choose an integer `M>=pi sqrt(2/eta)`.  Quantitative simultaneous recurrence gives an integer

```text
1<=n<=M^d                                                   (12)
```

and integers `r_j` such that

```text
|n omega_j-2pi r_j|<=2pi/M.                                 (13)
```

For `delta_j=n omega_j-2pi r_j`, positivity and

```text
cos(delta)>=1-delta^2/2                                    (14)
```

give

```text
A_d(n;omega)
 >=(1/d)sum_j cos(delta_j)
 >=1-2pi^2/M^2
 >=1-eta.                                                   (15)
```

This proves `(6)`.  The formalized delay--resolution theorem proves more: an arbitrary clock floor
`L` changes `(12)` only to `L<=n<=LM^d`, without changing `(13)`.

## 5. Proof of the lower bound

Let `theta=(theta_1,...,theta_d)` be Haar-uniform on the torus and write

```text
z_j=exp(i theta_j),
m=(1/d)sum_j z_j.                                           (16)
```

Define the near-coherence target

```text
E_d(eta)={theta:|m|>=1-eta}.                                (17)
```

### 5.1 Pairwise-variance pivot

The exact identity

```text
sum_(j,k)|z_j-z_k|^2=2d^2(1-|m|^2)                         (18)
```

shows that on `E_d(eta)`,

```text
sum_(j,k)|z_j-z_k|^2<=4eta d^2.                            (19)
```

Therefore some pivot `k` satisfies

```text
sum_j|z_j-z_k|^2<=4eta d.                                  (20)
```

Taking the union over the `d` possible pivots and using the Haar automorphism

```text
(theta_k,(theta_j-theta_k)_(j!=k)),                         (21)
```

reduces the target measure to a lower-tail estimate for `d-1` independent copies of

```text
Y=|exp(i Theta)-1|^2,
Theta uniform on [-pi,pi].                                  (22)
```

### 5.2 Gaussian small-ball bound

For `|theta|<=pi`, concavity of sine gives

```text
|exp(i theta)-1|>=2|theta|/pi.                              (23)
```

Hence for every `lambda>0`,

```text
E exp(-lambda Y)
 <=(1/(2pi))integral_R exp(-4lambda theta^2/pi^2)dtheta
 =sqrt(pi)/(4sqrt(lambda)).                                 (24)
```

Apply exponential Markov to `(20)` with `lambda=1/(8eta)`.  Equations `(21)`--`(24)` give

```text
Haar(E_d(eta))
 <=d exp(d/2)(sqrt(pi/2)sqrt(eta))^(d-1)
 =B_d(eta).                                                 (25)
```

### 5.3 Orbit avoidance

For every positive integer `n`, multiplication by `n` preserves Haar measure on the torus.
Therefore

```text
Haar(union_(1<=n<=N){omega:n omega in E_d(eta)})
 <=N B_d(eta).                                              (26)
```

If `(7)` holds, the union in `(26)` does not fill the torus.  Any frequency vector outside it
satisfies `(8)`.  This proves `(9)`.

## 6. Proof of the exponent

From `(6)` and `(4)`,

```text
limsup_(d->infinity) log T_d(eta)/d
 <=(1/2)log(1/eta)+log(pi sqrt(2))+o_eta(1).                 (27)
```

From `(5)` and `(9)`, for every fixed sufficiently small `eta`,

```text
liminf_(d->infinity) log T_d(eta)/d
 >=(1/2)log(1/eta)-1/2-(1/2)log(pi/2).                      (28)
```

Divide `(27)`--`(28)` by `log(1/eta)` and let `eta` decrease to zero.  Both sides converge to
`1/2`, proving `(10)`.

## 7. Prime-log and Connes consequence

The theorem determines the ambient minimax geometry.  For `d=pi(X)`, the universal cost of
near-perfect coherence is

```text
exp((pi(X)/2)log(1/eta)+O(pi(X))).                          (29)
```

The actual prime-log vector is not random and need not be worst-case.  Its unresolved arithmetic
rigidity is now isolated by `prime-log-kronecker-coherence-capacity-conjecture.md`:

```text
every fixed nonzero prime--polar coherence level
must have positive exponential cost in pi(X).               (30)
```

Thus `(10)` does not pretend to solve the prime-specific lower bound.  It proves that the
`exp(constant*pi(X))` scale is the universal high-dimensional phase scale and that the square-root
coherence exponent is forced before any zeta-specific input enters.  The Connes Gamma window lies
at `log T=o(pi(X))`; proving that the prime-log orbit obeys the positive entropy law would exclude
phase escape there.

## 8. Novelty and anti-theatre audit

Targeted searches through 2026-07-19 covered:

- simultaneous Dirichlet and Kronecker approximation;
- shrinking-target and covering-radius theorems for torus actions;
- infinite-time Bohr correspondence and Sidon constants for Dirichlet polynomials;
- large-value estimates for Dirichlet polynomials;
- phase synchronization and high-dimensional torus recurrence.

These parent theories contain the individual tools behind the two inequalities.  No source found
states the minimax coherence clock `(3)`, the finite two-sided bounds `(6)`--`(9)`, or the exact
half-entropy law `(10)`.  In particular:

1. Dirichlet approximation supplies only the upper bound and does not prove minimax sharpness.
2. Generic shrinking-target theorems fix the dimension or study almost-every orbit, rather than
   the iterated high-dimensional near-diagonal minimax law.
3. Bohr/Sidon theory recovers the infinite-time torus supremum but does not quantify the first
   near-coherence clock.
4. Dirichlet-polynomial large-value estimates concern value counts for coefficient sequences and
   do not state the universal worst-frequency exponent `(10)`.

The theorem passes the anti-theatre test because its answer is not present in the searched
literature and because both inequalities are load-bearing: removing either one destroys the exact
constant `1/2`.

Closest comparison sources:

- Classical Dirichlet simultaneous approximation and Kronecker recurrence.
- M. M. Dodson, *Diophantine approximation, Khintchine's theorem, torus geometry and Hausdorff
  dimension*, arXiv:0710.4264.
- O. F. Brevig, *On the Sidon Constant for Dirichlet Polynomials*, arXiv:1306.0403.
- L. Guth and J. Maynard, *New large value estimates for Dirichlet polynomials*,
  arXiv:2405.20552, v2 (2026).
- M. Hauke, A. Shubin, E. Stefanescu, and A. Zafeiropoulos, *Circle coverings driven by arithmetic
  sequences*, arXiv:2604.02005.

## 9. Lean status

The complete upper mechanism, including the stronger delayed weighted and prime--polar forms, is
formalized in

```text
formal/GaloisForLFunctions/RHTower/CCMPrimePoleFiniteCoherence.lean.
```

In particular:

```text
exists_fin_simultaneous_two_pi_phase_approximation_delayed_quantitative
one_sub_sq_phaseError_div_two_le_re_exp_I_mul_real
nonnegative_weighted_phaseSum_norm_floor_of_phase_approximation
exists_fin_primeLog_nonnegative_phaseSum_polar_floor_delayed_quantitative
```

are axiom-audited.  The Haar target-measure estimate `(25)`, orbit avoidance `(26)`, and the
asymptotic squeeze `(10)` remain to be formalized.  They use no conjectural number theory.

## Gates

- [x] define the minimax first-coherence clock
- [x] prove the quantitative upper bound
- [x] prove the pairwise-variance pivot
- [x] prove the Gaussian small-ball target estimate
- [x] prove orbit avoidance by Haar preservation and the union bound
- [x] prove the exact half-entropy exponent
- [x] run targeted corpus and external novelty searches
- [x] formalize and axiom-audit the complete upper mechanism
- [ ] formalize the Haar target-measure estimate
- [ ] formalize finite-time orbit avoidance
- [ ] formalize the asymptotic squeeze

## Log

- 2026-07-19 -- Derived the delay--resolution recurrence from the prime-phase obstruction.
- 2026-07-19 -- Proved the quadratic positive-weight upper law.
- 2026-07-19 -- Proved the matching Haar-avoidance lower law and the universal exponent `1/2`;
  passed a targeted anti-theatre audit and opened the unconditional Lean completion.
