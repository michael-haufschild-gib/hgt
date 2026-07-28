# Projective recurrence quantile and active-support law

- **ID:** `projective-recurrence-quantile-active-support-law`
- **Stage:** 3-formalized
- **Type:** QUANTILE RECURRENCE LAW / ACTIVE-SUPPORT CONSTRUCTIVE CEILING
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** `../3-formalized/new_scientific_knowledge/projective-weighted-coherence-water-filling-law.md`

## 1. Exact defects in parent theorem

The parent theorem studies the least deadline uniform over every phase packet.
Its lower bound only proves existence of one avoiding packet, and both displayed
errors are linear in full support size. Two stronger statements survive.

### 1.1 Fixed-spectrum lower bounds cannot depend only on weights

`[FALSIFIED]` No nontrivial weight-only lower bound can hold for every fixed
phase packet. If all phases are equal, the return amplitude is one at every
positive clock, independently of the weights. This is the exact obstruction to
replacing the minimax lower bound by a universal fixed-Hamiltonian lower bound.

`[PAPER-PROVED POSITIVE SURVIVOR]` Replace the existential adversary by a
Haar-quantile theorem. It controls the fraction of phase packets returning
through every finite horizon.

### 1.2 Full-support implementation cost is not intrinsic

The parent product-box proof synchronizes every nonpivot coordinate, including
coordinates below the water line. This creates one rounding constant per
support coordinate.

`[PAPER-PROVED POSITIVE SURVIVOR]` Synchronize only a chosen active subset.
Every discarded coordinate costs exactly twice its probability mass in the
amplitude defect and costs no clock dimension. The remainder is therefore
linear in selected active dimension, not full support.

## 2. Haar water budget

Let

```text
w_j>0,  sum_j w_j=1,  0<eta<=1.
```

For each pivot `k`, let `lambda_k` be the positive reverse-water level solving

```text
sum_(j!=k) min(w_j,1/lambda_k)=eta
```

when `eta<1-w_k`, and put `lambda_k=1` otherwise. Define

```text
H_k=(1/2) sum_(j!=k) log max(1,lambda_k w_j),

B_Haar(w,eta)
 =sum_k exp{(pi/4) lambda_k eta-H_k}.                 (1)
```

The factor `lambda_k eta` is a soft water dimension. In the active regime,

```text
lambda_k eta
 =sum_(j!=k) min(lambda_k w_j,1),                     (2)
```

so modes far below the water line contribute by total weighted mass rather
than by cardinality.

## 3. Haar-quantile theorem

For a phase packet `omega` on the torus, put

```text
A_w(n;omega)=|sum_j w_j exp(i n omega_j)|
```

and let

```text
E_N={omega : A_w(n;omega)>=1-eta for some 1<=n<=N}.
```

### Theorem 1 `[PAPER-PROVED]`

For normalized Haar measure `m`,

```text
m(E_N) <= N B_Haar(w,eta).                              (3)
```

Consequently, whenever `N B_Haar(w,eta)<=alpha`, at least a fraction
`1-alpha` of all phase packets avoid the return target through clock `N`.

### Proof

On the one-step target, the weighted variance identity gives a pivot `k` with

```text
sum_j w_j |z_j-z_k|^2 <= 4 eta.                         (4)
```

Projective shear makes the nonpivot phases independent. Exponential Markov at
`s_k=pi lambda_k/16` and the circle estimate

```text
integral exp(-u|z-1|^2) dz
 <= exp{-(1/2)log max(1,16u/pi)}
```

give the `k`-pivot contribution

```text
exp{(pi/4)lambda_k eta-H_k}.                            (5)
```

Union over pivots proves that one-step target measure is at most `(1)`.
Every positive integer power map preserves Haar measure. Union over the first
`N` powers proves `(3)`. Taking complements proves the quantile statement.
No independence between clock times is used.

## 4. Selected-support recurrence ceiling

Fix pivot `k` and a chosen set `A` of nonpivot coordinates. Put

```text
tau_A=sum_(j!=k,j notin A) w_j.                         (6)
```

For positive allocations `D_j<=w_j`, `j in A`, assume

```text
2 tau_A + sum_(j in A) D_j <= eta.                      (7)
```

Set `x_j=w_j/D_j>=1` and

```text
Q_j=ceil(pi sqrt(2x_j)),   j in A,
P=product_(j in A) Q_j.                                 (8)
```

### Theorem 2 `[PAPER-PROVED]`

For every phase packet there is `1<=n<=P` such that

```text
A_w(n;omega)>=1-eta,                                    (9)
```

and

```text
log P
 <= (1/2)sum_(j in A) log(w_j/D_j)
    + |A| log(2 pi sqrt(2)).                            (10)
```

Thus discarded modes cost probability mass in `(7)` but contribute neither
rate nor rounding cost in `(10)`. The explicit remainder is selected-support
linear.

### Proof

Use one product box for every discarded coordinate and `Q_j` boxes for
`j in A`. Pigeonhole applied to the `P+1` projective orbit points gives
`1<=n<=P` and centered active errors

```text
|theta_j|<=2pi/Q_j,  j in A.                            (11)
```

After removing the common pivot phase, every discarded phasor has real part
at least `-1`, while `cos theta>=1-theta^2/2` on active coordinates. Hence

```text
A_w(n;omega)
 >= 1-2 tau_A
      -sum_(j in A) w_j theta_j^2/2
 >= 1-2 tau_A-sum_(j in A) w_j/x_j
 =  1-2 tau_A-sum_(j in A) D_j
 >= 1-eta.                                              (12)
```

The ceiling inequality

```text
Q_j<=2 pi sqrt(2x_j)
```

and summation of logarithms give `(10)`.

The theorem leaves `(A,D)` free. Optimizing them trades synchronization rate
against discarded probability mass; no optimizer classification is needed
for the stated law.

## 5. Hostile attack

1. **“This predicts every fixed Hamiltonian.”** False and not claimed.
   Equation `(3)` is a Haar population bound; commensurate spectra can return
   at step one.
2. **“Haar phases at different times are independent.”** Not used. Only
   measure preservation and a union bound are used.
3. **“The quantile theorem is a relabeled minimax floor.”** No. The old floor
   extracted one point from a set of positive complement measure. Equation
   `(3)` retains the full measure estimate for every `N`.
4. **“Inactive coordinates disappeared without paying their phase error.”**
   They pay the sharp worst-case amplitude loss `2 tau_A` in `(7)` and `(12)`.
5. **“The active set is silently assumed to be the original water set.”**
   No. `A` and its allocations are arbitrary feasible choices. The original
   water set need not satisfy `(7)` because discarding a phase costs `2w_j`,
   not `w_j`.
6. **“The improvement proves an exact two-sided active-support law.”** It
   does not. The result is an exact Haar-quantile lower law and a selected-
   support universal upper law. No equality of their refined functionals is
   claimed.
7. **“This is already the hard effective-support theorem.”** Tail truncation
   is established methodology. The mathematical delta here is its exact
   integration with anisotropic water allocation and the selected-coordinate
   clock constant. Novelty remains unverified pending exact comparison with
   the 2026 recurrence literature.

## 6. Formalization obligations

- [x] Define `projectiveCanonicalHaarWaterBudget`.
- [x] Prove exact one-step target bound by the pivot-specific canonical sum.
- [x] Prove first-`N` Haar hit bound.
- [x] Define selected-support resolutions with value one off the selected set.
- [x] Prove hybrid active quadratic / inactive worst-case amplitude floor.
- [x] Prove selected-support deadline and logarithmic bound.
- [x] Run `#print axioms`, targeted Lean checks, lint, and final module build.

Audit result: target and umbrella modules pass; load-bearing declarations use
only `propext`, `Classical.choice`, and `Quot.sound`. Repository-wide lint was
run and still reports five pre-existing unrelated RHTower umbrella
reachability failures; none lies in this theorem's dependency surface.

Formal module:
`formal/GaloisForLFunctions/RHTower/ProjectiveWeightedHaarQuantileActiveSupport.lean`.
