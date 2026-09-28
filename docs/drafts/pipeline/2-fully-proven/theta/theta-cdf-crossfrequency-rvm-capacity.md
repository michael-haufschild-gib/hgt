# The Xi zero density lives in theta CDF cross-frequency coupling

- **ID:** `theta-cdf-crossfrequency-rvm-capacity`
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM and positive spectral-capacity classification
- **Routes:** STC, CSB, U, K-RVM, MPLF, theta source transport
- **Status:** `[PROVED HERE ON PAPER] [LEAN FORMALIZATION OPEN] [NOT AN RH PROOF]`
- **Dependencies:** [theta CDF-action quotient](../1-in-progress/theta-quantile-fourier-action-quotient.md); `HedenmalmThetaKernelEnergy.lean` (literal double-exponential source envelope); `HedenmalmThetaSourceDeterminantMultiplicity.lean` (algebraic multiplicities); `RiemannVonMangoldt.lean` (zero count); standard compact-operator Ky Fan and Weyl majorization inequalities.

## Statement

Let `D=P B|_(1⊥)` be the compact theta source inverse in the
mean-zero Fourier space, with matrix

```text
D_(m,n) = (Φ_m−Φ_(n−m))/(2πn),
Φ_n = ∫_0^1 q(t)(1−cos(2πnt))dt
    = ∫_ℝ (1−cos(2πnF(x)))dx.
```

For each `n≥1`, let `H_n=span{e_n,e_(-n)}` and let `D₀` be the
orthogonal direct sum of the exact `H_n` diagonal compressions of
`D`. Put `R=D−D₀`, the **full cross-frequency operator**. For a
compact operator `T`, write `s_j(T)` for decreasing singular values
and `K_N(T)=Σ_(j≤N)s_j(T)`.

1. The literal theta tail and strict log-concavity give the sharp
   action clock

   ```text
   Φ_n = log log n − log π + O(log log n/log n).
   ```

   In particular, at prime `p` the theta CDF action and the
   Mertens clock `x_p=log log p` differ by the fixed calibration
   `−log π` plus an integrably decaying clock error. Consequently
   `D₀` is Hilbert–Schmidt and

   ```text
   K_N(D₀)=O(log(N+2) log log(N+3))=o((log N)²).
   ```

   Moreover the paired-block metric
   `G₀=⊕_(n≥1)[[1,r_n],[r_n,1]]`, with
   `r_n=(Φ_(2n)−Φ_n)/Φ_n∈(0,1)`, is **uniformly positive and
   boundedly invertible**. The earlier source result had only
   positivity and injectivity. Its exact remaining defect is the
   full cross-frequency commutator `G₀D−D*G₀`.

2. The full determinant-bearing operator has eigenvalues `−1/z`
   for the nonzero XiC zeros `z`, with algebraic multiplicity. Its
   modulus-ordered eigenvalue partial sums obey

   ```text
   Σ_(j≤N)|λ_j(D)| = (1/(2π)+o(1)) (log N)².
   ```

3. Therefore the off-block operator obeys the unconditional capacity
   lower bound

   ```text
   liminf_(N→∞) K_N(R)/(log N)² ≥ 1/(2π).
   ```

   In particular `R` is neither trace class nor weak Schatten-one.
   Equivalently, its singular values have unavoidable logarithmic
   enhancement in the quantitative sense
   `limsup_(N→∞) N s_N(R)/log N ≥ 1/π` (allowing `+∞`).
   This conclusion does **not** assume RH: it uses the complete Xi
   divisor, wherever its zeros lie inside the critical strip.
4. **Cross-route positive survivor.** Let `K` be the Poisson/Mertens
   prime Gram operator and replace its `x_p=log log p` clock by the
   actual theta action `Φ_p`:

   ```text
   K_Φ(p,q) = (pq)^(-1/2) sech²((Φ_p−Φ_q)/2).
   ```

   Then `K_Φ` is bounded and positive, `K_Φ−K` is trace class with
   trace zero, and `K_Φ` has the same essential spectrum `[0,4]`.
   This is a source-derived prime-to-theta **clock** alignment. It
   does not identify `K_Φ` with the determinant-bearing theta inverse.
5. **Frequency admission is discrete.** Extend the action expression
   formally to a real frequency `r`:

   ```text
   Φ(r)=∫_ℝ (1−cos(2πrF(x)))dx.
   ```

   This nonnegative integral is finite **if and only if** `r∈ℤ`.
   Thus the theta clock is intrinsically a lattice action; its
   prime values admit endpoint cancellation, while ordinary
   differentiation through real frequency is unavailable.

Thus every stable opposite-frequency pair in the source-derived
Fourier quotient has too little spectral mass to carry the Xi zero
density. The full logarithmic spectral mass is necessarily created by
nonperturbative coupling **between distinct frequency pairs**. This
identifies where a source-side reality proof must act; it does not
prove the cross-frequency coupling has the needed sign.

## Theta tail gives the sharp CDF-action clock

The corpus's `thetaCuspFullSource_le_envelope` and
`thetaCuspFullSource_ge_envelope` state, on `x>0`,

```text
c exp(9x/2−π exp(2x)) ≤ k(x)
                         ≤ C exp(9x/2−π exp(2x)).
```

Evenness gives the reflected bound. Absorbing the linear term into
the double exponential, choose fixed `a∈(0,π)` and `C_a` such that
`k(x)≤C_a exp(−a exp(2|x|))` for sufficiently large `|x|`.
Writing `ρ=k/∫k` and `τ(x)=∫_(x)^∞ρ`, one integration of this
monotone envelope gives
`τ(x)≤C'_a exp(−a exp(2x))` for `x≥0`, after adjusting constants.

Fix `n≥3` and take
`L_n=(1/2)log((3/a)log n)`, enlarged to a fixed nonnegative
cutoff if needed. On `|x|≤L_n`, the CDF-action integrand is at most
`2`, contributing at most `4L_n`. On `x>L_n`, periodicity and
`F(x)=1−τ(x)` give

```text
1−cos(2πnF(x)) = 1−cos(2πnτ(x))
                  ≤ 2π²n² τ(x)².
```

The same bound holds on the negative tail by reflection. Since
`a exp(2L_n)=3 log n`, the integrated two-tail contribution is
uniformly bounded (in fact tends to zero). Hence
`Φ_n=O(log log n)`. This suffices for the operator-ideal argument, but
the coefficient of the double logarithm is also determined.

For the sharp constant, let
`ε_n=4 log log n/log n` and, for sufficiently large `n`, set

```text
L_n^± = (1/2)log(((1±ε_n)log n)/π).
```

Their difference is `O(ε_n)`. The lower envelope yields
`n ρ(L_n^-)≥c (log n)^(9/4) exp(ε_n log n)`, which tends to
infinity faster than any fixed power of `log n` below `25/4`.
Strict log-concavity and evenness of `k` make `ρ` decreasing on the
positive half-line. Integrating the phase by parts on
`[-L_n^-,L_n^-]` therefore gives

```text
|∫_(-L_n^-)^(L_n^-) cos(2πnF(x)) dx|
  ≤ C/(n ρ(L_n^-)) = o(ε_n).
```

Indeed, the boundary terms are each bounded by
`1/(2πnρ(L_n^-))`, while the variation of `1/ρ` on the symmetric
interval is at most `2/ρ(L_n^-)`. Thus the inner contribution to
`Φ_n` is `2L_n^-+o(ε_n)`.

For the outer tail, retain the exact `π` in the upper envelope.
Substituting `v=exp(2x)` into its tail integral gives, for large `x`,

```text
1−F(x) ≤ C (exp(2x))^(5/4) exp(−π exp(2x)).
```

At `L_n^+`, `n(1−F(L_n^+))` is bounded by a fixed power of
`log n` times `exp(−ε_n log n)=(log n)^(-4)`. Integrating the squared
tail bound shows the total contribution from `|x|>L_n^+` is
`o(ε_n)`. The two annuli between `L_n^-` and `L_n^+` have total
length `O(ε_n)` and integrand at most `2`, so contribute
`O(ε_n)`. Since all contributions are nonnegative,

```text
2L_n^- + o(ε_n) ≤ Φ_n ≤ 2L_n^+ + O(ε_n).
```

Both endpoints equal `log log n−log π+O(ε_n)`, proving

```text
Φ_n = log log n − log π + O(log log n/log n).
```

The previously proved paired-block inequalities give
`0<r_n<1`. The sharp action law also gives
`Φ_(2n)−Φ_n=O(log log n/log n)` and
`Φ_n∼log log n`, hence `r_n=O(1/log n)→0`.
All sufficiently late blocks therefore satisfy `r_n≤1/2`;
the finitely many earlier blocks have a positive minimum
`1−r_n`. Thus there is a single `c>0` with
`cI≤G₀≤2I`, and `G₀⁻¹` is bounded. This does not make `D`
self-adjoint in that metric: only its diagonal `H_n` blocks are
symmetrized, while the cross-frequency defect remains.

For prime `p`, this calibrates the Mertens coordinate
`x_p=log log p` by a fixed offset. It is a source-derived coordinate
match, not an operator transport or Xi-divisor identity.

The operator corollary follows from the same local trace-class argument
as the [Poisson/Mertens defect](stc-mertens-trace-class-xi-divisor-barrier.md).
On prime harmonic cell `I_p`, the theta-calibrated step coordinate
`φ_Φ(y)=Φ_p+log π+B` satisfies

```text
φ_Φ(y)−y
  = (x_p+B−y)+(Φ_p−x_p+log π)
  = O((1+y)e^(-y)).
```

The analytic-kernel Taylor expansion on unit spatial blocks still has
summable trace norms: its former `e^(-j)+e^(-k)` majorant becomes
`(1+j)e^(-j)+(1+k)e^(-k)`. Initial blocks are finite rank modulo the
smooth Wiener–Hopf kernel. Thus `UK_ΦU*−W_h∈S₁`, and subtracting
the proved `UKU*−W_h∈S₁` gives `K_Φ−K∈S₁`. The diagonal of
both prime matrices is `1/p`, so their trace-class difference has
zero trace. Positivity follows from positive definiteness of
`sech²((a-b)/2)` for arbitrary real labels `a,b`; boundedness follows
from the trace-class comparison with bounded `K`. Compact
equivalence gives `σ_ess(K_Φ)=[0,4]`.

For the discrete-admission law, if `r∉ℤ` then `F(x)→1` as
`x→+∞`, so the integrand tends to
`1−cos(2πr)>0`; its integral diverges. If `r∈ℤ`, the integrand
vanishes quadratically as `F(x)→0` on the left and as `F(x)→1`
on the right. The source's double-exponential tail makes both
tails integrable, while the finite middle interval is harmless.
Equivalently, in quantile coordinates `q(t)dt=dx` has infinite mass
at both endpoints, and an integer character cancels both.

The `H_n` block is exactly

```text
(1/(2πn)) [[Φ_n, Φ_(2n)−Φ_n],
           [−(Φ_(2n)−Φ_n), −Φ_n]].
```

The CDF-action ceiling alone gives
`|Φ_(2n)−Φ_n|≤Φ_(2n)+Φ_n=O(log log(n+3))`; thus the block trace
norm is `O(log log(n+3)/n)`. Its squared singular values are
summable, proving
`D₀∈S₂`. Truncate after `N` blocks. The trace norm of the head is
`O(Σ_(n≤N) log log(n+3)/n)=O(log N log log N)`; the tail operator
norm is `O(log log N/N)`. The Ky Fan norm of the tail is at most
`N` times that operator norm. This proves item 1.

## The Xi divisor forces logarithm-squared mass

The source determinant and algebraic-multiplicity theorems identify
the nonzero eigenvalues of `B` as `−1/z`, where `XiC(z)=0`, with
the zero's multiplicity. Because `Be=0`, the decomposition
`ℂe⊕e⊥` makes `B` block upper triangular with diagonal blocks
`0,D`. The nonzero eigenvalues and their algebraic multiplicities
therefore agree for `B` and `D`.

Write an XiC zero as `z=γ+i(1/2−β)`, corresponding to a ξ zero
`β+iγ`. The classical critical strip gives `|Im z|<1/2`.
The unconditional Riemann–von Mangoldt theorem gives
`N_+(T)∼T log T/(2π)` upper-half ξ zeros, counted with
multiplicity; conjugation gives the same lower-half count. Partial
summation therefore gives

```text
Σ_(XiC(z)=0, |Re z|≤T) 1/|Re z|
  = (1/(2π)+o(1)) (log T)².
```

Replacing `1/|Re z|` with `1/|z|` changes the sum by a bounded
amount, since `|Im z|<1/2` and the reciprocal-cube zero sum
converges under the same count. The number of terms is
`(T/π+o(T))log T`. Ordering the reciprocals by modulus and
inverting this count yields item 2; multiplicities remain included.

For every compact operator, Weyl's inequality majorizes the absolute
eigenvalue partial sum by `K_N`, even when the operator is nonnormal.
The Ky Fan triangle inequality gives

```text
K_N(R) ≥ K_N(D)−K_N(D₀)
       ≥ Σ_(j≤N)|λ_j(D)|−K_N(D₀).
```

Item 1 is lower order than item 2, proving item 3. A trace-class
operator has bounded `K_N`; a weak-Schatten-one operator has
`K_N=O(log N)`. Both are excluded by the proved lower bound. If the
displayed singular-value `limsup` were smaller than `1/π`, then
eventually `s_N(R)≤c log N/N` for some `c<1/π`; summation would give
`K_N(R)≤(c/2+o(1))(log N)²`, contradicting item 3.

## Meaning for source transport

The [Poisson/Mertens prime defect](stc-mertens-trace-class-xi-divisor-barrier.md)
is trace class, whereas the theta quotient's missing cross-frequency
piece `R` lies outside weak Schatten-one. Bounded left/right transport
of that prime defect, even after a trace-class correction, cannot
produce `R`. The universal continuum bulk, a singular clock change,
or other non-trace-class completion data would have to enter.

The genuine RH gate remains a **theta-specific orientation of this
global cross-frequency coupling**, equivalently a proof that actual
Xi eigenmodes have neutral boundary flux. The theorem locates the
required spectral capacity but supplies no sign or zero exclusion.
The [theta derivative dark-packet deformation](../../3-formalized/theta/theta-derivative-dark-divisor-packets.md)
shows why density capacity alone cannot orient zeros: a positive
source can retain the actual real-zero divisor and theta-scale tail
while acquiring an off-real packet. The exact modular source identity,
not just its tail class, must enter the sign argument.

**Audit:** The paper proof uses existing literal-source and Xi-divisor
Lean theorems plus standard compact-operator inequalities. The CDF
action, block decomposition, and Ky Fan lower bound are not yet
formalized in Lean. External novelty has not been established.
