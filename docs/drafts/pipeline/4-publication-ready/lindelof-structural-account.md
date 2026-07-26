# A structural account of the Lindelöf hypothesis

**Status:** none of the results below improves `μ(1/2) ≤ 13/84`. All are barrier, reduction, or
calibration theorems. All exponent statements are Lean-certified with axioms
`[propext, Classical.choice, Quot.sound]` in `formal/GaloisForLFunctions/HTGeometry/`.

---

## 0. The object

From the approximate functional equation, `μ(1/2) = (b − 1/2)/2` where `t^{b/2}` bounds the critical
block `Σ_{n∼√t}n^{−it}`. Writing `N = √(t/2π)`, an exponent pair `(κ,λ)` gives `N^{κ+λ}`, so

> **`μ(1/2) = (κ+λ − 1/2)/2`,** and LH is `κ+λ = 1/2`.

Verified: Weyl `(1/6,2/3) → 1/6`; Bourgain `(13/84,55/84) → 13/84`.

---

## 1. The exponent-pair semigroup is stationary at every record

The van der Corput processes act as `A(κ,λ) = (κ/(2κ+2), (κ+λ+1)/(2κ+2))`, `B(κ,λ) = (λ−1/2, κ+1/2)`.
`B` is an involution preserving `κ+λ`; only `A` can move it.

**Theorem 20.** `A` decreases `κ+λ` iff `(κ+λ)(2κ+1) > κ+1`. On the fixed-point line of `B`
(`λ = κ+1/2`, where `μ = κ`) this is `8κ²+4κ−1 > 0`, i.e. `κ > (√3−1)/4 = 0.18301…`.
**All four landmark pairs — Weyl `1/6`, Bombieri–Iwaniec `9/56`, Huxley `32/205`, Bourgain `13/84` —
lie on that line and below that threshold.** `A` strictly worsens every one, and the margin grows as
the record improves.

**Theorem 21.** Convexity and `B`-closure give a canonical form: the midpoint of any pair and its
`B`-image is `(μ, μ+½)`, again an exponent pair with the same `μ`. The line of symmetry carries the
full strength of the set.

**Theorem 22.** The induced line-to-line map is `T(μ) = (4μ+1)/(8μ+8)`, whose fixed points are the
roots of `8μ²+4μ−1` — the threshold again. `T` attracts from **both** sides, so the line is a
dynamical trap at `0.18301`, worse than every result since 1921.

**Theorems 23, 25.** The `A`-step obeys `epMu(A(κ,λ)) = (4μ+1)/(8κ+8)` and `λ ≥ 1/2` forces `κ ≤ 2μ`,
giving the floor `R(μ) = (4μ+1)/(16μ+8)`, whose iteration from the convexity bound is
`1/4 → 1/6 → 5/32 → 13/84 → …` with limit `(√5−1)/8`. **Saturation requires `λ = 1/2` exactly, and
`(1/2,1/2)` is the only known such pair** — so the chain runs for exactly one step, which is Weyl's
theorem, and its limit is the exponent-pair conjecture.

---

## 2. The frontier object

**Theorem 28.** The critical phase is a quadratic on blocks of length `N^{1/3}` and has no finite
degree across blocks (Theorem 29: every Taylor order sweeps exactly one power of `N`). Splitting into
`N^{2/3}` coherence blocks: **incoherent summation gives Weyl's `5/6`; coherent summation gives the
Lindelöf `1/2`. The entire gap is the block sum.**

**Theorem 37.** The block phases are `N√(2a/q)`; grouping by the reduced fraction gives a **Farey
dissection of order `L = N^{1/3}`**, with the frontier object

    Σ_{r ∈ F_L} A(r)·e(N√(2r)) ,    A carrying Gauss-sum data.

**Theorem 40.** There are two levels of cancellation. Within-arc square-root cancellation is worth
**exactly nothing**; across-arc alone gives `N^{2/3}`; **both together give exactly `N^{1/2}` = LH.**

**Theorem 43.** The neutrality is a conservation law: `Σ_{q≤L}φ(q)q^{−s} ≍ L^{2−s}` compensates the
within-arc gain exactly, for **any** phase. No sharpening of within-block estimates can ever move such
an exponent.

**Theorems 47–48.** The frequency set `{√(2a/q)}` is optimally spaced (distinct resonances differ by
`≫ N/(a₁a₂)`, because a nonzero integer is at least `1`) and has **minimal additive energy**, with the
largest `√d`-class exactly at the threshold. Every structural feature is optimal.

---

## 3. The obstruction

**Theorem 39.** The root-mean-square of the frontier sum is **exactly** `N^{1/2}` — the Lindelöf
value. **LH is a pure large-values statement.**

**Theorems 49, 50.** All five bridges from mean-value to pointwise are closed: Sobolev returns the
trivial bound at every scale (the variation term carries no `1/H` and `|F'| ≍ \log N·|F|`); Jensen is
closed by the zero geometry; large values + moments is circular; mollification re-enters the moment
problem; **amplification collapses to resonance and delivers exponent `0`** (Gál sums are
subpolynomial).

**Theorem 52.** The gap is **self-similar**: the mean square of the resonance sums over `q` is
*exactly* the intermediate target, just as the mean square of the frontier sum is exactly LH. No
reduction moves the gap to an easier level.

**Theorem 53.** Emptying the exceptional set `E_δ` by the `2k`-th moment needs `k > 1/δ`; no finite
order works uniformly, so counting requires all moments — which is LH.

**Theorem 55 (capstone).** `n^{−it}` is simultaneously **multiplicative** and **archimedean-smooth**.
Every method uses one property: the smooth family (van der Corput, exponent pairs, decoupling) is
stationary at the self-dual block; the multiplicative family (Halász, moments, resonance,
amplification) is extremal at characters, and `n^{−it}` is a character. **No tool sees both, and the
two families do not add: the smooth family's best plus the entire multiplicative family is still below
the target.**

**Theorem 56.** The unique classical couplings of the two properties are the functional equation and
the explicit formula. Both are priced: the functional equation is stationary at one level and
sub-polynomial at every deeper level (Theorems 41–42, Erdős–Ford); the explicit formula is closed by
the zero geometry. **LH is posed exactly at the fixed point of the only structure that could prove
it.**

**Theorems 58, 59.** The mechanism exists in the **conductor** aspect — Burgess uses multiplicativity
and *periodicity* to complete short sums and invoke Weil. `n^{−it}` is aperiodic, and completion cannot
be manufactured: small moduli have too few free parameters (`(ℤ/qℤ)^*` has rank `ω(q)`), and the
smallest modulus with `ω(q) ≥ π(N)` is the primorial `e^{N(1+o(1))}`, at which Burgess's threshold
`e^{N/4}` exceeds the available block `N` **exponentially**.

**Theorems 60, 61.** The AFE block parameter is pinned to `x = 2θ₀` — the saving requires `x < 2θ₀`,
nontriviality requires `x > 2θ₀` — and at that point **every dyadic block contributes exactly
`t^{θ₀}`**. The approximate functional equation is the identity map on the exponent. All progress must
come from the exponential-sum side.

---

## 4. Calibration

**Theorems 44, 45.** In the shared block-exponent currency (both problems start at the classical `5/6`):

| | classical | record | target | distance | covered | fraction |
|---|---|---|---|---|---|---|
| Lindelöf | `5/6` | `17/21` | `1/2` | `1/3` | `1/42` | **`1/14 ≈ 7.1 %`** |
| divisor | `5/6` | `339/416` | `3/4` | `1/12` | `23/1248` | `23/104 ≈ 22.1 %` |

**LH is exactly four times further from the classical exponent than the divisor conjecture**, and the
divisor problem is three times further along. Solving it completely leaves three quarters of LH's
distance untouched.

---

## 5. The one actionable target

**Theorem 34.** `Σ_a ε(a,q)e(N√(2a/q)) ≪ q^{1/2+ε}` uniformly for `q ≤ N^{1/3}` implies **`μ ≤ 1/12`**,
beating `13/84` and covering **half** of LH's distance.

**Theorems 35, 36.** Four classical tools fail on it with computed margins: van der Corput
(`|g''| ≥ N^{1/3}`), Poisson (dual longer by `≥ N^{1/2}`), Pólya–Vinogradov (phase faster than the
character saving), Weyl differencing + Weil (critical only at `κ = 1/3`; Weil unusable at every shift).

---

## 5a. The positive results (cycles 180–189)

**Theorem 80.** Substituting `s = r+m` in the principal arc's cubic-form sum
`Σ_{r,m≤L}e(rm(r+m)/L²)` yields, for each `s`, a chirp with small coefficient `α = −s/L²`; the
second-derivative test gives `√s + L/√s`, summing to `L^{3/2}` — **exactly the arc's Lindelöf
requirement. The principal arc is not an obstruction.**

**Theorem 81.** The same argument applies at every arc, giving `S_q ≪ L^{3/2}/q`, and the total over
all arcs is exactly `L^{5/2}` — **Weyl. The within-arc half of the problem is proved, and attaining it
everywhere still gives only Weyl**, confirming Theorem 43 constructively.

**Theorem 82.** Dividing out the proved factor `L^{3/2}`, LH becomes
`Σ_{a/q∈F_L}(1/q)ε_q(a|q)e(N√(2a/q)+θ_{a,q}) ≪ (\log L)^{O(1)}`:
**Weyl is its `ℓ¹` bound, Lindelöf its `ℓ²` bound.**

**Theorems 83–84.** The mass localises to the single dyadic range `q ∈ [L/2,L]`, where the phase
factors as `N√(2a)·q^{−1/2}` — **a genuine bilinear phase** (correcting D56, which had ruled this out
at the wrong scale).

**Theorem 85 (as corrected by E42).** Optimal mod-1 spacing of the frequencies `{N√(2a)/√L}` gives
`μ ≤ 1/12` — **beating Bourgain, falling short of LH by `L^{1/2}`** — and coincides exactly with
Theorem 34's intermediate target and Theorem 40's across-arc-only regime.

**Theorem 86.** The remaining `L^{1/2}` requires simultaneous cancellation in both variables — the
**double large sieve**, Bombieri–Iwaniec's own instrument. The formal reduction and the cycle-97
literature reading arrive at the same place independently.

---

## 5b. The scale-by-scale account (cycles 205–243)

Write the critical sum's dyadic blocks as `M = t^c`, `0 < c ≤ 1/2`.  An exponent pair `(κ,λ)` bounds
the block by `t^{κ + c(λ−κ)}`; the Lindelöf requirement is `t^{c/2}`.  The **deficit**

> **`D(P, c) = κ + (λ − κ − 1/2)·c = μ(P) + d(P)·(c − 1/2)`,  `d(P) := (λ−κ) − 1/2`**

organises everything.

**Theorem 113 (length-reflection law).** The deficit is the pointwise exponent corrected by the pair's
displacement from the line of symmetry times the length deficit `c − 1/2`.

**Theorem 114.** At `c = 1/2` the displacement term vanishes identically: the exponent-pair region is
two-dimensional, but the coefficient of its second dimension is `c − 1/2`, and the AFE forces
`c = 1/2`.  Every mechanism exploiting that dimension is priced at zero there.

**Theorem 116.** The van der Corput `B`-process satisfies `D(B(P), c) = D(P, 1−c)`: it *is* the
reflection `c ↦ 1−c`, whose fixed-point set — the line of symmetry — is exactly the set of pairs whose
deficit is length-independent.  All four landmark pairs lie there.

**Theorems 129–130.** For a `B`-closed family the support function `h(c) = min_P D(P,c)` satisfies
`h(c) = h(1−c) ≤ h(1/2)`: **the critical scale is where the region is hardest**, and `h(1/2) = 0`
forces `h ≡ 0`, i.e. the corner `(0,1/2)`.

**Theorems 120–122.** A covering by pairs valid at every length is worth exactly `min_P μ(P)`; the
covering architecture's entire value comes from range-restricted sources, and a restriction is worth
exactly the displacement discount `d(P)(1/2 − x₁)` at its threshold.

**Theorems 127, 148, 181–182.** Three routes — the covering architecture, the Farey-numerator
square-root target, and the vanishing abscissa `σ*` — all terminate at the corner `(0,1/2)`, which by
Theorem 193 is the unique zero of `μ` on `{κ ≥ 0, λ ≥ 1/2}`.

**Theorems 136, 215–217.** The `A`-process's productivity threshold at a line pair is `T(κ) = 2κ(1+2κ)`,
**increasing** in `κ`: improving the record shrinks the range where the process is productive, at rate
`> 2`, and at `κ = 0` the range is empty.  The classical tower has closed form
`κ_k = 1/(2^{k+2}−2)`, `λ_k = 1 − (k+1)/(2^{k+2}−2)`, `μ_k = 1/4 − k/(2(2^{k+2}−2))`, thresholds
`1/(k+2)`, and consecutive members exchange optimality at `2^{k+2}/((k+1)2^{k+2}+2) = 4/9, 8/25, 16/65`.
**Its exponents increase to `1/4`, the midpoint of the two trivial pairs — the tower converges to the
trivial bound at the one scale that decides the problem.**

**Theorems 207–209.** Every published estimate has the form `t^aM^b`; through the AFE its value is
`a + (b−1/2)/2` (critical block) or `a/(2(1−b))` (crossover), both positive whenever `a > 0`.  **LH
requires the first `t`-free bound in the subject's history**, and a century of work is the reduction of
`a` from `1/6` to `13/84`.

**Theorems 96–110 (architecture pricing).** Bourgain's Section-3 window is `[c−6θ, 6θ−b]`, centred at
the regime crossover `(c−b)/2 = 5/12` independently of `θ`, of width `12θ−(b+c)`; the spacing
estimates go dark at `(b+c)/12 = 11/72`.  The Section-4 covering has reach `(θ−β)/(α−1/2)` and floor
`max(43/279, 277/1792) = 277/1792`; **the record sits `1/5376` above it**, and Huxley's bound cannot be
removed (it is needed by `11/39816`).

**Theorems 157, 164–170 (off the critical line).** `μ(1/2) ≤ μ(σ) + (σ−1/2)/2`; the transfer band at
`σ` has width `(σ−1/2)(1/2−2θ)`; the reverse direction `μ(1/2) ≥ μ(σ)/(2(1−σ))` makes a single point of
positivity in `(1/2,1)` a refutation of LH.  The ANTEDB's value at `σ = 7/10` is `218/3005`, leaving
`4489/252420` of the band.

**Theorems 174–179, 195–197 (two more coordinates).** The vanishing abscissa `σ* = inf{σ : μ(σ)=0}`
satisfies `1/2 ≤ σ* ≤ 1` unconditionally, LH is `σ* = 1/2`, and `μ(1/2) ≤ (σ*−1/2)/2` makes the record
equivalent to `σ* ≤ 17/21`.  In measure, `|E_δ| ≪ T^{M−Aδ}`, and at the record the residual is
`T^{6459/70000}`.

**Theorems 192–194, 204–206 (the symmetric position).** The resonance method's logarithmic exponent is
`1/2` for every resonator length against the `1` a refutation needs; the moment method's floor lies
*above* the record while the covering architecture's lies *below* it.  **The record occupies the narrow
band between the two floors, and no known family has a floor at zero.**

## 6. Methodological record

Seven claims were withdrawn during the campaign, each caught by the same rule: **any derived exponent
below `13/84` is wrong until every input's domain of validity is checked.** The rule caught a naive
decoupling price (`1/16`), a chord used outside `[2,6]` (`3/20`), a box-optimised displacement
(`17/110`), a formula read to its limit (`1/2`), a self-similar recursion (`1/12`), a transfer to
weighted phases (the divisor conjecture), and — applied to the campaign's own results — an
unjustified corollary about the block range (E37, leading to Theorems 60–61), a misattributed
provenance for the Trudgian–Yang moment bounds (E39), and a wrong dual-sieve arithmetic (E42, which
relocated the missing input's value from `0` to `1/12`).

**A non-mathematical failure (E40).** The `HTGeometry` umbrella failed to build for sixty-four cycles
because `blockExponent` collided with a pre-existing definition; per-module builds masked it. Standing
practice now: **`lake build +Module` is not verification — build the umbrella, and scan new top-level
names against the area.**
