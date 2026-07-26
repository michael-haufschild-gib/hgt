# Lindelöf campaign — successor summary

Working log: `lindelof-hypothesis-campaign.md`, 197 cycles, 90 results, 14 corrections, 61 dead
routes. Consolidated account: `4-publication-ready/lindelof-structural-account.md`. This file is the
short version.

**Bottom line: LH is neither proved nor disproved. `μ(1/2) ≤ 13/84` (Bourgain 2017) stands.**

---

## 1. Read this first — the standing rule

> **Any exponent derivation in this campaign that yields a value below `13/84` is wrong until the
> domain of validity of every input has been checked explicitly. Compute the value, compare it to
> `13/84`, and only then decide whether it is a theorem.**

This rule has caught **seven** errors that nothing else caught: D51 (`1/16`), E24 (`3/20`), E27
(`17/110`), E30 (`1/2`), D52 (`1/12` by recursion), E35 (the divisor conjecture), and — applied to the
campaign's own Theorem 57 — E37 (an unjustified corollary, which led to Theorems 60–61). **Standing
practice since cycle 154: evaluate every formula in the corpus at the boundary of its stated range and
check against `13/84`.** E38 later corrected Theorem 69's scope by the same discipline.

Corrections to earlier cycles: **E30** (an exponent formula read outside its domain), **E32/E33**
(Theorem 38 withdrawn — a Farey arc's *sum of moduli* is not its contribution), **E34** (the
specification's S4 is not absolute), **E35** (the coherence decomposition does not transfer to
weighted phases), **E36** (algebraic resonance count `L log L`, not `L^{3/2}`).

---

## 2. The chain — what the campaign proved about the object

    ζ(1/2+it)  →  critical block Σ_{n∼√t} n^{-it}          μ = (b − 1/2)/2, b the block exponent
      →  coherence blocks of length N^{1/3}                 Thm 28: Weyl = incoherent, LH = coherent
      →  theta sums Θ(α_r) at resonances α_r ≈ a/q          Thm 30: saving needed = one factor of L
      →  Farey dissection over F_{N^{1/3}}                  Thm 37: Σ_{r∈F_L} A(r)e(N√(2r))
      →  two levels of cancellation                         Thm 40: within-arc is worth **nothing**
      →  frequency set S = {√(2a/q)}                        Thms 47–48: optimal spacing, minimal energy

**Three independent derivations of Weyl's `5/6`** (correlation bridge, incoherent block sum, theta
resonance count) — `weyl_three_ways`. The chain reproduces Voronoi's `Δ(x) ≪ x^{1/3}` as well
(Thm 44).

**Key numbers, all Lean-certified:**

| | value |
|---|---|
| classical / incoherent block exponent | `5/6` |
| Bourgain's record | `17/21 = 0.80952` |
| divisor-problem record `x^{131/416}` | `339/416 = 0.81490` |
| divisor conjecture | `3/4` |
| **Lindelöf** | **`1/2`** |
| progress toward LH | **`1/14 ≈ 7.1 %`** |
| progress toward the divisor conjecture | `23/104 ≈ 22.1 %` |
| LH's distance vs the divisor conjecture's | **exactly `4×`** |

---

## 3. The taxonomy (Theorem 51) — every route, priced

**(a) Direct pointwise.**

* *van der Corput / exponent pairs*: the `A`-process is inert at every record (Thm 20, threshold
  `(√3−1)/4`); the optimum is confined to the line of symmetry (Thm 21) which is a two-sided attractor
  (Thm 22); the machinery's floor is `(√5−1)/8` in relaxation (Thm 23) and **`1/6` realisably**
  (Thm 25 — only one `λ = 1/2` pair is known, and the family's limit *is* the exponent-pair
  conjecture); **within-block improvements are universally neutral** (Thm 43).
* *algebraic / Weil–Deligne*: reaches an `L^{−1}\log L` fraction of the resonances, delivers `L²`
  (Thm 46).

**(b) Mean value plus a bridge.** The mean square is already the Lindelöf value (Thm 39). All five
bridges closed: Sobolev (Thm 49, trivial at every scale), Jensen (zero-geometry barrier), large values
+ moments (circularity), mollification (moment re-entry), amplification (Thm 50, collapses to
resonance, exponent `0`).

**Mechanism search.** A specification S1–S8 was derived from the barrier set; both admissible branches
were instantiated exhaustively and every instantiation blocked, by four unrelated obstructions:
density (smooth numbers), structure (no bilinear variables), strength (the gap to Baker), scale
(Erdős–Ford is logarithmic at every tower depth, Thm 42).

---

## 4. The one actionable target

> **`Σ_{a} ε(a,q)·e(N√(2a/q)) ≪ q^{1/2+ε}` uniformly for `q ≤ N^{1/3}`  ⟹  `μ ≤ 1/12`.**

This **beats Bourgain** (`1/12 = 0.0833 < 0.1548`), is strictly weaker than LH, and covers **half** of
LH's distance — twice the entire divisor conjecture (Thm 34, Thm 45). Four classical tools have been
priced on it and all four fail with computed margins (Thms 35–36): van der Corput (`|g''| ≥ N^{1/3}`),
Poisson (dual longer by `≥ N^{1/2}`), Pólya–Vinogradov (phase faster than the character saving), Weyl
differencing + Weil (critical only at `κ = 1/3`; Weil unusable at every shift).

---

## 5. Do not re-attempt

* Voronoi expansions inside a second summation (E19, D52 — worth the divisor problem itself).
* Recursing the coherence decomposition (D52) or the `√d`-classes (D58).
* Salié evaluation of the resonance `a`-sum (D53 — the phase is irrational, not a rational character).
* Unweighted Farey equidistribution against the square-root phase (D54 — the weight is not slowly
  varying).
* The **sixth** moment — subconvexity-neutral against `13/84`. Cheapest non-neutral index is `k = 4`;
  cheapest *relative* improvement is the **twelfth** moment (`m(6) < 13/7`, a 7.1 % improvement on
  Heath-Brown), but that is `Ω`-blocked at its input's limit.
* Higher-rank spectral input (rank gap `n(n−1)/2` grows).
* Disproof via moment lower bounds (implies `¬RH`, strictly harder).

---

## 6. Where the Lean lives

`formal/GaloisForLFunctions/HTGeometry/` — all axiom-clean `[propext, Classical.choice, Quot.sound]`,
wired into the umbrella.

*Exponent arithmetic:* `ExponentPairSelfDuality`, `CorrelationExponentBridge`,
`MultiplicationTableThinness`, `AveragedDivisorInput`, `TernaryShiftAverageExponents`,
`ModelBreakdownIndex`, `IvicSizeCriticality`, `ReductionLoopUniform`, `TwoLevelAFE`, and others.

*Analysis (built during this campaign, sum-side; the corpus's pre-existing van der Corput tower in
`RHTower/` is integral-side):* `WeylDifferencing` (differencing identity and bound),
`VanDerCorputInequality` (averaging identity, shift inequality, correlation bound, the method's floor),
`LinearExponentialSum` (`‖Σ e(αn)‖ ≤ 1/(2‖α‖)` from Jordan's inequality), `QuadraticWeylBound` (the
correlation of a quadratic phase is a geometric series).

**Known duplication:** `RHTower/GaussLattice.norm_geom_sum_le` already had the geometric core of
`LinearExponentialSum`. Search `norm_geom_sum|geom_sum_eq` as well as `distToInt|linear.*phase` next
time.


---

## 7. The structural account (cycles 148–167)

**Theorem 55 (capstone).** `n^{−it}` is both **multiplicative** and **archimedean-smooth**. Every
method uses one: the smooth family (van der Corput, exponent pairs, decoupling) is stationary at the
self-dual block; the multiplicative family (Halász, moments, resonance, amplification) is extremal at
characters, and `n^{−it}` is a character. **No tool sees both, and the two families do not add.**

**Theorem 56.** The unique classical couplings of the two properties are the functional equation and
the explicit formula. Both priced. **LH is posed at the fixed point of the only structure that could
prove it.**

**Theorems 58–59.** The mechanism exists in the **conductor** aspect (Burgess: multiplicativity +
*periodicity* ⟹ completion ⟹ Weil). `n^{−it}` is aperiodic, and completion cannot be manufactured:
small moduli lack free parameters, and the smallest modulus with enough is the primorial `e^{N}`, at
which Burgess's threshold `e^{N/4}` exceeds the block `N` exponentially.

**Theorems 60–61.** The AFE block parameter is pinned to `x = 2θ₀`, and there **every dyadic block
contributes exactly `t^{θ₀}`** — the functional equation is the identity map on the exponent.

**Theorems 62–64.** At the resonance sum, completeness holds and algebraicity fails; Fourier expansion
gives `T(q) = ε_q√q·⟨ĉ,χ₂⟩` with `ĉ` **flat** (`|ĉ_h| ≍ q^{−1/2}`, confirmed independently by Parseval
and stationary phase). **The target is: a flat unit vector is orthogonal to the Legendre symbol.**

**Theorems 66–67.** The stationary phase is the reciprocal `N²/(2k)`, which is the campaign's original
differenced logarithmic phase; and reciprocal ↔ square-root are **Poisson duals**. The
additive-divisor and exponent-pair programmes are exchanged by that duality — one object, two
coordinate systems.

**Theorem 68.** Every powerful tool requires an arithmetic hypothesis — periodicity (Burgess),
algebraicity (Weil), completeness+algebraicity (Weil at the resonance sum), rationality (Kuznetsov) —
and the object satisfies none, **because `t` is real**.

**Theorems 65, 69.** From below: the best construction is `N^{o(1)}`, and this is **forced**, not a
limitation of technique — simultaneous approximation caps the resonant primes at `≍ \log t`, phase
accumulation caps usable products at `Ω(n) ≲ 1/η`, product `(\log N)^{1/η}`. **LH sits strictly between
construction (`0`) and bound (`17/21`), and the gap below (`1/2`) exceeds the gap above (`13/42`).**

**Conjugation principle (Thms 52, 66, 67, D60).** Every change of description preserves the
pointwise/mean-value gap, the phase family, the exponent, and the genericity. **The reduction
apparatus is closed.**

### The account in one line

> *The analytic tools are stationary at the object and the arithmetic tools cannot see it, because the
> object's only parameter is real.*


---

## 8. **READ THIS BEFORE ANYTHING ELSE** — the corpus already formalises Bourgain (cycles 193–197)

`formal/GaloisForLFunctions/RHTower/` contains **64 `Bourgain*` modules**: a `sorry`-free
formalisation of Bourgain's `13/84` proof — the sixfold cloud
(`bourgainMomentCurve h = (h, h², h^{3/2}, h^{1/2})`), the four-dimensional Bombieri–Iwaniec double
large sieve, the Gaussian spacing analysis, the decoupling inputs, the Section-4 exponent endgame, and
the reduction to `riemannZeta`.

**The campaign did not find this until cycle 193** and spent cycles 186–192 re-deriving the double
large sieve abstractly, producing a convention-dependent exponent that had to be withdrawn (E43).
**Standing rule, now mandatory: `rg -il` the corpus for the *name of the method* before analysing it,
not only for the names of the objects.**

### The corpus's exact open frontier

`RHTower/BourgainSpacingExponentArithmetic.bourgain_spacing_endgame` is the only hypothesis-carrying
capstone, conditional on

    hDirect : T^{3/7} ≤ M → S⁶ ≤ M³·T^{13/14}
    hMiddle : T^{5/12} ≤ M → S⁶ ≤ M⁴·T^{1/2}
    hLow    : M < T^{5/12} → S⁶ ≤ M²·T^{4/3}

### What the campaign added there (Theorems 89–90, Lean-certified)

At the critical block `M = T^{1/2}`:

| `hDirect`'s `T`-exponent | block exponent | `μ` | meaning |
|---|---|---|---|
| `3/2` | `1` | `1/4` | trivial |
| **`13/14`** | **`17/21`** | **`13/84`** | **Bourgain's record — exactly** |
| `0` | `1/2` | `0` | **exponent pair `(0,1/2)` ⟹ Lindelöf** |

* **Theorem 89:** the campaign's 195-cycle reduction and the corpus's Bourgain formalisation meet at
  **one hypothesis with one exponent**; `13/14` is the entire remaining gap.
* **Theorem 90:** `hDirect` at exponent `0` **is the exponent-pair conjecture**, so §3's Theorems
  20–25 are a complete pricing of the corpus's own target. Bourgain's record is `8/21 ≈ 38 %` of the
  way from trivial to that conjecture.

### A target that is **not** reachable — do not attempt it

`RHTower/BourgainParabolaTwoTorusL12`'s docstring says decoupling "improves this baseline to
`H^{6+ε}`". **For the two-torus parabola with unit coefficients the baseline `H^{9}` is *sharp*** —
`∫_{T²}|Σ_{n≤H}e(nu+n²v)|^{12} = J_{6,2}(H) ≍ H^6 + H^9 = H^9`, and `bourgainIndex h = h+1` confirms
unit spacing. The three-power gain belongs to Bourgain's **four-dimensional** cloud, not to that file's
2D object (cycle 195).

### Where a successor should work

1. `hDirect` in `BourgainSpacingExponentArithmetic.lean` — the whole gap is its exponent.
2. The four-dimensional cloud `BourgainSixfoldCloud` and its decoupling inputs.
3. **Not** the 2D parabola baseline (sharp), and **not** re-deriving the reduction to these objects —
   the campaign has done it twice, independently, and both routes agree.
