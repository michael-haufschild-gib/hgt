# Hurwitz quadratic tail-independence — Lean formalization status

Formalizing two proven paper cards:
- `docs/drafts/pipeline/2-fully-proven/new/hurwitz-quadratic-n2-density-shadow.md` (N=2, the minimal
  collision `Y₀Y₂−Y₁²`).
- `docs/drafts/pipeline/2-fully-proven/new/hurwitz-quadratic-all-n-tail-independence.md` (all finite N;
  subsumes N=2). **Target:** for `Re(s)>1, s∉ℤ`, every finite shift ladder `{ζ(s+k,a)}_{0≤k≤N}` has no
  nonzero `ℂ(a)`-polynomial relation of total `Y`-degree ≤ 2.

## Architecture (mirrors Böttcher/u0: abstract engine + isolated analytic core)

The card's "formalization shape": `finite relation → orbit polynomial p(T)=P(R+T·H) → coefficient
obstruction → independence`. Decomposition:

- **Abstract engine** (pure algebra, no Hurwitz zeta): orbit root-counting + monodromy-scalar arithmetic
  + (todo) quadratic weight-grading + row descent.
- **THE analytic core** (the single deep input, used in 3 places — Lemma-1 pole tower, N=2
  finite-difference, exponent filtration): *a non-integer complex power `x^α` (α∉ℤ) is independent from
  the integral-power/meromorphic germs.* This is the Hurwitz analogue of u₀-transcendence /
  natural-boundary. NOT in mathlib. To be isolated as a named interface (like `hTranscendental`), then
  discharged.

## mathlib surface

- HAS: `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`, `Complex.Gamma_ne_zero`,
  `Complex.exp_eq_one_iff`.
- LACKS: `ζ(s,a)` as a function of **complex** a (mathlib's `hurwitzZeta` only has `a : UnitAddCircle`),
  its singular expansion `ζ(s+k,-n+x)=x^{-s-k}+R_{n,k}(x)`, fractional polylog `Li_α`, the a-monodromy.

## Done (axiom-clean: [propext, Classical.choice, Quot.sound])

- `Hurwitz/OrbitObstruction.lean` — `eq_zero_of_three_roots`, `orbit_eq_zero_of_three_distinct`
  (≥3 distinct orbit points kill a deg-≤2 p), `two_mul_coeff_one_of_pm_one`,
  `coeff_one_eq_zero_of_pm_one` (q=-1 order-two: odd coeff vanishes).
- `Hurwitz/MonodromyScalar.lean` — `monoScalar s = exp(-2πi s)`; `monoScalar_eq_one_iff` (q=1⟺s∈ℤ),
  `monoScalar_sq_eq_one_iff` (q²=1⟺2s∈ℤ), `monoScalar_three_distinct` (s∉ℤ ∧ 2s∉ℤ ⟹ 1,q,q² distinct
  ⟹ order-≥3 branch), `monoScalar_eq_neg_one` (s∉ℤ ∧ 2s∈ℤ ⟹ q=-1 ⟹ order-two branch). The card's
  descent dichotomy is governed exactly by `2s∈ℤ`.

## Next bricks

1. Quadratic weight-grading (algebra): `Q=Σ q_{ij}Y_iY_j`, `A_w=Σ_{i+j=w} q_{ij}`; `Q(H(x))=Σ_w A_w x^{-2s-w}`.
2. Distinct-(complex-)exponent independence = the analytic core, isolated as interface; in-application
   exponents `{-2s-w}∪{-s-k}∪{0}` are pairwise-distinct complex numbers under `Re(s)>1, s∉ℤ`.
3. Rational-Tail Independence (Lemma 1): `Σ r_j(n)H_n^{(s+j)}=R(n) ⟹ r_j=0`, via OGF `Σ H_n^{(u)}z^n =
   Li_u(z)/(1-z)`, pole tower at `μ_m=2πim`, `Γ(1-s-j)≠0`.
4. Abstract N=2 spine, then all-N row descent, then discharge the analytic core.

## Update — analytic core (exp form) landed

`Hurwitz/ExpIndependence.lean` (axiom-clean) — THE distinct-exponent independence, exp form:
`expLin_linearIndependent` ({z↦exp(β_k z)} ℂ-independent for distinct β_k) via
differentiate-then-Vandermonde. This is the hard analytic input, done. Helpers reusable:
`iteratedDeriv_expLin` (eigenfunction), `iteratedDeriv_finset_sum`.

Hurwitz start now **13 axiom-clean theorems / 3 files** (OrbitObstruction, MonodromyScalar,
ExpIndependence) + STATUS.

### Remaining (in dependency order)
1. **Local + power bridges** (wiring-phase, routine): `expLin_eq_zero_on_open` (vanish on open U⊆ℂ ⟹
   c=0, identity theorem) and `x^α = exp(α·log x)` for the singular vector `H(x)=(x^{-s-k})`.
2. **Abstract descent spine** (conditional theorem, analogue of `u0_phi_independence_abstract`):
   quadratic weight-grading `A_w=Σ_{i+j=w}q_{ij}` + exponent filtration (via core) → `Q(H)=0`;
   orbit (via OrbitObstruction+MonodromyScalar) → odd/quadratic coeff control; row descent (via
   Rational-Tail Independence) → all coeffs 0. Isolate the ONE deep input as interface:
3. **Hurwitz-zeta local expansion** `ζ(s+k,-n+x)=x^{-s-k}+R_{n,k}(x)` with `R_{n,0}(0)=ζ(s)+η·H_n^{(s)}`
   — NOT in mathlib (mathlib's hurwitzZeta is a:UnitAddCircle only). The deep analytic input, analogue
   of u₀-transcendence/hliftF. Build or isolate as named hypothesis.
4. **Rational-Tail Independence (Lemma 1)** via the same core (pole tower / OGF).

## Update 2 — distinct-exponent core application-ready (axiom-clean)

`expLin_eq_zero_on_open` added: `∑ c_k exp(β_k z)=0` on a NONEMPTY OPEN U⊆ℂ (distinct β_k) ⟹ c=0
(entire ⟹ identity theorem ⟹ everywhere ⟹ Vandermonde). **No separate power-form bridge needed:**
the spine works in `z = log x`, so the Hurwitz singular term `x^{-s-k}` is `exp(-(s+k)z)` and the
relation (which holds on a punctured nbhd of x=0, an open set in z) feeds this lemma directly.

Hurwitz start: **14 axiom-clean theorems / 3 files.** The complete algebraic engine + analytic core
(distinct-exponent independence) is done. Remaining: the descent SPINE assembly (algebra; use aesop for
glue) conditional on the isolated Hurwitz-zeta local-expansion interface (the one deep input not in
mathlib), then discharge that interface, then Rational-Tail Independence (Lemma 1).

## Update 3 — exponent filtration (generic case) landed (axiom-clean)

`Hurwitz/ExponentFiltration.lean`: `coeffs_zero_of_exp_periodic_combo` — singular-vs-regular separation
via the monodromy shift z↦z+2πi (singular e^{β_k z} scales by e^{2πiβ_k}, regular R(e^z) is 2πi-periodic;
shift-difference + expLin ⟹ singular coeffs vanish when e^{2πiβ_k}≠1, i.e. β_k∉ℤ). Handles the GENERIC
case (2s∉ℤ): quadratic exponents -2s-w are non-integer.

**Hurwitz foundation = 15 axiom-clean theorems / 4 files** — the algebraic engine + the analytic core +
the generic exponent filtration ("easy half" complete).

### Precise remaining structure (intricate — two filtration mechanisms)
- **q=-1 / half-integer case (2s∈ℤ):** quadratic exponents -2s-w are INTEGERS ⟹ periodic in z; the
  monodromy filtration can't see them. Needs a LAURENT-coefficient filtration (match power of x) for the
  quadratic coefficient (the orbit's odd-coeff fallback supplies the rest — MonodromyScalar.eq_neg_one).
- **Rational-Tail Independence (Lemma 1, task #13):** the LINEAR/cross-term row descent. Σ r_j(n)H_n^{(s+j)}
  =R(n) ⟹ r_j=0. Deep (OGF Σ H_n^{(u)}z^n = Li_u(z)/(1-z), pole tower). Isolate as interface.
- **Hurwitz local expansion (deep input):** ζ(s+k,-n+x)=x^{-s-k}+R_{n,k}(x), R_{n,0}(0)=ζ(s)+ηH_n^{(s)} —
  NOT in mathlib. Isolate as named interface (analogue of u₀-transcendence/hliftF), then discharge.
- **Spine assembly:** combine the above into the conditional N=2 theorem, then all-N row descent.

## Update 4 — descent algebra brick (axiom-clean)

`Hurwitz/DescentAlgebra.lean`: `eq_zero_of_infinitely_many_neg_nat_roots` /
`eq_zero_of_eventually_neg_nat_roots` — a polynomial (cleared coefficient) vanishing at `a=-n` for
infinitely many / all large `n` is 0. The "vanishes at ∞ many -n ⟹ 0 as rational function" backbone
of the row descent. **Hurwitz foundation now 17 axiom-clean theorems / 5 files.**

## Update 5 — Hurwitz zeta deep input started (axiom-clean)

`Hurwitz/HurwitzZeta.lean`: `summable_hurwitzSeries` — ∑_m((m:ℂ)+a)^(-s) summable for Re s>1 (the
series mathlib lacks for complex shift), via Complex.norm_cpow_le + arg≤π bound + reverse-triangle +
Real p-series comparison. First brick of the local expansion (the harder deep input). 18 axiom-clean
theorems / 6 files. Next: holomorphic-in-a (tsum), then the m=n local split → x^{-s-k}+R_{n,k},
R_{n,0}(0)=ζ(s)+η H_n^{(s)}.

## Update 6 — Hurwitz zeta: N=2 row-descent input complete (axiom-clean)

`Hurwitz/HurwitzZeta.lean` now has (all [propext,Classical.choice,Quot.sound]):
summable_hurwitzSeries, hzeta (def), hzeta_split, hzeta_local_split (ζ(s,-n+x)=x^{-s}+R_n),
neg_real_cpow ((-r)^w=r^w e^{iπw}), hzeta_neg_nat (tail value ζ(s,-n)=ζ(s)+η H_n^{(s)}),
hzeta_neg_nat_diff (Δζ(s,-n)=η·n^{-s} — the N=2 non-integer-power obstruction).
F_k local split = hzeta_local_split at s+k (gives x^{-s-k}). The N=2 density-shadow card's analytic
inputs (singular x^{-s-k} + the finite-difference η n^{-s}) are IN PLACE.

### Remaining for a complete N=2 theorem
- R_n holomorphic at x=0 (analyticOnNhd of the tail tsum; locally-uniform conv of analytic terms).
- "η n^{-s} is not the finite difference of a rational function" (rational-function asymptotics: integral
  powers of n only; vs n^{-s}, s∉ℤ) — the non-rationality step.
- Spine assembly (OrbitObstruction + MonodromyScalar + ExponentFiltration + DescentAlgebra + the above):
  quadratic weight grading → q(F_0F_2-F_1²) survivor → finite-difference kills q → distinct-exponent
  kills the linear part.
Then all-N needs Lemma 1 (Rational-Tail Independence) in place of the finite difference.

## Update 7 — GENUINE-`hzeta` capstones landed (2026-07-01, axiom-clean)

The mathlib-bump rot in the area build was repaired (missing transitive imports:
`Mathlib.Analysis.Complex.LocallyUniformLimit` + `Pow.Deriv` in N2TailAnalytic,
`Deriv.Polynomial` in N2BlockAnalytic, `ExponentialBounds` in N2Theorem/AllNQuadFilt), and the
model→actual bridge was built in `Hurwitz/N2HZeta.lean` (all [propext, Classical.choice, Quot.sound]):

- `term_split` — principal-branch product split `((m−n)+x)^c = (m−n)^c·(1+x/(m−n))^c` for `Im x > 0`
  (the branch-cut analysis; fails on the lower half-plane for `m<n` — the upper-side hypothesis is
  the honest window).
- `principal_tail_eq_tailFactored`, `hzeta_eq_model` — `ζ(s+k, −n+e^z) = e^{−(s+k)z} + tailFactored`
  on the upper half-strip `0 < Im z < π`.
- `model_relation_of_hzeta_relation` — hzeta relation at `a = −n+x` (`‖x‖<1/2`, `Im x>0`, all `n≥N`)
  ⟹ the model relation on the FULL strip (identity theorem on the convex half-plane, via
  `blockSum`-style analyticity).
- **`hurwitz_n2_hzeta_unconditional`** — the N=2 card against the ACTUAL Hurwitz zeta: only
  `Re s > 1`, `s ∉ ℤ`. **`hurwitz_n2_hzeta_upper_half_plane`** — upper-half-plane form.
- **`hurwitz_allN_hzeta_quadratic_block`** — all-N quadratic filtration `AqN q w = 0` (`w ≤ 2N`)
  against the actual hzeta.

Card wrappers registered in `FullyProvenNewTargets` (`HurwitzN2HZetaUnconditionalTarget`,
`HurwitzN2HZetaUpperHalfPlaneTarget`, `HurwitzAllNHZetaQuadraticBlockTarget`). The N=2 card is now
complete at the genuine-function level.

### Remaining open input (all-N rows only)
`RationalTailIndependent` (Lemma 1): no `ℂ[a]`-relation `∑ r_j(−n)·H_n^{(s+j)} = P(−n)`. Needs the
OGF `∑ H_n^{(u)} z^n = Li_u(z)/(1−z)` pole-tower singularity analysis (fractional polylog — not in
mathlib). `PolylogPoleTower.lean` has the pole-arithmetic bricks; the OGF analytics are the open
work. The all-N quadratic block does NOT depend on it.

### Route plan for Lemma 1 (next session) — Euler–Maclaurin filtration, no polylog needed

The in-tree reduction chain already lands the all-N rows on ONE leaf:
`MixedTailIndependent N s` (⟺ `MixedPoleRootInput`, `AllNTailIndependence.lean`): a relation
`∑ h_i(n)·H_n^{(s+i)} + ∑ s_i(n)·n^{−s−i} = P(n)` (eventually, `H_n^{(u)} = harmonicTail =
∑_{l<n}(l+1)^{−u}`) forces all coefficients to vanish. The OGF/polylog pole tower is NOT needed:

1. `H_n^{(u)} = ζ(u) − hzeta u (n+1)` (exact, in-tree objects: `hzeta_split`-style).
2. Expand `hzeta u (n+1)` to finite order `K = maxdeg + 2` by iterated integral comparison
   (Euler–Maclaurin light): `hzeta u a = a^{1−u}/(u−1) + a^{−u}/2 + Σ_{r<K} c_r(u) a^{−u−r}
   + O(a^{−Re u−K})` — elementary complex-power sums, no special functions.
3. The relation becomes `∑ (integer scales n^d) + ∑ (non-integer scales n^{1−s−w}) + o(all) = 0`.
   With `s ∉ ℤ` the two scale families are disjoint and all exponents pairwise distinct;
   successive leading-term extraction (the `Spine.quadratic_filtration_top` / `evalShift`
   asymptotic tools, or a fresh finite filtration) kills every coefficient.
This upgrades `hurwitz_allN_hzeta_quadratic_block` to the full all-N tail-independence close,
including rows, against the actual hzeta (via `Hurwitz/N2HZeta.lean`'s bridge, already generic
in the width).
