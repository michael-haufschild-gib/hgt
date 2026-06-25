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
