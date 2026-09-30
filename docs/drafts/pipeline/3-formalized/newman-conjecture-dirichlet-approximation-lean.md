# Newman's conjecture: `H_{−τ}` has infinitely many non-real zeros (Lean programme)

- **ID:** NEWMAN-DOBNER-LEAN
- **Stage:** 3-formalized (Lean complete; card to be filed under 3-formalized)
- **Type:** THEOREM (paper, self-derived variant of Dobner 2020) → Lean programme
- **Source:** rh-goal-loop-opus-2026-09-29 cycle 29; frontier gate "no slack" (Λ = 0 edge);
  R:FinitenessThresholdCriterion (its open core `τ_fin = 0`).
- **Statement:** for every `τ > 0` the function `H_{−τ}(z) = ∫Φ(x)e^{−τx²}e^{izx}dx` has infinitely
  many non-real zeros. Hence the full-line de Bruijn–Newman constant is `≥ 0` (Newman's conjecture,
  Rodgers–Tao 2018, Dobner 2020), and `τ_fin = 0` unconditionally: the falsification criterion of
  R:FinitenessThresholdCriterion ("finitely many non-real zeros at some `t<0` ⇒ ¬RH") has an
  impossible premise.

## Goal
Formalize the no-slack gate (`0 ≤ Λ < 1/8`, RH ⇔ `Λ = 0`) completely, and close the heat-flow
falsification route with a theorem. Not an RH producer.

## Paper proof (normalization of the corpus: `H_0(z) = ξ(½+iz)`, `s = ½ + iz`)

Write `A(s) = H_{−τ}(z)`, `g_τ(u) = (4πτ)^{−1/2}e^{−u²/(4τ)}`, `G(w) = ½w(w−1)π^{−w/2}Γ(w/2)`
(so `ξ = Gζ`), `F_τ(w) = Σ_{n≥1} e^{−τ log²n} n^{−w}` (entire).

1. **Vertical Gaussian average.** `e^{−τx²} = ∫g_τ(u)e^{iux}du` and Fubini:
   `A(s) = ∫g_τ(u) ξ(s+iu) du`.
2. **Line shift.** For every real `a`: `A(s) = ∫g_τ(u−ia) ξ(s+a+iu) du` (entire integrand in `u`,
   Gaussian decay `|g_τ(u−ia)| = g_τ(u)e^{a²/(4τ)}` against the order-one envelope of `ξ`).
3. **Dirichlet expansion** on `Re(s+a) ≈ 2`: `ξ = G·Σ n^{−w}`, termwise integration (dominated by
   `ζ(2)·g_τ·|G|`).
4. **Log-linear model for `G`.** With `w₁ = s+a`, `L` a fixed slope `≈ G'/G(w₁)`:
   `|G(w₁+iu) − G(w₁)e^{iuL}| ≤ |G(w₁)|e^{−u Im L}·E(u)`, `E(u) = κ(u)e^{κ(u)}`,
   `κ(u) = C(u²+|u|+1)/T` for `|u| ≤ T/2` (Stirling `ψ(z) = log z − 1/(2z) + O(|z|⁻²)` from
   H:GammaDigammaStirlingBound; `|log w − log w'| ≤ 2|w−w'|/T`).
5. **Exact model sum.** `∫g_τ(u−ia)e^{iuk}du = e^{−ak−τk²}` (complex `k`), so
   `Σ_n G(w₁)n^{−w₁}e^{−a(L−log n)−τ(L−log n)²} = N(s)·F_τ(s−2τL)`,
   `N(s) = G(s+a)e^{−aL−τL²}` (holomorphic, non-vanishing in `s`).
6. **Error.** Core (`|u| ≤ T/2`): `≤ ζ(2)|G(w₁)|e^{a²/(4τ)}∫g_τ(u)e^{−u ImL}E(u)du`; relative to
   `|N(s)|` the factor is `e^{(a+2τ Re L)²/(4τ)}·O(τ^{1/2}/T^{…})` and `a + 2τ Re L = 2 − Re(s−2τL)`
   stays bounded on the relevant discs, so the relative error is `O_{τ,K}(1/T)` up to Gaussian
   moments. Far tail (`|u| ≥ T/2`): Gaussian `e^{−T²/(16τ)}` beats the order-one envelope and the
   lower bound `|G(2+iT)| ≥ c e^{−πT/4}` (from `|Γ(1+iy)|² = πy/sinh πy`).
   Result: `|A(s)/N(s) − F_τ(s−2τL)| ≤ ε` on discs `|s − s_c| ≤ r` at heights `T ≥ T₀(ε,τ,K)`.
7. **`F_τ` has a zero.** `F_τ` is entire of finite order (`|F_τ(w)| ≤ C e^{(Re w)²/(4τ)}`-type bound),
   `F_τ → 1` uniformly as `Re w → +∞`. If zero-free, `F_τ = e^{P}` with `P` a polynomial
   (H:finite-order zero-free factorization), `P` bounded on a half-plane ⇒ constant ⇒ `F_τ ≡ 1`,
   contradicting `F_τ(σ) > 1` for real `σ`.
8. **Transfer.** `F_τ` is strip almost periodic (H:DirichletStripAlmostPeriodic). Take a zero `w₀`,
   a circle `|w−w₀| = ρ` with `|F_τ| ≥ δ`, almost periods `T_m → ∞` with `|F_τ(w+iT_m) − F_τ(w)| ≤ δ/5`
   on the disc; centre `s_c = w₀ + iT_m + 2τL`. With `ε ≤ δ/5`, the minimum modulus principle
   (R:DeBruijnBarrierZerosSimple `exists_zero_of_norm_lt_sphere`) gives a zero `s*` of `A` in the disc;
   `Re s* ≈ Re w₀ + τ log(T_m/2π) → ∞`, so `z* = −i(s*−½)` is a non-real zero of `H_{−τ}`, at
   heights `→ ∞`: infinitely many.

## Lean plan (modules, RHTower)
- [x] P1–P2 `DeBruijnNegativeTimeContour`: Gaussian representation and line shift (compiled, built).
- [x] P4 `ArchimedeanFactorVerticalModel`: Stirling slope bound, vertical model, lower bound (compiled).
- [x] P3–P6 `DeBruijnNegativeTimeDirichletModel`: exact model sum `integral_model_eq`, explicit error
      bound `norm_negHeatS_sub_model_le` (compiled).
- [x] P7 `GaussianDirichletSeries`: `F_τ` entire, order ≤ 2, has a zero, strip almost periodic (built).
- [x] P8 `DeBruijnNewmanNonnegative`: transfer, infinitely many non-real zeros, `t<0` never
      real-rooted (built, wired).

## Log
- 2026-09-30 — created; paper proof self-derived (single contour line, no per-`n` saddle points:
  the relative loss `e^{(a+2τ Re L)²/(4τ)}` is bounded because `a + 2τ Re L = 2 − Re(s−2τL)`).
- 2026-09-30 — P1–P7 compiled. Remaining: P8 (asymptotics of the explicit bound with
  `V_T = √(16τT(log T+3))`, disc approximation, almost periods, minimum modulus, infinitude).
- 2026-09-30 — P8 done: `riemannHeat_neg_nonreal_zeros_infinite`, `not_real_rooted_of_neg`. All five modules
  clean under `lake env lean`, `--old` builds green, axioms `propext/Classical.choice/Quot.sound`, wired in
  RHTower.lean, collision scan clean (one private helper). STATUS MUST-553.
