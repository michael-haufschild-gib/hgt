# Rational AP locks with unbounded denominators force RH

- **ID:** unbounded-denominator-lock-closure
- **Stage:** 3-formalized
- **Type:** CONJECTURE (C2112), paper programme
- **Source:** Opus loop row 2106; builds on MUST-1322 and MUST-1327 (`3-formalized/bounded-denominator-lock-closure.md`)
- **Statement:** a Herglotz producer with lower-line lock `G(1−s) = (Σ_j q_j u_j^{−(s−½)})G(s)` with all `u_j ∈ ℚ_{>0}` and `Σ_j |q_j| max(1, u_j^{−1}) den(u_j)^{½+ε} < ∞` forces RH.

## Goal
Close the rational part of the open almost-periodic class in the uniqueness half (U) of the HF route. After MUST-1327 the AP class is open only for unbounded denominators, and for rational spectra mixed with irrational frequencies. Natural twins `ξ·A`, where `A = 1/(Dirichlet polynomial zero-free on Re ≥ ½)`, have S-unit (unbounded) denominators and satisfy the weight.

## Gates
- [x] 0 → 1  well-posed; attack recorded in row 2106 (the `den^{½}` weight is the Gauss-sum size, needed twice)
- [x] 1 → 2  paper proof of M1–M3 (superseded by the Lean proof)
- [x] 2 → 3  Lean: `RHTower.AbelianTwist.rationalLock_riemannHypothesis` (MUST-1388), weight `Σ_j|c_j|max(1,r_j^{−1})√den(r_j)·8^{ω(den r_j)} < ∞`
- [ ] 3 → 4  not pursued

## Programme
**M1 (limit-periodic coefficients).** The period law holds at all rational heights: `P(x) = √x Σ_n a(n)n^{−½}R(x/n)` is 1-periodic on `ℚ_{>0}`. So `F·V = H := Σ_{x₀ ∈ ℚ∩(0,1]} P(x₀) ζ(s, x₀)`, and `Σ |P(x₀)| den(x₀)^{½+ε} < ∞` (`den(nr) ≤ den(r)`, `Σ_{n≤X}|a(n)| ≪ X^{1+ε}`). `H` converges on `Re s ≥ ½`, `s ≠ 1`, because `ζ(s,x₀) = x₀^{−s} + ζ(s,x₀+1)`, `x₀^{−½} ≤ den^{½}`, and Euler–Maclaurin bounds `ζ(s,y)`, `y ∈ [1,2]`, uniformly.
- Lock plus Hurwitz FE: on the upper line `G(w) = w(w−1)Γ_ℝ(1−w)(2π)^{−w}Γ(w) Σ_{x₀} P(x₀)(e^{−πiw/2} expZeta(x₀,w) + e^{πiw/2} expZeta(−x₀,w))`.
- The convergence uses `|expZeta(b/q, ½+it)| ≪ √q·poly(t)`.
- Boundary uniqueness then gives the identity on the quadrant, and vertical decay plus Bohr vanishing give `a(n) = κ Σ_{x₀} P(x₀) e(∓n x₀)`. This is uniformly limit-periodic with `ℓ¹(den^{½+ε})` Fourier data.

**M2 (limit-periodic single character).** Given `a = exp⋆ℓ` (log-convergent) with such Fourier data, exactly one primitive character `χ₁` carries `a`: `F = C(s)L(s,χ₁)`.
- Twist by `f` with `f(p) = p^{−s₀}` for `p ≤ D`, `z_p` on a finite set `S` of primes `> D`, and `0` elsewhere.
- Frequencies with `den ≤ D` decompose exactly into characters mod `q ≤ D`, with `Σ_χ |C_χ| ≤ Σ |P̃| √den·(smooth factor)` uniformly in `D`.
- Frequencies with `den > D` are a tail bounded by `(Σ_{den>D}|P̃|)·Σ|f(n)| ≤ tail·e^{2K}ζ(s₀)`.
- `K` is uniform, because `Σ_a |u⁰(a)| ≤ |L₀| + 3R'` and `Σ_a |v_χ(a)| = 1`.
- Then the planting of `exists_charProduct_zero` works with uniform constants.

**M3 (endgame).** `C` is holomorphic on `Re s > ½` (it is absolutely convergent there from the weight). `G(1) ≠ 0` forces `χ₁` principal. Then `ζ`'s zeros right of `½` would be `G`'s zeros, which gives RH (as in MUST-1327).

## Paper proof details (2026-10-12)
**M1 needs only the standard hypothesis `Σ|q_j| max(1,1/u_j) < ∞`.**
- Convergence: `Σ_{x₀}|P(x₀)| x₀^{−σ} ≤ Σ_r |R(r)| r^{½−σ} Σ_{n≤1/r} |a(n)| n^{−σ} ≪ Σ_r |R(r)| r^{−½−ε}` for `σ ≤ ½`. So `H(s) = Σ_{x₀} P(x₀)ζ(s,x₀)` converges locally uniformly on `−1 < Re s ≤ ½`. Use `ζ(s,x₀) = x₀^{−s} + ζ(s,x₀+1)` and the uniform EM bound for `ζ(s,y)`, `y ∈ [1,2]`.
- Boundary uniqueness is run on the left: `G(1−s)` and `s(s−1)Γ_ℝ(s)H(s)` agree on the lower line and are holomorphic in `{Re s < ½, Im s < 0}`. So `F(w)Γ_ℝ(w) = Γ_ℝ(1−w)H(1−w)` on `{½ < Re w < 1, Im w > 0}`, and by the identity theorem on `{½ < Re w < 2, Im w > 0}`.
- On `1 < Re w < 2` the Hurwitz FE per `x₀` gives `ζ(1−w,x₀) = (2π)^{−w}Γ(w)(e^{−πiw/2} expZeta(x₀,w) + e^{πiw/2} expZeta(−x₀,w))`. Here `|expZeta| ≤ ζ(Re w)` uniformly, so no weight is needed.
- Gamma identity plus vertical decay plus Bohr vanishing give `a(n) = κ Σ_{x₀} P(x₀) e(−n x₀)`.

**M2 (weight `√den`).** For `x = b/q` let `Ψ_x(t) = e(tb/q)` on `ℤ/q`.
- B3 gives `Ψ_x(m r) = Σ_{χ mod q} charSection Ψ_x χ m · χ(r)` (`m` `q`-smooth, `(r,q) = 1`).
- Parseval gives `Σ_χ |charSection Ψ_x χ m| ≤ √φ(q)`.
- Twist `f`: `p^{−s₀}` on `p ≤ D`, `z_p` on `S` (primes `> D`), `0` elsewhere. For `den(x) ≤ D`: `Σ_n Ψ_x(n) f(n) = Σ_{χ mod q} A_{x,χ} E_χ`, where `A_{x,χ} = (Σ_m cs(m) m^{−s₀}) Π_{p≤D, p∤q}(1 − χ(p)p^{−s₀})^{−1}` and `E_χ = Π_{p∈S}(1 − χ(p)z_p)^{−1}`.
- Lift to characters mod `Q = lcm(q ≤ D)` (`E` agrees since `S ∤ Q`). `C^{(D)}_ψ → L(s₀,χ*) Γ_{χ*}(s₀)` for `ψ` induced by a primitive `χ*`. Total mass `≤ Σ_x |β(x)| √den(x)·ζ(s₀)²`, uniform in `D`.
- Frequencies with `den > D` are a tail bounded by `(Σ_{den>D}|β|)·ζ(s₀)e^{2K}`.
- `K ≤ |L₀| + 3R' + 2` is uniform in `Q`, since `Σ_a |Σ_{others} v_χ(a)| ≤ 3` and `Σ_a |v_χ(a)| = 1`.
- So the planting of `exists_charProduct_zero` works for large `D` (perturbation budget `c₁/24` for the tail).

**M3 (weight `den^{½+ε}`).** `F = Σ_{χ*} Γ_{χ*}(s) L(s,χ*)` with `Γ_{χ*}(s) = Σ_x β(x) Σ_{χ mod den(x) induced by χ*} (Σ_m cs_x(χ,m) m^{−s}) Π_{p|den(x)}(1 − χ*(p)p^{−s})`. This converges absolutely on `Re s > 0`, since `Σ_{m q-smooth} m^{−σ} ≤ 3^{ω(q)} ≪ q^ε`. M2 leaves one `χ*`, the pole at `1` makes it trivial, and then `F = Γ·ζ` with `Γ` holomorphic on `Re > 0`, which gives RH.

## Lean infrastructure needed
- Euler–Maclaurin continuation (`HTGeometry/LerchHurwitzDerivative.hurwitzZetaEM`) bridged to Mathlib `hurwitzZeta`, with bounds uniform in the shift.
- `expZeta(b/q, w) = q^{−w} Σ_c e(cb/q) ζ(w, c/q)` and the `√q` line bound.
- Countable-family versions of boundary uniqueness and decay (MUST-1322 already has the finite versions).
- A version of `exists_charProduct_zero` with an absolutely summable family of characters and an explicit tail.

## Log
- 2026-10-12 — created from row 2106.
- 2026-10-13 — Lean infrastructure for M2 delivered: `RHTower/CharacterProductZeroPlantingTwoLevel` (`exists_twoLevel_charProduct_zero`, MUST-1381).
  - Zero planting with characters mod `N`, band characters mod `N'` that do not factor through `N` (`Σ|D| ≤ |C(χ₁)|/96`), and any far family with `Σ|e_j| ≤ η`, where `η` depends only on the level-`N` data.
  - Also `exists_realization` (prime realization at any level with a prime floor `P₀`) and `prod_inv_estimates`.
  - Remaining Lean for M2: the Gauss-sum character expansion of `e(nb/q)` with smooth parts, and the Bohr-lift identity for the twisted series. The duplicate card `rational-lock-unbounded-denominators.md` is merged here.
- 2026-10-13 — far-part interface (MUST-1381 addendum 2): `exists_twoLevel_zero_of_far` accepts any far part with `|Φ(S,v)| ≤ η e^{2Σ_S|v_p|}` that is holomorphic in `v`. This covers the den `> D` tail and the perturbation `C^{(D)} − C` of the level-`N` coefficients. The power-series instance is `exists_twoLevel_zero_of_powerSeries`.
- 2026-10-13 — **M2 formalized** (MUST-1383, `RHTower/LimitPeriodicExpSingleCharacter`). `limitPeriodic_exp_single_character`: if `exp⋆ℓ = Σ_q Ψ_q` with period `q+1` and `Σ_q √(q+1) sup|Ψ_q| < ∞`, then at each `s₀ > 1` at most one character `ξ` mod `N` has `Γ_ξ(s₀) ≠ 0`, where `Γ_ξ = Σ_q Σ_{χ∼ξ} L(s,c_χ)L(s,χ)`. The frequencies `b/q` of `Σ_x β(x)e(nx)` with `Σ|β|√den < ∞` fit after grouping by denominator, since `Ψ_q` is bounded by `Σ_{den x = q+1}|β(x)|`. Remaining: M1 (lock ⟹ expansion) and M3 (pole and analyticity of `Γ` on `Re s > ½`).
- 2026-10-13 — **M3 formalized** (MUST-1385, `RHTower/LimitPeriodicProducerRH`). `limitPeriodic_producer_riemannHypothesis`: a zero-free producer `G = s(s−1)Γ_ℝF` with `a = Σ_qΨ_q` (period `q+1`, `Σ√(q+1)8^{ω(q+1)}B_q < ∞`) forces RH. Herglotz positivity is not needed. **Remaining: M1 only.** The lock must give `a(n) = Σ_x β(x)e(−nx)` with `Σ|β|den^{½+ε} < ∞`. The Lean inputs are the period law at every real height (`tendsto_far_real_height`, `tendsto_far_translation`) and the bounded-case template `bounded_denominator_lock_periodic` (`ZMod.LFunction_one_sub`). The missing piece is a countable-sum Hurwitz functional equation with bounds uniform in `x₀`.
- 2026-10-13 — **M1 Lean plan** (module `RHTower/WeilAlmostPeriodicLockCoefficients`). It works for any real frequencies `u_j > 0` with `Σ|c_j|max(1,u_j^{−1}) < ∞`.
  - A1/A2: `𝒫(x) = √x Σ_n a(n)n^{−3/2} ratSpec 0 c u x n = Σ_{n u_j = x} a(n)c_j√u_j`, and `𝒫(x+1) = 𝒫(x)` (`tendsto_far_real_height`, `tendsto_far_translation`).
  - Domination: `|w(n,j)|·[n u_j ≤ 1]·(n u_j)^{−σ} ≤ |a(n)|n^{−3/2}|c_j|max(1,u_j^{−1})` for `σ ≤ 3/2`.
  - A3 (rearrangement, `1 < Re s ≤ 3/2`): `F·V = Σ_{(n,j)} w (n u_j)^{−s} = Σ_{n u_j ≤ 1} w ζ(s, n u_j)`, by `HasSum.tsum_fiberwise` over the value `y`, using the period law to move `y` to `{y} ∈ (0,1]`.
  - A4: `Hrep(s) = Σ_{n u_j ≤ 1} w (y^{−s} + ζ_EM(s, y+1))` is holomorphic on `−½ < Re s ≤ 3/2`, `s ≠ 1` (`hurwitzZeta_eq_rpow_add_hurwitzZetaEM`, `norm_hurwitzZetaEM_le`).
  - A5–A7: `GV = s(s−1)Γ_ℝ Hrep` on the lower half strip and line. The lock gives `G(w) = w(w−1)Γ_ℝ(1−w)Hrep(1−w)` on the upper line. Uniqueness on the strip `½ < Re w < 3/2`, `Im w > 0` needs a strip variant of `eq_zero_of_vertical_halfLine`.
  - A8: `hurwitzZeta_one_sub` per term and `expZeta` as a Dirichlet series on `Re w > 1` give `(F − L(b))(1 + e^{−πiw}) = L(b⁻) − L(b)`.
  - A9 (Bohr): `a(n) = Σ_{m u_j ≤ 1} a(m)c_j√u_j e(n m u_j)`.
  - Rational corollary: group by `den(m u_j) | den(u_j)` and apply MUST-1385. The weight is `Σ_j |c_j|max(1,u_j^{−1})√den(u_j)·8^{ω(den u_j)} < ∞`.
- 2026-10-13 — **CLOSED in Lean.** The Lean statements are:
  - M1: `apLock_coefficients` (MUST-1387, any real frequencies).
  - M2: `limitPeriodic_exp_single_character` (MUST-1383).
  - M3: `limitPeriodic_producer_riemannHypothesis` (MUST-1385).
  - Assembly: `rationalLock_riemannHypothesis` (MUST-1388).
  - Modules: `RHTower/{CharacterProductZeroPlantingTwoLevel, LimitPeriodicExpSingleCharacter, LimitPeriodicProducerRH, WeilAlmostPeriodicLockCoefficients, WeilRationalLockRH}`.
- The paper's weight `den^{½+ε}` is replaced by `√den·8^{ω(den)}`, which is weaker.
- M1 holds for arbitrary positive real frequencies, so the remaining open lock classes are:
  - irrational frequencies (`a` almost periodic with irrational spectrum);
  - rational weights below `√den`.
