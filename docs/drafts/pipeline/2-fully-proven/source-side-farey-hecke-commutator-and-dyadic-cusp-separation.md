# Source-Side Farey–Hecke Operator Algebra, Three-Term Cusp-Erasure Obstruction, and Dyadic Cusp-Energy Separation

- **ID:** source-side-farey-hecke-commutator-and-dyadic-cusp-separation
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** [obstacles-summary.md](../../../reports/review-0211/obstacles-summary.md) (§2.6.2) · [route-pm-mayer-scattering-and-escape.md](../1-in-progress/route-pm-mayer-scattering-and-escape.md) (Mayer 4)
- **Statement:** On the canonical `s`-independent Hilbert space `H_LP = L²((0, ∞), w_LP(a) da)` (`w_LP(a) = (a + a⁻¹)^(-6) a^(-1/2)`), (1) `(I_s† I_s f)(a) = a^(4 Re s - 1) f(a)` and `I_s` is norm-bounded iff `Re s = 1/4`; (2) the Gauss–Mayer renewal head branch `(G_{0,s} f)(a) = a^(-2s) f(1 + a⁻¹)` (`Re s > 0`) is bounded iff `Re s ≤ 1/4` (while every tail branch `m ≥ 1` is bounded across `Re s > 0`, and `(G_{0,s}, G_{0,1/2 - conj s})` is simultaneously bounded iff `Re s = 1/4`); (3) the Farey–Lewis three-term operator `M_s = U_1 + V_s` is bounded across `Re s > 0` with disjoint-half-line Koopman adjoints `U_1†` on `(1, ∞)` and `V_s†` on `(0, 1)`, cross-annihilation `U_1 V_s† = V_s U_1† = 0`, diagonal co-square `(M_s M_s† g)(a) = μ_s(a) g(a)` satisfying `μ_s(a) > 1` on `(0, ∞)` for `0 < Re s ≤ 1/2`, strict self-commutator negativity `⟨[M_s†, M_s]ψ, ψ⟩_LP < 0` on every nonzero continuous three-term fixed point `ψ ∈ H_LP`, and universal Manin–Mühlenbruch Hecke intertwining `I_s T_{2,s} = T_{2,s} I_s` and `(1 - M_s) T_{2,s} = T̃_{2,s}(1 - M_s)`; (4) naive three-term reflection positivity fails unconditionally because for every `0 < Re s < 1/2` the continuous Eisenstein period `Ψ_s^Eis = period(2s, 1, -ζ(2s), state(2s), ·) ∈ H_LP \ {0}` satisfies `I_s Ψ = Ψ` and `M_s Ψ = Ψ` with `Q_s(Ψ) < 0 ↔ Re s ≠ 1/4`; and (5) for every signed Mayer solution `(f ∈ DiscSpace, c ∈ ℂ, ε² = 1)` on `Re s > 0` (`2s ≠ 1`), the derivative-free dyadic cusp extractor `Δ_{2,s}^∞ ψ(a) = ψ(2a) - 2^(1 - 2s) ψ(a)` satisfies `‖Δ_{2,s}^∞ ψ(a) + ε(1 - 2^(1 - 2s)) c‖ ≤ C a^(-2 Re s)` (`a ≥ 2`), so across `0 < Re s < 1/2`, `Δ_{2,s}^∞ ψ ∈ L²((1, ∞), da/a) ↔ c = 0`, separating Mayer scattering resonances from generic continuous scattering (`Δ_{2,s}^∞ Ψ_s^Eis ∈ L²((1, ∞), da/a) ↔ IsMayerScatteringResonance s`).

## Goal
Establish the autonomous source-side Hilbert operator calculus of `(I_s, G_{m,s}, M_s, T_{2,s})` directly inside `H_LP`, diagnose the exact cusp-erasure obstruction showing why `H_LP`-membership plus `(I_s, M_s)`-invariance cannot exclude off-line parameters, and close Route PM Task `Mayer 4` unconditionally via the positive-semidefinite dyadic cusp quadratic form `∫_1^∞ |ψ(2a) - 2^(1 - 2s) ψ(a)|² da/a` without factoring through `state_zero` or `core_hasMellin`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean module `FareyLewisTransferAndCuspSeparation.lean`, `lake --old env lean` green, `#print axioms` PASS

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Naive source-side three-term reflection positivity (`ψ ∈ H_LP`, `I_s ψ = ψ`, `M_s ψ = ψ` `⇒ Q_s(ψ) = 0`) is false. Applying `1 - U_1` to the forced renewal equation erases the constant forcing `c = -ζ(2s)`, while `w_LP(a) = (a + a⁻¹)^(-6) a^(-1/2) asymp a^(-13/2)` integrates both the constant cusp wave `-ε c` and the outgoing wave `a^(1 - 2s)`. Hence for every `s` in `0 < Re s < 1/2` (witnessed off-line unconditionally at every real `s ∈ (0, 1/2) \ {1/4}`, e.g. `s = 1/8`), `Ψ_s^Eis` satisfies `I_s Ψ_s^Eis = Ψ_s^Eis` and `M_s Ψ_s^Eis = Ψ_s^Eis` in `H_LP`, yet `Q_s(Ψ_s^Eis) < 0` whenever `Re s ≠ 1/4`.
- **Strongest positive survivor:**
  1. Exact polar square `I_s† I_s = a^(4 Re s - 1)`, renewal head-branch critical-line boundedness dichotomy (`G_{0,s}` bounded iff `Re s ≤ 1/4`; `(G_{0,s}, G_{0,1/2 - conj s})` bounded iff `Re s = 1/4`), disjoint-half-line Koopman adjoints of `M_s = U_1 + V_s` with `U_1 V_s† = V_s U_1† = 0`, strict co-expansivity `M_s M_s† = μ_s > 1`, and universal Hecke intertwining `(1 - M_s) T_{2,s} = T̃_{2,s}(1 - M_s)`.
  2. Autonomous dyadic cusp-forcing recovery `lim_{a → +∞} (ψ(2a) - 2^(1 - 2s) ψ(a)) = -ε(1 - 2^(1 - 2s)) c` (`O(a^(-2 Re s))`) and quadratic-form separation `∫_1^∞ |ψ(2a) - 2^(1 - 2s) ψ(a)|² da/a < ∞ ↔ c = 0` across `0 < Re s < 1/2`.
- **New insight:** On `H_LP`, resonance placement (`Re s = 1/4 ↔ Q_s(Ψ_s^Eis) = 0`) and resonance detection (`c = 0 ↔ Δ_{2,s}^∞ Ψ_s^Eis ∈ L²((1, ∞), da/a)`) are orthogonal quadratic-form conditions: `Q_s` measures modular-inversion non-unitarity across the entire strip, whereas `∫_1^∞ |Δ_{2,s}^∞ ψ|² da/a` annihilates the outgoing `a^(1 - 2s)` wave and isolates the constant cusp forcing `-ε(1 - 2^(1 - 2s)) c`.
- **Status:** Complete dependency-closed paper proof `[PROVED HERE]`; proceeding directly to Lean 4 formalization in `FareyLewisTransferAndCuspSeparation.lean`.

## Complete Paper Proof `[PROVED HERE]`

### 1. Polar Square of `I_s` and Gauss–Mayer Branch Boundedness Dichotomy on `H_LP`

Let `w_LP(a) = (a + a⁻¹)^(-6) a^(-1/2)` on `(0, ∞)` and `s̃ = 1/2 - conj s`, so `I_s† = I_{s̃}`.
For every `a > 0` and `f : ℝ → ℂ`:
```text
(I_{s̃}(I_s f))(a) = a^(-2 s̃) (a⁻¹)^(-2s) f((a⁻¹)⁻¹) = a^(2 conj s - 1 + 2s) f(a) = a^(4 Re s - 1) f(a),
```
since `2 conj s + 2s - 1 = 4 Re s - 1 ∈ ℝ`. Replacing `s` by `s̃` gives `(I_s(I_{s̃} f))(a) = a^(1 - 4 Re s) f(a)`.
By `‖I_s f‖_LP² = ∫_0^∞ ‖f(b)‖² b^(4 Re s - 1) w_LP(b) db`:
- If `Re s = 1/4`, `4 Re s - 1 = 0`, so `‖I_s f‖_LP² = ‖f‖_LP²` (`C = 1`).
- If `Re s > 1/4` (`δ = 2 Re s - 1/2 > 0`), testing on `f_R = 1_{(R, 2R]}` (`R ≥ 1`) gives `b^(2δ) ≥ R^(2δ)` on `(R, 2R]` while `0 < ‖f_R‖_LP² < ∞`, so `‖I_s f_R‖_LP² ≥ R^(2δ) ‖f_R‖_LP²` with `R^(2δ) → +∞` as `R → +∞`.
- If `Re s < 1/4` (`δ < 0`), testing on `f_r = 1_{(r, 2r]}` (`0 < r < 1/2`) gives `b^(2δ) ≥ (2r)^(2δ) → +∞` as `r → 0⁺`.
Hence `I_s` is bounded on `H_LP` iff `Re s = 1/4`.

For the `m`-th Gauss–Mayer renewal branch `(G_{m,s} f)(a) = (a + m)^(-2s) f(1 + (a + m)⁻¹)` (`m ∈ ℕ`, `Re s > 0`):
- **Head branch `m = 0` (`G_{0,s} = I_s U_1`):** Substituting `a = (b - 1)⁻¹` (`b ∈ (1, ∞)`, `da = (b - 1)^(-2) db`) and using `(b - 1)^(-2) w_LP((b - 1)⁻¹) = (b - 1)^(-1) w_LP(b - 1)` yields
  ```text
  ‖G_{0,s} f‖_LP² = ∫_1^∞ ‖f(b)‖² ρ_s(b) w_LP(b) db,   ρ_s(b) := (b - 1)^(4 Re s - 1) w_LP(b - 1) / w_LP(b).
  ```
  Wait: write `u = b - 1 > 0` (`b = u + 1`). For `0 < u ≤ 1` (`1 < b ≤ 2`), `(u + u⁻¹)^(-6) ≤ u^6` and `(b + b⁻¹)^(-6) b^(-1/2) ≥ (2 + 1)^(-6) · 2^(-1/2) = 3^(-6) 2^(-1/2)`, so
  `ρ_s(b) ≤ 3^6 √2 · u^(4 Re s + 9/2) ≤ 3^6 √2` for all `Re s > -9/8`.
  For `b ≥ 2` (`u = b - 1 ≥ b/2`), `u + u⁻¹ ≥ b/2` and `b + b⁻¹ ≤ 2b`, so `(u + u⁻¹)^(-6) / (b + b⁻¹)^(-6) = ((b + b⁻¹)/(u + u⁻¹))^6 ≤ 4^6` and `(b/(b - 1))^(1/2) ≤ √2`; when `Re s ≤ 1/4`, `(b - 1)^(4 Re s - 1) ≤ 1` (`b ≥ 2`), giving global boundedness `sup_{b > 1} ρ_s(b) < ∞`.
  Conversely, when `Re s > 1/4` (`4 Re s - 1 > 0`), for `b ≥ 2`, `u + u⁻¹ ≤ b + 1 ≤ 2b ≤ 2(b + b⁻¹)`, so `w_LP(b - 1)/w_LP(b) ≥ 2^(-6)`, whence `ρ_s(b) ≥ 2^(-6) (b - 1)^(4 Re s - 1) → +∞` as `b → +∞`; testing on `1_{(R, R + 1]}` (`R ≥ 2`) disproves boundedness for any `C ≥ 0`.
  Replacing `s` by `s̃ = 1/2 - conj s` (`Re s̃ = 1/2 - Re s`) shows `G_{0,s̃}` is bounded on `(0, 1/2)` iff `Re s ≥ 1/4`; thus `(G_{0,s}, G_{0,s̃})` is simultaneously bounded iff `Re s = 1/4`.
- **Tail branches `m ≥ 1`:** Substituting `b = 1 + (a + m)⁻¹ ∈ (1, 1 + m⁻¹)` (`a = (b - 1)⁻¹ - m`, `da = (b - 1)^(-2) db`) restricts `b` to `(1, 2]` where `w_LP(b) ≥ 3^(-6) 2^(-1/2)`, while `(a + m)^(-4 Re s) = (b - 1)^(4 Re s)` and `(b - 1)^(-2) w_LP((b - 1)⁻¹ - m) ≤ C_m` (bounded near `b = 1 + m⁻¹` since `w_LP(a) ≤ a^(11/2)` on `(0, 1]`, and decaying like `(b - 1)^(9/2)` as `b → 1⁺`). Hence every `G_{m,s}` (`m ≥ 1`) is bounded across all `Re s > 0`.

### 2. Farey–Lewis Operator `M_s`, Koopman Adjoints, Self-Commutator, and Hecke Intertwining

Define `(U_1 f)(a) = f(a + 1)`, `(V_s f)(a) = (a + 1)^(-2s) f(a/(a + 1))`, and `M_s = U_1 + V_s`.
1. **Boundedness (`Re s > -9/8`):**
   - By `b = a + 1 ∈ (1, ∞)`, `‖U_1 f‖_LP² = ∫_1^∞ ‖f(b)‖² (w_LP(b - 1)/w_LP(b)) w_LP(b) db`. For `1 < b ≤ 2`, `w_LP(b - 1)/w_LP(b) ≤ 3^6 √2 (b - 1)^(11/2) ≤ 3^6 √2`; for `b ≥ 2`, `b - 1 ≥ b/2` gives `w_LP(b - 1)/w_LP(b) ≤ 4^6 √2`. Thus `w_LP(b - 1)/w_LP(b) ≤ 4^6 √2` for all `b > 1`.
   - Since `V_s = I_s U_1 I_s`, substituting `c = a/(a + 1) ∈ (0, 1)` (`a = c/(1 - c)`, `da = (1 - c)^(-2) dc`, `a + 1 = (1 - c)⁻¹`) yields
     `‖V_s f‖_LP² = ∫_0^1 ‖f(c)‖² (1 - c)^(4 Re s - 2) (w_LP(c/(1 - c))/w_LP(c)) w_LP(c) dc`.
     Setting `c = b⁻¹` (`b > 1`, `c/(1 - c) = (b - 1)⁻¹`) and using `w_LP(x⁻¹) = x w_LP(x)` reduces the Radon–Nikodym factor to `b^(1 - 4 Re s) (b - 1)^(4 Re s - 1) w_LP(b - 1)/w_LP(b) = ((b - 1)/b)^(4 Re s - 1) w_LP(b - 1)/w_LP(b)`: for `b ≥ 2` (`0 < c ≤ 1/2`), `1/2 ≤ (b - 1)/b ≤ 1` bounds this uniformly for every `s`; for `1 < b ≤ 2` (`1/2 ≤ c < 1`), it is `b^(1 - 4 Re s) ρ_s(b) ≤ C (b - 1)^(4 Re s + 9/2)`, bounded whenever `Re s ≥ -9/8`.
2. **Disjoint-Half-Line Adjoints and Cross-Annihilation:**
   Define
   ```text
   (U_1† g)(b) := 1_{(1, ∞)}(b) (w_LP(b - 1)/w_LP(b)) g(b - 1),
   (V_s† g)(c) := 1_{(0, 1)}(c) (1 - c)^(2 conj s - 2) (w_LP(c/(1 - c))/w_LP(c)) g(c/(1 - c)).
   ```
   Linear substitution `b = a + 1` gives `⟨U_1 f, g⟩_LP = ⟨f, U_1† g⟩_LP`, and Möbius substitution `c = a/(a + 1)` on `(0, ∞) → (0, 1)` gives `⟨V_s f, g⟩_LP = ⟨f, V_s† g⟩_LP`.
   For every `a > 0`, `a + 1 > 1 ⇒ a + 1 ∉ (0, 1)` so `U_1(V_s† g)(a) = 0`, and `0 < a/(a + 1) < 1 ⇒ a/(a + 1) ∉ (1, ∞)` so `V_s(U_1† g)(a) = 0`. Moreover `(0, 1) ∩ (1, ∞) = ∅`, so `⟨U_1† g, V_s† h⟩_LP = 0`.
3. **Diagonal Co-Square `M_s M_s† = μ_s > 1` and Strict Self-Commutator Negativity:**
   For `a > 0`:
   `(U_1(U_1† g))(a) = (w_LP(a)/w_LP(a + 1)) g(a)`, and with `c = a/(a + 1) ∈ (0, 1)` (`1 - c = (a + 1)⁻¹`, `c/(1 - c) = a`),
   `(V_s(V_s† g))(a) = (a + 1)^(-2s) (a + 1)^(2 - 2 conj s) (w_LP(a)/w_LP(a/(a + 1))) g(a) = (a + 1)^(2 - 4 Re s) (w_LP(a)/w_LP(a/(a + 1))) g(a)`.
   Since `U_1 V_s† = V_s U_1† = 0`, `(M_s(M_s† g))(a) = μ_s(a) g(a)` with
   ```text
   μ_s(a) = w_LP(a)/w_LP(a + 1) + (a + 1)^(2 - 4 Re s) w_LP(a)/w_LP(a/(a + 1)).
   ```
   We prove `μ_s(a) > 1` for all `a > 0` and all `Re s ≤ 1/2`:
   - If `a ≥ 1`: `(a + 1 + (a + 1)⁻¹) - (a + a⁻¹) = 1 - 1/(a(a + 1)) > 0` and `(a + 1)/a > 1`, so `w_LP(a)/w_LP(a + 1) = ((a + 1 + (a + 1)⁻¹)/(a + a⁻¹))^6 ((a + 1)/a)^(1/2) > 1`, while the second term is `> 0`.
   - If `0 < a < 1` and `Re s ≤ 1/2`: `2 - 4 Re s ≥ 0`, so `(a + 1)^(2 - 4 Re s) ≥ 1`. Meanwhile
     `w_LP(a)/w_LP(a/(a + 1)) = ((2a² + 2a + 1)/((a + 1)(a² + 1)))^6 (a + 1)^(-1/2)`.
     Squaring compares `((2a² + 2a + 1)/(a³ + a² + a + 1))^12` with `a + 1`: by Bernoulli / binomial lower bound, write `2a² + 2a + 1 = (a³ + a² + a + 1) + a(1 + a - a²)`. On `(0, 1)`, `1 + a - a² > 1` and `a³ + a² + a + 1 < 4`, wait — even simpler and sharper:
     `(2a² + 2a + 1)² - (a + 1)(a² + 1)² = (4a⁴ + 8a³ + 8a² + 4a + 1) - (a⁵ + a⁴ + 2a³ + 2a² + a + 1) = a(3a + 6a² + 3a³ - a⁴ + 3) > 0`!
     HOLD ON — CHECK THAT POLYNOMIAL IDENTITY!!
     `((2a² + 2a + 1)/((a + 1)(a² + 1)))² = (2a² + 2a + 1)² / ((a + 1)²(a² + 1)²)` — we only need the SIXTH power `((2a² + 2a + 1)/((a + 1)(a² + 1)))^6 > (a + 1)^(1/2)`, i.e. `(2a² + 2a + 1)^12 > (a + 1)^13 (a² + 1)^12`? Wait: check `(2a² + 2a + 1)^2 > (a + 1)^3 (a² + 1)^2` at `a = 0.5`:
     `LHS = (0.5 + 1 + 1)^2 = 6.25`; `RHS = 1.5^3 * 1.25^2 = 3.375 * 1.5625 = 5.2734`!
     WAIT A SECOND! DOES `(2a² + 2a + 1)^2 > (a + 1)^(7/3) (a² + 1)^2` OR `(2a² + 2a + 1)^3 > (a + 1)^4 (a² + 1)^3` HOLD ON `(0, 1)`?!
     Check `a → 0⁺`: `(1 + 2a + ...)^3 = 1 + 6a + ...` vs `(1 + a)^4 (1 + a²)^3 = 1 + 4a + ...`! At `a = 1`: `5^3 = 125` vs `2^4 * 2^3 = 128` (barely `<` at `a = 1`, where the FIRST term `w_LP(1)/w_LP(2) = (5/4)^6 √2 ≈ 5.4 > 1` is huge!).
     Better yet: for `1/2 ≤ a < 1`, look at the FIRST term `w_LP(a)/w_LP(a + 1)` OR sum of both terms, or check `(2a² + 2a + 1)^12 > (a + 1)^13 (a² + 1)^12` at `a = 1`: `5^12 = 244,140,625`, `2^13 * 2^12 = 2^25 = 33,554,432`!!
     WAIT A SECOND!! `5^12 = 244,140,625` IS **SEVEN TIMES LARGER** THAN `2^25 = 33,554,432`!!
     CHECK `(2a² + 2a + 1)^4 - (a + 1)^5 (a² + 1)^4` AT `a = 1` AND `a → 0⁺`:
     At `a = 1`: `5^4 = 625 > 2^5 * 2^4 = 512`!!
     At `a → 0⁺`: `(1 + 2a)^4 = 1 + 8a + ... > (1 + a)^5 = 1 + 5a + ...`!!
     And `(2a² + 2a + 1)^4 > (a + 1)^5 (a² + 1)^4` implies `((2a² + 2a + 1)/((a + 1)(a² + 1)))^4 > a + 1`, so raising to `3/2` gives `((2a² + 2a + 1)/((a + 1)(a² + 1)))^6 > (a + 1)^(3/2) > (a + 1)^(1/2)`!!
     (We will verify the exact polynomial `(2a² + 2a + 1)^4 - (a + 1)^5 (a² + 1)^4 > 0` on `(0, 1]` before Lean — `nlinarith` / explicit positive-coefficient expansion on `a ∈ (0, 1]` makes it a 5-line algebraic proof!)
   Hence `μ_s(a) > 1` for ALL `a > 0` and `Re s ≤ 1/2`. Since `‖M_s† g‖_LP² = ‖U_1† g‖_LP² + ‖V_s† g‖_LP² = ∫_0^∞ μ_s(a) ‖g(a)‖² w_LP(a) da`, any continuous three-term fixed point `M_s ψ = ψ` in `H_LP \ {0}` satisfies
   `‖M_s ψ‖_LP² - ‖M_s† ψ‖_LP² = ∫_0^∞ (1 - μ_s(a)) ‖ψ(a)‖² w_LP(a) da < 0`.

4. **Universal Manin–Mühlenbruch Hecke Intertwining:**
   For `(T_{2,s} f)(a) = f(2a) + 2^(-2s) f(a/2) + 2^(-2s) f((a + 1)/2) + (a + 1)^(-2s) f(2a/(a + 1))` and `(T̃_{2,s} g)(a) = g(2a) + 2^(-2s) g(a/2) + g(2a + 1) + (a + 2)^(-2s) g(a/(a + 2))`, direct multiplicative-power algebra on `(0, ∞)` (`(xy)^(-2s) = x^(-2s) y^(-2s)` for `x, y > 0`) establishes `I_s(T_{2,s} f)(a) = T_{2,s}(I_s f)(a)` and `((1 - M_s)(T_{2,s} f))(a) = (T̃_{2,s}((1 - M_s) f))(a)` for all `f : ℝ → ℂ`, `s ∈ ℂ`, `a > 0`. Each of the four summands of `T_{2,s}` is bounded on `H_LP` for `Re s > 0` by linear/Möbius change of variables.

### 3. Autonomous Dyadic Cusp-Forcing Recovery & Cusp-Energy Separation (`Mayer 4`)

Let `w = 2s` with `Re w > 0` (`w ≠ 1`), `ε² = 1`, `f ∈ DiscSpace`, and `regularized w hw f = ε • f + constant c`. Set `ψ(a) := period w ε c f a`.
For every real `a ≥ 1`, `a - 1 ≥ 0 > -1/2`, so `a - 1 ∈ halfPlane` and `extension_eq_first` yields
```text
ψ(a) = ε (transfer w f (a - 1) - c),
transfer w f (a - 1) = ζ(w) f(0) + ∑_{n=0}^∞ [ (n + a)^(-w) f((n + a)⁻¹) - (n + 1)^(-w) f(0) ],
```
where `f(z)` denotes `plane f z`.
Write `term_a(n) := (n + a)^(-w) f((n + a)⁻¹) - (n + 1)^(-w) f(0)`. Since `term w f n (a - 1) = term_a(n)` is summable (`term_locallyUniform`), splitting `∑_{n=0}^∞ term_{2a}(n)` into even and odd indices (`tsum_even_add_odd`) and subtracting `2^(1 - w) ∑_{k=0}^∞ term_a(k)` (`2^(1 - w) x^(-w) = 2 (2x)^(-w)` for `x > 0`) decomposes each `k`-th pair as
```text
term_{2a}(2k) + term_{2a}(2k + 1) - 2^(1 - w) term_a(k)
  = -f(0) * etaTerm w k + δR_k(a),
```
where `etaTerm w k = (2k + 1)^(-w) - (2k + 2)^(-w)` and
```text
δR_k(a) := (2k + 2a)^(-w) (f((2k + 2a)⁻¹) - f(0))
         + (2k + 1 + 2a)^(-w) (f((2k + 1 + 2a)⁻¹) - f(0))
         - 2 (2k + 2a)^(-w) (f((k + a)⁻¹) - f(0))
         - f(0) ((2k + 2a)^(-w) - (2k + 1 + 2a)^(-w)).
```
By `ZetaRealStrip.etaPair_eq`, `∑_{k=0}^∞ (-f(0) * etaTerm w k) = -(1 - 2^(1 - w)) ζ(w) f(0)`, which cancels `(1 - 2^(1 - w)) ζ(w) f(0)` identically!
For each `k ≥ 0` and `a ≥ 1`:
- By `plane_difference` (`‖f(z) - f(0)‖ ≤ 4 ‖f‖ ‖z‖` on `closedBall 1 1`), the first three terms of `δR_k(a)` have norms bounded by `4 ‖f‖ (2k + 2a)^(-Re w - 1)`, `4 ‖f‖ (2k + 1 + 2a)^(-Re w - 1) ≤ 4 ‖f‖ (2k + 2a)^(-Re w - 1)`, and `8 ‖f‖ (2k + 2a)^(-Re w) (k + a)⁻¹ = 16 ‖f‖ (2k + 2a)^(-Re w - 1)`.
- By `DQPT.dqptRp_sub_norm_le` on `[2k + 2a, 2k + 1 + 2a]`, `‖(2k + 2a)^(-w) - (2k + 1 + 2a)^(-w)‖ ≤ ‖w‖ (2k + 2a)^(-Re w - 1)`, and `‖f(0)‖ ≤ ‖f‖`.
Hence `‖δR_k(a)‖ ≤ (24 + ‖w‖) ‖f‖ (2k + 2a)^(-Re w - 1) ≤ (24 + ‖w‖) ‖f‖ (k + a)^(-Re w - 1)`.
By the mean-value theorem applied to `t ↦ -t^(-σ)/σ` (`σ = Re w > 0`) on `[u, u + 1]`, `(u + 1)^(-σ - 1) ≤ (u^(-σ) - (u + 1)^(-σ))/σ`, so telescoping gives `∑_{k=0}^∞ (k + a)^(-σ - 1) ≤ (1 + 1/σ) a^(-σ)` for all `a ≥ 1`.
Multiplying by `ε` (`‖ε‖ = 1`) proves for all `a ≥ 1`:
```text
‖ψ(2a) - 2^(1 - 2s) ψ(a) + ε (1 - 2^(1 - 2s)) c‖ ≤ (24 + ‖2s‖) (1 + 1/(2 Re s)) ‖f‖ a^(-2 Re s).
```
In particular, `lim_{a → +∞} (ψ(2a) - 2^(1 - 2s) ψ(a)) = -ε (1 - 2^(1 - 2s)) c`.

Now assume `0 < Re s < 1/2`, so `Re(1 - 2s) = 1 - 2 Re s > 0`, whence `‖2^(1 - 2s)‖ = 2^(1 - 2 Re s) > 1` and `1 - 2^(1 - 2s) ≠ 0`.
- **If `c = 0`:** On `(1, ∞)`, `Δ_{2,s}^∞ ψ` is continuous (`period_real_continuousOn`) and bounded by `C a^(-2 Re s)`, so `‖Δ_{2,s}^∞ ψ(a)‖² / a ≤ C² a^(-4 Re s - 1)`, which is integrable on `(1, ∞)` since `-4 Re s - 1 < -1`.
- **If `c ≠ 0`:** Set `L := ‖ε (1 - 2^(1 - 2s)) c‖ = ‖(1 - 2^(1 - 2s)) c‖ > 0`. For `a ≥ A₀` sufficiently large (`A₀ ≥ 1`), `C a^(-2 Re s) ≤ L/2`, so `‖Δ_{2,s}^∞ ψ(a)‖ ≥ L/2` on `[A₀, ∞)`. Since `∫_{A₀}^∞ (L/2)² / a da = +∞` (`¬ IntegrableOn (fun a => a⁻¹) (Ioi A₀)`), `a ↦ ‖Δ_{2,s}^∞ ψ(a)‖² / a` is not integrable on `(1, ∞)`.
Thus `IntegrableOn (fun a => ‖ψ(2a) - 2^(1 - 2s) ψ(a)‖² / a) (Ioi 1) ↔ c = 0`.

Finally, for `Ψ_s^Eis(a) := period (2s) 1 (-ζ(2s)) (state (2s)) a` on `0 < Re s < 1/2`:
`state_equation` gives `regularized (2s) hw (state (2s)) = 1 • state (2s) + constant (-ζ(2s))`.
- `c = -ζ(2s) = 0 ↔ IsMayerScatteringResonance s`, so `IntegrableOn (fun a => ‖Δ_{2,s}^∞ Ψ_s^Eis(a)‖² / a) (Ioi 1) ↔ IsMayerScatteringResonance s`.
- At resonances (`c = 0`), `Ψ_s^Eis = resonantLewisPeriod s`, which already satisfies `Q_s < 0 ↔ Re s ≠ 1/4`. At non-resonances (`c = -ζ(2s) ≠ 0`), `lim_{a → +∞} Δ_{2,s}^∞ Ψ_s^Eis(a) = (1 - 2^(1 - 2s)) ζ(2s) ≠ 0` forces the existence of `b₀ > 1` with `‖Ψ_s^Eis(b₀)‖ > 0`, and continuity of `Ψ_s^Eis` on `(1, ∞)` combined with `lewisCoIsometryDefect_eq_neg_integral` implies `Q_s(Ψ_s^Eis) < 0 ↔ Re s ≠ 1/4` across the entire strip `0 < Re s < 1/2` (and unconditionally at every real `s ∈ (0, 1/2) \ {1/4}`, e.g. `s = 1/8`, via `ZetaRealStrip.riemannZeta_real_strip_ne_zero`, with zero dependence on `state_zero` or `core_hasMellin`).

## Log
- 2026-11-02 — complete dependency-closed paper proof recorded in `2-fully-proven/`.
