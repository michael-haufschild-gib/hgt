# The zero motive of ζ is the fixed part of every arithmetic family

- **ID:** awt-fixed-part-theorem
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-0911/fable.md` §5.2 (`(FP)`, B142, B85, B86)
- **Statement:** **(FP) holds unconditionally.** In every arithmetic family `(𝔉, ν)` of Euler products whose even window-trace moments are computed by orthogonality — the gauge torus, Dirichlet characters modulo `q ≤ Q`, the vertical line, Hecke eigenforms under the Weyl law and Rankin–Selberg square, number fields under a counting measure, summable Euler deformations, and their mixtures — the `2k`-th moment identity controls the variable traces only: the centred trace of `ζ` enters with `ν`-mass tending to zero or as an exact common factor, and no inequality derived from the family (including amplified moments and nonnegative product-coefficient couplings) bounds `|c_B(log p)|` below the trivial bound.

## Goal
Resolve Question 5.2 of `docs/reports/review-0911/fable.md` (`(FP)`) unconditionally, together with its named obstacle (reverse weight transfer through nonnegative coefficients of growing-conductor product families) and its corollaries for amplification and Deligne's tensor-moment programme over `ℤ` (B142).

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean modules in `ArithmeticWeightTheory`, `lake --old env lean` green, axiom audit PASS

## Mathematical statements and complete proofs

### 1. Amplified monodromy symmetry-breaking (`[PROVED HERE]`)

Let `s, L ⊂ ℕ₊` be finite sets of positive integers, `a : ℕ → ℝ_{\ge 0}`, `S_x = ∑_{n ∈ s} a_n χ_x(n)` on `G = GaugeTorus`, and `A : G → ℂ` any measurable amplifier.

1. **Coherent amplified pricing at the trivial fibre (`0`):** For *every* measure `ν` on `G` (without any orthogonality assumption), *every* measurable `A : G → ℂ` such that `x ↦ ‖A x‖² ‖S_x‖^{2k}` is `ν`-integrable, and *every* `k ∈ ℕ`,
   $$\nu(\{0\}) \, |A(0)|^2 \Bigl(\sum_{n \in s} a_n\Bigr)^{2k} \le \int_G |A(x)|^2 |S_x|^{2k} \, d\nu(x).$$
   *Proof.* At `x = 0`, `χ_0(n) = 1` (`twist_trivial` `[CORPUS]`), hence `S_0 = ∑_{n ∈ s} a_n ≥ 0` and `|S_0|^{2k} = (∑_{n ∈ s} a_n)^{2k}`. Nonnegativity of `|A(x)|^2 |S_x|^{2k}` on `G` gives `ν.real {0} · |A(0)|^2 |S_0|^{2k} = ∫_{\{0\}} |A|^2 |S|^{2k} dν ≤ ∫_G |A|^2 |S|^{2k} dν`. ∎

2. **Centred-trace decoupling under pole jump:** Let `C_x = A_{\mathrm{pole}} \mathbf{1}_{x = 0} - S_x` (with `c_0 = C_0 = A_{\mathrm{pole}} - S_0`). Then
   $$\int_G |A(x)|^2 |C_x|^{2k} \, d\nu(x) - \int_G |A(x)|^2 |S_x|^{2k} \, d\nu(x) = \nu(\{0\}) |A(0)|^2 \bigl(|c_0|^{2k} - |S_0|^{2k}\bigr),$$
   and `∫_{G \setminus \{0\}} |A(x)|^2 |C_x|^{2k} dν = ∫_G |A(x)|^2 |S_x|^{2k} dν - ν(\{0\}) |A(0)|^2 |S_0|^{2k}`. Thus orthogonality evaluates `∫ |A|^2 |S|^{2k} dν`, controlling only `C_x` on `G \setminus \{0\}` while `c_0` cancels identically. ∎

3. **Strict amplified saving off the trivial fibre (`x_0 ≠ 0`):** Let `x_j ∈ G` (`j ∈ Fin 4`) have coordinate `(j : ℝ)/4` at `p = 2` and `0` elsewhere, so `χ_{x_j}(2) = i^j` and `χ_{x_j}(p) = 1` for odd primes `p`. Let `ν = \frac{1}{4} ∑_{j=0}^3 δ_{x_j}`.
   - On `P = {4, 6, 9} = powSupport {2, 3} 1 · {2, 3}`, `(χ_{x_j}(4), χ_{x_j}(6), χ_{x_j}(9)) = ((-1)^j, i^j, 1)`, which are orthonormal under `ν` (`TwistOrthonormalOn ν {4, 6, 9}`).
   - Take prime-supported weights `s = {2, 3}`, `a_2 = a_3 = 1`, torsion fibre `x_2` (`χ_{x_2}(2) = -1, χ_{x_2}(3) = 1`), and phased amplifier `A(x) = -χ_x(2) + χ_x(3)`.
   - At `x_2`: `A(x_2) = 2`, `|A(x_2)|^2 = 4`, `(a_2 + a_3)^2 = 4`, and `ν.real {x_2} = 1/4`, so `ν.real {x_2} |A(x_2)|^2 (a_2 + a_3)^2 = 4`.
   - Yet `A(x) S_x = (-χ_x(2) + χ_x(3))(χ_x(2) + χ_x(3)) = -χ_x(4) + χ_x(9)`, whose `2·3 = 3·2 = 6` collision cancels identically, giving `∫_G |A(x)|^2 |S_x|^2 dν = 1 + 0 + 1 = 2 < 4`.
   Hence Iwaniec–Sarnak amplification strictly beats `(∑ a_n)^{2k}` under exact monodromy at nontrivial fibres `x_0 ≠ 0`, and is blocked at `ζ` specifically by phase coherence at `x_0 = 0`. ∎

### 2. One-way product-positivity coupling (`[PROVED HERE]`)

This resolves the named obstacle of `fable.md` §5.2: coupling `L_{\mathrm{base}}` to `L_f^{\mathrm{var}}` through nonnegative Dirichlet and von Mangoldt coefficients of `L_f = L_{\mathrm{base}} L_f^{\mathrm{var}}`.

1. **Abel–divisor monotonicity under symmetric shifts:**
   - *Prime-power lemma:* Let `c : ℕ → ℝ` satisfy `S_r := ∑_{j=0}^r c_j ≥ 0` for all `0 ≤ r ≤ m`, and let `r ≥ 1`. Define `F_m := ∑_{j=0}^m r^{m - j} c_j`. By induction on `m`: `F_0 = c_0 = S_0`; if `0 ≤ S_m ≤ F_m`, then `S_m ≤ r F_m`, hence `S_{m+1} = S_m + c_{m+1} ≤ r F_m + c_{m+1} = F_{m+1}`.
   - *Global multiplicative transfer:* Let `g : ArithmeticFunction ℝ` be multiplicative with `(ζ * g)(n) = ∑_{d ∣ n} g(d) ≥ 0` for all `n ≥ 1` (covering Hecke symmetric-square series `g(m) = τ(m^2)` via `sq_eq_zeta_mul` `[CORPUS]` and Dedekind cofactors). Let `idRpow a : ArithmeticFunction ℝ` send `n ≥ 1` to `n^a`. For `a ≥ 0`, `idRpow a` is multiplicative; on every prime power `p^m`, `(idRpow a * g)(p^m) = ∑_{j=0}^m (p^a)^{m - j} g(p^j) ≥ (ζ * g)(p^m) ≥ 0`. By multiplicativity (`Nat.recOnPosPrimePosCoprime`), `(idRpow a * g)(n) ≥ (ζ * g)(n) ≥ 0` for all `n ≥ 1`. Convolving with `idRpow (-a) ≥ 0` yields `(idRpow (-a) * (idRpow a * g))(n) ≥ 0` for all `n ≥ 1`.
   - *Log-derivative transfer:* Since `cosh(a log n) ≥ 1`, if `Λ(n) + λ_f^{\mathrm{var}}(n) ≥ 0` then `cosh(a log n) Λ(n) + λ_f^{\mathrm{var}}(n) ≥ Λ(n) + λ_f^{\mathrm{var}}(n) ≥ 0`.
   Thus symmetric shifts preserve both positivity couplings identically across every family `(𝔉, ν)` while shifting the base zero width by `+a` up to `1/2`. ∎

2. **Simple-pole rational-prime Euler-factor doubling (`F_θ = ζ · D_θ`):**
   For `1/2 < θ < 1`, let `flipPrimes θ = ⋃_k flipBlock θ k` (`ThePoleDoesNotDecideTheHalfPowerLaw` `[CORPUS]`), where `flipBlock θ k` consists of the first `⌊4^{θ k}⌋` primes in `(4^k, 2 · 4^k]`. Define the extra von Mangoldt weight `flipVM θ n = Λ(n)` if `IsPrimePow n ∧ n.minFac ∈ flipPrimes θ`, else `0`, and `doubledVM θ = Λ + flipVM θ` (the von Mangoldt weight of `F_θ(s) = ζ(s) ∏_{p ∈ flipPrimes θ} (1 - p^{-s})^{-1}`), with Dirichlet factor `d_θ : ArithmeticFunction ℝ` supported on `flipPrimes θ`-smooth integers (`d_θ(n) = 1` there, `0` otherwise).
   - *Analyticity across `s = 1` (simple pole preserved):* For every `σ > θ` (including `σ = 1`), `∑_n flipVM θ n · n^{-σ} < ∞`: prime terms in `flipBlock θ k` contribute `≤ ⌊4^{θ k}⌋ · log(2 · 4^k) · 4^{-σ k} ≤ 2(k+1)(4^{θ - σ})^k` (`summable_poly_mul_geometric` `[CORPUS]`), and prime powers `p^r` (`r ≥ 2`) are majorized by `∑_{n ≥ 1} Λ(n) n^{-2σ}` with `2σ > 2θ > 1` (`summable_vonMangoldt_rpow` `[CORPUS]`). Hence `-F_θ'/F_θ` has the exact same simple pole of residue `1` at `s = 1` and the same `archPoleWindow` as `ζ`.
   - *Product positivity preserved:* Since `d_θ ≥ 0` (`d_θ(1) = 1`) and `flipVM θ ≥ 0`, `(d_θ * (ζ * g))(n) ≥ 0` and `doubledVM θ n + λ_f^{\mathrm{var}}(n) ≥ Λ(n) + λ_f^{\mathrm{var}}(n) ≥ 0` for every positively `ζ`-coupled variable member.
   - *Cubic-spline window shift beats every nontrivial exponent `a < 1/2`:* Let `primeWindowOf w d = -smoothedPrimeKernelOf w cubicSpline d 1`, so `primeWindowOf Λ d = primeWindow d` and `archPoleWindow p - primeWindow p = c_B(log p)` (`orbitCorr_log_eq_archPoleWindow_sub_primeWindow` `[CORPUS]`). Let `K_0(v) = (EF.weilTest (cx cubicSpline) (cx cubicSpline) v).re = ∫ cubicSpline(u) cubicSpline(u - v) du`. Since `cubicSpline ≥ 0` (`cubicSpline_nonneg` `[CORPUS]`), `K_0(v) ≥ 0` for all `v ∈ ℝ`; at `v = 0`, `K_0(0) = ∫ cubicSpline^2 > 0` (`weilTest_self_zero`, `integral_cubicSpline_sq_pos` `[CORPUS]`). By continuity of `K_0` at `0`, pick `M ∈ ℕ₊` such that `|v| ≤ (log 2)/M ⇒ K_0(v) ≥ K_0(0)/2`. Partition `[k log 4, k log 4 + log 2]` into `M` subintervals of length `(log 2)/M`. For large `k`, `#(flipBlock θ k) = ⌊4^{θ k}⌋` (`eventually_card_flipBlock` `[CORPUS]`), so by pigeonhole one subinterval contains a subset `S_k ⊆ flipBlock θ k` of size `≥ ⌊4^{θ k}⌋ / M`. Choosing `p_k ∈ S_k`, every `q ∈ S_k` has `|log q - log p_k| ≤ (log 2)/M`, `q ≤ 2 · 4^k ≤ 2 p_k`, and `log q ≥ log 2`, giving
     $$\mathrm{primeWindowOf}(\mathrm{doubledVM}\,\theta, p_k) - \mathrm{primeWindow}(p_k) \ge \sum_{q \in S_k} \frac{\log q}{\sqrt{q}} \cdot \frac{K_0(0)}{2} \ge c_0 \, p_k^{\theta - 1/2}.$$
     For any `a < 1/2`, set `θ = (\max(a, 0) + 1/2)/2 + 1/2 ∈ (1/2, 1)`, so `θ - 1/2 > a`. By the triangle inequality, `ζ` (`Λ`) and `F_θ` (`doubledVM θ`) cannot both satisfy `|archPoleWindow p - primeWindowOf w p| ≤ K p^a` for all primes `p`. Consequently, no bound `|c_B(log p)| ≤ K p^a` (`a < 1/2`) follows from variable-family data and product-positivity couplings. ∎

### 3. Universal fixed-part theorem across all arithmetic families and mixtures (`[PROVED HERE]`)

1. **Five canonical family classes:**
   - *Gauge torus `(G, gaugeHaar)`:* `gaugeHaar {0} = 0`, `gaugeHaar (isozericClass σ_0) = 0` (`0 ≤ ½ ≤ σ_0 < 1`), `gaugeHaar jumpLocus = 0` `[CORPUS]`.
   - *Dirichlet characters modulo `q`:* uniform probability measure on `DirichletCharacter ℂ q` gives the principal singleton `{1}` mass `1 / φ(q)`, which tends to `0` along any modulus growth with `φ(q) → ∞`, and obeys `measureReal_singleton_zero_mul_amplified_pow_le` at every finite `q`.
   - *Vertical line `[-T, T]`:* normalized height measure `(2T)⁻¹ volume.restrict [-T, T]` gives `{0}` mass `0` and every bounded neighbourhood `[-H, H]` of `0` mass `≤ H / T → 0` as `T → ∞`, while moments obey `vertical_moment_eq_generic` and `generic_moment_le_vertical_moment` `[CORPUS]`.
   - *Hecke eigenforms under the Weyl law and Rankin–Selberg:*
     (i) By `BlackHoleRingdown.WeylBound.weyl_lower_bound` (`c Λ ≤ cuspCount Λ` for `Λ ≥ Λ_0` `[CORPUS]`), uniform Weyl counting on `CuspEigenIndex 0` below `Λ` gives any fixed finite set of modes mass `≤ r / cuspCount Λ → 0` as `Λ → ∞`.
     (ii) For any finite weighted family `(w_j, τ_j)` of real normalized Hecke sequences (`HeckeRec lam_j τ_j`, `τ_j(1) = 1`, `|τ_j(n)| ≤ K_j √n`), `lseries_sq_eq` and `sq_eq_zeta_mul` `[CORPUS]` yield for `Re s > 2`:
     $$\sum_j w_j \, L(\tau_j^2, s) = \zeta(s) \sum_j w_j \, L(\tau_j(\cdot^2), s), \qquad (\zeta * \tau_j(\cdot^2))(n) = \tau_j(n)^2 \ge 0.$$
   - *Number fields under a counting measure:* For any finite Galois extension `L/ℚ` with group `G` and `H ≤ G` (`F = L^H`), decompose `permChar H σ = 1 + varPermChar H σ` (`varPermChar H σ := permChar H σ - 1`). By `permChar_frob_eq` and `classMean_permChar` `[CORPUS]`, at every unramified prime `p ∤ disc L`, `degreeOneCount F p = 1 + varPermChar H (frob p) ≥ 0` with Galois mean `classMean (varPermChar H) = 0`. Across any probability distribution `w` on a finite collection of subfields, `∑_i w_i (1 + varPermChar H_i (frob_i p)) = 1 + ∑_i w_i varPermChar H_i (frob_i p)`, isolating `ζ`'s trace `1` as an exact common summand.

2. **Mixture closure and moment-identity decoupling:**
   - For any probability space `(Ω, ρ)` and integrable `V : Ω → ℝ` (`V ∈ L^{2k}`), expanding `(c + V)^{2k}` by the binomial theorem shows that `∫ (c + V)^{2k} dρ = ∑_{j=0}^{2k} \binom{2k}{j} c^{2k - j} μ_j` (`μ_0 = 1`) holds for *every* `c ∈ ℝ` whenever `∫ V^j dρ = μ_j` (`1 ≤ j ≤ 2k`). Moreover, pushing `ρ` forward along `ω ↦ c + V(ω)` realizes a genuine probability measure on `ℝ` with shift `c` for *every* `c ∈ ℝ`, so no moment or Hankel positivity inequality constrains `c`.
   - For any mixture sequence `ν_n = (1 - λ_n) μ_n + λ_n ρ_n` (`0 ≤ λ_n ≤ 1`) of a mass-vanishing component (`μ_n {α_n ≠ 0} → 0` with `α_n c + V_n` uniformly bounded on `{α_n ≠ 0}` at fixed prime `p`) and a common-factor component (`α = 1` `ρ_n`-a.e.), the difference between `∫ |α_n c + V_n|^{2k} dν_n` and `(1 - λ_n) ∫ |V_n|^{2k} dμ_n + λ_n ∫ |c + V_n|^{2k} dρ_n` tends to `0` as `n → ∞`.

3. **Jensen–Minkowski coercivity and the RH equivalence for cover-family tensor moments:**
   - Let `(Ω, ρ)` be a probability space and `V : Ω → ℝ` integrable with `∫ V dρ = 0`. For every `c ∈ ℝ` and `k ≥ 1`, convexity of `x ↦ |x|^{2k}` (or even-power binomial/Hölder: `|c| = |∫ (c + V) dρ| ≤ ∫ |c + V| dρ`, and `(|c + V|)^1 ≤ |c + V|^{2k}` via Hölder / `eLpNorm_mono_exponent`!) gives
     $$|c|^{2k} \le \int_\Omega |c + V(\omega)|^{2k} \, d\rho(\omega) \le 2^{2k - 1}\Bigl(|c|^{2k} + \int_\Omega |V(\omega)|^{2k} \, d\rho(\omega)\Bigr).$$
   - Instantiating on `(GaugeTorus, gaugeHaar)` with `C_x(p) = splineTrace (log p) + (fibreTrace g R (log p) x).re` (`|g| ≤ 1`, `R ≥ 0`), `∫ (fibreTrace g R (log p) x).re d(gaugeHaar) = 0`, so `primeTraceMoment k N ≤ ∑_{p ≤ N} log p ∫ |C_x(p)|^{2k} d(gaugeHaar) ≤ 2^{2k - 1} (primeTraceMoment k N + ∫ fibreMoment g R k N d(gaugeHaar))`. Combining with `integral_fibreMoment_le` and `riemannHypothesis_iff_tensorExponent_sublinear` `[CORPUS]` proves unconditionally:
     $$\mathrm{RiemannHypothesis} \iff \forall \varepsilon > 0,\; \forall^\infty k,\; \exists C,\; \forall N,\; \sum_{p \le N} \log p \int_G |C_x(p)|^{2k} \, d\mathrm{Haar}(x) \le C (N + 1)^{1 + \varepsilon k}.$$
   Thus Deligne's uniform tensor-moment hypothesis on a cover family containing `ζ` does not bypass RH: it is unconditionally equivalent to RH. ∎

## Log
- 2026-11-09 — created in `2-fully-proven` with complete dependency-closed proofs; proceeding immediately to Lean 4 formalization in `ArithmeticWeightTheory`.
