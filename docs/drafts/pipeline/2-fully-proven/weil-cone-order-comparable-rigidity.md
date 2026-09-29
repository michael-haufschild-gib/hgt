# Weil-cone rigidity along order-comparable directions

- **ID:** weil-order-comparable
- **Stage:** 2-fully-proven (paper; relies on the Herglotz representation of MUST-520)
- **Type:** THEOREM (paper)
- **Source:** MC conjecture loop, cycle 139 (`1-in-progress/mc-conjecture-loop-2026-09-28.md`); HF lane L61, MUST-524, HF-F54
- **Statement:** A Weil-positive weight system with pole weight 1 whose difference from Λ has constant sign on `n ≥ 2` equals Λ. Its existence is equivalent to RH.

## Setting
- `W` is the paper Weil cone of `weil-cone-finite-type-uniqueness.md` (Input B).
  - `lam` is Weil-positive when `W_lam(h⋆h̃*) ≥ 0` for **all** `h ∈ C_c^∞(ℝ^×_{>0})`.
  - The functional carries ζ's archimedean term and the pole term with weight `β = 1`.
- In `x = log n` coordinates, the distribution `T = (e^{x/2} + e^{−x/2}) + arch − Σ lam(n) n^{−½}(δ_{log n} + δ_{−log n})` is positive definite, hence tempered (Bochner–Schwartz).
  - In particular `Σ_{n≤x} lam(n) n^{−½} = 2√x + O((log x)^C)`, so **the pole weight is automatically 1**.
- Input B (Bochner–Schwartz plus Paley–Wiener–Schwartz) gives:
  - `Φ_lam := Γ̃ − H_lam` is holomorphic with `Re Φ_lam ≥ 0` on `σ > ½`;
  - `H_lam := D_lam − 1/(s−1)` and `Γ̃(s) = ½ψ(s/2+1) − ½log π`;
  - `Re Φ_lam(½+η+it) = (P_η ⋆ μ_lam)(t)`, where `μ_lam ≥ 0` is tempered and `P_η(t) = η/(π(η²+t²))`.
- For Λ: `Γ̃ − H_Λ = ξ'/ξ`, using `½ψ(s/2) + 1/s = ½ψ(s/2+1)`.
- The formal `RHTower.WeilPositive` tests only polar functions, so it is weaker and does not fix the pole weight. Every paper-W system is formally Weil-positive.

## Theorem C
Let `lam ∈ W`, and suppose `lam − Λ` has constant sign on `n ≥ 2`. Then `lam = Λ`, and RH holds.
- Corollary: RH ⟺ `W ∩ {lam ≤ Λ} ≠ ∅` ⟺ `W ∩ {lam ≥ Λ} ≠ ∅`, and each of these sets is `{Λ}` whenever it is nonempty.
- For the polar-only formal cone, the upward case keeps pole weight 1 by `RHTower.weil_supersystem_excess_small` (Lean). The downward case at pole weight `< 1` is not covered there.

## Proof

**Step 1 (Landau ⇒ RH).** Put `u := |lam − Λ| ≥ 0`, so that `D_u = ±(D_lam − D_Λ)` on `σ > 1`.
- `D_lam` is holomorphic on `σ > ½` except for a simple pole at 1 with residue 1.
- `D_Λ = −ζ'/ζ` is holomorphic near every point of the real segment `(0, 1)`, since `ζ(σ) = η(σ)/(1 − 2^{1−σ}) ≠ 0` there. It also has residue 1 at `s = 1`.
- So `D_u` continues holomorphically to a complex neighbourhood of `(½, ∞)`.
- Landau's theorem (a Dirichlet series with nonnegative coefficients is singular at its real abscissa of convergence) gives `σ_c(D_u) ≤ ½`. Hence `D_u` converges absolutely and is holomorphic on `σ > ½`.
- Then `−ζ'/ζ = D_lam ∓ D_u` is holomorphic on `σ > ½` except at `s = 1`. So ζ has no zeros in `σ > ½`, which is RH.
- Consequently `μ_Λ = πΣ_ρ δ_γ`, counted with multiplicity.

**Step 2 (the boundary distribution).**
- On `σ > ½`: `D_u = ±(H_lam − H_Λ) = ±(Φ_Λ − Φ_lam)`. Hence `Re D_u(½+η+it) = (P_η ⋆ T)(t)`, where `T := ∓(μ_lam − μ_Λ)`: upward `T = μ_Λ − μ_lam`, downward `T = μ_lam − μ_Λ`.
- (a) **T is positive definite.** `P_η ⋆ T(t) = Σ_n u(n) n^{−½−η} cos(t log n)` is the Fourier transform of a positive measure. As `η → 0`, `T` is the Fourier transform of the tempered positive measure `½Σ u(n) n^{−½}(δ_{log n} + δ_{−log n})`. Temperedness follows from the Weil box `|lam(n)| ≤ √n(log n + C₀)`, formal as `RHTower.abs_le_boxWidth_of_weilPositiveUpTo`.
  - In particular `|P_η ⋆ T(t)| ≤ P_η ⋆ T(0)` for all `t` and all `η > 0`.
- (b) **Spectral gap.** `supp FT(T) ⊆ {|x| ≥ log 2}`, because no integer lies in `(1, 2)`. So `T ⋆ K ≡ 0` for every Schwartz `K` with `supp K̂ ⊂ (−log 2, log 2)`.
- (c) **Local form.** Write `μ_lam = Σ_ρ c_ρ δ_γ + ν'` with `c_ρ ≥ 0` and `ν' ≥ 0` carried off the zero ordinates. Put `d_ρ := πm_ρ − c_ρ`, the atom deficit.
  - Two facts are used near an ordinate: `η·(P_η ⋆ ν')(x) → ν'({x})/π` as `η → 0`, for every `x`; and tempered atoms at distance `≥ δ > 0` contribute `O(η)`.

**Step 3 (upward).** Here `T = Σ d_ρ δ_γ − ν'`.
- At `t = 0` (not an ordinate): `P_η ⋆ T(0) ≤ Σ_ρ πm_ρ P_η(γ) ≤ η Σ 1/γ² → 0`.
- At an ordinate with `d₀ > 0`: `P_η ⋆ T(γ₀) ≥ d₀/(πη)·(1 − o(1))`. This contradicts (a).
- So every `d_ρ ≤ 0`, and `T ≤ 0` is a negative measure.
- (b) with a Fejér kernel `K_b(t) = (b/2π) sinc²(bt/2) ≥ 0`, `b < log 2`, gives `∫ K_b d|T| = 0`. Two incommensurable bandwidths have no common zero, so `T = 0`.
- Then `Re D_u(½+η+i·) ≡ 0`. Uniqueness of coefficients of absolutely convergent Dirichlet series gives `u = 0`.

**Step 4 (downward).** Here `T = −Σ d_ρ δ_γ + a₀δ₀ + ν`, where `a₀ = μ_lam({0}) ≥ 0` and `ν` has no atom at 0.
- (a) at `0` and at `γ₀` gives `d₀/(πη)·(1 − o(1)) ≤ |P_η ⋆ T(γ₀)| ≤ P_η ⋆ T(0) ≤ a₀/(πη) + o(1/η)`, hence **`d_ρ ≤ a₀`** for every zero.
- (b) at `t = 0` with `K_b`:
  `0 = a₀K_b(0) + (ν ⋆ K_b)(0) − Σ_ρ d_ρ K_b(γ) ≥ a₀(K_b(0) − Σ_ρ K_b(γ)) + (ν ⋆ K_b)(0)`.
- The constant: `K_b(γ)/K_b(0) ≤ 4/(bγ)²`.
  - Under RH, `Σ_ρ 1/(¼+γ²) = Σ_ρ 1/(ρ(1−ρ)) = 2 + γ_E − log 4π < 0.0462`.
  - The same identity forces `|γ| > 6.5` (each ordinate is counted together with its conjugate), so `Σ_ρ 1/γ² < 0.0465`.
  - With `b = 0.69`: `Σ_ρ K_b(γ) ≤ 0.39 K_b(0)`.
- Therefore `a₀ = 0`, every `d_ρ ≤ 0`, and `T ≥ 0`. Two incommensurable Fejér kernels in (b) give `T = 0`, and `u = 0` as in Step 3. ∎

## What is new
- Relation to known uniqueness results:
  - L61 (Lean) gives only log-density maximality of supersystems.
  - MUST-524 needs two-sided perturbations.
  - MUST-357 (Lean) needs `Σ|w| n^{−½} < ∞`.
  - The formal Mertens-constant theorem (`mertens_constant_nonpos_of_weilAtomSymbol_nonneg`) needs an exact expansion `A log x + B + o(1)`.
- Theorem C removes all of these hypotheses for order-comparable perturbations. The downward direction ("`Λ − c` needs regular rigidity", L61) is closed at pole weight 1.
- Two mechanisms carry the proof:
  - *positive definiteness* of a constant-sign perturbation's boundary distribution, which bounds every atom deficit by the atom at the centre `s = ½`;
  - the *prime-free gap* `(1, 2)`, which makes the perturbation invisible to low-frequency kernels. It is the same gap that pays the archimedean deficit `h(0) = −0.686` in L131.
- **Consequence for the uniqueness core:** a second Weil-positive completion with pole weight 1 must differ from Λ with both signs infinitely often. Constant-sign and two-sided (MUST-524) directions are excluded.
- In the paper cone `W`, both directions are closed, because temperedness fixes the pole weight at 1.
- In the polar-only formal cone, downward deletions of positive density remain. There, pole weight `< 1` is not excluded by the definition.
  - The low-frequency test `K ≥ 0` gives `β ≥ 1 − Σ_ρ K(γ)/pole(K)`.
  - Every system of the form `βΛ + e` with `e` of continuous boundary symbol and `β < 1` fails: its absolutely continuous density `(1−β)h − Re D_e` integrates against low-frequency `K` to `(1−β)∫hK < 0`.

## Second proof of the upward case (real axis only)
The upward case needs neither RH nor the spectral gap.
- On the real segment, `Φ_Λ = ξ'/ξ` holds as a meromorphic identity, and `ξ` has no zeros on `(½, 1)`.
- Hence `D_w(σ) = ξ'/ξ(σ) − Φ_lam(σ) ≤ ξ'/ξ(σ)` for `½ < σ ≤ 1`, using `Φ_lam(σ) ≥ 0` (Herglotz at interior real points).
- `ξ(½) ≠ 0` and `ξ'(½) = 0` give `ξ'/ξ(σ) → 0` as `σ → ½⁺`.
- Landau makes `D_w(σ) = Σ w(n) n^{−σ}` there, so `D_w(σ) ≥ D_w(1) > 0` unless `w = 0`. Contradiction.
- Inputs: Herglotz positivity on the real segment `(½, 1]`, and analyticity of `D_lam` near the real ray.

## Third proof of the upward case: Riemann's kernel is a null vector (cycle 143)
- Riemann's kernel `Φ(u) = Σ_n (2π²n⁴e^{9u/2} − 3πn²e^{5u/2}) e^{−πn²e^{2u}}` has transform `Ξ`, which vanishes at every zero of `ζ`. So `Φ` lies in the radical of the zero side `W(f, g) = Σ_ρ m_ρ f̂(γ) \overline{ĝ(\bar γ)}`, unconditionally.
- `Φ > 0`: `Φ(u) = Σ_n e^{u/2}(4π²Y² − 6πY)e^{−πY}` with `Y = n²e^{2u} ≥ 1` for `u ≥ 0`, and `4π²Y² − 6πY > 0` there; `Φ` is even.
- Let `lam ≥ Λ` be Weil-positive (all tests, pole weight 1) with `lam(n₀) > Λ(n₀)`. The explicit formula gives, for every test `f` and `k = f ⋆ f̃`,
  `Weil_lam(k) = W(f, f) − Σ_{n ≥ 2} (lam(n) − Λ(n)) n^{−½} (k(log n) + k(−log n))`.
- Take `f = Φχ_L`, `χ_L` a smooth cutoff equal to 1 on `[−L+1, L−1]`. Then `k ≥ 0`, so every atom term is `≥ 0`, and `k(log n₀) ≥ ∫_0^{log n₀} Φ(t)Φ(t − log n₀) dt =: c₀ > 0` once `L ≥ log n₀ + 1`. The zero side satisfies `|W(f, f)| ≤ e^{−e^{2L−2}} ∫|f|²` (near-radical estimate). For large `L` the functional is `≤ −δc₀/2 < 0`, a contradiction.
- No Landau step, Herglotz representation, or zero-sum constant is needed; the only analytic input is the explicit formula for `ζ` on `C²` compactly supported autocorrelations.
- **Scope.** `Φ` itself is not a polar test (`Ξ(±i/2) = ½ ≠ 0`). Cycle 144 repairs this with the polar second difference `Φχ_L − αΦχ_L(·−c) − αΦχ_L(·+c)`, `α = 1/(2cosh(c/2))`. Its negative lobes at `±c` cost `≤ 8CΣ(w(n)/n)e^{−|log n − c|}`, which is small for a suitable `c ∈ [M, 2M]` because the excess of a Weil-positive supersystem has log-density zero (L61). It does not extend downward: a contradiction there needs `k_f ≤ 0` at every atom where `lam < Λ`, and autocorrelations of radical vectors are positive-definite functions of width ≍ 1, wider than the gaps between the `log n`.

## Corollaries (cycle 140)
- **(E) Summable error.** The proof is unchanged if `lam − Λ = u₀ + e`, where `u₀` has constant sign and `Σ |e(n)| n^{−½} < ∞`.
  - `D_e` converges absolutely on `σ ≥ ½`, so Landau applies to `u₀`.
  - In Step 2 the boundary distribution of `D_e` is a continuous almost periodic function: it has no atoms, and its spectrum lies in `|x| ≥ log 2`.
  - Hence `lam = Λ` in both directions.
- **(D) Majorant form of Weil's criterion (unconditional).** Let `𝒞₊` be the cone of positive-definite polar tests `Φ` of compact support with `Φ(log n) ≥ 0` for all `n ≥ 2`. Then
  **RH ⟺ `W_Λ(Φ) = arch(Φ) − Σ Λ(n) n^{−½}(Φ(log n) + Φ(−log n)) ≥ 0` for every `Φ ∈ 𝒞₊`.**
  - ⇒ is Weil's criterion.
  - ⇐, step 1 (finite level). At each level `A`, LP duality with the Weil box is the argument of L79 (`exists_weilPositive_iff_primeBlindPositive`). It gives `w_A ≥ 0` on `n ≤ e^{2A}` such that `Λ + w_A` is Weil-positive up to level `A`. The obstruction to feasibility would be a `Φ ∈ 𝒞₊` with `W_Λ(Φ) < 0`.
  - ⇐, step 2 (limit). Box compactness (L68) gives `w ≥ 0` with `Λ + w ∈ W`.
  - ⇐, step 3 (conclusion). Theorem C(a) gives `w = 0` and RH. (For the polar-only cone, L61 (Lean) supplies pole weight 1 upward.)
- **Where (D) sits (audit).**
  - The ⇐ direction of (D) needs only the Landau step of Theorem C: a comparable Weil-positive system forces RH. The uniqueness `w = 0` is not needed.
  - So (D) is Landau's oscillation theorem in Weil-dual form, i.e. the majorant twin of the cycle-110/130 minorant wall, not a new mechanism.
  - The same duality gives a smaller RH-equivalent cone. If `Φ(u)e^{−u/2}` is nonincreasing on `[log 2, ∞)`, then the prime pairing is `∫ (ψ(x) − x) g_Φ(x) dx` with `g_Φ ≥ 0`. This is Landau's one-sided Chebyshev criterion.
  - The genuinely new content of this card is the **uniqueness**: the comparable part of `W` is the single point Λ. In L115's language, `𝒞₊` is the primal cone dual to the direction cone `{w ≥ 0}`.
- **Reading of (D).**
  - On `𝒞₊` the primes enter only through a nonnegative sum, so RH becomes an *upper* bound for prime sums.
  - Majorants give no freedom: if `lam⁺ ≥ Λ` is Weil-positive on `𝒞₊`, the same duality yields `v ≥ 0` with `lam⁺ + v ∈ W`, and Theorem C(a) forces `lam⁺ + v = Λ`.
  - So sieve majorants of Λ, which have density `≥ 2` by the parity phenomenon, cannot certify (D). This is the majorant twin of the cycle-110 minorant wall.

## Lean status (2026-09-29)
The RH-implication (Landau) halves of Theorem C(a) and (b) are formal, and so is the uniqueness `w = 0` of Theorem C(a), in the full cone (cycle 143) and in the polar cone (cycle 144). Downward uniqueness remains paper, blocked on a formal Herglotz representation.
- Module `RHTower/WeilFullConeRiemannKernelRigidity.lean` (414 lines), cycle 143:
  - `weilFullFunctional lam k`: pole term `k̂(i/2) + k̂(−i/2)`, prime atoms `lam(n) n^{−½}(k(log n) + k(−log n))` on `n ≥ 2`, archimedean term `(1/2π)∫ k̂ γ`. `WeilPositiveFull lam`: nonnegative real part on every autocorrelation `f ⋆ f̃` of a `C²` compactly supported `f`.
  - `zeta_W_eq_weilFullFunctional`: the zero side `W(f, f)` equals the full functional of Λ (Zeta23's explicit formula).
  - `riemannKernelReal_pos`, `riemannPhiKernel_eq_ofReal`: `Φ` is real and positive.
  - `exists_norm_W_truncatedRiemannKernel_le`: `W(Φχ_L, Φχ_L) → 0`.
  - `eq_vonMangoldt_of_weilPositiveFull_of_ge`: **Theorem C(a) uniqueness, unconditional**: a Weil-positive `lam ≥ Λ` equals Λ on `n ≥ 2`.
- Module `RHTower/WeilPositivityMajorantRigidity.lean` (1003 lines), cycle 144, in the corpus's polar cone `WeilPositive` (every level, tests with `f̂(±i/2) = 0`):
  - `eq_vonMangoldt_of_weilPositive_of_ge`: **Theorem C(a) uniqueness for polar tests, unconditional**: a Weil-positive `lam ≥ Λ` equals Λ on `n ≥ 2`. This is strictly stronger than the full-cone statement, and it supersedes L61's log-density bound.
  - Test: `polarRiemannDifference L c = u − αu(·−c) − αu(·+c)`, `u = Φχ_L`, `α = 1/(2cosh(c/2))`. Its transform `(1 − 2α cos cz)û` vanishes at `±i/2` and is `≤ 3|û|` on the strip.
  - `polarAutocorr_ge`: `k_f(y) ≥ k(y) − 2α(k(y+c) + k(y−c))`. `exists_truncatedRiemannAutocorr_le`: `k(v) ≤ Ce^{−2|v|}` uniformly in `L`.
  - `exists_excess_le_log`: from L61, `Σ_{n≤K}(lam − Λ)(n)/n = o(log K)`. `exists_mul_excessSmoothing_le`: averaging over `c ∈ [M, 2M]`.
  - `riemannHypothesis_iff_weilPositive_vonMangoldt`: Weil's criterion for the corpus's `WeilPositive`. The corpus had no link from `WeilPositive` to Mathlib's `RiemannHypothesis`. The proof goes through the Hodge-index exclusion `zeta_re_eq_half_of_hodgeIndex` and the zero-free box `|γ| < 4`.
  - `riemannHypothesis_iff_exists_weilPositive_ge`: **corollary (D) in Lean**: RH ⟺ some Weil-positive `lam ≥ Λ` exists, and then `lam = Λ`.
- Module `RHTower/ChebyshevDeficitPrimitiveOneSidedRH.lean` (712 lines). With `D(T) = ∫_0^T (e^t − ψ(e^t)) dt`:
  - `riemannHypothesis_of_logChebyshevDeficitPrimitive_ge`: if `−B e^{T/2} ≤ D(T)` for all `T ≥ 0`, then RH.
  - `riemannHypothesis_of_logChebyshevDeficitPrimitive_le`: the reverse one-sided bound also gives RH.
  - Mechanism: integration by parts gives the Laplace transform of `D`. The corpus's Landau theorem (`false_of_analyticAt_abscissa`) moves the abscissa of `(B ± e^{−T/2}D(T))dT + dT` to 0. The resulting transform continues the regularized critical-Mellin defect, and `riemannHypothesis_of_regularizedCriticalMellinDefect_extension` concludes.
- Module `RHTower/WeilParityPoleOneSidedRH.lean` (399 lines), in the CCM restricted Weil framework (full form, pole term included):
  - `riemannHypothesis_iff_evenParityPole_nonneg`: RH ⟺ the even literal pole `e^{x/2} + e^{−x/2}` has nonnegative Weil energy at every aperture.
  - `riemannHypothesis_iff_oddParityPole_nonneg`: the same for the odd pole. The corpus previously needed both parities.
  - `evenParityPole_atom_nonneg`: every visible prime atom has energy `2(2(e^a/n − e^{−a}) + (2a − log n)(1+1/n)) ≥ 0` on the even pole.
  - `riemannHypothesis_of_evenParityPole_supersystem`: weights `lam ≥ Λ` with nonnegative even-pole energy at every aperture force RH. Only even-pole positivity of `lam` is needed, which is weaker than Weil positivity.
  - `riemannHypothesis_iff_exists_evenParityPole_supersystem`: RH ⟺ such a majorant exists.
- Downward (cycle 142, same module):
  - `oddParityPole_atom_le`: every visible atom's odd-pole energy is at most `4e^a/n`.
  - `riemannHypothesis_of_oddParityPole_subsystem`: weights `0 ≤ lam ≤ Λ` with nonnegative odd-pole energy at every aperture force RH. No density hypothesis is needed, because the literal pole vectors carry the pole weight.
  - `riemannHypothesis_iff_exists_oddParityPole_subsystem`.
  - The one-sided criteria are generalized to `D(T) ≥ −B(1+T)e^{T/2}` and `≤ B(1+T)e^{T/2}` (`riemannHypothesis_of_logChebyshevDeficitPrimitive_ge_mul` / `_le_mul`).
- All theorems use only the axioms `propext, Classical.choice, Quot.sound`. They are wired into `RHTower.lean`, and the lint gate is clean for both modules.
- Literature note: the one-sided deficit criterion is Landau's oscillation theorem in integrated form (classical in substance). The single-parity statements and the supersystem theorem are specific to the Weil-cone setting.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper; inputs: MUST-520 Herglotz representation, Landau's theorem, `Σ_ρ 1/(ρ(1−ρ)) = 2 + γ − log 4π`)
- [ ] 2 → 3  formalized: partial. Both Landau steps, the single-parity criteria and upward uniqueness (full and polar cones) are formal; see the Lean status section. Downward uniqueness still needs a formal Herglotz representation of Weil positivity (positivity ⇒ analyticity with boundary measure).

## Log
- 2026-09-29 — cycle 139: conjectured, proved on paper, card created.
- 2026-09-29 — cycle 140: real-axis proof of the upward case; corollaries (E) summable error, (D) majorant form of Weil's criterion.
- 2026-09-29 — Lean: `ChebyshevDeficitPrimitiveOneSidedRH`, `WeilParityPoleOneSidedRH` (Landau step and single-parity criteria), axiom-clean.
- 2026-09-29 — Lean (cycle 142): downward Landau step `riemannHypothesis_of_oddParityPole_subsystem`; both directions of the RH-implication are now formal in the CCM full Weil form.
- 2026-09-29 — cycle 143: third proof of upward uniqueness (Riemann's kernel as a positive null vector), formalized in `WeilFullConeRiemannKernelRigidity` (axiom-clean).
- 2026-09-29 — cycle 144: upward uniqueness in the polar cone (`WeilPositivityMajorantRigidity`, axiom-clean).
