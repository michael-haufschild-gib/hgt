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

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper; inputs: MUST-520 Herglotz representation, Landau's theorem, `Σ_ρ 1/(ρ(1−ρ)) = 2 + γ − log 4π`)
- [ ] 2 → 3  formalized: blocked on a formal Herglotz representation of `WeilPositive` (positivity ⇒ analyticity). The existing formal tools (Toeplitz ceiling with crude constant; Mertens-constant tests) reach only the summable and exact-expansion cases.

## Log
- 2026-09-29 — cycle 139: conjectured, proved on paper, card created.
- 2026-09-29 — cycle 140: real-axis proof of the upward case; corollaries (E) summable error, (D) majorant form of Weil's criterion.
