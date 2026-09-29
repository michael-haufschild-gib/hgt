# Λ is an extreme point of the Weil cone (Hamburger rigidity of two-sided perturbations)

- **ID:** weil-lambda-extreme-point
- **Stage:** 2-fully-proven (paper, 2026-09-29)
- **Type:** THEOREM (paper)
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, L140 (settles L129)
- **Statement:** Let `w: ℕ_{≥2} → ℝ` with `Σ|w(n)|n^{−σ} < ∞` for `σ > 1`. If `Λ + w` and `Λ − w` are both Weil-positive for ζ's archimedean datum, then `w = 0`. Equivalently, if RH holds, Λ is an extreme point of the (convex, closed) Weil cone `W`.

## Goal
- **Uniqueness side of the Minkowski split, two-sided form.** No symmetric deformation of Λ preserves Weil positivity, for arbitrary infinite-type `w`. It includes the pure-atomic "second crystalline structure" of L105/L129, which is therefore excluded.
- **Non-circularity.** RH is implied by the hypothesis (convexity); nothing about zeros is assumed.

## Proof (paper)
1. `Λ = ½((Λ+w) + (Λ−w)) ∈ W`, so RH holds and `μ_Λ/2 = πΣ m_ρδ_γ`. `D_w` is holomorphic on `σ > ½`, as a difference of Herglotz functions (companion card `weil-cone-finite-type-uniqueness`, input (B)).
2. `μ_{Λ±w}/2 = μ_Λ/2 ∓ Re D_w ≥ 0` for both signs. So `Re D_w` has purely atomic boundary measure on the critical ordinates, with atoms `πr_ρ`, `|r_ρ| ≤ m_ρ`. By (B) the poles are simple with real residues.
3. `S = Σ r_ρ[1/(s−ρ) + 1/ρ]` converges. `E = D_w − S` has constant boundary real part, so by Schwarz reflection `E` is entire. Real coefficients pair `r_ρ = r_ρ̄`, giving `D_w(s) + D_w(1−s) = κ`.
4. `F = ζ(D_w − κ/2)` is a Dirichlet series, absolutely convergent on `σ > 1`. `(s−1)F` is entire of finite order: the poles of `D_w` sit on zeros of ζ of multiplicity at least `|r_ρ|`. It satisfies `Γ_ℝ(s)F(s) = Γ_ℝ(1−s)(−F)(1−s)`.
5. By Hamburger's theorem (Hamburger 1921; see Titchmarsh §2.13), `F = −F = cζ`. So `F = 0`, `D_w = κ/2`, `w(1) = 0` gives `κ = 0`, hence `w = 0`. ∎

## Cited inputs
- Hamburger's theorem.
- Bochner–Schwartz / Paley–Wiener–Schwartz (Herglotz dictionary and polynomial growth near the line).
- Schwarz reflection for distributional boundary values.
- Mittag-Leffler convergence: `Σ|r_ρ|/|ρ|² < ∞` since `|r_ρ| ≤ m_ρ`.

## Gates
- [x] 0 → 1, 1 → 2: proof above.
- [ ] 2 → 3: Lean. Needs Hamburger's theorem (not in mathlib or the corpus) and the boundary-value dictionary.

## Log
- 2026-09-29 — created from L140. Corrects L139's "multiplicative FE" (the relation is linear, `D_w(s) + D_w(1−s) = κ`).

## Lean (2026-09-29)
- Step 5 (Hamburger) is formal:
  - `HTGeometry.coeff_eq_of_completed_functional_equation`;
  - `HTGeometry.coeff_eq_zero_of_odd_completed_functional_equation`. This is exactly the sign `−1` case used here: `Γ_ℝ(s)F(s) = −Γ_ℝ(1−s)F(1−s)` ⇒ `F = 0`.
- Hypothesis form: `F`'s completed function minus `αΓ_ℝ(s) + βΓ_ℝ(s−1)` is holomorphic and `O(1/(1+t²))` on `−½ ≤ Re s ≤ 3/2`.
- Steps 1–4 (the Weil-cone ⇒ FE wiring) remain paper-only. They need the Herglotz boundary-value dictionary and Schwarz reflection, neither of which is in mathlib.
- **2026-09-29 (later): reflection-free Lean route.** Step 5 is now available in the form L140 actually produces, with data on `Re s ≥ ½` only. Module `HTGeometry/HamburgerCriticalLine`, standard axioms.
  - `coeff_eq_zero_of_critical_line_odd`. Let `f = Σaₙn^{−s}`, and let `E := Γ_ℝ f − βΓ_ℝ(s−1)` be continuous on `½ ≤ Re s ≤ 3/2`, holomorphic inside and `O(1/(1+t²))`. If `E(s) + E(1−s) = −β(Γ_ℝ(s−1) + Γ_ℝ(−s))` on `Re s = ½` (oddness across the line as a *boundary condition*), then `f = 0`.
  - Supporting results:
    - `critical_line_odd_theta_relation`: the theta relation from the right half-plane alone;
    - `coeff_eq_zero_of_odd_coeffTheta_relation` / `coeff_eq_of_coeffTheta_relation`: Hamburger's conclusion from a theta relation;
    - a contour shift onto a boundary line (continuity only).
  - This removes steps 3–4's Schwarz reflection and the left-half-plane continuation from the Lean path.
- **Exact remaining Lean gap for L140.** The boundary-regularity lemma for two-sided perturbations: if Λ ± w are both in W (Herglotz form), then `Z·D_w` (`Z = Γ_ℝζ`) is continuous up to the critical line, has polynomial growth in `½ ≤ Re s ≤ 3/2`, and `Re D_w⁺` vanishes off the zeros.
  - Then `Z(½+it)(D_w(½+it) + D_w(½−it)) = 2Z·Re D_w⁺ = 0`, which is exactly the hypothesis `hC` (with `β = 0` after subtracting the pole).
  - The inputs are the Herglotz representation (corpus: `HerglotzRepresentationDisc`, `SuzukiHalfPlaneHerglotz`) and the atomic Herglotz measure of `ξ'/ξ` under RH (Hadamard product).
  - RH itself follows from `Λ ∈ W` via the corpus's `riemannHypothesis_iff_analyticAt_logDeriv`.
- **2026-09-29: L140 Lean programme, brick 1 done.** `HTGeometry/PoissonMeasureUniqueness`, standard axioms, wired.
  - `map_mk_eq_of_poissonIntegral_eq`: a finite measure on angles is determined, on `ℝ/2πℤ`, by its disc Poisson integral. Proof: moments via mathlib's Poisson formula applied to `Re zᵏ`, `Im zᵏ`, plus Fourier uniqueness.
  - `map_mk_le_of_poissonIntegral_le`: `P[μ] ≤ P[ν]` with harmonic difference ⇒ `μ ≤ ν`.
  - **Remaining bricks**, in order:
    - (2) the atomic Poisson measure of `Re ξ'/ξ` under RH, transported by the Cayley map `z = (s−3/2)/(s+½)`, from the Hadamard real-part expansion;
    - (3) the sandwich `0 ≤ Re(Ψ ± D_w) ≤ 2Re Ψ` ⇒ atomic measures ⇒ `D_w = Σ r_ρ(pair kernels) + const` (Herglotz reconstruction: equal real parts ⇒ imaginary constant);
    - (4) continuity of `Z·D_w` up to the line, the odd boundary identity and the decay bound;
    - (5) the Weil-cone definition, `Λ ∈ W ⇒ RH` (corpus), and assembly with `coeff_eq_zero_of_critical_line_odd`.
