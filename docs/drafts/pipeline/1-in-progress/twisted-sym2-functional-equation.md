# Functional equation of the twisted symmetric square via Rankin–Selberg

- **ID:** SYM2-FE
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper, classical) → THEOREM (Lean)
- **Source:** selberg-quarter-conjecturing-loop.md cycles 71–75; shimura-sym2-holomorphy.md
- **Statement:** For u a Maass cusp form on Γ₀(N+1) and χ an even primitive character mod an odd prime q ∤ N+1,
  Λ(s, sym²u ⊗ χ) = L_∞(s) q^{3s/2} L(s, sym²u ⊗ χ) (up to fixed Euler factors at p | N+1) satisfies
  Λ(s, sym²u ⊗ χ) = ε(χ) Λ(1 − s, sym²ū ⊗ χ̄) with ε(χ) = ε₀ χ(N') τ(χ)³ q^{−3/2}.

## Goal
Every GL₂ family argument for Selberg's eigenvalue problem (Duke–Iwaniec (1.7), Iwaniec 10/49, Luo–Rudnick–Sarnak
nonvanishing) uses the forced zero L(2τ, sym²u⊗χ) = 0 (closed in Lean: `shimura_forced_zero_tw`) together with this
functional equation and its root number. Without the root-number phases only ν ≤ 3/10 follows (cycle 73a).

## Approach (weight-0 route, reusing the Γ(N) Eisenstein modules)
1. Scattering matrix of the Γ(N) Eisenstein series: continue φ_{∞σ}(s) = C(s) Σ_u L_u(2s) L(Φ_σ(u ·), 2s − 1)
   (`SelbergEisensteinCriticalLine.phiExt`) to all s via completed Dirichlet L-functions; prove Φ(s)Φ(1 − s) = I.
2. E(1 − s) = Φ(1 − s) E(s): the difference is cuspidal (constant terms cancel by step 1), a Δ-eigenfunction with
   eigenvalue s(1 − s), of moderate growth; for s(1 − s) ∉ ℝ it vanishes (Green's identity on Γ(N)\ℍ, corpus
   `SelbergMaassCoreGreen`); identity theorem.
3. Rankin–Selberg R(s) = ∫_{Γ(Nq²)\ℍ} u ū_χ E(z, s): unfolding at every cusp σ gives the constant term of
   (u ū_χ)|σ; summing with φ_{∞σ} recovers the dual series with Gauss sums.
4. Divide by the functional equation of L(s, χ) (mathlib `completedLFunction_one_sub`) to isolate sym²u ⊗ χ.

## Log
- 2026-09-26 — created. Plan above; step 1 first (pure Dirichlet-L algebra on existing `phiσ`).
- 2026-09-26 — **Root-number source closed in Lean** (`HalfWeightTwistedThetaInversion`, built `--old`, wired, standard axioms):
  - `thetaChar_inversion`: Σψ(n)e(n²z) = τ(ψ)(−2iq²z)^{−1/2}Σψ̄(n)e(−n²/(4q²z)) for ψ ≠ 1 mod a prime q;
  - `thetaTw_eq_char_sq`: θ_χ = τ(χ̄)Σχ²(n)e(n²z);
  - `thetaTw_inversion`: τ(χ)θ_χ(z) = τ(χ̄)τ(χ²)(−2iq²z)^{−1/2}θ_χ̄(−1/(4q²z));
  - `thetaPeriodic_inversion`: every q-periodic weight c(n), dual ĉ(n) = Σ_r c(r)e(rn/q).
- 2026-09-26 — **Cusp structure of the dual (paper).**
  - At the Fricke cusp 0 of Γ₀(4q²) with f of level one, G_χ|W = c·f(q²z)·conj θ_χ̄(z)·y^{1/4}. Its constant term vanishes: the frequencies q²m of f(q²·) meet only n ≡ 0 (q), where χ̄²(n) = 0.
  - So the dual of the Shimura integral lives at the q−1 cusps b/q (singular for ψ = χ², which has conductor q, at level 4q²). There the theta weight is ψ(n)e(bn²/q), with dual weight Σ_r ψ(r)e((br²+rn)/q).
  - For f of level M > 1, f(4z) at b/q sits at the cusp 0 of Γ₀(M). The dual therefore involves f|W_M, another cusp form with the same eigenvalue, so newform theory is not needed.
- **Revised step order (weight ½, matches the forced zero `shimura_forced_zero_tw`):**
  - (i) expansion of G_χ at every cusp b/q;
  - (ii) weight-½ Eisenstein series E_{b/q}(z,w;ψ) with its Fourier expansion at ∞ and its modularity, following the pattern of `EstarTw`;
  - (iii) scattering identity E_∞(1−w) = Σ_b Φ_b(w)E_{b/q}(w), plus the cusps over 2 and M. Proved coefficient by coefficient via the functional equations of L(s, χ_nψ), or by Green uniqueness;
  - (iv) unfold at each b/q and sum over b; the Gauss sums combine to τ(ψ)³.
- 2026-09-26 — **Dual series closed in Lean** (`HalfWeightDualEisenstein`, built `--old`, wired, standard axioms).
  - `eisK`: the row-weighted Poincaré series Σ_{⟨T⟩\Γ₀(4M)} κ(c)·conj(j)·Im^w;
  - `eisK_smul`: automorphy whenever κ(c_γ) = μ·κ(c_{γδ});
  - `eisK_eq_coeffs`: the Fourier coefficients D^κ_n = Σ κ(c)c^{−2w}klH₁(n,c);
  - `eisDual` = eisK with κ(c) = ψ₀(c/q) at level 4M'q (`kapQ`), and `eisDual_smul`: Ê(δz) = ψ₀(d)j(δ,z)Ê(z) on Γ₀(4M'q²), the same law as E*_ψ.
- **Paper facts found while building it.**
  - (a) D̂_n(w) = i^{1/2}/√2 · q^{1/2−2w} μN_q(n) · L(Btw ψ₀⁻¹, 2w−½), where μN_q(n) = N_q(n) − 1 (Legendre symbol). This mirrors D*_n with ψ₀ ↦ ψ₀⁻¹ and the q-part Qf/τ replaced by q^{1/2−2w}μN_q(n) (scratch DC1, compiles).
  - (b) D̂_0 = 0 since μN_q(0) = 0, so Ê has no constant term at ∞. The y^{1−w} term of E*_ψ(1−w) must therefore come from the 2-adic partner Ê₀ (the Eisenstein series at the 2-adic cusp 0 with q-adic middle cusp). **The FE needs Ê₀'s Fourier coefficients at ∞**: odd-c theta-multiplier Kloosterman sums.
  - (c) Coefficientwise, the FE of E*_ψ implies Gauss's sign τ(χ_D) = i^{a}√|D| for all fundamental D. So either prove the Gauss sign (not in mathlib) or prove the Eisenstein FE by a sign-free method (Maass–Selberg uniqueness, or theta).
  - (d) In the Shimura pairing, ⟨G, E₀⟩ = r(w)⟨G, E_∞⟩ explicitly, because G|W₄ ∝ f(z)·conj θ_χ(z)·y^{1/4} (f(4W₄z) = f(γz) with γ ∈ Γ₀(M)). The 2-adic partner changes only the Euler factor at 2.
- 2026-09-26 — **Correction: Ê is not the FE partner of E*_ψ (support mismatch).**
  - For q ∤ n and α ≥ 2, Hensel lifting makes sqCount(n + bq^{α−1}, q^α) = N_q(n) independent of b. So A_α(n) = N_q(n)Σ_bψ₀(b) = 0: **E*_ψ has Fourier coefficients only at n ≡ 0 (q)**.
  - Ê has coefficients ∝ μN_q(n) = (n/q), so it **lives on q ∤ n**.
  - Cause: at weight ½ the multiplier's q-part is the quadratic Gauss sum G(−dc₁; q) = (−dc₁/q)ε_q√q. The effective q-local weight of Ê is therefore (ψ₀η)(c/q)·η(−d), where η is the Legendre symbol.
  - The partner must have effective q-local d-weight trivial, i.e. d-character η in `eTerm`, together with c-weight (ηψ₀)(c/q). This gives the Ramanujan sum c_q(n) = q[q|n] − 1, which still needs a q ∤ c complement for the −1, as in weight 0 where the Epstein dual Σψ(m)|mqz+n|^{−2s} splits into rows q‖c plus q^{−2s}·(rows q∤c).
  - The row-weighted machinery `eisK` generalises directly to a d-character (replace `eTerm M 1` by `eTerm M ψ'`).
  - The existing modules remain correct statements about Ê (another element of the ψ-Eisenstein space), but they are not yet the partner.
- **Route decision.** Weight ½ at q and at 2 needs η-twisted partners, the 2-adic partner, the Gauss sign, and local FEs. Weight 0 gets the Eisenstein FE for characters from the Epstein/Poisson method with only τ(ψ) (no quadratic Gauss sums): Θ(z,t) = Σψ(n)e^{−πt|mLz+n|²/y}, with Θ(t) = τ(ψ)/(qLt)·Θ̂(1/(L²t)), gives a mathlib `StrongFEPair` (template: corpus `GL3EpsteinContinuation`). Next brick: the weight-0 Epstein-with-character FE module. The weight-0 route then needs RS unfolding of u·ū_χ and a Hecke layer to divide out L(s,χ).
