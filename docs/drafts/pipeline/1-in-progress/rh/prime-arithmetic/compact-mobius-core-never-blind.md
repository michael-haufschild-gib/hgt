# Compact Möbius cores are never blind (no compactly supported (N1') witness)

- **ID:** compact-core-blind-nogo
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) for (A1), (A2); CONJECTURE for the full statement (see Correction)
- **Source:** producer-loop-opus-2026-10-12 rows 183–185; HF route (N1) = `XiDivisibleBlindTest`
- **Statement (proved, A2):** if a compactly supported core `f` with `B̂ = O(ξ^{−5/2−ε})` has `Ψ_f(n) = 0`
  for all `n ≥ 2`, then `∫_T^∞ B̂ ≤ C e^{−a√T}`. So a blind compact core is Gevrey-2 smooth.
- **Statement (proved, A1):** a piecewise `C^∞` compact core with a jump discontinuity, or with any finite-order break,
  is never blind.
- **Open:** compact cores of Gevrey class `1 < s < 2`.

## Goal
The ansatz `F̂ = ζ·𝓜f` (`F(x) = e^{x/2} Σ_m f(m e^x)`) produces Ξ-divisible tests whose blindness at
`log ℕ_{≥2}` is the ζ-free condition `Ψ_f(n) = 0, n ≥ 2` (`logNode_blind_iff_cosDilationKernel_vanishes`).
The theorem kills every compactly supported Möbius core, for every support ratio. Lean already has the
special case `β ≤ 2α` (`RHTower/CosDilationShortSupportRigidity`). Positive survivor: an (N1) witness core
`f` must have `A_f(r) ≠ 0` for arbitrarily small `r`. Equivalently, its support ratio is infinite, and the balance
happens between the centre `r = 1` and the window at `r ≈ 0` (the tail of `B` paired with slow chirps).

## Notation
`g(u) = e^{u/2} f(e^u) ∈ C_c^∞`, `B = g ⋆ g̃` (even, PD, `B̂ = |ĝ|² ≥ 0`, `supp B ⊆ [−log R, log R]`,
`R = β/α`), `A(r) = A_f(r) = r^{−1/2} B(log r)`, `A_e(r) = A(|r|)`. By `tsum_dilationAutocorr_abs_eq`:
`P(x) := Σ_k A_e(x+k) = a + b cos 2πx` with `a = Ψ(0)`, `b = 2Ψ(1)`.

## Proof architecture
1. **Pairing identity.** For a window `φ` with `φ(r) = O(r^{−2})`, unfolding `∫_0^1 P Θ`,
   `Θ = Σ_j φ(·+j)`, gives `Σ_j ∫ A_e φ(·+j) = a ∫φ + b ∫ φ(r) cos 2πr dr`.
2. **Windows.** `h = c τ^{−1/2}`, `Φ_τ(u) = e^{−u²/2h²} cos τu` (positive type,
   `Φ̂_τ = (h√(2π)/2)(e^{−h²(ξ−τ)²/2} + e^{−h²(ξ+τ)²/2}) > 0`), `μ(τ) = ∫ B Φ_τ = (2π)^{−1}∫ B̂ Φ̂_τ > 0`.
   r-window `φ_τ(r) = r^{−1/2} Φ_τ(log r)` (`r > 0`), test `φ = φ_τ + φ_τ(−·)`.
3. **Bookkeeping.** The identity becomes `2 Σ_{k∈ℤ} (F_k + B_k) = E(τ)`, with
   `F_k = ∫_0^∞ A(r) φ_τ(r−k+1) dr` (forward window at `r ≈ k`) and `B_k = ∫_0^∞ A(r) φ_τ(k+1−r) dr`
   (backward window at `r ≈ k`).
4. **Centre.** `F_1 = ∫ B Φ_τ = μ(τ)` exactly. `B_1 = ∫ B(u) e^{(u+ψ)/2} Φ_τ(ψ(u)) du`, where
   `ψ(u) = −log(2−e^u) = u + u² + O(u³)` (the parabolic map `r ↦ 1/(2−r)`). Its even part is
   `Φ_τ(u) cos(τu²) + O(h)`. `Φ_τ·(1 − cos τu²)` is a difference of complex Gaussians with
   `α = (1 − 2ic²)/(2h²)` (since `τh² = c²`), and its Fourier transform is `O(c²)` times a Gaussian of variance
   `(1+O(c⁴))/h²` (**W1**). So `B_1 ≥ μ(τ) − C c² μ̃(τ) − C h μ̃(τ) − C e^{−κτ}`, where `μ̃` uses widened Gaussians.
5. **Integers `k ≥ 2`.** Near `u = log k`, `F_k, B_k` pair `B` with `k^{1/2} Φ_τ(k v + O(k² v²))`. Up to an
   `O(c²)` chirp, this is a cross-correlation of two complex Gaussian packets at `log k` and `0`. Cauchy–Schwarz
   for the PSD form `(χ₁,χ₂) ↦ ∫∫ B(u−v) χ₁(u) χ̄₂(v)` gives
   `|F_k|, |B_k| ≤ C √k μ̃(kτ)` (**W2**; note `|Q(χ₁,χ₂)|² ≤ Q(χ₁,χ₁) Q(χ₂,χ₂)` is exact).
   Windows at `k ≤ 0` and `k > R+1` only see Gaussian tails: `≤ C e^{−κτ}`.
6. **Errors.** `∫φ_τ = Re ∫ e^{−u²/2h²+iτu+u/2} du = O(e^{−c²τ/2})`. `∫ φ_τ(r) cos 2πr dr` has no stationary point
   near `u = 0`; a local contour shift by `y = c²` gives `O(e^{−c²τ/2})` (**W3**). So `|E(τ)| ≤ C e^{−κτ}`.
7. **Maximiser.** Weight `W_T(τ) = τ^N e^{−T/τ}`. `μ W_T → 0` because `B̂` decays faster than any power, so a
   maximiser `τ*` exists. Either `μ(T)` is already `≤ e^{−κT}`, or `τ* ≥ T/K`. In that case `μ(τ*+y) ≤ (1+o(1)) μ(τ*)`
   for `|y| ≲ τ*^{1/2}`, and `μ(kτ*) ≤ k^{−N}(1+o(1)) μ(τ*)`. Steps 3–6 give
   `2μ(τ*)[2 − C c² − 2(ζ(N−½)−1)(1+o(1))] ≤ C e^{−κτ*}`. With `c` small and `N ≥ 4`: `μ(T) ≤ C e^{−κ' T}`.
8. **Contradiction.** Exponential decay of the windowed masses gives `∫ B̂(ξ) e^{κ''|ξ|} dξ < ∞`. Then `B` is real-analytic,
   and it is compactly supported, so `B ≡ 0`, hence `g ≡ 0` and `f ≡ 0`.

Only `B̂ = O(ξ^{−N−1})` with `ζ(N−½) − 1` small is used, so `f ∈ C_c^4` already suffices.

## Finite-order variant (paper, independent proof)
Let `f` be piecewise `C^∞` with finitely many breaks, and let `j` be the minimal order of a derivative jump
(jumps `D_i` of `g^{(j)}` at `u_i = log y_i`). Then the jump of `P^{(2j+1)}` at `0` equals
`2(−1)^{j+1}[Σ D_i² + Σ_{k≥2} k^{−2j−3/2} Σ_{y_i = k y_l} D_i D_l]`. The form is `⟨D, μ⋆D⟩` on `ℓ²(ℚ_{>0})`, with
`μ̂(χ) = Re L(2j+3/2, χ)`. `|arg L(σ, χ)| ≤ Σ_p arcsin p^{−σ} < π/2` for `σ ≥ 3/2`, so the form is
positive definite. Hence no witness core has a finite-order break.

## Correction (same day): Gevrey-2 is where the method stops
Steps 4 and 7 above are too optimistic. The backward window at `r = 1` is a chirped Gaussian, so its error kernel is
widened by `√(1+4c⁴)`. Comparing it with `μ(τ)` needs control of `B̂` *below* `τ` on the scale `√τ/c`. The
maximiser only controls frequencies above `τ`. The rigorous replacement is the **integrated identity**: integrate the
per-`τ` identity against `ρ_T(τ) = τ^s e^{−a(T−τ)_+/√T}`. A Gaussian of width `√τ/c` smooths a weight whose
log-derivative is `≤ a/√T` to within a constant factor. The `k ≥ 2` kernels satisfy
`ρ_T(ξ/k) ≤ k^{−s} ρ_T(ξ)`. The centre gives `(2 − O(c²))`, the integers `k ≥ 2` give at most `2wΣ_k k^{−1/2−s}`
(`< 1` for `s ≥ 3/2`), and the errors `E(τ) = O(1)` for small `τ` are weighted by `e^{−a√T}`. Result:
`T^s ∫_T^∞ B̂ ≤ C e^{−a√T}` (**A2**).
Why the bound sits at `e^{−√ξ}`: if `B` is Gevrey-`s`, its singular region at frequency `τ` has width
`τ^{−(s−1)/s}`, and the parabolic chirp over that region is `τ^{(2−s)/s}`. For `s > 2` the two branches `A(1±x)`
stay correlated, the centre `≈ 2μ > 0` dominates, and there is no witness. For `s < 2` they decorrelate.
Exact anti-invariance under the parabolic map `ψ` (Fatou coordinate `z = 1/(r−1)`, `ψ: z ↦ z−1`) gives singular parts
`e^{−c/|r−1|} sin(π/(r−1))`, which are Gevrey-2 with `B̂ ≍ e^{−2√(cξ)}`, exactly the boundary of (A2).

**Conjecture C186 (quantum-modular witnesses):** a blind compact core exists iff there is a positive-definite
`B` whose singular parts at every Farey point are Gevrey-2 and anti-invariant under the parabolic stabilisers of
`PGL₂(ℤ)` (period-function / quantum-modular structure at `s = ½`, cf. the Voronoi–Lewis–Zagier lane).

## Log
- 2026-10-13 — created (row 185). Lean special case `β ≤ 2α`: `eq_zero_of_cosDilationKernel_blind_of_le_two_mul`.
- 2026-10-13 — [L] finite-order variant, j = 1 (derivative jumps), ALL support ratios:
  `RHTower/PiecewiseLinearCoreBlindnessRigidity.plCore_coeff_eq_zero_of_cosDilationKernel_blind`
  (f = Σ e_j (x − y_j)_+, Σe = Σey = 0, y distinct positive; Ψ_f(n) = 0 ∀ n ≥ 2 ⇒ e ≡ 0).
  Ingredients: closed form `dilationAutocorr_plCore` (A_f(r) = (r/12)Σ e_j e_l |y_j − y_l/r|³), corner
  decomposition 12P = H + |x|³W near 0 (`eventually_plTerm`), identity theorem for analytic functions,
  `plCornerForm_ge` (Σ_{k≥2} k^{−3}-type Schur bound, ≥ Σ e_j² y_j³ /(K+1)). Standard axioms, audited, wired.
- 2026-10-13 — [L] j = 0 (jump discontinuities), support ratio < 11:
  `RHTower/StepCoreBlindnessRigidity.stepCore_coeff_eq_zero_of_cosDilationKernel_blind`, via the bounded Poisson
  periodization `RHTower/DilationAutocorrelationPeriodizationBounded`. All ratios need the character bound
  Re L(3/2, χ) > 0 (Fourier on finite-rank tori); open in Lean.
