# Parity selection of the restricted Weil ground state fails under an isolated off-line quartet

- **ID:** ccm-parity-selection-fails-off-line-quartet
- **Stage:** 3-formalized (Lean, standard axioms; STATUS MUST-805)
- **Type:** THEOREM (no-go for a core mechanism of route RW / Connes' "remaining step 1")
- **Source:** geometric loop G67 (`rh-geometric-topological-loop-2026-10-06.md`); goal-loop rows 506, 507, 514;
  frontier map RW line "Open: ground simplicity/parity selection"; Connes, arXiv 2602.04022 §6.6
  ("In order to apply Theorem 6.1 one needs to show that the smallest eigenvalue of the Weil quadratic form
  QW_λ is simple with even eigenvector"); Connes–van Suijlekom, CMP 406 (2026) 312, Thm 6.1.

## Statement

Let `z_q` be the spectral points of the Xi zero copies (`XiC(z) = ξ(½+iz)`, multiplicities retained),
`Q_a` the CCM restricted Weil source quadratic at aperture `a`, `J` the physical embedding into
`L²(−a,a)`, `μ(a)` the ground energy.

**Theorem.** Suppose the non-real spectral points form a finite multiset, and there is
`σ = t + iδ` (`t > 0`, `δ > 0`) which is a spectral point such that every non-real spectral point is
in the quartet `{σ, σ̄, −σ, −σ̄}` or has `|Im z| < δ`. Then for every `A` there is an aperture
`a > A` at which every ground state of `Q_a` is odd. Equivalently: if Connes' step 1 (an even ground state)
holds at all large apertures, then RH holds, or there are infinitely many off-line zeros, or the maximal
real part of the off-line zeros is attained by at least two zeros in the upper half-plane.

Explicit apertures: `a_k = (π/2 − β + 2πk)/(2t)`, `β = arctan(δ/t)`, all large `k`.

## Proof

Notation: for `u ∈ L²(−a,a)`, `û(w) = ∫ u(x) e^{iwx} dx`. Zero sum (corpus, smooth interior sources):
`Q_a(u) = Re Σ_q û(−z_q) · conj û(−z̄_q)`, absolutely convergent.

1. **Splitting.** For a real `z_q` the term is `|û(−z_q)|² ≥ 0`. For a lower off-line point `w`
   (`0 < |Im w| < δ`), Cauchy–Schwarz gives `|û(w)| ≤ ‖u‖ N(w)` with `N(w)² = ∫_{−a}^{a} e^{−2 Im(w)x} dx
   = sinh(2a|Im w|)/|Im w|`. So the term is bounded by `‖u‖² sinh(2a|Im w|)/|Im w|`. Let `L(a)` be the
   sum of these coefficients over the finite lower multiset.
2. **Top quartet on a parity sector.** For `u` even or odd, `û(−w) = ±û(w)`, so the real part of the
   term is the same at all four quartet points: `Re(p q̄)` with `p = û(σ)`, `q = û(σ̄)`. With `M` the
   number of copies on the quartet (`M ≥ 1`), the top contribution is `M Re(p q̄)`.
3. **Even lower bound.** `4 Re(p q̄) = |p+q|² − |p−q|² ≥ −|p−q|²`. For even `u`,
   `p − q = ∫ u (cos σx − cos σ̄x) dx = ∫ u(x)(−2i sin(tx) sinh(δx)) dx`. So
   `|p−q|² ≤ ‖u‖² D⁺` with `D⁺ = ∫_{−a}^{a} 4 sin²(tx) sinh²(δx) dx`. Hence for every even smooth `u`:
   `Q_a(u) ≥ −((M/4) D⁺ + L) ‖u‖²`. This extends to every even form-domain vector by density of smooth
   sources and continuity of `Q_a` and `J`.
4. **Odd test.** Let `g(x) = 2 cos(tx) sinh(δx)` on `[−a,a]`. Then `g` is real and odd, so
   `conj ĝ(σ̄) = ĝ(−σ) = −ĝ(σ)`, and `ĝ(σ) = i ∫ g sin(σx) = −D⁻/2 + i I₁`, where
   `D⁻ = ‖g‖² = ∫ 4cos²(tx) sinh²(δx)` and `I₁ = ∫_0^a sin(2tx) sinh(2δx) dx`.
   The top contribution is `−(M/4)(D⁻² − 4I₁²)`.
   On-line part: write `g` as a combination of four exponentials. For real `w`,
   `|ĝ(w)|² ≤ 8 cosh²(δa)[1/(δ²+(w+t)²) + 1/(δ²+(w−t)²)] ≤ 16 cosh²(δa)|σ|²/(δ² w²)`, using
   `min_w (δ²+(w−t)²)/w² = δ²/|σ|²`. Hence `P(g) ≤ 16 cosh²(δa)(|σ|²/δ²) S` with `S = Σ_q |z_q|^{−2} < 33/100`.
   So the formal zero sum `Q̃(g)` satisfies `Q̃(g)/‖g‖² ≤ −(M/4)D⁻ + M I₁²/D⁻ + L + P(g)/D⁻`.
5. **Smoothing.** Let `v_n = (g·1_{[−b_n,b_n]}) ∗ ρ_n`, with `b_n ↑ a` and `ρ_n` an even mollifier of
   width `< a − b_n`. Then `v_n` is a smooth odd interior source, and `v̂_n = Ĝ_{b_n} ρ̂_n`. The bounds
   `|Ĝ_b(w)| ≤ K/(1+|w|)` (uniform in `b ≤ a`) and `|ρ̂_n| ≤ e^{1/2}` hold on `|Im w| ≤ ½`. Dominated
   convergence over the zero copies gives `Q_a(v_n) → Q̃(g)` and `‖v_n‖ → ‖g‖`.
6. **Asymptotics at `a_k`.** There `sin(2ta) = t/|σ|` and `cos(2ta) = δ/|σ|`, which gives
   - `D⁻ − D⁺ = ∫ 4cos(2tx) sinh²(δx) = 2J − 2 sin(2ta)/t`, with
     `J = ∫_{−a}^{a} cos(2tx) cosh(2δx) = (δ² sinh 2δa + t² cosh 2δa)/|σ|³ ≥ sinh(2δa)/|σ|`;
   - therefore `D⁻ − D⁺ ≥ 2(sinh(2δa) − 1)/|σ|`;
   - `I₁ = tδ e^{−2δa}/(2|σ|³)`;
   - `D⁻ ≥ sinh(2δa)/δ − 2a`.

   Hence `(M/4)(D⁻ − D⁺) − M I₁²/D⁻ − 2L − P(g)/D⁻ → +∞`, because `L = o(e^{2δa})` and `P/D⁻ = O(1)`.
   For large `k`, some smooth odd `v` has `Q_a(v) < c_e ‖Jv‖²`, where `c_e = −(M/4)D⁺ − L` is the even
   floor.
7. **Ground states are odd.** Let `u` be a ground state. The corpus gives that both parity parts of a
   ground state are ground states (`ccmRestrictedWeil_ground_evenOdd_components`). If `u_e ≠ 0`, then
   `c_e‖Ju_e‖² ≤ Q(u_e) = μ‖Ju_e‖² ≤ (Q(v)/‖Jv‖²)‖Ju_e‖² < c_e‖Ju_e‖²`, a contradiction. So `u_e = 0`.

## What the theorem says

- Connes' step 1 is not a technical input. Any proof of even ground parity for all large `λ` excludes
  the simplest ¬RH configuration: one off-line quartet on top of finitely many shallower ones.
- Fingerprint: under such a configuration, the parity gap `μᵉ − μᵒ` oscillates with phase `2ta`. The
  sign alternation recurs with period `π/t` in the aperture, where `t` is the ordinate of the top zero,
  and the amplitude is of order `e^{2δa}/|σ|`. This matches goal-loop row 506's planted numerics
  (half-period `π/(2γ₁)`).
- Not covered: infinitely many off-line zeros, or a non-unique top (the multi-top model is a coupled
  `2m×2m` problem with an almost-periodic gap).

## Lean

Modules (namespace `RHTower.CCMParityQuartet`, wired into `GaloisForLFunctions.RHTower`;
`#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`):

| Module | Content |
|---|---|
| `RHTower/CCMParityQuartetModel` | closed forms for `D⁺`, `D⁻`, `I`; phase apertures; `exists_phaseAperture_gap` |
| `RHTower/CCMParityQuartetZeroSum` | `sourceQuadratic_eq_re_tsum`, `summable_zeroSumTerm`, `re_zeroSumTerm_quartet`, `norm_integral_mul_sq_le` |
| `RHTower/CCMParityQuartetEvenFloor` | `IsolatedTopQuartet`, `sourceQuadratic_ge_of_smooth_even`, `evenPart_toCCMFormVector`, `sourceQuadratic_ge_of_isEven` |
| `RHTower/CCMParityQuartetOddTest` | smooth cutoffs, `oddTestSource`, `sourceQuadratic_le_offLine_add`, `testTransform_gTrunc_top`, convergence of `v_n` |
| `RHTower/CCMParitySelectionNoGo` | `exists_aperture_ground_odd`, `not_isolatedTopQuartet_of_eventually_even_ground` |

Corpus inputs used: `ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm`,
`suzukiScrewSmoothForm_eq_tsum`, `testTransform_ibp`, `denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector`,
`continuous_ccmRestrictedWeilSourceQuadratic`, `ccmRestrictedWeil_ground_evenOdd_components`,
`ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source`, `ccmArchimedeanFormToAperture_injective`,
`xiSpectralPoint_inv_sq_summable`.

## Gates
- [x] 0 → 1 in-progress
- [x] 1 → 2 fully proven (paper proof above)
- [x] 2 → 3 formalized (2026-10-07)
- [ ] 3 → 4 publication-ready

## Log
- 2026-10-07 — created from G67 with a complete paper proof.
- 2026-10-07 — formalized in five modules (MUST-805). The smoothing uses interval-integral cutoffs
  `χ(x) = ∫_{x−b}^{x+b} ρ` instead of convolution. The critical-line part needs only a uniform bound
  `∫|v′| ≤ K`, with no convergence of the infinite zero sum. Next: remove the unique-top hypothesis
  through the almost-periodic structure of the multi-top gap.
