# Critical-scale anti-crystal law (PTR gaplessness at depth C/log T)

- **ID:** PTR-CRIT-AC
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** ptr-goal-loop-2026-10-09.md rows 62–66; 3-formalized/ptr-anti-crystal-gapless-realization.md
- **Statement:** There is C > 0 such that, for all large T, the ordered zeta ordinates in [T^{1/2}, T³] are not
  (C/log T)-rigid. Hence every strict lower-Pólya E with Re E = Ξ, E ≠ 0 on ℝ, has for all large T a zero with
  Im z ≥ −2C/log T and Re z ∈ [T^{1/2} − 1, T³ + K].

## Goal
PTR's open core lives at depth c/log T. Rows 62–66 prove gaplessness of lossless ports at every fixed depth,
and at depth C/log log T. This card targets the critical scale itself: every lossless port of Ξ would be forced
to have resonances within O(1/log T), the zero-spacing scale.

## Gates
- [x] 0 → 1  in-progress: well-posed; attack idea below; countermodel analysis done
- [x] 1 → 2  fully-proven: paper proof v2 (below), every input a corpus theorem
- [x] 2 → 3  formalized: `exists_eventually_not_rigidWindow_critical`, `exists_eventually_shallow_resonance_critical`
  (XiCriticalityCriticalDepth); standard axioms only; all modules wired

## Approach
Critical rigidity: g' ≤ g e^{(g+g')L/C}, g ≤ g' e^{(g+g')L/C}, L = log T, so consecutive normalized gap ratios
are ≤ e^{4π/C}·(1+o(1)).

1. **Method limit (cycle 66).** Pair correlation on (0,1) alone cannot decide critical rigidity. Slowly varying
   lattices with local normalized spacing ν distributed with density ∝ ν^{−3}/ζ(2) on (1,∞), plus denser
   regions, reproduce F(α)=α on (0,1) at leading order.
2. **What kills the countermodel.** Short-range count control. Sparse stretches (ν ≥ 1/b > 1 over ≫ R zeros)
   carry count deficits ≍ R in windows of length R/L. The smooth-mass variance at scale R/L is O(1)·T
   (GUE: log R), so such windows are rare.
3. **Argument.**
   - Fix α₀ ∈ (0,1) and R large, then C ≫ R.
   - (a) Choose a Fejér-type ρ with ρ̂ supported in |β| ≤ ε, width R/L. Smooth mass M(t) = Σ_γ ρ(t−γ) has
     variance ≤ c₀ T (needs F(T^β,T) two-sided for |β| ≤ ε).
   - (b) Off an exceptional set of measure ≤ T/(η²R²), the zeros near t form a near-lattice with ν ∈ 1 ± η.
     This uses rigidity over span MR/L, which needs C ≫ MR.
   - (c) There the narrow oscillatory sum S(t) = Σ x^{iγ}ρ(t−γ), x = T^{α₀}, is O(1/δ) by summation by parts,
     since increments ≈ 2πα₀ν are non-resonant. On the exceptional set use Cauchy–Schwarz with (a).
   - (d) Narrow pair identity: ∫|S|² = ∫k(β)F(T^{α₀+β},T)dβ ≈ c T R α₀, by the corpus uniform F on compacts
     of (0,1). Contradiction for R large.
4. **Lean inputs needed.**
   - (A′) Montgomery uniform two-sided for 1 ≤ x ≤ T^{ε}, including the x^{−2}log T term. The corpus chain
     stops at x ≥ (log T)³ (`eventually_montgomeryForm_lower_uniform`), because the xbBlock energy
     T L²/x is main there.
   - (B) Narrow-kernel pair identity via Fourier integration of F over α.
   - (C) Rigidity + near-lattice summation by parts with polynomial-tail weights.

**[OPEN CORE]:** (A′). An unconditional Montgomery asymptotic for small x needs the exact energy of xbBlock
≈ −x^{−1/2+it}log(t/2π) and the cross term with the prime side. Alternative: Selberg's unconditional
∫|S(t+h)−S(t)|² ≪ T log(2+hL), which the corpus does not have.

## Paper proof (draft v1, 2026-10-11)
Notation: L = log T, N = #zeros with 0 < γ ≤ T, W = [T^{1/2}, T³], α₀ = 1/4, x = T^{α₀}.
Critical rigidity on W at scale C/L means: strict increase, g' ≤ g e^{(g+g')L/C}, g ≤ g' e^{(g+g')L/C}.
By `re_eq_half_of_strict_window`, every zero with ordinate in W is on the line ("local RH").

**Step V (count control under local RH).** For τ = B/L with B ≥ B₀ (absolute), let
M_τ(t) = Σ_ρ τ²/(τ²+(t−γ)²) and m(t) = (τ/2) log(t/2π). Then ∫_T^{2T} (M_τ − m)² dt ≤ K₀ T, with K₀ absolute.
- (V7) Hadamard: τ Re ξ'/ξ(½+τ+it) = Σ_ρ τ(½+τ−β)/|s−ρ|². Zeros of W contribute τ²/(τ²+(t−γ)²).
  The others are at distance ≥ T/2 and contribute O(τ L/T).
- Γ-part: Re ξ'/ξ = Re ζ'/ζ + ½ log(t/2π) + O(1/t), via the two-sided digamma bound in the corpus.
- (V1–V4) Selberg's rectangle formula `norm_logDeriv_zeta_add_selberg_le`:
  - parameters x = T^θ (θ = 1/20), c = 3/2, σ_L = −1, H = T^{3θ}, good horizontals with ‖G'/G‖ ≪ L²;
  - error o(1);
  - zero term ≤ 2x^{−τ}M_τ/(ℓτ²), with x^{−τ}/(ℓτ) = e^{−θB}/(θB) =: κ/2 small.
- Absorb the zero term: (1−κ)|M_τ − m| ≤ τ|P_x(s)| + κ m + o(1), where P_x is Selberg's smoothed
  von Mangoldt polynomial.
- (V5–V6) MVT: ∫_T^{2T} |P_x(½+τ+it)|² ≤ (T + O(x²)) Σ Λ(n)²/n^{1+2τ} ≤ 2T(1/(4τ²) + O(1/τ)).
  So τ²∫|P_x|² = O(T), and κ²m² ≤ e^{−2θB}/θ² = O(1).

**Step K (kernel).** φ ∈ C_c^∞[−1,1], even, φ ≥ 0, ∫φ = 1. Put K_R(Δ) = ∫ φ(β) e^{iβ(L/R)Δ} dβ.
This is a Schwartz function, K_R(0) = 1, width ≍ R/L.

**Step F (Montgomery averaged).**
- P := Σ_{γ,γ'} x^{i(γ−γ')} w(γ−γ') K_R(γ−γ') = ∫ φ(β) F(x e^{βL/R}, T) dβ, exactly (finite sums).
- Here x e^{βL/R} = T^{α₀+β/R}, and the corpus uniform asymptotic on [α₀−1/R, α₀+1/R] gives
  P = (T/2π) α₀ L (1+o(1)) = α₀ N (1+o(1)).

**Step L (local lattice).** P = Σ_γ Ψ(γ), with Ψ(γ) = Σ_{γ'} x^{i(γ−γ')} w K_R(γ−γ').
- Good γ (local mass within 1/10 of its mean at scale τ ≍ M₀R/L): rigidity over span ≍ M₀R/L with
  C ≫ M₀³R² makes the zeros there a lattice with spacing g = 2πν/L, ν ∈ [3/4, 3/2], up to relative error η.
- Poisson summation: Σ_m K_R(mg) e^{−iθm} = (1/g) Σ_k K̂_R((θ+2πk)/g) = 0, since θ = α₀Lg = 2πα₀ν
  stays ≥ 3/16·2π from 2πℤ while supp K̂_R ⊂ [−L/R, L/R] and 2πν/R < 3π/8.
- So |Ψ(γ)| ≤ (lattice error ≪ M₀³R²/C) + (w − 1 error = O((M₀R/L)²R)) + (tails ≪ R M₀^{1−n}).
- Bad γ: write P = ∫ Σ_γ ψ(t−γ)Ψ(γ) dt with a unit-mass bump ψ of width τ. The bad set E has
  |E| ≤ 100K₀T/m², and ∫_E |Q| ≤ (L/(M₀R)) ∫_E M_τ² ≤ (L/(M₀R)) 202K₀T.
- Zeros below T^{1/2} (possibly off-line): ≤ T^{1/2}L·x^{1}·O(L) = o(TL), since α₀ < 1/2.

**Conclusion.** α₀N(1+o(1)) = P ≤ N·(small) + O(K₀/(M₀R))·TL + o(TL). This is a contradiction for
M₀R ≫ K₀ and C ≫ M₀³R². Hence ¬rigid(C/L) for all large T.

**PTR corollary.** `rigidWindow_of_resonance_free` with h = 2C/L.

## Paper proof (v2, 2026-10-11, replaces the L-steps of v1)
Parameters: α₀ = 1/8, R = 16 (c = L/16, θ = α₀L), δ = 1/20, τ₁ = B₁/L, τ₂ = B₂/L = 32τ₁, h = τ₁, rigidity
scale h_rig = C/L, x_S = T^{1/20} (Selberg polynomial D). Order: B₁ huge, B₂ = 32B₁, C ≫ B₂³, then T large.
Y = 3T^{1/2}; Low = zeros with 0 < γ < Y; I = indices with Y ≤ γ_n ≤ T (on the line by strictness).

0. **Why one point is not enough.** A half-lattice of density 2ρ ending at t has the same Lorentz masses at t as a
   full lattice of density ρ, at every scale ≪ the rigidity scale. So goodness of t must test a grid
   p_j = t + 2jτ₂, |j| ≤ 6, at both scales.
1. **Low pairs.** |x^z w(z) K̃(z)| ≤ x·(4/(3+Δ²))·e^c, with z = ρ+ρ̄'−1, |Re z| < 1, |4 − z²| ≥ 3 + Δ², and
   |K̃(z)| ≤ e^{c|Re z|}. Row sums are ≤ 4T^{α₀+1/R}·lorentzMass = O(T^{α₀+1/R}L), and #Low = O(T^{1/2}L).
   Total O(T^{1/2+3/16}L²) = o(TL).
2. **Bulk.** P_bulk = Σ_{n∈I} Ψ_n, with Ψ_n = Σ_{m∈I} e^{iθΔ}·4/(4+Δ²)·K_c(Δ) and Δ = γ_n − γ_m.
   - Crude: ‖Ψ_n‖ ≤ 2M_{2R/L}(γ_n) ≤ 2M_{τ₁}(γ_n) ≤ 6M_{τ₁}(t) for |γ_n − t| ≤ τ₁, using K_c ≤ 2f_{2/c} and the
     shift f_τ(u+v) ≥ f_τ(u)/3 for |v| ≤ τ.
   - Edges (γ_n within 1 of Y or T): ‖Ψ_n‖ ≤ 4·lorentzMass = O(L), O(L) of them, so O(L²).
3. **Count control (C_p).** (1−δ)τλ/2 ≤ M_τ(p) ≤ (1+δ)τλ/2 for τ ∈ {τ₁, τ₂}, all grid p, with λ = ℓ_t.
   From V3: if ‖D(½+τ+ip)‖ ≤ Θ₀ := δ(L/2 − 2)/4 for all grid p and both τ, then (C_p) holds for T large.
4. **Window structure (deterministic).** Assume (C_p) and rigidity on [t − 12τ₂, t + 12τ₂].
   - (F1) Every grid p has a zero within τ₂. Otherwise M_{τ₁}(p) ≤ 2(τ₁/τ₂)²M_{τ₂}(p) ≤ (1+δ)τ₁²λ/τ₂, which is
     < (1−δ)τ₁λ/2.
   - (F2) Every gap g_m with γ_m ∈ [t − 8τ₂, t + 8τ₂] is < 4τ₂. A gap ≥ 4τ₂ contains a grid point at distance
     ≥ τ₂ from all zeros.
   - (F3) Any two gaps in that window have ratio ≤ e^η, η = 40B₂/C (gap_chain_span_local, span ≤ 20τ₂).
   - (F4) The window chain covers [t − 5τ₂, t + 5τ₂], by (F1) at p = t ∓ 6τ₂.
   - (F5) Upper bound on g (the sparse Lorentz sum): (1−δ)τ₁λ/2 − (1+δ)τ₁²λ/τ₂ ≤ 2 + πτ₁e^η/g.
   - (F6) Lower bound on g (the dense count): 2τ₁e^{−η}/g − 1 ≤ #{|γ − t| ≤ τ₁} ≤ 2M_{τ₁}(t) ≤ (1+δ)τ₁λ.
   - So ν = gL/2π ∈ [0.28, 2.6] for λ ≥ 0.45L, which is non-resonant for α₀ = 1/8, R = 16.
5. **Good row (deterministic).** For |γ_n − t| ≤ τ₁, take g = g_n and M = ⌈τ₂e^η/g⌉.
   - Near-lattice with ε = e^η − 1; far zeros are at distance ≥ τ₂; the far mass is ≤ 3(1+δ)τ₂λ/2.
   - `norm_fejer_pair_sum_le` gives ‖Ψ_n‖ ≤ 16R²/(2πν_lo B₂) + (α₀+2/R)2πν_hi(e^η−1)(2M+1)M + o(1)
     + 12(1+δ)R²/B₂ =: ε₁.
6. **Box partition.** For interior n: 2h‖Ψ_n‖ = ∫1_{|t−γ_n|≤h}‖Ψ_n‖dt.
   - For good t, every row in the box is ≤ ε₁. For bad t, Σ_{box ∋ t}‖Ψ_n‖ ≤ 2M_h(t)·6M_{τ₁}(t) ≤ 12Maj(t)²,
     where Maj = 2(B₁ + τ₁‖D(½+τ₁+it)‖) (V3 at t).
   - Markov: vol(bad ∩ [a,b]) ≤ 26·(1/Θ₀²)·5(T+o(T))/τ₁².
   - Hence Σ_int‖Ψ_n‖ ≤ ε₁·N(T) + (6/h)·8(B₁²·vol(bad) + 5.1T) ≤ ε₁N(T) + 1.6·10⁸TL/B₁.
7. **Contradiction.** Re P ≥ (1−ε)(T/2π)L/8 (F1 module), while |P| ≤ o(TL) + ε₁N(T) + 1.6·10⁸TL/B₁ + O(L²).
   This is false for B₁ ≥ 10¹², ε₁ ≤ 1/200, T large. Hence ¬RigidWindow(C/L, T).

## Lean modules (final, all wired, axioms: propext, Classical.choice, Quot.sound)
- HTGeometry.LorentzOrderedSums: lattice/sparse/dense Lorentz sums; shift (×3), scale and tail comparisons.
- HTGeometry.FejerLatticeVanishing / FejerNearLattice: Poisson vanishing on lattices; near-lattice bound;
  `norm_fejer_pair_sum_le` (one row with weight and far tail); `norm_fejerKernel_le_two_lorentzF`.
- HTGeometry.BoxPartitionSums: `box_partition_sum_le` (good/bad split by ∫⁻), `volume_Icc_inter_lt_norm_le`
  (Chebyshev).
- RHTower.ZetaNarrowLorentzMass, ZetaNarrowCountControl (V1–V3), MontgomeryAveragedForm (F1).
- RHTower.ZetaCriticalWindowStructure: `CountControl`, `window_structure`.
  Grid control and rigidity give gaps < 4τ₂, ratios ≤ e^{40τ₂/h}, coverage, and sparse/dense spacing bounds.
- RHTower.ZetaCriticalRowBound: `critRow`, crude bounds, and `norm_critRow_le_of_window` (good row by Poisson).
- RHTower.ZetaCriticalGoodRows: `norm_critRow_le_of_countControl`.
- RHTower.ZetaCriticalRowNumerics: `norm_critRow_le_critical`
  (‖Ψ_n‖ ≤ 10⁻⁴ at B₁ = 10¹³, B₂ = 32·10¹³, C = 10⁶⁰).
- RHTower.ZetaCriticalPairDecomposition: pair term bounds, on-line identity, bulk rows, low pairs.
- RHTower.ZetaCriticalCountControl: count control from V3, majorant, bad set, Chebyshev + mean square.
- RHTower.ZetaCriticalInteriorRows: good/bad heights and `sum_norm_critRow_interior_le`
  (Σ_int ≤ 10⁻⁴#I + TL/20000).
- RHTower.ZetaZeroAntiCrystalCritical: `false_of_critical_facts`.
- RHTower.ZetaCriticalAsymptotics: N(T), low pairs, edges, mean-square length, width mass, V3 range, all eventual.
- RHTower.XiCriticalityCriticalDepth: the theorem and the PTR corollary.

## No-go closure (mandatory when falsified)
- n/a (open)

## Log
- 2026-10-11 — created after cycle 66 (log log depth proved). Countermodel analysis recorded above.
- 2026-10-11 — formalized (cycle 67). Final constants: α₀ = 1/8, R = 16, δ = 1/20, B₁ = 10¹³, B₂ = 32·10¹³,
  C = 10⁶⁰. Grid count control at 13 points × 2 scales replaces single-point control. A half-lattice of double
  density defeats single points.
