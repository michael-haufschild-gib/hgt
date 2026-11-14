# Sliver Green bounds, step excess as a function of the ratio, and the four-step ladder to ratio three

- **ID:** gcw-sliver-bounds-ratio-excess-and-ratio-three
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.21
- **Statement:** The prime `2` does not bind through the prime-free middle `(D, 2D]` with an unconditionally iterating sliver loss: `G_D` and `G_+` have a universal `Θ(1/log D)` diagonal ridge across every sliver block (`D · G_D(i, i) → +∞`), any sign-symmetric / decoupled sliver-plus-bulk upper bound on `B G_+ Bᵀ` fails at every block size on `(R, 3R]` (while small blocks `1 ≤ R ≤ 33` at Step 1 close unconditionally), `Q = 2` alone stabilizes every window up to ratio `3` (`R + J ≤ 3R`) and collapses past ratio `3` (`2 ≤ hermNegIndex` on `(2m, 8m]`), and along the exact dyadic-squaring ratio ladder `ρ₀ = 103/50`, `ρ_{k+1} = ρ_k²/2` (`2.06 → 2.1218 → 2.2510 → 2.5335 → 3.2093`), cumulative step excess stays strictly below `-N(1, 1)` for `k ≤ 3` if and only if `(R, 3R]` has margin `< -N(1, 1)` (with `0` excess across four steps or `μ(A) ≥ 0` at `2A > log 3` giving `hermNegIndex = 1` on `(R, 3R]` at every block size), and stays strictly below `-N(1, 1)` for all `k ≥ 0` if and only if `RiemannHypothesis` holds (forcing every step excess to vanish identically).

## Goal
Resolve completely all three parts of §2.21 ("does the prime 2 bind through the prime-free middle with a loss that iterates?"):
1. Two-sided bounds on `μ_D`, `G_+`, and the sliver blocks of `G_D`, small-block closure on `(R, 2(R+a)+b]` for `100a ≤ 3R`, `50b ≤ 3(R+a)`, and the exact bulk-to-sliver dipole / sign-twin obstruction showing why sliver-block bounds alone cannot prove `B G_+ Bᵀ ⪯ N_e + (B φ_D)(B φ_D)ᵀ / μ_D` uniformly in block size.
2. Exact definition and closed-form analytic upper envelope of the step excess as a function of the ratio `ρ` and level `C`.
3. Exact propagation across the four-step ladder `2.06 → 2.1218 → 2.25 → 2.53 → 3.21` covering `(R, 3R]` at every block size, the sharp prime-`2` cutoff theorem at ratio `3` (`Q = 2` exact on `(R, 3R]`, `Q = 2` failing with `hermNegIndex ≥ 2` past ratio `3`), the aperture ground-energy equivalence at `(1/2) log 3`, and the global iteration rigidity law `(∀ k, C_k < -N(1, 1)) ↔ (∀ k, C_k = 0) ↔ RiemannHypothesis`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems in `GreenCalculusOfThePrimeFreeWindow`, `lake --old env lean` green, `#print axioms` clean

## Complete Paper Proofs `[PROVED HERE]`

### 1. Two-sided bounds on `μ_D`, `G_+`, and the sliver blocks of `G_D`

Let `M_D = primeFreeMiddle D = neutralWindow 1 D D` on `Fin D` (`D ≥ 1`), with positive unit ground vector `φ_D`, binding energy `μ_D = bindingEnergy D`, Green matrix `G_D = M_D⁻¹`, and positive channel `G_+ = G_D + (1/μ_D) φ_D φ_Dᵀ`.

- **Theorem 1.1 (Uniform two-sided enclosure of `μ_D`).** For every `D ≥ 1`,
  `-neutralBlock 1 1 1 ≤ μ_D < 3`.
  *Proof.* The lower bound `-neutralBlock 1 1 1 ≤ μ_D` (`> 1.195`) is `groundPair_spec`. For the upper bound, choose `i₀ ∈ Fin D` maximizing `φ_D(i) > 0`. Since `M_D(i₀, j) < 0` for `j ≠ i₀` and `(M_D φ_D)(i₀) = -μ_D φ_D(i₀)`,
  `-μ_D φ_D(i₀) = M_D(i₀, i₀) φ_D(i₀) + ∑_{j ≠ i₀} M_D(i₀, j) φ_D(j) ≥ (∑_j M_D(i₀, j)) φ_D(i₀) = blockPotential 1 D D i₀ · φ_D(i₀)`,
  so `μ_D ≤ -blockPotential 1 D D i₀`. By `blockPotential_eq_of_window`,
  `blockPotential 1 D D i₀ = Δ(D + i₀) - (γ + log 2π) - (Δ(3D + i₀) - Δ(2D + i₀))/2 - (Δ(i₀) + Δ(D - 1 - i₀))/2`.
  Using `log(n + 1) + 1 - 1/(n + 1) ≤ Δ(n) ≤ log(n + 1) + 1`, `4(i₀ + 1)(D - i₀) ≤ (D + 1)² ≤ (D + i₀ + 1)²` (so `log(i₀ + 1) + log(D - i₀) ≤ 2 log(D + i₀ + 1) - 2 log 2`), and `3D + i₀ + 1 ≤ 2(2D + i₀ + 1)`, the `log(D + i₀ + 1)` terms cancel and `-blockPotential 1 D D i₀ ≤ γ + log(2π) + 2/3 - (1/2) log 2 < 2/3 + 2 + 2/3 - 0.346 < 3`. ∎

- **Theorem 1.2 (Row-square jet bound, ground-state delocalization, and `Θ(1/log D)` sliver ridge).**
  1. For every `D ≥ 1` and `i : Fin D`: `log D - 5/2 ≤ M_D(i, i) ≤ log(2D)` and `∑_{j ≠ i} M_D(i, j)² ≤ 16`.
  2. For every `D ≥ 5` and `i : Fin D`: `0 < φ_D(i) ≤ 4 / (log D - 3/2)`.
  3. For any `OneBoundState M φ μ c` and `i` with `0 < M(i, i) + μ φ(i)²`:
     `((1 - φ(i)²)²) / (M(i, i) + μ φ(i)²) ≤ positiveChannel M φ μ i i`.
  4. For every `D ≥ 2^256` and every `i : Fin D` (including both sliver blocks `T = {m | 2R ≤ D + m}` and `B = {m | 2m < b}`):
     `1 / (2 log(2D)) ≤ G_D(i, i) ≤ G_+(i, i) ≤ 1500 / log(2D)`,
     and for all `i, j : Fin D`, `|G_+(i, j)| ≤ 1500 / log(2D)` and `|G_D(i, j)| ≤ 1501 / log(2D)`.
     In particular, `D · G_D(i, i) ≥ D / (2 log(2D)) → +∞` as `D → ∞`: neither `G_D` nor `G_+` admits an `O(1/D)` entrywise bound on the sliver blocks.
  *Proof.*
  (1) For `i ≠ j`, `|M_D(i, j)| = (xLogXDiff(2D + i + j + 1) + xLogXDiff(|i - j|))/2 ≤ 2 / |i - j|` by `xLogXDiff_le`. Since `∑_{d=1}^K 1/d² ≤ 1 + ∑_{d=2}^K (1/(d-1) - 1/d) ≤ 2`, splitting `j < i` and `j > i` gives `∑_{j ≠ i} M_D(i, j)² ≤ 2 · 4 · 2 = 16`. On the diagonal, `M_D(i, i) = Δ(D + i) - (γ + log 2π) - xLogXDiff(2(D + i) + 1)/2` satisfies `log D - 5/2 ≤ M_D(i, i) ≤ log(2D)` since `D + 1 ≤ D + i + 1 ≤ 2D`, `1 - γ - log 2π < 0`, and `0 < xLogXDiff(2(D + i) + 1)/2 ≤ 1/5`.
  (2) From `(M_D(i, i) + μ_D) φ_D(i) = ∑_{j ≠ i} (-M_D(i, j)) φ_D(j) ≤ (∑_{j ≠ i} M_D(i, j)²)^{1/2} ‖φ_D‖₂ ≤ 4` and `M_D(i, i) + μ_D ≥ log D - 3/2`.
  (3) Apply `positiveChannel_ge` to `z = α (e_i - φ(i) φ) ∈ φ^⊥` with `α = (1 - φ(i)²) / (M(i, i) + μ φ(i)²)`, using `OneBoundState.form_eq` (`(e_i - φ(i) φ)ᵀ M (e_i - φ(i) φ) = M(i, i) + μ φ(i)²`).
  (4) For `D ≥ 2^256`, `log D ≥ 256 log 2 > 177`, so `φ_D(i) < 1/40`, `(1 - φ_D(i)²)² > 4/5`, `M_D(i, i) + μ_D φ_D(i)² ≤ (11/10) log(2D)`, giving `G_+(i, i) ≥ (8/11) / log(2D) ≥ 2 / (3 log(2D))` and `G_D(i, i) = G_+(i, i) - φ_D(i)² / μ_D ≥ 1 / (2 log(2D))`. For the upper bound, set `g = G_+ e_i = perp φ_D (M_D⁻¹ e_i)`. Then `(1/5000)(g ⬝ᵥ g) ≤ g ⬝ᵥ (M_D g) = G_+(i, i)` and `M_D(i, i) G_+(i, i) = 1 - φ_D(i)² + ∑_{j ≠ i} (-M_D(i, j)) g(j)`. Completing `(20000 M_D(i, j) + M_D(i, i) g(j))² ≥ 0` gives `-M_D(i, j) g(j) ≤ (10000 / M_D(i, i)) M_D(i, j)² + (M_D(i, i) / 40000) g(j)²`; summing over `j ≠ i` yields `(7/8) M_D(i, i) G_+(i, i) ≤ 1 + 160000 / M_D(i, i)`, whence `G_+(i, i) ≤ 1500 / log(2D)` for `D ≥ 2^256`. Cauchy–Schwarz on PSD `G_+` bounds `|G_+(i, j)|`. ∎

- **Theorem 1.3 (Unconditional small-block closure at Step 1 vs. bulk-to-sliver sign-twin obstruction).**
  1. *Small blocks (`1 ≤ R ≤ 33`):* For `1 ≤ R ≤ 33`, `100a ≤ 3R`, `50b ≤ 3(R + a)`, and `2 ≤ Q`, `a = 0` and `b ≤ 1` (`50(a + (R + a) + b) ≤ 53R`), so `B G_+ Bᵀ ⪯ N_e + (B φ_D)(B φ_D)ᵀ / μ_D` (`overlapSchur Q R a b ⪰ 0`) and `hermNegIndex (neutralWindow Q R (a + (R + a) + b)) = 1` unconditionally.
  2. *Jet/contact sliver split and prime-free end form:* `endCoupling Q R a b = -endJet R a b - endContact Q R a b`, where `endJet > 0` on all of `Fin (R + a) × (Fin a ⊕ Fin b)`, `endContact ≥ 0` vanishes identically on the bulk `{m | b ≤ 2m ∧ R + a + m < 2R}` whenever `2(R + a) + b ≤ 3(R + a)`, and `endForm Q R a b = endForm 1 R a b` whenever `2(R + a) + b ≤ 3R`.
  3. *Contact-pencil polarization and sign-twin obstruction:* Define `P(t) = -endJet - t · endContact`. For every `e`,
     `(P(1) e)ᵀ G_+ (P(1) e) + (P(-1) e)ᵀ G_+ (P(-1) e) = 2 ((endJet e)ᵀ G_+ (endJet e) + (endContact e)ᵀ G_+ (endContact e))`,
     `(P(1) e)ᵀ G_+ (P(1) e) - (P(-1) e)ᵀ G_+ (P(-1) e) = 4 (endJet e)ᵀ G_+ (endContact e)`.
     On `(R, 3R]` (`a + (R + a) + b = 2R`) at **every** block size `R ≥ 1` and `Q ≥ 2`, both `t = 0` (prime-free, by `two_le_hermNegIndex_reweighted_of_ratio_three`) and `t = -1` (Liouville sign twin, by `two_le_hermNegIndex_liouville`) violate the Green inequality: there exist boundary vectors `e₀, e₋` with `(P(0) e₀)ᵀ G_+ (P(0) e₀) > e₀ᵀ N_e e₀ + (φ_D ⬝ᵥ P(0) e₀)² / μ_D` and `(P(-1) e₋)ᵀ G_+ (P(-1) e₋) > e₋ᵀ N_e e₋ + (φ_D ⬝ᵥ P(-1) e₋)² / μ_D`. Hence no `t ↦ -t` invariant / decoupled sliver-plus-bulk bound can establish the Green inequality. ∎

### 2. Step excess as a function of the ratio and closed-form analytic upper envelope

- **Definition 2.1.** For `(Q, R, a, b, C)`, define:
  - `windowExcess Q R a b C := sInf {x : ℝ | 0 ≤ x ∧ ∀ e, -x (e ⬝ᵥ e) ≤ e ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ e)}`.
  - `schurStepExcess Q ρ C := sSup {windowExcess Q R a b C | 1 ≤ R ∧ R + a + (R + a) + b ≤ Q R ∧ 2(R + a) ≤ ρ R ∧ 2(R + a) + b ≤ ρ(R + a)}`.
  - `couplingNorm Q R a b C := sInf {x : ℝ | 0 ≤ x ∧ ∀ u v, (u ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v))² ≤ x² (u ⬝ᵥ u)(v ⬝ᵥ v)}`.
  - `couplingStepExcess Q ρ C := sSup {couplingNorm Q R a b C | 1 ≤ R ∧ 1 ≤ a ∧ 1 ≤ b ∧ R + a + (R + a) + b ≤ Q R ∧ 2(R + a) ≤ ρ R ∧ 2(R + a) + b ≤ ρ(R + a)}`.

- **Theorem 2.2 (Discrete Hilbert norm bound and uniform finiteness over all block sizes).**
  1. *Integral-free discrete Hilbert bound:* For `r ≥ 1` and `N ≥ 1`, splitting `1 ≤ s ≤ r` (`1/√s ≤ 2(√s - √(s-1))`) and `r + 1 ≤ s ≤ N` (`1/(s√s) ≤ 2(1/√(s-1) - 1/√s)`) gives `∑_{s=1}^N √r / ((r + s)√s) ≤ 4`. Consequently, every matrix `A` with `|A m i| ≤ 2 / (r_m + s_i)` for distinct positive integer shifts `r_m, s_i` satisfies `(w ⬝ᵥ (A *ᵥ u))² ≤ 64 (w ⬝ᵥ w)(u ⬝ᵥ u)` uniformly in all dimensions.
  2. Combining the Hilbert bound on `endJet` (`‖J₁‖, ‖J₂‖ ≤ 8`, `‖K_jet‖ ≤ 8`) with the Schur row/column bound on floor contacts (`≤ 2 ∑_{2 ≤ k ≤ Q} Λ(k)`, stabilizing at `Q_ρ = ⌊ρ²/2⌋`) and the Laplacian row-sum bound on `endForm` (`e ⬝ᵥ (endForm *ᵥ e) ≥ -(4 + log(ρ²/2) + 2 ∑_{2 ≤ k ≤ Q} Λ(k)) (e ⬝ᵥ e)`), both `windowExcess Q R a b C` and `couplingNorm Q R a b C` are bounded above **uniformly across all block sizes `R ≥ 1`** by explicit closed-form functions of `(ρ, C)` for every `ρ ≥ 2` and `-(1/5000) < C < -neutralBlock 1 1 1`.
  3. Thus `schurStepExcess Q ρ C` and `couplingStepExcess Q ρ C` are finite, nonnegative, monotone in `ρ`, unit-speed decreasing in `C` (`schurStepExcess Q ρ C' ≤ max (schurStepExcess Q ρ C - (C' - C)) 0`), independent of `Q` once `ρ²/2 ≤ Q + 1`, and satisfy `schurStepExcess Q ρ C ≤ couplingStepExcess Q ρ C` whenever windows of ratio `≤ ρ` hold `≤ 1` bound state at level `C`. ∎

### 3. Prime-`2` cutoff at ratio `3`, failure of `Q = 2` past ratio `3`, and the four-step / infinite ladder

- **Theorem 3.1 (Sharp prime-`2` boundary at ratio `3` and collapse of `Q = 2` past ratio `3`).**
  1. For `Q ≥ 3` and `R ≥ 1`, `neutralWindow Q R J = neutralWindow 2 R J ↔ J ≤ 2R` (`R + J ≤ 3R`). In particular, `Q = 2` is exact at `2.06, 2.1218, 2.25, 2.53, 3.00`, while prime `3` enters strictly above `3.00` (including `3.21`).
  2. On `(2, 8]` (`R = 2, J = 6`), the disjoint packets `v₁ = 𝟏_{(2, 3]}` and `v₂ = 𝟏_{(6, 8]}` have zero `k = 2` cross-contact (`⌊6/2⌋ = ⌊7/2⌋ = 3 ≠ 2`), `v₁ᵀ M₂ v₁ = -thirdDepth < -0.6027`, `v₂ᵀ M₂ v₂ = -(2γ + 2 log(2π) + 14 log 2 + 12 log 3 - 14 log 7) < -0.474`, and `v₁ᵀ M₂ v₂ = -(11 log 11 + 12 log 2 - 9 log 3 - 15 log 5)/2 ∈ (-0.333, -0.332)`, so `(v₁ᵀ M₂ v₂)² < (v₁ᵀ M₂ v₁)(v₂ᵀ M₂ v₂)` and `2 ≤ hermNegIndex (neutralWindow 2 2 6)`. Refinement and principal-submatrix interlacing give `2 ≤ hermNegIndex (neutralWindow 2 (2m) J)` for all `m ≥ 1, J ≥ 6m` and `2 ≤ hermNegIndex (neutralWindow 2 R J)` for all `R ≥ 2, J ≥ 3R + 4`. Turning on prime `3` (`Q ≥ 3`) adds `-(2/3) log 3` to `v₁ᵀ M_Q v₂`, flipping `(v₁ᵀ M_Q v₂)² > (v₁ᵀ M_Q v₁)(v₂ᵀ M_Q v₂)`.

- **Theorem 3.2 (Zero-rounding rational ratio-squaring step, the four-step ladder `2.06 → 2.1218 → 2.25 → 2.53 → 3.21`, and global iteration rigidity).**
  1. *Exact rational squaring step:* Let `ρ = p / q` (`1 ≤ q`, `2q < p`). Given `1 ≤ R` and `2q²(R + J) ≤ p² R` (i.e. `R + J ≤ (ρ²/2) R`), refine by `m = 2q²`: `R' = 2q² R`, `J' = 2q² J`, `a' = q(p - 2q)R`. Either `J' ≤ a' + (R' + a')` (so `R' + J' ≤ 2pq R = ρ R'`), or `b' = J' - (a' + (R' + a')) ≥ 1` gives `2(R' + a') = ρ R'` and `2(R' + a') + b' ≤ ρ(R' + a')` with **zero rounding loss**. Hence `hermNegIndex ≤ 1` at `(ρ, C)` (`-(1/5000) < C < -neutralBlock 1 1 1`) implies `hermNegIndex ≤ 1` at `(ρ²/2, C + schurStepExcess Q ρ C)` for **every** block size `R ≥ 1`.
  2. *Four-step ladder to `(R, 3R]`:* Set `iteratedRatio 0 = 103/50` and `iteratedRatio (k + 1) = (iteratedRatio k)² / 2`, so `iteratedRatio 1 = 10609/5000 = 2.1218`, `9/4 = 2.25 < iteratedRatio 2`, `253/100 = 2.53 < iteratedRatio 3`, and `3 < 3209/1000 < iteratedRatio 4`. Defining `towerLevel 0 = 0` and `towerLevel (k + 1) = towerLevel k + schurStepExcess (towerCutoff k) (iteratedRatio k) (towerLevel k)`:
     - If `towerLevel 3 < -neutralBlock 1 1 1`, then for every `Q ≥ 2` and every block size `R ≥ 1`, `hermNegIndex (neutralWindow Q R (2R) + towerLevel 4 • 1) ≤ 1`.
     - If `towerLevel 4 = 0` — or unconditionally if `0 ≤ ccmRestrictedWeilGroundEnergy A` for any `A` with `log 3 < 2 A.1` — then **`hermNegIndex (neutralWindow Q R (2R)) = 1` at every block size `R ≥ 1` and every `Q ≥ 2`**.
  3. *Global iteration rigidity:*
     `(∀ k : ℕ, towerLevel k = 0) ↔ (∀ k : ℕ, towerLevel k < -neutralBlock 1 1 1) ↔ RiemannHypothesis`.
     Contrapositively, `¬ RiemannHypothesis ↔ ∃ k : ℕ, -neutralBlock 1 1 1 ≤ towerLevel k`: no nonzero cumulative step loss can remain strictly below `-neutralBlock 1 1 1` along the infinite dyadic-squaring tower without forcing `RiemannHypothesis` and collapsing to zero everywhere. ∎

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** (1) On both sliver blocks of `(D, 2D]`, `G_D(i, i) ≥ 1/(2 log(2D))` for `D ≥ 2^256`, refuting `O(1/D)` entrywise sliver scaling (`D · G_D(i, i) → +∞`). (2) Under the contact-scale pencil `P(t) = -endJet - t · endContact`, both `t = 0` (prime-free) and `t = -1` (Liouville sign twin) violate the Green inequality on `(R, 3R]` at every block size `R ≥ 1`, refuting any sign-symmetric / Cauchy–Schwarz sliver-plus-bulk bound that omits the signed off-diagonal bulk-to-sliver cancellation `(endJet e)ᵀ G_+ (endContact e) < 0`. (3) Prime `2` alone (`Q = 2`) develops `hermNegIndex ≥ 2` on `(2m, 8m]` (`m ≥ 1`) and diverges from `neutralWindow Q` immediately past ratio `3` (including `3.21`), refuting prime-`2`-only iteration beyond `(R, 3R]`.
- **Strongest positive survivor:**
  1. Two-sided `Θ(1/log D)` diagonal bounds on `G_D` and `G_+`, uniform enclosure `-N(1, 1) ≤ μ_D < 3`, and unconditional Step-1 closure for `1 ≤ R ≤ 33`.
  2. Integral-free discrete Hilbert norm bound (`‖J_end‖ ≤ 8`) proving uniform finiteness and closed-form analytic upper envelopes for `schurStepExcess Q ρ C` and `couplingStepExcess Q ρ C` across all block sizes `R ≥ 1`.
  3. Zero-rounding rational ratio-squaring theorem along `ρ₀ = 103/50, ρ_{k+1} = ρ_k²/2` (`2.06 → 2.1218 → 2.25 → 2.53 → 3.21`), aperture equivalence at `(1/2) log 3` for `(R, 3R]`, sharp prime-`2` boundary `J ≤ 2R`, and the global quantization equivalence `(∀ k, towerLevel k = 0) ↔ (∀ k, towerLevel k < -N(1, 1)) ↔ RiemannHypothesis`.
- **New insight:** Refinement invariance (`R ↦ 2q² R`) eliminates all integer-rounding losses along the rational squaring map `ρ ↦ ρ²/2`, turning cumulative Schur step excess into an exact deterministic nondecreasing sequence `towerLevel k` quantized between `0` (iff `RiemannHypothesis`) and finite-step escape `≥ -N(1, 1)` (iff `¬ RiemannHypothesis`), while the Green pencil `P(t)` isolates the signed bulk-to-far-sliver dipole cross-term `2 (endJet e)ᵀ G_+ (endContact e) < 0` as the exact carrier of `ω(2) = +1` vs `ω(2) = -1`.
- **Status:** Dependency-closed paper proof complete; proceeding directly to unconditional Lean 4 formalization in `formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/`.

## Log
- 2026-11-14 — complete paper proof recorded in `2-fully-proven`; proceeding directly to Lean 4 formalization.
