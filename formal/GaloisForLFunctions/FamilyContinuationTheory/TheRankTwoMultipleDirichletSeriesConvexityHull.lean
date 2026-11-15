import GaloisForLFunctions.FamilyContinuationTheory.TheFloorBinBilinearGramIdentity
import GaloisForLFunctions.FamilyContinuationTheory.TheMetaplecticVoronoiExponentInvariants

/-!
# The rank-two multiple Dirichlet series convexity hull and estimate-ladder exclusion

In a Weyl-group multiple Dirichlet series of root system `A₂` and residue-symbol order `n ≥ 2` over
`K = ℚ(ω)`, the normalized series
`Z^*(s₁, s₂) = ξ_K(n s₁ − n/2 + 1) ξ_K(n s₂ − n/2 + 1) ξ_K(n(s₁ + s₂) − n + 1) Z(s₁, s₂)`
continues meromorphically via the two reflections `w₁(s₁, s₂) = (1 − s₁, s₁ + s₂ − ½)` and
`w₂(s₁, s₂) = (s₁ + s₂ − ½, 1 − s₂)` generating `W(A₂) ≅ S₃`. Evaluating this two-variable
continuation against the estimate ladder of the compensated sextic probe resolves all three
rank-two producer tests in the negative and establishes the exact convex-analytic and minimax
boundaries separating rank two from `7/8`:

* **`W(A₂) ≅ S₃` scattering duality, empty chamber intersection, and Kubota polar locus**
  (`one_sub_kubotaArg_reflect`, `normalizingTriple_weylS1`, `not_weylCone_interior_strip`,
  `kubotaPolarLocus_slice_iff`). Under `s ↦ 1 − s`, `1 − (n s − n/2)` equals `n(1 − s) − n/2`
  reflected to `n s − n/2 + 1`, matching `ξ_K(1 − z) = ξ_K(z)` against the Kubota–Patterson
  scattering denominator `ξ_K(n s − n/2 + 1)`. None of the six absolute-convergence cones
  `w⁻¹([1, ∞)²)` intersects the critical slice `(0, 1) × ℝ`, and on `s₁ = (1 − δ)/2` the `W(A₂)`
  Kubota polar hyperplanes meet `s₂` at `{½ ± 1/n, ½ ± 1/n + δ/2}` with rightmost pole
  `½ + 1/n + δ/2` (`419/408` at `n = 3, δ = 79/204`).
* **Braid-invariant Stirling cocycle and exact two-variable `W(A₂)` convexity hull**
  (`weylStirlingCocycle_braid`, `weylA2Convexity_le_convex_cone_sum`,
  `exists_convex_cone_attaining_weylA2Convexity`). Accumulating single-reflection Stirling
  log-costs `(½ − a) L_a` satisfies the braid cocycle identity across all `(L₁, L₂, L₁₂) ∈ ℝ³`. At
  `|Im s₁| = O(1), |Im s₂| = T → ∞` (`(0, 1, 1)`), the exact convex lower envelope of the six cone
  growth bounds on `[0, 1] × ℝ` is
  `weylA2Convexity(σ₁, σ₂) = max(0, 1 − (σ₁ + 2σ₂)/3, 3/2 − (2σ₁ + 4σ₂)/3, 3/2 − σ₁ − 2σ₂)`,
  attained at every point of `[0, 1] × ℝ` by an explicit convex combination of cone points.
* **Sharp-truncation Perron plateau and binding-bin exclusion** (`perronSharpExponent_ge`,
  `perronSharpExponent_eq_plateau`, `binding_bin_a2_specialization_chain`). Along `s₁ = (1 − δ)/2`,
  the sharp-truncation Perron exponent `(σ₂ + 2 μ A₀)/(1 + 2 μ)` (`A₀ = (5 + δ)/4`) has global
  minimum `7/8 + δ/4` (`793/816` at `δ = 79/204`), constant across `[−(1 − δ)/4, (2 + δ)/4]`. Every
  `A₂` specialization exponent (`793/816 < 1 < 419/408 < 487/408 < 1099/816`) strictly exceeds both
  `rowCount(79/204, ½) + δ/2 = 224609/260712` and the `7/8` threshold `4571/5304`.
* **Universal global minimax half-plane laws and rank-two rejection boundaries**
  (`universal_balanced_minimax_le`, `universal_unslotted_minimax_le`,
  `rank_two_rejection_boundary_exponents`). For `δ ≥ 0, R ≥ 2/3`, the global minimax of
  `max(lowBoundaryGen, highBoundary)` over `ℝ³` is bounded below by `1 − 2/(3(6R + 6δ − 1))`
  (attained whenever `R + δ ≤ 3/2`), and over `ℓ ≥ 0` with `R ≤ (δ + 5)/6, R + δ ≥ 4/9` by
  `(3R + 3δ + 1)/(2R + 2δ + 3)` (attained whenever `R + δ ≥ 3/2`), giving exact rejection
  boundaries `1` (`δ = 1, R = 1`), `679/747` (`δ = 79/204, R = 1`), `1474/1599`, `577/645` (`39/40`
  at `δ = 1`), `1121/1257`, and `2173/2445`, all strictly above `7/8`.
* **Conductor doubling, Kubota–signed-Gram bifurcation coincidence, and off-diagonal payoff ladder**
  (`row_mean_square_conductor_doubling`, `kubota_pole_eq_signedGram_bifurcation`,
  `offDiag_saving_payoff_and_obstruction`). Squaring a linear row sum doubles `(κ, κ') = (1, 1)`
  (`A₂`, trace `−1`, order `3`) to `(2, 2)` (`Ã₁`, trace `2`, parabolic); on `δ = 0`, the `A₂`
  Kubota pole `½ + 1/n` coincides with the signed-Gram phase transition `R_crit(n) = ½ + 1/n`
  (`5/6` at `n = 3`, `s = 0`), while `probeThetaHybridFree 6 ≥ 4/5` locks `s = 0 < 1/12` across all
  geometries (`5/6 − s` hits `3/4` at `s = 1/12` and `2/3` at `s = 1/6`).
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.Budget

open Finset

noncomputable section

/-! ### `W(A₂) ≅ S₃` reflections, scattering duality, and Kubota polar locus -/

/-- First simple-root Weyl reflection of `A₂` in Dirichlet-series coordinates:
`(s₁, s₂) ↦ (1 − s₁, s₁ + s₂ − ½)`. -/
def weylS1 (p : ℝ × ℝ) : ℝ × ℝ := (1 - p.1, p.1 + p.2 - 1 / 2)

/-- Second simple-root Weyl reflection of `A₂` in Dirichlet-series coordinates:
`(s₁, s₂) ↦ (s₁ + s₂ − ½, 1 − s₂)`. -/
def weylS2 (p : ℝ × ℝ) : ℝ × ℝ := (p.1 + p.2 - 1 / 2, 1 - p.2)

/-- Longest element `w₀ = w₁ w₂ w₁ = w₂ w₁ w₂` of `W(A₂)`: `(s₁, s₂) ↦ (1 − s₂, 1 − s₁)`. -/
def weylLongest (p : ℝ × ℝ) : ℝ × ℝ := (1 - p.2, 1 - p.1)

/-- Enumeration of the six elements `(e, w₁, w₂, w₁ w₂, w₂ w₁, w₀)` of `W(A₂) ≅ S₃`. -/
def weylAct : Fin 6 → ℝ × ℝ → ℝ × ℝ
  | 0 => fun p => p
  | 1 => weylS1
  | 2 => weylS2
  | 3 => fun p => weylS1 (weylS2 p)
  | 4 => fun p => weylS2 (weylS1 p)
  | 5 => weylLongest

theorem weylS1_involutive : Function.Involutive weylS1 := by
  rintro ⟨σ₁, σ₂⟩
  simp only [weylS1, Prod.mk.injEq]
  constructor <;> ring

theorem weylS2_involutive : Function.Involutive weylS2 := by
  rintro ⟨σ₁, σ₂⟩
  simp only [weylS2, Prod.mk.injEq]
  constructor <;> ring

theorem weylLongest_involutive : Function.Involutive weylLongest := by
  rintro ⟨σ₁, σ₂⟩
  simp only [weylLongest, Prod.mk.injEq]
  constructor <;> ring

/-- Braid relation `w₁ w₂ w₁ = w₂ w₁ w₂ = w₀` and Coxeter order `(w₁ w₂)³ = id` of `W(A₂)`. -/
theorem weylA2_braid_and_order_three (p : ℝ × ℝ) :
    weylS1 (weylS2 (weylS1 p)) = weylLongest p ∧
      weylS2 (weylS1 (weylS2 p)) = weylLongest p ∧
      (weylS1 ∘ weylS2)^[3] p = p := by
  rcases p with ⟨σ₁, σ₂⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [weylS1, weylS2, weylLongest, Prod.mk.injEq]; constructor <;> ring
  · simp only [weylS1, weylS2, weylLongest, Prod.mk.injEq]; constructor <;> ring
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Function.comp_apply,
      weylS1, weylS2, Prod.mk.injEq]
    constructor <;> ring

/-- Metaplectic scattering numerator argument `n s − n/2` of the order-`n` Kubota Eisenstein
scattering matrix `φ(s) = ξ_K(n s − n/2) / ξ_K(n s − n/2 + 1)`. -/
def kubotaArg (n s : ℝ) : ℝ := n * s - n / 2

/-- Triple of completed `ξ_K`-arguments `(n s₁ − n/2 + 1, n s₂ − n/2 + 1, n(s₁ + s₂) − n + 1)`
normalizing the `A₂` multiple Dirichlet series of order `n`. -/
def normalizingTriple (n : ℝ) (p : ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (n * p.1 - n / 2 + 1, n * p.2 - n / 2 + 1, n * (p.1 + p.2) - n + 1)

/-- **Scattering-argument duality.** Reflecting `s ↦ 1 − s` maps `1 − (n s − n/2)` identically to
`n s − n/2 + 1`, so `ξ_K(1 − z) = ξ_K(z)` converts the reflected normalizing factor into the
scattering denominator `ξ_K(n s − n/2 + 1)`. -/
theorem one_sub_kubotaArg_reflect (n s : ℝ) :
    1 - kubotaArg n (1 - s) = kubotaArg n s + 1 := by
  unfold kubotaArg
  ring

theorem normalizingTriple_weylS1 (n : ℝ) (p : ℝ × ℝ) :
    normalizingTriple n (weylS1 p) =
      (1 - kubotaArg n p.1, (normalizingTriple n p).2.2, (normalizingTriple n p).2.1) := by
  simp only [normalizingTriple, weylS1, kubotaArg, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

theorem normalizingTriple_weylS2 (n : ℝ) (p : ℝ × ℝ) :
    normalizingTriple n (weylS2 p) =
      ((normalizingTriple n p).2.2, 1 - kubotaArg n p.2, (normalizingTriple n p).1) := by
  simp only [normalizingTriple, weylS2, kubotaArg, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- Preimage cone `w⁻¹([1, ∞)²)` on which the `w`-transformed `A₂` series converges absolutely. -/
def weylCone (w : Fin 6) (p : ℝ × ℝ) : Prop :=
  1 ≤ (weylAct w p).1 ∧ 1 ≤ (weylAct w p).2

/-- **Empty chamber intersection on `(0, 1) × ℝ`.** None of the six `W(A₂)` absolute-convergence
cones intersects the open critical strip `0 < σ₁ < 1` at any `σ₂ ∈ ℝ`: evaluating at
`s₁ = (1 − δ)/2 ∈ (0, ½)` always requires two-variable Phragmén–Lindelöf interpolation across
cones. -/
theorem not_weylCone_interior_strip {σ₁ : ℝ} (h0 : 0 < σ₁) (h1 : σ₁ < 1) (σ₂ : ℝ) (w : Fin 6) :
    ¬ weylCone w (σ₁, σ₂) := by
  fin_cases w <;> simp only [weylCone, weylAct, weylS1, weylS2, weylLongest] <;>
    rintro ⟨ha, hb⟩ <;> linarith

/-- `W(A₂)`-orbit of the Kubota–Patterson determinant polar hyperplanes `s_i = ½ + 1/n`. -/
def kubotaPolarLocus (n : ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ w : Fin 6, (weylAct w p).1 = 1 / 2 + 1 / n ∨ (weylAct w p).2 = 1 / 2 + 1 / n

/-- Rightmost Kubota polar abscissa `½ + 1/n + δ/2` along the slice `s₁ = (1 − δ)/2`. -/
def kubotaRightmostPole (n δ : ℝ) : ℝ := 1 / 2 + 1 / n + δ / 2

/-- Along `s₁ = (1 − δ)/2` (`δ ≥ 0`, `n > 0`, `δ ≠ 2/n`), the `W(A₂)` Kubota polar hyperplanes
intersect `s₂` exclusively at `{½ + 1/n, ½ − 1/n, ½ + 1/n + δ/2, ½ − 1/n + δ/2}`, with attained
maximum `kubotaRightmostPole n δ = ½ + 1/n + δ/2`. -/
theorem kubotaPolarLocus_slice_iff {n δ : ℝ} (hn : 0 < n) (hδ : 0 ≤ δ) (hne : δ ≠ 2 / n)
    (s₂ : ℝ) :
    kubotaPolarLocus n ((1 - δ) / 2, s₂) ↔
      s₂ = 1 / 2 + 1 / n ∨ s₂ = 1 / 2 - 1 / n ∨
        s₂ = 1 / 2 + 1 / n + δ / 2 ∨ s₂ = 1 / 2 - 1 / n + δ / 2 := by
  have h1n : 0 < 1 / n := one_div_pos.mpr hn
  have h2n : 2 / n = 2 * (1 / n) := by ring
  have hne' : δ ≠ 2 * (1 / n) := h2n ▸ hne
  constructor
  · rintro ⟨w, hw⟩
    fin_cases w <;> simp only [weylAct, weylS1, weylS2, weylLongest] at hw
    · rcases hw with h | h
      · exfalso; linarith
      · exact Or.inl (by linarith)
    · rcases hw with h | h
      · exfalso; apply hne'; linarith
      · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · rcases hw with h | h
      · exact Or.inr (Or.inr (Or.inl (by linarith)))
      · exact Or.inr (Or.inl (by linarith))
    · rcases hw with h | h
      · exact Or.inr (Or.inr (Or.inr (by linarith)))
      · exfalso; linarith
    · rcases hw with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inr (Or.inr (by linarith)))
    · rcases hw with h | h
      · exact Or.inr (Or.inl (by linarith))
      · exfalso; apply hne'; linarith
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, Or.inr rfl⟩
    · exact ⟨2, Or.inr (by simp only [weylAct, weylS2]; ring)⟩
    · exact ⟨2, Or.inl (by simp only [weylAct, weylS2]; ring)⟩
    · exact ⟨3, Or.inl (by simp only [weylAct, weylS1, weylS2]; ring)⟩

theorem kubotaPolarLocus_le_rightmost {n δ s₂ : ℝ} (hn : 0 < n) (hδ : 0 ≤ δ) (hne : δ ≠ 2 / n)
    (hpole : kubotaPolarLocus n ((1 - δ) / 2, s₂)) :
    s₂ ≤ kubotaRightmostPole n δ := by
  have h1n : 0 < 1 / n := one_div_pos.mpr hn
  unfold kubotaRightmostPole
  rcases (kubotaPolarLocus_slice_iff hn hδ hne s₂).mp hpole with rfl | rfl | rfl | rfl <;>
    linarith

/-! ### Braid-invariant Stirling cocycle and exact two-variable `W(A₂)` convexity hull -/

/-- Accumulated Stirling vertical-growth log-cost along reduced words in `W(A₂)` for root
log-heights `(L₁, L₂, L₁₂)`. -/
def weylStirlingCocycle (L₁ L₂ L₁₂ : ℝ) : Fin 6 → ℝ × ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun p => (1 / 2 - p.1) * L₁
  | 2 => fun p => (1 / 2 - p.2) * L₂
  | 3 => fun p => (1 / 2 - p.2) * L₂ + (1 - p.1 - p.2) * L₁₂
  | 4 => fun p => (1 / 2 - p.1) * L₁ + (1 - p.1 - p.2) * L₁₂
  | 5 => fun p => (1 / 2 - p.1) * L₁ + (1 - p.1 - p.2) * L₁₂ + (1 / 2 - p.2) * L₂

/-- **Braid cocycle identity.** Accumulating single-reflection Stirling costs `(½ − a) L_a` along
`e → w₁ → w₂ w₁ → w₁ w₂ w₁` and along `e → w₂ → w₁ w₂ → w₂ w₁ w₂` produces identical expressions
at `w₀` for all `(L₁, L₂, L₁₂) ∈ ℝ³`. -/
theorem weylStirlingCocycle_braid (L₁ L₂ L₁₂ : ℝ) (p : ℝ × ℝ) :
    weylStirlingCocycle L₁ L₂ L₁₂ 1 p + (1 / 2 - (weylAct 1 p).2) * L₁₂ =
        weylStirlingCocycle L₁ L₂ L₁₂ 4 p ∧
      weylStirlingCocycle L₁ L₂ L₁₂ 2 p + (1 / 2 - (weylAct 2 p).1) * L₁₂ =
        weylStirlingCocycle L₁ L₂ L₁₂ 3 p ∧
      weylStirlingCocycle L₁ L₂ L₁₂ 4 p + (1 / 2 - (weylAct 4 p).1) * L₂ =
        weylStirlingCocycle L₁ L₂ L₁₂ 5 p ∧
      weylStirlingCocycle L₁ L₂ L₁₂ 3 p + (1 / 2 - (weylAct 3 p).2) * L₁ =
        weylStirlingCocycle L₁ L₂ L₁₂ 5 p := by
  simp only [weylStirlingCocycle, weylAct, weylS1, weylS2]
  exact ⟨by ring, by ring, by ring, by ring⟩

/-- Specialization `(L₁, L₂, L₁₂) = (0, 1, 1)` governing vertical growth `|Z(s₁, s₂)| ≪ T^{2 μ}`
over `ℚ(ω)` at fixed `|Im s₁| = O(1)` and `|Im s₂| = T → ∞`. -/
def weylConeCost (w : Fin 6) (p : ℝ × ℝ) : ℝ := weylStirlingCocycle 0 1 1 w p

/-- Exact two-variable `W(A₂)` convexity-hull exponent on `[0, 1] × ℝ`:
`max(0, 1 − (σ₁ + 2σ₂)/3, 3/2 − (2σ₁ + 4σ₂)/3, 3/2 − σ₁ − 2σ₂)`. -/
def weylA2Convexity (σ₁ σ₂ : ℝ) : ℝ :=
  max (max 0 (1 - (σ₁ + 2 * σ₂) / 3))
    (max (3 / 2 - (2 * σ₁ + 4 * σ₂) / 3) (3 / 2 - σ₁ - 2 * σ₂))

/-- On each of the six absolute-convergence cones `weylCone w`, `weylA2Convexity` is bounded above
by `weylConeCost w`. -/
theorem weylA2Convexity_le_weylConeCost (w : Fin 6) (p : ℝ × ℝ) (hc : weylCone w p) :
    weylA2Convexity p.1 p.2 ≤ weylConeCost w p := by
  rcases p with ⟨σ₁, σ₂⟩
  unfold weylA2Convexity weylConeCost
  fin_cases w <;>
    simp only [weylCone, weylAct, weylS1, weylS2, weylLongest, weylStirlingCocycle] at hc ⊢ <;>
    rcases hc with ⟨ha, hb⟩ <;>
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> linarith

/-- Joint convexity of `weylA2Convexity` over arbitrary finite convex combinations in `ℝ²`. -/
theorem weylA2Convexity_convex_sum {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (pts : ι → ℝ × ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (hsum : ∑ i ∈ s, lam i = 1) :
    weylA2Convexity (∑ i ∈ s, lam i * (pts i).1) (∑ i ∈ s, lam i * (pts i).2) ≤
      ∑ i ∈ s, lam i * weylA2Convexity (pts i).1 (pts i).2 := by
  set X := ∑ i ∈ s, lam i * (pts i).1
  set Y := ∑ i ∈ s, lam i * (pts i).2
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
  · refine Finset.sum_nonneg fun i hi => mul_nonneg (hlam i hi) ?_
    exact (le_max_left _ _).trans (le_max_left _ _)
  · have hlin : 1 - (X + 2 * Y) / 3 =
        ∑ i ∈ s, lam i * (1 - ((pts i).1 + 2 * (pts i).2) / 3) := by
      have h1 : ∑ i ∈ s, lam i * (1 - ((pts i).1 + 2 * (pts i).2) / 3) =
          (∑ i ∈ s, lam i) - (X + 2 * Y) / 3 := by
        have hcongr : ∀ i, lam i * (1 - ((pts i).1 + 2 * (pts i).2) / 3) =
            lam i - (lam i * (pts i).1) / 3 - 2 * ((lam i * (pts i).2) / 3) := fun _ => by ring
        simp_rw [hcongr, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div]
        dsimp only [X, Y]
        ring
      rw [h1, hsum]
    rw [hlin]
    refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hlam i hi)
    exact (le_max_right _ _).trans (le_max_left _ _)
  · have hlin : 3 / 2 - (2 * X + 4 * Y) / 3 =
        ∑ i ∈ s, lam i * (3 / 2 - (2 * (pts i).1 + 4 * (pts i).2) / 3) := by
      have h1 : ∑ i ∈ s, lam i * (3 / 2 - (2 * (pts i).1 + 4 * (pts i).2) / 3) =
          3 / 2 * (∑ i ∈ s, lam i) - (2 * X + 4 * Y) / 3 := by
        have hcongr : ∀ i, lam i * (3 / 2 - (2 * (pts i).1 + 4 * (pts i).2) / 3) =
            3 / 2 * lam i - 2 * ((lam i * (pts i).1) / 3) - 4 * ((lam i * (pts i).2) / 3) :=
          fun _ => by ring
        simp_rw [hcongr, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div]
        dsimp only [X, Y]
        ring
      rw [h1, hsum, mul_one]
    rw [hlin]
    refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hlam i hi)
    exact (le_max_left _ _).trans (le_max_right _ _)
  · have hlin : 3 / 2 - X - 2 * Y =
        ∑ i ∈ s, lam i * (3 / 2 - (pts i).1 - 2 * (pts i).2) := by
      have h1 : ∑ i ∈ s, lam i * (3 / 2 - (pts i).1 - 2 * (pts i).2) =
          3 / 2 * (∑ i ∈ s, lam i) - X - 2 * Y := by
        have hcongr : ∀ i, lam i * (3 / 2 - (pts i).1 - 2 * (pts i).2) =
            3 / 2 * lam i - lam i * (pts i).1 - 2 * (lam i * (pts i).2) := fun _ => by ring
        simp_rw [hcongr, Finset.sum_sub_distrib, ← Finset.mul_sum]
        rfl
      rw [h1, hsum, mul_one]
    rw [hlin]
    refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hlam i hi)
    exact (le_max_right _ _).trans (le_max_right _ _)

/-- **Optimality of the two-variable `W(A₂)` convexity envelope.** Every convex combination of
points chosen from the six `W(A₂)` absolute-convergence cones has interpolated Stirling growth
exponent at least `weylA2Convexity`. -/
theorem weylA2Convexity_le_convex_cone_sum (lam : Fin 6 → ℝ) (pts : Fin 6 → ℝ × ℝ)
    (hlam : ∀ w, 0 ≤ lam w) (hsum : ∑ w : Fin 6, lam w = 1)
    (hcone : ∀ w, weylCone w (pts w)) :
    weylA2Convexity (∑ w : Fin 6, lam w * (pts w).1) (∑ w : Fin 6, lam w * (pts w).2) ≤
      ∑ w : Fin 6, lam w * weylConeCost w (pts w) := by
  refine (weylA2Convexity_convex_sum Finset.univ lam pts (fun w _ => hlam w) hsum).trans ?_
  exact Finset.sum_le_sum fun w _ =>
    mul_le_mul_of_nonneg_left (weylA2Convexity_le_weylConeCost w (pts w) (hcone w)) (hlam w)

/-- Canonical base vertices of the six `W(A₂)` absolute-convergence cones. -/
def weylConeVertex : Fin 6 → ℝ × ℝ
  | 0 => (1, 1)
  | 1 => (0, 3 / 2)
  | 2 => (3 / 2, 0)
  | 3 => (1, -1 / 2)
  | 4 => (-1 / 2, 1)
  | 5 => (0, 0)

theorem weylCone_weylConeVertex (w : Fin 6) : weylCone w (weylConeVertex w) := by
  fin_cases w <;> norm_num [weylCone, weylConeVertex, weylAct, weylS1, weylS2, weylLongest]

/-- **Exact attainability of `weylA2Convexity` across `[0, 1] × ℝ`.** Every `(σ₁, σ₂) ∈ [0, 1] × ℝ`
is an explicit convex combination of points in the six `W(A₂)` cones whose weighted Stirling cost
equals `weylA2Convexity σ₁ σ₂`. -/
theorem exists_convex_cone_attaining_weylA2Convexity {σ₁ : ℝ} (h0 : 0 ≤ σ₁) (h1 : σ₁ ≤ 1)
    (σ₂ : ℝ) :
    ∃ (lam : Fin 6 → ℝ) (pts : Fin 6 → ℝ × ℝ),
      (∀ w, 0 ≤ lam w) ∧
      ∑ w : Fin 6, lam w = 1 ∧
      (∀ w, weylCone w (pts w)) ∧
      ∑ w : Fin 6, lam w * (pts w).1 = σ₁ ∧
      ∑ w : Fin 6, lam w * (pts w).2 = σ₂ ∧
      ∑ w : Fin 6, lam w * weylConeCost w (pts w) = weylA2Convexity σ₁ σ₂ := by
  rcases le_total (3 / 2 - σ₁ / 2) σ₂ with htop | hbelow1
  · set r : ℝ := σ₂ - (3 / 2 - σ₁ / 2)
    have hr : 0 ≤ r := sub_nonneg.mpr htop
    let lam : Fin 6 → ℝ := fun
      | 0 => σ₁ | 1 => 1 - σ₁ | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0
    let pts : Fin 6 → ℝ × ℝ := fun
      | 0 => (1, 1 + r) | 1 => (0, 3 / 2 + r) | 2 => (3 / 2, 0)
      | 3 => (1, -1 / 2) | 4 => (-1 / 2, 1) | 5 => (0, 0)
    have hval : weylA2Convexity σ₁ σ₂ = 0 :=
      le_antisymm (max_le (max_le le_rfl (by linarith)) (max_le (by linarith) (by linarith)))
        ((le_max_left _ _).trans (le_max_left _ _))
    refine ⟨lam, pts, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w; fin_cases w <;> simp only [lam] <;> linarith
    · rw [Fin.sum_univ_six]; simp only [lam]; ring
    · intro w
      fin_cases w
      · simp only [weylCone, pts, weylAct]; exact ⟨le_rfl, by linarith [hr]⟩
      · simp only [weylCone, pts, weylAct, weylS1]; exact ⟨le_rfl, by linarith [hr]⟩
      · norm_num [weylCone, pts, weylAct, weylS2]
      · norm_num [weylCone, pts, weylAct, weylS1, weylS2]
      · norm_num [weylCone, pts, weylAct, weylS1, weylS2]
      · norm_num [weylCone, pts, weylAct, weylLongest]
    · rw [Fin.sum_univ_six]; simp only [lam, pts]; ring
    · rw [Fin.sum_univ_six]; simp only [lam, pts, r]; ring
    · rw [hval, Fin.sum_univ_six]
      simp only [lam, pts, weylConeCost, weylStirlingCocycle]; ring
  · rcases le_total (3 / 4 - σ₁ / 2) σ₂ with hmid1 | hbelow2
    · set t : ℝ := 2 - (2 * σ₁ + 4 * σ₂) / 3
      have ht0 : 0 ≤ t := by simp only [t]; linarith
      have ht1 : t ≤ 1 := by simp only [t]; linarith
      let lam : Fin 6 → ℝ := fun
        | 0 => (1 - t) * σ₁
        | 1 => (1 - t) * (1 - σ₁)
        | 2 => t * ((2 * σ₁ + 1) / 4)
        | 3 => 0
        | 4 => t * ((3 - 2 * σ₁) / 4)
        | 5 => 0
      have hval : weylA2Convexity σ₁ σ₂ = 1 - (σ₁ + 2 * σ₂) / 3 :=
        le_antisymm (max_le (max_le (by linarith) le_rfl) (max_le (by linarith) (by linarith)))
          ((le_max_right _ _).trans (le_max_left _ _))
      refine ⟨lam, weylConeVertex, ?_, ?_, weylCone_weylConeVertex, ?_, ?_, ?_⟩
      · intro w
        fin_cases w <;> simp only [lam]
        · exact mul_nonneg (by linarith [ht1]) h0
        · exact mul_nonneg (by linarith [ht1]) (by linarith [h1])
        · exact mul_nonneg ht0 (by linarith [h0])
        · exact le_rfl
        · exact mul_nonneg ht0 (by linarith [h1])
        · exact le_rfl
      · rw [Fin.sum_univ_six]; simp only [lam]; ring
      · rw [Fin.sum_univ_six]; simp only [lam, weylConeVertex]; ring
      · rw [Fin.sum_univ_six]; simp only [lam, weylConeVertex, t]; ring
      · rw [hval, Fin.sum_univ_six]
        simp only [lam, weylConeVertex, weylConeCost, weylStirlingCocycle, t]; ring
    · rcases le_total (-σ₁ / 2) σ₂ with hmid2 | hbot
      · set s : ℝ := 1 - (2 * σ₁ + 4 * σ₂) / 3
        have hs0 : 0 ≤ s := by simp only [s]; linarith
        have hs1 : s ≤ 1 := by simp only [s]; linarith
        let lam : Fin 6 → ℝ := fun
          | 0 => 0
          | 1 => 0
          | 2 => (1 - s) * ((2 * σ₁ + 1) / 4)
          | 3 => s * σ₁
          | 4 => (1 - s) * ((3 - 2 * σ₁) / 4)
          | 5 => s * (1 - σ₁)
        have hval : weylA2Convexity σ₁ σ₂ = 3 / 2 - (2 * σ₁ + 4 * σ₂) / 3 :=
          le_antisymm (max_le (max_le (by linarith) (by linarith)) (max_le le_rfl (by linarith)))
            ((le_max_left _ _).trans (le_max_right _ _))
        refine ⟨lam, weylConeVertex, ?_, ?_, weylCone_weylConeVertex, ?_, ?_, ?_⟩
        · intro w
          fin_cases w <;> simp only [lam]
          · exact le_rfl
          · exact le_rfl
          · exact mul_nonneg (by linarith [hs1]) (by linarith [h0])
          · exact mul_nonneg hs0 h0
          · exact mul_nonneg (by linarith [hs1]) (by linarith [h1])
          · exact mul_nonneg hs0 (by linarith [h1])
        · rw [Fin.sum_univ_six]; simp only [lam]; ring
        · rw [Fin.sum_univ_six]; simp only [lam, weylConeVertex]; ring
        · rw [Fin.sum_univ_six]; simp only [lam, weylConeVertex, s]; ring
        · rw [hval, Fin.sum_univ_six]
          simp only [lam, weylConeVertex, weylConeCost, weylStirlingCocycle, s]; ring
      · set r : ℝ := -σ₁ / 2 - σ₂
        have hr : 0 ≤ r := sub_nonneg.mpr hbot
        let lam : Fin 6 → ℝ := fun
          | 0 => 0 | 1 => 0 | 2 => 0 | 3 => σ₁ | 4 => 0 | 5 => 1 - σ₁
        let pts : Fin 6 → ℝ × ℝ := fun
          | 0 => (1, 1) | 1 => (0, 3 / 2) | 2 => (3 / 2, 0)
          | 3 => (1, -1 / 2 - r) | 4 => (-1 / 2, 1) | 5 => (0, -r)
        have hval : weylA2Convexity σ₁ σ₂ = 3 / 2 - σ₁ - 2 * σ₂ :=
          le_antisymm (max_le (max_le (by linarith) (by linarith)) (max_le (by linarith) le_rfl))
            ((le_max_right _ _).trans (le_max_right _ _))
        refine ⟨lam, pts, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro w; fin_cases w <;> simp only [lam] <;> linarith
        · rw [Fin.sum_univ_six]; simp only [lam]; ring
        · intro w
          fin_cases w
          · norm_num [weylCone, pts, weylAct]
          · norm_num [weylCone, pts, weylAct, weylS1]
          · norm_num [weylCone, pts, weylAct, weylS2]
          · simp only [weylCone, pts, weylAct, weylS1, weylS2]; constructor <;> linarith [hr]
          · norm_num [weylCone, pts, weylAct, weylS1, weylS2]
          · simp only [weylCone, pts, weylAct, weylLongest]; constructor <;> linarith [hr]
        · rw [Fin.sum_univ_six]; simp only [lam, pts]; ring
        · rw [Fin.sum_univ_six]; simp only [lam, pts, r]; ring
        · rw [hval, Fin.sum_univ_six]
          simp only [lam, pts, weylConeCost, weylStirlingCocycle, r]; ring

/-! ### Sharp-truncation Perron plateau and binding-bin exclusion (First Lemma & Subpart (a)) -/

/-- Right edge `(5 + δ)/4 = 3/2 − w₀/2` at which `weylA2Convexity((1 − δ)/2, σ₂)` vanishes. -/
theorem weylA2Convexity_slice_eq_zero_iff (δ σ₂ : ℝ) :
    weylA2Convexity ((1 - δ) / 2) σ₂ = 0 ↔ (5 + δ) / 4 ≤ σ₂ := by
  unfold weylA2Convexity
  constructor
  · intro h0
    have hle : 1 - (((1 - δ) / 2) + 2 * σ₂) / 3 ≤ 0 := by
      calc 1 - (((1 - δ) / 2) + 2 * σ₂) / 3 ≤
            max (max 0 (1 - (((1 - δ) / 2) + 2 * σ₂) / 3))
              (max (3 / 2 - (2 * ((1 - δ) / 2) + 4 * σ₂) / 3)
                (3 / 2 - ((1 - δ) / 2) - 2 * σ₂)) :=
          (le_max_right _ _).trans (le_max_left _ _)
        _ = 0 := h0
    linarith
  · intro hge
    exact le_antisymm (max_le (max_le le_rfl (by linarith)) (max_le (by linarith) (by linarith)))
      ((le_max_left _ _).trans (le_max_left _ _))

/-- Sharp-truncation Perron contour exponent `(σ₂ + 2 μ A₀)/(1 + 2 μ)` along `s₁ = (1 − δ)/2` with
right-edge abscissa `A₀ = (5 + δ)/4` and `μ = weylA2Convexity((1 − δ)/2, σ₂)`. -/
def perronSharpExponent (δ σ₂ : ℝ) : ℝ :=
  (σ₂ + 2 * weylA2Convexity ((1 - δ) / 2) σ₂ * ((5 + δ) / 4)) /
    (1 + 2 * weylA2Convexity ((1 - δ) / 2) σ₂)

/-- **Global lower bound for the sharp-truncation `W(A₂)` Perron contour.** Across all
`δ, σ₂ ∈ ℝ`, `perronSharpExponent δ σ₂ ≥ 7/8 + δ/4`. -/
theorem perronSharpExponent_ge (δ σ₂ : ℝ) :
    7 / 8 + δ / 4 ≤ perronSharpExponent δ σ₂ := by
  set μ := weylA2Convexity ((1 - δ) / 2) σ₂
  have hμ0 : 0 ≤ μ := (le_max_left _ _).trans (le_max_left _ _)
  have hμ_piece : 3 / 2 - (2 * ((1 - δ) / 2) + 4 * σ₂) / 3 ≤ μ :=
    (le_max_left _ _).trans (le_max_right _ _)
  unfold perronSharpExponent
  rw [le_div_iff₀ (by linarith : 0 < 1 + 2 * μ)]
  linarith

/-- **Exact Perron plateau.** Throughout `σ₂ ∈ [−(1 − δ)/4, (2 + δ)/4]`, `perronSharpExponent δ σ₂`
is identically constant and equal to `7/8 + δ/4`. -/
theorem perronSharpExponent_eq_plateau (δ σ₂ : ℝ)
    (hlo : -(1 - δ) / 4 ≤ σ₂) (hhi : σ₂ ≤ (2 + δ) / 4) :
    perronSharpExponent δ σ₂ = 7 / 8 + δ / 4 := by
  have hμ : weylA2Convexity ((1 - δ) / 2) σ₂ = 3 / 2 - (2 * ((1 - δ) / 2) + 4 * σ₂) / 3 :=
    le_antisymm (max_le (max_le (by linarith) (by linarith)) (max_le le_rfl (by linarith)))
      ((le_max_left _ _).trans (le_max_right _ _))
  unfold perronSharpExponent
  rw [hμ, div_eq_iff (by linarith)]
  ring

/-- **First Lemma & Subpart (a): binding-bin `A₂` specialization chain.** At the binding bin
`δ = 79/204` (`s₁ = 125/408`), the square-row cubic support `1/2` falls strictly short of
`rowCount(79/204, ½) = 21766/32589`, while every two-variable `A₂` continuation exponent
(`793/816 < 1 < 419/408 < 487/408 < 1099/816`) strictly exceeds both
`rowCount(79/204, ½) + δ/2 = 224609/260712` and the `7/8` threshold `4571/5304`, making the
published high exponent strictly positive. -/
theorem binding_bin_a2_specialization_chain :
    (1 / 2 : ℝ) < rowCount (79 / 204) (1 / 2) ∧
      (1 - (79 / 204 : ℝ)) + (79 / 204) / 2 = 329 / 408 ∧
      rowCount (79 / 204) (1 / 2) + (79 / 204) / 2 = 224609 / 260712 ∧
      (∀ R : ℝ,
        endpointExponent (17 / 48) (23 / 48) (1 / 6) (7 / 8) (79 / 204) (79 / 408) R ≤ 0 ↔
          R + (79 / 204) / 2 ≤ 4571 / 5304) ∧
      (∀ σ₂ : ℝ, 793 / 816 ≤ perronSharpExponent (79 / 204) σ₂) ∧
      perronSharpExponent (79 / 204) (1 / 2) = 793 / 816 ∧
      kubotaRightmostPole 3 (79 / 204) = 419 / 408 ∧
      (5 + (79 / 204 : ℝ)) / 4 = 1099 / 816 ∧
      (329 / 408 : ℝ) < 224609 / 260712 ∧
      (224609 / 260712 : ℝ) < 4571 / 5304 ∧
      (4571 / 5304 : ℝ) < 793 / 816 ∧
      (793 / 816 : ℝ) < 1 ∧
      (1 : ℝ) < 419 / 408 ∧
      (419 / 408 : ℝ) < 487 / 408 ∧
      (487 / 408 : ℝ) < 1099 / 816 ∧
      (∀ R : ℝ, 793 / 816 ≤ R + (79 / 204) / 2 →
        0 < endpointExponent (17 / 48) (23 / 48) (1 / 6) (7 / 8) (79 / 204) (79 / 408) R) := by
  rw [rowCount_binding]
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  · intro R
    unfold endpointExponent
    constructor <;> intro h <;> linarith
  · intro σ₂
    have h := perronSharpExponent_ge (79 / 204) σ₂
    linarith
  · have h := perronSharpExponent_eq_plateau (79 / 204) (1 / 2) (by norm_num) (by norm_num)
    linarith
  · norm_num [kubotaRightmostPole]
  · intro R hR
    unfold endpointExponent
    linarith

/-! ### Universal global minimax half-plane laws and rank-two rejection boundaries -/

/-- High-side half-plane boundary in bin `δ` with prime amplitude `q` and row count `R`, so that
`endpointExponent lx ly ℓ σ₀ δ q R = highBoundary lx ly ℓ δ q R − σ₀`. -/
def highBoundary (lx ly ℓ δ q R : ℝ) : ℝ :=
  (1 + δ) * (1 - ly) / 2 - ℓ / 2 + q * ℓ + (1 - lx + ℓ) * (R + δ / 2 - 1 / 6)

theorem endpointExponent_eq_highBoundary_sub (lx ly ℓ σ₀ δ q R : ℝ) :
    endpointExponent lx ly ℓ σ₀ δ q R = highBoundary lx ly ℓ δ q R - σ₀ := by
  unfold endpointExponent highBoundary
  ring

/-- Four linear lower faces of `lowBoundaryGen` across all `(lx, ly, ℓ) ∈ ℝ³`. -/
private theorem lowBoundaryGen_linear_faces (lx ly ℓ : ℝ) :
    5 / 6 + lx / 6 - ℓ / 6 ≤ lowBoundaryGen lx ly ℓ ∧
      5 / 6 + (lx + ly) / 12 - ℓ / 6 ≤ lowBoundaryGen lx ly ℓ ∧
      1 / 3 + 2 * lx / 3 + ly / 2 + ℓ / 3 ≤ lowBoundaryGen lx ly ℓ ∧
      1 / 3 + 7 * (lx + ly) / 12 + ℓ / 3 ≤ lowBoundaryGen lx ly ℓ := by
  unfold lowBoundaryGen
  have hν0 : (0 : ℝ) ≤ max 0 (ly - lx) := le_max_left _ _
  have hν1 : ly - lx ≤ max 0 (ly - lx) := le_max_right _ _
  have hμ0 : (0 : ℝ) ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hμ1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Universal balanced-spillover global minimax law.** For every `δ ≥ 0`, every `R ≥ 2/3`, and
every `(lx, ly, ℓ) ∈ ℝ³` without sign or regime restrictions,
`max(lowBoundaryGen lx ly ℓ, highBoundary lx ly ℓ δ (δ/2) R) ≥ 1 − 2/(3(6R + 6δ − 1))`. -/
theorem universal_balanced_minimax_le {δ R : ℝ} (hδ : 0 ≤ δ) (hR : 2 / 3 ≤ R) (lx ly ℓ : ℝ) :
    1 - 2 / (3 * (6 * R + 6 * δ - 1)) ≤
      max (lowBoundaryGen lx ly ℓ) (highBoundary lx ly ℓ δ (δ / 2) R) := by
  set M := max (lowBoundaryGen lx ly ℓ) (highBoundary lx ly ℓ δ (δ / 2) R)
  set D : ℝ := 6 * R + 6 * δ - 1
  have hD : 0 < 3 * D := by simp only [D]; linarith
  obtain ⟨hf1, hf2, -, hf4⟩ := lowBoundaryGen_linear_faces lx ly ℓ
  have hL1 : 5 / 6 + lx / 6 - ℓ / 6 ≤ M := hf1.trans (le_max_left _ _)
  have hL2 : 5 / 6 + (lx + ly) / 12 - ℓ / 6 ≤ M := hf2.trans (le_max_left _ _)
  have hL4 : 1 / 3 + 7 * (lx + ly) / 12 + ℓ / 3 ≤ M := hf4.trans (le_max_left _ _)
  have hH : highBoundary lx ly ℓ δ (δ / 2) R ≤ M := le_max_right _ _
  have hm1 := mul_le_mul_of_nonneg_left hL1 (by linarith : 0 ≤ 6 * (3 * R - 2))
  have hm2 := mul_le_mul_of_nonneg_left hL2 (by linarith : 0 ≤ 2 * (9 * δ + 2))
  have hm4 := mul_le_mul_of_nonneg_left hL4 (by norm_num : (0 : ℝ) ≤ 2)
  have hmH := mul_le_mul_of_nonneg_left hH (by norm_num : (0 : ℝ) ≤ 3)
  have hid : 6 * (3 * R - 2) * (5 / 6 + lx / 6 - ℓ / 6) +
        2 * (9 * δ + 2) * (5 / 6 + (lx + ly) / 12 - ℓ / 6) +
        2 * (1 / 3 + 7 * (lx + ly) / 12 + ℓ / 3) +
        3 * highBoundary lx ly ℓ δ (δ / 2) R = 3 * D - 2 := by
    unfold highBoundary
    simp only [D]
    ring
  have hw : (6 * (3 * R - 2) + 2 * (9 * δ + 2) + 2 + 3) * M = 3 * D * M := by
    simp only [D]; ring
  have hbound : 3 * D - 2 ≤ 3 * D * M := by linarith
  have hrew : 1 - 2 / (3 * D) = (3 * D - 2) / (3 * D) := by
    symm
    rw [sub_div, div_self hD.ne']
  rw [hrew, div_le_iff₀ hD]
  linarith

/-- Attainment of `1 − 2/(3(6R + 6δ − 1))` on the balanced edge `lx = ly = (1 − ℓ_*)/2` with
`ℓ_* = (3 − 2R − 2δ)/(6R + 6δ − 1) ≥ 0` whenever `R + δ ≤ 3/2`. -/
theorem universal_balanced_minimax_attained {δ R : ℝ} (hδ : 0 ≤ δ) (hR : 2 / 3 ≤ R)
    (hsum : R + δ ≤ 3 / 2) :
    let D := 6 * R + 6 * δ - 1
    let ℓs := (3 - 2 * R - 2 * δ) / D
    let xs := (1 - ℓs) / 2
    0 ≤ ℓs ∧
      lowBoundaryGen xs xs ℓs = 1 - 2 / (3 * D) ∧
      highBoundary xs xs ℓs δ (δ / 2) R = 1 - 2 / (3 * D) := by
  dsimp only
  set D : ℝ := 6 * R + 6 * δ - 1
  have hDdef : D = 6 * R + 6 * δ - 1 := rfl
  have hDpos : 0 < D := by simp only [D]; linarith [hδ, hR]
  have hDne : D ≠ 0 := hDpos.ne'
  set ℓs : ℝ := (3 - 2 * R - 2 * δ) / D
  have hℓs : 0 ≤ ℓs := div_nonneg (by linarith [hsum]) hDpos.le
  have hℓD : ℓs * D = 3 - 2 * R - 2 * δ := div_mul_cancel₀ _ hDne
  have h2 : 2 / (3 * D) * (12 * D) = 8 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hDne]
    norm_num
  have h12D : 12 * D ≠ 0 := mul_ne_zero (by norm_num) hDne
  have hedge : (1 - ℓs) / 2 + (1 - ℓs) / 2 + ℓs - 1 = 0 := by ring
  refine ⟨hℓs, ?_, ?_⟩
  · unfold lowBoundaryGen
    rw [sub_self, max_self, hedge, max_self]
    apply mul_right_cancel₀ h12D
    linear_combination -3 * hℓD - hDdef + h2
  · unfold highBoundary
    apply mul_right_cancel₀ h12D
    linear_combination (18 * R + 18 * δ - 6) * hℓD + (6 * R + 6 * δ - 10) * hDdef + h2

/-- **Universal unslotted-spillover global minimax law.** For `2/3 ≤ R ≤ (δ + 5)/6`,
`4/9 ≤ R + δ`, and any `(lx, ly, ℓ) ∈ ℝ³` with `0 ≤ ℓ`,
`max(lowBoundaryGen lx ly ℓ, highBoundary lx ly ℓ δ (δ/2) R) ≥ (3R + 3δ + 1)/(2R + 2δ + 3)`. -/
theorem universal_unslotted_minimax_le {δ R : ℝ} (hR0 : 2 / 3 ≤ R) (hR1 : R ≤ (δ + 5) / 6)
    (hsum : 4 / 9 ≤ R + δ) {lx ly ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    (3 * R + 3 * δ + 1) / (2 * R + 2 * δ + 3) ≤
      max (lowBoundaryGen lx ly ℓ) (highBoundary lx ly ℓ δ (δ / 2) R) := by
  set M := max (lowBoundaryGen lx ly ℓ) (highBoundary lx ly ℓ δ (δ / 2) R)
  set D₂ : ℝ := 2 * R + 2 * δ + 3
  have hD₂ : 0 < D₂ := by simp only [D₂]; linarith [hsum]
  obtain ⟨-, -, hf3, hf4⟩ := lowBoundaryGen_linear_faces lx ly ℓ
  have hL3 : 1 / 3 + 2 * lx / 3 + ly / 2 + ℓ / 3 ≤ M := hf3.trans (le_max_left _ _)
  have hL4 : 1 / 3 + 7 * (lx + ly) / 12 + ℓ / 3 ≤ M := hf4.trans (le_max_left _ _)
  have hH : highBoundary lx ly ℓ δ (δ / 2) R ≤ M := le_max_right _ _
  have hm3 := mul_le_mul_of_nonneg_left hL3 (by linarith [hR0] : 0 ≤ 14 * (3 * R - 2))
  have hm4 := mul_le_mul_of_nonneg_left hL4 (by linarith [hR1] : 0 ≤ 6 * (δ + 5 - 6 * R))
  have hmH := mul_le_mul_of_nonneg_left hH (by norm_num : (0 : ℝ) ≤ 7)
  have hid : 14 * (3 * R - 2) * (1 / 3 + 2 * lx / 3 + ly / 2 + ℓ / 3) +
        6 * (δ + 5 - 6 * R) * (1 / 3 + 7 * (lx + ly) / 12 + ℓ / 3) +
        7 * highBoundary lx ly ℓ δ (δ / 2) R =
      3 * (3 * R + 3 * δ + 1) + (9 * R + 9 * δ - 4) * ℓ := by
    unfold highBoundary
    ring
  have hw : (14 * (3 * R - 2) + 6 * (δ + 5 - 6 * R) + 7) * M = 3 * D₂ * M := by
    simp only [D₂]; ring
  have hℓ_term : 0 ≤ (9 * R + 9 * δ - 4) * ℓ := mul_nonneg (by linarith [hsum]) hℓ
  have hbound : 3 * (3 * R + 3 * δ + 1) ≤ 3 * D₂ * M := by linarith
  rw [div_le_iff₀ hD₂]
  linarith

/-- Attainment of `(3R + 3δ + 1)/(2R + 2δ + 3)` at `(2(R + δ)/(2R + 2δ + 3),
2(R + δ)/(2R + 2δ + 3), 0)` whenever `3/2 ≤ R + δ`. -/
theorem universal_unslotted_minimax_attained {δ R : ℝ} (hsum : 3 / 2 ≤ R + δ) :
    let D₂ := 2 * R + 2 * δ + 3
    let xs := 2 * (R + δ) / D₂
    lowBoundaryGen xs xs 0 = (3 * R + 3 * δ + 1) / D₂ ∧
      highBoundary xs xs 0 δ (δ / 2) R = (3 * R + 3 * δ + 1) / D₂ := by
  dsimp only
  set D₂ : ℝ := 2 * R + 2 * δ + 3
  have hD₂pos : 0 < D₂ := by simp only [D₂]; linarith
  have hD₂ne : D₂ ≠ 0 := hD₂pos.ne'
  set xs : ℝ := 2 * (R + δ) / D₂
  have hdual : 0 ≤ xs + xs + 0 - 1 := by
    have heq : xs + xs + 0 - 1 = (2 * R + 2 * δ - 3) / D₂ := by
      simp only [xs, D₂]; field_simp [hD₂ne]; ring
    rw [heq]
    exact div_nonneg (by linarith) hD₂pos.le
  refine ⟨?_, ?_⟩
  · unfold lowBoundaryGen
    rw [sub_self, max_self, max_eq_right hdual]
    simp only [xs, D₂]
    field_simp [hD₂ne]
    ring
  · unfold highBoundary
    simp only [xs, D₂]
    field_simp [hD₂ne]
    ring

/-- **Rejection Test (§2.5): exact global minimax boundary exponents for all rank-two `A₂`
specializations.** Across all geometries, norm-bound continuation (`R = 1`) collapses to `σ₀ = 1`
at `δ = 1` (`ℓ ≥ 0`, no zero-free half-plane `< 1`) and `σ₀ = 679/747` on `δ = 79/204` alone; the
two-variable `W(A₂)` convexity norm bound (`R = 941/816`), cubic Kubota pole (`R = 5/6`),
principal `L`-pole (`R = 329/408`), and sharp-truncation Perron minimum (`R = 635/816`) have exact
global minimax half-plane boundaries `1474/1599`, `577/645` (`39/40` at `δ = 1`), `1121/1257`, and
`2173/2445`, every one strictly greater than `7/8`. -/
theorem rank_two_rejection_boundary_exponents :
    (∀ lx ly ℓ : ℝ, 0 ≤ ℓ →
      1 ≤ max (lowBoundaryGen lx ly ℓ) (highBoundary lx ly ℓ 1 (1 / 2) 1)) ∧
    max (lowBoundaryGen (4 / 7) (4 / 7) 0) (highBoundary (4 / 7) (4 / 7) 0 1 (1 / 2) 1) = 1 ∧
    (∀ lx ly ℓ : ℝ,
      679 / 747 ≤
        max (lowBoundaryGen lx ly ℓ) (highBoundary lx ly ℓ (79 / 204) (79 / 408) 1)) ∧
    (∀ lx ly ℓ : ℝ, 0 ≤ ℓ →
      1474 / 1599 ≤
        max (lowBoundaryGen lx ly ℓ) (highBoundary lx ly ℓ (79 / 204) (79 / 408) (941 / 816))) ∧
    max (lowBoundaryGen (849 / 1599) (750 / 1599) 0)
        (highBoundary (849 / 1599) (750 / 1599) 0 (79 / 204) (79 / 408) (941 / 816)) =
      1474 / 1599 ∧
    (∀ lx ly ℓ : ℝ,
      577 / 645 ≤
        max (lowBoundaryGen lx ly ℓ) (highBoundary lx ly ℓ (79 / 204) (79 / 408) (5 / 6))) ∧
    (∀ lx ly ℓ : ℝ, 0 ≤ ℓ →
      39 / 40 ≤ max (lowBoundaryGen lx ly ℓ) (highBoundary lx ly ℓ 1 (1 / 2) (5 / 6))) ∧
    max (lowBoundaryGen (11 / 20) (11 / 20) 0)
        (highBoundary (11 / 20) (11 / 20) 0 1 (1 / 2) (5 / 6)) = 39 / 40 ∧
    (∀ lx ly ℓ : ℝ,
      1121 / 1257 ≤
        max (lowBoundaryGen lx ly ℓ) (highBoundary lx ly ℓ (79 / 204) (79 / 408) (329 / 408))) ∧
    (∀ lx ly ℓ : ℝ,
      2173 / 2445 ≤
        max (lowBoundaryGen lx ly ℓ) (highBoundary lx ly ℓ (79 / 204) (79 / 408) (635 / 816))) ∧
    (7 / 8 : ℝ) < 2173 / 2445 ∧
    (2173 / 2445 : ℝ) < 1121 / 1257 ∧
    (1121 / 1257 : ℝ) < 577 / 645 ∧
    (577 / 645 : ℝ) < 679 / 747 ∧
    (679 / 747 : ℝ) < 1474 / 1599 ∧
    (1474 / 1599 : ℝ) < 39 / 40 ∧
    (39 / 40 : ℝ) < 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · intro lx ly ℓ hℓ
    have h := universal_unslotted_minimax_le (δ := 1) (R := 1)
      (by norm_num) (by norm_num) (by norm_num) (lx := lx) (ly := ly) hℓ
    linarith
  · norm_num [lowBoundaryGen, highBoundary]
  · intro lx ly ℓ
    have h := universal_balanced_minimax_le (δ := 79 / 204) (R := 1)
      (by norm_num) (by norm_num) lx ly ℓ
    linarith
  · intro lx ly ℓ hℓ
    set M := max (lowBoundaryGen lx ly ℓ) (highBoundary lx ly ℓ (79 / 204) (79 / 408) (941 / 816))
    obtain ⟨hf1, -, hf3, -⟩ := lowBoundaryGen_linear_faces lx ly ℓ
    have hL1 : 5 / 6 + lx / 6 - ℓ / 6 ≤ M := hf1.trans (le_max_left _ _)
    have hL3 : 1 / 3 + 2 * lx / 3 + ly / 2 + ℓ / 3 ≤ M := hf3.trans (le_max_left _ _)
    have hH : highBoundary lx ly ℓ (79 / 204) (79 / 408) (941 / 816) ≤ M := le_max_right _ _
    have hid : 625 * (5 / 6 + lx / 6 - ℓ / 6) +
          566 * (1 / 3 + 2 * lx / 3 + ly / 2 + ℓ / 3) +
          408 * highBoundary lx ly ℓ (79 / 204) (79 / 408) (941 / 816) =
        1474 + 441 * ℓ := by
      unfold highBoundary
      ring
    linarith
  · norm_num [lowBoundaryGen, highBoundary]
  · intro lx ly ℓ
    have h := universal_balanced_minimax_le (δ := 79 / 204) (R := 5 / 6)
      (by norm_num) (by norm_num) lx ly ℓ
    linarith
  · intro lx ly ℓ hℓ
    have h := universal_unslotted_minimax_le (δ := 1) (R := 5 / 6)
      (by norm_num) (by norm_num) (by norm_num) (lx := lx) (ly := ly) hℓ
    linarith
  · norm_num [lowBoundaryGen, highBoundary]
  · intro lx ly ℓ
    have h := universal_balanced_minimax_le (δ := 79 / 204) (R := 329 / 408)
      (by norm_num) (by norm_num) lx ly ℓ
    linarith
  · intro lx ly ℓ
    have h := universal_balanced_minimax_le (δ := 79 / 204) (R := 635 / 816)
      (by norm_num) (by norm_num) lx ly ℓ
    linarith

/-! ### Subparts (b) and (c): conductor doubling, Kubota–signed-Gram coincidence, payoff ladder -/

/-- **Subpart (b): squaring a linear row sum breaks `W(A₂)` finiteness via conductor doubling.**
Linear `A₂` reflection-summation has `(κ, κ') = (1, 1)` (`trace = −1`, elliptic order `3`),
whereas squaring `|A(u)|²` doubles `(κ, κ')` to `(2, 2)` (`trace = 2`, parabolic `Ã₁` with
unbounded iterate `(1 + 2m, 2m)`), while dual twist summation returns `≥ β` and hybrid-slotted
column reflection locks at `θ ≥ 4/5` (`σ₀ ≥ 5/6`). -/
theorem row_mean_square_conductor_doubling :
    (voronoiCompositeMatrix 1 1).trace = -1 ∧
      voronoiCompositeMatrix 1 1 ^ 3 = 1 ∧
      (voronoiCompositeMatrix 2 2).trace = 2 ∧
      (∀ m : ℕ,
        (sumScaleKappa 2 ∘ reflectScaleKappa 2)^[m] (1, 0) = (1 + 2 * (m : ℝ), 2 * (m : ℝ))) ∧
      (∀ lx ly ℓ β : ℝ,
        β ≤ lowBoundaryFree lx ly ℓ + max 0 (principalExcess (lx + ly) ℓ β) / 2) ∧
      (∀ lx ly ℓ v : ℝ,
        5 / 6 ≤ positiveFormBoundary 6 (probeThetaHybridFree 6 lx ly ℓ v)) := by
  refine ⟨?_, voronoiCompositeMatrix_elliptic_orders.1, ?_, ?_,
    le_lowBoundaryFree_add_half_principalExcess, ?_⟩
  · rw [trace_voronoiCompositeMatrix]; norm_num
  · rw [trace_voronoiCompositeMatrix]; norm_num
  · intro m
    have h := (parabolic_quadratic_and_iterate (κ := 2) (by norm_num) m 1 0).2
    have h42 : (4 : ℝ) / 2 = 2 := by norm_num
    rw [h42] at h
    rw [h]
    simp only [Prod.mk.injEq]
    constructor <;> ring
  · intro lx ly ℓ v
    have hθ := free_floor_le_probeThetaHybridFree (by norm_num : (3 : ℝ) ≤ 6) lx ly ℓ v
    have hmon := (positiveFormBoundary_strictMono (by norm_num : (1 : ℝ) < 6)).monotone hθ
    have hval : positiveFormBoundary 6 ((6 - 2) / (6 - 1)) = 5 / 6 := by
      norm_num [positiveFormBoundary]
    linarith

/-- **Subpart (c): exact coincidence of the floor-bin `A₂` Kubota pole with `R_crit(n)`.** On the
floor bin `δ = 0` (`s₁ = ½`), `kubotaRightmostPole n 0 = ½ + 1/n` equals the signed-Gram phase
bifurcation threshold (`signedGramBrokenTheta = signedGramSymmetricTheta`), and at the cubic cover
`n = 3` (`R₀ = 5/6`) in the sextic (`n = 6`) probe gives `σ₀ = 5/6` (`s = 0`). -/
theorem kubota_pole_eq_signedGram_bifurcation {n : ℝ} (hn : 1 < n) :
    kubotaRightmostPole n 0 = 1 / 2 + 1 / n ∧
      signedGramBrokenTheta n (kubotaRightmostPole n 0) =
        signedGramSymmetricTheta n (kubotaRightmostPole n 0) ∧
      kubotaRightmostPole 3 0 = 5 / 6 ∧
      positiveFormBoundary 6 (signedGramSymmetricTheta 6 (kubotaRightmostPole 3 0)) = 5 / 6 := by
  have hk : kubotaRightmostPole n 0 = 1 / 2 + 1 / n := by unfold kubotaRightmostPole; ring
  have hk3 : kubotaRightmostPole 3 0 = 5 / 6 := by norm_num [kubotaRightmostPole]
  refine ⟨hk, ?_, hk3, ?_⟩
  · rw [hk]
    exact (signedGram_phase_endpoints hn).1
  · rw [hk3]
    norm_num [positiveFormBoundary, signedGramSymmetricTheta]

/-- **Subpart (c): off-diagonal / bilinear saving payoff ladder and rank-two `s = 0` lock.** In the
sextic probe, pre-Cauchy–Schwarz saving `s` lowers the universal floor `5/6` linearly to `5/6 − s`
(`3/4` at `s = 1/12`, `2/3` at `s = 1/6`, `1/2` at `s = 1/3`), whereas every Cauchy–Schwarz /
rank-two reflection model (`s = 0`) satisfies `5/6 ≤ positiveFormBoundary 6 (probeThetaEscapeModel
1 6 lx ly ℓ v 0)` unconditionally across all `(lx, ly, ℓ, v) ∈ ℝ⁴`. -/
theorem offDiag_saving_payoff_and_obstruction (lx ly ℓ v s : ℝ) :
    5 / 6 - s ≤ positiveFormBoundary 6 (probeThetaEscapeModel 1 6 lx ly ℓ v s) ∧
      (positiveFormBoundary 6 (probeThetaEscapeModel 1 6 lx ly ℓ v s) ≤ 3 / 4 → 1 / 12 ≤ s) ∧
      (positiveFormBoundary 6 (probeThetaEscapeModel 1 6 lx ly ℓ v s) ≤ 2 / 3 → 1 / 6 ≤ s) ∧
      (positiveFormBoundary 6 (probeThetaEscapeModel 1 6 lx ly ℓ v s) ≤ 1 / 2 → 1 / 3 ≤ s) ∧
      5 / 6 ≤ positiveFormBoundary 6 (probeThetaEscapeModel 1 6 lx ly ℓ v 0) := by
  have hbase := escape_below_free_floor_bound (k := 1) (n := 6) le_rfl (by norm_num) lx ly ℓ v s
  have hmon := (positiveFormBoundary_strictMono (by norm_num : (1 : ℝ) < 6)).monotone hbase
  have hlhs : positiveFormBoundary 6 ((6 - 2) / (6 - 1) - 2 * 6 / (6 - 1) * s) = 5 / 6 - s := by
    unfold positiveFormBoundary
    ring
  rw [hlhs] at hmon
  have hbase0 := escape_below_free_floor_bound (k := 1) (n := 6) le_rfl (by norm_num) lx ly ℓ v 0
  have hmon0 := (positiveFormBoundary_strictMono (by norm_num : (1 : ℝ) < 6)).monotone hbase0
  have hlhs0 : positiveFormBoundary 6 ((6 - 2) / (6 - 1) - 2 * 6 / (6 - 1) * 0) = 5 / 6 := by
    norm_num [positiveFormBoundary]
  rw [hlhs0] at hmon0
  exact ⟨hmon, fun h => by linarith, fun h => by linarith, fun h => by linarith, hmon0⟩

end

end GaloisForLFunctions.FamilyContinuationTheory.Budget
