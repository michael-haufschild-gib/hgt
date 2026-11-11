import GaloisForLFunctions.FamilyContinuationTheory.TheExponentPlaneOfTheLowSide
import GaloisForLFunctions.FamilyContinuationTheory.TheTargetOccursAmongItsTwists

/-!
# The budget in the twist exponent

Every half-plane `σ₀ = ½ + (1 − 1/n) θ/2` of the positive form corresponds to a single effective
twist-family exponent `θ = (2n/(n − 1))(σ₀ − ½)` (`positiveFormTheta`). Rewriting the exponent
budget of the compensated probe and of reflected large sieves in the single variable `θ` isolates
the exact thresholds reachable by reflection, slot compensation, and large sieves across all
residue-symbol orders `n ≥ 2` and both regimes of the Gram bound:

* **Reflected multiplicative vs. additive large sieves** (`optimalSexticSieve_ge`,
  `sieve_gaussSum_excess_obstruction`, `planar_sieve_min_order`). A multiplicative large sieve term
  `K^u N^v` with diagonal Gauss-sum excess `u + v = 1 + η` (`η > 0`, `u + 2v ≥ 5/6`) cannot reach
  `θ = 1`: at the sextic order the optimal multiplicative large sieve
  `K + N + K^{5/6}N^{1/3} + K^{1/3}N^{5/6}` reaches its minimum `2β = 52/27` (`σ₀ = 26/27`) at
  `θ = 10/9 > 1`. Passing to the additive planar sieve `K + N` (`u + v = 1`) lowers the unslotted
  reflected floor to `θ = 1` (`σ₀ = 1 − 1/(2n)`), where the dual diagonal blocks `θ < 1`.
* **Multi-row and conductor-order corners** (`thetaDesign_ge_trivial`, `corner_theta_two_six`,
  `corner_theta_three_four`, `corner_theta_four_three`). Two or more balanced row variables force
  `θ ≥ n/(n − 1)`; without slots only `(κ, n) = (2, 6)` enters `θ < 1` (`θ = 14/15`), while
  `(3, 4)` and `(4, 3)` stop at `22/21` and `11/9`.
* **Published vertex and universal floor-bin barrier** (`probeThetaGen_published`,
  `endpoint_binding_bin_pos_of_probeThetaGen_le`, `endpointExponentOrder_floor_bin_pos_of_lt`).
  At `n = 6` the published geometry reaches `θ = 9/10` (`σ₀ = 7/8`) and the binding bin
  `δ = 79/204` blocks `θ ≤ 9/10 − 3/5000` in both Gram regimes. Across every order `n ≥ 2` and
  both Gram regimes, trivial summation of the floor bin (`δ = 0`, `R = 1`) blocks every geometry
  with `θ < (5n − 8)/(5(n − 1))` (`22/25` at `n = 6`, `4/5` at `n = 4`, `7/10` at `n = 3`), with
  attainment at `(2/5, 2/5, 1/5)`.
* **Universal reflection-sieve floor and twist circularity** (`free_floor_le_probeThetaFree`,
  `probeThetaFree_with_principal_twists`). Without the dual-length penalty, nonnegative rescaled
  row length `2ℓ ≤ lx + ly` forces `θ ≥ (n − 2)/(n − 1)` (`4/5` at `n = 6`), attained on
  marked-length rows at `ℓ = 1`; bounding the reflected rows through the order-`n` twist family
  itself returns `(n/(n − 1))(2β − 1)`, whose positive-form boundary is `β` identically.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.Budget

noncomputable section

/-! ### Bijection between zero-free boundaries and twist-family exponents -/

/-- Effective twist-family exponent `θ` associated to a half-plane boundary `σ₀` for residue
symbols of order `n`: the inverse of `positiveFormBoundary n θ = ½ + (1 − 1/n) θ/2`. -/
def positiveFormTheta (n σ₀ : ℝ) : ℝ := 2 * n / (n - 1) * (σ₀ - 1 / 2)

theorem positiveFormBoundary_positiveFormTheta {n : ℝ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) (σ₀ : ℝ) :
    positiveFormBoundary n (positiveFormTheta n σ₀) = σ₀ := by
  have hsub : n - 1 ≠ 0 := sub_ne_zero.mpr hn1
  unfold positiveFormBoundary positiveFormTheta
  field_simp
  ring

theorem positiveFormTheta_positiveFormBoundary {n : ℝ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) (θ : ℝ) :
    positiveFormTheta n (positiveFormBoundary n θ) = θ := by
  have hsub : n - 1 ≠ 0 := sub_ne_zero.mpr hn1
  unfold positiveFormBoundary positiveFormTheta
  field_simp
  ring

theorem positiveFormTheta_strictMono {n : ℝ} (hn : 1 < n) :
    StrictMono (positiveFormTheta n) := by
  intro a b hab
  unfold positiveFormTheta
  have hcoef : 0 < 2 * n / (n - 1) := div_pos (by linarith) (by linarith)
  exact mul_lt_mul_of_pos_left (by linarith) hcoef

theorem positiveFormBoundary_strictMono {n : ℝ} (hn : 1 < n) :
    StrictMono (positiveFormBoundary n) := by
  intro a b hab
  unfold positiveFormBoundary
  have hcoef : 0 < 1 - 1 / n := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hn
  nlinarith [mul_lt_mul_of_pos_left hab hcoef]

theorem positiveFormTheta_le_iff {n σ₀ θ : ℝ} (hn : 1 < n) :
    positiveFormTheta n σ₀ ≤ θ ↔ σ₀ ≤ positiveFormBoundary n θ := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n ≠ 1 := by linarith
  constructor
  · intro h
    simpa [positiveFormBoundary_positiveFormTheta hn0 hn1] using
      (positiveFormBoundary_strictMono hn).monotone h
  · intro h
    simpa [positiveFormTheta_positiveFormBoundary hn0 hn1] using
      (positiveFormTheta_strictMono hn).monotone h

theorem le_positiveFormTheta_iff {n σ₀ θ : ℝ} (hn : 1 < n) :
    θ ≤ positiveFormTheta n σ₀ ↔ positiveFormBoundary n θ ≤ σ₀ := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n ≠ 1 := by linarith
  constructor
  · intro h
    simpa [positiveFormBoundary_positiveFormTheta hn0 hn1] using
      (positiveFormBoundary_strictMono hn).monotone h
  · intro h
    simpa [positiveFormTheta_positiveFormBoundary hn0 hn1] using
      (positiveFormTheta_strictMono hn).monotone h

theorem positiveFormTheta_half (n : ℝ) : positiveFormTheta n (1 / 2) = 0 := by
  unfold positiveFormTheta
  ring

theorem positiveFormTheta_one {n : ℝ} (hn1 : n ≠ 1) :
    positiveFormTheta n 1 = n / (n - 1) := by
  have hsub : n - 1 ≠ 0 := sub_ne_zero.mpr hn1
  unfold positiveFormTheta
  field_simp
  ring

theorem positiveFormTheta_dual_diagonal {n : ℝ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    positiveFormTheta n (1 - 1 / (2 * n)) = 1 := by
  have hsub : n - 1 ≠ 0 := sub_ne_zero.mpr hn1
  unfold positiveFormTheta
  field_simp
  ring

theorem positiveFormTheta_floor_bin {n : ℝ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    positiveFormTheta n (1 - 4 / (5 * n)) = (5 * n - 8) / (5 * (n - 1)) := by
  have hsub : n - 1 ≠ 0 := sub_ne_zero.mpr hn1
  unfold positiveFormTheta
  field_simp
  ring

theorem positiveFormTheta_free_floor {n : ℝ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    positiveFormTheta n (1 - 1 / n) = (n - 2) / (n - 1) := by
  have hsub : n - 1 ≠ 0 := sub_ne_zero.mpr hn1
  unfold positiveFormTheta
  field_simp
  ring

/-- The complete sextic dictionary between zero-free boundaries `σ₀` and effective twist-family
exponents `θ`. -/
theorem positiveFormTheta_six_landmarks :
    positiveFormTheta 6 1 = 6 / 5 ∧
      positiveFormTheta 6 (71 / 72) = 7 / 6 ∧
      positiveFormTheta 6 (26 / 27) = 10 / 9 ∧
      positiveFormTheta 6 (11 / 12) = 1 ∧
      positiveFormTheta 6 (8 / 9) = 14 / 15 ∧
      positiveFormTheta 6 (7 / 8) = 9 / 10 ∧
      positiveFormTheta 6 (13 / 15) = 22 / 25 ∧
      positiveFormTheta 6 (5 / 6) = 4 / 5 ∧
      positiveFormTheta 6 (1 / 2) = 0 := by
  norm_num [positiveFormTheta]

/-! ### General-order unbalanced probe budget in the single variable `θ` -/

/-- General-order low boundary of the compensated probe across both regimes of the Gram bound. -/
def lowBoundaryGenOrder (n lx ly ℓ : ℝ) : ℝ :=
  1 - (1 - lx - max 0 (ly - lx) / 2 + ℓ) / n + max 0 (lx + ly + ℓ - 1) / 2

/-- General-order low boundary without the dual-length penalty across both Gram regimes. -/
def lowBoundaryFreeOrder (n lx ly ℓ : ℝ) : ℝ :=
  1 - (1 - lx - max 0 (ly - lx) / 2 + ℓ) / n

/-- General-order high-side exponent of nonprincipal rows of top length `1 − lx + ℓ` in bin
`δ = 2a − 1` with prime amplitude `q` and row count `R`. -/
def endpointExponentOrder (n lx ly ℓ σ₀ δ q R : ℝ) : ℝ :=
  (1 + δ) * (1 - ly) / 2 - σ₀ - ℓ / 2 + q * ℓ + (1 - lx + ℓ) * (R + δ / 2 - 1 / n)

/-- Effective twist-family exponent of the compensated probe at order `n` in both Gram regimes. -/
def probeThetaGen (n lx ly ℓ : ℝ) : ℝ :=
  (n - 2 + 2 * lx + max 0 (ly - lx) - 2 * ℓ + n * max 0 (lx + ly + ℓ - 1)) / (n - 1)

/-- Effective twist-family exponent of the balanced compensated probe (`lx = ly = M/2`). -/
def probeTheta (n M ℓ : ℝ) : ℝ :=
  (n - 2 + (M - 2 * ℓ) + n * max 0 (M + ℓ - 1)) / (n - 1)

/-- Effective twist-family exponent of the probe without the dual-length penalty. -/
def probeThetaFree (n lx ly ℓ : ℝ) : ℝ :=
  (n - 2 + 2 * lx + max 0 (ly - lx) - 2 * ℓ) / (n - 1)

theorem lowBoundaryGenOrder_six (lx ly ℓ : ℝ) :
    lowBoundaryGenOrder 6 lx ly ℓ = lowBoundaryGen lx ly ℓ := by
  unfold lowBoundaryGenOrder lowBoundaryGen
  ring

theorem lowBoundaryFreeOrder_six (lx ly ℓ : ℝ) :
    lowBoundaryFreeOrder 6 lx ly ℓ = lowBoundaryFree lx ly ℓ := by
  unfold lowBoundaryFreeOrder lowBoundaryFree
  ring

theorem lowBoundaryGenOrder_balanced (n M ℓ : ℝ) :
    lowBoundaryGenOrder n (M / 2) (M / 2) ℓ = lowBoundaryOrder n M ℓ := by
  unfold lowBoundaryGenOrder lowBoundaryOrder
  rw [sub_self, max_self, show M / 2 + M / 2 + ℓ - 1 = M + ℓ - 1 by ring]
  ring

theorem endpointExponentOrder_six (lx ly ℓ σ₀ δ q R : ℝ) :
    endpointExponentOrder 6 lx ly ℓ σ₀ δ q R = endpointExponent lx ly ℓ σ₀ δ q R := rfl

theorem probeThetaGen_balanced (n M ℓ : ℝ) :
    probeThetaGen n (M / 2) (M / 2) ℓ = probeTheta n M ℓ := by
  unfold probeThetaGen probeTheta
  rw [sub_self, max_self, show M / 2 + M / 2 + ℓ - 1 = M + ℓ - 1 by ring]
  ring

theorem positiveFormBoundary_probeThetaGen {n : ℝ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) (lx ly ℓ : ℝ) :
    positiveFormBoundary n (probeThetaGen n lx ly ℓ) = lowBoundaryGenOrder n lx ly ℓ := by
  have hsub : n - 1 ≠ 0 := sub_ne_zero.mpr hn1
  unfold positiveFormBoundary probeThetaGen lowBoundaryGenOrder
  field_simp
  ring

theorem probeThetaGen_eq_positiveFormTheta {n : ℝ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) (lx ly ℓ : ℝ) :
    probeThetaGen n lx ly ℓ = positiveFormTheta n (lowBoundaryGenOrder n lx ly ℓ) := by
  rw [← positiveFormBoundary_probeThetaGen hn0 hn1,
    positiveFormTheta_positiveFormBoundary hn0 hn1]

theorem positiveFormBoundary_probeThetaFree {n : ℝ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) (lx ly ℓ : ℝ) :
    positiveFormBoundary n (probeThetaFree n lx ly ℓ) = lowBoundaryFreeOrder n lx ly ℓ := by
  have hsub : n - 1 ≠ 0 := sub_ne_zero.mpr hn1
  unfold positiveFormBoundary probeThetaFree lowBoundaryFreeOrder
  field_simp
  ring

theorem probeThetaFree_le_probeThetaGen {n : ℝ} (hn : 1 < n) (lx ly ℓ : ℝ) :
    probeThetaFree n lx ly ℓ ≤ probeThetaGen n lx ly ℓ := by
  unfold probeThetaFree probeThetaGen
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  nlinarith [le_max_left (0 : ℝ) (lx + ly + ℓ - 1)]

/-! ### Reflected multiplicative large sieves vs. the additive planar sieve -/

/-- General-order diagonal exponent `1 + (1 − 1/n) θ` of the positive form. -/
def diagonalExponentOrder (n θ : ℝ) : ℝ := 1 + (1 - 1 / n) * θ

/-- General-order exponent contributed by a reflected large-sieve term `K^u N^v` at family
length `P = Z^θ` (`K = Z^{2 − θ}`, `N = Z^{3 − 2θ}`). -/
def sieveTermExponentOrder (n u v θ : ℝ) : ℝ :=
  θ + u * (2 - θ) + v * (3 - 2 * θ) - θ / n

/-- **Additive planar sieve floor at general order.** With the optimal additive large sieve
`K + N` (`(u, v) = (1, 0)` and `(0, 1)`), the target-square exponent is at least `2 − 1/n` for
every `θ ∈ ℝ`, attained at `θ = 1` (`σ₀ = 1 − 1/(2n)`). -/
theorem planar_sieve_min_order {n : ℝ} (hn : 1 ≤ n) (θ : ℝ) :
    2 - 1 / n ≤
      max (diagonalExponentOrder n θ)
        (max (sieveTermExponentOrder n 1 0 θ) (sieveTermExponentOrder n 0 1 θ)) := by
  have hn0 : (0 : ℝ) < n := by linarith
  rcases le_total 1 θ with hθ | hθ
  · refine le_max_of_le_left ?_
    unfold diagonalExponentOrder
    have hcoef : 0 ≤ 1 - 1 / n := by
      rw [sub_nonneg, div_le_one hn0]
      exact hn
    have hmul : 1 - 1 / n ≤ (1 - 1 / n) * θ := by
      simpa using mul_le_mul_of_nonneg_left hθ hcoef
    linarith
  · refine le_max_of_le_right (le_max_of_le_left ?_)
    unfold sieveTermExponentOrder
    have h1 : θ / n ≤ 1 / n := div_le_div_of_nonneg_right hθ hn0.le
    linarith

theorem planar_sieve_attained_order (n : ℝ) :
    max (diagonalExponentOrder n 1)
        (max (sieveTermExponentOrder n 1 0 1) (sieveTermExponentOrder n 0 1 1)) =
      2 - 1 / n := by
  have h1 : diagonalExponentOrder n 1 = 2 - 1 / n := by unfold diagonalExponentOrder; ring
  have h2 : sieveTermExponentOrder n 1 0 1 = 2 - 1 / n := by unfold sieveTermExponentOrder; ring
  have h3 : sieveTermExponentOrder n 0 1 1 = 2 - 1 / n := by unfold sieveTermExponentOrder; ring
  rw [h1, h2, h3, max_self, max_self]

/-- **Dual-diagonal Parseval barrier.** After Poisson reflection in the family index of length
`Z^θ`, the dual Parseval diagonal has exponent `2`, which stays within the generic target
`θ + 1` if and only if `1 ≤ θ`. -/
theorem dual_diagonal_barrier_iff (θ : ℝ) :
    max 2 (θ + 1) ≤ θ + 1 ↔ 1 ≤ θ := by
  rw [max_le_iff]
  constructor
  · intro h
    linarith [h.1]
  · intro h
    exact ⟨by linarith, le_rfl⟩

/-- **Diagonal Gauss-sum obstruction for reflected multiplicative large sieves.** Any reflected
sieve term `K^u N^v` with diagonal excess `u + v = 1 + η` and `5/6 ≤ u + 2v` forces the sextic
target-square exponent to be at least `11/6 + 5η / (6(u + 2v))`, attained at
`θ = 1 + η / (u + 2v)`. When `η > 0`, no family length reaches the `θ = 1` value `11/6`. -/
theorem sieve_gaussSum_excess_obstruction {u v η : ℝ} (huv : u + v = 1 + η)
    (hslope : 5 / 6 ≤ u + 2 * v) (θ : ℝ) :
    11 / 6 + 5 * η / (6 * (u + 2 * v)) ≤ max (diagonalExponent θ) (sieveTermExponent u v θ) := by
  have hpos : 0 < u + 2 * v := by linarith
  have hne : u + 2 * v ≠ 0 := hpos.ne'
  set θ₀ : ℝ := 1 + η / (u + 2 * v)
  rcases le_total θ₀ θ with hθ | hθ
  · refine le_max_of_le_left ?_
    unfold diagonalExponent
    have heq : 1 + 5 * θ₀ / 6 = 11 / 6 + 5 * η / (6 * (u + 2 * v)) := by
      simp only [θ₀]
      field_simp
      ring
    linarith
  · refine le_max_of_le_right ?_
    unfold sieveTermExponent
    have hrew : θ + u * (2 - θ) + v * (3 - 2 * θ) - θ / 6 =
        (u + v + 5 / 6) + (u + 2 * v - 5 / 6) * (1 - θ) := by ring
    rw [hrew, huv]
    have hdiff : -(η / (u + 2 * v)) ≤ 1 - θ := by
      have : θ - 1 ≤ η / (u + 2 * v) := by simp only [θ₀] at hθ; linarith
      linarith
    have hmul : (u + 2 * v - 5 / 6) * -(η / (u + 2 * v)) ≤ (u + 2 * v - 5 / 6) * (1 - θ) :=
      mul_le_mul_of_nonneg_left hdiff (by linarith)
    have hval : 1 + η + 5 / 6 + (u + 2 * v - 5 / 6) * -(η / (u + 2 * v)) =
        11 / 6 + 5 * η / (6 * (u + 2 * v)) := by
      field_simp
      ring
    linarith

/-- Exponent of the target square under the optimal sextic multiplicative large sieve
`K + N + K^{5/6}N^{1/3} + K^{1/3}N^{5/6}` applied to the reflected rows. -/
def optimalSexticSieveExponent (θ : ℝ) : ℝ :=
  max (diagonalExponent θ)
    (max (sieveTermExponent 1 0 θ)
      (max (sieveTermExponent 0 1 θ)
        (max (sieveTermExponent (5 / 6) (1 / 3) θ) (sieveTermExponent (1 / 3) (5 / 6) θ))))

/-- **Sharp floor of the optimal sextic multiplicative large sieve.** Across all `θ ∈ ℝ`, the
reflected optimal sextic multiplicative large sieve gives `2β ≥ 52/27` (`σ₀ ≥ 26/27`),
corresponding to effective twist exponent `positiveFormTheta 6 (26/27) = 10/9 > 1`. -/
theorem optimalSexticSieve_ge (θ : ℝ) :
    52 / 27 ≤ optimalSexticSieveExponent θ := by
  have h := sieve_gaussSum_excess_obstruction (u := 5 / 6) (v := 1 / 3) (η := 1 / 6)
    (by norm_num) (by norm_num) θ
  have hval : (11 : ℝ) / 6 + 5 * (1 / 6) / (6 * (5 / 6 + 2 * (1 / 3))) = 52 / 27 := by norm_num
  rw [hval] at h
  unfold optimalSexticSieveExponent
  rcases max_choice (diagonalExponent θ) (sieveTermExponent (5 / 6) (1 / 3) θ) with hmax | hmax
  · rw [hmax] at h
    exact le_max_of_le_left h
  · rw [hmax] at h
    exact le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_left h)))

/-- `52/27` is attained uniquely at `θ = 10/9`. -/
theorem optimalSexticSieve_attained :
    optimalSexticSieveExponent (10 / 9) = 52 / 27 := by
  norm_num [optimalSexticSieveExponent, diagonalExponent, sieveTermExponent]

/-- Even the diagonal sextic lower-bound term `(K N)^{17/32} = (K N)^{1/2 + 1/32}` forces
`2β ≥ 571/306 > 11/6` (`σ₀ ≥ 571/612`, effective twist exponent `53/51 > 1`). -/
theorem sextic_diagonal_lower_bound_obstruction (θ : ℝ) :
    571 / 306 ≤ max (diagonalExponent θ) (sieveTermExponent (17 / 32) (17 / 32) θ) := by
  have h := sieve_gaussSum_excess_obstruction (u := 17 / 32) (v := 17 / 32) (η := 1 / 16)
    (by norm_num) (by norm_num) θ
  have hval : (11 : ℝ) / 6 + 5 * (1 / 16) / (6 * (17 / 32 + 2 * (17 / 32))) = 571 / 306 := by
    norm_num
  rwa [hval] at h

/-! ### Multi-row and conductor-order corners in the twist exponent -/

/-- Effective twist exponent of a balanced design with `k` row variables of order `n`. -/
def thetaDesign (k n : ℝ) : ℝ := positiveFormTheta n (lowBoundaryDesign k n)

/-- **Two or more row variables exceed the trivial barrier.** For `k ≥ 2` and `n ≥ 3`, the
balanced effective twist exponent is at least `n/(n − 1)`. -/
theorem thetaDesign_ge_trivial {k n : ℝ} (hk : 2 ≤ k) (hn : 3 ≤ n) :
    n / (n - 1) ≤ thetaDesign k n := by
  unfold thetaDesign
  rw [← positiveFormTheta_one (by linarith)]
  exact (positiveFormTheta_strictMono (by linarith)).monotone (one_le_lowBoundaryDesign hk hn)

/-- Unslotted conductor-order tradeoffs in the variable `θ`: `(2, 6)` reaches `14/15 < 1`, whereas
`(3, 4)` and `(4, 3)` are blocked above `1` at `22/21` and `11/9`. -/
theorem corner_theta_two_six (M : ℝ) :
    14 / 15 ≤ positiveFormTheta 6 (max (lowUnslotted 2 6 M) (floorUnslotted 6 M)) := by
  have h := (positiveFormTheta_strictMono (by norm_num : (1 : ℝ) < 6)).monotone (corner_two_six M)
  have hval : positiveFormTheta 6 (8 / 9) = 14 / 15 := by norm_num [positiveFormTheta]
  linarith

theorem corner_theta_two_six_attained :
    positiveFormTheta 6 (max (lowUnslotted 2 6 (2 / 3)) (floorUnslotted 6 (2 / 3))) = 14 / 15 := by
  rw [corner_two_six_attained]
  norm_num [positiveFormTheta]

theorem corner_theta_three_four (M : ℝ) :
    22 / 21 ≤ positiveFormTheta 4 (max (lowUnslotted 3 4 M) (floorUnslotted 4 M)) := by
  have h := (positiveFormTheta_strictMono (by norm_num : (1 : ℝ) < 4)).monotone
    (corner_three_four M)
  have hval : positiveFormTheta 4 (25 / 28) = 22 / 21 := by norm_num [positiveFormTheta]
  linarith

theorem corner_theta_four_three (M : ℝ) :
    11 / 9 ≤ positiveFormTheta 3 (max (lowUnslotted 4 3 M) (floorUnslotted 3 M)) := by
  have h := (positiveFormTheta_strictMono (by norm_num : (1 : ℝ) < 3)).monotone
    (corner_four_three M)
  have hval : positiveFormTheta 3 (49 / 54) = 11 / 9 := by norm_num [positiveFormTheta]
  linarith

/-! ### Published vertex (`θ = 9/10`) and binding-bin barrier in both Gram regimes -/

theorem probeThetaGen_published :
    probeThetaGen 6 (17 / 48) (23 / 48) (1 / 6) = 9 / 10 := by
  norm_num [probeThetaGen]

/-- **Published binding-bin barrier in `θ` across both Gram regimes.** For every geometry with
`lx ≤ 1` whose effective twist exponent is at most `9/10 − 3/5000 = 4497/5000`
(`σ₀ ≤ 7/8 − 1/4000`), the high exponent in bin `δ = 79/204` at the published row count is
strictly positive. -/
theorem endpoint_binding_bin_pos_of_probeThetaGen_published_le {lx ly ℓ : ℝ} (hlx : lx ≤ 1)
    (hθ : probeThetaGen 6 lx ly ℓ ≤ 9 / 10 - 3 / 5000) :
    0 < endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ) (79 / 204) (79 / 408)
      (rowCount (79 / 204) (1 / 2)) := by
  have hσ : lowBoundaryGen lx ly ℓ ≤ 7 / 8 - 1 / 4000 := by
    have hmon := (positiveFormBoundary_strictMono (by norm_num : (1 : ℝ) < 6)).monotone hθ
    rw [positiveFormBoundary_probeThetaGen (by norm_num) (by norm_num),
      lowBoundaryGenOrder_six] at hmon
    have hval : positiveFormBoundary 6 (9 / 10 - 3 / 5000) = 7 / 8 - 1 / 4000 := by
      norm_num [positiveFormBoundary]
    linarith
  rcases le_or_gt lx ly with hle | hgt
  · rw [lowBoundaryGen_eq_of_le ℓ hle] at hσ ⊢
    exact endpointExponent_pos_of_lowBoundary_le hlx hσ
  · rw [rowCount_binding]
    have hν : max 0 (ly - lx) = 0 := max_eq_left (by linarith)
    unfold lowBoundaryGen at hσ ⊢
    rw [hν] at hσ ⊢
    have hμ0 : (0 : ℝ) ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
    have hμ1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
    generalize max 0 (lx + ly + ℓ - 1) = μ at hσ hμ0 hμ1 ⊢
    unfold endpointExponent
    linarith

/-- **Binding-bin barrier in `θ` for admissible row counts across both Gram regimes.** For every
geometry with `lx ≤ 1`, `0 ≤ ly`, `0 ≤ ℓ`, and row count `R ≥ 21766/32589 − 1/10000`, if the
effective twist exponent is at most `9/10 − 6/6250` (`σ₀ ≤ 7/8 − 1/2500`), then the high exponent
in bin `δ = 79/204` is strictly positive. -/
theorem endpoint_binding_bin_pos_of_probeThetaGen_le {lx ly ℓ R : ℝ}
    (hlx : lx ≤ 1) (hly : 0 ≤ ly) (hℓ : 0 ≤ ℓ) (hR : 21766 / 32589 - 1 / 10000 ≤ R)
    (hθ : probeThetaGen 6 lx ly ℓ ≤ 9 / 10 - 6 / 6250) :
    0 < endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ) (79 / 204) (79 / 408) R := by
  have hσ : lowBoundaryGen lx ly ℓ ≤ 7 / 8 - 1 / 2500 := by
    have hmon := (positiveFormBoundary_strictMono (by norm_num : (1 : ℝ) < 6)).monotone hθ
    rw [positiveFormBoundary_probeThetaGen (by norm_num) (by norm_num),
      lowBoundaryGenOrder_six] at hmon
    have hval : positiveFormBoundary 6 (9 / 10 - 6 / 6250) = 7 / 8 - 1 / 2500 := by
      norm_num [positiveFormBoundary]
    linarith
  rcases le_or_gt lx ly with hle | hgt
  · rw [lowBoundaryGen_eq_of_le ℓ hle] at hσ ⊢
    exact endpointExponent_pos_of_lowBoundary_le_of_rowCount hlx hly hℓ hR hσ
  · have hh : 0 ≤ 1 - lx + ℓ := by linarith
    have hmono : endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ) (79 / 204) (79 / 408)
        (21766 / 32589 - 1 / 10000) ≤
        endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ) (79 / 204) (79 / 408) R := by
      unfold endpointExponent
      nlinarith [mul_nonneg hh (sub_nonneg.2 hR)]
    refine lt_of_lt_of_le ?_ hmono
    have hν : max 0 (ly - lx) = 0 := max_eq_left (by linarith)
    unfold lowBoundaryGen at hσ ⊢
    rw [hν] at hσ ⊢
    have hμ0 : (0 : ℝ) ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
    have hμ1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
    generalize max 0 (lx + ly + ℓ - 1) = μ at hσ hμ0 hμ1 ⊢
    unfold endpointExponent
    linarith

/-! ### Universal floor-bin barrier (`θ ≥ (5n − 8)/(5(n − 1))`) across all orders and Gram regimes -/

/-- **Universal floor-bin barrier in the twist exponent.** For every residue-symbol order `n ≥ 2`
and every geometry `(lx, ly, ℓ) ∈ ℝ³` (in either regime of the Gram bound), if
`probeThetaGen n lx ly ℓ < (5n − 8)/(5(n − 1))`, then the floor-bin high exponent (`δ = 0`,
`q = 0`, `R = 1`) is strictly positive. -/
theorem endpointExponentOrder_floor_bin_pos_of_lt {n lx ly ℓ : ℝ} (hn : 2 ≤ n)
    (hθ : probeThetaGen n lx ly ℓ < (5 * n - 8) / (5 * (n - 1))) :
    0 < endpointExponentOrder n lx ly ℓ (lowBoundaryGenOrder n lx ly ℓ) 0 0 1 := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) < n := by linarith
  have hσ : lowBoundaryGenOrder n lx ly ℓ < 1 - 4 / (5 * n) := by
    have hmon := positiveFormBoundary_strictMono hn1 hθ
    rw [positiveFormBoundary_probeThetaGen hn0.ne' hn1.ne',
      ← positiveFormTheta_floor_bin hn0.ne' hn1.ne',
      positiveFormBoundary_positiveFormTheta hn0.ne' hn1.ne'] at hmon
    exact hmon
  set r : ℝ := 1 / n with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have hrle : r ≤ 1 / 2 := by
    rw [hr, div_le_iff₀ hn0]
    linarith
  set ν : ℝ := max 0 (ly - lx)
  set μ : ℝ := max 0 (lx + ly + ℓ - 1)
  have hν0 : 0 ≤ ν := le_max_left _ _
  have hν1 : ly - lx ≤ ν := le_max_right _ _
  have hμ0 : 0 ≤ μ := le_max_left _ _
  have hμ1 : lx + ly + ℓ - 1 ≤ μ := le_max_right _ _
  set A : ℝ := 1 / 5 - lx - ν / 2 + ℓ
  set B : ℝ := μ - (lx + ly + ℓ - 1)
  set C : ℝ := ν - (ly - lx)
  have hB : 0 ≤ B := sub_nonneg.mpr hμ1
  have hC : 0 ≤ C := sub_nonneg.mpr hν1
  have hσ_rew : 1 - 4 / (5 * n) - lowBoundaryGenOrder n lx ly ℓ = A * r - μ / 2 := by
    unfold lowBoundaryGenOrder
    change 1 - 4 / (5 * n) - (1 - (1 - lx - ν / 2 + ℓ) / n + μ / 2) = A * (1 / n) - μ / 2
    simp only [A]
    field_simp
    ring
  have hAr : μ / 2 < A * r := by linarith [hσ, hσ_rew]
  have hApos : 0 < A := by
    by_contra hcon
    rw [not_lt] at hcon
    have : A * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hrpos.le
    linarith
  have hμltA : μ < A := by
    have h1 : A * r ≤ A * (1 / 2) := mul_le_mul_of_nonneg_left hrle hApos.le
    linarith
  have hE_rew : endpointExponentOrder n lx ly ℓ (lowBoundaryGenOrder n lx ly ℓ) 0 0 1 =
      5 / 6 * (A - μ) + 1 / 3 * B + 1 / 6 * C + (1 / 4 - r / 2) * ν := by
    unfold endpointExponentOrder lowBoundaryGenOrder
    change (1 + 0) * (1 - ly) / 2 - (1 - (1 - lx - ν / 2 + ℓ) / n + μ / 2) - ℓ / 2 + 0 * ℓ +
        (1 - lx + ℓ) * (1 + 0 / 2 - 1 / n) =
      5 / 6 * (A - μ) + 1 / 3 * B + 1 / 6 * C + (1 / 4 - (1 / n) / 2) * ν
    simp only [A, B, C]
    field_simp
    ring
  rw [hE_rew]
  have hνterm : 0 ≤ (1 / 4 - r / 2) * ν := mul_nonneg (by linarith) hν0
  linarith

/-- The floor-bin threshold `(5n − 8)/(5(n − 1))` (`22/25` at `n = 6`) is universally attained at
`(lx, ly, ℓ) = (2/5, 2/5, 1/5)`, where under zero-density count `R = 1 − δ` every bin has
exponent `(q − δ/2)/5`. -/
theorem probeThetaGen_floor_attained {n : ℝ} (hn1 : n ≠ 1) :
    probeThetaGen n (2 / 5) (2 / 5) (1 / 5) = (5 * n - 8) / (5 * (n - 1)) := by
  have hsub : n - 1 ≠ 0 := sub_ne_zero.mpr hn1
  unfold probeThetaGen
  rw [sub_self, max_self, show (2 : ℝ) / 5 + 2 / 5 + 1 / 5 - 1 = 0 by norm_num, max_self]
  field_simp
  ring

theorem endpointExponentOrder_floor_attained {n : ℝ} (hn0 : n ≠ 0) (δ q : ℝ) :
    endpointExponentOrder n (2 / 5) (2 / 5) (1 / 5) (1 - 4 / (5 * n)) δ q (1 - δ) =
      (q - δ / 2) / 5 := by
  unfold endpointExponentOrder
  field_simp
  ring

/-! ### Universal reflection-sieve floor (`θ ≥ (n − 2)/(n − 1)`) and twist circularity -/

/-- **Universal reflection-sieve floor.** For every order `n > 1` and every geometry with
nonnegative rescaled row length `2ℓ ≤ lx + ly`, the effective twist exponent without the
dual-length penalty is at least `(n − 2)/(n − 1)` (`4/5` at `n = 6`, `3/4` at `n = 5`, `2/3` at
`n = 4`, `1/2` at `n = 3`, `0` at `n = 2`). -/
theorem free_floor_le_probeThetaFree {n lx ly ℓ : ℝ} (hn : 1 < n) (h : 2 * ℓ ≤ lx + ly) :
    (n - 2) / (n - 1) ≤ probeThetaFree n lx ly ℓ := by
  unfold probeThetaFree
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  have hν : ly - lx ≤ max 0 (ly - lx) := le_max_right _ _
  linarith

/-- On rows as long as the marked index (`lx + ly = 1 + ℓ`, `lx ≤ ly`), `probeThetaFree` equals
`(n − 1 − ℓ)/(n − 1)`, reaching `(n − 2)/(n − 1)` (`4/5` at `n = 6`) at `ℓ = 1`. -/
theorem probeThetaFree_marked_length {n lx ly ℓ : ℝ} (hle : lx ≤ ly) (hM : lx + ly = 1 + ℓ) :
    probeThetaFree n lx ly ℓ = (n - 1 - ℓ) / (n - 1) := by
  unfold probeThetaFree
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ly - lx)]
  congr 1
  linarith

/-- General-order excess of the principal `n`-th-power twists in the mean square of the marked
rows when the target has a zero at real part `β`. -/
def principalExcessOrder (n M ℓ β : ℝ) : ℝ := (2 + 2 * ℓ - M) / n + 2 * β - 2

theorem principalExcessOrder_six (M ℓ β : ℝ) :
    principalExcessOrder 6 M ℓ β = principalExcess M ℓ β := rfl

/-- **Twist circularity at general order.** Replacing the dual-length term by half the excess of
the principal `n`-th-power twists gives effective twist exponent `(n/(n − 1))(2β − 1) =
positiveFormTheta n β` when `lx ≤ ly`, and at least `positiveFormTheta n β` in both Gram regimes:
passing through the twists recovers the target zero `β` with zero gain. -/
theorem probeThetaFree_with_principal_twists {n lx ly : ℝ} (hn0 : n ≠ 0) (hn1 : n ≠ 1)
    (ℓ β : ℝ) (hle : lx ≤ ly) :
    positiveFormTheta n (lowBoundaryFreeOrder n lx ly ℓ +
      principalExcessOrder n (lx + ly) ℓ β / 2) = n / (n - 1) * (2 * β - 1) := by
  have hsub : n - 1 ≠ 0 := sub_ne_zero.mpr hn1
  unfold positiveFormTheta lowBoundaryFreeOrder principalExcessOrder
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ly - lx)]
  field_simp
  ring

theorem le_probeThetaFree_with_principal_twists {n lx ly ℓ β : ℝ} (hn : 1 < n) :
    n / (n - 1) * (2 * β - 1) ≤
      positiveFormTheta n (lowBoundaryFreeOrder n lx ly ℓ +
        max 0 (principalExcessOrder n (lx + ly) ℓ β) / 2) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hβ : β ≤ lowBoundaryFreeOrder n lx ly ℓ +
      max 0 (principalExcessOrder n (lx + ly) ℓ β) / 2 := by
    have h1 : principalExcessOrder n (lx + ly) ℓ β ≤
        max 0 (principalExcessOrder n (lx + ly) ℓ β) := le_max_right _ _
    have h2 : ly - lx ≤ max 0 (ly - lx) := le_max_right _ _
    set m : ℝ := max 0 (principalExcessOrder n (lx + ly) ℓ β)
    set ν : ℝ := max 0 (ly - lx)
    have hrew : lowBoundaryFreeOrder n lx ly ℓ + m / 2 - β =
        (ν - (ly - lx)) / (2 * n) + (m - principalExcessOrder n (lx + ly) ℓ β) / 2 := by
      unfold lowBoundaryFreeOrder principalExcessOrder
      change 1 - (1 - lx - ν / 2 + ℓ) / n + m / 2 - β =
        (ν - (ly - lx)) / (2 * n) + (m - ((2 + 2 * ℓ - (lx + ly)) / n + 2 * β - 2)) / 2
      field_simp
      ring
    have hterm1 : 0 ≤ (ν - (ly - lx)) / (2 * n) := div_nonneg (by linarith) (by linarith)
    linarith
  have hmon := (positiveFormTheta_strictMono hn).monotone hβ
  have heq : positiveFormTheta n β = n / (n - 1) * (2 * β - 1) := by
    have hsub : n - 1 ≠ 0 := by linarith
    unfold positiveFormTheta
    field_simp
  linarith

end

end GaloisForLFunctions.FamilyContinuationTheory.Budget
