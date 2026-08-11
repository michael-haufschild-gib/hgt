import GaloisForLFunctions.RHTower.RouteEComponentHistoryShuffle
import GaloisForLFunctions.RHTower.RouteEGibbsUniformCellComparison

/-!
# Route E component-history Gibbs parity comparison

Component histograms do more than count replica orbits: every multiplicative slot receiver has
exactly the same all-order product on the whole cell.  This discharges the equal-product premise
in the Gibbs history theorem.  For the binary singleton cell, the physical anchored parity mean
is therefore within the explicit Gibbs curvature defect of its exact uniform bias
`(1 - 2 / M)^|C|`.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

open GaloisForLFunctions.HTGeometry

section HistogramProduct

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (J : C → Type*) [∀ c, Fintype (J c)] [∀ c, DecidableEq (J c)]

/-- Multiplicative receiver attached to one replica slot of a component history. -/
def routeEComponentSlotReceiver {m : ℕ} (value : ∀ c, J c → ℝ)
    (x : RouteEComponentHistory J m) (r : Fin m) : ℝ :=
  ∏ c, value c (x r c)

omit [DecidableEq C] in
/-- A multiplicative receiver's total product depends only on component histograms. -/
theorem routeE_componentSlotReceiver_product_eq_histogram
    {m : ℕ} (value : ∀ c, J c → ℝ) (x : RouteEComponentHistory J m) :
    (∏ r, routeEComponentSlotReceiver J value x r) =
      ∏ c, ∏ b, value c b ^ tupleHistogram (fun r => x r c) b := by
  classical
  change (∏ r, ∏ c, value c (x r c)) = _
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro c _hc
  symm
  calc
    (∏ b, value c b ^ tupleHistogram (fun r => x r c) b) =
        ∏ b, ∏ r ∈ (Finset.univ : Finset (Fin m)) with x r c = b, value c b := by
      apply Finset.prod_congr rfl
      intro b _hb
      simp [tupleHistogram]
    _ = ∏ r, value c (x r c) :=
      Finset.prod_fiberwise' Finset.univ (fun r => x r c) (value c)

/-- Two histories in one component-histogram cell have exactly equal receiver products. -/
theorem routeE_componentHistogramCell_receiver_product_eq
    {m : ℕ} (k : ∀ c, J c → ℕ) (value : ∀ c, J c → ℝ)
    {x y : RouteEComponentHistory J m}
    (hx : x ∈ routeEComponentHistogramCell J m k)
    (hy : y ∈ routeEComponentHistogramCell J m k) :
    (∏ r, routeEComponentSlotReceiver J value x r) =
      ∏ r, routeEComponentSlotReceiver J value y r := by
  classical
  rw [routeE_componentSlotReceiver_product_eq_histogram J value x,
    routeE_componentSlotReceiver_product_eq_histogram J value y]
  apply Finset.prod_congr rfl
  intro c _hc
  have hxc : tupleHistogram (fun r => x r c) = k c :=
    (Finset.mem_filter.mp hx).2 c
  have hyc : tupleHistogram (fun r => y r c) = k c :=
    (Finset.mem_filter.mp hy).2 c
  rw [hxc, hyc]

end HistogramProduct

section BinaryPhysicalBias

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Exact uniform anchored parity for an arbitrary binary component histogram. -/
theorem routeE_binary_componentHistogram_cell_subtype_character_mean
    (m : ℕ) (k : C → Bool → ℕ)
    (hk : ∀ c, ∑ b, k c b = m + 1) :
    ((∑ x : {x // x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k},
          ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
        (Fintype.card
          {x // x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k} : ℝ)) =
      ∏ c, ((1 : ℝ) - 2 * (k c true : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
  classical
  let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
  have hsum :
      (∑ x : {x // x ∈ cell}, ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) =
        ∑ x ∈ cell, ∏ c, routeEBinaryPresenceCharacter (x 0 c) := by
    exact (Finset.sum_subtype cell (fun _ => Iff.rfl)
      (fun x => ∏ c, routeEBinaryPresenceCharacter (x 0 c))).symm
  have hmean := routeE_componentHistogram_anchor_zero_character_mean_count_sum
    (fun _ : C => Bool) m k (fun _ => routeEBinaryPresenceCharacter) hk
  change ((∑ x : {x // x ∈ cell}, ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
      (Fintype.card {x // x ∈ cell} : ℝ)) = _
  rw [hsum, Fintype.card_coe, hmean]
  apply Finset.prod_congr rfl
  intro c _hc
  have hcount : k c true + k c false = m + 1 := by
    simpa [Fintype.sum_bool] using hk c
  rw [Fintype.sum_bool]
  simp only [routeEBinaryPresenceCharacter, Bool.false_eq_true, ↓reduceIte,
    mul_one, mul_neg]
  have hcountR :
      (k c true : ℝ) + (k c false : ℝ) = ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  field_simp [ne_of_gt hm]
  linarith [hcountR]

/-- Balanced incidence mass of a binary component histogram.  A component contributes its
smaller empirical occupancy, so both sparse presence and sparse absence are detected. -/
def routeEBinaryHistogramBalancedMass
    (m : ℕ) (k : C → Bool → ℕ) : ℝ :=
  ∑ c, min ((k c true : ℝ) / ((m + 1 : ℕ) : ℝ))
    (1 - (k c true : ℝ) / ((m + 1 : ℕ) : ℝ))

/-- One binary empirical parity factor is exponentially controlled by its balanced occupancy. -/
theorem routeE_abs_one_sub_two_mul_le_exp_neg_two_min (u : ℝ) :
    |1 - 2 * u| ≤ Real.exp (-2 * min u (1 - u)) := by
  rcases le_total u (1 / 2 : ℝ) with hu | hu
  · have habs : |1 - 2 * u| = 1 - 2 * u := abs_of_nonneg (by linarith)
    have hmin : min u (1 - u) = u := min_eq_left (by linarith)
    rw [habs, hmin]
    simpa only [neg_mul] using Real.one_sub_le_exp_neg (2 * u)
  · have habs : |1 - 2 * u| = 2 * u - 1 := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have hmin : min u (1 - u) = 1 - u := min_eq_right (by linarith)
    rw [habs, hmin]
    calc
      2 * u - 1 = 1 - 2 * (1 - u) := by ring
      _ ≤ Real.exp (-(2 * (1 - u))) := Real.one_sub_le_exp_neg (2 * (1 - u))
      _ = Real.exp (-2 * (1 - u)) := by congr 1; ring

omit [DecidableEq C] in
/-- Exact histogram bias is bounded by the exponential of minus twice balanced incidence mass. -/
theorem routeE_abs_binary_histogramBias_le_exp_balancedMass
    (m : ℕ) (k : C → Bool → ℕ) :
    |∏ c, ((1 : ℝ) - 2 * (k c true : ℝ) / ((m + 1 : ℕ) : ℝ))| ≤
      Real.exp (-2 * routeEBinaryHistogramBalancedMass m k) := by
  classical
  rw [Finset.abs_prod]
  calc
    (∏ c, |(1 : ℝ) - 2 * (k c true : ℝ) / ((m + 1 : ℕ) : ℝ)|) ≤
        ∏ c, Real.exp (-2 * min
          ((k c true : ℝ) / ((m + 1 : ℕ) : ℝ))
          (1 - (k c true : ℝ) / ((m + 1 : ℕ) : ℝ))) := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro c _hc
      have hform :
          (1 : ℝ) - 2 * (k c true : ℝ) / ((m + 1 : ℕ) : ℝ) =
            1 - 2 * ((k c true : ℝ) / ((m + 1 : ℕ) : ℝ)) := by ring
      rw [hform]
      exact routeE_abs_one_sub_two_mul_le_exp_neg_two_min _
    _ = Real.exp (-2 * routeEBinaryHistogramBalancedMass m k) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [routeEBinaryHistogramBalancedMass]
      rw [Finset.mul_sum]

/-- Uniform anchored parity on the subtype of a binary singleton cell has the exact hostile bias. -/
theorem routeE_binary_singleton_cell_subtype_character_mean
    (m : ℕ) (k : C → Bool → ℕ)
    (hk : ∀ c, ∑ b, k c b = m + 1)
    (hone : ∀ c, k c true = 1) :
    ((∑ x : {x // x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k},
          ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
        (Fintype.card
          {x // x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k} : ℝ)) =
      ((1 : ℝ) - 2 / ((m + 1 : ℕ) : ℝ)) ^ Fintype.card C := by
  classical
  let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
  have hsum :
      (∑ x : {x // x ∈ cell}, ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) =
        ∑ x ∈ cell, ∏ c, routeEBinaryPresenceCharacter (x 0 c) := by
    exact (Finset.sum_subtype cell (fun _ => Iff.rfl)
      (fun x => ∏ c, routeEBinaryPresenceCharacter (x 0 c))).symm
  change ((∑ x : {x // x ∈ cell}, ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
      (Fintype.card {x // x ∈ cell} : ℝ)) = _
  rw [hsum, Fintype.card_coe]
  exact routeE_binary_singleton_component_character_mean m k hk hone

/-- **All-order physical binary histogram comparison.**  Exact component histograms discharge
the product-equality premise.  For arbitrary multiplicities, physical Gibbs parity differs from
the explicit empirical bias `prod_c (1 - 2 k_c / M)` by only the aperture curvature defect. -/
theorem routeE_binary_componentHistory_gibbsParity_sub_histogramBias_le
    (m : ℕ) (k : C → Bool → ℕ) (value : C → Bool → ℝ) (X H : ℝ)
    (hk : ∀ c, ∑ b, k c b = m + 1)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (haperture : ∀ x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k,
      ∀ r, routeEComponentSlotReceiver (fun _ : C => Bool) value x r ∈
        Set.Icc (X - H) (X + H)) :
    let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
    |(∑ x : {x // x ∈ cell},
          routeEProductHistoryGibbsWeight X
              (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1) *
            ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
          (∑ x : {x // x ∈ cell},
            routeEProductHistoryGibbsWeight X
              (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1)) -
        ∏ c, ((1 : ℝ) - 2 * (k c true : ℝ) / ((m + 1 : ℕ) : ℝ))| ≤
      Real.exp (((m + 1 : ℕ) : ℝ) * H ^ 2 / (X * (X - H))) - 1 := by
  classical
  dsimp only
  let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
  have hcellPos : 0 < cell.card := by
    rw [routeE_componentHistogramCell_card (fun _ : C => Bool) (m + 1) k hk]
    exact Finset.prod_pos fun c _hc => Nat.multinomial_pos Finset.univ (k c)
  let witness : {x // x ∈ cell} := ⟨Classical.choose (Finset.card_pos.mp hcellPos),
    Classical.choose_spec (Finset.card_pos.mp hcellPos)⟩
  letI : Nonempty {x // x ∈ cell} := ⟨witness⟩
  have hcompare := routeE_productHistoryGibbsMean_sub_uniformMean_le
    (Ω := {x // x ∈ cell}) (R := Fin (m + 1)) X H
    (fun x => routeEComponentSlotReceiver (fun _ : C => Bool) value x.1)
    (fun x => ∏ c, routeEBinaryPresenceCharacter (x.1 0 c))
    hX hH hHX
    (fun x r => haperture x.1 x.2 r)
    (fun x y => routeE_componentHistogramCell_receiver_product_eq
      (fun _ : C => Bool) k value x.2 y.2)
    (fun x => by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
        (fun c _ => by
          cases x.1 0 c <;> simp [routeEBinaryPresenceCharacter]))
  have huniform := routeE_binary_componentHistogram_cell_subtype_character_mean m k hk
  rw [huniform] at hcompare
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hcompare

/-- **Balanced-incidence physical endpoint.**  Physical all-order parity is bounded by an explicit
sum of histogram imbalance and Gibbs curvature.  No orbit-size surrogate remains. -/
theorem routeE_abs_binary_componentHistory_gibbsParity_le_balancedMass_add_curvature
    (m : ℕ) (k : C → Bool → ℕ) (value : C → Bool → ℝ) (X H : ℝ)
    (hk : ∀ c, ∑ b, k c b = m + 1)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (haperture : ∀ x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k,
      ∀ r, routeEComponentSlotReceiver (fun _ : C => Bool) value x r ∈
        Set.Icc (X - H) (X + H)) :
    let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
    let physicalMean :=
      (∑ x : {x // x ∈ cell},
          routeEProductHistoryGibbsWeight X
              (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1) *
            ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
        (∑ x : {x // x ∈ cell},
          routeEProductHistoryGibbsWeight X
            (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1))
    |physicalMean| ≤
      Real.exp (-2 * routeEBinaryHistogramBalancedMass m k) +
        (Real.exp (((m + 1 : ℕ) : ℝ) * H ^ 2 / (X * (X - H))) - 1) := by
  dsimp only
  let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
  let physicalMean :=
    (∑ x : {x // x ∈ cell},
        routeEProductHistoryGibbsWeight X
            (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1) *
          ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
      (∑ x : {x // x ∈ cell},
        routeEProductHistoryGibbsWeight X
          (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1))
  let histogramBias :=
    ∏ c, ((1 : ℝ) - 2 * (k c true : ℝ) / ((m + 1 : ℕ) : ℝ))
  let curvatureDefect :=
    Real.exp (((m + 1 : ℕ) : ℝ) * H ^ 2 / (X * (X - H))) - 1
  have hcomparison : |physicalMean - histogramBias| ≤ curvatureDefect := by
    dsimp [physicalMean, histogramBias, curvatureDefect, cell]
    exact routeE_binary_componentHistory_gibbsParity_sub_histogramBias_le
      m k value X H hk hX hH hHX haperture
  have hbias : |histogramBias| ≤
      Real.exp (-2 * routeEBinaryHistogramBalancedMass m k) := by
    exact routeE_abs_binary_histogramBias_le_exp_balancedMass m k
  calc
    |physicalMean| ≤ |physicalMean - histogramBias| + |histogramBias| := by
      linarith [abs_sub_abs_le_abs_sub physicalMean histogramBias]
    _ ≤ curvatureDefect + Real.exp (-2 * routeEBinaryHistogramBalancedMass m k) :=
      add_le_add hcomparison hbias
    _ = _ := by ring

/-- Arbitrary binary histogram version of the physical conditional parity-energy split. -/
theorem routeE_binary_componentHistory_gibbsParity_histogramEnergy_le
    (m : ℕ) (k : C → Bool → ℕ) (value : C → Bool → ℝ) (X H : ℝ)
    (hk : ∀ c, ∑ b, k c b = m + 1)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (haperture : ∀ x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k,
      ∀ r, routeEComponentSlotReceiver (fun _ : C => Bool) value x r ∈
        Set.Icc (X - H) (X + H)) :
    let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
    let physicalMean :=
      (∑ x : {x // x ∈ cell},
          routeEProductHistoryGibbsWeight X
              (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1) *
            ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
        (∑ x : {x // x ∈ cell},
          routeEProductHistoryGibbsWeight X
            (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1))
    let histogramBias :=
      ∏ c, ((1 : ℝ) - 2 * (k c true : ℝ) / ((m + 1 : ℕ) : ℝ))
    let curvatureDefect :=
      Real.exp (((m + 1 : ℕ) : ℝ) * H ^ 2 / (X * (X - H))) - 1
    physicalMean ^ 2 ≤ 2 * histogramBias ^ 2 + 2 * curvatureDefect ^ 2 := by
  dsimp only
  let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
  let physicalMean :=
    (∑ x : {x // x ∈ cell},
        routeEProductHistoryGibbsWeight X
            (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1) *
          ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
      (∑ x : {x // x ∈ cell},
        routeEProductHistoryGibbsWeight X
          (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1))
  let histogramBias :=
    ∏ c, ((1 : ℝ) - 2 * (k c true : ℝ) / ((m + 1 : ℕ) : ℝ))
  let curvatureDefect :=
    Real.exp (((m + 1 : ℕ) : ℝ) * H ^ 2 / (X * (X - H))) - 1
  have hcomparison : |physicalMean - histogramBias| ≤ curvatureDefect := by
    dsimp [physicalMean, histogramBias, curvatureDefect, cell]
    exact routeE_binary_componentHistory_gibbsParity_sub_histogramBias_le
      m k value X H hk hX hH hHX haperture
  have heta :
      0 ≤ ((m + 1 : ℕ) : ℝ) * H ^ 2 / (X * (X - H)) := by
    have hXH : 0 < X - H := sub_pos.mpr hHX
    positivity
  have hcurvature : 0 ≤ curvatureDefect := by
    dsimp [curvatureDefect]
    exact sub_nonneg.mpr (Real.one_le_exp heta)
  have hdefectSq : (physicalMean - histogramBias) ^ 2 ≤ curvatureDefect ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hcurvature).2 hcomparison
  nlinarith [sq_nonneg (physicalMean - 2 * histogramBias)]

/-- **All-order physical binary parity comparison.**  Component-histogram constraints force
equal receiver products, so no equal-product hypothesis remains.  The exact physical Gibbs mean
differs from the hostile uniform parity bias only by the quadratic aperture curvature defect. -/
theorem routeE_binary_componentHistory_gibbsParity_sub_bias_le
    (m : ℕ) (k : C → Bool → ℕ) (value : C → Bool → ℝ) (X H : ℝ)
    (hk : ∀ c, ∑ b, k c b = m + 1)
    (hone : ∀ c, k c true = 1)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (haperture : ∀ x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k,
      ∀ r, routeEComponentSlotReceiver (fun _ : C => Bool) value x r ∈
        Set.Icc (X - H) (X + H)) :
    let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
    |(∑ x : {x // x ∈ cell},
          routeEProductHistoryGibbsWeight X
              (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1) *
            ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
          (∑ x : {x // x ∈ cell},
            routeEProductHistoryGibbsWeight X
              (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1)) -
        ((1 : ℝ) - 2 / ((m + 1 : ℕ) : ℝ)) ^ Fintype.card C| ≤
      Real.exp (((m + 1 : ℕ) : ℝ) * H ^ 2 / (X * (X - H))) - 1 := by
  classical
  dsimp only
  let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
  have hcellCard : cell.card = (m + 1) ^ Fintype.card C :=
    routeE_binary_singleton_component_cell_card m k hk hone
  have hcellPos : 0 < cell.card := by
    rw [hcellCard]
    positivity
  let witness : {x // x ∈ cell} := ⟨Classical.choose (Finset.card_pos.mp hcellPos),
    Classical.choose_spec (Finset.card_pos.mp hcellPos)⟩
  letI : Nonempty {x // x ∈ cell} := ⟨witness⟩
  have hcompare := routeE_productHistoryGibbsMean_sub_uniformMean_le
    (Ω := {x // x ∈ cell}) (R := Fin (m + 1)) X H
    (fun x => routeEComponentSlotReceiver (fun _ : C => Bool) value x.1)
    (fun x => ∏ c, routeEBinaryPresenceCharacter (x.1 0 c))
    hX hH hHX
    (fun x r => haperture x.1 x.2 r)
    (fun x y => routeE_componentHistogramCell_receiver_product_eq
      (fun _ : C => Bool) k value x.2 y.2)
    (fun x => by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
        (fun c _ => by
          cases x.1 0 c <;> simp [routeEBinaryPresenceCharacter]))
  have huniform := routeE_binary_singleton_cell_subtype_character_mean m k hk hone
  rw [huniform] at hcompare
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hcompare

/-- **Physical conditional parity-energy endpoint.**  The squared Gibbs parity mean splits into
twice the exact binary histogram bias energy and twice the explicit all-order curvature energy.
This identifies, without a measure-change hypothesis, the two quantities an arithmetic producer
must make small. -/
theorem routeE_binary_componentHistory_gibbsParity_energy_le
    (m : ℕ) (k : C → Bool → ℕ) (value : C → Bool → ℝ) (X H : ℝ)
    (hk : ∀ c, ∑ b, k c b = m + 1)
    (hone : ∀ c, k c true = 1)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (haperture : ∀ x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k,
      ∀ r, routeEComponentSlotReceiver (fun _ : C => Bool) value x r ∈
        Set.Icc (X - H) (X + H)) :
    let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
    let physicalMean :=
      (∑ x : {x // x ∈ cell},
          routeEProductHistoryGibbsWeight X
              (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1) *
            ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
        (∑ x : {x // x ∈ cell},
          routeEProductHistoryGibbsWeight X
            (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1))
    let uniformBias := ((1 : ℝ) - 2 / ((m + 1 : ℕ) : ℝ)) ^ Fintype.card C
    let curvatureDefect :=
      Real.exp (((m + 1 : ℕ) : ℝ) * H ^ 2 / (X * (X - H))) - 1
    physicalMean ^ 2 ≤ 2 * uniformBias ^ 2 + 2 * curvatureDefect ^ 2 := by
  dsimp only
  let cell := routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k
  let physicalMean :=
    (∑ x : {x // x ∈ cell},
        routeEProductHistoryGibbsWeight X
            (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1) *
          ∏ c, routeEBinaryPresenceCharacter (x.1 0 c)) /
      (∑ x : {x // x ∈ cell},
        routeEProductHistoryGibbsWeight X
          (routeEComponentSlotReceiver (fun _ : C => Bool) value x.1))
  let uniformBias := ((1 : ℝ) - 2 / ((m + 1 : ℕ) : ℝ)) ^ Fintype.card C
  let curvatureDefect :=
    Real.exp (((m + 1 : ℕ) : ℝ) * H ^ 2 / (X * (X - H))) - 1
  have hcomparison : |physicalMean - uniformBias| ≤ curvatureDefect := by
    dsimp [physicalMean, uniformBias, curvatureDefect, cell]
    exact routeE_binary_componentHistory_gibbsParity_sub_bias_le
      m k value X H hk hone hX hH hHX haperture
  have heta :
      0 ≤ ((m + 1 : ℕ) : ℝ) * H ^ 2 / (X * (X - H)) := by
    have hXH : 0 < X - H := sub_pos.mpr hHX
    positivity
  have hcurvature : 0 ≤ curvatureDefect := by
    dsimp [curvatureDefect]
    exact sub_nonneg.mpr (Real.one_le_exp heta)
  have hdefectSq : (physicalMean - uniformBias) ^ 2 ≤ curvatureDefect ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hcurvature).2 hcomparison
  nlinarith [sq_nonneg (physicalMean - 2 * uniformBias)]

end BinaryPhysicalBias

end

end RHTower
