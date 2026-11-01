import GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheFullResolvent
import GaloisForLFunctions.HTGeometry.HermitianSpectralWindowBounds
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheMultiscaleProjectionBound

/-!
# The excited resolvent of a finite flip

Write `E_i` for the energies `log N − λ_i` of the full prime matrix, `e_i` for its eigenbasis and
`Q_N(w) = (log N − γ)|w|² − ⟨P_N w, w⟩ = Σ_i (E_i − γ) ⟨w, e_i⟩²` (`primeEnergy_eq_sum`).

* **The ground** (`eventually_exists_ground`): for `0 < t < 2 log 2`, eventually there is an index
  `i₀` with `|E_{i₀} − γ| ≤ ε` and `E_i ≥ γ + t` for all `i ≠ i₀` (`IsGroundBelow`).
* **Coercivity and Cauchy–Schwarz off the ground** (`primeEnergy_sub_ge_of_perp`,
  `inner_sq_le_excited`): for `w ⊥ e_{i₀}` and `s < t`, `Q_N(w) − s|w|² ≥ (t − s)|w|²` and
  `⟨w, v⟩² ≤ ρ_{i₀}(v) (Q_N(w) − s|w|²)`, with the **excited resolvent**
  `ρ_{i₀}(v) = Σ_{i ≠ i₀} ⟨v, e_i⟩²/(E_i − γ − s)`.
* **Finite flips** (`eventually_excitedResolvent_finiteFlip_le`): for a finite prime set `F`,
  `ρ_{i₀}(v_F) → δ_F² W_F(s)`, `W_F(s) = Σ_{m≥2} w_F(m)/(E_m − γ − s)`: the full resolvent tends to
  `δ_F²(−1/s + W_F(s))` and the ground term to `−δ_F²/s`.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (PrimeHorizonIndex fullPrimeMatrix
  fullPrimeMatrix_isHermitian fullPrimeEnergyEigenvalue fullPrimeEnergySublevel)
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (ramanujanAdjunctionEnergy_one)

local notation "γ" => Real.eulerMascheroniConstant

/-- The eigenvectors of the full prime matrix. -/
abbrev primeEigen (N : ℕ) (i : PrimeHorizonIndex N) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (fullPrimeMatrix_isHermitian N).eigenvectorBasis i

/-- The renormalized prime energy `Q_N(w) = (log N − γ)|w|² − ⟨P_N w, w⟩`. -/
def primeEnergy (N : ℕ) (w : EuclideanSpace ℝ (PrimeHorizonIndex N)) : ℝ :=
  (Real.log N - γ) * ‖w‖ ^ 2 - ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) w, w⟫

theorem primeEnergy_eq_sum (N : ℕ) (w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeEnergy N w = ∑ i, (fullPrimeEnergyEigenvalue N i - γ) * ⟪w, primeEigen N i⟫ ^ 2 := by
  unfold primeEnergy
  rw [HTGeometry.shiftedHermitianEnergy_eq_sum (fullPrimeMatrix_isHermitian N)]
  refine sum_congr rfl fun i _ => ?_
  unfold fullPrimeEnergyEigenvalue
  ring

theorem norm_sq_eq_sum_eigen (N : ℕ) (w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ‖w‖ ^ 2 = ∑ i, ⟪w, primeEigen N i⟫ ^ 2 := by
  rw [← (fullPrimeMatrix_isHermitian N).eigenvectorBasis.sum_sq_inner_left w]
  exact sum_congr rfl fun i _ => by rw [real_inner_comm]

theorem inner_eq_sum_eigen (N : ℕ) (w v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪w, v⟫ = ∑ i, ⟪w, primeEigen N i⟫ * ⟪v, primeEigen N i⟫ := by
  rw [← (fullPrimeMatrix_isHermitian N).eigenvectorBasis.sum_inner_mul_inner w v]
  exact sum_congr rfl fun i _ => by rw [real_inner_comm v]

/-- `i₀` is the only index whose energy lies below `γ + t`. -/
def IsGroundBelow (N : ℕ) (t : ℝ) (i₀ : PrimeHorizonIndex N) : Prop :=
  ∀ i, i ≠ i₀ → γ + t ≤ fullPrimeEnergyEigenvalue N i

/-- `Q_N(w) − s|w|² = Σ_i (E_i − γ − s)⟨w, e_i⟩²`. -/
theorem primeEnergy_sub_eq_sum (N : ℕ) (s : ℝ) (w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeEnergy N w - s * ‖w‖ ^ 2 =
      ∑ i, (fullPrimeEnergyEigenvalue N i - γ - s) * ⟪w, primeEigen N i⟫ ^ 2 := by
  rw [primeEnergy_eq_sum, norm_sq_eq_sum_eigen, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- **Coercivity off the ground**: `(t − s)|w|² ≤ Q_N(w) − s|w|²` for `w ⊥ e_{i₀}`. -/
theorem primeEnergy_sub_ge_of_perp {N : ℕ} {t s : ℝ} {i₀ : PrimeHorizonIndex N}
    (hg : IsGroundBelow N t i₀) {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hw : ⟪w, primeEigen N i₀⟫ = 0) :
    (t - s) * ‖w‖ ^ 2 ≤ primeEnergy N w - s * ‖w‖ ^ 2 := by
  rw [primeEnergy_sub_eq_sum, norm_sq_eq_sum_eigen, mul_sum]
  refine sum_le_sum fun i _ => ?_
  by_cases hi : i = i₀
  · subst hi; rw [hw]; simp
  · exact mul_le_mul_of_nonneg_right (by linarith [hg i hi]) (sq_nonneg _)

/-- The **excited resolvent** `Σ_{i ≠ i₀} ⟨v, e_i⟩²/(E_i − γ − s)`. -/
def excitedResolvent (N : ℕ) (s : ℝ) (i₀ : PrimeHorizonIndex N)
    (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) : ℝ :=
  ∑ i ∈ univ.erase i₀, ⟪v, primeEigen N i⟫ ^ 2 / (fullPrimeEnergyEigenvalue N i - γ - s)

/-- **Cauchy–Schwarz off the ground**: `⟨w, v⟩² ≤ ρ_{i₀}(v) (Q_N(w) − s|w|²)` for `w ⊥ e_{i₀}`. -/
theorem inner_sq_le_excited {N : ℕ} {t s : ℝ} {i₀ : PrimeHorizonIndex N}
    (hg : IsGroundBelow N t i₀) (hst : s < t) {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hw : ⟪w, primeEigen N i₀⟫ = 0) (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪w, v⟫ ^ 2 ≤ excitedResolvent N s i₀ v * (primeEnergy N w - s * ‖w‖ ^ 2) := by
  set d : PrimeHorizonIndex N → ℝ := fun i => fullPrimeEnergyEigenvalue N i - γ - s
  have hd : ∀ i ∈ univ.erase i₀, 0 < d i := fun i hi => by
    have := hg i (ne_of_mem_erase hi); simp only [d]; linarith
  have hsplit : ⟪w, v⟫ = ∑ i ∈ univ.erase i₀, ⟪w, primeEigen N i⟫ * ⟪v, primeEigen N i⟫ := by
    rw [inner_eq_sum_eigen, ← add_sum_erase _ _ (mem_univ i₀), hw, zero_mul, zero_add]
  have henergy : primeEnergy N w - s * ‖w‖ ^ 2 =
      ∑ i ∈ univ.erase i₀, d i * ⟪w, primeEigen N i⟫ ^ 2 := by
    rw [primeEnergy_sub_eq_sum, ← add_sum_erase _ _ (mem_univ i₀), hw]
    simp [d]
  have hcs := sq_sum_weighted_le (univ.erase i₀) (fun i => 1 / d i)
    (fun i => d i * ⟪w, primeEigen N i⟫) (fun i => ⟪v, primeEigen N i⟫)
    (fun i hi => (one_div_pos.mpr (hd i hi)).le)
  have e1 : ∑ i ∈ univ.erase i₀, 1 / d i * (d i * ⟪w, primeEigen N i⟫) * ⟪v, primeEigen N i⟫ =
      ∑ i ∈ univ.erase i₀, ⟪w, primeEigen N i⟫ * ⟪v, primeEigen N i⟫ :=
    sum_congr rfl fun i hi => by have := (hd i hi).ne'; field_simp
  have e2 : ∑ i ∈ univ.erase i₀, 1 / d i * (d i * ⟪w, primeEigen N i⟫) ^ 2 =
      ∑ i ∈ univ.erase i₀, d i * ⟪w, primeEigen N i⟫ ^ 2 :=
    sum_congr rfl fun i hi => by have := (hd i hi).ne'; field_simp
  have e3 : ∑ i ∈ univ.erase i₀, 1 / d i * ⟪v, primeEigen N i⟫ ^ 2 = excitedResolvent N s i₀ v :=
    sum_congr rfl fun i _ => by simp only [d]; ring
  rw [e1, e2, e3] at hcs
  rw [hsplit, henergy, mul_comm]
  exact hcs

/-- The ground index of a sublevel of size one. -/
theorem isGroundBelow_of_card_one {N : ℕ} {t : ℝ} {i₀ : PrimeHorizonIndex N}
    (hc : (fullPrimeEnergySublevel N (γ + t)).card = 1)
    (hi₀ : fullPrimeEnergyEigenvalue N i₀ < γ + t) : IsGroundBelow N t i₀ := by
  intro i hi
  have hmem : i₀ ∈ fullPrimeEnergySublevel N (γ + t) := mem_filter.mpr ⟨mem_univ _, hi₀⟩
  by_contra hlt
  rw [not_le] at hlt
  exact hi ((card_le_one_iff.mp hc.le) (mem_filter.mpr ⟨mem_univ _, hlt⟩) hmem)

private theorem shift_eventually {P : ℕ → Prop} (h : ∀ᶠ N : ℕ in atTop, P (N + 1)) :
    ∀ᶠ N : ℕ in atTop, P N := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  refine eventually_atTop.mpr ⟨N₀ + 1, fun N hN => ?_⟩
  have := hN₀ (N - 1) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at this

private theorem finiteFlipConductorCoefficient_one' (F : Finset ℕ) :
    finiteFlipConductorCoefficient F 1 = finiteFlipHarmonicDensity F := by
  simp only [finiteFlipConductorCoefficient, (finiteFlipMobius_isMultiplicative F).map_one,
    Nat.totient_one, Nat.cast_one, Real.sqrt_one, mul_one, div_one]

/-- **The ground eigenline.** For `0 < t < 2 log 2` and `ε > 0`, eventually there is an index `i₀`
with `|E_{i₀} − γ| ≤ ε` and every other energy at least `γ + t`. -/
theorem eventually_exists_ground {t : ℝ} (ht : 0 < t) (ht2 : t < 2 * Real.log 2) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ i₀ : PrimeHorizonIndex N, IsGroundBelow N t i₀ ∧
      |fullPrimeEnergyEigenvalue N i₀ - γ| ≤ ε := by
  obtain ⟨idx, hE, -⟩ := exists_finiteFlip_conductor_eigenline (∅ : Finset ℕ) (by simp)
    (by norm_num : 0 < 1)
  rw [ramanujanAdjunctionEnergy_one] at hE
  have hE' := (hE.sub_const γ)
  rw [sub_self] at hE'
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hnear := hE'.eventually (Metric.closedBall_mem_nhds (0 : ℝ) (lt_min hε (half_pos ht)))
  have hcount := hshift.eventually (eventually_fullPrime_ground_count_one ht ht2)
  refine shift_eventually ?_
  filter_upwards [hnear, hcount] with N hN hc
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hN
  have hlt : fullPrimeEnergyEigenvalue (N + 1) (idx N) < γ + t := by
    have := (abs_le.mp (hN.trans (min_le_right _ _))).2; linarith
  exact ⟨idx N, isGroundBelow_of_card_one hc hlt, hN.trans (min_le_left _ _)⟩

/-- **The excited resolvent of a finite flip.** For `0 < s < t < 2 log 2` and `ε > 0`, eventually,
for every ground index `i₀` below `γ + t`, `ρ_{i₀}(v_F) ≤ δ_F² (Λ_F(s) + 1/s) + ε`, where
`Λ_F = finiteFlipSecular F`. -/
theorem eventually_excitedResolvent_finiteFlip_le (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht2 : t < 2 * Real.log 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ i₀ : PrimeHorizonIndex N, IsGroundBelow N t i₀ →
      excitedResolvent N s i₀ (finiteFlipHorizonVector F N) ≤
        finiteFlipHarmonicDensity F ^ 2 * (finiteFlipSecular F s + 1 / s) + ε := by
  have hs2 : s < 2 * Real.log 2 := hst.trans ht2
  obtain ⟨idx, hE, ha⟩ := exists_finiteFlip_conductor_eigenline F hF (by norm_num : 0 < 1)
  rw [ramanujanAdjunctionEnergy_one] at hE
  rw [finiteFlipConductorCoefficient_one'] at ha
  have hR := tendsto_finiteFlipFiniteResolvent F hF hs hs2
  set δ := finiteFlipHarmonicDensity F
  -- the ground term `⟨v, e_{idx}⟩²/(E_{idx} − γ − s) → −δ²/s`
  have hden : Tendsto (fun N : ℕ => fullPrimeEnergyEigenvalue (N + 1) (idx N) - γ - s) atTop
      (𝓝 (-s)) := by
    have := (hE.sub_const γ).sub_const s; rwa [sub_self, zero_sub] at this
  have hground := ha.div hden (by linarith)
  have hlim := hR.sub hground
  have hval : δ ^ 2 * finiteFlipSecular F s - δ ^ 2 / -s = δ ^ 2 * (finiteFlipSecular F s + 1 / s) := by
    field_simp; ring
  rw [hval] at hlim
  have hev := hlim.eventually (ge_mem_nhds (lt_add_of_pos_right _ hε))
  have hnear := (hE.sub_const γ).eventually (Metric.ball_mem_nhds (0 : ℝ) (show 0 < t by linarith))
  refine shift_eventually ?_
  filter_upwards [hev, hnear] with N hN hnN i₀ hg
  rw [sub_self] at hnN
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hnN
  -- the eigenline `idx N` is the ground `i₀`
  have hidx : idx N = i₀ := by
    by_contra hne
    have := hg (idx N) hne
    have := (abs_lt.mp hnN).2
    linarith
  subst hidx
  have hsplit : finiteFlipFiniteResolvent F (N + 1) s =
      ⟪finiteFlipHorizonVector F (N + 1), primeEigen (N + 1) (idx N)⟫ ^ 2 /
          (fullPrimeEnergyEigenvalue (N + 1) (idx N) - γ - s) +
        excitedResolvent (N + 1) s (idx N) (finiteFlipHorizonVector F (N + 1)) := by
    rw [finiteFlipFiniteResolvent, ← add_sum_erase _ _ (mem_univ (idx N))]
    rfl
  rw [hsplit] at hN
  linarith

end GaloisForLFunctions.RenormalizedIntersectionTheory
