import GaloisForLFunctions.ArithmeticPositiveDuality.NormalizedQuartetRelocation
import GaloisForLFunctions.ArithmeticPositiveDuality.TheUnitCellTraceOfZeroRelocation
import GaloisForLFunctions.ArithmeticPositiveDuality.PowerSumDensitiesAndRationalMellinFactors
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem

/-!
# An actual normalized relocation has a signed density

Hardy's theorem supplies two distinct critical-line donor pairs. The explicit
quartet preserves the rational multiplier at zero and one. Its literal Mellin
density is eventually positive at integers and negative at their midpoints.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology MeasureTheory RHTower

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Two distinct positive critical-line donor ordinates exist without a simplicity assumption. -/
theorem exists_two_critical_donor_ordinates :
    ∃ γ₁ γ₂ : ℝ, 1 < γ₁ ∧ γ₁ < γ₂ ∧
      riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0 := by
  obtain ⟨T₀, _, hT⟩ := exists_riemannZeta_line_zero_dyadic
  let T := max T₀ 2
  have hT₂ : (2 : ℝ) ≤ T := le_max_right _ _
  have hT₀T : T₀ ≤ T := le_max_left _ _
  obtain ⟨γ₁, hγ₁, hz₁⟩ := hT T hT₀T
  obtain ⟨γ₂, hγ₂, hz₂⟩ := hT (4 * T) (by linarith only [hT₀T, hT₂])
  refine ⟨γ₁, γ₂, ?_, ?_, ?_, ?_⟩
  · linarith only [hγ₁.1, hT₂]
  · linarith only [hγ₁.2, hγ₂.1, hT₂]
  · simpa [linePt] using hz₁
  · simpa [linePt] using hz₂

theorem criticalPairDensity_eq_cellKernel {γ : ℝ}
    (hz : riemannZeta (1 / 2 + (γ : ℂ) * I) = 0)
    (N : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    criticalPairDensity γ ((N : ℝ) + θ) = criticalPairCellKernel γ N θ := by
  have hf : ⌊(N : ℝ) + θ⌋₊ = N := by
    apply (Nat.floor_eq_iff (by positivity : 0 ≤ (N : ℝ) + θ)).mpr
    constructor <;> linarith only [hθ, hθ1]
  simp only [criticalPairDensity, integerPowerDensity, hf, Complex.ofReal_add,
    Complex.ofReal_natCast, criticalPairCellKernel, zeroPowerSumCellKernel, hz, sub_zero]

/-- At actual donor zeros the regularized cell kernel is the literal density. -/
theorem quartetDensity_eq_cellDefect {γ₁ γ₂ : ℝ}
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0)
    (c : ℝ) (N : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    quartetDensity γ₁ γ₂ c ((N : ℝ) + θ) = quartetCellDefect γ₁ γ₂ c N θ := by
  rw [quartetDensity, quartetCellDefect,
    criticalPairDensity_eq_cellKernel hz₁ N hθ hθ1,
    criticalPairDensity_eq_cellKernel hz₂ N hθ hθ1]

/-- The donor quartic is the product of its two real quadratic factors. -/
theorem zeroRelocationDen_eq_pair_product (γ₁ γ₂ : ℝ) (s : ℂ) :
    zeroRelocationDen γ₁ γ₂ s =
      ((s - 1 / 2) ^ 2 + (γ₁ : ℂ) ^ 2) * ((s - 1 / 2) ^ 2 + (γ₂ : ℂ) ^ 2) := by
  apply Complex.ext <;>
    simp [zeroRelocationDen, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- The explicit signed density realizes the difference from the original zeta function. -/
theorem mellin_normalizedRelocationDensity {γ₁ γ₂ : ℝ}
    (hγ₁ : 1 < γ₁) (hγ₂ : γ₁ < γ₂) {s : ℂ} (hs : 1 < s.re) :
    (∫ Y in Set.Ioi (1 : ℝ), (Y : ℂ) ^ (-s) *
      (quartetDensity γ₁ γ₂ (normalizedRelocationTrace γ₁ γ₂) Y : ℂ)) =
      riemannZeta s *
        (zeroRelocationFactor (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂ s - 1) := by
  rw [mellin_quartetDensity (by linarith only [hγ₁]) hγ₂ _ hs,
    normalizedRelocation_factor_eq hγ₁ (hγ₁.trans hγ₂) (by linarith only [hs]),
    zeroRelocationDen_eq_pair_product]
  ring

/-- The normalized density changes sign in every sufficiently large unit interval. -/
theorem eventually_normalizedRelocationDensity_opposite_signs {γ₁ γ₂ : ℝ}
    (hγ₁ : 1 < γ₁) (hγ₂ : γ₁ < γ₂)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0) :
    ∀ᶠ N : ℕ in atTop,
      0 < quartetDensity γ₁ γ₂ (normalizedRelocationTrace γ₁ γ₂) N ∧
        quartetDensity γ₁ γ₂ (normalizedRelocationTrace γ₁ γ₂) ((N : ℝ) + 1 / 2) < 0 := by
  filter_upwards [eventually_quartetCellDefect_opposite_signs
    (by linarith only [hγ₁] : 0 < γ₁) hγ₂
    (normalizedRelocationTrace_neg hγ₁ (hγ₁.trans hγ₂))] with N hN
  constructor
  · have he := quartetDensity_eq_cellDefect hz₁ hz₂
      (normalizedRelocationTrace γ₁ γ₂) N (θ := 0) le_rfl (by norm_num)
    simp only [add_zero] at he
    rw [he]
    exact hN.1
  · rw [quartetDensity_eq_cellDefect hz₁ hz₂ _ N (by norm_num) (by norm_num)]
    exact hN.2

/-- The literal density has a uniform cubic error after its Bernoulli term. -/
theorem exists_uniform_quartetDensity_cell_remainder {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0) (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
      |(N : ℝ) ^ 2 * quartetDensity γ₁ γ₂ c ((N : ℝ) + θ) +
        c * unitCellBernoulli θ / 2| ≤ C / (N : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_quartetCellDefect_remainder hγ₁ hγ₂ c
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with N hN
  intro θ hθ hθ1
  rw [quartetDensity_eq_cellDefect hz₁ hz₂ c N hθ hθ1]
  exact hN θ ⟨hθ, hθ1.le⟩

/-- On a unit interval the Bernoulli profile has absolute value at most `1/6`. -/
theorem abs_unitCellBernoulli_le {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    |unitCellBernoulli θ| ≤ 1 / 6 := by
  rw [abs_le]
  have hp := mul_nonneg hθ (sub_nonneg.mpr hθ1)
  dsimp only [unitCellBernoulli]
  constructor
  · nlinarith only [sq_nonneg (θ - 1 / 2)]
  · nlinarith only [hp]

/-- The lattice expansion gives a genuine inverse-square bound at every large real cutoff. -/
theorem exists_quartetDensity_inverse_square_bound {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0) (c : ℝ) :
    ∃ A X : ℝ, 0 ≤ A ∧ 1 ≤ X ∧ ∀ Y : ℝ, X ≤ Y →
      |quartetDensity γ₁ γ₂ c Y| ≤ A / Y ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_quartetDensity_cell_remainder hγ₁ hγ₂ hz₁ hz₂ c
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hb
  let K := C + |c| / 12
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨4 * K, (N₀ : ℝ) + 2, by positivity, ?_, ?_⟩
  · have hN₀nonneg : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
    linarith only [hN₀nonneg]
  intro Y hY
  have hYpos : 0 < Y := by
    have hN₀nonneg : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
    linarith only [hY, hN₀nonneg]
  let N := ⌊Y⌋₊
  let θ := Y - (N : ℝ)
  have hfloor : (N : ℝ) ≤ Y := Nat.floor_le hYpos.le
  have htop : Y < (N : ℝ) + 1 := Nat.lt_floor_add_one Y
  have hN₀le : N₀ ≤ N := by
    exact_mod_cast (by linarith only [hY, htop] : (N₀ : ℝ) ≤ N)
  have hN : 1 ≤ N := by
    have hN₀nonneg : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
    exact_mod_cast (by linarith only [hY, htop, hN₀nonneg] : (1 : ℝ) ≤ N)
  have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hnR
  have hθ : 0 ≤ θ := sub_nonneg.mpr hfloor
  have hθ1 : θ < 1 := by dsimp only [θ]; linarith only [htop]
  have hYeq : (N : ℝ) + θ = Y := by dsimp only [θ]; ring
  have htrace := hN₀ N hN₀le θ hθ hθ1
  rw [hYeq] at htrace
  have hBern : |c * unitCellBernoulli θ / 2| ≤ |c| / 12 := by
    rw [abs_div, abs_mul]
    have hp := mul_le_mul_of_nonneg_left (abs_unitCellBernoulli_le hθ hθ1.le) (abs_nonneg c)
    calc
      _ ≤ (|c| * (1 / 6)) / |(2 : ℝ)| := div_le_div_of_nonneg_right hp (abs_nonneg _)
      _ = _ := by norm_num; ring
  have hCN : C / (N : ℝ) ≤ C := by
    apply (div_le_iff₀ hnpos).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hnR hC
  have hscaled : (N : ℝ) ^ 2 * |quartetDensity γ₁ γ₂ c Y| ≤ K := by
    have htri := norm_sub_le
      ((N : ℝ) ^ 2 * quartetDensity γ₁ γ₂ c Y + c * unitCellBernoulli θ / 2)
      (c * unitCellBernoulli θ / 2)
    simp only [add_sub_cancel_right, Real.norm_eq_abs] at htri
    rw [abs_mul, abs_of_nonneg (sq_nonneg (N : ℝ))] at htri
    calc
      _ ≤ |(N : ℝ) ^ 2 * quartetDensity γ₁ γ₂ c Y + c * unitCellBernoulli θ / 2| +
          |c * unitCellBernoulli θ / 2| := htri
      _ ≤ C / (N : ℝ) + |c| / 12 := add_le_add htrace hBern
      _ ≤ K := add_le_add hCN le_rfl
  have hYN : Y ≤ 2 * (N : ℝ) := by linarith only [htop, hnR]
  have hYsq : Y ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by
    nlinarith only [pow_le_pow_left₀ hYpos.le hYN 2]
  apply (le_div_iff₀ (sq_pos_of_pos hYpos)).mpr
  calc
    _ = Y ^ 2 * |quartetDensity γ₁ γ₂ c Y| := mul_comm _ _
    _ ≤ (4 * (N : ℝ) ^ 2) * |quartetDensity γ₁ γ₂ c Y| :=
      mul_le_mul_of_nonneg_right hYsq (abs_nonneg _)
    _ = 4 * ((N : ℝ) ^ 2 * |quartetDensity γ₁ γ₂ c Y|) := by ring
    _ ≤ 4 * K := mul_le_mul_of_nonneg_left hscaled (by norm_num)

/-- Actual critical-line zeros yield an endpoint-normalized off-line quartet with
an explicit Mellin density of both signs. -/
theorem exists_normalizedRelocation_signed_density :
    ∃ γ₁ γ₂ : ℝ, 1 < γ₁ ∧ γ₁ < γ₂ ∧
      riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0 ∧
      0 < normalizedRelocationHeight γ₁ γ₂ ∧ normalizedRelocationTrace γ₁ γ₂ < 0 ∧
      zeroRelocationFactor (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂ 0 = 1 ∧
      zeroRelocationFactor (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂ 1 = 1 ∧
      (∀ s : ℂ, 1 < s.re →
        (∫ Y in Set.Ioi (1 : ℝ), (Y : ℂ) ^ (-s) *
          (quartetDensity γ₁ γ₂ (normalizedRelocationTrace γ₁ γ₂) Y : ℂ)) =
          riemannZeta s *
            (zeroRelocationFactor (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂ s - 1)) ∧
      ∀ᶠ N : ℕ in atTop,
        0 < quartetDensity γ₁ γ₂ (normalizedRelocationTrace γ₁ γ₂) N ∧
          quartetDensity γ₁ γ₂ (normalizedRelocationTrace γ₁ γ₂) ((N : ℝ) + 1 / 2) < 0 := by
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hz₁, hz₂⟩ := exists_two_critical_donor_ordinates
  obtain ⟨h₀, h₁⟩ := normalizedRelocation_endpoints hγ₁ (hγ₁.trans hγ₂)
  exact ⟨γ₁, γ₂, hγ₁, hγ₂, hz₁, hz₂,
    normalizedRelocationHeight_pos hγ₁ (hγ₁.trans hγ₂),
    normalizedRelocationTrace_neg hγ₁ (hγ₁.trans hγ₂), h₀, h₁,
    fun _ hs => mellin_normalizedRelocationDensity hγ₁ hγ₂ hs,
    eventually_normalizedRelocationDensity_opposite_signs hγ₁ hγ₂ hz₁ hz₂⟩

#print axioms exists_two_critical_donor_ordinates
#print axioms exists_normalizedRelocation_signed_density

end GaloisForLFunctions.ArithmeticPositiveDuality
