import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Central
import GaloisForLFunctions.HTGeometry.ActiveQuasiAbelianPalette
import GaloisForLFunctions.RHTower.ConstrainedProlateParityExactTransfer

/-!
# Exact Hermite parity floor evaluations and ratios

The normalized Hermite functions at the origin satisfy
```text
h_{2m}(0)^(2 : ℕ) = \sqrt{2} \binom{2m}{m} / 4^m = \sqrt{2} \cdot \text{normalizedCentralBinom}(m).
```

In the positive compressed-Fourier sector (modes 0 and 4, corresponding to $m=0$ and $m=2$),
the weight on the base mode is:
```text
h_0(0)^(2 : ℕ) / (h_0(0)^(2 : ℕ) + h_4(0)^(2 : ℕ)) = 1 / (1 + 3/8) = 8/11.
```

In the negative compressed-Fourier sector (modes 2 and 6, corresponding to $m=1$ and $m=3$),
the weight on the base mode is:
```text
h_2(0)^(2 : ℕ) / (h_2(0)^(2 : ℕ) + h_6(0)^(2 : ℕ)) = (1/2) / (1/2 + 5/16) = 8/13.
```

The ratio of the two sector coefficients is:
```text
(8/11) / (8/13) = 13/11,
```
which matches the scale constant in `ccm_fuchsModel_parity_floor_scaled_ratio_tendsto`.
-/

namespace RHTower

/-- Normalized central binomial coefficient $\binom{2m}{m} / 4^m$. -/
noncomputable def normalizedCentralBinom (m : ℕ) : ℝ :=
  (Nat.centralBinom m : ℝ) / (4 ^ m : ℝ)

theorem normalizedCentralBinom_zero : normalizedCentralBinom 0 = 1 := by
  unfold normalizedCentralBinom
  norm_num [Nat.centralBinom, Nat.choose]

theorem normalizedCentralBinom_one : normalizedCentralBinom 1 = 1 / 2 := by
  unfold normalizedCentralBinom
  norm_num [Nat.centralBinom, Nat.choose]

theorem normalizedCentralBinom_two : normalizedCentralBinom 2 = 3 / 8 := by
  unfold normalizedCentralBinom
  norm_num [Nat.centralBinom, Nat.choose]

theorem normalizedCentralBinom_three : normalizedCentralBinom 3 = 5 / 16 := by
  unfold normalizedCentralBinom
  norm_num [Nat.centralBinom, Nat.choose]

/-- Model squared Hermite evaluation at origin for index `2m`. -/
noncomputable def hermiteOriginSq (m : ℕ) : ℝ :=
  Real.sqrt 2 * normalizedCentralBinom m

theorem hermiteOriginSq_zero : hermiteOriginSq 0 = Real.sqrt 2 := by
  unfold hermiteOriginSq
  rw [normalizedCentralBinom_zero, mul_one]

theorem hermiteOriginSq_one : hermiteOriginSq 1 = Real.sqrt 2 / 2 := by
  unfold hermiteOriginSq
  rw [normalizedCentralBinom_one]
  ring

theorem hermiteOriginSq_two : hermiteOriginSq 2 = 3 * Real.sqrt 2 / 8 := by
  unfold hermiteOriginSq
  rw [normalizedCentralBinom_two]
  ring

theorem hermiteOriginSq_three : hermiteOriginSq 3 = 5 * Real.sqrt 2 / 16 := by
  unfold hermiteOriginSq
  rw [normalizedCentralBinom_three]
  ring

/-- Positive-sector two-mode Hermite floor ratio: $m=0$ versus $m=2$ gives $8/11$. -/
theorem positive_sector_hermite_floor_ratio_eq :
    hermiteOriginSq 0 / (hermiteOriginSq 0 + hermiteOriginSq 2) = 8 / 11 := by
  rw [hermiteOriginSq_zero, hermiteOriginSq_two]
  have hnum : Real.sqrt 2 + 3 * Real.sqrt 2 / 8 = 11 * Real.sqrt 2 / 8 := by ring
  rw [hnum]
  field_simp

/-- Negative-sector two-mode Hermite floor ratio: $m=1$ versus $m=3$ gives $8/13$. -/
theorem negative_sector_hermite_floor_ratio_eq :
    hermiteOriginSq 1 / (hermiteOriginSq 1 + hermiteOriginSq 3) = 8 / 13 := by
  rw [hermiteOriginSq_one, hermiteOriginSq_three]
  have hnum : Real.sqrt 2 / 2 + 5 * Real.sqrt 2 / 16 = 13 * Real.sqrt 2 / 16 := by ring
  rw [hnum]
  field_simp
  ring

/-- Exact ratio of the positive and negative sector floor weights: $(8/11) / (8/13) = 13/11$. -/
theorem parity_floor_weight_ratio_eq :
    (hermiteOriginSq 0 / (hermiteOriginSq 0 + hermiteOriginSq 2)) /
      (hermiteOriginSq 1 / (hermiteOriginSq 1 + hermiteOriginSq 3)) = 13 / 11 := by
  rw [positive_sector_hermite_floor_ratio_eq, negative_sector_hermite_floor_ratio_eq]
  norm_num

/-- Scaled parity ratio constant factor: $(8/11) \cdot (A_4 / A_6) / (8/13) = 13 A_4 / (11 A_6)$. -/
theorem parity_floor_fuchs_constant_ratio_eq (A4 A6 : ℝ) (hA6 : A6 ≠ 0) :
    (8 / 11 * A4) / (8 / 13 * A6) = 13 * A4 / (11 * A6) := by
  field_simp

end RHTower
