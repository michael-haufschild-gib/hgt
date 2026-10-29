import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaFiniteMeanZeroOffDiagonal
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaCouplingUsesOnlyDetailMass

/-!
# All signed Haar Gamma cross terms cost ordinary mass

Mean cancellation pays each signed interaction from the positive boundary
remainders of its two cells. Summing disjoint target cells spends each row
remainder once. The exact Gamma error therefore costs ordinary Haar mass,
uniformly over the horizon and including every low index.
-/

noncomputable section
open MeasureTheory Set Filter
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open MeanZeroIntervals BiarithmeticGaugeGeometry HTGeometry

/-- The positive row remainders available to all actual Haar cross interactions. -/
def haarGammaBoundaryCost (d : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
    ∫ p : ℝ × ℝ, (d a * haarProfile a p.1) ^ 2
      ∂gammaRectangleRemainderMeasure
        (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
        (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ))

/-- All Gamma cross terms share the exact boundary cost, whose total uses only pair widths. -/
theorem haarGamma_error_and_boundary_bounds (d : ℕ → ℝ) (X : ℕ) :
    |levyEnergy (haarSectionProfile d X) -
        ∑ a ∈ Finset.Icc 1 X, d a ^ 2 * levyEnergy (haarProfile a)| ≤
      haarGammaBoundaryCost d X ∧
    haarGammaBoundaryCost d X ≤
      Real.exp (1 / 2) * ∑ a ∈ Finset.Icc 1 X, logCellWidth a * d a ^ 2 := by
  let S := Finset.Icc 1 X
  let L : S → ℝ := fun i => Real.log ((2 * (i : ℕ) : ℕ) : ℝ)
  let U : S → ℝ := fun i => Real.log ((2 * (i : ℕ) + 2 : ℕ) : ℝ)
  let f : S → ℝ → ℝ := fun i x => d i * haarProfile i x
  have hpos (i : S) : 1 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
  have hwidth (i : S) : U i - L i = logCellWidth (i : ℕ) := haarPairWidth (hpos i)
  have hab (i : S) : L i < U i := by
    apply sub_pos.mp
    rw [hwidth]
    exact logCellWidth_pos (hpos i)
  have hw (i : S) : U i - L i ≤ 1 := by
    rw [hwidth]
    have hi := hpos i
    exact (logCellWidth_le_inv hi).trans
      ((div_le_one (by positivity : (0 : ℝ) < (i : ℕ))).mpr (by exact_mod_cast hi))
  have hsep (i j : S) (hij : i ≠ j) : U i ≤ L j ∨ U j ≤ L i := by
    have hne : (i : ℕ) ≠ (j : ℕ) := fun he => hij (Subtype.ext he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (Real.log_le_log (by positivity)
        (by exact_mod_cast (show 2 * (i : ℕ) + 2 ≤ 2 * (j : ℕ) by omega)))
    · exact Or.inr (Real.log_le_log (by positivity)
        (by exact_mod_cast (show 2 * (j : ℕ) + 2 ≤ 2 * (i : ℕ) by omega)))
  have hd : Pairwise (Function.onFun Disjoint (fun i : S => Ioo (L i) (U i))) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hx hy
    rcases hsep i j hij with h | h <;> linarith only [h, hx.1, hx.2, hy.1, hy.2]
  have hv (i : S) : BoundedVariationOn (f i) univ := bv_const_mul _ (haarProfile_bv i)
  have hc (i : S) : HasCompactSupport (f i) := (haarProfile_compact i).mul_left
  have hsum : (fun x => ∑ i : S, f i x) = haarSectionProfile d X := by
    funext x
    exact Finset.sum_coe_sort S (fun a => d a * haarProfile a x)
  have hsv : BoundedVariationOn (fun x => ∑ i : S, f i x) univ := by
    rw [hsum]
    exact haarSectionProfile_bv d X
  have hsc : HasCompactSupport (fun x => ∑ i : S, f i x) := by
    rw [hsum]
    exact haarSectionProfile_compact d X
  have hmean (i : S) : ∫ x in Ioo (L i) (U i), f i x = 0 := by
    change (∫ x in Ioo (L i) (U i), d i * haarProfile i x) = 0
    rw [integral_const_mul, setIntegral_haarProfile_pair (hpos i), mul_zero]
  have hb (i : S) (x : ℝ) : f i x ^ 2 ≤ d i ^ 2 := by
    have ha := abs_haarProfile_le_one (hpos i) x
    have hm := mul_nonneg (sub_nonneg.mpr ha)
      (show 0 ≤ 1 + |haarProfile i x| by positivity)
    have hs : haarProfile i x ^ 2 ≤ 1 := by nlinarith only [hm, sq_abs (haarProfile i x)]
    simpa only [f, mul_pow, mul_one] using mul_le_mul_of_nonneg_left hs (sq_nonneg (d i))
  have hs (i : S) : ∀ᵐ x ∂volume, x ∉ Ioo (L i) (U i) → f i x = 0 := by
    filter_upwards [Measure.ae_ne volume (L i)] with x hx
    intro hout
    change d i * haarProfile i x = 0
    rw [haarProfile_zero_outside_pair (hpos i), mul_zero]
    intro hin
    exact hout ⟨lt_of_le_of_ne hin.1 (Ne.symm hx), hin.2⟩
  have hdiag : (∑ i : S, levyEnergy (f i)) =
      ∑ a ∈ Finset.Icc 1 X, d a ^ 2 * levyEnergy (haarProfile a) := by
    simp only [f, levyEnergy_const_mul]
    exact Finset.sum_coe_sort S (fun a => d a ^ 2 * levyEnergy (haarProfile a))
  have hcost : (∑ i : S, ∑ j : S, ∫ p : ℝ × ℝ, f i p.1 ^ 2
      ∂gammaRectangleRemainderMeasure (L i) (U i) (L j) (U j)) =
      haarGammaBoundaryCost d X := by
    let R : ℕ → ℕ → ℝ := fun a b => ∫ p : ℝ × ℝ, (d a * haarProfile a p.1) ^ 2
      ∂gammaRectangleRemainderMeasure
        (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
        (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ))
    change (∑ i : S, ∑ j : S, R i j) = ∑ a ∈ S, ∑ b ∈ S, R a b
    calc
      _ = ∑ i : S, ∑ b ∈ S, R i b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_coe_sort S (R i)
      _ = _ := Finset.sum_coe_sort S (fun a => ∑ b ∈ S, R a b)
  constructor
  · have he := abs_levyEnergy_sum_sub_diagonal_le_remainders L U (fun i : S => d i ^ 2) f
      hab hw hsep hv hc hsv hsc hmean hb hs
    rwa [hsum, hdiag, hcost] at he
  · rw [← hcost, ← Finset.sum_coe_sort S (fun a => logCellWidth a * d a ^ 2), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hm : Measurable (f i) := measurable_const.mul (measurable_haarProfile i)
    have he := sum_gammaRectangle_remainder_sq_le (hab i) (hw i) L U hd
      hm (sq_nonneg (d i)) (hb i)
    simpa only [hwidth, mul_assoc] using he

/-- The full signed Gamma error is controlled by ordinary pair-width mass. -/
theorem haarSectionProfile_gamma_error_le_width (d : ℕ → ℝ) (X : ℕ) :
    |levyEnergy (haarSectionProfile d X) -
        ∑ a ∈ Finset.Icc 1 X, d a ^ 2 * levyEnergy (haarProfile a)| ≤
      Real.exp (1 / 2) * ∑ a ∈ Finset.Icc 1 X, logCellWidth a * d a ^ 2 :=
  (haarGamma_error_and_boundary_bounds d X).1.trans (haarGamma_error_and_boundary_bounds d X).2

/-- Every signed Haar Gamma interaction costs ordinary square mass, with no removed head. -/
theorem haarSectionProfile_gamma_error_le_mass (d : ℕ → ℝ) (X : ℕ) :
    |levyEnergy (haarSectionProfile d X) -
        ∑ a ∈ Finset.Icc 1 X, d a ^ 2 * levyEnergy (haarProfile a)| ≤
      16 * Real.exp (1 / 2) * ∫ x, haarSectionProfile d X x ^ 2 := by
  refine (haarSectionProfile_gamma_error_le_width d X).trans ?_
  rw [integral_haarSectionProfile_sq, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hw := logCellWidth_le_sixteen_haarMass (Finset.mem_Icc.mp ha).1
  calc
    _ ≤ Real.exp (1 / 2) * ((16 * haarMass a) * d a ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw (sq_nonneg _)) (Real.exp_pos _).le
    _ = _ := by ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
