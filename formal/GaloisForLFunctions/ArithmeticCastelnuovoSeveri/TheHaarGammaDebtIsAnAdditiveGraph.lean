import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHaarGammaCrossTermsArePositive
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHaarPrimeSourceRetainsItsDivisorSquares

/-!
# The exact additive graph in the signed Haar Gamma source

Positive rectangle couplings identify the complete Gamma matrix. In the
same ground coordinates as the divisor squares, its signed contribution
is a row potential minus a nonnegative additive graph energy. No head or
touching interaction is removed.
-/

noncomputable section
open MeasureTheory Set Filter
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open MeanZeroIntervals BiarithmeticGaugeGeometry HTGeometry

/-- The original Gamma form retains the positive matrix of all Haar cross terms. -/
theorem haarSectionProfile_gamma_eq_matrix (d : ℕ → ℝ) (X : ℕ) :
    levyEnergy (haarSectionProfile d X) =
      (∑ a ∈ Finset.Icc 1 X, levyEnergy (haarProfile a) * d a ^ 2) +
        ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
          haarGammaCoupling a b * d a * d b := by
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
    exact (logCellWidth_le_inv (hpos i)).trans
      ((div_le_one (by positivity : (0 : ℝ) < (i : ℕ))).mpr (by exact_mod_cast hi))
  have hsep (i j : S) (hij : i ≠ j) : U i ≤ L j ∨ U j ≤ L i := by
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (Real.log_le_log (by positivity)
        (by exact_mod_cast (show 2 * (i : ℕ) + 2 ≤ 2 * (j : ℕ) by omega)))
    · exact Or.inr (Real.log_le_log (by positivity)
        (by exact_mod_cast (show 2 * (j : ℕ) + 2 ≤ 2 * (i : ℕ) by omega)))
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
  have hb (i : S) (x : ℝ) : f i x ^ 2 ≤ d i ^ 2 := by
    have he := abs_haarProfile_le_one (hpos i) x
    have hm := mul_nonneg (sub_nonneg.mpr he)
      (show 0 ≤ 1 + |haarProfile i x| by positivity)
    have hs : haarProfile i x ^ 2 ≤ 1 := by nlinarith only [hm, sq_abs (haarProfile i x)]
    simpa only [f, mul_pow, mul_one] using mul_le_mul_of_nonneg_left hs (sq_nonneg (d i))
  have hs (i : S) : ∀ᵐ x ∂volume, x ∉ Ioo (L i) (U i) → f i x = 0 := by
    filter_upwards [Measure.ae_ne volume (L i)] with x hx
    intro hout
    change d i * haarProfile i x = 0
    rw [haarProfile_zero_outside_pair (hpos i), mul_zero]
    intro hin
    exact hout ⟨lt_of_le_of_ne hin.1 hx.symm, hin.2⟩
  have hdiag : (∑ i : S, levyEnergy (f i)) =
      ∑ a ∈ S, levyEnergy (haarProfile a) * d a ^ 2 := by
    simp only [f, levyEnergy_const_mul]
    rw [Finset.sum_coe_sort S (fun a => d a ^ 2 * levyEnergy (haarProfile a))]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  let R : ℕ → ℕ → ℝ := fun a b => haarGammaCoupling a b * d a * d b
  have hterm (i j : S) :
      (∫ p : ℝ × ℝ, f i p.1 * f j p.2
        ∂gammaRectangleMeasure (L i) (U i) (L j) (U j)) = -R i j := by
    have he : (fun p : ℝ × ℝ => f i p.1 * f j p.2) =
        fun p => (d i * d j) * (haarProfile i p.1 * haarProfile j p.2) := by
      funext p
      dsimp only [f]
      ring
    rw [he, integral_const_mul]
    change _ = -(-(∫ p : ℝ × ℝ, haarProfile i p.1 * haarProfile j p.2
      ∂gammaRectangleMeasure (L i) (U i) (L j) (U j)) * d i * d j)
    ring
  have hcross : (∑ i : S, ∑ j : S, ∫ p : ℝ × ℝ, f i p.1 * f j p.2
      ∂gammaRectangleMeasure (L i) (U i) (L j) (U j)) =
        -(∑ a ∈ S, ∑ b ∈ S, R a b) := by
    simp_rw [hterm, Finset.sum_neg_distrib]
    congr 1
    calc
      _ = ∑ i : S, ∑ b ∈ S, R i b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_coe_sort S (R i)
      _ = _ := Finset.sum_coe_sort S (fun a => ∑ b ∈ S, R a b)
  have he := levyEnergy_sum_eq_diagonal_sub_rectangles L U (fun i : S => d i ^ 2) f
    hab hw hsep hv hc hsv hsc hb hs
  rw [hsum, hdiag, hcross, sub_neg_eq_add] at he
  exact he

/-- Ground coordinates shared by the additive and multiplicative difference squares. -/
def haarGroundCoordinate (d : ℕ → ℝ) (a : ℕ) : ℝ :=
  Real.sqrt ((2 * a + 1 : ℕ) : ℝ) * d a

/-- The actual positive Gamma coupling in the divisor ground coordinates. -/
def haarGammaGraphWeight (a b : ℕ) : ℝ :=
  haarGammaCoupling a b /
    (Real.sqrt ((2 * a + 1 : ℕ) : ℝ) * Real.sqrt ((2 * b + 1 : ℕ) : ℝ))

theorem haarGammaGraphWeight_nonneg {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    0 ≤ haarGammaGraphWeight a b :=
  div_nonneg (haarGammaCoupling_nonneg ha hb) (by positivity)

theorem haarGammaGraphWeight_symm {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    haarGammaGraphWeight a b = haarGammaGraphWeight b a := by
  rw [haarGammaGraphWeight, haarGammaGraphWeight, haarGammaCoupling_symm ha hb,
    mul_comm (Real.sqrt ((2 * a + 1 : ℕ) : ℝ))]

/-- The exact diagonal and all positive row couplings before signed graph payment. -/
def haarGammaRowPotential (X a : ℕ) : ℝ :=
  levyEnergy (haarProfile a) / ((2 * a + 1 : ℕ) : ℝ) +
    ∑ b ∈ Finset.Icc 1 X, haarGammaGraphWeight a b

/-- The adverse signed Gamma contribution is an additive graph energy. -/
def haarGammaGraphEnergy (d : ℕ → ℝ) (X : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
    haarGammaGraphWeight a b * (haarGroundCoordinate d a - haarGroundCoordinate d b) ^ 2

theorem haarGammaGraphEnergy_nonneg (d : ℕ → ℝ) (X : ℕ) :
    0 ≤ haarGammaGraphEnergy d X := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact Finset.sum_nonneg fun a ha => Finset.sum_nonneg fun b hb =>
    mul_nonneg (haarGammaGraphWeight_nonneg (Finset.mem_Icc.mp ha).1
      (Finset.mem_Icc.mp hb).1) (sq_nonneg _)

private theorem haarGamma_diagonal_ground (d : ℕ → ℝ) (a : ℕ) :
    levyEnergy (haarProfile a) * d a ^ 2 =
      (levyEnergy (haarProfile a) / ((2 * a + 1 : ℕ) : ℝ)) * haarGroundCoordinate d a ^ 2 := by
  have hn : (0 : ℝ) < ((2 * a + 1 : ℕ) : ℝ) := by positivity
  rw [haarGroundCoordinate, mul_pow, Real.sq_sqrt hn.le]
  field_simp [hn.ne'] <;> ring

private theorem haarGamma_cross_ground (d : ℕ → ℝ) (a b : ℕ) :
    haarGammaCoupling a b * d a * d b =
      haarGammaGraphWeight a b * haarGroundCoordinate d a * haarGroundCoordinate d b := by
  have ha : Real.sqrt ((2 * a + 1 : ℕ) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < ((2 * a + 1 : ℕ) : ℝ))).ne'
  have hb : Real.sqrt ((2 * b + 1 : ℕ) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < ((2 * b + 1 : ℕ) : ℝ))).ne'
  rw [haarGammaGraphWeight, haarGroundCoordinate, haarGroundCoordinate]
  field_simp [ha, hb] <;> ring

/-- Exact signed Gamma decomposition in the original divisor ground coordinates. -/
theorem haarSectionProfile_gamma_eq_row_sub_graph (d : ℕ → ℝ) (X : ℕ) :
    levyEnergy (haarSectionProfile d X) =
      (∑ a ∈ Finset.Icc 1 X, haarGammaRowPotential X a * haarGroundCoordinate d a ^ 2) -
        haarGammaGraphEnergy d X := by
  let S := Finset.Icc 1 X
  let u := haarGroundCoordinate d
  let K := haarGammaGraphWeight
  have hrev : (∑ a ∈ S, ∑ b ∈ S, K a b * u b ^ 2) =
      ∑ a ∈ S, ∑ b ∈ S, K a b * u a ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [show K b a = K a b from haarGammaGraphWeight_symm
      (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp ha).1]
  have hexp : (∑ a ∈ S, ∑ b ∈ S, K a b * (u a - u b) ^ 2) =
      2 * (∑ a ∈ S, ∑ b ∈ S, K a b * u a ^ 2) -
        2 * (∑ a ∈ S, ∑ b ∈ S, K a b * u a * u b) := by
    have he (a b : ℕ) : K a b * (u a - u b) ^ 2 =
        K a b * u a ^ 2 + K a b * u b ^ 2 - 2 * (K a b * u a * u b) := by ring
    simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hrev]
    ring
  have hrow : (∑ a ∈ S, haarGammaRowPotential X a * u a ^ 2) =
      (∑ a ∈ S, (levyEnergy (haarProfile a) / ((2 * a + 1 : ℕ) : ℝ)) * u a ^ 2) +
        ∑ a ∈ S, ∑ b ∈ S, K a b * u a ^ 2 := by
    simp only [haarGammaRowPotential, add_mul, Finset.sum_add_distrib, Finset.sum_mul, S, K]
  have hm := haarSectionProfile_gamma_eq_matrix d X
  simp_rw [haarGamma_diagonal_ground, haarGamma_cross_ground] at hm
  change levyEnergy (haarSectionProfile d X) =
    (∑ a ∈ S, haarGammaRowPotential X a * u a ^ 2) -
      (1 / 2 : ℝ) * ∑ a ∈ S, ∑ b ∈ S, K a b * (u a - u b) ^ 2
  rw [hrow, hexp]
  linarith only [hm]

/-- The exact signed diagonal left by the original arithmetic potential and Gamma rows. -/
def haarWeilGroundPotential (X a : ℕ) : ℝ :=
  (levyEnergy (haarProfile a) +
    (2 * gammaHardyPhaseRate 0 - Real.log ((2 * a + 1 : ℕ) : ℝ)) * haarMass a -
      haarPrimeOutgoingCharge X a) / ((2 * a + 1 : ℕ) : ℝ) +
    ∑ b ∈ Finset.Icc 1 X, haarGammaGraphWeight a b

/-- The full original Weil source retains its divisor reserve, both poles, and exact
signed potential when the adverse additive Gamma graph is moved to the left. -/
theorem haarSectionProfile_roughWeil_add_graph_eq (d : ℕ → ℝ) (X : ℕ) :
    roughWeil (haarSectionProfile d X) + haarGammaGraphEnergy d X =
      haarPrimeLogDefect d X +
        (2 * coshHalfMoment (haarSectionProfile d X) ^ 2 -
          2 * sinhHalfMoment (haarSectionProfile d X) ^ 2) +
        ∑ a ∈ Finset.Icc 1 X, haarWeilGroundPotential X a * haarGroundCoordinate d a ^ 2 := by
  have hterm (a : ℕ) : haarWeilGroundPotential X a * haarGroundCoordinate d a ^ 2 =
      haarGammaRowPotential X a * haarGroundCoordinate d a ^ 2 +
        2 * gammaHardyPhaseRate 0 * (haarMass a * d a ^ 2) -
        (Real.log ((2 * a + 1 : ℕ) : ℝ) * haarMass a + haarPrimeOutgoingCharge X a) *
          d a ^ 2 := by
    have hn : (0 : ℝ) < ((2 * a + 1 : ℕ) : ℝ) := by positivity
    dsimp only [haarWeilGroundPotential, haarGammaRowPotential]
    simp only [haarGroundCoordinate, mul_pow, Real.sq_sqrt hn.le]
    field_simp [hn.ne'] <;> ring
  have hsum : (∑ a ∈ Finset.Icc 1 X,
      haarWeilGroundPotential X a * haarGroundCoordinate d a ^ 2) =
      (∑ a ∈ Finset.Icc 1 X, haarGammaRowPotential X a * haarGroundCoordinate d a ^ 2) +
        2 * gammaHardyPhaseRate 0 * (∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2) -
        ∑ a ∈ Finset.Icc 1 X,
          (Real.log ((2 * a + 1 : ℕ) : ℝ) * haarMass a + haarPrimeOutgoingCharge X a) *
            d a ^ 2 := by
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hg := haarSectionProfile_gamma_eq_row_sub_graph d X
  rw [roughWeil, integral_haarSectionProfile_sq, ← haarPrimeEnergy_eq_primeSum,
    haarPrimeLogDefect, hsum]
  linarith only [hg]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
