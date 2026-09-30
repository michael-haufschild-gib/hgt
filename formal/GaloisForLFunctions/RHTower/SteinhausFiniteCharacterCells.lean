import GaloisForLFunctions.RHTower.SteinhausModel

/-!
# Positive measure for finite-character phase cells

A finite collection of Steinhaus characters defines an open phase cell. Integer translations
preserve every character, so an arbitrary real phase prescription has a representative in the
unit cube. Finite open rectangles show that every neighborhood of that representative has
positive product measure, including at boundary coordinates.

The cell size and prefix remain fixed. Uniform covariance stability and common-height measure
transport must be supplied separately before this gives a recurrence event.
-/

noncomputable section
open MeasureTheory Filter Topology Finset Complex
namespace RHTower
open SteinhausModel

theorem continuous_steinhausCharacter (n : ℕ) : Continuous (X n) := by
  unfold X
  fun_prop

theorem steinhausCharacter_add_integer (n : ℕ) (omega : Omega) (k : ℕ → ℤ) :
    X n (fun p => omega p + k p) = X n omega := by
  let m : ℤ := ∑ p ∈ n.primeFactors, (n.factorization p : ℤ) * k p
  have hsum : (∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * (omega p + k p)) =
      (∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * omega p) + (m : ℝ) := by
    dsimp only [m]
    push_cast
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
  unfold X
  rw [hsum]
  have harg : ((2 * Real.pi : ℝ) : ℂ) * I *
      (((∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * omega p) + (m : ℝ) : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) * I *
        ((∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * omega p : ℝ) : ℂ) +
        (m : ℂ) * (2 * (Real.pi : ℂ) * I) := by push_cast; ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem steinhausCharacter_fract (n : ℕ) (omega : Omega) :
    X n (fun p => Int.fract (omega p)) = X n omega := by
  have h := steinhausCharacter_add_integer n omega (fun p => -⌊omega p⌋)
  simpa only [Int.fract, Int.cast_neg, sub_eq_add_neg] using h

private theorem unitInterval_measure_pos_of_mem_nhds {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {U : Set ℝ} (hU : U ∈ 𝓝 x) :
    0 < (volume.restrict (Set.Icc (0 : ℝ) 1)) U := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hU
  let a := max 0 (x - δ)
  let b := min 1 (x + δ)
  have hab : a < b := by
    dsimp only [a, b]
    exact max_lt (lt_min (by norm_num) (by linarith [hx.1]))
      (lt_min (by linarith [hx.2]) (by linarith))
  have hI : Set.Ioo a b ⊆ Set.Icc (0 : ℝ) 1 := by
    intro y hy
    exact ⟨(le_max_left _ _).trans hy.1.le, hy.2.le.trans (min_le_left _ _)⟩
  have hIU : Set.Ioo a b ⊆ U := by
    intro y hy
    apply hsub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have ha := (le_max_right (0 : ℝ) (x - δ)).trans_lt hy.1
    have hb := hy.2.trans_le (min_le_right (1 : ℝ) (x + δ))
    constructor <;> linarith
  have hpos : 0 < (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Ioo a b) := by
    rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.mpr hI,
      Real.volume_Ioo, ENNReal.ofReal_pos]
    linarith
  exact hpos.trans_le (measure_mono hIU)

/-- Every open neighborhood of a unit-cube phase has positive product measure. -/
theorem steinhausMeasure_pos_of_isOpen {U : Set Omega} (hU : IsOpen U)
    {omega : Omega} (homega : ∀ p, omega p ∈ Set.Icc (0 : ℝ) 1) (hmem : omega ∈ U) :
    0 < steinhausMeasure U := by
  obtain ⟨S, V, hV, hsub⟩ := isOpen_pi_iff.mp hU omega hmem
  have hprod : 0 < steinhausMeasure (Set.pi (S : Set ℕ) V) := by
    rw [steinhausMeasure, Measure.infinitePi_pi _ (fun p hp => (hV p hp).1.measurableSet)]
    apply bot_lt_iff_ne_bot.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact ne_of_gt (unitInterval_measure_pos_of_mem_nhds (homega p)
      ((hV p hp).1.mem_nhds (hV p hp).2))
  exact hprod.trans_le (measure_mono hsub)

/-- A finite-character phase cell uses only the prime factors of its finite prefix. -/
def steinhausCharacterCell (B : ℕ) (omega : Omega) (ε : ℝ) : Set Omega :=
  {eta | ∀ n ∈ Icc 1 B, ‖X n eta - X n omega‖ < ε}

theorem isOpen_steinhausCharacterCell (B : ℕ) (omega : Omega) (ε : ℝ) :
    IsOpen (steinhausCharacterCell B omega ε) := by
  simp only [steinhausCharacterCell, Set.setOf_forall]
  apply isOpen_biInter_finset
  intro n _
  exact isOpen_lt ((continuous_steinhausCharacter n).sub continuous_const).norm continuous_const

/-- Every positive-radius finite-character cell has positive Steinhaus measure,
including cells centred at arbitrary real phase prescriptions outside the unit cube. -/
theorem steinhausMeasure_characterCell_pos (B : ℕ) (omega : Omega) {ε : ℝ} (hε : 0 < ε) :
    0 < steinhausMeasure (steinhausCharacterCell B omega ε) := by
  apply steinhausMeasure_pos_of_isOpen (isOpen_steinhausCharacterCell B omega ε)
    (omega := fun p => Int.fract (omega p))
  · intro p
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  · intro n _
    rw [steinhausCharacter_fract, sub_self, norm_zero]
    exact hε

end RHTower
