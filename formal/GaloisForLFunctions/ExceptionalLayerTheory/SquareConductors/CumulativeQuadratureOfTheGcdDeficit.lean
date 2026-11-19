import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CumulativeEndpointQuadrature
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SquareAndSixthPowerSamplesOfTheReciprocalPrimeOctave

/-!
# Reciprocal weighting of the accumulated gcd shortfall

At each power-grid endpoint weight the new shortfall by the reciprocal
of one plus the total shortfall so far. Pain's right-endpoint inequality
compares this sum to the logarithm of the total. Its bounded quadrature
error preserves the exponent detected by the original arithmetic test.
-/

noncomputable section

open Filter Finset MeasureTheory
open scoped Topology
open GaloisForLFunctions.CumulativeQuadrature

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem grid_zero (r : ℕ) : powerGridGcdDeficit r 0 = 0 := by
  simp [powerGridGcdDeficit]

theorem gcd_deficit_increment_bounds (r k : ℕ) :
    0 ≤ powerGridGcdDeficit r (k+1) - powerGridGcdDeficit r k ∧
    powerGridGcdDeficit r (k+1) - powerGridGcdDeficit r k ≤ Real.log 2 := by
  simp only [powerGridGcdDeficit, sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le k)),
    add_sub_cancel_left]
  exact ⟨le_max_right _ _, max_le
    (sub_le_self _ (div_nonneg (Real.log_natCast_nonneg _) (by positivity)))
    (Real.log_nonneg (by norm_num))⟩

theorem monotone_gcd_deficit (r : ℕ) : Monotone (powerGridGcdDeficit r) :=
  monotone_nat_of_le_succ fun k => sub_nonneg.mp (gcd_deficit_increment_bounds r k).1

private theorem grid_nonneg (r k : ℕ) : 0 ≤ powerGridGcdDeficit r k := by
  simpa only [grid_zero] using monotone_gcd_deficit r (Nat.zero_le k)

/-- Each charge is divided by one plus the total including that charge. -/
def gcdDeficitLogSum (r : ℕ) : ℕ → ℝ :=
  rightSum (powerGridGcdDeficit r) (fun t => (1+t)⁻¹)

private theorem inv_antitone : AntitoneOn (fun t : ℝ => (1+t)⁻¹) (Set.Ici 0) := by
  intro a ha b _ hab
  exact inv_anti₀ (by linarith only [Set.mem_Ici.mp ha]) (add_le_add_right hab 1)

private theorem grid_log_defect (r k : ℕ) :
    defect (powerGridGcdDeficit r) (fun t => (1+t)⁻¹) k =
      Real.log (1+powerGridGcdDeficit r k) - gcdDeficitLogSum r k := by
  rw [defect, grid_zero]
  congr 1
  have hu := Set.uIcc_of_le (grid_nonneg r k)
  have hp (t : ℝ) (ht : t ∈ Set.uIcc 0 (powerGridGcdDeficit r k)) : 0 < 1+t := by
    rw [hu] at ht
    linarith only [ht.1]
  have hi := (inv_antitone.mono (show Set.uIcc 0 (powerGridGcdDeficit r k) ⊆ Set.Ici 0 by
    rw [hu]; exact fun _ ht => ht.1)).intervalIntegrable (μ := volume)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => Real.log (1+t)) (f' := fun t : ℝ => (1+t)⁻¹)
    (fun t ht => by simpa only [one_div, div_eq_inv_mul, mul_one] using
      (((hasDerivAt_id' (x := t)).const_add 1).log (hp t ht).ne')) hi
  simpa using h

/-- Sharp mesh-variation bound for the reciprocal readings on every grid. -/
theorem gcd_log_sum_error (r k : ℕ) :
    0 ≤ Real.log (1+powerGridGcdDeficit r k) - gcdDeficitLogSum r k ∧
    Real.log (1+powerGridGcdDeficit r k) - gcdDeficitLogSum r k ≤
      Real.log 2 * (1-(1+powerGridGcdDeficit r k)⁻¹) := by
  have ha : AntitoneOn (fun t : ℝ => (1+t)⁻¹)
      (Set.Icc (powerGridGcdDeficit r 0) (powerGridGcdDeficit r k)) := by
    rw [grid_zero]; exact inv_antitone.mono (fun _ ht => ht.1)
  have h := defect_bounds k (monotone_gcd_deficit r) ha
    (fun i _ => (gcd_deficit_increment_bounds r i).2)
  simpa only [grid_log_defect, grid_zero, add_zero, inv_one] using h

/-- The bounded defect converges. After endpoint k the remaining change
is at most log 2 divided by one plus the accumulated shortfall there. -/
theorem gcd_log_sum_limiting_error (r : ℕ) :
    ∃ c : ℝ, Tendsto (fun k => Real.log (1+powerGridGcdDeficit r k) - gcdDeficitLogSum r k)
      atTop (𝓝 c) ∧ ∀ k, 0 ≤ c - (Real.log (1+powerGridGcdDeficit r k) - gcdDeficitLogSum r k) ∧
        c - (Real.log (1+powerGridGcdDeficit r k) - gcdDeficitLogSum r k) ≤
          Real.log 2 / (1+powerGridGcdDeficit r k) := by
  have ha : AntitoneOn (fun t : ℝ => (1+t)⁻¹) (Set.Ici (powerGridGcdDeficit r 0)) := by
    rw [grid_zero]
    exact inv_antitone
  obtain ⟨c,hc,he⟩ := limiting_defect (monotone_gcd_deficit r) ha
    (fun k => inv_nonneg.mpr (by linarith only [grid_nonneg r k]))
    (fun i => (gcd_deficit_increment_bounds r i).2)
  exact ⟨c, hc.congr (grid_log_defect r), fun k => by
    simpa only [grid_log_defect, div_eq_mul_inv] using he k⟩

/-- A sublinear slope in log K on arbitrarily late endpoints, with a separate
additive constant at each slope. -/
def sublinearGcdLogSum (r : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∃ᶠ k : ℕ in atTop,
    gcdDeficitLogSum r k ≤ B + δ*Real.log k

theorem sublinear_log_sum_iff_subpower_grid (r : ℕ) :
    sublinearGcdLogSum r ↔ subpowerGcdGrid r := by
  constructor
  · intro h δ hδ
    obtain ⟨B,hB⟩ := h δ hδ
    refine ⟨Real.exp (B + Real.log 2), (hB.and_eventually (eventually_ge_atTop 1)).mono ?_⟩
    rintro k ⟨hk,hk₁⟩
    have hk₀ : 0 < (k:ℝ) := Nat.cast_pos.mpr hk₁
    have hD : 0 < 1+powerGridGcdDeficit r k := by linarith only [grid_nonneg r k]
    have he := (gcd_log_sum_error r k).2
    have herr : Real.log 2 * (1 - (1+powerGridGcdDeficit r k)⁻¹) ≤ Real.log 2 :=
      (mul_le_mul_of_nonneg_left (sub_le_self 1 (inv_nonneg.mpr hD.le))
        (Real.log_nonneg (by norm_num))).trans_eq (mul_one _)
    have hb : Real.log (1+powerGridGcdDeficit r k) ≤
        (B + Real.log 2) + δ*Real.log k := by linarith only [he.trans herr, hk]
    have hex := Real.exp_le_exp.mpr hb
    rw [Real.exp_log hD, Real.exp_add, mul_comm δ, ← Real.rpow_def_of_pos hk₀] at hex
    linarith only [hex]
  · intro h δ hδ
    obtain ⟨A,hA⟩ := h δ hδ
    let B := 1+max A 0
    have hB : 0 < B := by dsimp only [B]; linarith only [le_max_right A 0]
    refine ⟨Real.log B, (hA.and_eventually (eventually_ge_atTop 1)).mono ?_⟩
    rintro k ⟨hk,hk₁⟩
    have hk₀ : 0 < (k:ℝ) := Nat.cast_pos.mpr hk₁
    have hpow := Real.one_le_rpow (Nat.one_le_cast.mpr hk₁ : (1:ℝ) ≤ k) hδ.le
    have hb : 1 + powerGridGcdDeficit r k ≤ B*(k:ℝ)^δ := by
      rw [show B = 1 + max A 0 by rfl, add_mul, one_mul]
      exact add_le_add hpow (hk.trans (mul_le_mul_of_nonneg_right (le_max_left A 0)
        (Real.rpow_nonneg hk₀.le _)))
    have hlog := Real.log_le_log (by linarith only [grid_nonneg r k]) hb
    rw [Real.log_mul hB.ne' (Real.rpow_pos_of_pos hk₀ δ).ne', Real.log_rpow hk₀] at hlog
    exact (sub_nonneg.mp (gcd_log_sum_error r k).1).trans hlog

/-- Only the reciprocal readings of the actual square/cube products enter
this logarithmic form of the RH criterion. -/
theorem rh_iff_sublinear_square_gcd_log_sum :
    RiemannHypothesis ↔ sublinearGcdLogSum 2 :=
  riemannHypothesis_iff_square_cube_gcd_deficit.trans (sublinear_log_sum_iff_subpower_grid 2).symm

/-- On the (s+2)-power grid, the same slope test reads the closed abscissa
threshold (s+1)/(s+2). -/
theorem sublinear_gcd_log_sum_iff_abscissa (s : ℕ) :
    sublinearGcdLogSum (s+2) ↔ _root_.RHTower.zetaZeroAbscissa ≤ ((s:ℝ)+1)/((s:ℝ)+2) :=
  (sublinear_log_sum_iff_subpower_grid _).trans ((subpower_gcd_grid_iff_octave _).trans
    (subpower_octave_grid_iff_abscissa s (by norm_num : |(-1:ℝ)| = 1)))

#print axioms gcd_log_sum_error
#print axioms gcd_log_sum_limiting_error
#print axioms rh_iff_sublinear_square_gcd_log_sum
#print axioms sublinear_gcd_log_sum_iff_abscissa

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
