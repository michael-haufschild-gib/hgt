import GaloisForLFunctions.ArithmeticIncidencePositivity.LagChebyshevAbelSummation

/-!
# Arithmetic degree and horizon torsion

The two-pole box defect cannot be the difference of ordinary cohomology dimensions: it is
strictly between zero and one at `log(3/2)`. At an integer horizon it instead has the exact
arithmetic form `E(log(N+1)) = N - log(Q_N)`, where `Q_N = lcm(1,...,N+1)/(N+1)` is a positive
integer. Thus its real charge and its integral data have distinct, explicit roles.
-/

noncomputable section

open Finset
open scoped NNReal
open GaloisForLFunctions.ArithmeticIncidencePositivity

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The box defect already takes nonintegral values before any prime-power node occurs. -/
theorem boxDefect_between_zero_and_one :
    0 < chebyshevTwoPoleDefect (Real.log (3 / 2 : ℝ)) ∧
      chebyshevTwoPoleDefect (Real.log (3 / 2 : ℝ)) < 1 := by
  have hlog : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hlog' : Real.log (3 / 2 : ℝ) < (3 / 2 : ℝ) - 1 :=
    Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
  have hnodes : lagChebyshev (Real.log (3 / 2 : ℝ)) = 0 := by
    have hfloor : ⌊Real.exp (Real.log (3 / 2 : ℝ))⌋₊ < 2 := by
      rw [Real.exp_log (by norm_num)]
      exact (Nat.floor_lt (by norm_num)).mpr (by norm_num)
    unfold lagChebyshev
    apply Finset.sum_eq_zero
    intro n hn
    have hn' : n = 0 ∨ n = 1 := by
      simp only [mem_Icc] at hn
      omega
    rcases hn' with rfl | rfl <;> simp
  rw [chebyshevTwoPoleDefect, hnodes,
    sub_zero, twoPoleWeight, Real.exp_log (by norm_num)]
  constructor <;> linarith only [hlog, hlog']

/-- No integer equals the box defect at this node-free aperture. -/
theorem boxDefect_ne_integer (z : ℤ) :
    chebyshevTwoPoleDefect (Real.log (3 / 2 : ℝ)) ≠ (z : ℝ) := by
  intro hz
  obtain ⟨h0, h1⟩ := boxDefect_between_zero_and_one
  rw [hz] at h0 h1
  have hz0 : (0 : ℤ) < z := by exact_mod_cast h0
  have hz1 : z < (1 : ℤ) := by exact_mod_cast h1
  omega

/-- Ordinary finite-dimensional cohomology cannot have the proposed box Euler characteristic. -/
theorem no_dimension_model_for_boxDefect :
    ¬ ∃ h0 h1 : ℝ → ℕ, ∀ s : ℝ,
      (h0 s : ℝ) - (h1 s : ℝ) = chebyshevTwoPoleDefect s := by
  rintro ⟨h0, h1, h⟩
  have he := h (Real.log (3 / 2 : ℝ))
  apply boxDefect_ne_integer
    ((h0 (Real.log (3 / 2 : ℝ)) : ℤ) - h1 (Real.log (3 / 2 : ℝ)))
  simpa only [Int.cast_sub, Int.cast_natCast] using he.symm

/-- The number of complete horizon lengths in the least common divisor-incidence period. -/
def horizonTorsionOrder (N : ℕ) : ℕ := Nat.lcmUpto (N + 1) / (N + 1)

theorem horizon_dvd_period (N : ℕ) : N + 1 ∣ Nat.lcmUpto (N + 1) := by
  exact Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨by omega, le_rfl⟩)

theorem horizonTorsionOrder_pos (N : ℕ) : 0 < horizonTorsionOrder N := by
  exact Nat.div_pos (Nat.le_of_dvd (Nat.lcmUpto_pos _) (horizon_dvd_period N))
    (by omega)

theorem horizonTorsionOrder_mul_horizon (N : ℕ) :
    horizonTorsionOrder N * (N + 1) = Nat.lcmUpto (N + 1) := by
  exact Nat.div_mul_cancel (horizon_dvd_period N)

/-- The torsion charge is the logarithmic difference between period and horizon. -/
theorem log_horizonTorsionOrder (N : ℕ) :
    Real.log (horizonTorsionOrder N : ℝ) =
      Real.log (Nat.lcmUpto (N + 1) : ℝ) - Real.log (N + 1 : ℕ) := by
  rw [horizonTorsionOrder, Nat.cast_div (horizon_dvd_period N) (by positivity),
    Real.log_div (by exact_mod_cast (Nat.lcmUpto_ne_zero _)) (by positivity)]

private theorem lagChebyshev_eq_psi (s : ℝ) :
    lagChebyshev s = Chebyshev.psi (Real.exp s) := by
  unfold lagChebyshev Chebyshev.psi
  rw [← Finset.Ioc_insert_left (Nat.zero_le _), Finset.sum_insert (by simp)]
  simp

/-- The box invariant is an integer degree minus a logarithmic torsion charge. -/
theorem boxDefect_eq_degree_sub_log_torsion (N : ℕ) :
    chebyshevTwoPoleDefect (Real.log (N + 1 : ℕ)) =
      (N : ℝ) - Real.log (horizonTorsionOrder N : ℝ) := by
  rw [chebyshevTwoPoleDefect, twoPoleWeight, lagChebyshev_eq_psi,
    Real.exp_log (by positivity), Chebyshev.psi_eq_log_lcmUpto, log_horizonTorsionOrder]
  push_cast
  ring

instance horizonTorsionOrder_neZero (N : ℕ) : NeZero (horizonTorsionOrder N) :=
  ⟨(horizonTorsionOrder_pos N).ne'⟩

/-- A finite cyclic group realizes the integral torsion order. -/
abbrev HorizonTorsion (N : ℕ) := ZMod (horizonTorsionOrder N)

theorem card_horizonTorsion (N : ℕ) :
    Nat.card (HorizonTorsion N) = horizonTorsionOrder N := by
  exact Nat.card_zmod _

/-- The arithmetic Euler formula retains an actual finite-group cardinality. -/
theorem boxDefect_eq_degree_sub_log_card (N : ℕ) :
    chebyshevTwoPoleDefect (Real.log (N + 1 : ℕ)) =
      (N : ℝ) - Real.log (Nat.card (HorizonTorsion N) : ℝ) := by
  rw [card_horizonTorsion, boxDefect_eq_degree_sub_log_torsion]

/-- Between consecutive integer horizons, only the continuous polar charge changes. -/
theorem boxDefect_cell_interpolation (N : ℕ) {s : ℝ}
    (hs0 : Real.log (N + 1 : ℕ) ≤ s) (hs1 : s < Real.log (N + 2 : ℕ)) :
    chebyshevTwoPoleDefect s =
      (N : ℝ) - Real.log (horizonTorsionOrder N : ℝ) +
        (Real.exp s - (N + 1 : ℕ)) + (s - Real.log (N + 1 : ℕ)) := by
  have hfloor : ⌊Real.exp s⌋₊ = N + 1 := by
    rw [Nat.floor_eq_iff (Real.exp_pos s).le]
    constructor
    · simpa only [Real.exp_log (by positivity : (0 : ℝ) < (N + 1 : ℕ))] using
        Real.exp_le_exp.mpr hs0
    · have h := Real.exp_lt_exp.mpr hs1
      rw [Real.exp_log (by positivity)] at h
      push_cast at h ⊢
      linarith only [h]
  have hanchor := boxDefect_eq_degree_sub_log_torsion N
  simp only [chebyshevTwoPoleDefect, twoPoleWeight, lagChebyshev,
    Real.exp_log (by positivity : (0 : ℝ) < (N + 1 : ℕ)), Nat.floor_natCast] at hanchor
  rw [chebyshevTwoPoleDefect, twoPoleWeight, lagChebyshev, hfloor]
  push_cast at hanchor ⊢
  linarith only [hanchor]

/-- The unique integer cell containing a nonnegative logarithmic aperture, indexed from zero. -/
def arithmeticHorizon (s : ℝ≥0) : ℕ := ⌊Real.exp (s : ℝ)⌋₊ - 1

theorem arithmeticHorizon_bounds (s : ℝ≥0) :
    Real.log (arithmeticHorizon s + 1 : ℕ) ≤ (s : ℝ) ∧
      (s : ℝ) < Real.log (arithmeticHorizon s + 2 : ℕ) := by
  have hfloor1 : 1 ≤ ⌊Real.exp (s : ℝ)⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_exp s.property)
  have hsum : arithmeticHorizon s + 1 = ⌊Real.exp (s : ℝ)⌋₊ := by
    unfold arithmeticHorizon
    omega
  have hsum' : arithmeticHorizon s + 2 = ⌊Real.exp (s : ℝ)⌋₊ + 1 := by omega
  rw [hsum, hsum']
  constructor
  · have h := Real.log_le_log (by exact_mod_cast (show 0 < ⌊Real.exp (s : ℝ)⌋₊ by omega))
        (Nat.floor_le (Real.exp_pos (s : ℝ)).le)
    simpa only [Real.log_exp] using h
  · have h := Real.strictMonoOn_log (Real.exp_pos (s : ℝ))
        (by positivity : (0 : ℝ) < (⌊Real.exp (s : ℝ)⌋₊ : ℝ) + 1)
        (Nat.lt_floor_add_one (Real.exp (s : ℝ)))
    simpa only [Real.log_exp, Nat.cast_add, Nat.cast_one] using h

/-- Every nonnegative aperture splits into integer degree, logarithmic torsion, and the exact
continuous evolution from its left integer horizon. -/
theorem boxDefect_all_apertures (s : ℝ≥0) :
    chebyshevTwoPoleDefect (s : ℝ) =
      (arithmeticHorizon s : ℝ) - Real.log (horizonTorsionOrder (arithmeticHorizon s) : ℝ) +
        (Real.exp (s : ℝ) - (arithmeticHorizon s + 1 : ℕ)) +
          ((s : ℝ) - Real.log (arithmeticHorizon s + 1 : ℕ)) :=
  boxDefect_cell_interpolation _ (arithmeticHorizon_bounds s).1 (arithmeticHorizon_bounds s).2

end GaloisForLFunctions.BiarithmeticGeometry
