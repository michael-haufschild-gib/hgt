import GaloisForLFunctions.ArithmeticIncidencePositivity.LagChebyshevAbelSummation

/-!+# Arithmetic degree and horizon torsion

The two-pole box defect cannot be the difference of ordinary cohomology dimensions: it is
strictly between zero and one at `log(3/2)`. At an integer horizon it instead has the exact
arithmetic form `E(log(N+1)) = N - log(Q_N)`, where `Q_N = lcm(1,...,N+1)/(N+1)` is a positive
integer. Thus its real charge and its integral data have distinct, explicit roles.
-/

noncomputable section

open Finset
open GaloisForLFunctions.ArithmeticIncidencePositivity

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The box defect already takes nonintegral values before any prime-power node occurs. -/
theorem boxDefect_between_zero_and_one :
    0 < chebyshevTwoPoleDefect (Real.log (3 / 2 : ℝ)) ∧
      chebyshevTwoPoleDefect (Real.log (3 / 2 : ℝ)) < 1 := by
  have hlog : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hlog' : Real.log (3 / 2 : ℝ) < (3 / 2 : ℝ) - 1 :=
    Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
  have hlt : Real.log (3 / 2 : ℝ) < Real.log 2 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  rw [chebyshevTwoPoleDefect, lagChebyshev_eq_zero_of_lt_log_two hlt,
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

end GaloisForLFunctions.BiarithmeticGeometry
