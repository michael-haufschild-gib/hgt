import GaloisForLFunctions.HTGeometry.EllipticGammaReciprocalRankReversal
import GaloisForLFunctions.HTGeometry.EllipticGammaParityDegeneration

/-!
# The reciprocal nomes and the flat disk

The reciprocal period `-m/(ω + n_j)` has imaginary part `m·Im ω/|ω + n_j|²`, so its nome has modulus
`b_j^m` with `b_j < 1`: along the rational cofinal scaling the nomes are exponentially small,
uniformly in the label.

On the closed disk of radius `1/4` about `i` the multiplicative coordinate is bounded above and
below, so `1 - x` is bounded away from zero there.  These are the two inputs the zero-nome
degeneration needs to become an exponentially flat statement.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {N : ℕ}

/-- The modulus of the standard exponential coordinate. -/
theorem norm_exp_two_pi_I_eq (w : ℂ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w)‖ = Real.exp (-(2 * Real.pi * w.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_ellipticNome_eq (τ : ℂ) :
    ‖ellipticNome τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
  rw [ellipticNome]
  exact norm_exp_two_pi_I_eq τ

theorem norm_coordinate_eq (z : ℂ) :
    ‖multipleEllipticGammaCoordinate z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  rw [multipleEllipticGammaCoordinate]
  exact norm_exp_two_pi_I_eq z

/-- The imaginary part of a reciprocal period. -/
theorem inversePeriod_im {omega : ℂ} (n : Fin N → ℤ) (m : ℕ) (j : Fin N) :
    (inversePeriod omega n m j).im
      = (m : ℝ) * omega.im / Complex.normSq (omega + ((n j : ℤ) : ℂ)) := by
  rw [inversePeriod, Complex.div_im]
  have hre : (-(m : ℂ)).re = -(m : ℝ) := by simp
  have him : (-(m : ℂ)).im = 0 := by simp
  have hwim : (omega + ((n j : ℤ) : ℂ)).im = omega.im := by simp
  rw [hre, him, hwim, zero_mul, zero_div, zero_sub, neg_mul, neg_div, neg_neg]

/-- **The reciprocal nome is exponentially small in the scaling parameter.** -/
theorem norm_nome_inversePeriod {omega : ℂ} (n : Fin N → ℤ) (m : ℕ) (j : Fin N) :
    ‖ellipticNome (inversePeriod omega n m j)‖
      = (Real.exp (-(2 * Real.pi * omega.im
        / Complex.normSq (omega + ((n j : ℤ) : ℂ))))) ^ m := by
  rw [norm_ellipticNome_eq, inversePeriod_im]
  rw [show -(2 * Real.pi * ((m : ℝ) * omega.im / Complex.normSq (omega + ((n j : ℤ) : ℂ))))
      = (m : ℝ) * -(2 * Real.pi * omega.im / Complex.normSq (omega + ((n j : ℤ) : ℂ))) by
    field_simp]
  exact Real.exp_nat_mul _ m

/-- **A uniform exponential bound for the whole reciprocal packet.** -/
theorem exists_nome_bound {omega : ℂ} (homega : Transcendental ℚ omega) (himω : 0 < omega.im)
    (n : Fin N → ℤ) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ (m : ℕ) (j : Fin N),
      ‖ellipticNome (inversePeriod omega n m j)‖ ≤ r ^ m := by
  classical
  rcases isEmpty_or_nonempty (Fin N) with hE | hNE
  · refine ⟨1 / 2, by norm_num, by norm_num, fun m j => ?_⟩
    exact (hE.false j).elim
  · set b : Fin N → ℝ := fun j =>
      Real.exp (-(2 * Real.pi * omega.im / Complex.normSq (omega + ((n j : ℤ) : ℂ)))) with hb
    have hbpos : ∀ j, 0 < b j := fun j => Real.exp_pos _
    have hb1 : ∀ j, b j < 1 := by
      intro j
      rw [hb]
      refine Real.exp_lt_one_iff.mpr ?_
      have hne : omega + ((n j : ℤ) : ℂ) ≠ 0 :=
        add_intCast_ne_zero_of_transcendental homega (n j)
      have hnormpos : 0 < Complex.normSq (omega + ((n j : ℤ) : ℂ)) := by
        rw [Complex.normSq_pos]
        exact hne
      have hpi : 0 < Real.pi := Real.pi_pos
      have hquot : 0 < 2 * Real.pi * omega.im / Complex.normSq (omega + ((n j : ℤ) : ℂ)) := by
        positivity
      linarith
    have huniv : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty
    refine ⟨Finset.univ.sup' huniv b, ?_, ?_, fun m j => ?_⟩
    · obtain ⟨j0⟩ := hNE
      exact le_trans (hbpos j0).le (Finset.le_sup' b (Finset.mem_univ j0))
    · exact (Finset.sup'_lt_iff huniv).mpr fun j _ => hb1 j
    · rw [norm_nome_inversePeriod]
      exact pow_le_pow_left₀ (hbpos j).le (Finset.le_sup' b (Finset.mem_univ j)) m

/-- The closed disk of radius `1/4` about `i`. -/
def flatDisk : Set ℂ := Metric.closedBall Complex.I (1 / 4)

theorem im_bounds_of_mem_flatDisk {z : ℂ} (hz : z ∈ flatDisk) :
    3 / 4 ≤ z.im ∧ z.im ≤ 5 / 4 := by
  have hdist : ‖z - Complex.I‖ ≤ 1 / 4 := by
    rw [flatDisk, Metric.mem_closedBall, Complex.dist_eq] at hz
    exact hz
  have him : |(z - Complex.I).im| ≤ ‖z - Complex.I‖ := Complex.abs_im_le_norm _
  have hval : (z - Complex.I).im = z.im - 1 := by simp
  rw [hval] at him
  have habs := le_trans him hdist
  rw [abs_le] at habs
  constructor <;> linarith [habs.1, habs.2]

/-- On the flat disk the coordinate is bounded by a fixed number below one. -/
theorem norm_coordinate_le_of_mem {z : ℂ} (hz : z ∈ flatDisk) :
    ‖multipleEllipticGammaCoordinate z‖ ≤ Real.exp (-(3 * Real.pi / 2)) := by
  obtain ⟨hlow, -⟩ := im_bounds_of_mem_flatDisk hz
  rw [norm_coordinate_eq]
  refine Real.exp_le_exp.mpr ?_
  have hpi : 0 < Real.pi := Real.pi_pos
  nlinarith

/-- On the flat disk the coordinate is bounded below. -/
theorem norm_coordinate_ge_of_mem {z : ℂ} (hz : z ∈ flatDisk) :
    Real.exp (-(5 * Real.pi / 2)) ≤ ‖multipleEllipticGammaCoordinate z‖ := by
  obtain ⟨-, hhigh⟩ := im_bounds_of_mem_flatDisk hz
  rw [norm_coordinate_eq]
  refine Real.exp_le_exp.mpr ?_
  have hpi : 0 < Real.pi := Real.pi_pos
  nlinarith

theorem exp_neg_three_pi_half_lt_one : Real.exp (-(3 * Real.pi / 2)) < 1 := by
  refine Real.exp_lt_one_iff.mpr ?_
  have hpi : 0 < Real.pi := Real.pi_pos
  linarith

/-- On the flat disk the boundary factor `1 - x` is bounded away from zero. -/
theorem norm_one_sub_coordinate_ge_of_mem {z : ℂ} (hz : z ∈ flatDisk) :
    1 - Real.exp (-(3 * Real.pi / 2)) ≤ ‖1 - multipleEllipticGammaCoordinate z‖ := by
  have hx := norm_coordinate_le_of_mem hz
  have hrev : ‖(1 : ℂ)‖ - ‖multipleEllipticGammaCoordinate z‖
      ≤ ‖1 - multipleEllipticGammaCoordinate z‖ := norm_sub_norm_le _ _
  rw [norm_one] at hrev
  linarith

/-- On the flat disk the boundary factor is bounded above. -/
theorem norm_one_sub_coordinate_le_of_mem {z : ℂ} (hz : z ∈ flatDisk) :
    ‖1 - multipleEllipticGammaCoordinate z‖ ≤ 2 := by
  have hx := norm_coordinate_le_of_mem hz
  have hlt := exp_neg_three_pi_half_lt_one
  have hle : ‖1 - multipleEllipticGammaCoordinate z‖
      ≤ ‖(1 : ℂ)‖ + ‖multipleEllipticGammaCoordinate z‖ := by
    have := norm_sub_le (1 : ℂ) (multipleEllipticGammaCoordinate z)
    exact this
  rw [norm_one] at hle
  linarith

theorem one_sub_coordinate_ne_zero_of_mem {z : ℂ} (hz : z ∈ flatDisk) :
    (1 : ℂ) - multipleEllipticGammaCoordinate z ≠ 0 := by
  intro h0
  have hge := norm_one_sub_coordinate_ge_of_mem hz
  rw [h0, norm_zero] at hge
  have := exp_neg_three_pi_half_lt_one
  linarith

end

end GaloisForLFunctions.HTGeometry
