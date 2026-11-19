import GaloisForLFunctions.FiniteFreeProbability.ThetaJensenRealRoots

/-!
# The real theta-factor zero at the Xi saddle

At fixed degree the tilted theta source concentrates even on the Hermite
scale. Binomial expansion before averaging shows that its own rescaled
Jensen factor tends to a pure power. In odd degree the unique zero is at
the saddle to accuracy little-o of the Hermite width.
-/

open Polynomial Finset Filter Topology
open GaloisForLFunctions.SignAlternation RHTower

namespace FiniteFreeProbability

noncomputable section

local notation "Θ" => jensenPoly thetaCuspRawEvenMoment

private theorem affine_power_expectation (n d : ℕ) (a b : ℝ) (Z : ℝ[X]) :
    xiThetaExpectation n ((C a * Z + C b)^d) =
      ∑ j ∈ range (d+1), ((d.choose j : ℝ) * a^j * b^(d-j)) * xiThetaExpectation n (Z^j) := by
  rw [add_pow, map_sum]
  refine sum_congr rfl fun j _ => ?_
  have hp : (C a * Z)^j * C b^(d-j) * (d.choose j : ℝ[X]) =
      C ((d.choose j : ℝ) * a^j * b^(d-j)) * Z^j := by
    simp only [mul_pow, map_mul, map_pow, map_natCast]
    ring
  rw [hp, xiThetaExpectation_C_mul]

private theorem eval_theta_affine_power (n d : ℕ) (x : ℝ) :
    (Θ d n).eval x =
      thetaCuspRawEvenMoment n * xiThetaExpectation n ((C x * X + C 1)^d) := by
  rw [affine_power_expectation, Finset.mul_sum]
  simp only [jensenPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one,
    xiThetaExpectation_X_pow]
  refine sum_congr rfl fun j _ => ?_
  field_simp [(thetaCuspRawEvenMoment_pos n).ne']

/-- Normalization in which the saddle is at zero and one unit is the Xi Hermite width. -/
def thetaSaddleJensen (d n : ℕ) : ℝ[X] :=
  C ((thetaCuspRawEvenMoment n * xiJensenDelta n^d)⁻¹) * (Θ d n).comp
    (C ((thetaJensenSaddle n^2)⁻¹) * (C (xiJensenDelta n) * X - 1))

private theorem thetaSaddle_eval (d n : ℕ) (x : ℝ) :
    (thetaSaddleJensen d n).eval x = xiThetaExpectation n ((xiThetaHermiteArgument n x)^d) := by
  simp only [thetaSaddleJensen, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_one]
  rw [show (thetaJensenSaddle n^2)⁻¹ * (xiJensenDelta n*x-1) =
      (xiJensenDelta n*x-1)/thetaJensenSaddle n^2 by ring, eval_theta_affine_power]
  have ha : C ((xiJensenDelta n*x-1)/thetaJensenSaddle n^2)*X + C 1 =
      C (xiJensenDelta n)*xiThetaHermiteArgument n x := by
    apply Polynomial.funext
    intro y
    have h := xiThetaHermiteArgument_affine n x y
    simp only [eval_add, eval_mul, eval_C, eval_X]
    linarith only [h]
  rw [ha, mul_pow, ← map_pow, xiThetaExpectation_C_mul]
  field_simp [(thetaCuspRawEvenMoment_pos n).ne', (xiJensenDelta_pos n).ne']

/-- Finite coefficient expansion at the Hermite scale in terms of actual fluctuation moments. -/
theorem thetaSaddleJensen_expansion (d n : ℕ) :
    thetaSaddleJensen d n = ∑ j ∈ range (d+1),
      C ((d.choose j : ℝ)*xiThetaExpectation n (xiThetaFluctuation n^j)) *
        (C (xiJensenDelta n)*X-1)^j * X^(d-j) := by
  apply Polynomial.funext
  intro x
  rw [thetaSaddle_eval, xiThetaHermiteArgument, add_comm (C x), affine_power_expectation]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_one]
  exact sum_congr rfl fun _ _ => by ring

/-- The theta factor alone has a pure-power limit at each real point of the Hermite scale. -/
theorem tendsto_thetaSaddleJensen (d : ℕ) (x : ℝ) :
    Tendsto (fun n => (thetaSaddleJensen d n).eval x) atTop (𝓝 (x^d)) := by
  have hA : Tendsto (fun n => xiJensenDelta n*x-1) atTop (𝓝 (-1)) := by
    simpa using (tendsto_xiJensenDelta.mul_const x).sub_const 1
  have h := tendsto_finsetSum (range (d+1)) (fun j _ =>
    (((tendsto_xiThetaExpectation_fluctuation j).const_mul (d.choose j : ℝ)).mul
      (hA.pow j)).mul_const (x^(d-j)))
  simpa [thetaSaddleJensen_expansion, mul_ite, ite_mul] using h

/-- Hermite coordinate of the unique odd root. -/
def thetaOddRootCoordinate (k n : ℕ) : ℝ :=
  (thetaJensenSaddle n^2 * thetaOddRoot n k + 1)/xiJensenDelta n

private theorem odd_coordinate_root (k n : ℕ) :
    (thetaSaddleJensen (2*k+1) n).eval (thetaOddRootCoordinate k n) = 0 := by
  simp only [thetaSaddleJensen, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_one]
  have ha : (thetaJensenSaddle n^2)⁻¹ * (xiJensenDelta n*thetaOddRootCoordinate k n-1) =
      thetaOddRoot n k := by
    unfold thetaOddRootCoordinate
    field_simp [(xiJensenDelta_pos n).ne', (thetaJensenSaddle_pos n).ne']
  rw [ha, thetaOddRoot_spec, mul_zero]

private theorem saddle_odd_mono (k n : ℕ) : StrictMono (thetaSaddleJensen (2*k+1) n).eval := by
  intro x y hxy
  simp only [thetaSaddleJensen, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_one]
  apply mul_lt_mul_of_pos_left _ (inv_pos.mpr (mul_pos (thetaCuspRawEvenMoment_pos n)
    (pow_pos (xiJensenDelta_pos n) _)))
  apply thetaJensen_odd_strictMono
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right (mul_lt_mul_of_pos_left hxy (xiJensenDelta_pos n)) _)
    (inv_pos.mpr (sq_pos_of_pos (thetaJensenSaddle_pos n)))

/-- The unique odd zero converges to the saddle on a scale strictly finer than its Hermite width. -/
theorem tendsto_thetaOddRootCoordinate (k : ℕ) : Tendsto (thetaOddRootCoordinate k) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hneg : (-ε)^(2*k+1) < 0 := by rw [pow_succ]; exact mul_neg_of_pos_of_neg
    (lt_of_le_of_ne ((even_two_mul k).pow_nonneg _) (pow_ne_zero _ (neg_ne_zero.mpr hε.ne')).symm)
    (neg_neg_of_pos hε)
  filter_upwards [(tendsto_thetaSaddleJensen (2*k+1) (-ε)).eventually_lt_const hneg,
    (tendsto_thetaSaddleJensen (2*k+1) ε).eventually_const_lt (pow_pos hε _)] with n hlo hhi
  rw [Real.dist_eq, sub_zero, abs_lt]
  rw [← odd_coordinate_root k n] at hlo hhi
  exact ⟨(saddle_odd_mono k n).lt_iff_lt.mp hlo, (saddle_odd_mono k n).lt_iff_lt.mp hhi⟩

#print axioms thetaSaddleJensen_expansion
#print axioms tendsto_thetaOddRootCoordinate

end

end FiniteFreeProbability
