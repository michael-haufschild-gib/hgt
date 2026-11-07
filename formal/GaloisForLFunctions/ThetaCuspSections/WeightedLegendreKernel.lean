import GaloisForLFunctions.ThetaCuspSections.WeightedLegendreExterior
import GaloisForLFunctions.ThetaCuspSections.PowerPolynomialKernel
import GaloisForLFunctions.HTGeometry.MonicOrthoExtremalComparison
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# A degree-preserving kernel for power-weighted cores

Weighted Legendre derivatives give the exact polynomial expansion and
energy at every degree. Their exterior leading scale bounds evaluation
without embedding into a larger unweighted polynomial space.
-/

open Polynomial MeasureTheory Set
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections

/-- The weighted modes span every polynomial with the same degree cutoff. -/
theorem polynomial_eq_weightedLegendre_sum (r N : ℕ) (P : ℝ[X])
    (hP : P.degree < (N : WithBot ℕ)) :
    ∃ c : Fin N → ℝ, ∀ x, P.eval x =
      ∑ j, c j * (legendreDerivative ((j : ℕ) + r) r).eval x := by
  have hspan := _root_.HTGeometry.mem_span_of_degree_lt
    (f := fun n => legendreDerivative (n + r) r)
    (shiftedLegendreDerivative_natDegree r)
    (fun n => legendreDerivative_ne_zero (by omega)) N P hP
  have hset : (fun n => legendreDerivative (n + r) r) '' {n : ℕ | n < N} =
      range (fun j : Fin N => legendreDerivative ((j : ℕ) + r) r) := by
    ext Q
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, j.isLt, rfl⟩
  rw [hset] at hspan
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
  refine ⟨c, fun x => ?_⟩
  have he := congrArg (Polynomial.eval x) hc
  simpa only [eval_finsetSum, eval_smul, smul_eq_mul] using he.symm

/-- The diagonal kernel retains the exact weighted norms. -/
def weightedLegendreKernel (r N : ℕ) (x : ℝ) : ℝ :=
  ∑ j : Fin N, (legendreDerivative ((j : ℕ) + r) r).eval x ^ 2 /
    weightedLegendreEnergy r ((j : ℕ) + r) ((j : ℕ) + r)

/-- Orthogonality diagonalizes the weighted polynomial energy at every cutoff. -/
theorem integral_weightedLegendre_sum_sq (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ r *
      (∑ j, c j * (legendreDerivative ((j : ℕ) + r) r).eval x) ^ 2) =
      ∑ j, c j ^ 2 * weightedLegendreEnergy r ((j : ℕ) + r) ((j : ℕ) + r) := by
  have hexp (x : ℝ) : (1 - x ^ 2) ^ r *
      (∑ j, c j * (legendreDerivative ((j : ℕ) + r) r).eval x) ^ 2 =
      ∑ i, ∑ j, (c i * c j) * ((1 - x ^ 2) ^ r *
        (legendreDerivative ((i : ℕ) + r) r).eval x *
        (legendreDerivative ((j : ℕ) + r) r).eval x) := by
    simp only [sq]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [intervalIntegral.integral_const_mul]
  change (∑ j, (c i * c j) * weightedLegendreEnergy r
    ((i : ℕ) + r) ((j : ℕ) + r)) = _
  rw [Finset.sum_eq_single i]
  · rw [← sq]
  · intro j _ hji
    rw [weightedLegendreEnergy_eq_zero (fun h => hji (Fin.ext (by omega))), mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Weighted Cauchy bounds every polynomial evaluation by its natural core energy. -/
theorem polynomial_sq_le_weightedLegendreKernel (r N : ℕ) (P : ℝ[X])
    (hP : P.degree < (N : WithBot ℕ)) (x : ℝ) :
    P.eval x ^ 2 ≤ weightedLegendreKernel r N x *
      ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ r * P.eval u ^ 2 := by
  obtain ⟨c, hc⟩ := polynomial_eq_weightedLegendre_sum r N P hP
  simp_rw [hc]
  rw [integral_weightedLegendre_sum_sq, mul_comm]
  unfold weightedLegendreKernel
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro j _
    exact mul_nonneg (sq_nonneg _) (weightedLegendreEnergy_self_pos (by omega)).le
  · intro j _
    exact div_nonneg (sq_nonneg _) (weightedLegendreEnergy_self_pos (by omega)).le
  · intro j _
    have hne := (weightedLegendreEnergy_self_pos (n := (j : ℕ) + r) (r := r) (by omega)).ne'
    apply le_of_eq
    field_simp

private theorem sum_even_powers_le {x : ℝ} (hx : 4 ≤ x) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), x ^ (2 * j)) ≤ 16 / 15 * x ^ (2 * n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have he : x ^ (2 * (n + 1)) = x ^ (2 * n) * x ^ 2 := by
      rw [Nat.mul_add, pow_add]
    have hx2 : 16 ≤ x ^ 2 := by nlinarith only [hx]
    have hp := mul_le_mul_of_nonneg_left hx2 (by positivity : 0 ≤ x ^ (2 * n))
    rw [he]
    nlinarith only [ih, hp]

/-- One top-mode coefficient controls the entire exterior kernel at every degree. -/
theorem weightedLegendreKernel_le {x : ℝ} (hx : 4 ≤ |x|) (r n : ℕ) :
    weightedLegendreKernel r (n + 1) x ≤
      16 / 15 * weightedLegendreLeadRatio r n * |x| ^ (2 * n) := by
  unfold weightedLegendreKernel
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (legendreDerivative (j + r) r).eval x ^ 2 / weightedLegendreEnergy r (j + r) (j + r))]
  have hsum : (∑ j ∈ Finset.range (n + 1),
      (legendreDerivative (j + r) r).eval x ^ 2 / weightedLegendreEnergy r (j + r) (j + r)) ≤
      weightedLegendreLeadRatio r n * ∑ j ∈ Finset.range (n + 1), |x| ^ (2 * j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    have hnorm := weightedLegendreEnergy_self_pos (n := j + r) (r := r) (by omega)
    calc
      _ ≤ (legendreDerivativeLead (j + r) r ^ 2 * |x| ^ (2 * j)) /
          weightedLegendreEnergy r (j + r) (j + r) :=
        div_le_div_of_nonneg_right (shiftedLegendreDerivative_sq_le (by linarith only [hx]) r j)
          hnorm.le
      _ = weightedLegendreLeadRatio r j * |x| ^ (2 * j) := by
        rw [weightedLegendreLeadRatio]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (weightedLegendreLeadRatio_mono r hjn) (by positivity)
  have hgeo := mul_le_mul_of_nonneg_left (sum_even_powers_le hx n)
    (weightedLegendreLeadRatio_pos r n).le
  exact hsum.trans (hgeo.trans_eq (by ring))

/-- The natural weighted basis gives a degree-preserving bound for every power core. -/
theorem polynomial_sq_le_exact_power_core {R : ℝ} (hR : 0 < R) (m : ℕ)
    {P : ℝ[X]} {n : ℕ} (hdeg : P.degree < ((n + 1 : ℕ) : WithBot ℕ))
    {b : ℝ} (hb : 4 * R ≤ |b|) :
    P.eval b ^ 2 ≤ (16 / 15 * weightedLegendreLeadRatio (2 * m) n / R) *
      (|b| / R) ^ (2 * n) * parabolicPowerEnergy R m P := by
  by_cases hP : P = 0
  · subst P
    simp [parabolicPowerEnergy]
  let Q : ℝ[X] := P.comp (C R * X)
  have hQeval (x : ℝ) : Q.eval x = P.eval (R * x) := by
    simp only [Q, eval_comp, eval_mul, eval_C, eval_X]
  have hQdeg : Q.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have hlin : (C R * X).natDegree = 1 := by simp [hR.ne']
    have hQN : Q.natDegree = P.natDegree := by
      dsimp only [Q]
      rw [natDegree_comp, hlin, mul_one]
    have hPN := (natDegree_lt_iff_degree_lt hP).mpr hdeg
    exact (degree_le_natDegree (p := Q)).trans_lt (by exact_mod_cast (hQN.trans_lt hPN))
  have hcov := intervalIntegral.mul_integral_comp_mul_add
    (f := fun b : ℝ => ((1 - b ^ 2 / R ^ 2) ^ m * P.eval b) ^ 2)
    (a := -1) (b := 1) (c := R) (d := 0)
  have hscaled (x : ℝ) :
      ((1 - (R * x + 0) ^ 2 / R ^ 2) ^ m * P.eval (R * x + 0)) ^ 2 =
        (1 - x ^ 2) ^ (2 * m) * Q.eval x ^ 2 := by
    simp only [hQeval, add_zero, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero 2 hR.ne')]
    rw [← pow_mul, Nat.mul_comm m 2]
  simp_rw [hscaled] at hcov
  simp only [mul_neg, mul_one, add_zero] at hcov
  have hI : (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ (2 * m) * Q.eval x ^ 2) =
      parabolicPowerEnergy R m P / R := by
    apply (eq_div_iff hR.ne').mpr
    rw [mul_comm]
    exact hcov
  have hpoint := polynomial_sq_le_weightedLegendreKernel (2 * m) (n + 1) Q hQdeg (b / R)
  rw [hQeval, show R * (b / R) = b by field_simp [hR.ne'], hI] at hpoint
  have habs : |b / R| = |b| / R := by rw [abs_div, abs_of_pos hR]
  have hk := weightedLegendreKernel_le (x := b / R)
    (by rw [habs]; exact (le_div_iff₀ hR).mpr hb) (2 * m) n
  rw [habs] at hk
  have hE := parabolicPowerEnergy_nonneg hR.le m P
  calc
    _ ≤ _ := hpoint
    _ ≤ (16 / 15 * weightedLegendreLeadRatio (2 * m) n * (|b| / R) ^ (2 * n)) *
        (parabolicPowerEnergy R m P / R) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = _ := by ring

#print axioms polynomial_sq_le_weightedLegendreKernel
#print axioms weightedLegendreKernel_le
#print axioms polynomial_sq_le_exact_power_core

end GaloisForLFunctions.ThetaCuspSections
