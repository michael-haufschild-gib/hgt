import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.EmissionRate.Limit
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CompositionRigidity

/-! # Operational domain of the square root of the logarithmic Hamiltonian -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.EmissionRate

open ModeCapacities
open scoped ENNReal LinearPMap

/-- The positive diagonal square root, on its maximal multiplication domain. -/
def root : Gas →ₗ.[ℂ] Gas := _root_.RHTower.maximalRealDiagonal (fun n => Real.sqrt (energy n))

theorem root_selfAdjoint : IsSelfAdjoint root :=
  _root_.RHTower.maximalRealDiagonal_isSelfAdjoint _

private theorem root_mass (f : Gas) (n : ℕ+) :
    ‖(Real.sqrt (energy n) : ℂ) * f n‖ ^ 2 = energy n * ‖f n‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (energy_nonneg n)]

private theorem root_domain (f : Gas) :
    f ∈ root.domain ↔ Summable (fun n : ℕ+ => energy n * ‖f n‖ ^ 2) := by
  change Memℓp (fun n : ℕ+ => (Real.sqrt (energy n) : ℂ) * f n) 2 ↔ _
  rw [memℓp_gen_iff (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, root_mass]

private theorem weight_nonneg (f : Gas) (n : ℕ+) : 0 ≤ energy n * ‖f n‖ ^ 2 :=
  mul_nonneg (energy_nonneg n) (sq_nonneg _)

theorem finite_iff (f : Gas) : form f ≠ ⊤ ↔ f ∈ root.domain := by
  rw [root_domain, form]
  constructor
  · intro h
    simpa only [ENNReal.toReal_ofReal (weight_nonneg f _)] using ENNReal.summable_toReal h
  · intro h
    rw [← ENNReal.ofReal_tsum_of_nonneg (weight_nonneg f) h]
    exact ENNReal.ofReal_ne_top

theorem form_eq (f : root.domain) : form (f : Gas) = ENNReal.ofReal (‖root f‖ ^ 2) := by
  have h : HasSum (fun n : ℕ+ => energy n * ‖(f : Gas) n‖ ^ 2) (‖root f‖ ^ 2) :=
    (mass_sum (root f)).congr_fun fun n => (root_mass f.val n).symm
  rw [form, ← ENNReal.ofReal_tsum_of_nonneg (weight_nonneg f.val) h.summable, h.tsum_eq]

private theorem diagonal_moment (b : ℕ+ → ℝ) (f : (_root_.RHTower.maximalRealDiagonal b).domain) :
    HasSum (fun n : ℕ+ => b n * ‖(f : Gas) n‖ ^ 2)
      (inner ℂ (f : Gas) (_root_.RHTower.maximalRealDiagonal b f)).re := by
  refine (Complex.hasSum_re (lp.hasSum_inner (𝕜 := ℂ) (f : Gas)
    (_root_.RHTower.maximalRealDiagonal b f))).congr_fun fun n => ?_
  rw [RCLike.inner_apply, _root_.RHTower.maximalRealDiagonal_apply, mul_assoc, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem root_nonnegative (f : root.domain) : 0 ≤ (inner ℂ (f : Gas) (root f)).re := by
  exact (tsum_nonneg fun n => mul_nonneg (Real.sqrt_nonneg (energy n))
    (sq_nonneg (‖(f : Gas) n‖))).trans_eq (diagonal_moment (fun n => Real.sqrt (energy n)) f).tsum_eq

theorem hamiltonian_expectation (f : hamiltonian.domain) :
    form (f : Gas) = ENNReal.ofReal (inner ℂ (f : Gas) (hamiltonian f)).re := by
  have moment : HasSum (fun n : ℕ+ => energy n * ‖(f : Gas) n‖ ^ 2)
      (inner ℂ (f : Gas) (hamiltonian f)).re := diagonal_moment energy f
  rw [form, ← ENNReal.ofReal_tsum_of_nonneg (weight_nonneg f.val) moment.summable, moment.tsum_eq]

/-- Bounded measured loss rates recognize precisely the maximal form domain. -/
theorem bounded_iff (s : Conserving) (f : Gas) :
    (∃ C : ℝ, ∀ t : Duration, ENNReal.ofReal (loss s f t) ≤ ENNReal.ofReal C) ↔
      f ∈ root.domain := by
  rw [← finite_iff, ← supremum_rate s f]
  constructor
  · rintro ⟨C, h⟩
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le h)
  · intro h
    refine ⟨(⨆ u : Duration, ENNReal.ofReal (loss s f u)).toReal, fun t => ?_⟩
    exact (le_iSup (fun u : Duration => ENNReal.ofReal (loss s f u)) t).trans_eq
      (ENNReal.ofReal_toReal h).symm

private theorem twice_weight (f : Gas) (n : ℕ+) :
    (Real.sqrt (energy n) : ℂ) * ((Real.sqrt (energy n) : ℂ) * f n) =
      (energy n : ℂ) * f n := by
  rw [← mul_assoc, ← sq, ← Complex.ofReal_pow, Real.sq_sqrt (energy_nonneg n)]

private theorem second_domain (f : root.domain) :
    root f ∈ root.domain ↔ f.val ∈ hamiltonian.domain := by
  change Memℓp (fun n : ℕ+ => (Real.sqrt (energy n) : ℂ) *
    ((Real.sqrt (energy n) : ℂ) * (f : Gas) n)) 2 ↔
    Memℓp (fun n : ℕ+ => (energy n : ℂ) * (f : Gas) n) 2
  simp only [twice_weight]

/-- On the maximal Hamiltonian domain the positive root can be applied
twice. The two compositions agree on every coordinate. -/
theorem root_square (f : Gas) :
    f ∈ hamiltonian.domain ↔ ∃ h : f ∈ root.domain, root ⟨f,h⟩ ∈ root.domain := by
  constructor
  · intro h
    let g : hamiltonian.domain := ⟨f,h⟩
    have bound (n : ℕ+) : energy n * ‖f n‖ ^ 2 ≤ ‖f n‖ ^ 2 + ‖hamiltonian g n‖ ^ 2 := by
      rw [hamiltonian_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (energy_nonneg n)]
      change energy n * ‖f n‖ ^ 2 ≤ ‖f n‖ ^ 2 + energy n ^ 2 * ‖f n‖ ^ 2
      rw [← one_add_mul]
      exact mul_le_mul_of_nonneg_right (by nlinarith only [sq_nonneg (energy n - 1), energy_nonneg n])
        (sq_nonneg _)
    have first := (root_domain f).mpr (Summable.of_nonneg_of_le (weight_nonneg f) bound
      ((mass_sum f).summable.add (mass_sum (hamiltonian g)).summable))
    exact ⟨first,(second_domain ⟨f,first⟩).mpr h⟩
  · rintro ⟨first,second⟩
    exact (second_domain ⟨f,first⟩).mp second

theorem root_twice (f : root.domain) (h : root f ∈ root.domain) :
    root ⟨root f,h⟩ = hamiltonian ⟨f.val,(second_domain f).mp h⟩ :=
  lp.ext (funext (twice_weight f.val))

#print axioms finite_iff
#print axioms root_selfAdjoint
#print axioms root_nonnegative
#print axioms form_eq
#print axioms hamiltonian_expectation
#print axioms bounded_iff
#print axioms root_square
#print axioms root_twice

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.EmissionRate
