import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.Nested
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting
import GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp

/-!
# The critical propagator on the full prime gas

The positive multiplier determined by the nested order experiments is
the canonical half-temperature heat. Its fourth power is the Gibbs
operator at inverse temperature two.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder MatrixOrder

abbrev GasOp := Gas →L[ℂ] Gas

def gain (n : ℕ+) := Real.sqrt (n.val:ℝ)

theorem gain_pos (n : ℕ+) : 0 < gain n := Real.sqrt_pos.mpr (by exact_mod_cast n.pos)

theorem gain_sq (n : ℕ+) : gain n^2 = (n.val:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)

def attenuation (n : ℕ+) : ℝ := (gain n)⁻¹

theorem attenuation_pos (n : ℕ+) : 0 < attenuation n := inv_pos.mpr (gain_pos n)

private theorem bounded_attenuation (n : ℕ+) : ‖(attenuation n:ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_of_nonneg (attenuation_pos n).le]
  apply inv_le_one_of_one_le₀
  exact Real.one_le_sqrt.mpr (by exact_mod_cast n.pos)

/-- The positive amplitude fixed by cyclic-order resolution. -/
def criticalOperator : GasOp := HTGeometry.LpDiagonal.lpDiag (fun n : ℕ+ => (attenuation n:ℂ))
  1 zero_le_one bounded_attenuation

theorem critical_apply (f : Gas) (n : ℕ+) :
    criticalOperator f n = (attenuation n:ℂ)*f n := rfl

theorem critical_heat (n : ℕ+) : (attenuation n:ℂ) = heat (1/2) n := by
  have hn : 0 < (n.val:ℝ) := by exact_mod_cast n.pos
  rw [attenuation,gain,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hn,← Real.exp_neg,
    Complex.ofReal_exp,heat,energy]
  congr 1
  push_cast
  ring

theorem critical_isPositive : criticalOperator.IsPositive := by
  constructor
  · intro f g
    rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
    refine tsum_congr fun n => ?_
    simp only [coe_coe,critical_apply,RCLike.inner_apply,map_mul,Complex.conj_ofReal]
    ring
  · intro f
    have hs : Summable (fun n : ℕ+ => inner ℂ (criticalOperator f n) (f n)) := lp.summable_inner _ _
    change 0 ≤ (inner ℂ (criticalOperator f) f).re
    rw [lp.inner_eq_tsum,Complex.re_tsum hs]
    apply tsum_nonneg
    intro n
    have h : inner ℂ (criticalOperator f n) (f n) = (attenuation n:ℂ)*(Complex.normSq (f n):ℂ) := by
      simp only [critical_apply,RCLike.inner_apply,map_mul,Complex.conj_ofReal,← Complex.mul_conj]
      ring
    rw [h,← Complex.ofReal_mul,Complex.ofReal_re]
    exact mul_nonneg (attenuation_pos n).le (Complex.normSq_nonneg _)

theorem critical_injective : Function.Injective criticalOperator := by
  intro f g h
  apply lp.ext
  funext n
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (attenuation_pos n).ne')
    (congrArg (fun v : Gas => v n) h)

def number (k : ℕ) : ℕ+ := ⟨k+1,Nat.succ_pos _⟩

theorem number_injective : Function.Injective number := by
  intro i j h
  have h' : i+1 = j+1 := congrArg PNat.val h
  omega

theorem number_surjective : Function.Surjective number := by
  intro n
  refine ⟨n.val-1,PNat.coe_injective ?_⟩
  change n.val-1+1 = n.val
  have h := n.pos
  omega

def coefficients (G : GasOp) : Kernel := fun i j => G (lp.single 2 (number j) (1:ℂ)) (number i)

theorem coefficients_injective : Function.Injective coefficients := by
  intro G F h
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (HilbertSchmidt.lpBasis ℕ+).dense_span) ?_
  rintro _ ⟨j,rfl⟩
  obtain ⟨k,rfl⟩ := number_surjective j
  rw [HilbertSchmidt.lpBasis_apply]
  apply lp.ext
  funext n
  obtain ⟨i,rfl⟩ := number_surjective n
  exact congrFun (congrFun h i) k

theorem critical_coefficients : coefficients criticalOperator = phaseKernel 1 := by
  funext i j
  rw [coefficients,critical_apply,lp.single_apply,Pi.single_apply,phaseKernel]
  by_cases h : i = j
  · subst j
    rw [if_pos rfl,if_pos rfl,mul_one]
    change (↑((gain (number i))⁻¹):ℂ) = (↑(gain (number i)):ℂ)⁻¹*1
    rw [Complex.ofReal_inv,mul_one]
  · rw [if_neg (fun hn => h (number_injective hn)),if_neg h,mul_zero]

/-- Arbitrarily large positive conserving experiments fix the actual bounded operator. -/
theorem cofinal_operator_iff (G : GasOp) :
    (∀ m, ∃ M ≥ m, (corner (coefficients G) M).PosSemidef ∧ Test (coefficients G) M) ↔
      G = criticalOperator := by
  rw [cofinal_positive_iff,← critical_coefficients]
  exact coefficients_injective.eq_iff

theorem critical_square_apply (f : Gas) (n : ℕ+) :
    (criticalOperator^2) f n = heat 1 n*f n := by
  change criticalOperator (criticalOperator f) n = _
  rw [critical_apply,critical_apply,critical_heat,← mul_assoc,← heat_add,add_halves]

theorem critical_square_hs : (criticalOperator^2).IsHilbertSchmidt := by
  have hs := (summable_heat_sq_iff 1).mpr (by norm_num)
  have h : criticalOperator^2 = HilbertSchmidt.diagOp (heat 1) hs := by
    ext f n
    rw [critical_square_apply,HilbertSchmidt.diagOp_apply]
  rw [h]
  exact HilbertSchmidt.isHilbertSchmidt_diagOp _ hs

theorem critical_fourth_trace : opTrace ((criticalOperator^2)^2) = riemannZeta 2 := by
  let z : {s : ℂ // 1 < s.re} := ⟨2,by norm_num⟩
  have h : (criticalOperator^2)^2 = gibbsOperator z := by
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext n
    change (criticalOperator^2) ((criticalOperator^2) f) n = gibbsOperator z f n
    rw [critical_square_apply,critical_square_apply,
      ← mul_assoc,← heat_add,gibbsOperator_apply]
    norm_num [z]
  exact (congrArg opTrace h).trans (partition_eq_zeta z)

#print axioms critical_heat
#print axioms cofinal_operator_iff
#print axioms critical_isPositive
#print axioms critical_square_hs
#print axioms critical_fourth_trace

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
