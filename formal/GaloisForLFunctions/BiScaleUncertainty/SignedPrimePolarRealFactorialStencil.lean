import GaloisForLFunctions.BiScaleUncertainty.ExplicitNyquistPolarAndChebyshevFactorialProducer
import Mathlib.Algebra.Order.Floor.Semifield

/-! The factorial bi-null stencil at arbitrary nonnegative real scales.
Floor carries preserve a logarithmic error bound. -/

open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower
noncomputable section
set_option autoImplicit false

theorem factorialLog_mono : Monotone (floorSummatory chebyshevPsi) := by
  intro a b hab
  rw [floorSummatory_chebyshevPsi, floorSummatory_chebyshevPsi]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (fun j hj => Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hab⟩)
  intro j hj _
  exact Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hj).1)

private theorem factorialLog_add_le (a d : ℕ) {X : ℝ} (hX : (a+d : ℕ) ≤ X) :
    floorSummatory chebyshevPsi (a+d)-floorSummatory chebyshevPsi a ≤
      (d : ℝ)*Real.log (X+1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hXd : ((a+d : ℕ) : ℝ) ≤ X := by
      push_cast at hX ⊢
      linarith
    have hi := ih hXd
    have he : floorSummatory chebyshevPsi (a+(d+1)) =
        floorSummatory chebyshevPsi (a+d)+Real.log ((a+d+1 : ℕ) : ℝ) := by
      rw [floorSummatory_chebyshevPsi, floorSummatory_chebyshevPsi,
        show a+(d+1) = (a+d)+1 by omega,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ a+d+1)]
    have hl : Real.log ((a+d+1 : ℕ) : ℝ) ≤ Real.log (X+1) := by
      apply Real.log_le_log (by positivity)
      push_cast at hX ⊢
      linarith
    rw [he]
    push_cast at hl ⊢
    linarith

/-- A short change of factorial cutoff costs only its length times a logarithm. -/
theorem factorialLog_short_increment {a b c : ℕ} {X : ℝ}
    (hab : a ≤ b) (hbc : b-a ≤ c) (hbX : (b : ℝ) ≤ X) :
    0 ≤ floorSummatory chebyshevPsi b-floorSummatory chebyshevPsi a ∧
      floorSummatory chebyshevPsi b-floorSummatory chebyshevPsi a ≤
        (c : ℝ)*Real.log (X+1) := by
  refine ⟨sub_nonneg.mpr (factorialLog_mono hab), ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  have hd : d ≤ c := by omega
  have hlog : 0 ≤ Real.log (X+1) := Real.log_nonneg (by
    have h0 : (0 : ℝ) ≤ (a+d : ℕ) := Nat.cast_nonneg _
    linarith)
  exact (factorialLog_add_le a d hbX).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hd) hlog)

/-- Integer dilation creates fewer than `a` floor carries. -/
theorem factorial_floor_dilation {v : ℝ} (hv : 0 ≤ v) {a : ℕ} (ha : 1 ≤ a) :
    a*⌊v⌋₊ ≤ ⌊(a : ℝ)*v⌋₊ ∧
      ⌊(a : ℝ)*v⌋₊ < a*⌊v⌋₊+a := by
  have hlo := Nat.floor_le hv
  have hhi := Nat.lt_floor_add_one v
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  constructor
  · apply Nat.le_floor
    push_cast
    exact mul_le_mul_of_nonneg_left hlo haR.le
  · apply (Nat.floor_lt (mul_nonneg haR.le hv)).2
    push_cast
    nlinarith

/-- The dilation stencil is applied after factorial summation. -/
def realFactorialBiNull (v : ℝ) : ℝ :=
  floorSummatory chebyshevPsi ⌊4*v⌋₊ -
    4*floorSummatory chebyshevPsi ⌊2*v⌋₊ +
    4*floorSummatory chebyshevPsi ⌊v⌋₊

theorem realFactorialBiNull_nat (N : ℕ) :
    realFactorialBiNull (N : ℝ) = chebyshevBiNullProducer N := by
  unfold realFactorialBiNull chebyshevBiNullProducer
  norm_cast
  simp only [Nat.floor_natCast]

/-- The signed carries sharpen the sum of their absolute costs. -/
theorem abs_realFactorialBiNull_le {v : ℝ} (hv : 0 ≤ v) :
    |realFactorialBiNull v| ≤ 9*Real.log (4*v+1)+1 := by
  let k := ⌊v⌋₊
  have hk : (k : ℝ) ≤ v := Nat.floor_le hv
  have h4 := factorial_floor_dilation hv (a := 4) (by omega)
  have h2 := factorial_floor_dilation hv (a := 2) (by omega)
  norm_num only [Nat.cast_ofNat] at h4 h2
  have hc4 := factorialLog_short_increment h4.1
    (show ⌊4*v⌋₊-4*k ≤ 3 by dsimp [k]; omega) (Nat.floor_le (by positivity : 0 ≤ 4*v))
  have hc2 := factorialLog_short_increment h2.1
    (show ⌊2*v⌋₊-2*k ≤ 1 by dsimp [k]; omega)
    (show (⌊2*v⌋₊ : ℝ) ≤ 4*v by have := Nat.floor_le (by positivity : 0 ≤ 2*v); linarith)
  have hlog : 0 ≤ Real.log (4*v+1) := Real.log_nonneg (by linarith)
  have hb : |chebyshevBiNullProducer k| ≤ 5*Real.log (4*v+1)+1 := by
    by_cases hk0 : k = 0
    · simp [hk0, chebyshevBiNullProducer, floorSummatory]
      positivity
    · have h := abs_chebyshevBiNullProducer_le (show 1 ≤ k by omega)
      have hl : Real.log (4*(k : ℝ)+1) ≤ Real.log (4*v+1) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith
  have hb' := abs_le.mp hb
  rw [abs_le]
  unfold realFactorialBiNull
  dsimp [k] at hb'
  unfold chebyshevBiNullProducer at hb'
  norm_num only [Nat.cast_ofNat, one_mul] at hc4 hc2
  constructor <;> linarith [hc4.1, hc4.2, hc2.1, hc2.2]

/-- Numeric-only off-grid certificate, valid for every real parameter. -/
theorem realFactorialBiNull_certificate (v : ℝ) :
    |realFactorialBiNull (|v|)| ≤ 9*Real.log (4*|v|+1)+1 :=
  abs_realFactorialBiNull_le (abs_nonneg v)

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
