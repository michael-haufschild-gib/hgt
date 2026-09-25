import GaloisForLFunctions.RHTower.MobiusDivisorContinuousHeadMoment

noncomputable section
open Finset Set
namespace RHTower

private theorem continuous_head_first_block (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) {x : ℝ} (hx : x ∈ Ioo (1 : ℝ) 2) :
    mobiusDivisorContinuousHead P x = divisorContinuousUnitHead x := by
  unfold mobiusDivisorContinuousHead
  rw [sum_eq_single 1]
  · simp
  · intro d hd hd1
    have hd0 := Nat.pos_of_mem_divisors hd
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
    rw [divisorContinuousUnitHead_eq_zero
      ((div_le_one (by linarith)).mpr (by linarith [hx.2]))]
    ring
  · intro h1
    exact (h1 (Nat.one_mem_divisors.mpr
      (Finset.prod_ne_zero_iff.mpr (fun p hp => (hprime p hp).ne_zero)))).elim

theorem mobiusDivisorSelectionFibre_pair_eq_unsigned_above_half
    (M : ℕ) (P : Finset ℕ) (hprime : ∀ r ∈ P, r.Prime)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpP : p ∉ P) (hqP : q ∉ P) (hpq : p ≠ q)
    (hlo : p * q < M) (hhi : M < 2 * (p * q)) :
    mobiusDivisorSelectionFibre M P {p, q} =
      divisorUnsignedDilationChannel M (p * q) := by
  have hR : ∀ r ∈ ({p, q} : Finset ℕ), r.Prime := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hp
    · exact hq
  have hdis : Disjoint ({p, q} : Finset ℕ) P := by
    simp [hpP, hqP]
  have hr : (∏ r ∈ ({p, q} : Finset ℕ), r) = p * q := by
    simp [hpq]
  have hmu : (((ArithmeticFunction.moebius (p * q) : ℤ) : ℝ)) = 1 := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hp.coprime_iff_not_dvd.mpr
        (fun h => hpq ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one))),
      ArithmeticFunction.moebius_apply_prime hp,
      ArithmeticFunction.moebius_apply_prime hq]
    norm_num
  have hprod0 : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hprodR : (0 : ℝ) < p * q := by exact_mod_cast hprod0
  have hx : (M : ℝ) / (p * q) ∈ Ioo (1 : ℝ) 2 := by
    constructor
    · exact (one_lt_div hprodR).mpr (by exact_mod_cast hlo)
    · exact (div_lt_iff₀ hprodR).mpr (by exact_mod_cast hhi)
  have hcont := continuous_head_first_block P hprime hx
  have hinterp := mobiusDivisorContinuousHead_div P hprime M (p * q) hprod0
  have hF := mobiusDivisorSelectionFibre_product_interpolation M P {p, q} hR hdis
  simp only [hr, hmu, mul_one] at hF
  rw [← hinterp] at hF
  have hcont' : mobiusDivisorContinuousHead P ((M : ℝ) / (p * q : ℕ)) =
      divisorContinuousUnitHead ((M : ℝ) / (p * q : ℕ)) := by
    simpa only [Nat.cast_mul] using hcont
  rw [hcont'] at hF
  calc
    _ = Real.sqrt (p * q : ℕ) *
          divisorContinuousUnitHead ((M : ℝ) / (p * q : ℕ)) := hF
    _ = divisorUnsignedDilationChannel M (p * q) :=
      divisorContinuousUnitHead_dilation M (p * q) hprod0

theorem mobiusDivisorSelectionFibre_pair_pos_above_half
    (M : ℕ) (P : Finset ℕ) (hprime : ∀ r ∈ P, r.Prime)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpP : p ∉ P) (hqP : q ∉ P) (hpq : p ≠ q)
    (hlo : p * q < M) (hhi : M < 2 * (p * q)) :
    0 < mobiusDivisorSelectionFibre M P {p, q} := by
  rw [mobiusDivisorSelectionFibre_pair_eq_unsigned_above_half
    M P hprime hp hq hpP hqP hpq hlo hhi,
    ← divisorContinuousUnitHead_dilation M (p * q) (Nat.mul_pos hp.pos hq.pos)]
  have hprodR : (0 : ℝ) < (p * q : ℕ) := by
    exact_mod_cast (Nat.mul_pos hp.pos hq.pos)
  have hx : (M : ℝ) / (p * q : ℕ) ∈ Ioo (1 : ℝ) 2 := by
    constructor
    · exact (one_lt_div hprodR).mpr (by exact_mod_cast hlo)
    · exact (div_lt_iff₀ hprodR).mpr (by exact_mod_cast hhi)
  exact mul_pos (Real.sqrt_pos.mpr hprodR)
    (divisorContinuousUnitHead_pos_first hx)

end RHTower
