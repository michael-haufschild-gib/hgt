import GaloisForLFunctions.RHTower.WeilLogShiftCostKernel
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Reverse Cauchy–Schwarz and its exact equality case for the Weil cost kernel. -/

open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilCostPair_smul_left {ι : Type*} [Fintype ι]
    (x u v : ι → ℝ) (a : ℝ) :
    finiteWeilCostPair x (fun i => a * u i) v = a * finiteWeilCostPair x u v := by
  simp only [finiteWeilCostPair, mul_assoc, ← Finset.mul_sum]

theorem finiteWeilCostPair_smul_right {ι : Type*} [Fintype ι]
    (x u v : ι → ℝ) (a : ℝ) :
    finiteWeilCostPair x u (fun i => a * v i) = a * finiteWeilCostPair x u v := by
  rw [finiteWeilCostPair_symm, finiteWeilCostPair_smul_left, finiteWeilCostPair_symm x v u]

/-- Every positive vector determines a sharp rank-one bound; equality means proportionality. -/
theorem finiteWeilCostPair_reverse_cauchy {ι : Type*} [Fintype ι]
    (x u v : ι → ℝ) (hx : Function.Injective x) (hv : 0 < finiteWeilCostPair x v v) :
    finiteWeilCostPair x u u * finiteWeilCostPair x v v ≤ finiteWeilCostPair x u v ^ 2 ∧
      (finiteWeilCostPair x u u * finiteWeilCostPair x v v = finiteWeilCostPair x u v ^ 2 ↔
        ∃ c : ℝ, u = fun i => c * v i) := by
  have hm : finiteWeilCostMoment x v ≠ 0 := by
    intro he
    have hn := (finiteWeilCostPair_moment_zero x v hx he).1
    linarith
  have hm2 : 0 < finiteWeilCostMoment x v * finiteWeilCostMoment x v := mul_self_pos.mpr hm
  let z := fun i => finiteWeilCostMoment x v * u i + (-finiteWeilCostMoment x u) * v i
  have hzm : finiteWeilCostMoment x z = 0 := by
    dsimp [z]
    rw [finiteWeilCostMoment_linearCombination]
    ring
  obtain ⟨hz, hz0⟩ := finiteWeilCostPair_moment_zero x z hx hzm
  have hqz := finiteWeilCostPair_linearCombination x u v
    (finiteWeilCostMoment x v) (-finiteWeilCostMoment x u)
  change finiteWeilCostPair x z z = _ at hqz
  have hid : (finiteWeilCostMoment x v * finiteWeilCostMoment x v) *
        (finiteWeilCostPair x u u * finiteWeilCostPair x v v - finiteWeilCostPair x u v ^ 2) +
      (finiteWeilCostMoment x u * finiteWeilCostPair x v v -
        finiteWeilCostMoment x v * finiteWeilCostPair x u v) ^ 2 =
      finiteWeilCostPair x v v * finiteWeilCostPair x z z := by
    rw [hqz]
    ring
  have hprod := mul_nonpos_of_nonneg_of_nonpos hv.le hz
  have htotal := hprod
  rw [← hid] at htotal
  constructor
  · by_contra h
    have hpos := mul_pos hm2 (sub_pos.mpr (lt_of_not_ge h))
    nlinarith only [htotal, hpos, sq_nonneg (finiteWeilCostMoment x u * finiteWeilCostPair x v v -
      finiteWeilCostMoment x v * finiteWeilCostPair x u v)]
  · constructor
    · intro he
      rw [he, sub_self, mul_zero, zero_add] at hid
      have hprod0 : finiteWeilCostPair x v v * finiteWeilCostPair x z z = 0 := by
        nlinarith only [hid, hprod, sq_nonneg (finiteWeilCostMoment x u * finiteWeilCostPair x v v -
          finiteWeilCostMoment x v * finiteWeilCostPair x u v)]
      have hzero := hz0.mp ((mul_eq_zero.mp hprod0).resolve_left (ne_of_gt hv))
      refine ⟨finiteWeilCostMoment x u / finiteWeilCostMoment x v, ?_⟩
      funext i
      apply mul_left_cancel₀ hm
      have hi := congrFun hzero i
      change finiteWeilCostMoment x v * u i + (-finiteWeilCostMoment x u) * v i = 0 at hi
      have hc : finiteWeilCostMoment x v *
          (finiteWeilCostMoment x u / finiteWeilCostMoment x v) = finiteWeilCostMoment x u := by
        rw [mul_comm, div_mul_cancel₀ _ hm]
      calc
        finiteWeilCostMoment x v * u i = finiteWeilCostMoment x u * v i := by
          linarith only [hi]
        _ = finiteWeilCostMoment x v *
            ((finiteWeilCostMoment x u / finiteWeilCostMoment x v) * v i) := by
          rw [← mul_assoc, hc]
    · rintro ⟨c, rfl⟩
      rw [finiteWeilCostPair_smul_left, finiteWeilCostPair_smul_right,
        finiteWeilCostPair_smul_left]
      ring

theorem finiteWeilCostPair_nonneg {ι : Type*} [Fintype ι]
    (x u v : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    0 ≤ finiteWeilCostPair x u v :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hu i) (hv j)) (Real.exp_pos _).le

theorem finiteWeilCostPair_self_zero_iff {ι : Type*} [Fintype ι]
    (x u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) :
    finiteWeilCostPair x u u = 0 ↔ u = 0 := by
  constructor
  · intro he
    funext i
    have ht (i j : ι) : 0 ≤ u i * u j * Real.exp (2 * |x j - x i|) :=
      mul_nonneg (mul_nonneg (hu i) (hu j)) (Real.exp_pos _).le
    have hrow := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => ht i j)
      (Finset.mem_univ i)
    have hsum := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
        Finset.sum_nonneg (s := Finset.univ) fun k _ => ht j k)
      (Finset.mem_univ i)
    change (∑ j, u i * u j * Real.exp (2 * |x j - x i|)) ≤ finiteWeilCostPair x u u at hsum
    rw [he] at hsum
    simp only [sub_self, abs_zero, mul_zero, Real.exp_zero, mul_one] at hrow
    have hsq : u i ^ 2 = 0 := by nlinarith only [hrow, hsum, sq_nonneg (u i)]
    exact sq_eq_zero_iff.mp hsq
  · rintro rfl
    simp [finiteWeilCostPair]

/-- A nonnegative right vector discharges positivity, including the zero-vector case. -/
theorem finiteWeilCostPair_nonnegative_right_reverse_cauchy {ι : Type*} [Fintype ι]
    (x u v : ι → ℝ) (hx : Function.Injective x)
    (hv : ∀ i, 0 ≤ v i) :
    finiteWeilCostPair x u u * finiteWeilCostPair x v v ≤ finiteWeilCostPair x u v ^ 2 ∧
      (finiteWeilCostPair x u u * finiteWeilCostPair x v v = finiteWeilCostPair x u v ^ 2 ↔
        v = 0 ∨ ∃ c : ℝ, u = fun i => c * v i) := by
  by_cases hz : v = 0
  · subst v
    simp [finiteWeilCostPair]
  · have hp : 0 < finiteWeilCostPair x v v :=
      lt_of_le_of_ne (finiteWeilCostPair_nonneg x v v hv hv)
        (Ne.symm (fun he => hz ((finiteWeilCostPair_self_zero_iff x v hv).mp he)))
    simpa [hz] using finiteWeilCostPair_reverse_cauchy x u v hx hp

/-- The square-root cost obeys the reverse triangle law, strictly away from rays. -/
theorem finiteWeilCostPair_sqrt_superadditive {ι : Type*} [Fintype ι]
    (x u v : ι → ℝ) (hx : Function.Injective x)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    Real.sqrt (finiteWeilCostPair x u u) + Real.sqrt (finiteWeilCostPair x v v) ≤
        Real.sqrt (finiteWeilCostPair x (u + v) (u + v)) ∧
      (Real.sqrt (finiteWeilCostPair x (u + v) (u + v)) =
          Real.sqrt (finiteWeilCostPair x u u) + Real.sqrt (finiteWeilCostPair x v v) ↔
        v = 0 ∨ ∃ c : ℝ, u = fun i => c * v i) := by
  have hA := finiteWeilCostPair_nonneg x u u hu hu
  have hB := finiteWeilCostPair_nonneg x v v hv hv
  have hC := finiteWeilCostPair_nonneg x u v hu hv
  have hS := finiteWeilCostPair_nonneg x (u + v) (u + v)
    (fun i => add_nonneg (hu i) (hv i)) (fun i => add_nonneg (hu i) (hv i))
  have hsum : finiteWeilCostPair x (u + v) (u + v) =
      finiteWeilCostPair x u u + 2 * finiteWeilCostPair x u v + finiteWeilCostPair x v v := by
    change finiteWeilCostPair x (fun i => u i + v i) (fun i => u i + v i) = _
    simpa using finiteWeilCostPair_linearCombination x u v 1 1
  obtain ⟨hCS, hCS0⟩ := finiteWeilCostPair_nonnegative_right_reverse_cauchy x u v hx hv
  have ha := Real.sqrt_nonneg (finiteWeilCostPair x u u)
  have hb := Real.sqrt_nonneg (finiteWeilCostPair x v v)
  have hs := Real.sqrt_nonneg (finiteWeilCostPair x (u + v) (u + v))
  have ha2 := Real.sq_sqrt hA
  have hb2 := Real.sq_sqrt hB
  have hs2 := (Real.sq_sqrt hS).trans hsum
  have hab := mul_nonneg ha hb
  have hab2 : (Real.sqrt (finiteWeilCostPair x u u) *
      Real.sqrt (finiteWeilCostPair x v v)) ^ 2 =
        finiteWeilCostPair x u u * finiteWeilCostPair x v v := by
    rw [mul_pow, ha2, hb2]
  have hcross : Real.sqrt (finiteWeilCostPair x u u) *
      Real.sqrt (finiteWeilCostPair x v v) ≤ finiteWeilCostPair x u v := by
    nlinarith only [hab2, hCS, hab, hC]
  have hcross0 : finiteWeilCostPair x u u * finiteWeilCostPair x v v =
        finiteWeilCostPair x u v ^ 2 ↔
      finiteWeilCostPair x u v = Real.sqrt (finiteWeilCostPair x u u) *
        Real.sqrt (finiteWeilCostPair x v v) := by
    constructor
    · intro he
      nlinarith only [he, hab2, hab, hC]
    · intro he
      rw [he, hab2]
  constructor
  · nlinarith only [ha2, hb2, hs2, hcross, ha, hb, hs]
  · rw [← hCS0, hcross0]
    constructor
    · intro he
      rw [he] at hs2
      nlinarith only [ha2, hb2, hs2]
    · intro he
      nlinarith only [ha2, hb2, hs2, he, ha, hb, hs]

end RHTower
